%%%-------------------------------------------------------------------
%%% Copyright (c) 2007-2016 Hibari developers.  All rights reserved.
%%%
%%% Licensed under the Apache License, Version 2.0 (the "License");
%%% you may not use this file except in compliance with the License.
%%% You may obtain a copy of the License at
%%%
%%%     http://www.apache.org/licenses/LICENSE-2.0
%%%
%%% Unless required by applicable law or agreed to in writing, software
%%% distributed under the License is distributed on an "AS IS" BASIS,
%%% WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
%%% See the License for the specific language governing permissions and
%%% limitations under the License.
%%%
%%% File    : brick_simple_client.erl
%%% Purpose : The client for a simple table-oriented interface to a
%%%           cluster of bricks.
%%%-------------------------------------------------------------------

%% @doc Provide a simple, table-oriented interface to a cluster of
%% bricks.
%%
%% An external entity, such as the cluster manager, will call
%% <tt>set_gh()</tt> to define the current GH (global hash) for a
%% particular table.  Any subsequent operation to use that particular
%% table (e.g. <tt>get()</tt> will use that GH for choosing the brick
%% to which to send the op.

-module(brick_simple_client).

-include("gmt_elog.hrl").

-behaviour(gen_server).

-include("brick.hrl").
-include("brick_hash.hrl").
-include("brick_public.hrl").

-define(FOO_TIMEOUT, 15000).

%% API for brick_simple
-export([do/4, fold_table/7]).

%% API for this gen_server
-export([start_link/0,
         get_gh/1, set_gh/3, set_gh/4, set_gh_all_nodes/2, unset_gh/2]).
-export([key_to_chain/2, key_to_brick/3, find_the_brick/3]).
-export([node_to_tables/1, node_to_tables/2,
         node_to_chains/1, node_to_chains/2,
         node_to_bricks/1, node_to_bricks/2,
         brick_to_chain/1, brick_to_table/1, tab_to_x/1]).
-export([state/0]).                             % Debugging

%% gen_server callbacks
-export([init/1, handle_call/3, handle_cast/2, handle_info/2,
         terminate/2, code_change/3]).

%% Consistent hash checking ... TODO: does this belong in this module?
%% brick_ets??
-export([chash_migration_pre_check/2]).         % public
-export([chash_migration_pre_check2/4]).        % private


-record(state, {
          gh_dict                               % Key = table name,
                                                % Val = tab_gh_r()
         }).

-record(tab_gh_r, {
          gh                                    % global hash record
         }).


-include("brick_specs.hrl").


%% @spec (atom(), do_list(), prop_list(), timeout())
%%    -> zzz_do_reply() | {txn_fail, list()} | {wrong_brick, term()}
%% @doc Send a list of do ops to a brick.
%%
do(Tab, OpList, OpFlags, Timeout) ->
    case find_the_brick(Tab, OpList) of
        brick_not_available = Err ->
            {txn_fail, [{0, Err}]};
        {ServerName, Node}=Brick ->
            ?DBG_OPx({simple, do, Brick, OpList}),
            brick_server:do(ServerName, Node, OpList, OpFlags, Timeout)
    end.


%% @spec (atom(), fun_arity_2(), term(), integer(), proplist(), integer(), integer()) ->
%%       term() | {term(), integer(), integer(), integer()}
%% @doc Attempt a fold operation across all keys in a table.
%%
%% A simultaneous migration will shred this iteration process into a
%% zillion pieces, so don't do it during migration.  :-)
%%
%% If MaxParallel == 0, a true fold will be performed.
%%
%% If MaxParallel >= 1, then an independent fold will be performed
%% upon each chain, with up to MaxParallel number of folds running in
%% parallel.  The result from each chain fold will be returned to the
%% caller as-is, i.e. will *not* be combined like in a "reduce" phase
%% of a map-reduce cycle.
%%
%% The arguments for the fold fun, fun_arity_2(), should be:
%% <ul>
%% <li> {ChainName, Tuple_From_get_many}</li>
%% <li> UserAccumulatorTerm</li>
%% </ul>
%%
%% Tuple_From_get_many is a single result tuple from a get_many()
%% result.  Its format can vary according to the Flags argument, which
%% is passed as-is to a get_many() call.  For example, if Flags = [],
%% then Tuple_From_get_many will match {Key, TS, Value}.  If Flags =
%% [witness], then Tuple_From_get_many will match {Key, TS}.

fold_table(Tab, Fun, Acc, NumItems, Flags, MaxParallel, Timeout) ->
    {ok, _, GH} = get_gh(Tab),
    if GH#g_hash_r.current_h_desc == GH#g_hash_r.new_h_desc ->
            ChainList = brick_hash:all_chains(GH, current),
            Chains = [Ch || {Ch, _Brs} <- ChainList],
            if MaxParallel == 0 ->
                    fold_table_int(Tab, Chains, Fun, Acc, NumItems, Flags, Timeout);
               true ->
                    Fdo = fun(Chain) ->
                                  fold_table_int(Tab, [Chain], Fun, Acc,
                                                 NumItems, Flags, Timeout)
                          end,
                    gmt_pmap:pmap(Fdo, Chains, MaxParallel)
            end;
       true ->
            exit({error, migration_in_progress})
    end.

%% @doc Get the global hash record (#g_hash_r{}) for table Tab from the
%%      local brick_simple server.

get_gh(Tab) ->
    gen_server:call(?MODULE, {get_gh, Tab}).

%% @doc Set the global hash record (#g_hash_r{}) for table Tab on the
%%      specified brick_simple server.

set_gh(Node, Tab, GH) ->
    set_gh(Node, Tab, GH, 5*1000).

set_gh(Node, Tab, GH, Timeout) ->
    gen_server:call({?MODULE, Node}, {set_gh, Tab, GH}, Timeout).

%% @doc Set global hash struct for table Tab on all known Erlang
%%      nodes, using short timeout value (only 2 sec).

set_gh_all_nodes(Tab, GH) ->
    [catch gen_server:call({?MODULE, Node}, {set_gh, Tab, GH}, 2*1000) ||
        Node <- [node()|nodes()] ].

%% @doc This is a kludge to make regression/smoke tests easier to predict.

unset_gh(Node, Tab) ->
    erase({'@#@_last_simple_rev', Tab}),
    gen_server:call({?MODULE, Node}, {unset_gh, Tab}).

node_to_tables(Node) ->
    node_to_tables(Node, current).

%% @spec (atom(), current) -> list(atom())
%% @doc Admin helper: given a node name, find all GDSS tables with at
%%      least one brick on that node.

node_to_tables(Node, current) ->
    tab_to_x(fun(Tab, ChList) -> [Tab || {_Ch, Brs} <- ChList,
                                          lists:keymember(Node, 2, Brs)]
              end).

node_to_chains(Node) ->
    node_to_chains(Node, current).

%% @spec (atom(), current) -> list(atom())
%% @doc Admin helper: given a node name, find all GDSS table chains with at
%%      least one brick on that node.

node_to_chains(Node, current) ->
    tab_to_x(fun(_Tab, ChList) -> [Ch || {Ch, Brs} <- ChList,
                                          lists:keymember(Node, 2, Brs)]
              end).

%% @spec (atom()) -> list(atom())
%% @doc Admin helper: given a node name, find all GDSS table bricks with at
%%      least one brick on that node.

node_to_bricks(Node) ->
    node_to_bricks(Node, current).

node_to_bricks(Node, current) ->
    tab_to_x(fun(_Tab, ChList) -> [Br || {_Ch, Brs} <- ChList,
                                          {Br, Nd} <- Brs, Nd == Node]
              end).

%% @spec ({atom(), atom()}) -> unknown | atom()

brick_to_chain(Brick) ->
    case tab_to_x(fun(_Tab, ChList) -> [Ch || {Ch, Brs} <- ChList,
                                              Br <- Brs, Br == Brick]
                  end) of
        [X] -> X;
        []  -> unknown
    end.

%% @spec ({atom(), atom()}) -> unknown | atom()

brick_to_table(Brick) ->
    case tab_to_x(fun(Tab, ChList) ->
                          [Tab || {_Ch, Brs} <- ChList,
                                  Br <- Brs, Br == Brick]
                  end) of
        [X] -> X;
        []  -> unknown
    end.

state() ->
    gen_server:call(?MODULE, {state}).

%% @spec (atom(), binary() | io_list(), read | write) -> {brick(), node()}

find_the_brick(Tab, Key, ReadWrite) ->
    Do = if ReadWrite == read  -> brick_server:make_get(Key);
            ReadWrite == write -> brick_server:make_delete(Key)
         end,
    case get_gh(Tab) of
        {ok, _, GH} ->
            case brick_server:extract_do_list_keys_find_bricks([Do], GH) of
                {[{_, _}=Brick], _, _} ->
                    Brick;
                _ ->
                    brick_not_available
            end;
        _Err ->
            brick_not_available
    end.

%%====================================================================
%% API
%%====================================================================
%%--------------------------------------------------------------------
%% Function: start_link() -> {ok,Pid} | ignore | {error,Error}
%% Description: Starts the server
%%--------------------------------------------------------------------
start_link() ->
    gen_server:start_link({local, ?MODULE}, ?MODULE, [], []).

%%====================================================================
%% gen_server callbacks
%%====================================================================

%%--------------------------------------------------------------------
%% Function: init(Args) -> {ok, State} |
%%                         {ok, State, Timeout} |
%%                         ignore               |
%%                         {stop, Reason}
%% Description: Initiates the server
%%--------------------------------------------------------------------
init([]) ->
    %% TODO: replace dict with process dictionary?  A Microbenchmark below
    %% (dict_test*) suggests that dict is twice as slow.  {shrug}
    GHDict = dict:new(),
    {ok, #state{gh_dict = GHDict}}.

%%--------------------------------------------------------------------
%% Function: %% handle_call(Request, From, State) -> {reply, Reply, State} |
%%                                      {reply, Reply, State, Timeout} |
%%                                      {noreply, State} |
%%                                      {noreply, State, Timeout} |
%%                                      {stop, Reason, Reply, State} |
%%                                      {stop, Reason, State}
%% Description: Handling call messages
%%--------------------------------------------------------------------
handle_call({get_gh, Tab}, _From, State) ->
    Reply = case dict:find(Tab, State#state.gh_dict) of
                {ok, T} when is_record(T, tab_gh_r) ->
                    GH = T#tab_gh_r.gh,
                    {ok, GH#g_hash_r.minor_rev, GH};
                error ->
                    error
            end,
    {reply, Reply, State};
handle_call({set_gh, Tab, NewGH}, _From, State) ->
    ?DBG_CHAINx({simple_set_gh, node(), NewGH}),
    ?ELOG_INFO("brick_simple(set_gh): minor_rev=~p",
               [NewGH#g_hash_r.minor_rev]),
    %% TODO any sanity checking of the NewGH?
    %% TODO do anything different if Tab is already there?  If not there?
    case dict:find(Tab, State#state.gh_dict) of
        {ok, T} when is_record(T, tab_gh_r) ->
            OldGH = T#tab_gh_r.gh,
            if NewGH#g_hash_r.minor_rev < OldGH#g_hash_r.minor_rev ->
                    {reply, {error, OldGH#g_hash_r.minor_rev}, State};
               true ->
                    NewT = T#tab_gh_r{gh = NewGH},
                    NewD = dict:store(Tab, NewT, State#state.gh_dict),
                    {reply, ok, State#state{gh_dict = NewD}}
            end;
        error ->
            %% Almost Cut-and-paste....
            NewT = #tab_gh_r{gh = NewGH},
            NewD = dict:store(Tab, NewT, State#state.gh_dict),
            {reply, ok, State#state{gh_dict = NewD}}
    end;
handle_call({unset_gh, Tab}, _From, State) ->
    NewD = dict:erase(Tab, State#state.gh_dict),
    {reply, ok, State#state{gh_dict = NewD}};
handle_call({state}, _From, State) ->
    {reply, State, State};
handle_call({stop}, _From, State) ->
    {stop, normal, ok, State};
handle_call(_Request, _From, State) ->
    Reply = unknown_call,
    {reply, Reply, State}.

%%--------------------------------------------------------------------
%% Function: handle_cast(Msg, State) -> {noreply, State} |
%%                                      {noreply, State, Timeout} |
%%                                      {stop, Reason, State}
%% Description: Handling cast messages
%%--------------------------------------------------------------------
handle_cast(_Msg, State) ->
    {noreply, State}.

%%--------------------------------------------------------------------
%% Function: handle_info(Info, State) -> {noreply, State} |
%%                                       {noreply, State, Timeout} |
%%                                       {stop, Reason, State}
%% Description: Handling all non call/cast messages
%%--------------------------------------------------------------------
handle_info({current_gh_version, Tab, Pid, Ref}, State) ->
    Vers = case dict:find(Tab, State#state.gh_dict) of
               {ok, T} when is_record(T, tab_gh_r) ->
                   GH = T#tab_gh_r.gh,
                   GH#g_hash_r.minor_rev;
               error ->
                   -1                   % TODO is this sane??
           end,
    Pid ! {current_gh_version, Ref, Vers},
    {noreply, State};
handle_info(_Info, State) ->
    {noreply, State}.

%%--------------------------------------------------------------------
%% Function: terminate(Reason, State) -> void()
%% Description: This function is called by a gen_server when it is about to
%% terminate. It should be the opposite of Module:init/1 and do any necessary
%% cleaning up. When it returns, the gen_server terminates with Reason.
%% The return value is ignored.
%%--------------------------------------------------------------------
terminate(_Reason, _State) ->
    ok.

%%--------------------------------------------------------------------
%% Func: code_change(OldVsn, State, Extra) -> {ok, NewState}
%% Description: Convert process state when code is changed
%%--------------------------------------------------------------------
code_change(_OldVsn, State, _Extra) ->
    {ok, State}.

%%--------------------------------------------------------------------
%%% Internal functions
%%--------------------------------------------------------------------

%% @doc Select the brick to which to send a do list.
%%
%% TODO I don't remember why the process dictionary get() and put()
%% stuff was a good idea.  Perhaps it isn't, since we're having a
%% synchronous message exchange with the local brick_simple
%% gen_server anyway?  Perhaps it's merely a way to avoid message
%% passing overhead of sending an entire GH each time?  But if so, why
%% did I think that was going to be such a big deal?  Is it really a
%% big deal?

find_the_brick(Tab, DoList) ->
    find_the_brick_loop(Tab, DoList, 4*5).

find_the_brick_loop(_Tab, _DoList, 0) ->
    brick_not_available;
find_the_brick_loop(Tab, DoList, N) ->
    try
        Ref = make_ref(),
        ?MODULE ! {current_gh_version, Tab, self(), Ref},
        GH =
        receive
            {current_gh_version, Rf, -1} when Rf == Ref ->
                timer:sleep(250),
                find_the_brick_loop(Tab, DoList, N - 1);
            {current_gh_version, Rf, Rev} when Rf == Ref ->
                case get({'@#@_last_simple_rev', Tab}) of
                    {Rev, GH0} ->
                        GH0;
                    _ ->                        % Old, or undefined/first call.
                        {ok, CurrentRev, GH0} = get_gh(Tab),
                        put({'@#@_last_simple_rev', Tab}, {CurrentRev, GH0}),
                        GH0
                end
        after 5000 ->
                exit({timeout, brick_simple_server})
        end,
        case brick_server:extract_do_list_keys_find_bricks(DoList, GH) of
            {[{_, _}=Brick], _, _} ->
                Brick;
            _ ->
                brick_not_available
        end
    catch
        _X:_Y ->
            brick_not_available
    end.

key_to_chain(Tab, Key) ->
    {ok, _, GH} = get_gh(Tab),
    brick_hash:key_to_chain(Key, GH).

key_to_brick(Tab, Key, ReadWrite) when ReadWrite == read ; ReadWrite == write ->
    {ok, _, GH} = get_gh(Tab),
    brick_hash:key_to_brick(ReadWrite, Key, GH).

%% @spec (atom(), g_hash_r()) ->
%%       {list({integer(), list({atom(), integer()})}), term()}
%% @doc Run a "pre-migration check" of a migration g_hash_r(), to
%% determine how many keys would migrate and to where.

chash_migration_pre_check(Tab, MigLH) ->
    {ok, _, GH0} = brick_simple_client:get_gh(Tab),
    GH1 = brick_hash:init_global_hash_state(
            true, migrating, 1,
            GH0#g_hash_r.current_h_desc, brick_hash:all_chains(GH0, current),
            MigLH, MigLH#hash_r.healthy_chainlist),
    ChainsHeads = [{Ch, hd(Brs)} ||
                      {Ch, Brs} <- brick_hash:all_chains(GH1, current)],
    SweepKey = ?BRICK__BIGGEST_KEY, % good enough hack
    GH2 = lists:foldl(fun({Ch, _HeadBr}, GHx) ->
                              brick_hash:set_chain_sweep_key(Ch, SweepKey, GHx)
                      end, GH1, ChainsHeads),
    ChHdEts = [begin
                   {ok, Ps} = brick_server:status(Br, Nd),
                   Is = proplists:get_value(implementation, Ps),
                   Ets = proplists:get_value(ets_table_name, Is),
                   {Ch, Hd, Ets}
               end || {Ch, {Br, Nd} = Hd} <- ChainsHeads],
    C_Keys = [{Ch, rpc:async_call(Nd, brick_simple, chash_migration_pre_check2,
                                  [Ets, Ch, GH0, GH2])}
              || {Ch, {_Br, Nd}, Ets} <- ChHdEts],
    Rs = [{Ch, rpc:yield(C_K)} || {Ch, C_K} <- C_Keys],
    {BeforeD, KeepD, MoveD, MoveWhereD, Bummer} =
        lists:foldl(
          fun({Ch, {badrpc, Err}},
              {BeforeDict, KeepDict, MoveDict, MoveWhereDict, Bummer}) ->
                  {BeforeDict, KeepDict, MoveDict, MoveWhereDict,
                   [{Ch, Err}|Bummer]};
             ({Ch, {_Ch, Size, Keep, Moving}},
              {BeforeDict, KeepDict, MoveDict, MoveWhereDict, Bummer}) ->
                  BD = orddict:store(Ch, Size, BeforeDict),
                  KD = orddict:store(Ch, Keep, KeepDict),
                  MD = lists:foldl(
                         fun({Chx, Moved}, Dx) ->
                                 orddict:update_counter(Chx, Moved, Dx)
                         end, MoveDict, Moving),
                  MWD = orddict:store(Ch, Moving, MoveWhereDict),
                  {BD, KD, MD, MWD, Bummer}
          end,
          {orddict:new(), orddict:new(),orddict:new(), orddict:new(), []}, Rs),
    [{keys_before, BeforeD}, {keys_keep, KeepD}, {keys_moving, MoveD},
     {keys_moving_where, MoveWhereD}, {errors, Bummer}].

chash_migration_pre_check2(Ets, ChainName, OldGH, NewGH) ->
    process_flag(priority, low),
    Size = ets:info(Ets, size),
    {M, D} = ets:foldl(
               fun(ST, {Mine, OtherDict}) ->
                       Key = element(1, ST),            % icky icky
                       Old = brick_hash:key_to_chain(Key, OldGH),
                       New = brick_hash:key_to_chain(Key, NewGH),
                       if Old == New ->
                               {Mine + 1, OtherDict};
                          true ->
                               {Mine, orddict:update_counter(New, 1,OtherDict)}
                       end
               end, {0, orddict:new()}, Ets),
    {ChainName, Size, M, orddict:to_list(D)}.

fold_table_int(Tab, Chains, Fun, Acc, NumItems, Flags, Timeout) ->
    fold_table_iter(Tab, Chains, <<>>, Fun, Acc, NumItems, Flags, Timeout).

fold_table_iter(Tab, [Ch|_Chs]=ChainList, <<>> = Key, Fun, Acc, NumItems, Flags, Timeout) ->
    %% Need to send the first query directly to the chain's tail brick.
    {ok, _, GH} = get_gh(Tab),
    {TailNd, TailBr} = brick_hash:chain2brick(Ch, read, GH, current),
    DoOp = brick_server:make_get_many(Key, NumItems, Flags),
    try brick_server:do(TailNd, TailBr, [DoOp], [ignore_role], Timeout) of
        [{ok, {L, MoreP}}] ->
            %%io:format("DBG: iter1 hd(L) = ~p\n", [hd(L)]),
            fold_table_iter2(Tab, ChainList, Key, Fun, Acc, NumItems, Flags, Timeout,
                             L, MoreP)
    catch exit:{Reason, _}
        when Reason == timeout orelse Reason == noproc ->
            timer:sleep(1000),
            fold_table_iter(Tab, ChainList, Key, Fun, Acc, NumItems, Flags, Timeout)
    end;
fold_table_iter(Tab, [_|_] = ChainList, Key, Fun, Acc, NumItems, Flags, Timeout) ->
    %%io:format("DBG: iter1 ~p\n", [Key]),
    try brick_simple:get_many(Tab, Key, NumItems, Flags, Timeout) of
        {ok, {L, MoreP}} ->
            fold_table_iter2(Tab, ChainList, Key, Fun, Acc, NumItems, Flags, Timeout,
                             L, MoreP)
    catch exit:{Reason, _}
        when Reason == timeout orelse Reason == noproc ->
            timer:sleep(1000),
            fold_table_iter(Tab, ChainList, Key, Fun, Acc, NumItems, Flags, Timeout)
    end;
fold_table_iter(_Tab, [], <<>>, _Fun, Acc, _NumItems, _Flags, _Timeout) ->
    Acc.

fold_table_iter2(Tab, [Ch|Chs] = ChainList, PrevKey, Fun, Acc, NumItems, Flags, Timeout,
                 Keys, MoreP) ->
    %%io:format("DBG: iter2 ~p\n", [PrevKey]),
    NewAcc = lists:foldl(Fun, Acc, [{Ch, K} || K <- Keys]),
    if MoreP == false ->
            %% Advance to the next chain.
            fold_table_iter(Tab, Chs, <<>>, Fun, NewAcc, NumItems,
                            Flags, Timeout);
       true ->
            LastKey = if Keys == [] ->
                              PrevKey; % Trust MoreP == true, do it again.
                         true ->
                              element(1, lists:last(Keys))
                      end,
            fold_table_iter(Tab, ChainList, LastKey, Fun, NewAcc,
                            NumItems, Flags, Timeout)
    end.

tab_to_x(XformFun) ->
    lists:usort(
      lists:flatten(
        [begin
             {ok, _, GH} = get_gh(Tab),
             ChList = (GH#g_hash_r.current_h_desc)#hash_r.healthy_chainlist,
             XformFun(Tab, ChList)
         end || Tab <- brick_admin:get_tables({global, brick_admin})])).

