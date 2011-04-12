%%%-------------------------------------------------------------------
%%% Copyright (c) 2011 Gemini Mobile Technologies, Inc.  All rights reserved.
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
%%% File    : brick_simple_stub.erl
%%% Purpose : A stub for a simple table-oriented interface to a
%%%           cluster of bricks.
%%%-------------------------------------------------------------------

%% @doc For testing purposes, provide a stub to act as a cluster of
%% bricks.  This stub should not be started in a production
%% environment.  This stub can be started and stopped at any time.
%% The real brick_simple_client is shutdown when this stub is running
%% and is restarted after this this stub is stopped.

-module(brick_simple_stub).

%% API for start and stop
-export([start/0, stop/0]).

%% API for start_table, stop_table, clear_table, and wait_for_table
-export([start_table/1, stop_table/1, clear_table/1, wait_for_table/1]).

%% API for brick_simple_client
-export([do/4, fold_table/7]).

%% API for start_link_table_subscriber and loop_table_subscriber
-export([start_link_table_subscriber/1, loop_table_subscriber/6]).

-define(MOCK_MOD, brick_simple_client).


%%====================================================================
%% Types - common
%%====================================================================

-type attr() :: atom() | {term(), term()}.
-type attrlist() :: [attr()].
-type cnt() :: non_neg_integer().
-type from() :: {pid(),reference()}.
-type key() :: binary() | iolist().
-type len() :: non_neg_integer().
-type ng() :: key_not_exist | {key_exists, ts()} | {ts_error, ts()} | invalid_flag_present | invalid_op_present.
%% -type now() :: {non_neg_integer(), non_neg_integer(), non_neg_integer()}.
-type md5() :: binary() | iolist().
-type table() :: atom().
-type time_t() :: non_neg_integer().   %% UNIX time_t
-type ts() :: non_neg_integer().       %% now() usecs
-type val() :: binary() | iolist().

%%====================================================================
%% Types - external
%%====================================================================

-type update_flag() :: {testset, ts()}
                     | value_in_ram
                     | attr().
-type add_op() :: {add, key(), ts(), val(), time_t(), [update_flag()]}.
-type set_op() :: {set, key(), ts(), val(), time_t(), [update_flag()]}.
-type replace_op() :: {replace, key(), ts(), val(), time_t(), [update_flag()]}.
-type update_op() :: add_op() | set_op() | replace_op().
-type update_reply() :: ok | ng().

-type delete_flag() :: {testset, ts()}
                     | must_exist
                     | must_not_exist.
-type delete_op() :: {delete, key(), [delete_flag()]}.
-type delete_reply() :: ok | ng().

-type get_flag() :: {testset, ts()}
                  | must_exist
                  | must_not_exist
                  | witness
                  | get_all_attribs.
-type get_op() :: {get, key(), [get_flag()]}.
-type get_reply_flag() :: {val_len, len()} | value_in_ram | attr().
-type get_reply() :: {ok, ts()}
                   | {ok, ts(), [get_reply_flag()]}
                   | {ok, ts(), val()}
                   | {ok, ts(), val(), time_t(), [get_reply_flag()]}.

-type get_many_flag() :: {max_bytes, cnt()}
                       | {max_num, cnt()}
                       | {binary_prefix, key()}
                       | witness
                       | get_all_attribs.
-type get_many_op() :: {get_many, key(), [get_many_flag()]}.
-type get_many_reply() :: {ok, {[{key(), ts()}
                                 | {key(), ts(), [get_reply_flag()]}
                                 %% DISABLE | {key(), ts(), val()}
                                 | {key(), ts(), val(), time_t(), [get_reply_flag()]}
                                ], boolean()}
                          }.

-type oplist() :: [txn | update_op() | delete_op() | get_op() | get_many_op()].
-type opflags() :: [update_flag() | delete_flag() | get_flag() | get_many_flag()].

-type replylist() :: [update_reply() | delete_reply() | get_reply() | get_many_reply()].


%%====================================================================
%% Types - internal
%%====================================================================

-record(key, {
          key = <<>> :: key() | '$1',
          ts = 0 :: ts() | '_',
          exp = 0 :: time_t() | '_',
          len = 0 :: len() | '_',
          md5 = <<>> :: md5() | '_',      %% @TODO: will probably go away ...
          attrs = [] :: attrlist() | '_'
         }).

-record(val, {
          key = #key{} :: #key{},
          val = <<>> :: val() | {const,<<>>}
         }).

-record(md5val, {                         %% @TODO: will probably go away ...
          md5 = <<>> :: md5(),
          val = <<>> :: val()
         }).

-record(md5cnt, {                         %% @TODO: will probably go away ...
          md5 = <<>> :: md5(),
          cnt = 0 :: cnt()
         }).

-type format() :: undefined | short | long.

-record(put, {
          val = #val{} :: #val{}
         }).

-record(del, {
          key = #key{} :: #key{}
         }).

-record(getkey, {
          key = #key{} :: #key{},
          format = undefined :: format() | {const,format()}
         }).

-record(getval, {
          val = #val{} :: #val{},
          format = undefined :: format() | {const,format()}
         }).

-record(getkeys, {
          keys = [] :: [#key{}],
          more = false :: boolean(),
          format = undefined :: format()
         }).

-record(getvals, {
          vals = [] :: [#val{}],
          more = false :: boolean(),
          format = undefined :: format()
         }).

-type wop() :: #put{} | #del{}.
-type rop() :: #getkey{} | #getval{} | #getkeys{} | #getvals{}.
-type op() :: rop() | wop().

-type ok() :: {ok, ts()} | [#key{}] | [#val{}].
-record(succ, {result = undefined :: ok()}).
-record(fail, {reason = undefined :: ng()}).

-type ops() :: [op() | #succ{} | #fail{} ].

-record(do, {
          ts = 0 :: ts(),
          ops = [] :: ops(),
          from = undefined :: undefined | from()
         }).


%%====================================================================
%% API
%%====================================================================

-spec start() -> ok.
%% @doc start (or clear) "stub" brick_simple
start() ->
    start_main().

-spec stop() -> ok.
%% @doc stop "stub" brick_simple
stop() ->
    stop_main().

-spec start_table(table()) -> ok.
%% @doc start (or clear) a table
start_table(Tab) ->
    create_tables(Tab).

-spec stop_table(table()) -> ok.
%% @doc stop a table
stop_table(Tab) ->
    delete_tables(Tab).

-spec clear_table(table()) -> ok.
%% @doc delete all objects of table
clear_table(Tab) ->
    clear_tables(Tab).

-spec wait_for_table(table()) -> ok.
%% @doc wait for table
wait_for_table(Tab) ->
    wait_for_tables(Tab).

-spec fold_table(table(), fun(), term(), non_neg_integer(), attrlist(), non_neg_integer(), timeout()) -> no_return().
fold_table(_Tab, _Fun, _Acc, _NumItems, _Flags, _MaxParallel, _Timeout) ->
    exit(not_implemented).


%%====================================================================
%% Internal - main
%%====================================================================

start_main() ->
    ok = stop_main(),
    ok = install_module(),
    ok = mnesia:start(),
    ok.

stop_main() ->
    stopped = mnesia:stop(),
    ok = uninstall_module(),
    ok.

install_module() ->
    ok = delete_module(),
    Forms = meck:abstract_code(meck:beam_file(?MODULE)),
    ok = meck:compile_forms(meck:rename_module(Forms, ?MOCK_MOD), meck:compile_options(?MODULE)),
    ok.

uninstall_module() ->
    ok = delete_module(),
    {ok, _Pid} = supervisor:restart_child(brick_client_data_sup, ?MOCK_MOD),
    ok.

delete_module() ->
    ok = supervisor:terminate_child(brick_client_data_sup, ?MOCK_MOD),
    code:purge(?MOCK_MOD),
    code:delete(?MOCK_MOD),
    ok.


%%====================================================================
%% Internal - tables
%%====================================================================

create_tables(Tab) ->
    ok = stop_table_subscriber(Tab),
    ok = create_table_key(Tab),
    ok = create_table_do(Tab),
    ok = create_table_md5val(Tab),
    ok = create_table_md5cnt(Tab),
    ok = start_table_subscriber(Tab),
    ok = wait_for_tables(Tab),
    ok.

delete_tables(Tab) ->
    ok = stop_table_subscriber(Tab),
    ok = delete_table_key(Tab),
    ok = delete_table_do(Tab),
    ok = delete_table_md5val(Tab),
    ok = delete_table_md5cnt(Tab),
    ok.

clear_tables(Tab) ->
    %% NOTE: non-atomic
    ok = clear_table_key(Tab),
    ok = clear_table_do(Tab),
    ok = clear_table_md5val(Tab),
    ok = clear_table_md5cnt(Tab),
    ok.

create_table_key(Tab) ->
    MTab = table_key(Tab),
    Opts = [{type, ordered_set},
            {ram_copies, [node()]},
            {record_name, key},
            {attributes, record_info(fields, key)}],
    %% DISABLE ... very slow {index, [exp]}],
    do_create_table(MTab, Opts).

create_table_do(Tab) ->
    MTab = table_do(Tab),
    Opts = [{type, ordered_set},
            {ram_copies, [node()]},
            {record_name, do},
            {attributes, record_info(fields, do)}],
    do_create_table(MTab, Opts).

create_table_md5val(Tab) ->
    MTab = table_md5val(Tab),
    Opts = [{type, ordered_set},
            {ram_copies, [node()]},
            {record_name, md5val},
            {attributes, record_info(fields, md5val)}],
    do_create_table(MTab, Opts).

create_table_md5cnt(Tab) ->
    MTab = table_md5cnt(Tab),
    Opts = [{type, set},
            {ram_copies, [node()]},
            {record_name, md5cnt},
            {attributes, record_info(fields, md5cnt)}],
    %% DISABLE ... very slow {index, [cnt]}],
    do_create_table(MTab, Opts).

do_create_table(MTab, Opts) ->
    {atomic, ok} = mnesia:create_table(MTab, Opts),
    ok.

delete_table_key(Tab) ->
    MTab = table_key(Tab),
    do_delete_table(MTab).

delete_table_do(Tab) ->
    MTab = table_do(Tab),
    do_delete_table(MTab).

delete_table_md5val(Tab) ->
    MTab = table_md5val(Tab),
    do_delete_table(MTab).

delete_table_md5cnt(Tab) ->
    MTab = table_md5cnt(Tab),
    do_delete_table(MTab).

do_delete_table(MTab) ->
    case mnesia:delete_table(MTab) of
        {atomic, ok} ->
            ok;
        {aborted, {no_exists,MTab}} ->
            ok
    end.

clear_table_key(Tab) ->
    MTab = table_key(Tab),
    do_clear_table(MTab).

clear_table_do(Tab) ->
    MTab = table_do(Tab),
    do_clear_table(MTab).

clear_table_md5val(Tab) ->
    MTab = table_md5val(Tab),
    do_clear_table(MTab).

clear_table_md5cnt(Tab) ->
    MTab = table_md5cnt(Tab),
    do_clear_table(MTab).

do_clear_table(MTab) ->
    {atomic, ok} = mnesia:clear_table(MTab),
    ok.

table_key(Tab) ->
    table(Tab, "_key").

table_do(Tab) ->
    table(Tab, "_do").

table_md5val(Tab) ->
    table(Tab, "_md5val").

table_md5cnt(Tab) ->
    table(Tab, "_md5cnt").

table(Tab, Type) ->
    list_to_atom(atom_to_list(Tab) ++ Type).

tables(Tab) ->
    [table_key(Tab), table_do(Tab), table_md5val(Tab), table_md5cnt(Tab)].

wait_for_tables(Tab) ->
    %% NOTE: hard-coded timeout for wait for tables
    ok = mnesia:wait_for_tables(tables(Tab), 60000),
    ok.


%%====================================================================
%% Internal - subscriber
%%====================================================================

start_table_subscriber(Tab) ->
    ChildSpec = {Tab, {?MODULE, start_link_table_subscriber, [Tab]},
                 temporary, 2000, worker, [?MODULE]},
    case supervisor:start_child(brick_client_data_sup, ChildSpec) of
        {ok, _Pid} ->
            ok
    end.

start_link_table_subscriber(Tab) ->
    Caller = self(),
    From = {Caller, make_ref()},
    Fun = fun() ->
                  DoTab = table_do(Tab),
                  Md5valTab = table_md5val(Tab),
                  Md5cntTab = table_md5cnt(Tab),
                  mnesia:subscribe({table, DoTab, simple}),
                  Caller ! {From, ok},
                  %% @TODO - restore blobs and last "valid" timestamp
                  %% from disk storage
                  %% @TODO - restore mnesia index to same state as
                  %% disk storage
                  NowTS = make_ts(),
                  loop_table_subscriber(Tab, DoTab, Md5valTab, Md5cntTab, NowTS, NowTS)
          end,
    Pid = proc_lib:spawn_link(Fun),
    receive
        {From, ok} ->
            {ok, Pid}
    after 5000 ->
            %% NOTE: hard-coded timeout
            exit(timeout)
    end.

stop_table_subscriber(Tab) ->
    case supervisor:terminate_child(brick_client_data_sup, Tab) of
        ok ->
            ok;
        {error, not_found} ->
            ok
    end,
    case supervisor:delete_child(brick_client_data_sup, Tab) of
        ok ->
            ok;
        {error, not_found} ->
            ok
    end,
    ok.

loop_table_subscriber(Tab, DoTab, Md5valTab, Md5cntTab, LastTS, MaxTS) ->
    %% @TODO - sync storage on disk before sending reply to caller
    %% @TODO - squid-like "disk priming" for reading values on disk
    %% @TODO - background scavenger-like processing that respects
    %%         LastTS and MaxTS
    receive
        {mnesia_table_event,
         {write, {DoTab, NewTS, Ops, {Caller,_}=From}, _ActivityId}} = _Event ->
            %% DEBUG io:format("pre-event(~p): ~p -> ~p~n", [Tab, _ActivityId, From]),
            Reply = do_res(Tab, DoTab, Md5valTab, Md5cntTab, NewTS, Ops),
            %% DEBUG io:format("post-event(~p): ~p -> ~p ~p~n", [Tab, _ActivityId, From, Reply]),
            Caller ! {From, Reply},
            NewMaxTS = erlang:max(MaxTS, NewTS),
            ?MODULE:loop_table_subscriber(Tab, DoTab, Md5valTab, Md5cntTab, NewTS, NewMaxTS);
        {mnesia_table_event,
         {delete_object, _OldRecord, _ActivityId}} = _Event ->
            %% DEBUG io:format("event(~p): ~p~n", [Tab, _Event]),
            ?MODULE:loop_table_subscriber(Tab, DoTab, Md5valTab, Md5cntTab, LastTS, MaxTS);
        {mnesia_table_event,
         {delete, {DoTab, _Key}, _ActivityId}} = _Event ->
            %% DEBUG io:format("event(~p): ~p~n", [Tab, _Event]),
            ?MODULE:loop_table_subscriber(Tab, DoTab, Md5valTab, Md5cntTab, LastTS, MaxTS);
        %% schema table
        {mnesia_table_event,
         {write, {schema, DoTab, _}, _ActivityId}} = _Event ->
            %% DEBUG io:format("event(~p): ~p~n", [Tab, _Event]),
            ?MODULE:loop_table_subscriber(Tab, DoTab, Md5valTab, Md5cntTab, LastTS, MaxTS);
        {mnesia_table_event,
         {delete, {schema, DoTab}, _ActivityId}} = _Event ->
            %% DEBUG io:format("event(~p): ~p~n", [Tab, _Event]),
            ?MODULE:loop_table_subscriber(Tab, DoTab, Md5valTab, Md5cntTab, LastTS, MaxTS);
        Event ->
            %% DEBUG io:format("event(~p): ~p~n", [Tab, Event]),
            exit({Tab, unknown, Event})
    end.


%%====================================================================
%% Internal - stub implementation
%%====================================================================

-spec do(table(), oplist(), opflags(), timeout()) -> replylist() | {txn_fail, list()}.
%% @doc Send a list of do operations to a table
do(Tab, OpList, OpFlags, Timeout) ->
    WO = lists:any(fun is_write_op/1, OpList),
    RO = lists:any(fun is_read_op/1, OpList),
    Caller = self(),
    From = {Caller, make_ref()},
    Txn = fun() -> do_req(From, Tab, OpList, OpFlags) end,
    if WO ->
            case mnesia:transaction(Txn) of
                {atomic, ok} ->
                    %% DEBUG io:format("receive(~p) transaction -> ~p~n", [Tab, From]),
                    receive
                        {From, Reply} ->
                            filter_reply(Reply)
                    after Timeout ->
                            exit(timeout)
                    end;
                {atomic, Reply} when is_list(Reply) ->
                    filter_reply(Reply);
                {aborted, timeout} ->
                    exit(timeout);
                {aborted, Reason} ->
                    case Reason of
                        {no_exists,_} ->
                            {txn_fail, [{0,brick_not_available}]};
                        _ ->
                            {txn_fail, [Reason]}
                    end
            end;
       RO ->
            try mnesia:async_dirty(Txn) of
                ok ->
                    %% DEBUG io:format("receive(~p) dirty -> ~p~n", [Tab, From]),
                    receive
                        {From, Reply} ->
                            filter_reply(Reply)
                    after Timeout ->
                            exit(timeout)
                    end;
                Reply when is_list(Reply) ->
                    filter_reply(Reply)
            catch
                exit:timeout ->
                    exit(timeout);
                exit:{aborted,Reason} ->
                    case Reason of
                        {no_exists,_} ->
                            {txn_fail, [{0,brick_not_available}]};
                        _ ->
                            {txn_fail, [Reason]}
                    end;
                exit:Reason ->
                    case Reason of
                        {no_exists,_} ->
                            {txn_fail, [{0,brick_not_available}]};
                        _ ->
                            {txn_fail, [Reason]}
                    end
            end;
       true ->
            {txn_fail, [{0,invalid_op_present}]}
    end.

is_write_op({add, _Key, _TS, _Val, _Exp, _Flags}) -> true;
is_write_op({set, _Key, _TS, _Val, _Exp, _Flags}) -> true;
is_write_op({replace, _Key, _TS, _Val, _Exp, _Flags}) -> true;
is_write_op({delete, _Key, _Flags}) -> true;
is_write_op(_) -> false.

is_read_op({get, _Key, _Flags}) -> true;
is_read_op({get_many, _Key, _Flags}) -> true;
is_read_op(_) -> false.


%%====================================================================
%% Internal - stub request
%%====================================================================

-spec do_req(from(), table(), oplist(), opflags()) -> ok | replylist().
%% @doc Execute a list of do operations
do_req(From, Tab, [txn|OpList], OpFlags) ->
    do_req1(From, Tab, OpList, OpFlags, true);
do_req(From, Tab, OpList, OpFlags) ->
    do_req1(From, Tab, OpList, OpFlags, false).

-spec do_req1(from(), table(), oplist(), opflags(), boolean()) -> ok | replylist().
do_req1(From, Tab, OpList, _OpFlags, Txn) ->
    case do_req2(Tab, OpList, _OpFlags, Txn) of
        {true, ReplyList} ->
            ReplyList;
        {false, Ops} ->
            DoTab = table_do(Tab),
            Do = #do{ts=make_ts(), from=From, ops=Ops},
            mnesia:write(DoTab, Do, write)
    end.

-spec do_req2(table(), oplist(), opflags(), boolean()) -> {boolean(), ops()}.
do_req2(Tab, OpList, _OpFlags, Txn) ->
    KeyTab = table_key(Tab),
    Fun = fun({add, Key, TS, Val, Exp, Flags}, {IsSync,N,Acc}) ->
                  Res = case mnesia:read(KeyTab, Key) of
                            [] ->
                                key_put(KeyTab, Key, TS, Val, Exp, Flags);
                            [#key{ts=OldTS}] ->
                                key_fail(Txn, N, {key_exists, OldTS})
                        end,
                  {is_sync(IsSync,Res),N+1,[Res|Acc]};
             ({set, Key, TS, Val, Exp, Flags}, {IsSync,N,Acc}) ->
                  Res = case mnesia:read(KeyTab, Key, write) of
                            [] ->
                                key_put(KeyTab, Key, TS, Val, Exp, Flags);
                            [#key{ts=OldTS}] ->
                                case proplists:get_value(testset, Flags, OldTS) of
                                    OldTS ->
                                        key_put(KeyTab, Key, TS, Val, Exp, Flags);
                                    _ ->
                                        key_fail(Txn, N, {ts_error, OldTS})
                                end
                        end,
                  {is_sync(IsSync,Res),N+1,[Res|Acc]};
             ({replace, Key, TS, Val, Exp, Flags}, {IsSync,N,Acc}) ->
                  Res = case mnesia:read(KeyTab, Key, write) of
                            [] ->
                                key_fail(Txn, N, key_not_exist);
                            [#key{ts=OldTS}] ->
                                case proplists:get_value(testset, Flags, OldTS) of
                                    OldTS ->
                                        key_put(KeyTab, Key, TS, Val, Exp, Flags);
                                    _ ->
                                        key_fail(Txn, N, {ts_error, OldTS})
                                end
                        end,
                  {is_sync(IsSync,Res),N+1,[Res|Acc]};
             ({delete, Key, Flags}, {IsSync,N,Acc}) ->
                  Res = case mnesia:read(KeyTab, Key, write) of
                            [] ->
                                key_fail(Txn, N, key_not_exist);
                            [#key{ts=OldTS}=K] ->
                                case proplists:get_value(testset, Flags, OldTS) of
                                    OldTS ->
                                        key_del(KeyTab, Key, K);
                                    _ ->
                                        key_fail(Txn, N, {ts_error, OldTS})
                                end
                        end,
                  {is_sync(IsSync,Res),N+1,[Res|Acc]};
             ({get, Key, Flags}, {IsSync,N,Acc}) ->
                  Res = case mnesia:read(KeyTab, Key, read) of
                            [] ->
                                key_fail(Txn, N, key_not_exist);
                            [#key{ts=OldTS}=K] ->
                                case proplists:get_value(testset, Flags, OldTS) of
                                    OldTS ->
                                        key_get(KeyTab, Key, Flags, K);
                                    _ ->
                                        key_fail(Txn, N, {ts_error, OldTS})
                                end
                        end,
                  {is_sync(IsSync,Res),N+1,[Res|Acc]};
             ({get_many, Key, Flags}, {IsSync,N,Acc}) ->
                  Res = key_select(KeyTab, Key, Flags),
                  {is_sync(IsSync,Res),N+1,[Res|Acc]};
             (_, {IsSync,N,Acc}) ->
                  Res = key_fail(Txn, N, invalid_op_present),
                  {is_sync(IsSync,Res),N+1,[Res|Acc]}
          end,
    {IsSync,_N,ReplyList} = lists:foldl(Fun, {true,1,[]}, OpList),
    {IsSync,lists:reverse(ReplyList)}.

is_sync(false, _) ->
    false;
is_sync(_, X) when is_record(X, fail) ->
    true;
is_sync(_, _) ->
    false.

key_fail(true, I, Err) ->
    exit({I, Err});
key_fail(_, _, Err) ->
    #fail{reason=Err}.

key_put(KeyTab, Key, TS, Val, Exp, Flags) ->
    Md5 = crypto:md5(Val),
    Attrs = filter_attrs(Flags),
    K = #key{key=Key
             , ts=TS  %% TODO: server-side make_ts()
             , exp=Exp
             , len=byte_size(Val)
             , md5=Md5
             , attrs=Attrs
            },
    ok = mnesia:write(KeyTab, K, write),
    #put{val=#val{key=K, val=Val}}.

key_del(KeyTab, Key, K) ->
    ok = mnesia:delete(KeyTab, Key, write),
    #del{key=K}.

key_get(_KeyTab, _Key, Flags, K) ->
    Wit = proplists:is_defined(witness, Flags),
    All = proplists:is_defined(get_all_attribs, Flags),
    case {Wit, All} of
        {true, false} ->
            #getkey{key=K, format=short};
        {true, true} ->
            #getkey{key=K, format=long};
        {false, false} ->
            #getval{val=#val{key=K}, format=short};
        {false, true} ->
            #getval{val=#val{key=K}, format=long}
    end.

key_select(KeyTab, Key, Flags) ->
    Wit = proplists:is_defined(witness, Flags),
    All = proplists:is_defined(get_all_attribs, Flags),
    Pre = proplists:get_value(binary_prefix, Flags),
    Num = proplists:get_value(max_num, Flags, -1),
    case {Wit, All} of
        {true, false} ->
            {Keys, More} = key_select1(KeyTab, Key, Pre, Num, fun key/1),
            #getkeys{keys=Keys, more=More, format=short};
        {true, true} ->
            {Keys, More} = key_select1(KeyTab, Key, Pre, Num, fun key/1),
            #getkeys{keys=Keys, more=More, format=long};
        {false, false} ->
            {Vals, More} = key_select1(KeyTab, Key, Pre, Num, fun val/1),
            %% DISABLE #getvals{vals=Vals, more=More, format=short};
            #getvals{vals=Vals, more=More, format=long};
        {false, true} ->
            {Vals, More} = key_select1(KeyTab, Key, Pre, Num, fun val/1),
            #getvals{vals=Vals, more=More, format=long}
    end.

key(X) ->
    X.

val(X) ->
    #val{key=X}.

key_select1(KeyTab, Key, Prefix, Num, Fun) ->
    %% TODO: implement max_bytes
    MatchHead = #key{key='$1', _='_'},
    Guard = {'>', '$1', Key},
    Result = {{'$1', '$_'}},
    Pattern = {MatchHead, [Guard], [Result]},
    key_select2(KeyTab, [Pattern], Prefix, Num, Fun).

key_select2(KeyTab, MatchSpec, Prefix, Num, Fun) when Num >= 0 ->
    key_select3(mnesia:select(KeyTab, MatchSpec, Num+1, read)
                , Prefix, Num, Fun);
key_select2(KeyTab, MatchSpec, Prefix, Num, Fun) ->
    key_select3({mnesia:select(KeyTab, MatchSpec, read), undefined}
                , Prefix, Num, Fun).

key_select3(Select, undefined, Num, Fun) ->
    key_select4(Select, undefined, 0, Num, Fun, []);
key_select3(Select, Prefix, Num, Fun) when is_binary(Prefix) ->
    key_select4(Select, Prefix, byte_size(Prefix), Num, Fun, []).

key_select4('$end_of_table', _Prefix, _PrefixLen, _Num, _Fun, Acc) ->
    {lists:reverse(Acc), false};
key_select4({[], undefined}, _Prefix, _PrefixLen, _Num, _Fun, Acc) ->
    {lists:reverse(Acc), false};
key_select4({[], Cont}, Prefix, PrefixLen, Num, Fun, Acc) ->
    key_select4(mnesia:select(Cont), Prefix, PrefixLen, Num, Fun, Acc);
key_select4({L, _Cont}, _Prefix, _PrefixLen, 0, _Fun, Acc) when L =/= [] ->
    {lists:reverse(Acc), true};
key_select4({_L, Cont}, Prefix, PrefixLen, 0, Fun, Acc) ->
    key_select4(mnesia:select(Cont), Prefix, PrefixLen, 0, Fun, Acc);
key_select4({[{_Key,H}|T], Cont}, undefined=Prefix, PrefixLen, Num, Fun, Acc) ->
    key_select4({T, Cont}, Prefix, PrefixLen, Num-1, Fun, [Fun(H)|Acc]);
key_select4({[{Key,H}|T], Cont}, Prefix, PrefixLen, Num, Fun, Acc) ->
    case Key of
        <<Prefix:PrefixLen/binary, _Rest/binary>> ->
            key_select4({T, Cont}, Prefix, PrefixLen, Num-1, Fun, [Fun(H)|Acc]);
        _ ->
            key_select4('$end_of_table', Prefix, PrefixLen, Num, Fun, Acc)
    end.

filter_attrs(Flags) ->
    lists:filter(
      fun({testset, _})       -> false;
         ({max_num, _})       -> false;
         ({binary_prefix, _}) -> false;
         ({val_len, _})       -> false;
         ({_, _})             -> true;
         (must_exist)         -> false;
         (must_not_exist)     -> false;
         (witness)            -> false;
         (get_all_attribs)    -> false;
         (value_in_ram)       -> false; %% TBD
         (A) when is_atom(A)  -> true;
         (_)                  -> false
      end, Flags).

%%====================================================================
%% Internal - stub response
%%====================================================================

-spec do_res(table(), table(), table(), table(), ts(), ops()) -> ok.
%% @doc Execute a list of do operations
do_res(_Tab, DoTab, Md5valTab, Md5cntTab, TS, Ops) ->
    Txn =  fun() ->
                   Reply = lists:map(
                             fun(Succ) when is_record(Succ, succ) ->
                                     Succ;
                                (Fail) when is_record(Fail, fail) ->
                                     Fail;
                                (#put{val=#val{key=#key{md5=Md5}, val=Val}}=Put) ->
                                     %% NOTE: Only reading from the
                                     %% count table is sufficient
                                     case mnesia:dirty_read(Md5cntTab, Md5) of
                                         [] ->
                                             ok = mnesia:dirty_write(Md5valTab, #md5val{md5=Md5, val=Val});
                                         [_] ->
                                             noop
                                     end,
                                     mnesia:dirty_update_counter(Md5cntTab, Md5, 1),
                                     Put;
                                (#del{key=#key{md5=Md5}}=Del) ->
                                     mnesia:dirty_update_counter(Md5cntTab, Md5, -1),
                                     Del;
                                (#getkey{}=GetKey) ->
                                     GetKey;
                                (#getval{val=#val{key=#key{md5=Md5}}=V}=GetVal) ->
                                     [#md5val{val=Val}] = mnesia:dirty_read(Md5valTab, Md5),
                                     GetVal#getval{val=V#val{val=Val}};
                                (#getkeys{}=GetKeys) ->
                                     GetKeys;
                                (#getvals{vals=Vs}=GetVals) ->
                                     NewVs = lists:map(
                                               fun(#val{key=#key{md5=Md5}}=V) ->
                                                       [#md5val{val=Val}] = mnesia:dirty_read(Md5valTab, Md5),
                                                       V#val{val=Val}
                                               end, Vs),
                                     GetVals#getvals{vals=NewVs}
                             end, Ops),
                   ok = mnesia:dirty_delete(DoTab, TS),
                   Reply
           end,
    mnesia:async_dirty(Txn).

filter_reply(Reply) ->
    lists:map(
      fun(#succ{result=Succ}) ->
              Succ;
         (#fail{reason=Fail}) ->
              Fail;
         (Put) when is_record(Put, put) ->
              ok;
         (Del) when is_record(Del, del) ->
              ok;
         (#getkey{key=#key{ts=TS}, format=short}) ->
              {ok, TS};
         (#getkey{key=#key{ts=TS, len=Len, attrs=Attrs}, format=long}) ->
              {ok, TS, [{val_len,Len}|Attrs]};
         (#getval{val=#val{key=#key{ts=TS}, val=Val}, format=short}) ->
              {ok, TS, Val};
         (#getval{val=#val{key=#key{ts=TS, exp=Exp, len=Len, attrs=Attrs}, val=Val}, format=long}) ->
              {ok, TS, Val, Exp, [{val_len,Len}|Attrs]};
         (#getkeys{keys=Ks, more=More, format=short}) ->
              {ok, {[ {Key, TS} || #key{key=Key, ts=TS} <- Ks ], More}};
         (#getkeys{keys=Ks, more=More, format=long}) ->
              {ok, {[ {Key, TS, [{val_len,Len}|Attrs]}
                      || #key{key=Key, ts=TS, len=Len, attrs=Attrs} <- Ks ], More}};
         (#getvals{vals=Vs, more=More, format=short}) ->
              {ok, {[ {Key, TS, Val} || #val{key=#key{key=Key, ts=TS}, val=Val} <- Vs ], More}};
         (#getvals{vals=Vs, more=More, format=long}) ->
              {ok, {[ {Key, TS, Val, Exp, [{val_len,Len}|Attrs]}
                      || #val{key=#key{key=Key, ts=TS, exp=Exp, len=Len, attrs=Attrs}, val=Val} <- Vs ], More}}
      end, Reply).


%%====================================================================
%% Internal - stub timestamps and now
%%====================================================================

-spec make_ts() -> ts().
%% @doc Create a timestamp based on the current time (erlang:now()).
make_ts() ->
    {MSec, Sec, USec} = now(),
    (MSec * 1000000 * 1000000) + (Sec * 1000000) + USec.

-ifdef(UNUSED).
-spec make_now(ts()) -> now().
%% @doc Convert a timestamp from make_ts/1 back into erlang:now()
%% format.
make_now(Ts) ->
    MSec = Ts div (1000000 * 1000000),
    MTs = Ts rem (1000000 * 1000000),
    Sec = MTs div 1000000,
    STs = MTs rem 1000000,
    USec = STs,
    {MSec, Sec, USec}.
-endif. %% -ifdef(UNUSED).
