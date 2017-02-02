%%%-------------------------------------------------------------------
%%% Copyright (c) 2007-2017 Hibari developers.  All rights reserved.
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
%%% File    : brick_simple.erl
%%% Purpose : A simple table-oriented interface to a cluster of bricks.
%%%-------------------------------------------------------------------

%% @doc Provide a simple, table-oriented interface to a cluster of
%% bricks.

-module(brick_simple).

-include("gmt_elog.hrl").

-include("brick.hrl").
-include("brick_hash.hrl").
-include("brick_public.hrl").

-define(FOO_TIMEOUT, 15000).

-export([add/3, add/4, add/6, replace/3, replace/4, replace/6,
         set/3, set/4, set/6, rename/3, rename/4, rename/6,
         get/2, get/3, get/4,
         delete/2, delete/3, delete/4,
         get_many/3, get_many/4, get_many/5,
         do/2, do/3, do/4]).
-export([fold_table/5, fold_table/6, fold_table/7,
         fold_key_prefix/5, fold_key_prefix/9]).
-export([clear_table/1]).

-include("brick_specs.hrl").

-type finite_timeout() :: non_neg_integer().

-spec add(table_name(), key(), val()) -> do1_res().
-spec add(table_name(), key(), val(), flags_list() | finite_timeout()) -> do1_res().
-spec add(table_name(), key(), val(), exp_time(), flags_list(), finite_timeout()) -> do1_res().
-spec replace(table_name(), key(), val_impl()) -> do1_res().
-spec replace(table_name(), key(), val_impl(), flags_list() | finite_timeout()) -> do1_res().
-spec replace(table_name(), key(), val_impl(), exp_time(), flags_list(), finite_timeout()) -> do1_res().
-spec set(table_name(), key(), val()) -> do1_res().
-spec set(table_name(), key(), val(), flags_list() | finite_timeout()) -> do1_res().
-spec set(table_name(), key(), val(), exp_time(), flags_list(), finite_timeout()) -> do1_res().
-spec rename(table_name(), key(), key()) -> do1_res().
-spec rename(table_name(), key(), key(), flags_list() | finite_timeout()) -> do1_res().
-spec rename(table_name(), key(), key(), exp_time(), flags_list(), finite_timeout()) -> do1_res().
-spec get(table_name(), key()) -> do1_res().
-spec get(table_name(), key(), flags_list() | finite_timeout()) -> do1_res().
-spec get(table_name(), key(), flags_list(), finite_timeout()) -> do1_res().
-spec delete(table_name(), key()) -> do1_res().
-spec delete(table_name(), key(), flags_list() | finite_timeout()) -> do1_res().
-spec delete(table_name(), key(), flags_list(), finite_timeout()) -> do1_res().
-spec get_many(table_name(), key(), integer()) -> do1_res().
-spec get_many(table_name(), key(), integer(), flags_list() | finite_timeout()) -> do1_res().
-spec get_many(table_name(), key(), integer(), flags_list(), finite_timeout()) -> do1_res().

-spec do(atom(), do_op_list(), do_flags_list(), finite_timeout()) -> do_res().


%% @spec (atom(), io_list(), io_list())
%%    -> zzz_add_reply()
%% @equiv add(Tab, Key, Value, 0, [], DefaultTimeout)
%% @doc Add a Key/Value pair to a brick, failing if Key already exists.

add(Tab, Key, Value) ->
    add(Tab, Key, Value, 0, [], ?FOO_TIMEOUT).

%% @spec (atom(), io_list(), io_list(), prop_list() | finite_timeout())
%%    -> zzz_add_reply()
%% @equiv add(Tab, Key, Value, 0, Flags, DefaultTimeoutOrFlags)
%% @doc Add a Key/Value pair to a brick, failing if Key already exists.

add(Tab, Key, Value, Flags) when is_list(Flags) ->
    add(Tab, Key, Value, 0, Flags, ?FOO_TIMEOUT);
add(Tab, Key, Value, Timeout) when is_integer(Timeout) ->
    add(Tab, Key, Value, 0, [], Timeout).

%% @spec (atom(), io_list(), io_list(), integer(), prop_list(), finite_timeout())
%%    -> zzz_add_reply()
%% @doc Add a Key/Value pair to a brick, failing if Key already exists.

add(Tab, Key, Value, ExpTime, Flags, Timeout) ->
    case do(Tab, [brick_server:make_add(Key, Value, ExpTime, Flags)],
            Timeout) of
        [Res] -> Res;
        Else  -> Else
    end.

%% @spec (atom(), io_list(), io_list())
%%    -> zzz_add_reply()
%% @equiv replace(Tab, Key, Value, 0, [], DefaultTimeout)
%% @doc Replace a Key/Value pair in a brick, failing if Key does not already exist.

replace(Tab, Key, Value) ->
    replace(Tab, Key, Value, 0, [], ?FOO_TIMEOUT).

%% @spec (atom(), io_list(), io_list(), prop_list() | finite_timeout())
%%    -> zzz_add_reply()
%% @equiv replace(Tab, Key, Value, 0, Flags, DefaultTimeoutOrFlags)
%% @doc Replace a Key/Value pair in a brick, failing if Key does not already exist.

replace(Tab, Key, Value, Flags) when is_list(Flags) ->
    replace(Tab, Key, Value, 0, Flags, ?FOO_TIMEOUT);
replace(Tab, Key, Value, Timeout) when is_integer(Timeout) ->
    replace(Tab, Key, Value, 0, [], Timeout).

%% @spec (atom(), io_list(), io_list(), integer(), prop_list(), finite_timeout())
%%    -> zzz_add_reply()
%% @doc Replace a Key/Value pair in a brick, failing if Key does not already exist.

replace(Tab, Key, Value, ExpTime, Flags, Timeout) ->
    case do(Tab,[brick_server:make_replace(Key, Value, ExpTime, Flags)],
            Timeout) of
        [Res] -> Res;
        Else  -> Else
    end.

%% @spec (atom(), io_list(), io_list())
%%    -> zzz_add_reply()
%% @equiv set(Tab, Key, Value, 0, [], DefaultTimeout)
%% @doc Add a Key/Value pair to a brick.

set(Tab, Key, Value) ->
    set(Tab, Key, Value, 0, [], ?FOO_TIMEOUT).

%% @spec (atom(), io_list(), io_list(), prop_list() | finite_timeout())
%%    -> zzz_add_reply()
%% @equiv set(Tab, Key, Value, 0, Flags, DefaultTimeoutOrFlags)
%% @doc Add a Key/Value pair to a brick.

set(Tab, Key, Value, Flags) when is_list(Flags) ->
    set(Tab, Key, Value, 0, Flags, ?FOO_TIMEOUT);
set(Tab, Key, Value, Timeout) when is_integer(Timeout) ->
    set(Tab, Key, Value, 0, [], Timeout).

%% @spec (atom(), io_list(), io_list(), integer(), prop_list(), finite_timeout())
%%    -> zzz_add_reply()
%% @doc Add a Key/Value pair to a brick.

set(Tab, Key, Value, ExpTime, Flags, Timeout) ->
    case do(Tab, [brick_server:make_set(Key, Value, ExpTime, Flags)],
            Timeout) of
        [Res] -> Res;
        Else  -> Else
    end.

%% @spec (atom(), io_list(), io_list())
%%    -> zzz_add_reply()
%% @equiv rename(Tab, Key, NewKey, 0, [], DefaultTimeout)
%% @doc Rename a Key/Value pair to NewKey/Value pair in a brick,
%% failing if Key does not already exist.

rename(Tab, Key, NewKey) ->
    rename(Tab, Key, NewKey, 0, [], ?FOO_TIMEOUT).

%% @spec (atom(), io_list(), io_list(), prop_list() | finite_timeout())
%%    -> zzz_add_reply()
%% @equiv rename(Tab, Key, NewKey, 0, Flags, DefaultTimeoutOrFlags)
%% @doc Rename a Key/Value pair to NewKey/Value pair in a brick,
%% failing if Key does not already exist.

rename(Tab, Key, NewKey, Flags) when is_list(Flags) ->
    rename(Tab, Key, NewKey, 0, Flags, ?FOO_TIMEOUT);
rename(Tab, Key, NewKey, Timeout) when is_integer(Timeout) ->
    rename(Tab, Key, NewKey, 0, [], Timeout).

%% @spec (atom(), io_list(), io_list(), integer(), prop_list(), finite_timeout())
%%    -> zzz_add_reply()
%% @doc Rename a Key/Value pair to NewKey/Value pair in a brick,
%% failing if Key does not already exist.

rename(Tab, Key, NewKey, ExpTime, Flags, Timeout) ->
    case do(Tab,[brick_server:make_rename(Key, NewKey, ExpTime, Flags)],
            Timeout) of
        [Res] -> Res;
        Else  -> Else
    end.

%% @spec (atom(), io_list())
%%    -> zzz_get_reply()
%% @equiv get(Tab, Key, [], DefaultTimeout)
%% @doc Get a Key/Value pair from a brick.

get(Tab, Key) ->
    get(Tab, Key, [], ?FOO_TIMEOUT).

%% @spec (atom(), io_list(), prop_list() | finite_timeout())
%%    -> zzz_get_reply()
%% @equiv get(Tab, Key, [], DefaultTimeoutOrFlags)
%% @doc Get a Key/Value pair from a brick.

get(Tab, Key, Flags) when is_list(Flags) ->
    get(Tab, Key, Flags, ?FOO_TIMEOUT);
get(Tab, Key, Timeout) when is_integer(Timeout) ->
    get(Tab, Key, [], Timeout).

%% @spec (atom(), io_list(), prop_list(), finite_timeout())
%%    -> zzz_get_reply()
%% @doc Get a Key/Value pair from a brick.

get(Tab, Key, Flags, Timeout) ->
    case do(Tab, [brick_server:make_get(Key, Flags)], Timeout) of
        [Res] -> Res;
        Else  -> Else
    end.

%% @spec (atom(), io_list())
%%    -> zzz_delete_reply()
%% @equiv delete(Tab, Key, [], DefaultTimeout)
%% @doc Delete a Key/Value pair from a brick.

delete(Tab, Key) ->
    delete(Tab, Key, [], ?FOO_TIMEOUT).

%% @spec (atom(), io_list(), prop_list() | finite_timeout())
%%    -> zzz_delete_reply()
%% @equiv delete(Tab, Key, [], DefaultTimeoutOrFlags)
%% @doc Delete a Key/Value pair from a brick.

delete(Tab, Key, Flags) when is_list(Flags) ->
    delete(Tab, Key, Flags, ?FOO_TIMEOUT);
delete(Tab, Key, Timeout) when is_integer(Timeout) ->
    delete(Tab, Key, [], Timeout).

%% @spec (atom(), io_list(), prop_list(), finite_timeout())
%%    -> zzz_delete_reply()
%% @doc Delete a Key/Value pair from a brick.

delete(Tab, Key, Flags, Timeout) ->
    case do(Tab, [brick_server:make_delete(Key, Flags)], Timeout) of
        [Res] -> Res;
        Else  -> Else
    end.

%% @spec (atom(), io_list(), integer())
%%    -> zzz_getmany_reply()
%% @equiv getmany(Tab, Key, MaxNum, [], DefaultTimeout)
%% @doc Get many Key/Value pairs from a brick, up to MaxNum.
%%
%% TODO: If you're in a context where you're a simple client, and if
%%       you don't know what chain you're dealing with (because you're
%%       simple client *because* you don't want to know those
%%       details), . . . . then this API doesn't make sense.  You'll
%%       get a list of keys/vals from some chain C1, then when you
%%       call again for the next set of keys/vals you'll probably be
%%       directed by this API to some another chain C2?  Oops.
%%       Or your first call would give you some chain Cx, and if you
%%       strictly request the last key from call 1 in your call 2, you'll
%%       still get chain Cx, but you'll have no way of querying any
%%       other chain?

get_many(Tab, Key, MaxNum) when is_integer(MaxNum) ->
    get_many(Tab, Key, MaxNum, [], ?FOO_TIMEOUT).

%% @spec (atom(), io_list(), integer(), prop_list() | finite_timeout())
%%    -> zzz_getmany_reply()
%% @equiv getmany(Tab, Key, MaxNum, [], DefaultTimeoutOrFlags)
%% @doc Get many Key/Value pairs from a brick, up to MaxNum.

get_many(Tab, Key, MaxNum, Flags) when is_list(Flags) ->
    get_many(Tab, Key, MaxNum, Flags, ?FOO_TIMEOUT);
get_many(Tab, Key, MaxNum, Timeout) when is_integer(Timeout) ->
    get_many(Tab, Key, MaxNum, [], Timeout).

%% @spec (atom(), io_list(), integer(), prop_list(), finite_timeout())
%%    -> zzz_getmany_reply()
%% @doc Get many Key/Value pairs from a brick, up to MaxNum.

get_many(Tab, Key, MaxNum, Flags, Timeout) ->
    case do(Tab, [brick_server:make_get_many(Key, MaxNum, Flags)], Timeout) of
        [Res] -> Res;
        Else  -> Else
    end.

fold_table(Tab, Fun, Acc, NumItems, Flags) ->
    fold_table(Tab, Fun, Acc, NumItems, Flags, 0).

fold_table(Tab, Fun, Acc, NumItems, Flags, MaxParallel) ->
    fold_table(Tab, Fun, Acc, NumItems, Flags, MaxParallel, ?FOO_TIMEOUT).

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

fold_table(Tab, Fun, Acc, NumItems, Flags, MaxParallel, Timeout)
  when is_atom(Tab), is_function(Fun), is_integer(NumItems), is_list(Flags), is_integer(MaxParallel), is_integer(Timeout) ->
    brick_simple_client:fold_table(Tab, Fun, Acc, NumItems, Flags, MaxParallel, Timeout).


%% @doc See {@link fold_key_prefix/9. fold_key_prefix/9}, using
%% default values of `NumItems = 100', `SleepTime = 0', and
%% `Timeout = ?FOO_TIMEOUT', and set the starting key and matching
%% prefix to be the same.

fold_key_prefix(Tab, Prefix, Fun, Acc, Flags) when is_binary(Prefix) ->
    fold_key_prefix(Tab, Prefix, Prefix, Fun, Acc, Flags, 100, 0, ?FOO_TIMEOUT);
fold_key_prefix(Tab, Prefix, Fun, Acc, Flags) ->
    PreBin = gmt_util:bin_ify(Prefix),
    fold_key_prefix(Tab, PreBin, PreBin, Fun, Acc, Flags, 100, 0, ?FOO_TIMEOUT).

%% @spec (atom(), binary(), binary(), fun_arity_2(), term(), proplist(),
%%        integer(), integer(), integer())
%%    -> {ok, term(), integer()} | {error, term(), term()}
%%
%% @doc Convenience function: For a binary prefix `Prefix', fold over all keys
%% in `Tab' starting with `StartKey', sleeping for `SleepTime' milliseconds
%% between iterations and using `Flags0' and `NumItems' as arguments to
%% `brick_simple:get_many()'.
%%
%% The user should not add the `{binary_prefix, X}' property to the
%% `Flags0' argument: it will be automatically managed on behalf of
%% the user.
%%
%% The arguments for the fold fun, fun_arity_2(), should be:
%% <ul>
%% <li> Tuple_From_get_many</li>
%% <li> UserAccumulatorTerm</li>
%% </ul>
%%
%% See the description of `Tuple_From_get_many' in the
%% {@link fold_table/6. fold_table/6} documentation.
%%
%% The return values will be one of
%% <ul>
%% <li> `{ok, Acc::term(), Iterations::integer()}' </li>
%% <li> `{error, GdssError::term(), Acc::term(), Iterations::integer()}' </li>
%% </ul>

fold_key_prefix(Tab, Prefix, StartKey, Fun, Acc, Flags0, NumItems,
                SleepTime, Timeout)
  when is_atom(Tab), is_binary(Prefix), is_binary(StartKey), is_function(Fun),
       is_list(Flags0), is_integer(NumItems), is_integer(SleepTime) ->
    Flags = [{binary_prefix, Prefix}|Flags0],
    GetFun = fun(Key) -> brick_simple:get_many(Tab, Key, NumItems,
                                               Flags, Timeout)
             end,
    fold_key_prefix2(GetFun(StartKey), GetFun, Tab, StartKey, Fun, Acc,
                     SleepTime, 1).

fold_key_prefix2({ok, {Rs, true}}, GetFun, Tab, Key, Fun, Acc, SleepTime, Iters) ->
    Acc2 = lists:foldl(Fun, Acc, Rs),
    LastKey = if
                  Rs =:= [] -> Key;
                  true      -> element(1, lists:last(Rs))
              end,
    timer:sleep(SleepTime),
    fold_key_prefix2(GetFun(LastKey), GetFun, Tab, Key, Fun, Acc2, SleepTime, Iters + 1);
fold_key_prefix2({ok, {Rs, false}}, _GetFun, _Tab, _Key, Fun, Acc, _SleepTime, Iters) ->
    Acc2 = lists:foldl(Fun, Acc, Rs),
    {ok, Acc2, Iters};
fold_key_prefix2(Err, _GetFun, _Tab, _Key, _Fun, Acc, _SleepTime, Iters) ->
    {error, Err, Acc, Iters}.

%% @spec (atom()) -> ok | term().
%% @doc Delete all keys in a table.
clear_table(Tab) when is_atom(Tab) ->
    Fun = fun({_Ch, {K,_TS}}, _Acc) -> ok = brick_simple:delete(Tab, K) end,
    catch brick_simple:fold_table(Tab, Fun, ok, 1000, [witness]).

%% @spec (atom(), do_list())
%%    -> zzz_do_reply() | {error, mumble(), mumble2()}
%% @equiv do(Tab, OpList, [], DefaultTimeout)
%% @doc Send a list of do ops to a brick.

do(Tab, OpList) ->
    do(Tab, OpList, [], ?FOO_TIMEOUT).

%% @spec (atom(), do_list(), prop_list() | finite_timeout())
%%    -> zzz_do_reply() | {error, mumble(), mumble2()}
%% @equiv do(Tab, OpList, [], DefaultTimeoutOrFlags)
%% @doc Send a list of do ops to a brick.

do(Tab, OpList, Timeout)
  when is_list(OpList), is_integer(Timeout) ->
    do(Tab, OpList, [], Timeout).

%% @spec (atom(), do_list(), prop_list(), finite_timeout())
%%    -> zzz_do_reply() | {txn_fail, list()} | {wrong_brick, term()}
%% @doc Send a list of do ops to a brick.
%%
%% Include the current timestamp in the command tuple, to allow the
%% server the option of shedding load if the server is too busy by
%% ignoring requests that are "too old".

do(_Tab, [] = _OpList, _OpFlags, _Timeout) ->
    [];
do(_Tab, [txn] = _OpList, _OpFlags, _Timeout) ->
    [];
do(Tab, OpList, OpFlags, Timeout)
  when is_list(OpList), is_list(OpFlags), is_integer(Timeout) ->
    brick_simple_client:do(Tab, OpList, OpFlags, Timeout).


%%--------------------------------------------------------------------
%%% Internal functions
%%--------------------------------------------------------------------
