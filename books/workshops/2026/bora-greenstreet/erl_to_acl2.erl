% Erlang in ACL2
%
% Copyright (C) Kuter Bora.
%
% License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
%
% Main Author: Kuter Bora
% Contributing Author: Mark Greenstreet

-module(erl_to_acl2).
-export([exprs_to_acl2/1, module_to_acl2/1]).
-export([test_expr/1, test_module/1]).

%% indentation is not supported. What exists now is for debugging purposes.

test_expr(Str) ->
    io:format(
        "Erlang:\n ~p~nACL2:~n~s",
        [get_AST(Str), exprs_to_acl2(Str)]).

test_module(Module) ->
    io:format(
        "Erlang:\n ~p~nACL2:~n~s",
        [get_module(Module), module_to_lisp(get_module(Module))]).


exprs_to_acl2(Str) ->
    exprs_to_lisp(get_AST(Str)).

module_to_acl2(Str) ->
    module_to_lisp(get_module(Str)).


get_module(Str) ->
    {ok, Tokens, _} = erl_scan:string(Str),
    parse_forms(Tokens).

parse_forms([]) -> [];
parse_forms(Tokens) ->
    {FormTokens, Rest} = take_form(Tokens, []),
    case erl_parse:parse_form(FormTokens) of
        {ok, Form} ->
            [Form | parse_forms(Rest)];
        Error ->
            Error
    end.

take_form([{dot, _} = Dot | Rest], Acc) ->
    {lists:reverse([Dot | Acc]), Rest};
take_form([Token | Rest], Acc) ->
    take_form(Rest, [Token | Acc]).

get_AST(Str) ->
    {ok, Tokens, _} = erl_scan:string(Str),
    {ok, AST} = erl_parse:parse_exprs(Tokens),
    AST.

% No support for import of export yet! You will have to configure those manually.
module_to_lisp([{attribute, _, module, Name} | FnDefs]) ->
    LispFnDefs = fn_defs_to_lisp(FnDefs),
    "((attrs (module . "
    ++ atom_to_list(Name) ++ ") (export) (import))"
    ++ "\n (fn-defns\n "
    ++ LispFnDefs
    ++ "))".

fn_defs_to_lisp([]) -> "";
fn_defs_to_lisp([Fn | Tl]) ->
    fn_to_lisp(Fn) ++ "\n" ++ fn_defs_to_lisp(Tl).

fn_to_lisp({function, _, Name, Arity, Cls}) ->
    "(((name . "
    ++ atom_to_list(Name)
    ++ ") (arity . "
    ++ integer_to_list(Arity)
    ++ "))\n"
    ++ clause_list_to_lisp(Cls)
    ++ ")".
    

exprs_to_lisp([]) -> "nil";
exprs_to_lisp([AST]) -> "(" ++ expr_to_lisp(AST) ++ ")";
exprs_to_lisp(ASTs) -> "(" ++ exprs_to_lisp0(ASTs) ++ ")".

exprs_to_lisp0([]) -> "";
exprs_to_lisp0([AST]) -> expr_to_lisp(AST);
exprs_to_lisp0([Hd | Tl]) ->
    expr_to_lisp(Hd) ++ "\n  " ++ exprs_to_lisp0(Tl).

clause_list_to_lisp([]) -> "nil";
clause_list_to_lisp([Cl]) -> clause_to_lisp(Cl);
clause_list_to_lisp([Hd | Tl]) ->
    clause_to_lisp(Hd) ++ clause_list_to_lisp(Tl).

expr_to_lisp(Expr) ->
    case Expr of
        {integer, _, V} ->
            "(:integer " ++ integer_to_list(V) ++ ")";
        {atom, _, V} ->
            "(:atom " ++ atom_to_list(V) ++ ")";
        {string, _, V} ->
            "(:string \"" ++ V ++ "\")";
        {nil, _} ->
            "(:nil)";
        {'fun', _, {clauses, Cls}} ->
            "(:fun\n  (" ++ clause_list_to_lisp(Cls) ++ "))";
        {cons, _, Hd, Tl} ->
            "(:cons "++ expr_to_lisp(Hd) ++ " \n  " ++ expr_to_lisp(Tl) ++ ")";
        {tuple, _, ExprList} ->
            "(:tuple\n  "
                ++ expr_to_lisp(normalize_expr_list(ExprList))
                ++")";
        {var, _, Id} ->
            "(:var " ++ atom_to_list(Id) ++ ")";
        {op, _, Op, Expr1} ->
            "(:unop " ++ atom_to_list(Op) ++ " "
            ++ expr_to_lisp(Expr1) ++ ")";
        {op, _, Op, Expr1, Expr2} ->
            "(:binop " ++ atom_to_list(Op) ++ " "
            ++ expr_to_lisp(Expr1) ++ " "
            ++ expr_to_lisp(Expr2) ++ ")";
        {match, _, Expr1,  Expr2} ->
            "(:match "
            ++ expr_to_lisp(Expr1) ++ " "
            ++ expr_to_lisp(Expr2) ++ ")";
        {'if', _, Cls} ->
            "(:if\n  (" ++ clause_list_to_lisp(Cls) ++ "))";
        {'case', _, Expr1, Cls} ->
            "(:case-of " ++ expr_to_lisp(Expr1)
            ++  "\n  (" ++ clause_list_to_lisp(Cls) ++ "))";
        {call, _, {atom, _, Fn}, Args} ->
            "(:call " ++ atom_to_list(Fn) ++ " "
            ++ expr_to_lisp(normalize_expr_list(Args)) ++ ")";
        {call, _, {remote, _, {atom, _, Mod}, {atom, _, Fn}}, Args} ->
            "(:remote-call " ++ atom_to_list(Mod) ++ " " ++ atom_to_list(Fn) ++ " "
            ++ expr_to_lisp(normalize_expr_list(Args)) ++ ")";
        {call, _, Expr1, Args} ->
            "(:fun-call " ++ expr_to_lisp(Expr1) ++ " "
            ++ expr_to_lisp(normalize_expr_list(Args)) ++ ")";
        {'receive', _, Cls} ->
            "(:receive\n  (" ++ clause_list_to_lisp(Cls) ++ "))";
        _ -> "(:reject)"
    end.

normalize_expr_list([]) -> {nil, 1};
normalize_expr_list([Hd | Tl]) ->
    {cons, 1, Hd, normalize_expr_list(Tl)}.

guards_to_lisp([]) -> "";
guards_to_lisp([Hd | Tl]) ->
    exprs_to_lisp(Hd) ++ guards_to_lisp(Tl).

clause_to_lisp(Cl) ->
    case Cl of
        {clause, _, [], [], Exprs} ->
            "((cases)\n   (guards)\n    "
            ++ "(body " ++ exprs_to_lisp(Exprs) ++ "))\n";
        {clause, _, Cases, [], Exprs} ->
            "((cases " ++ exprs_to_lisp0(Cases) ++ ")"
            ++ "\n   (guards)"
            ++ "\n   (body " ++ exprs_to_lisp0(Exprs) ++ "))\n";
        {clause, _, [], Guards, Exprs} ->
            "((cases)\n   "
            ++ "(guards " ++ guards_to_lisp(Guards) ++ ")\n   "
            ++ "(body " ++ exprs_to_lisp0(Exprs) ++ "))\n";
    
        {clause, _, Cases, Guards, Exprs} ->
            "((cases " ++ exprs_to_lisp0(Cases) ++ ")\n   "
            ++ "(guards " ++ guards_to_lisp(Guards) ++ ")\n   "
            ++ "(body " ++ exprs_to_lisp0(Exprs) ++ "))\n"
    end.