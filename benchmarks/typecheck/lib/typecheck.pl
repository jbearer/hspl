wellTyped(Gamma, variable(X), T) :- member([X, T], Gamma).

wellTyped(_, intLiteral(Expr), intType) :- integer(Expr).

wellTyped(_, boolLiteral(true), boolType).
wellTyped(_, boolLiteral(false), boolType).

wellTyped(Gamma, lambda(X, Expr), funcType(Arg, Result)) :-
    wellTyped([[X, Arg] | Gamma], Expr, Result).

wellTyped(Gamma, app(F, X), T) :-
    wellTyped(Gamma, F, funcType(Arg, T)),
    wellTyped(Gamma, X, Arg).

wellTyped(Gamma, let(X, LetExpr, InExpr), T) :-
    wellTyped(Gamma, LetExpr, LetT),
    wellTyped([[X, LetT] | Gamma], InExpr, T).

wellTyped(Gamma, if(Cond, True, False), T) :-
    wellTyped(Gamma, Cond, boolType),
    wellTyped(Gamma, True, T),
    wellTyped(Gamma, False, T).

wellTyped(Gamma, preOp(negate, Expr), intType) :-
    wellTyped(Gamma, Expr, intType).
wellTyped(Gamma, preOp(not, Expr), boolType) :-
    wellTyped(Gamma, Expr, boolType).

wellTyped(Gamma, binOp(L, Op, R), intType) :-
    member(Op, [plus, minus, times, divide]),
    wellTyped(Gamma, L, intType),
    wellTyped(Gamma, R, intType).
wellTyped(Gamma, binOp(L, Op, R), boolType) :-
    member(Op, [and, or]),
    wellTyped(Gamma, L, boolType),
    wellTyped(Gamma, R, boolType).

wellTyped(Expr, Type) :- wellTyped([], Expr, Type).
