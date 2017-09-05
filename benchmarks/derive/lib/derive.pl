% Compute the symbolic derivative of simple algebraic expressions.
% Based on derive.pl from the van Roy benchmark set (https://github.com/SWI-Prolog/bench)

d(sum(U, V), X, sum(DU, DV)) :- !,
    d(U, X, DU),
    d(V, X, DV).

d(difference(U, V), X , difference(DU, DV)) :- !,
    d(U, X, DU),
    d(V, X, DV).

d(product(U, V), X , sum(product(DU, V), product(U, DV))) :- !,
    d(U, X, DU),
    d(V, X, DV).

d(quotient(U, V), X, quotient(difference(product(DU, V), product(U, DV)), power(V, 2))) :- !,
    d(U, X, DU),
    d(V, X, DV).

d(power(U, N), X, product(DU, product(const(N), power(U, N1)))) :- !,
    integer(N),
    N1 is N-1,
    d(U, X, DU).

d(exp(U), X, product(exp(U), DU)) :- !,
    d(U, X, DU).

d(log(U), X, quotient(DU, U)) :- !,
    d(U, X, DU).

d(var(X), X, const(1)) :- !.

d(_, _, const(0)).
