% generated: 25 October 1989
% option(s):
%
%   (deriv) ops8
%
%   David H. D. Warren
%
%   symbolic derivative of (x+1)*((^(x,2)+2)*(^(x,3)+3))

%% top:-ops8,log10,divide10.

log10 :- d(log(log(log(log(log(log(log(log(log(log(var(x))))))))))), x, D), print(D).

%% divide10 :- d((((((((quotient(var(x), var(x)))/x)/x)/x)/x)/x)/x)/x)/x,x,_).

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
