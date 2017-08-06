% Create pseudo-perfect numbers (numbers of the form 2^(p-1)*(2^p - 1), where p is prime.
% Based on perfect.pl from the van Roy benchmark set (https://github.com/SWI-Prolog/bench)

top :-
	findall(C, perfect(C), X),
    print(X),
	ok(X).

ok([ 6,
     28,
     496,
     8128,
     2096128,
     33550336,
     8589869056,
     137438691328,
     35184367894528,
     144115187807420416,
     2305843008139952128,
     9444732965670570950656,
     2417851639228158837784576,
     38685626227663735544086528,
     9903520314282971830448816128,
     40564819207303336344294875201536,
     166153499473114483824745506383331328,
     2658455991569831744654692615953842176,
     10889035741470030830754200461521744560128,
     2787593149816327892690784192460327776944128,
     44601490397061246283066714178813853366747136,
     182687704666362864775460301858080473799697891328,
     46768052394588893382517909811217778170473142550528,
     191561942608236107294793378084303638130997321548169216,
     12554203470773361527671578846336104669690446551334525075456,
     3213876088517980551083924184681057554444177758164088967397376
   ]).

isComposite(X, Y) :-
	N is Y*Y,
	N =< X,
	X mod Y =:= 0.
isComposite(X, Y) :-
	Y < X,
	Y1 is Y + 1,
	isComposite(X, Y1).

% Non-deterministically bind X to every prime number in the given list
selectPrime([X|_], X) :-
	Y is 2,
	X > 1,
	\+ isComposite(X, Y).
selectPrime([_|T], Z) :-
	selectPrime(T, Z).

power(_, 0, 1) :- !.
power(B, P, R) :-
	P1 is P-1,
	power(B, P1, R1),
	R is R1*B.

% compute 2^(p-1)*(2^p-1)
pseudoPerfect(P, R) :-
	power(2, P, X),
	R1 is X-1,
	power(2, P-1, R2),
	R is R1 * R2.

% Non-deterministically bind R to the pseudo-perfect number generated by each prime in the given list
selectPerfect([P|_], R) :-
	pseudoPerfect(P, R).
selectPerfect([_|T], R) :-
	selectPerfect(T, R).


%generate one list of N numbers.
%genList(10, L).
generateList(N, Xs) :- generateList(0, N, Xs).
generateList(N, N, [N]).
generateList(X, N, [X|Xs]) :-
    X < N,
    X1 is X + 1,
    generateList(X1, N, Xs).

%list of N perfect numbers
%perfect(100, C)
perfect(C) :-
	generateList(101, R),
	findall(L, selectPrime(R, L), P),
	selectPerfect(P, C).
