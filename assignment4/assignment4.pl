/* YOUR CODE HERE (Prolem 1, delete the following line) */
/*range(S, E, S).
range(P, S, S).*/
range(P, E, S) :- S >= P, S =< E.

?- range(1,2,2).
?- not(range(1,2,3)).

/* YOUR CODE HERE (Prolem 2, delete the following line) */
reverseL([], []).
reverseL([H | T], V) :- reverseL(T, RevT), append(RevT, [H], V).

?- reverseL([],X).
?- reverseL([1,2,3],X).
?- reverseL([a,b,c],X).

/* YOUR CODE HERE (Prolem 3, delete the following line) */
/*memberL(X, []) :- false.*/
memberL(X, [H | T]) :- X = H; memberL(X, T).

?- not(memberL(1, [])).
?- memberL(1,[1,2,3]).
?- not(memberL(4,[1,2,3])).
?- memberL(X, [1,2,3]).

/* YOUR CODE HERE (Prolem 4, delete the following line) */
zip([], [], []).
zip([_ | _], [], []).
zip([], [_ | _], []).

zip([Xh | Xt], [Yh | Yt], [Xh-Yh | Zt]) :- zip(Xt, Yt, Zt).

?- zip([1,2],[a,b],Z).
?- zip([a,b,c,d], [1,X,y], Z).
?- zip([a,b,c],[1,X,y,z], Z).
?- length(A,2), length(B,2), zip(A, B, [1-a, 2-b]).

/* YOUR CODE HERE (Prolem 5, delete the following line) */
in_sort(Ls, S) :- isort(Ls, [], S).
isort([], Acc, Acc).
isort([H | T], Acc, S) :- insert(H, Acc, NewAcc), isort(T, NewAcc, S).

insert(X, [Y | T], [Y | NT]) :- X > Y, insert(X, T, NT).
insert(X, [Y | T], [X, Y | T]) :- X =< Y.
insert(X, [], [X]).

?- insert(3, [2,4,5], L).
?- insert(3, [1,2,3], L).
?- not(insert(3, [1,2,4], [1,2,3])).
?- insert(3, L, [2,3,4,5]).
?- insert(9, L, [1,3,6,9]).
?- insert(3, L, [1,3,3,5]).

/* YOUR CODE HERE (Prolem 6, delete the following line) */
rmv_member(_, [], []).
rmv_member(X, [X | Xt], Y) :- rmv_member(X, Xt, Y).
rmv_member(X, [T | Xt], Y) :- rmv_member(X, Xt, Yt), append([T], Yt, Y).

remove_duplicates([], []).
remove_duplicates([X | Y], Z) :- rmv_member(X, Y, Yt), remove_duplicates(Yt, Zt), append([X], Zt, Z).

?- remove_duplicates([1,2,3,4,2,3],X).
?- remove_duplicates([1,4,5,4,2,7,5,1,3],X).
?- remove_duplicates([], X).

/* YOUR CODE HERE (Prolem 7, delete the following line) */
intersectionL(_, [], []).
intersectionL([], _, []).
intersectionL([H | T1], L2, [H | T3]) :- memberL(H, L2), intersectionL(T1, L2, T3).
intersectionL([_ | T1], L2, L3) :- intersectionL(T1, L2, L3).
?- intersectionL([1,2,3,4],[1,3,5,6],[1,3]).
?- intersectionL([1,2,3,4],[1,3,5,6],X).
?- intersectionL([1,2,3],[4,3],[3]).

/* YOUR CODE HERE (Prolem 8, delete the following line) */
prefix(P,L) :- append(P,_,L).
suffix(S,L) :- append(_,S,L).

partition([L], [L], []).
partition(L,P,S) :- 
    length(L, N),
    PrefL is div(N, 2),
    SecL is N - PrefL,
    length(P, PrefL),
    length(S, SecL),
    append(P, S, L).
?- partition([a],[a],[]).
?- partition([1,2,3],[1],[2,3]).
?- partition([a,b,c,d],X,Y).

/* YOUR CODE HERE (Prolem 9, delete the following line) */
merge([], [], []),
merge([], L2, L2).
merge(L1, [], L1).

merge([H1 | T1], [H2 | T2], Z) :- H1 < H2, merge(T1, [H2 | T2], Z1), append([H1], Z1, Z).
merge(L1, [H2 | T2], Z) :- merge(L1, T2, Z1), append([H2], Z1, Z).

?- merge([],[1],[1]).
?- merge([1],[],[1]).
?- merge([1,3,5],[2,4,6],X).

/* YOUR CODE HERE (Prolem 10, delete the following line) */
mergesort([], []).
mergesort([X], [X]).

mergesort([X,Y|Lt, S]:-
    partition([X,Y|Lt], L1, L2),
    mergesort(L1, S1),
    mergesort(L2, S2),
    merge(S1,S2,S).

?- mergesort([3,2,1],X).
?- mergesort([1,2,3],Y).
?- mergesort([],Z).
