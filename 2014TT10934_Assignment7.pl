match(X,[X|_]).
match(X,[_|Ys]):- match(X,Ys).
% constant types
hastype(_, intconst(_), "int").
hastype(_, strconst(_), "str").
hastype(_, biconst(_), "bool").
% assumption rule
hastype(Gamma, v(E), T):- match(p(E,T),Gamma).
% implies rule (elimination and introduction)
hastype(Gamma, app(E1,E2), T):- hastype(Gamma,E1,arrow(T1, T)),hastype(Gamma,E2,T1).
hastype(Gamma, abs(X,E),arrow(T1,T2)):- hastype([p(X,T1)|Gamma],E,T2).
% and rules
hastype(Gamma, pair(E1,E2), star(T1,T2)):- hastype(Gamma,E1,T1),hastype(Gamma,E2,T2).
hastype(Gamma, projl(E), T1):- hastype(Gamma,E,star(T1,_)).
hastype(Gamma, projr(E), T2):- hastype(Gamma,E,star(_,T2)).
% or rules
hastype(Gamma, inl(E),plus(T1,_)):- hastype(Gamma,E,T1).
hastype(Gamma, inr(E),plus(_,T2)):- hastype(Gamma,E,T2).
hastype(Gamma, case(E0,inl(X),E1,inr(Y),E2), T3):- hastype(Gamma, E0, plus(T1, T2)), hastype([p(X,T1)|Gamma],E1,T3), hastype([p(Y,T2)|Gamma],E2,T3).
% extended pair rules
hastype(Gamma, extendedpair([E|[]]),T):- hastype(Gamma, E, T).
hastype(Gamma, extendedpair([E|Es]), star(T1,T2)):- hastype(Gamma, E, T1), hastype(Gamma,extendedpair(Es),T2).
% extended projection rules
hastype(Gamma, extendedproj([E|_],1), T) :-  hastype(Gamma, E, star(T,_)).
hastype(Gamma, extendedproj([_|Es],N), T):- N>1, N1 is N-1, hastype(Gamma, extendedproj(Es,N1),T).
% not rule
hastype(G,nega(E1),T):-hastype(G,E1,T).
% sum rule
hastype(G, add(E1,E2), T):- hastype(G,E1,T),hastype(G,E2,T).



