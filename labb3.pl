% Load model, initial state and formula from file.
verify(Input) :-
see(Input), read(T), read(L), read(S), read(F), seen,
check(T, L, S, [], F).



/**
A predicate which accepts a state and either the list of adjacency lists, and returns the specific adjacency list in the last predicate
or accepts the mappings of values and returns a list of values that hold for the given state.
*/

getSublist(Head, [[Head, Tail]| _], Tail):- !.
getSublist(State, [H|T], List):-
getSublist(State, T, List).

/*
The basecase, check if the formula holds for this current state.
*/
check(_, Values, State, _, X) :- 
getSublist(State, Values, Vals), member(X, Vals).

% And
% Check the two formulas independently, both need to hold for the compound formula to be true.
check(Transitions, Values, State, _, and(F, G)) :-
check(Transitions, Values, State, [], F), check(Transitions, Values, State, [], G).

% Or
% Check the two formulas independently, however only one needs to hold for the compound formula to be true.
check(Transitions, Values, State, _, or(F, G)):-
(check(Transitions, Values, State, [], F); check(Transitions, Values, State, [], G)).

% AX
/*
We get the adjacency list of the current state, then we iterate through this adjacency list and check that X holds for each state
immediately reachably throught the current state. This is done in the iterate predicate.
*/
check(Transitions, Values, State, Visited, ax(X)):-
getSublist(State, Transitions, XStates), iterate(Transitions, Values, XStates, Visited, X).

% EX
/*
Get the adjacency list of the current predicate. We then use the member predicate, a hypothetical state, and the adjacency list
to check if any immediately reachable states from the current hold for X. Prolog will try to match the hypothetical state with each of the
members of the adjacency list until it finds one that holds, relying on backtracking.
*/
check(Transitions, Values, State, Visited, ex(X)):-
getSublist(State, Transitions, Neighbours), member(HypState, Neighbours), check(Transitions, Values, HypState, Visited, X).

% AG
/*
The basecase for ag, if we are checking a state we have already reached, this recursive thread can terminate successfully. Success occurs when
each recursive thread terminates successfully.
*/
check(_, _, State, Visited, ag(_)):- member(State, Visited), !.

/*
The first thing we do is check the current state, then we add it to the list of visited states. We then use the ax predicate to check if ag(x)
holds for every next state.
*/
check(Transitions, Values, State, Visited, ag(X)):-
check(Transitions, Values, State, [], X), check(Transitions, Values, State, [State|Visited], ax(ag(X))).

% EG
% Similar to above, however there is only one recursive thread that needs to be satisfied, because we use ex instead of ax.
check(_, _, State, Visited, eg(_)):- member(State, Visited), !.

% Similar to ag, however, instead of checking whether eg holds for all of the current states neighbours, we use ex to check if it holds for at least one.
check(Transitions, Values, State, Visited, eg(X)):-
check(Transitions, Values, State, [], X), getSublist(State, Transitions, Neighbours), member(HypState, Neighbours), check(Transitions, Values, HypState, [State|Visited], eg(X)).


% EF
% The basecase is if we find a state where x is satisfied somewhere in the future, i.e. a state we have not yet visited.
check(Transitions, Values, State, Visited, ef(X)):-
not(member(State, Visited)), check(Transitions, Values, State, [], X).

/*
First we make sure that we have not yet visited the current state, then we add it to the states visited, then we check whether or not
any states reachable from the current state have a state where X holds in the future.
*/
check(Transitions, Values, State, Visited, ef(X)):-
not(member(State, Visited)), getSublist(State, Transitions, Neighbours), member(HypState, Neighbours), check(Transitions, Values, HypState, [State|Visited], ef(X)).


% AF
%Again, the basecase is when we find a state where X holds. We check that we have not visited the state so we guarantee that the program terminates.

check(Transitions, Values, State, Visited, af(X)):-
not(member(State, Visited)), check(Transitions, Values, State, [], X).

%Same as above, except we check whether it holds for all of the immediately reachable states from the current state.
check(Transitions, Values, State, Visited, af(X)):-
not(member(State, Visited)), check(Transitions, Values, State, [State|Visited], ax(af(X))).


% The negation of the basecase

check(_, Values, State, _, neg(X)) :- 
getSublist(State, Values, Vals), not(member(X, Vals)).



%A predicate used by ax, we iterate through all adjacent states and check whether x holds for all of them.
iterate(_, _, [], _, _).
iterate(Transitions, Values, [State|XState], Visited, X):-
check(Transitions, Values, State, Visited, X), !, iterate(Transitions, Values, XState, Visited, X).