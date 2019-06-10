/**
The verify predicate takes an input file and 
stores the premises, the goal we wish to prove, and
the proof lines into three variables. It then sends these 3
variables to the startpoint of the proof checking, valid_proof.
*/
verify(InputFileName) :- see(InputFileName),
read(Prems), read(Goal), read(Proof),
seen, valid_proof(Prems, Goal, Proof).


/**
Predicate for updating list of proofs checked
*/
addList(List1, Element, [Element|List1]).


updateList([Element|List1], Element).
updateList(List1, Element):- !,
updateList([Element|List1], Element),!.


/**
A predicate which copies list 1 to list 2
*/
copyList([],[]).
copyList([H|T1],[H|T2]) :- copyList(T1,T2).

/**
starts by checking if the last line of the
proof is the same as the goal. Essentially it checks that
the proof somehow ends up with the desired result. Also checks that the proof sequence is correct.
*/
valid_proof(Prems, Goal, Proof):-
check_goal(Goal, Proof), check_proof(Proof, []).

/**
Check that the goal is the same as the last line of proofs.
*/
check_goal(G, Proof):-
findLastProof(Proof, X), G = X, !.

/**
Iterate through proof until last line is reached, return the proof sequence in X.
*/
findLastProof([[_, Last, _]|[]], Last).
findLastProof([First|Tail], X):-
findLastProof(Tail, X).

/**
Iterate through each line of proofs until we reach end, checking each line as we pass through it and
adding each checked line of proof to a list we will use to check our following lines against.
*/
check_proof([], _).
check_proof([H|T], CheckedProof):-
check_line(H, CheckedProof), addList(CheckedProof, H, NewCheckedProof), check_proof(T, NewCheckedProof).



/**
CHECKING THE VALIDITY OF EACH LINE (EXCLUDING BOXES)
*/


/**
If the line of proof check_line is called with is a premise, we check that it is a member of the list of premises.
*/
check_line([_, P, premise],_):-!,
member(P, Prems), !.


/**
If the line of proof check_line is called with is derived using and elimination, we check that the derived element
exists anded with some other element on the given line in our already checked lines.
*/
check_line([_, P, andel1(Line)], CheckedProof):-!,
member([Line, and(P, _), _], CheckedProof), !.

check_line([_, P, andel2(Line)], CheckedProof):-!,
member([Line, and(_, P), _], CheckedProof), !.

check_line([_, P, copy(Line)], CheckedProof):-!,
member([Line, P, _], CheckedProof), !.

check_line([_, and(X, Y), andint(Line1, Line2)], CheckedProof):-!,
member([Line1, X, _], CheckedProof), member([Line2, Y, _], CheckedProof), write("andint performed").

check_line([_, or(X, _), orint1(Line)], CheckedProof):-!,
member([Line, X, _], CheckedProof), !.

check_line([_, or(_, Y), orint2(Line)], CheckedProof):- !,
member([Line, Y, _], CheckedProof), !.

check_line([_, P, impel(Line1, Line2)], CheckedProof):-!,
member([Line1, P1, _], CheckedProof),!, member([Line2, imp(P1, P), _], CheckedProof),!.

check_line([_, neg(neg(P)), negnegint(Line)], CheckedProof):-!,
member([Line, P, _], CheckedProof), !.

check_line([_, P, negnegel(Line)], CheckedProof):-!,
member([Line, neg(neg(P)), _], CheckedProof),!.

check_line([_, neg(P), mt(Line1, Line2)], CheckedProof):-!,
member([Line1, imp(P, Q), _], CheckedProof), !, member([Line2, neg(Q), _], CheckedProof), !.

check_line([_, or(P, neg(P)), lem], CheckedProof):-!,
true, !.

check_line([[Startline, Assumption, assumption]|Restofbox], CheckedProof):-!,
copyList(CheckedProof, TemporaryCheckedProof), updateList(CheckedProof, [Startline, Assumption, assumption]), check_box([[Startline, Assumption, assumption]|Restofbox], TemporaryCheckedProof, CheckedProof).

check_line([_, P, contel(Line)], CheckedProof):-!,
member([Line, cont, _], CheckedProof), !.

check_line([_, cont, negel(Line1, Line2)], CheckedProof):-!,
member([Line1, P, _], CheckedProof), member([Line2, neg(P), _], CheckedProof), !.

/**
BOX TYPE SHIT BELOW
*/

check_line([_, imp(P, Q), impint(Line1, Line2)], CheckedProof):-!,
findBox(Line1, Line2, CheckedProof, [Line1, P, assumption], [Line2, Q, _]).


check_line([_, Assumption, assumption], CheckedProof):-!,
true.

check_line([_, P, pbc(Line1, Line2)], CheckedProof):-!,
findBox(Line1, Line2, CheckedProof, [Line1, neg(P), assumption], [Line2, cont, _]).

check_line([_, X, orel(Line1, Line2, Line3, Line4, Line5)], CheckedProof):-!,
member([Line1, or(P, Q), _], CheckedProof), findBox(Line2, Line3, CheckedProof, [Line2, P, assumption], [Line3, X, _]),
findBox(Line4, Line5, CheckedProof, [Line4, Q, assumption], [Line5, X, _]).

check_line([_, P, negint(Line1, Line2)], CheckedProof):-!,
findBox(Line1, Line2, CheckedProof, [Line1, neg(P), assumption], [Line2, cont, _]).


/**
check the validity line by line inside the box by sending each line to check_line. After we are done, the whole box is added to checked proof.
*/
check_box([], List, List2):- true.
check_box([Head|[]], TemporaryCheckedProof, [H|CheckedProof]).
check_box([H|T], TemporaryCheckedProof, CheckedProof):- !,
check_line(H, TemporaryCheckedProof), addList(TemporaryCheckedProof, H, NewCheckedProof), check_box(T, NewCheckedProof, CheckedProof).

findBox(Line1, Line2, [[Line1, Assumption, assumption]|Tail], [Line1, Assumption, assumption], Lastline).
findBox(Line1, Line2, [H|T], Firstline, Lastline):- !,
getLast(Line2, Tail, Lastline),!, findBox(Line1, Line2, [[Line1, Assumption, assumption]|Tail], [Line1, Assumption, assumption], Lastline), !.

getLast(Line2, [Head|[]], Head).
getLast(Line2, [H|T], Lastline):-
getLast(Line2, T, Lastline).





