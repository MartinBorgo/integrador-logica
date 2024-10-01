%Predicado para Limpiar la consola
clear :- 
    (current_prolog_flag(windows, true) -> shell('cls') ; shell('clear')).

% Definición de operadores
:- op(900, xfy, or).
:- op(800, fy, not).

% ----------------- Utils ----------------- %

% Predicado que me ayuda a saber si un literal esta negado
negativeLiteral(not Literal) :- 
    not(compound(Literal)).

% Predicado para saber si dos literales son complementarios
complement(X, not X).
complement(not X, X).

% Predicado para encontrar un par complementario en dos listas de literales.


% ----------------- Parser ----------------- %

% Predicado para dividir una disyunción en una lista
toList(Left or Right, [Left | Rest]) :-
    toList(Right, Rest).

toList(Left or Right, [Left | Rest]) :-
    negativeLiteral(Left),
    toList(Right, Rest).

toList(Literal, [Literal]) :-
    not(compound(Literal)), !.

toList(not Literal, [not Literal]) :-
    not(compound(Literal)), !.

% Predicado para pasar una lista de disyunciones a una lista de listas de literales
listOfList([], []) :- !.

listOfList([Disjunction | List], [LiteralList | Result]) :- 
    toList(Disjunction, LiteralList),
    listOfList(List, Result).

% ----------------- Resolvente ----------------- %

% Predicado que aplica la resolución
resolution([FirsLiteral | FirsClause], SecondClause, Resolvent) :-
    select(not FirsLiteral, SecondClause, Elimination),
    union(FirsClause, Elimination, Resolvent).

resolution([not FirsLiteral | FirsClause], SecondClause, Resolvent) :-
    select(FirsLiteral, SecondClause, Elimination),
    union(FirsClause, Elimination, Resolvent).

resolution([FirsLiteral | FirsClause], SecondClause, Resolvent) :-
    resolution(FirsClause, SecondClause, IntermediateResult),
    union([FirsLiteral], IntermediateResult, Resolvent). % Esto es por si se llega a repetir el FirstElement


% ----------------- Prueba ----------------- %
test1 :- 
    toList(a or b or c or not h, Ls),
    format('Testeo del predicado para converitr disyunciones en listas: '), 
    write(Ls).

test2 :-
    listOfList([a or b or not c, b or not a or not h], Ls),
    format('Testeo del predicado para convertir listas de disyunciones en listas de listas: '), 
    write(Ls).

test3 :-
    resolution([a, not b], [d, b, not a], C),
    format('Testeo del predicado resolvente: '), 
    write(C).