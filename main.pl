%Predicado para Limpiar la consola
clear :- 
    (current_prolog_flag(windows, true) -> shell('cls') ; shell('clear')).

% Definición de operadores
:- op(900, xfy, or).
:- op(800, fy, not).

% ----------------- Utils ----------------- %

% Predicado que me ayuda a saber si un literal esta negado
negativeLiteral(not Literal) :- atom(Literal).

% Predicado para saber si dos literales son complementarios
complement(X, not X).
complement(not X, X).

% Preficado para saber si es refutable un conjunto de clausulas
isRefutable([]).

% Predicado para eliminar los elementos repretidos
removeDuplicates([], []) :- !.
removeDuplicates([H | T], [H | R]) :-
    not(member(H, T)),
    removeDuplicates(T, R).

removeDuplicates([H | T], R) :-
    member(H, T),
    removeDuplicates(T, R).

% ----------------- Prints ----------------- %

% Predicado para dar formato a cada paso de deducción
formatStep([A, B, R]) :-
    format('Resolvente ==> ~|~t~w~t~15+ |>> ~|~t~w~t~15+ ---> ~|~t~w~t~5+~n', [A, B, R]).

% Predicado para imprimir un procedimiento de deducción.
printDeduction([]) :- !.
printDeduction([FirstStep | DeductionStep]) :-
    formatStep(FirstStep),
    printDeduction(DeductionStep).

% Este predicado hace lo mismo que el anterior pero para todas las refutaciones posibles.
printAllDeductions([]) :- !.
printAllDeductions([FirstDeduction | AllDeductions]) :-
    printDeduction(FirstDeduction),
    format('~n~|~t+ ---------------- x ---------------- +~t~60+~n~n'),
    printAllDeductions(AllDeductions).

% ----------------- ClauseParser ----------------- %

% Predicado para dividir una disyunción en una lista
toList(Left or Right, [Left | Rest]) :- toList(Right, Rest).

toList(Left or Right, [Left | Rest]) :-
    negativeLiteral(Left),
    toList(Right, Rest).

toList(Literal, [Literal]) :- atom(Literal), !.
toList(not Literal, [not Literal]) :- atom(Literal), !.

% Predicado para pasar una lista de disyunciones a una lista de listas de literales
toListOfLists([], []) :- !.
toListOfLists([Disjunction | List], [LiteralList | Result]) :- 
    toList(Disjunction, LiteralList),
    toListOfLists(List, Result).

% ----------------- ListParser ----------------- %

% Predicado para parsear una lista de Literales en una clausula
toClause([], box) :- !.
toClause([Head | []], Head) :- !.
toClause([Head | LiteralList], Head or Clause) :-
    toClause(LiteralList, Clause).

% Predicado para convertir las lista de lista de literales en un lista de clausulas
listOfClauses([], []) :- !.
listOfClauses([LiteralList | ListOfLists], [Clause | ClauseList]) :-
    toClause(LiteralList, Clause),
    listOfClauses(ListOfLists, ClauseList).

% Predicado para parsear los datos de una lista que contiene todos los pasos para la refutación
deductionParser([], []) :- !.
deductionParser([FirsStep | DeductionSteps], [ClauseList | ParsedData]) :-
    listOfClauses(FirsStep, ClauseList),
    deductionParser(DeductionSteps, ParsedData).

% Predicado que hace lo mismo que el anterior pero para la lista de todas las posibles refutaciones
generalParser([], []) :- !.
generalParser([FirstDeduction | AllDeductions], [ParsedDeduction | ParsedData]) :-
    deductionParser(FirstDeduction, ParsedDeduction),
    generalParser(AllDeductions, ParsedData).

% ----------------- Resolvente ----------------- %

% Predicado para realizar la resolvente
resolving(FirsClause, SecondClause, Resolvent) :-
    select(Literal, FirsClause, RestA),
    complement(Literal, OppositeLiteral),
    select(OppositeLiteral, SecondClause, RestB),
    union(RestA, RestB, Resolvent).

% ----------------- Resolución Lineal ----------------- %

% Predicado recursivo para aplicar la resolución lineal y obtener los pasos
linearResolution(Step, DeductionSet, [[Step, Clause, Resolvent]]) :-
    member(Clause, DeductionSet),
    resolving(Step, Clause, Resolvent),
    isRefutable(Resolvent).

linearResolution(Step, DeductionSet, [[Step, Clause, Resolvent] | NextSteps]) :-
    member(Clause, DeductionSet),
    resolving(Step, Clause, Resolvent),
    not(isRefutable(Resolvent)),
    not(member(Resolvent, DeductionSet)),
    linearResolution(Resolvent, [Resolvent | DeductionSet], NextSteps).

linearResolution(Step, DeductionSet, [[Step, Clause, Resolvent] | NextSteps]) :-
    member(Clause, DeductionSet),
    resolving(Step, Clause, Resolvent),
    not(isRefutable(Resolvent)),
    linearResolution(Resolvent, DeductionSet, NextSteps).

% Predicado para poder econtrar todas las soluciones posibles (o eso intenta)
findAllRefutations(DeductionSet, AllRefutations) :-
    findall(DeductionSteps, (
        member(Top, DeductionSet),
        linearResolution(Top, DeductionSet, DeductionSteps)
    ),AllRefutationsRaw),
    removeDuplicates(AllRefutationsRaw, AllRefutations).

% ----------------- Refutacion/es ----------------- %

% Predicado principal donde se empieza a hacer la resolución lineal
refutation(not Proof, DeductionSet, DeductionSteps) :-
    append(DeductionSet, [Proof], NewDeductionSet),
    toListOfLists(NewDeductionSet, ParsedSet),
    member(Top, ParsedSet),
    linearResolution(Top, ParsedSet, DeductionSteps).

refutation(Proof, DeductionSet, DeductionSteps) :-
    append(DeductionSet, [not Proof], NewDeductionSet),
    toListOfLists(NewDeductionSet, ParsedSet),
    member(Top, ParsedSet),
    linearResolution(Top, ParsedSet, DeductionSteps).

% Predicado para encontrar todas las posibles deducciones en el conjunto de deducción
allRefutations(not Proof, DeductionSet, DeductionSteps) :-
    append(DeductionSet, [Proof], NewDeductionSet),
    toListOfLists(NewDeductionSet, ParsedSet),
    findAllRefutations(ParsedSet, DeductionSteps).

allRefutations(Proof, DeductionSet, DeductionSteps) :-
    append(DeductionSet, [not Proof], NewDeductionSet),
    toListOfLists(NewDeductionSet, ParsedSet),
    findAllRefutations(ParsedSet, DeductionSteps).

% [[[p, q], [not q], [p]], [[p], [not p], []]]
% ----------------- Correr el commando ----------------- %

todasLasRefutaciones :-
    allRefutations(c,[p or not q, q, not p, not c], Ls),
    generalParser(Ls, Resturn),
    format('Todas las refutaciones posibles por Resolución Lineal: ~n'),
    printAllDeductions(Resturn).

refutar :-
    refutation(c,[p or not q, q, not p, not c], Ls),
    deductionParser(Ls, Data),
    format('Refutación por Resolución Lineal: ~n'),
    printDeduction(Data).
