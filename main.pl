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

% Preficado para saber si es refutable un conjunto de clausulas
isRefutable([]).

% Devuelve el primer elemento de una lista
first([Head | _], Head).

% Predicado para eliminar los elementos repretidos
removeDuplicates([], []) :- !.
removeDuplicates([H | T], [H | R]) :-
    not(member(H, T)),
    removeDuplicates(T, R).

removeDuplicates([H | T], R) :-
    member(H, T),
    removeDuplicates(T, R).

% Predicado para dar formato a cada paso de deducción
formatStep([A, B, R]) :-
    format('Resolución ==> ~|~t~w~t~15+ |>> ~|~t~w~t~15+ ---> ~|~t~w~t~5+~n', [A, B, R]).

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

% Predicado para implrimir listas de forma más organizada
printList([]) :- !.
printList([H | T]) :-
    writeln(H),
    printList(T).

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
resolution(FirsClause, SecondClause, Resolvent) :-
    select(Literal, FirsClause, RestA),
    complement(Literal, OppositeLiteral),
    select(OppositeLiteral, SecondClause, RestB),
    union(RestA, RestB, Resolvent).

% ----------------- Resolución Lineal ----------------- %

% Predicado recursivo para aplicar la resolución lineal y obtener los pasos
resolve(Step, DeductionSet, [[Step, Clause, Resolvent]]) :-
    member(Clause, DeductionSet),
    resolution(Step, Clause, Resolvent),
    isRefutable(Resolvent).

resolve(Step, DeductionSet, [[Step, Clause, Resolvent] | NextSteps]) :-
    member(Clause, DeductionSet),
    resolution(Step, Clause, Resolvent),
    not(isRefutable(Resolvent)),
    not(member(Resolvent, DeductionSet)),
    resolve(Resolvent, [Resolvent | DeductionSet], NextSteps).

resolve(Step, DeductionSet, [[Step, Clause, Resolvent] | NextSteps]) :-
    member(Clause, DeductionSet),
    resolution(Step, Clause, Resolvent),
    not(isRefutable(Resolvent)),
    resolve(Resolvent, DeductionSet, NextSteps).

% Predicado para poder econtrar todas las soluciones posibles (o eso intenta)
findAllRefutations(DeductionSet, AllRefutations) :-
    findall(DeductionSteps, (
        member(Top, DeductionSet),
        resolve(Top, DeductionSet, DeductionSteps)
    ), AllRefutationsRaw),
    removeDuplicates(AllRefutationsRaw, AllRefutations).

% Predicado principal donde se empieza a hacer la resolución lineal
linearResolution(not Proof, DeductionSet, DeductionSteps) :-
    append(DeductionSet, [[Proof]], NewDeductionSet),
    first(NewDeductionSet, Top),
    resolve(Top, NewDeductionSet, DeductionSteps).

linearResolution(Proof, DeductionSet, DeductionSteps) :-
    append(DeductionSet, [[not Proof]], NewDeductionSet),
    first(NewDeductionSet, Top),
    resolve(Top, NewDeductionSet, DeductionSteps).

% Predicado para encontrar todas las posibles deducciones en el conjunto de deducción
linearResolutionwithAllRefutations(not Proof, DeductionSet, DeductionSteps) :-
    append(DeductionSet, [[Proof]], NewDeductionSet),
    findAllRefutations(NewDeductionSet, DeductionSteps).

linearResolutionwithAllRefutations(Proof, DeductionSet, DeductionSteps) :-
    append(DeductionSet, [[not Proof]], NewDeductionSet),
    findAllRefutations(NewDeductionSet, DeductionSteps).

% [[[p, q], [not q], [p]], [[p], [not p], []]]
% ----------------- Correr el commando ----------------- %

todasLasRefutaciones :-
    linearResolutionwithAllRefutations(c,[[p, not q],[q],[not p],[not c]], Ls),
    generalParser(Ls, Resturn),
    format('Todas las refutaciones posibles por Resolución Lineal: ~n'),
    printAllDeductions(Resturn).

refutar :-
    linearResolution(c,[[p, not q],[q],[not p],[not c]], Ls),
    deductionParser(Ls, Data),
    format('Refutación por Resolución Lineal: ~n'),
    printDeduction(Data).