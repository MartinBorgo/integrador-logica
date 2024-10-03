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
removeDuplicates([], []).

removeDuplicates([H | T], [H | R]) :-
    not(member(H, T)),
    removeDuplicates(T, R).

removeDuplicates([H | T], R) :-
    member(H, T),
    removeDuplicates(T, R).

% Predicado para implrimir listas de forma más organizada
printList([]).

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

test_all_deductions :-
    linearResolutionwithAllRefutations(c,[[p, not q],[q],[not p],[not c]], Ls),
    format('Testeo para ver si el metodo de encontrar todas las refutaciones anda: ~n'),
    printList(Ls).