# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2022
# File name: propositions/semantics.py

"""Semantic analysis of propositional-logic constructs."""

from typing import AbstractSet, Iterable, Iterator, Mapping, Sequence, Tuple

from propositions.syntax import *
from propositions.proofs import *
from itertools import *

#: A model for propositional-logic formulas, a mapping from variable names to
#: truth values.
Model = Mapping[str, bool]

def is_model(model: Model) -> bool:
    """Checks if the given dictionary is a model over some set of variable
    names.

    Parameters:
        model: dictionary to check.

    Returns:
        ``True`` if the given dictionary is a model over some set of variable
        names, ``False`` otherwise.
    """
    for key in model:
        if not is_variable(key):
            return False
    return True

def variables(model: Model) -> AbstractSet[str]:
    """Finds all variable names over which the given model is defined.

    Parameters:
        model: model to check.

    Returns:
        A set of all variable names over which the given model is defined.
    """
    assert is_model(model)
    return model.keys()

def evaluate(formula: Formula, model: Model) -> bool:
    """Calculates the truth value of the given formula in the given model.

    Parameters:
        formula: formula to calculate the truth value of.
        model: model over (possibly a superset of) the variable names of the
            given formula, to calculate the truth value in.

    Returns:
        The truth value of the given formula in the given model.

    Examples:
        >>> evaluate(Formula.parse('~(p&q76)'), {'p': True, 'q76': False})
        True

        >>> evaluate(Formula.parse('~(p&q76)'), {'p': True, 'q76': True})
        False
    """
    assert Formula.is_formula(formula)
    assert is_model(model)
    assert formula.variables().issubset(variables(model))
    # Task 2.1
    # Joan
    if is_constant(formula.root):
        if formula.root =='T':
            return True
        elif formula.root == 'F':
            return False
    elif is_variable(formula.root):
        return model[formula.root]
    elif is_unary(formula.root):
        return (not evaluate(formula.first, model))
    elif is_binary(formula.root):
        if formula.root == '&':
            return evaluate(formula.first, model) and evaluate(formula.second, model)
        elif formula.root == '|':
            return evaluate(formula.first, model) or evaluate(formula.second, model)
        elif formula.root == '->':
            if evaluate(formula.first, model) == True and evaluate(formula.second, model) == False:
                return False
            else:
                return True
        elif formula.root == '+':
            return evaluate(formula.first, model) ^ evaluate(formula.second, model) # ^ is the XOR operator in python
        elif formula.root == '<->':
            return not (evaluate(formula.first, model) ^ evaluate(formula.second, model))
        elif formula.root == '-&':
            return not (evaluate(formula.first, model) and evaluate(formula.second, model))
        elif formula.root == '-|':
            return not (evaluate(formula.first, model) or evaluate(formula.second, model))
    # Joan

def all_models(variables: Sequence[str]) -> Iterable[Model]:
    """Calculates all possible models over the given variable names.

    Parameters:
        variables: variable names over which to calculate the models.

    Returns:
        An iterable over all possible models over the given variable names. The
        order of the models is lexicographic according to the order of the given
        variable names, where False precedes True.

    Examples:
        >>> list(all_models(['p', 'q']))
        [{'p': False, 'q': False}, {'p': False, 'q': True}, {'p': True, 'q': False}, {'p': True, 'q': True}]

        >>> list(all_models(['q', 'p']))
        [{'q': False, 'p': False}, {'q': False, 'p': True}, {'q': True, 'p': False}, {'q': True, 'p': True}]
    """
    for v in variables:
        assert is_variable(v)
    # Task 2.2
    # Joan
    # https://docs.python.org/3/library/itertools.html Iterators with itertools
    # https://wiki.python.org/moin/Generators Generators
    # https://www.datacamp.com/tutorial/python-iterators-generators-tutorial
    
    variables = tuple(variables) # if variables is a set, it needs to be a tuple for the generator to work nicely. See test.
    idxs = range(len(variables)) # the range object is iterable
    vals = product({False, True}, repeat=len(variables)) # vals is an iterator
    models = ( { variables[i]:val[i] for i in idxs } for val in vals ) # wrapping in parenthesis makes it a generator
    return models
    # Joan

def truth_values(formula: Formula, models: Iterable[Model]) -> Iterable[bool]:
    """Calculates the truth value of the given formula in each of the given
    models.

    Parameters:
        formula: formula to calculate the truth value of.
        models: iterable over models to calculate the truth value in.

    Returns:
        An iterable over the respective truth values of the given formula in
        each of the given models, in the order of the given models.

    Examples:
        >>> list(truth_values(Formula.parse('~(p&q76)'), all_models(['p', 'q76'])))
        [True, True, True, False]
    """
    # Task 2.3
    # Joan
    for model in models:
        yield evaluate(formula, model)  # generator
    # Joan

def print_truth_table(formula: Formula) -> None:
    """Prints the truth table of the given formula, with variable-name columns
    sorted alphabetically.

    Parameters:
        formula: formula to print the truth table of.

    Examples:
        >>> print_truth_table(Formula.parse('~(p&q76)'))
        | p | q76 | ~(p&q76) |
        |---|-----|----------|
        | F | F   | T        |
        | F | T   | T        |
        | T | F   | T        |
        | T | T   | F        |
    """
    # Task 2.4
    # Joan
    svars = sorted(formula.variables())  # returns a list which can directly go to .join
    print('| ' + ' | '.join(svars) + ' | ' + str(formula) + ' |')
    print('|-' + '-|-'.join(['-'*len(v) for v in svars]) + '-|-' + '-'*len(str(formula)) + '-|')
    for model in all_models(svars):
        print('| ' + ' | '.join([str(model[v])[0] + ' '*(len(v)-1) for v in svars]) + ' | ' + str(evaluate(formula,model))[0] + ' '*len(str(formula)) + '|')
    # Joan

def is_tautology(formula: Formula) -> bool:
    """Checks if the given formula is a tautology.

    Parameters:
        formula: formula to check.

    Returns:
        ``True`` if the given formula is a tautology, ``False`` otherwise.
    """
    # Task 2.5a
    # Joan
    tvals = list(truth_values(formula, all_models(formula.variables())))
    if all(tvals):
        return True
    else:
        return False
    # Joan

def is_contradiction(formula: Formula) -> bool:
    """Checks if the given formula is a contradiction.

    Parameters:
        formula: formula to check.

    Returns:
        ``True`` if the given formula is a contradiction, ``False`` otherwise.
    """
    # Task 2.5b
    # Joan
    tvals = list(truth_values(formula, all_models(formula.variables())))
    if not any(tvals):
        return True
    else:
        return False
    # Joan

def is_satisfiable(formula: Formula) -> bool:
    """Checks if the given formula is satisfiable.

    Parameters:
        formula: formula to check.

    Returns:
        ``True`` if the given formula is satisfiable, ``False`` otherwise.
    """
    # Task 2.5c
    # Joan
    tvals = list(truth_values(formula, all_models(formula.variables())))
    if any(tvals):
        return True
    else:
        return False
    # Joan

def _synthesize_for_model(model: Model) -> Formula:
    """Synthesizes a propositional formula in the form of a single conjunctive
    clause that evaluates to ``True`` in the given model, and to ``False`` in
    any other model over the same variable names.

    Parameters:
        model: model over a nonempty set of variable names, in which the
            synthesized formula is to hold.

    Returns:
        The synthesized formula.
    """
    assert is_model(model)
    assert len(model.keys()) > 0
    # Task 2.6
    # Joan
    monads = [Formula(var) if model[var] else Formula('~', Formula(var)) for var in variables(model)]     
    conjunction = monads[0]
    for i in range(len(monads)-1):
        conjunction = Formula('&', conjunction, monads[i+1])
    return conjunction  

    ## The monads list comprehension above is equivalent to the loop
    # monads = []
    # for var in variables(model):
    #     if model[var] == True:
    #         monads.append(Formula(var))
    #     else:
    #         monads.append(Formula('~', Formula(var)))
    # Joan

def synthesize(variables: Sequence[str], values: Iterable[bool]) -> Formula:
    """Synthesizes a propositional formula in DNF over the given variable names,
    that has the specified truth table.

    Parameters:
        variables: nonempty set of variable names for the synthesized formula.
        values: iterable over truth values for the synthesized formula in every
            possible model over the given variable names, in the order returned
            by `all_models`\ ``(``\ `~synthesize.variables`\ ``)``.

    Returns:
        The synthesized formula.

    Examples:
        >>> formula = synthesize(['p', 'q'], [True, True, True, False])
        >>> for model in all_models(['p', 'q']):
        ...     evaluate(formula, model)
        True
        True
        True
        False
    """
    assert len(variables) > 0
    # Task 2.7
    # Joan
    models = list(all_models(variables))
    values = list(values)
    if not any(values):
        monads = [Formula('&', Formula(var), Formula('~', Formula(var))) for var in variables]
    else:
        monads = [_synthesize_for_model(models[i]) for i in range(len(values)) if values[i]]  

    disjunction = monads[0]
    for i in range(len(monads)-1):
        disjunction = Formula('|', disjunction, monads[i+1])
    return disjunction  
    # Joan

def _synthesize_for_all_except_model(model: Model) -> Formula:
    """Synthesizes a propositional formula in the form of a single disjunctive
    clause that evaluates to ``False`` in the given model, and to ``True`` in
    any other model over the same variable names.

    Parameters:
        model: model over a nonempty set of variable names, in which the
            synthesized formula is to not hold.

    Returns:
        The synthesized formula.
    """
    assert is_model(model)
    assert len(model.keys()) > 0
    # Optional Task 2.8

def synthesize_cnf(variables: Sequence[str], values: Iterable[bool]) -> Formula:
    """Synthesizes a propositional formula in CNF over the given variable names,
    that has the specified truth table.

    Parameters:
        variables: nonempty set of variable names for the synthesized formula.
        values: iterable over truth values for the synthesized formula in every
            possible model over the given variable names, in the order returned
            by `all_models`\ ``(``\ `~synthesize.variables`\ ``)``.

    Returns:
        The synthesized formula.

    Examples:
        >>> formula = synthesize_cnf(['p', 'q'], [True, True, True, False])
        >>> for model in all_models(['p', 'q']):
        ...     evaluate(formula, model)
        True
        True
        True
        False
    """
    assert len(variables) > 0
    # Optional Task 2.9

def evaluate_inference(rule: InferenceRule, model: Model) -> bool:
    """Checks if the given inference rule holds in the given model.

    Parameters:
        rule: inference rule to check.
        model: model to check in.

    Returns:
        ``True`` if the given inference rule holds in the given model, ``False``
        otherwise.

    Examples:
        >>> evaluate_inference(InferenceRule([Formula('p')], Formula('q')),
        ...                    {'p': True, 'q': False})
        False

        >>> evaluate_inference(InferenceRule([Formula('p')], Formula('q')),
        ...                    {'p': False, 'q': False})
        True
    """
    assert is_model(model)
    # Task 4.2
    # Joan
    tas = [evaluate(assumption, model) for assumption in rule.assumptions]
    tc = evaluate(rule.conclusion, model)
    if all(tas) and not tc:
        return False
    else:
        return True
    # Joan

def is_sound_inference(rule: InferenceRule) -> bool:
    """Checks if the given inference rule is sound, i.e., whether its
    conclusion is a semantically correct implication of its assumptions.

    Parameters:
        rule: inference rule to check.

    Returns:
        ``True`` if the given inference rule is sound, ``False`` otherwise.
    """
    # Task 4.3
    # Joan
    return all([evaluate_inference(rule, model) for model in all_models(rule.variables())])
    # Joan
