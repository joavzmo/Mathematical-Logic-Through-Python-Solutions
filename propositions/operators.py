# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2022
# File name: propositions/operators.py

"""Syntactic conversion of propositional formulas to use only specific sets of
operators."""

from propositions.syntax import *
from propositions.semantics import *

def to_not_and_or(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'~'``, ``'&'``, and ``'|'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'~'``, ``'&'``, and
        ``'|'``.
    """
    # Task 3.5
    # Joan
    substitution_map = {'T': Formula.parse('(p|~p)'),
                        'F': Formula.parse('(p&~p)'),
                        '->': Formula.parse('(~p|q)'),
                        '+': Formula.parse('((p&~q)|(~p&q))'),
                        '<->': Formula.parse('((p&q)|(~p&~q))'),
                        '-&': Formula.parse('~(p&q)'),
                        '-|': Formula.parse('~(p|q)')}
    
    return Formula.substitute_operators(formula, substitution_map)
    # Joan

def to_not_and(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'~'`` and ``'&'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'~'`` and ``'&'``.
    """
    # Task 3.6a
    # Joan
    formula = to_not_and_or(formula)
    substitution_map = {'|': Formula.parse('~(~p&~q)')} # De Morgan law
    
    return Formula.substitute_operators(formula, substitution_map)
    # Joan

def to_nand(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'-&'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'-&'``.
    """
    # Task 3.6b
    # Joan
    formula = to_not_and(formula)
    substitution_map = {'&': Formula.parse('((p-&q)-&(p-&q))'),
                        '~': Formula.parse('(p-&p)')}
    
    return Formula.substitute_operators(formula, substitution_map)
    # Joan

def to_implies_not(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'->'`` and ``'~'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'->'`` and ``'~'``.
    """
    # Task 3.6c
    # Joan
    formula = to_not_and(formula)
    substitution_map = {'&': Formula.parse('~(p->~q)')}
    
    return Formula.substitute_operators(formula, substitution_map)
    # Joan

def to_implies_false(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'->'`` and ``'F'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'->'`` and ``'F'``.
    """
    # Task 3.6d
    # Joan
    formula = to_implies_not(formula)
    substitution_map = {'~': Formula.parse('(p->F)')}
    
    return Formula.substitute_operators(formula, substitution_map)
    # Joan
