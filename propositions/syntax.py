# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2022
# File name: propositions/syntax.py

"""Syntactic handling of propositional formulas."""

from __future__ import annotations
from functools import lru_cache
from typing import Mapping, Optional, Set, Tuple, Union

from logic_utils import frozen, memoized_parameterless_method

@lru_cache(maxsize=100) # Cache the return value of is_variable
def is_variable(string: str) -> bool:
    """Checks if the given string is a variable name.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is a variable name, ``False`` otherwise.
    """
    return string[0] >= 'p' and string[0] <= 'z' and \
           (len(string) == 1 or string[1:].isdecimal())

@lru_cache(maxsize=100) # Cache the return value of is_constant
def is_constant(string: str) -> bool:
    """Checks if the given string is a constant.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is a constant, ``False`` otherwise.
    """
    return string == 'T' or string == 'F'

@lru_cache(maxsize=100) # Cache the return value of is_unary
def is_unary(string: str) -> bool:
    """Checks if the given string is a unary operator.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is a unary operator, ``False`` otherwise.
    """
    return string == '~'

@lru_cache(maxsize=100) # Cache the return value of is_binary
def is_binary(string: str) -> bool:
    """Checks if the given string is a binary operator.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is a binary operator, ``False`` otherwise.
    """
    return string in {'&', '|',  '->', '+', '<->', '-&', '-|'}

# Joan
@lru_cache(maxsize=100)
def first_chunk_str(string):
    # case {'->', '-&', '-|'}
    if string and string[0] == '-':
        chunk, rest = string[:2], string[2:]
    # case {'<->'}
    elif string and string[0] == '<':
        chunk, rest = string[:3], string[3:]
    # case {'&', '|', '+', constants, first letter of variables}
    else:
        chunk, rest = string[:1], string[1:]
    
    # extend variables
    if chunk and is_variable(chunk):
        while rest and rest[0].isdecimal():
            chunk += rest[0]
            rest = rest[1:]

    return chunk, rest
# Joan

@frozen
class Formula:
    """An immutable propositional formula in tree representation, composed from
    variable names, and operators applied to them.

    Attributes:
        root (`str`): the constant, variable name, or operator at the root of
            the formula tree.
        first (`~typing.Optional`\\[`Formula`]): the first operand of the root,
            if the root is a unary or binary operator.
        second (`~typing.Optional`\\[`Formula`]): the second operand of the
            root, if the root is a binary operator.
    """
    root: str
    first: Optional[Formula]
    second: Optional[Formula]

    def __init__(self, root: str, first: Optional[Formula] = None,
                 second: Optional[Formula] = None):
        """Initializes a `Formula` from its root and root operands.

        Parameters:
            root: the root for the formula tree.
            first: the first operand for the root, if the root is a unary or
                binary operator.
            second: the second operand for the root, if the root is a binary
                operator.
        """
        if is_variable(root) or is_constant(root):
            assert first is None and second is None
            self.root = root
        elif is_unary(root):
            assert first is not None and second is None
            self.root, self.first = root, first
        else:
            assert is_binary(root)
            assert first is not None and second is not None
            self.root, self.first, self.second = root, first, second

    @memoized_parameterless_method
    def __repr__(self) -> str:
        """Computes the string representation of the current formula.

        Returns:
            The standard string representation of the current formula.
        """
        # Task 1.1
        # Joan
        if is_variable(self.root) or is_constant(self.root):
            return self.root
        elif is_unary(self.root):
            return self.root + self.first.__repr__()
        else:
            assert is_binary(self.root)
            return '(' + self.first.__repr__() + self.root + self.second.__repr__() + ')'
        # Joan

    def __eq__(self, other: object) -> bool:
        """Compares the current formula with the given one.

        Parameters:
            other: object to compare to.

        Returns:
            ``True`` if the given object is a `Formula` object that equals the
            current formula, ``False`` otherwise.
        """
        return isinstance(other, Formula) and str(self) == str(other)

    def __ne__(self, other: object) -> bool:
        """Compares the current formula with the given one.

        Parameters:
            other: object to compare to.

        Returns:
            ``True`` if the given object is not a `Formula` object or does not
            equal the current formula, ``False`` otherwise.
        """
        return not self == other

    def __hash__(self) -> int:
        return hash(str(self))

    @memoized_parameterless_method
    def variables(self) -> Set[str]:
        """Finds all variable names in the current formula.

        Returns:
            A set of all variable names used in the current formula.
        """
        # Task 1.2
        # Joan
        if is_constant(self.root):
            return set()
        elif is_variable(self.root):
            return {self.root}
        elif is_unary(self.root):
            return self.first.variables()
        else:
            assert is_binary(self.root)
            return self.first.variables() | self.second.variables()
        # Joan

    @memoized_parameterless_method
    def operators(self) -> Set[str]:
        """Finds all operators in the current formula.

        Returns:
            A set of all operators (including ``'T'`` and ``'F'``) used in the
            current formula.
        """
        # Task 1.3
        # Joan
        if is_constant(self.root):
            return {self.root}
        elif is_variable(self.root):
            return set()
        elif is_unary(self.root):
            return {self.root} | self.first.operators()
        else:
            assert is_binary(self.root)
            return {self.root} | self.first.operators() | self.second.operators()
        # Joan

    @staticmethod
    def _parse_prefix(string: str) -> Tuple[Union[Formula, None], str]:
        """Parses a prefix of the given string into a formula.

        Parameters:
            string: string to parse.

        Returns:
            A pair of the parsed formula and the unparsed suffix of the string.
            If the given string has as a prefix a variable name (e.g.,
            ``'x12'``) or a unary operator followed by a variable name, then the
            parsed prefix will include that entire variable name (and not just a
            part of it, such as ``'x1'``). If no prefix of the given string is a
            valid standard string representation of a formula then returned pair
            should be of ``None`` and an error message, where the error message
            is a string with some human-readable content.
        """
        # Task 1.4
        # Joan
        chunk, rest = first_chunk_str(string)
        if not chunk:
            pre = None
            suf = 'Error: empty string'
        elif is_constant(chunk):
            pre = Formula(chunk)
            suf = rest
        elif is_variable(chunk):
            pre = Formula(chunk)
            suf = rest
        elif is_unary(chunk):
            first, rest = Formula._parse_prefix(rest)
            if first is None:
                pre = None
                suf = rest
            else:
                pre = Formula(chunk, first)
                suf = rest
        elif chunk == '(':
            # Entering binary chunk. Get first formula
            first, rest = Formula._parse_prefix(rest)
            if first is None:
                pre = None
                suf = rest
            else:
                # Get binary operator
                binop, rest = first_chunk_str(rest)
                if not is_binary(binop):
                    pre = None
                    suf = 'Error: wrong syntax'
                else:
                    # Get second formula
                    second, rest = Formula._parse_prefix(rest)
                    if second is None:
                        pre = None
                        suf = rest
                    elif not rest.startswith(')'):
                        pre = None
                        suf = 'Error: wrong syntax'
                    else:
                        pre = Formula(binop, first, second)
                        suf = rest[1:] 
        else:
            pre = None
            suf = 'Error: wrong syntax'        
        
        return pre, suf
        # Joan

    @staticmethod
    def is_formula(string: str) -> bool:
        """Checks if the given string is a valid representation of a formula.

        Parameters:
            string: string to check.

        Returns:
            ``True`` if the given string is a valid standard string
            representation of a formula, ``False`` otherwise.
        """
        # Task 1.5
        # Joan
        string = str(string)
        chunk, rest = Formula._parse_prefix(string)
        while chunk and rest:
            chunk, rest = Formula._parse_prefix(rest)
        if chunk and not rest:
            return True
        else:
            return False
        # Joan
        
    @staticmethod
    def parse(string: str) -> Formula:
        """Parses the given valid string representation into a formula.

        Parameters:
            string: string to parse.

        Returns:
            A formula whose standard string representation is the given string.
        """
        assert Formula.is_formula(string)
        # Output format is now enforced by verified syntax rules
        formula, emptystring = Formula._parse_prefix(string)
        return formula
        # Task 1.6

    def polish(self) -> str:
        """Computes the polish notation representation of the current formula.

        Returns:
            The polish notation representation of the current formula.
        """
        # Optional Task 1.7

    @staticmethod
    def parse_polish(string: str) -> Formula:
        """Parses the given polish notation representation into a formula.

        Parameters:
            string: string to parse.

        Returns:
            A formula whose polish notation representation is the given string.
        """
        # Optional Task 1.8

    def substitute_variables(self, substitution_map: Mapping[str, Formula]) -> \
            Formula:
        """Substitutes in the current formula, each variable name `v` that is a
        key in `substitution_map` with the formula `substitution_map[v]`.

        Parameters:
            substitution_map: mapping defining the substitutions to be
                performed.

        Returns:
            The formula resulting from performing all substitutions. Only
            variable name occurrences originating in the current formula are
            substituted (i.e., variable name occurrences originating in one of
            the specified substitutions are not subjected to additional
            substitutions).

        Examples:
            >>> Formula.parse('((p->p)|r)').substitute_variables(
            ...     {'p': Formula.parse('(q&r)'), 'r': Formula.parse('p')})
            (((q&r)->(q&r))|p)
        """
        for variable, newformula in substitution_map.items():
            assert is_variable(variable)
        # Task 3.3
        # Joan
            # Loop over the variables in the map
            # and substitute if we find them in the formula, recursively
            if self.root == variable:
                return newformula
            elif is_unary(self.root):
                return Formula(self.root, Formula.substitute_variables(self.first, substitution_map))
            elif is_binary(self.root):
                return Formula(self.root, Formula.substitute_variables(self.first, substitution_map), Formula.substitute_variables(self.second, substitution_map))
        # In case none of the previous returns happens
        return self
        # Joan

    def substitute_operators(self, substitution_map: Mapping[str, Formula]) -> \
            Formula:
        """Substitutes in the current formula, each constant or operator `op`
        that is a key in `substitution_map` with the formula
        `substitution_map[op]` applied to its (zero or one or two) operands,
        where the first operand is used for every occurrence of ``'p'`` in the
        formula and the second for every occurrence of ``'q'``.

        Parameters:
            substitution_map: mapping defining the substitutions to be
                performed.

        Returns:
            The formula resulting from performing all substitutions. Only
            operator occurrences originating in the current formula are
            substituted (i.e., operator occurrences originating in one of the
            specified substitutions are not subjected to additional
            substitutions).

        Examples:
            >>> Formula.parse('((x&y)&~z)').substitute_operators(
            ...     {'&': Formula.parse('~(~p|~q)')})
            ~(~~(~x|~y)|~~z)
        """
        for operator in substitution_map:
            assert is_constant(operator) or is_unary(operator) or is_binary(operator)
            assert substitution_map[operator].variables().issubset({'p', 'q'})
        # Task 3.4
        # Joan
        if is_constant(self.root) and self.root in substitution_map:
            return substitution_map[self.root]
        elif is_unary(self.root):
            first = Formula.substitute_operators(self.first, substitution_map)
            if self.root in substitution_map:
                return Formula.substitute_variables(substitution_map[self.root], {'p':first})
            else:
                return Formula(self.root, first)
        elif is_binary(self.root):
            first = Formula.substitute_operators(self.first, substitution_map)
            second = Formula.substitute_operators(self.second, substitution_map)
            if self.root in substitution_map:
                return Formula.substitute_variables(substitution_map[self.root], {'p':first, 'q':second})
            else:
                return Formula(self.root, first, second)
        return self
        # Joan