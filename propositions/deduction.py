# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2022
# File name: propositions/deduction.py

"""Useful proof manipulation maneuvers in Propositional Logic."""

from propositions.syntax import *
from propositions.proofs import *
from propositions.axiomatic_systems import *

def prove_corollary(antecedent_proof: Proof, consequent: Formula,
                    conditional: InferenceRule) -> Proof:
    """Converts the given proof of a formula `antecedent` to a proof of the
    given formula `consequent` by using the given assumptionless inference rule
    of which ``'(``\ `antecedent`\ ``->``\ `consequent`\ ``)'`` is a
    specialization.

    Parameters:
        antecedent_proof: valid proof of `antecedent`.
        consequent: formula to prove.
        conditional: assumptionless inference rule of which the assumptionless
            inference rule with conclusion
            ``'(``\ `antecedent`\ ``->``\ `consequent`\ ``)'`` is a
            specialization.

    Returns:
        A valid proof of `consequent` from the same assumptions as the given
        proof, via the same inference rules as the given proof and in addition
        `~propositions.axiomatic_systems.MP` and `conditional`.
    """
    assert antecedent_proof.is_valid()
    assert InferenceRule([],
                         Formula('->', antecedent_proof.statement.conclusion,
                                 consequent)).is_specialization_of(conditional)
    # Task 5.3a
    # Joan
    statement = InferenceRule(antecedent_proof.statement.assumptions, consequent)
    rules = antecedent_proof.rules | set([MP]) | set([conditional])
    
    N = len(antecedent_proof.lines)
    lines = list(antecedent_proof.lines)
    lines.append(Proof.Line(Formula('->', antecedent_proof.statement.conclusion, consequent), conditional, () ))
    lines.append(Proof.Line(consequent, MP, (N-1, N) ))
    lines = tuple(lines)
    
    return Proof(statement, rules, lines)
    # Joan

def combine_proofs(antecedent1_proof: Proof, antecedent2_proof: Proof,
                   consequent: Formula, double_conditional: InferenceRule) -> \
        Proof:
    """Combines the given proofs of two formulas `antecedent1` and `antecedent2`
    into a proof of the given formula `consequent` by using the given
    assumptionless inference rule of which
    ``'(``\ `antecedent1`\ ``->(``\ `antecedent2`\ ``->``\ `consequent`\ ``))'``
    is a specialization.

    Parameters:
        antecedent1_proof: valid proof of `antecedent1`.
        antecedent2_proof: valid proof of `antecedent2` from the same
            assumptions and inference rules as `antecedent1_proof`.
        consequent: formula to prove.
        double_conditional: assumptionless inference rule of which the
            assumptionless inference rule with conclusion
            ``'(``\ `antecedent1`\ ``->(``\ `antecedent2`\ ``->``\ `consequent`\ ``))'``
            is a specialization.

    Returns:
        A valid proof of `consequent` from the same assumptions as the given
        proofs, via the same inference rules as the given proofs and in addition
        `~propositions.axiomatic_systems.MP` and `double_conditional`.
    """
    assert antecedent1_proof.is_valid()
    assert antecedent2_proof.is_valid()
    assert antecedent1_proof.statement.assumptions == \
           antecedent2_proof.statement.assumptions
    assert antecedent1_proof.rules == antecedent2_proof.rules
    assert InferenceRule(
        [], Formula('->', antecedent1_proof.statement.conclusion,
        Formula('->', antecedent2_proof.statement.conclusion, consequent))
        ).is_specialization_of(double_conditional)
    # Task 5.3b
    # Joan
    statement = InferenceRule(antecedent1_proof.statement.assumptions, consequent)
    rules = antecedent1_proof.rules | set([MP]) | set([double_conditional])
    
    N1 = len(antecedent1_proof.lines)
    N2 = len(antecedent2_proof.lines)
    lines = list(antecedent1_proof.lines)
    lines2 = [L if L.is_assumption() else Proof.Line(L.formula, L.rule, (a+N1 for a in L.assumptions) ) for L in antecedent2_proof.lines]
    lines = lines + lines2
    lines.append(Proof.Line(Formula('->', antecedent1_proof.statement.conclusion, Formula('->', antecedent2_proof.statement.conclusion, consequent)), double_conditional, () ))
    lines.append(Proof.Line(Formula('->', antecedent2_proof.statement.conclusion, consequent), MP, (N1-1, N1+N2) ))
    lines.append(Proof.Line(consequent, MP, (N1+N2-1, N1+N2+1) ))
    lines = tuple(lines)
    
    return Proof(statement, rules, lines)
    # Joan

def remove_assumption(proof: Proof) -> Proof:
    """Converts the given proof of some `conclusion` formula, the last
    assumption of which is an assumption `assumption`, to a proof of
    ``'(``\ `assumption`\ ``->``\ `conclusion`\ ``)'`` from the same assumptions
    except `assumption`.

    Parameters:
        proof: valid proof to convert, with at least one assumption, via some
            set of inference rules all of which have no assumptions except
            perhaps `~propositions.axiomatic_systems.MP`.

    Returns:
        A valid proof of ``'(``\ `assumption`\ ``->``\ `conclusion`\ ``)'``
        from the same assumptions as the given proof except the last one, via
        the same inference rules as the given proof and in addition
        `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`, and
        `~propositions.axiomatic_systems.D`.
    """        
    assert proof.is_valid()
    assert len(proof.statement.assumptions) > 0
    for rule in proof.rules:
        assert rule == MP or len(rule.assumptions) == 0
    # Task 5.4
    # Joan
    assumptions = proof.statement.assumptions[:-1] # Get rid of phi
    phi = proof.statement.assumptions[-1]
    
    statement = InferenceRule(assumptions, Formula('->', phi, proof.statement.conclusion))
    rules = proof.rules | set((I0, D, I1, MP))

    lines = []
    for L in proof.lines:
        
        if L.formula in assumptions:
            lines.append(L)
            lines.append(Proof.Line(I1.specialize({'p': phi, 'q': L.formula}).conclusion, I1, []))
            lines.append(Proof.Line(Formula('->', phi, L.formula), MP, [len(lines)-2, len(lines)-1]))

        elif L.formula == phi:
            lines.append(Proof.Line(Formula('->', phi, phi), I0, []))
            
        elif L.rule == MP:   # Thanks to hjbolus. Idea is to show phi -> L.formula applying 2 MP to D 
            n = len(lines)
            q = proof.lines[L.assumptions[1]].formula.first

            lines.append(Proof.Line(D.specialize({'p': phi, 'q': q, 'r': L.formula}).conclusion, D, []))

            antecedent_1 = lines[-1].formula.first
            for line_number in range(len(lines)):
                if lines[line_number].formula == antecedent_1:
                    p1_1 = line_number
                    break
            lines.append(Proof.Line(lines[-1].formula.second, MP, [p1_1, n]))

            antecedent_2 = lines[-1].formula.first
            for line_number in range(len(lines)):
                if lines[line_number].formula == antecedent_2:
                    p1_2 = line_number
                    break
            lines.append(Proof.Line(lines[-1].formula.second, MP, [p1_2, n+1]))

        else:
            lines.append(L)
            lines.append(Proof.Line(I1.specialize({'p': phi, 'q': L.formula}).conclusion, I1, []))
            lines.append(Proof.Line(Formula('->', phi, L.formula), MP, [len(lines)-2, len(lines)-1]))

    return Proof(statement, rules, lines)
    # Joan

def prove_from_opposites(proof_of_affirmation: Proof,
                         proof_of_negation: Proof, conclusion: Formula) -> \
        Proof:
    """Combines the given proofs of a formula `affirmation` and its negation
    ``'~``\ `affirmation`\ ``'`` into a proof of the given formula.

    Parameters:
        proof_of_affirmation: valid proof of `affirmation`.
        proof_of_negation: valid proof of ``'~``\ `affirmation`\ ``'`` from the
            same assumptions and inference rules of `proof_of_affirmation`.
        conclusion: formula to prove.

    Returns:
        A valid proof of `conclusion` from the same assumptions as the given
        proofs, via the same inference rules as the given proofs and in addition
        `~propositions.axiomatic_systems.MP` and
        `~propositions.axiomatic_systems.I2`.
    """
    assert proof_of_affirmation.is_valid()
    assert proof_of_negation.is_valid()
    assert proof_of_affirmation.statement.assumptions == \
           proof_of_negation.statement.assumptions
    assert Formula('~', proof_of_affirmation.statement.conclusion) == \
           proof_of_negation.statement.conclusion
    assert proof_of_affirmation.rules == proof_of_negation.rules
    # Task 5.6
    # Joan
    # I2 = InferenceRule([], Formula.parse('(~p->(p->q))'))
    return combine_proofs(proof_of_negation, proof_of_affirmation, conclusion, I2)
    # Joan

def prove_by_way_of_contradiction(proof: Proof) -> Proof:
    """Converts the given proof of ``'~(p->p)'``, the last assumption of which
    is an assumption ``'~``\ `formula`\ ``'``, to a proof of `formula` from the
    same assumptions except ``'~``\ `formula`\ ``'``.

    Parameters:
        proof: valid proof of ``'~(p->p)'`` to convert, the last assumption of
            which is of the form ``'~``\ `formula`\ ``'``, via some set of
            inference rules all of which have no assumptions except perhaps
            `~propositions.axiomatic_systems.MP`.

    Returns:
        A valid proof of `formula` from the same assumptions as the given proof
        except the last one, via the same inference rules as the given proof and
        in addition `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`,
        `~propositions.axiomatic_systems.D`, and
        `~propositions.axiomatic_systems.N`.
    """
    assert proof.is_valid()
    assert proof.statement.conclusion == Formula.parse('~(p->p)')
    assert len(proof.statement.assumptions) > 0
    assert proof.statement.assumptions[-1].root == '~'
    for rule in proof.rules:
        assert rule == MP or len(rule.assumptions) == 0
    # Task 5.7
    # Joan
    N = InferenceRule([], Formula.parse('((~q->~p)->(p->q))'))
     
    phi = proof.statement.assumptions[-1].first

    proof2 = remove_assumption(proof) # (~phi->~(p->p))
    proof3 = prove_corollary(proof2, Formula('->',Formula.parse('(p->p)'), phi), N) # ((p->p)->phi)
    
    statement = InferenceRule(proof3.statement.assumptions, phi)
    rules = proof3.rules

    lines = list(proof3.lines)
    lines.append(Proof.Line(Formula.parse('(p->p)'), I0, []))
    lines.append(Proof.Line(phi, MP, [len(lines)-1, len(lines)-2]))
    lines = tuple(lines)

    return Proof(statement, rules, lines)
    # Joan
