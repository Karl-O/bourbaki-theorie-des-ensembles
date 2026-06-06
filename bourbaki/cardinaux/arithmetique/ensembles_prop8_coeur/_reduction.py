"""CŒUR Prop. 8 — réduction finale du CAS 1 : Eq(A, B) quand h fixe le marqueur.

On compose le CAS 1 des copies de gauche (eq_copies_cas_fixe :
bij(h) ⇒ (h(*)=* ⇒ Eq(A×{0}, B×{0}))) avec le transport déjà certifié
eq_copies_gauches_implique_eq (Eq(A×{0},B×{0}) ⇒ Eq(A,B)) pour obtenir

    eq_cas_fixe_implique_eq :
        ⊢ est_bijection_de(h, A⊔{∅}, B⊔{∅}) ⇒ ((h(*)=*) ⇒ Eq(A, B)).

C'est le CAS 1 COMPLET de la preuve back-and-forth de la Proposition 8 : si une
bijection h : A⊔{∅} → B⊔{∅} FIXE le point marqué * = (∅,1), alors A et B sont
équipotents.  Reste, pour l'inconditionnel eq_somme_un_implique_eq, le CAS 2
(h(*)=(b₀,0), échange a₀↦b₀) et le recollement par cas — REPORTÉS.
"""
from __future__ import annotations

from bourbaki.logique.formule import var, egal
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.logique.tactiques.tactiques_abrege import syllogisme
from bourbaki.ensembles.familles.ensembles_somme_disjointe import UN, somme_disjointe
from bourbaki.cardinaux.ensembles_cardinaux import est_bijection_de
from bourbaki.cardinaux.arithmetique.ensembles_copie_marquee import eq_copies_gauches_implique_eq
from bourbaki.cardinaux.arithmetique.ensembles_prop8_coeur._cas1 import eq_copies_cas_fixe


_STAR = E.couple(E.VIDE, UN)


def eq_cas_fixe_implique_eq(a="A", b="B", h="h"):
    """⊢ est_bijection_de(h, A⊔{∅}, B⊔{∅}) ⇒ ((h(*)=*) ⇒ Eq(A, B)).

    CAS 1 complet : composition du CAS 1 des copies de gauche
    (eq_copies_cas_fixe) avec le transport eq_copies_gauches_implique_eq."""
    vh = var(h)
    va = var(a) if isinstance(a, str) else a
    vb = var(b) if isinstance(b, str) else b
    AS = somme_disjointe(va, E.singleton(E.VIDE))
    BS = somme_disjointe(vb, E.singleton(E.VIDE))
    fix = egal(E.valeur(vh, _STAR), _STAR)

    cas1 = eq_copies_cas_fixe(a, b, h)        # bij(h) ⇒ (h(*)=* ⇒ Eq(A×{0},B×{0}))
    transport = eq_copies_gauches_implique_eq(a, b)   # Eq(A×{0},B×{0}) ⇒ Eq(A,B)

    # Sous bij(h) et h(*)=* : Eq(A×{0},B×{0}) puis Eq(A,B)
    hbij = N.assume(est_bijection_de(vh, AS, BS))
    hfix = N.assume(fix)
    eq_copies = N.modus_ponens(hfix, N.modus_ponens(hbij, cas1))   # Eq(A×{0},B×{0})
    eq_AB = N.modus_ponens(eq_copies, transport)                  # Eq(A,B)
    inner = N.loi_deduction(fix, eq_AB)                           # bij(h) ⊢ (h(*)=* ⇒ Eq(A,B))
    return N.loi_deduction(est_bijection_de(vh, AS, BS), inner)


__all__ = ["eq_cas_fixe_implique_eq"]
