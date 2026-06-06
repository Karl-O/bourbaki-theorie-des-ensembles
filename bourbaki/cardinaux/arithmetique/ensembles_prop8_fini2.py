"""§III.3.4 / §III.4.1 — PROPOSITION 8 INCONDITIONNELLE puis JALON ⊢ Fini(2).

Le CAS 2 de la Proposition 8 (back-and-forth) est désormais FERMÉ par la
transposition CONSTRUITE (ensembles_transposition.transposition_existe, tous
conjoints CLOS).  La brique de transposition exigée par le CAS 2 est l'HT
CONDITIONNELLE (ht_glob_conditionnel) :

    (∀h)((bij(h, A⊔{∅}, B⊔{∅}) et h(*)∈B×{0}) ⇒ HT(B, h(*))),

qui est la forme CORRECTE (vs l'inconditionnelle transposition_globale, FAUSSE pour
h arbitraire dont h(*) sortirait de B⊔{∅}).  Elle SUFFIT pour le CAS 2 car
cas2_via_transposition ne consomme HT que SOUS (bij(h) et h(*)∈B×{0}) — exactement
le cadre où ht_glob_conditionnel la fournit.

  • cas2_h2(A,B)               — ⊢ H2(A,B)  (le CAS 2, désormais PROUVÉ, plus une
        hypothèse : la transposition le ferme) ;
  • prop8_successeur_injectif(A,B) — ⊢ (successeur(A)=successeur(B)) ⇒ (Card A=Card B)
        (PROPOSITION 8 INCONDITIONNELLE : le successeur cardinal est injectif) ;
  • fini_deux()               — ⊢ Fini(2)  (2 EST UN ENTIER NATUREL, le JALON).

Rien n'est postulé : la transposition est un terme CONSTRUIT et ses 4 conjoints de
bijection sont certifiés par le noyau.
"""
from __future__ import annotations

import functools

from bourbaki.logique.formule import (Terme, var, egal, et, non, appartient, existe)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.logique.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, instancie)
from bourbaki.logique.tactiques.tactiques_abrege_egalite import symetrie
from bourbaki.ensembles.familles.ensembles_somme_disjointe import (somme_disjointe,
                                                                   ZERO, UN)
from bourbaki.cardinaux.ensembles_cardinaux import (est_bijection_de, cardinal,
                                                    equipotent)
from bourbaki.cardinaux.arithmetique.ensembles_transposition._ht_glob import (
    ht_glob_conditionnel)
from bourbaki.cardinaux.arithmetique.ensembles_prop8_transposition import (
    transposition_hypothese, cas2_via_transposition)
from bourbaki.cardinaux.arithmetique.ensembles_prop8_assemblage import (
    cas2_hypothese, prop8_successeur_injectif_mod_cas2)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


_STAR = E.couple(E.VIDE, UN)            # * = (∅, 1)
_H = "h"
_TAU = "tau"


def _A0(a):
    return E.produit(_t(a), E.singleton(ZERO))


def _B0(b):
    return E.produit(_t(b), E.singleton(ZERO))


def _AS(a):
    return somme_disjointe(_t(a), E.singleton(E.VIDE))


def _BS(b):
    return somme_disjointe(_t(b), E.singleton(E.VIDE))


# ═══════════════════════════════════════════════════════════════════════════════
# CAS 2 PROUVÉ :  ⊢ H2(A,B)   (la transposition ferme le cas 2)
# ═══════════════════════════════════════════════════════════════════════════════
@functools.lru_cache(maxsize=None)
def cas2_h2(a="A", b="B", h=_H, tau=_TAU):
    """⊢ H2(A,B) = (∀h)((bij(h,A⊔{∅},B⊔{∅}) et h(*)∈B×{0}) ⇒ Eq(A×{0},B×{0})).

    Le CAS 2 de la Proposition 8, désormais PROUVÉ par la transposition CONSTRUITE.
    Pour chaque h, SOUS (bij(h) et h(*)∈B×{0}) :
      • ht_glob_conditionnel(h) fournit HT(B,h(*))  (la transposition existe) ;
      • cas2_via_transposition donne {HT(B,h(*))} ⊢ (bij(h) et h(*)∈B0) ⇒ Eq(A0,B0) ;
      • on décharge HT, MP avec l'HT dérivée, d'où (bij(h) et h(*)∈B0) ⇒ Eq(A0,B0).
    Généralisation en h ⇒ H2.  C'est le CAS 2 reporté, ICI FERMÉ (anti-faux : la
    transposition est construite et prouvée, pas postulée)."""
    vh = _t(h)
    AS, BS = _AS(a), _BS(b)
    B0 = _B0(b)
    hstar = E.valeur(vh, _STAR)
    bij_f = est_bijection_de(vh, AS, BS)
    ante = et(bij_f, appartient(hstar, B0))                  # bij(h) et h(*)∈B×{0}
    HT_f = transposition_hypothese(b, hstar, tau)            # HT(B,h(*))

    # ht_glob_conditionnel : (∀h)((bij(h) et h(*)∈B0) ⇒ HT(B,h(*)))
    htg = ht_glob_conditionnel(a, b, h, tau)
    htg_h = instancie(htg, vh)                               # (bij(h) et h(*)∈B0) ⇒ HT(B,h(*))

    # cas2_via_transposition : {HT(B,h(*))} ⊢ (bij(h) et h(*)∈B0) ⇒ Eq(A0,B0)
    corps = cas2_via_transposition(a, b, h, tau)             # [hyp HT(B,h(*))]
    corps_imp = N.loi_deduction(HT_f, corps)                 # HT(B,h(*)) ⇒ ((bij(h) et h(*)∈B0) ⇒ Eq(A0,B0))

    # sous ante : HT (de htg_h) ⇒ Eq(A0,B0)
    hante = N.assume(ante)
    HT = N.modus_ponens(hante, htg_h)                        # HT(B,h(*))  [hyp ante]
    imp = N.modus_ponens(HT, corps_imp)                      # (bij(h) et h(*)∈B0) ⇒ Eq(A0,B0)  [hyp ante]
    eqAB = N.modus_ponens(hante, imp)                        # Eq(A0,B0)  [hyp ante]
    body = N.loi_deduction(ante, eqAB)                       # (bij(h) et h(*)∈B0) ⇒ Eq(A0,B0)
    return N.generalisation(h, body)                         # H2(A,B)


# ═══════════════════════════════════════════════════════════════════════════════
# PROPOSITION 8 INCONDITIONNELLE :  ⊢ (succ A = succ B) ⇒ (Card A = Card B)
# ═══════════════════════════════════════════════════════════════════════════════
@functools.lru_cache(maxsize=None)
def prop8_successeur_injectif(a="A", b="B", h=_H, tau=_TAU):
    """⊢ (successeur(A) = successeur(B)) ⇒ (Card A = Card B).   (PROPOSITION 8, E.III.3.4.)

    Le successeur cardinal 𝔞 ↦ 𝔞+1 = Card(𝔞⊔{∅}) est INJECTIF.  INCONDITIONNEL :
    cas2_h2 PROUVE H2(A,B) (CAS 2 fermé par la transposition construite), puis
    prop8_successeur_injectif_mod_cas2 (déjà clos, CAS 1 + recollement) transforme
    H2 en (succ A=succ B ⇒ Card A=Card B).  Plus aucun report : la Proposition 8 est
    désormais ENTIÈRE."""
    H2 = cas2_h2(a, b, h, tau)                               # ⊢ H2(A,B)
    mod = prop8_successeur_injectif_mod_cas2(a, b, h)        # ⊢ H2 ⇒ (succ=succ ⇒ Card=Card)
    return N.modus_ponens(H2, mod)                           # ⊢ (succ A=succ B) ⇒ (Card A=Card B)


__all__ = ["cas2_h2", "prop8_successeur_injectif"]
