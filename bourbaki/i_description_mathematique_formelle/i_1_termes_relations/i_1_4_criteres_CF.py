"""Critères formatifs CF1–CF8 (Bourbaki §I.1.4).

Comme les CS, ce sont des MÉTA-critères : ils décrivent comment la formation des
termes/relations se comporte. Ils se vérifient sur la couche LECTURE
(est_terme / est_relation / depuis_assemblage), pas par le noyau.

Énoncés (V7 §I.1.4, verbatim) :
  CF1 : A,B relations ⟹ (A∨B) relation
  CF2 : A relation ⟹ (¬A) relation
  CF3 : A relation, x lettre ⟹ τ_x(A) terme
  CF4 : t,u termes, s signe spécifique relationnel de poids 2 ⟹ (s t u) relation
  CF5 : A,B relations ⟹ (A⇒B) relation
  CF6 : y∉A ⟹ (y|x)A garde son espèce (renommage)
  CF7 : (y|x)A garde l'espèce de A (relation↔relation, terme↔terme)
  CF8 : T terme ⟹ (T|x)A garde l'espèce de A
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.assemblage import (Assemblage, concat, disjonction, negation, implication,
                        conjonction, equivalence, egalite, existe, pour_tout,
                        tau_x, substitution_b_x_a as sub, lettres)
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.i_1_app_lecture import DEFAUT, est_relation, est_terme, depuis_assemblage


def _sorte(a, sig):
    try:
        return depuis_assemblage(a, sig).sorte
    except Exception:
        return None


# @livre Ch.I §1.4 Crit.1 | E I.19 L.10-10 | PDF p.19
# @livre Ch.I §1.4 Demo.- | E I.19 L.11-19 | PDF p.19  (démo de CF1 par concaténation de constructions formatives ; vaut aussi pour CF2-CF4, « on établit de façon analogue »)
def cf1(a, b, sig=DEFAUT) -> bool:
    return est_relation(a, sig) and est_relation(b, sig) and est_relation(disjonction(a, b), sig)


# @livre Ch.I §1.4 Crit.2 | E I.19 L.20-20 | PDF p.19
def cf2(a, sig=DEFAUT) -> bool:
    return est_relation(a, sig) and est_relation(negation(a), sig)


# @livre Ch.I §1.4 Crit.3 | E I.19 L.21-21 | PDF p.19
def cf3(a, x, sig=DEFAUT) -> bool:
    return est_relation(a, sig) and est_terme(tau_x(a, x), sig)


# @livre Ch.I §1.4 Crit.4 | E I.19 L.22-23 | PDF p.19
def cf4(t, u, sig=DEFAUT) -> bool:
    """Signe spécifique relationnel de poids 2 (= ici) appliqué à deux termes."""
    return est_terme(t, sig) and est_terme(u, sig) and est_relation(egalite(t, u), sig)


# @livre Ch.I §1.4 Crit.5 | E I.19 L.25-25 | PDF p.19
def cf5(a, b, sig=DEFAUT) -> bool:
    return est_relation(a, sig) and est_relation(b, sig) and est_relation(implication(a, b), sig)


# @livre Ch.I §1.4 Crit.6 | E I.19 L.26-28 | PDF p.19
def cf6(a, x, y, sig=DEFAUT) -> bool:
    """y∉A ⟹ (y|x)A garde l'espèce de A."""
    if y in lettres(a):
        raise ValueError("CF6 exige y ∉ A")
    s = _sorte(a, sig)
    return s is not None and _sorte(sub(Assemblage((y,)), x, a), sig) == s


# @livre Ch.I §1.4 Crit.7 | E I.20 L.4-5 | PDF p.20
# @livre Ch.I §1.4 Demo.- | E I.20 L.6-27 | PDF p.20  (démo de CF7 : récurrence sur la construction formative ; cas lettre / ¬ / ∨ / signe, puis sous-cas a-b-c du τ_z)
def cf7(a, x, y, sig=DEFAUT) -> bool:
    """(y|x)A garde l'espèce de A (x, y lettres quelconques)."""
    s = _sorte(a, sig)
    return s is not None and _sorte(sub(Assemblage((y,)), x, a), sig) == s


# @livre Ch.I §1.4 Crit.8 | E I.20 L.28-29 | PDF p.20
# @livre Ch.I §1.4 Demo.- | E I.21 L.1-17 | PDF p.21  (démonstration de CF8 : récurrence, cas a-b-c du τ)
# @livre Ch.I §1.4 Rem.- | E I.21 L.18-22 | PDF p.21  (sens intuitif de (B|x)A — prose)
def cf8(a, x, t, sig=DEFAUT) -> bool:
    """T terme ⟹ (T|x)A garde l'espèce de A."""
    if not est_terme(t, sig):
        raise ValueError("CF8 exige T terme")
    s = _sorte(a, sig)
    return s is not None and _sorte(sub(t, x, a), sig) == s


# @livre Ch.I §3.4 Crit.9 | E I.29 L.17-19 | PDF p.29  (CF9 : énoncé L.17-18, démo L.19 via CF1+CF2)
def cf9(a, b, sig=DEFAUT) -> bool:
    """A,B relations ⟹ (A et B) relation. CF9, E I.29 (§I.3.4)."""
    return est_relation(a, sig) and est_relation(b, sig) and est_relation(conjonction(a, b), sig)


# @livre Ch.I §3.5 Crit.10 | E I.30 L.41-42 | PDF p.30  (CF10 : énoncé L.41, démo L.42 via CF5+CF9)
def cf10(a, b, sig=DEFAUT) -> bool:
    """A,B relations ⟹ (A ⇔ B) relation. CF10, E I.30 (§I.3.5)."""
    return est_relation(a, sig) and est_relation(b, sig) and est_relation(equivalence(a, b), sig)


# @livre Ch.I §4.1 Crit.11 | E I.32 L.19-21 | PDF p.32  (CF11 : énoncé L.19-20, démo L.21 via CF3+CF8+CF2)
def cf11(r, x, sig=DEFAUT) -> bool:
    """R relation, x lettre ⟹ (∃x)R et (∀x)R relations (E I.32 L.19-21)."""
    return (est_relation(r, sig)
            and est_relation(existe(x, r), sig) and est_relation(pour_tout(x, r), sig))


def cf12(a, r, x, sig=DEFAUT) -> bool:
    """A,R relations ⟹ quantificateurs typiques (∃_A x)R, (∀_A x)R relations.

    (∃_A x)R := (∃x)(A et R) ; (∀_A x)R := ¬(∃x)(A et ¬R).
    """
    ex = existe(x, conjonction(a, r))
    al = negation(existe(x, conjonction(a, negation(r))))
    return est_relation(ex, sig) and est_relation(al, sig)


def cf13(t, u, sig=DEFAUT) -> bool:
    """T,U termes ⟹ (T ⊂ U) relation.  (T⊂U := (∀z)((z∈T)⇒(z∈U)).)"""
    def dans(z, w):
        return concat(concat(Assemblage(("in",)), z), w)
    z = Assemblage(("z",))
    incl = pour_tout("z", implication(dans(z, t), dans(z, u)))
    return est_terme(t, sig) and est_terme(u, sig) and est_relation(incl, sig)


__all__ = ["cf1", "cf2", "cf3", "cf4", "cf5", "cf6", "cf7", "cf8",
           "cf9", "cf10", "cf11", "cf12", "cf13"]
