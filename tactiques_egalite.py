"""Couche 3 (suite) — critères quantifiés/égalitaires dérivés + réflexivité.

PDF p.~32--34, ~39, Bourbaki, Chap. I §4–§5.

  C30 (instanciation) : ⊢ (∀x)R ⇒ (T|x)R     (dérivé de S5 + contraposition + DNE)
  Théorème 1          : ⊢ x = x                (réflexivité de l'égalité, E.I.39)

Tout est produit par le noyau. Seules primitives de confiance employées :
S1–S7, MP, C6 (déduction, via syllogisme), C27 (généralisation).
"""
from __future__ import annotations

from assemblage import (
    Assemblage, negation, conjonction, egalite, existe, pour_tout,
    substitution_b_x_a,
)
from lecture import Signature, DEFAUT
import noyau
from noyau import Theoreme
from tactiques import syllogisme, antecedent_consequent
from tactiques_prop import (
    contraposition, double_negation_elim,
    conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere,
)


def instanciation_en_x(r: Assemblage, x: str, sig: Signature = DEFAUT) -> Theoreme:
    """⊢ (∀x)R ⇒ R.  Cas T = x du critère C30 ((x|x)R = R).

    Preuve : S5 sur ¬R avec T = x donne ⊢ ¬R ⇒ (∃x)¬R ; contraposée :
    ⊢ ¬(∃x)¬R ⇒ ¬¬R, soit ⊢ (∀x)R ⇒ ¬¬R ; on compose avec ¬¬R ⇒ R (DNE).
    """
    s5 = noyau.s5(negation(r), Assemblage((x,)), x, sig)  # ⊢ ¬R ⇒ (∃x)¬R
    contra = contraposition(s5, sig)                      # ⊢ ¬(∃x)¬R ⇒ ¬¬R = (∀x)R⇒¬¬R
    return syllogisme(contra, double_negation_elim(r, sig), sig)  # ⊢ (∀x)R ⇒ R


def instanciation(r: Assemblage, t: Assemblage, x: str, sig: Signature = DEFAUT) -> Theoreme:
    """⊢ (∀x)R ⇒ (T|x)R.  C30 GÉNÉRAL (terme T quelconque). PDF E.I.34.

    Preuve : S5 sur ¬R avec le terme T donne ⊢ (T|x)¬R ⇒ (∃x)¬R ; or
    (T|x)¬R = ¬(T|x)R (CS5) ; contraposée : ⊢ ¬(∃x)¬R ⇒ ¬¬(T|x)R, soit
    ⊢ (∀x)R ⇒ ¬¬(T|x)R ; on compose avec ¬¬(T|x)R ⇒ (T|x)R (DNE).
    """
    s5 = noyau.s5(negation(r), t, x, sig)                 # ⊢ (T|x)¬R ⇒ (∃x)¬R
    contra = contraposition(s5, sig)                      # ⊢ (∀x)R ⇒ ¬¬(T|x)R
    tr = substitution_b_x_a(t, x, r)                      # (T|x)R
    return syllogisme(contra, double_negation_elim(tr, sig), sig)  # ⊢ (∀x)R ⇒ (T|x)R


def reflexivite(x: str = "x", sig: Signature = DEFAUT) -> Theoreme:
    """⊢ x = x.  Théorème 1 (E.I.39), preuve Bourbaki reconstruite pas à pas.

    1.  ⊢ R ⇔ R               (R := ¬(x=x))           equivalence_reflexive
    2.  ⊢ (∀x)(R ⇔ R)         généralisation (C27)
    3.  ⊢ (∀x)(R⇔R) ⇒ (τxR = τxR)   S7        ; MP → ⊢ τxR = τxR = (τx¬S|x)S
    4.  ⊢ (∀x)S               double négation (S = x=x)  [C26, sens ⇐]
    5.  ⊢ (∀x)S ⇒ S           instanciation (C30, T=x) ; MP → ⊢ S
    """
    from tactiques_prop import equivalence_reflexive, double_negation_intro
    S = egalite(Assemblage((x,)), Assemblage((x,)))   # x = x
    R = negation(S)                                   # ¬(x=x)

    equiv_rr = equivalence_reflexive(R, sig)          # ⊢ R⇔R
    gen = noyau.generalisation(x, equiv_rr, sig)      # ⊢ (∀x)(R⇔R)
    s7 = noyau.s7(R, R, x, sig)                       # ⊢ (∀x)(R⇔R) ⇒ (τxR=τxR)
    tau_eq = noyau.modus_ponens(gen, s7, sig)         # ⊢ τxR = τxR  = (τx¬S | x)S

    P = tau_eq.conclusion
    forall_S = noyau.modus_ponens(tau_eq, double_negation_intro(P, sig), sig)  # ⊢ ¬¬P = (∀x)S
    assert forall_S.conclusion == pour_tout(x, S)     # garde-fou : ¬¬P ≡ (∀x)S

    inst = instanciation_en_x(S, x, sig)              # ⊢ (∀x)S ⇒ S
    return noyau.modus_ponens(forall_S, inst, sig)    # ⊢ S = (x = x)


def reflexivite_terme(t: Assemblage, sig: Signature = DEFAUT) -> Theoreme:
    """⊢ T = T pour un TERME T quelconque (terme composé, pas seulement une lettre).

    De ⊢ x=x (Th1) on tire ⊢ (∀x)(x=x) (C27), puis C30 général instancie au
    terme T : ⊢ (∀x)(x=x) ⇒ (T|x)(x=x) = (T = T).
    """
    xx = egalite(Assemblage(("x",)), Assemblage(("x",)))
    gen = noyau.generalisation("x", reflexivite("x", sig), sig)   # ⊢ (∀x)(x=x)
    return noyau.modus_ponens(gen, instanciation(xx, t, "x", sig), sig)  # ⊢ T = T


def c44(t: Assemblage, u: Assemblage, v: Assemblage, w: str,
        sig: Signature = DEFAUT) -> Theoreme:
    """⊢ (T = U) ⇒ (V{T} = V{U}).  Substitutivité de = pour les termes (C44).

    V est un terme contenant la lettre-trou w (V{T} = (T|w)V). On suppose que
    U ne contient pas w. Preuve : S6 avec R{w} = (V{w} = V{U}) donne
    (T=U) ⇒ ((V{T}=V{U}) ⇔ (V{U}=V{U})) ; sous T=U et par réflexivité de V{U}.
    """
    vU = substitution_b_x_a(u, w, v)                  # V{U}
    s6 = noyau.s6(t, u, w, egalite(v, vU), sig)        # (T=U)⇒((V{T}=V{U})⇔(V{U}=V{U}))
    equiv = noyau.modus_ponens(noyau.assume(egalite(t, u), sig), s6, sig)
    vtu = noyau.modus_ponens(reflexivite_terme(vU, sig),
                             equivalence_arriere(equiv, sig), sig)  # {T=U}⊢ V{T}=V{U}
    return noyau.loi_deduction(egalite(t, u), vtu, sig)


def importation(thm: Theoreme, sig: Signature = DEFAUT) -> Theoreme:
    """⊢ A ⇒ (B ⇒ C)  ⟹  ⊢ (A et B) ⇒ C.  (décurryfication via C6.)"""
    a, bc = antecedent_consequent(thm.conclusion, sig)
    b, _ = antecedent_consequent(bc, sig)
    h = noyau.assume(conjonction(a, b), sig)          # (A et B) ⊢ (A et B)
    hbc = noyau.modus_ponens(conjonction_elim_gauche(h, sig), thm, sig)  # ⊢ B⇒C
    hc = noyau.modus_ponens(conjonction_elim_droite(h, sig), hbc, sig)   # ⊢ C
    return noyau.loi_deduction(conjonction(a, b), hc, sig)


def symetrie(x: str = "x", y: str = "y", sig: Signature = DEFAUT) -> Theoreme:
    """⊢ (x = y) ⇒ (y = x).  Théorème 2 (E.I.40), preuve Bourbaki.

    S6 sur R=(y=x), lettre y : ⊢ (x=y) ⇒ ((x=x) ⇔ (y=x)). Sous l'hypothèse
    x=y, l'équivalence + la réflexivité (x=x) donnent y=x ; on décharge.
    """
    X, Y = Assemblage((x,)), Assemblage((y,))
    Sxy = egalite(X, Y)
    s6 = noyau.s6(X, Y, y, egalite(Y, X), sig)        # ⊢ (x=y) ⇒ ((x=x) ⇔ (y=x))
    h = noyau.assume(Sxy, sig)                        # {x=y} ⊢ (x=y)
    equiv = noyau.modus_ponens(h, s6, sig)            # {x=y} ⊢ (x=x) ⇔ (y=x)
    yx = noyau.modus_ponens(reflexivite(x, sig), equivalence_avant(equiv, sig), sig)
    return noyau.loi_deduction(Sxy, yx, sig)          # ⊢ (x=y) ⇒ (y=x)


def transitivite(x: str = "x", y: str = "y", z: str = "z",
                 sig: Signature = DEFAUT) -> Theoreme:
    """⊢ ((x=y) et (y=z)) ⇒ (x=z).  Théorème 3 (E.I.40), preuve Bourbaki.

    S6 sur R=(y=z), lettre y : ⊢ (x=y) ⇒ ((x=z) ⇔ (y=z)). Sous {x=y, y=z},
    l'équivalence (sens ⇐) + y=z donnent x=z ; on décharge puis on importe.
    """
    X, Y, Z = Assemblage((x,)), Assemblage((y,)), Assemblage((z,))
    Sxy, Syz = egalite(X, Y), egalite(Y, Z)
    s6 = noyau.s6(X, Y, y, egalite(Y, Z), sig)        # ⊢ (x=y) ⇒ ((x=z) ⇔ (y=z))
    hxy, hyz = noyau.assume(Sxy, sig), noyau.assume(Syz, sig)
    equiv = noyau.modus_ponens(hxy, s6, sig)          # {x=y} ⊢ (x=z) ⇔ (y=z)
    hxz = noyau.modus_ponens(hyz, equivalence_arriere(equiv, sig), sig)  # {x=y,y=z}⊢ x=z
    t1 = noyau.loi_deduction(Syz, hxz, sig)           # {x=y} ⊢ (y=z) ⇒ (x=z)
    t2 = noyau.loi_deduction(Sxy, t1, sig)            # ⊢ (x=y) ⇒ ((y=z) ⇒ (x=z))
    return importation(t2, sig)                       # ⊢ ((x=y) et (y=z)) ⇒ (x=z)


__all__ = ["instanciation_en_x", "instanciation", "reflexivite",
           "reflexivite_terme", "c44", "importation", "symetrie", "transitivite"]
