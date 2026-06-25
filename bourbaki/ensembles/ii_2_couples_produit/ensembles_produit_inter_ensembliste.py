"""§II.2 — FORMULE (23) du Résumé E.R.12 en ÉGALITÉ D'ENSEMBLES PLEINE.

Bourbaki (Résumé E.R.12, §3, item 3d ; X, X' parties de E, Y, Y' parties de F) :

    (23)   (X × Y) ∩ (X' × Y') = (X ∩ X') × (Y ∩ Y')        [ÉGALITÉ D'ENSEMBLES]

Le dépôt ne prouvait jusqu'ici (23) qu'au niveau APPARTENANCE D'UN COUPLE
(`couple_dans_intersection_produits`, ensembles_produit_distributif.py) — ÉCART
MAJEUR de fidélité (cf. FIDELITE_PDF.md / ANOMALIES « écart de portée systématique
des égalités de produits »).  Ce module COMBLE le trou : il livre (23) en ÉGALITÉ
D'ENSEMBLES (==), exactement comme le module frère
ensembles_produit_extensionnalite.py a livré la formule (22).

STRATÉGIE (calque strict du (22)-ensembliste) — soit
    A = (X × Y) ∩ (X' × Y')        B = (X ∩ X') × (Y ∩ Y')
On montre, sous les ambiants {X⊂E, X'⊂E, Y⊂F, Y'⊂F} :
  1. A ⊂ E×F   :  A ⊂ X×Y  (l'intersection ⊂ son 1er facteur, CLOS) puis
                  X×Y ⊂ E×F  (monotonie du produit sous X⊂E, Y⊂F) ; transitivité.
  2. B ⊂ E×F   :  X∩X' ⊂ X ⊂ E  et  Y∩Y' ⊂ Y ⊂ F, puis monotonie du produit.
  3. (∀u)(∀v)((u,v)∈A ⇔ (u,v)∈B)   = la composante COUPLE déjà prouvée et CLOSE,
     `couple_dans_intersection_produits` (ensembles_produit_distributif.py).
Puis on applique l'EXTENSIONNALITÉ DES PARTIES D'UN PRODUIT
(`produit_egalite_par_couples`, ensembles_produit_extensionnalite.py).  La
conclusion est le nœud `=` (A=B), PAS l'équivalence d'appartenance d'un couple.

theorie_ensembles() INCHANGÉE (= 22) : aucun axiome ajouté (recollement pur).

Liants : tout est en TERMES (non en noms) ; on réutilise `_produit_monotone` du
module frère (binders p, q, z internes maîtrisés).  Trou de Leibniz frais réservé
côté brique d'extensionnalité.
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (Terme, var, egal, et, impl,
                                       appartient, inclus)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    projection_gauche, instancie, equivalence_avant)
from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_theoremes import _instance_intersection
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege import syllogisme
from bourbaki.ensembles.ii_2_couples_produit.ensembles_produit_extensionnalite import (
    produit_egalite_par_couples, _produit_monotone)
from bourbaki.ensembles.ii_2_couples_produit.ensembles_produit_distributif import (
    couple_dans_intersection_produits)


def _t(x):
    return x if isinstance(x, Terme) else var(x)


# ── inclusions de base sur l'intersection (en TERMES, CLOSES) ──────────────────
def _inter_inclus_facteur_gauche(va, vb):
    """⊢ a∩b ⊂ a   (l'intersection est incluse dans son 1er facteur ; a,b TERMES).

    Calque de inclusion_intersection_gauche, mais en termes : z∈a∩b ⇔ (z∈a et z∈b)
    (AXIOME_INTER), puis projection sur le conjoint gauche."""
    vz = var("z")
    c = _instance_intersection(va, vb, vz)                 # z∈a∩b ⇔ (z∈a et z∈b)
    proj = projection_gauche(appartient(vz, va), appartient(vz, vb))
    return N.generalisation("z", syllogisme(equivalence_avant(c), proj))


def _inclusion_trans_termes(vA, vB, vC, h_ab, h_bc):
    """De {Γ}⊢A⊂B et {Δ}⊢B⊂C (théorèmes Γ/Δ-portés, termes), déduire {Γ,Δ}⊢A⊂C.

    Transitivité de ⊂ en termes : instancie chaque inclusion en z, syllogisme,
    re-généralise.  Calque du corps de inclusion_transitive (tactiques_abrege2)."""
    vz = var("z")
    zab = instancie(h_ab, vz)                              # z∈A ⇒ z∈B
    zbc = instancie(h_bc, vz)                              # z∈B ⇒ z∈C
    return N.generalisation("z", syllogisme(zab, zbc))     # A⊂C


# ── A ⊂ E×F et B ⊂ E×F sous les ambiants ──────────────────────────────────────
def _membre_gauche_inclus(vX, vXp, vY, vYp, vE, vF, pXE, pXpE, pYF, pYpF):
    """{X⊂E,X'⊂E,Y⊂F,Y'⊂F} ⊢ (X×Y)∩(X'×Y') ⊂ E×F.

    A=(X×Y)∩(X'×Y') ⊂ X×Y  (intersection ⊂ 1er facteur, CLOS) ⊂ E×F (monotonie)."""
    XY = E.produit(vX, vY)
    XpYp = E.produit(vXp, vYp)
    A = E.intersection(XY, XpYp)
    amb = E.produit(vE, vF)
    A_in_XY = _inter_inclus_facteur_gauche(XY, XpYp)        # A ⊂ X×Y  (CLOS)
    XY_in_amb = _produit_monotone(vX, vY, vE, vF, pXE, pYF) # X×Y ⊂ E×F
    return _inclusion_trans_termes(A, XY, amb, A_in_XY, XY_in_amb)


def _membre_droit_inclus(vX, vXp, vY, vYp, vE, vF, pXE, pXpE, pYF, pYpF):
    """{X⊂E,X'⊂E,Y⊂F,Y'⊂F} ⊢ (X∩X')×(Y∩Y') ⊂ E×F.

    X∩X' ⊂ X ⊂ E  et  Y∩Y' ⊂ Y ⊂ F, puis monotonie du produit."""
    XXp = E.intersection(vX, vXp)
    YYp = E.intersection(vY, vYp)
    # X∩X' ⊂ E  (via X∩X' ⊂ X ⊂ E)
    XXp_in_E = _inclusion_trans_termes(XXp, vX, vE,
                                       _inter_inclus_facteur_gauche(vX, vXp), pXE)
    # Y∩Y' ⊂ F  (via Y∩Y' ⊂ Y ⊂ F)
    YYp_in_F = _inclusion_trans_termes(YYp, vY, vF,
                                       _inter_inclus_facteur_gauche(vY, vYp), pYF)
    return _produit_monotone(XXp, YYp, vE, vF, XXp_in_E, YYp_in_F)   # (X∩X')×(Y∩Y') ⊂ E×F


# ── composante COUPLE (∀u,v) — déjà prouvée et CLOSE ──────────────────────────
def _memes_couples_23(vX, vXp, vY, vYp, u="u", v="v"):
    """⊢ (∀u)(∀v)((u,v)∈(X×Y)∩(X'×Y') ⇔ (u,v)∈(X∩X')×(Y∩Y'))   (cœur, CLOS).

    `couple_dans_intersection_produits(u,v,A,B,C,D)` prouve
        (u,v)∈(A×B)∩(C×D) ⇔ (u,v)∈(A∩C)×(B∩D).
    Mapping pour (23) : A→X, B→Y, C→X', D→Y'  ⇒
        (u,v)∈(X×Y)∩(X'×Y') ⇔ (u,v)∈(X∩X')×(Y∩Y')."""
    eq = couple_dans_intersection_produits(u, v, vX, vY, vXp, vYp)
    return N.generalisation(u, N.generalisation(v, eq))


# ── FORMULE (23) en ÉGALITÉ D'ENSEMBLES ───────────────────────────────────────
# @livre Ch.II §R.3 Prop.23 | E.R.12 L.22-23 | PDF p.315
def produit_inter_ensembliste(a="X", b="Xp", c="Y", d="Yp", e="E", f="F"):
    """⊢ ( X⊂E ∧ X'⊂E ∧ Y⊂F ∧ Y'⊂F ) ⇒ (X×Y)∩(X'×Y') = (X∩X')×(Y∩Y').

    FORMULE (23) du Résumé E.R.12 (§3, item 3d) en ÉGALITÉ D'ENSEMBLES PLEINE.
    Les deux membres sont ⊂ E×F sous les ambiants ; on applique l'extensionnalité
    des parties d'un produit (`produit_egalite_par_couples`) avec la composante
    couple déjà prouvée (`couple_dans_intersection_produits`).  Conclusion = `=`."""
    vX, vXp, vY, vYp, vE, vF = _t(a), _t(b), _t(c), _t(d), _t(e), _t(f)
    A = E.intersection(E.produit(vX, vY), E.produit(vXp, vYp))   # (X×Y)∩(X'×Y')
    B = E.produit(E.intersection(vX, vXp), E.intersection(vY, vYp))  # (X∩X')×(Y∩Y')
    hyp = et(et(et(inclus(vX, vE), inclus(vXp, vE)), inclus(vY, vF)), inclus(vYp, vF))
    h = N.assume(hyp)
    pXE = conjonction_elim_gauche(conjonction_elim_gauche(conjonction_elim_gauche(h)))   # X⊂E
    pXpE = conjonction_elim_droite(conjonction_elim_gauche(conjonction_elim_gauche(h)))  # X'⊂E
    pYF = conjonction_elim_droite(conjonction_elim_gauche(h))                            # Y⊂F
    pYpF = conjonction_elim_droite(h)                                                    # Y'⊂F

    A_amb = _membre_gauche_inclus(vX, vXp, vY, vYp, vE, vF, pXE, pXpE, pYF, pYpF)   # A⊂E×F
    B_amb = _membre_droit_inclus(vX, vXp, vY, vYp, vE, vF, pXE, pXpE, pYF, pYpF)    # B⊂E×F
    couples = _memes_couples_23(vX, vXp, vY, vYp)                                   # (∀u,v) …
    egal_AB = N.modus_ponens(                                  # extensionnalité ⇒ A=B
        conjonction_intro(conjonction_intro(A_amb, B_amb), couples),
        produit_egalite_par_couples(A, B, vE, vF))
    return N.loi_deduction(hyp, egal_AB)                       # ⊢ HYP ⇒ (A = B)


def produit_inter_ensembliste_cible(a="X", b="Xp", c="Y", d="Yp", e="E", f="F"):
    """Énoncé visé de produit_inter_ensembliste : l'ÉGALITÉ (23) sous les ambiants."""
    vX, vXp, vY, vYp, vE, vF = _t(a), _t(b), _t(c), _t(d), _t(e), _t(f)
    A = E.intersection(E.produit(vX, vY), E.produit(vXp, vYp))
    B = E.produit(E.intersection(vX, vXp), E.intersection(vY, vYp))
    hyp = et(et(et(inclus(vX, vE), inclus(vXp, vE)), inclus(vY, vF)), inclus(vYp, vF))
    return impl(hyp, egal(A, B))


__all__ = ["produit_inter_ensembliste", "produit_inter_ensembliste_cible"]
