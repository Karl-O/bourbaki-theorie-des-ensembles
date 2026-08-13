"""§II.2 — DISTRIBUTIVITÉ du produit cartésien sur la réunion, RÉUNION SUR LE
PREMIER FACTEUR (le second facteur Y reste commun), au niveau de l'APPARTENANCE
D'UN COUPLE.  Formule (22) du Résumé E.R.12 (§3, item 3c), X, X' parties de E,
Y partie de F :

    (22)   (X × Y) ∪ (X' × Y) = (X ∪ X') × Y

C'est la DUALE de  A × (B ∪ C) = (A × B) ∪ (A × C)  (réunion sur le SECOND
facteur, déjà formalisée dans ensembles_produit_distributif.py via
couple_dans_produit_distributif_reunion). On la certifie ici en CALQUANT
EXACTEMENT ce module dual, rôles des deux facteurs échangés (la réunion porte
maintenant sur le facteur GAUCHE, le facteur droit Y est partagé).

FORME LIVRÉE — couple-level (∀ couple z = (u,v)), STRICTEMENT comme le dual.
Le module dual ne prouve PAS l'égalité ENSEMBLISTE pleine (∀z, z couple ou non) :
celle-ci exige la poussée des ∃p,q de AXIOME_PRODUIT à travers ∨/∧ + l'extensionnalité,
qu'il REPORTE explicitement (cf. sa docstring, lignes 17-18). Par cohérence avec lui,
on livre ICI la MÊME forme : l'équivalence d'appartenance d'un COUPLE, qui est le
CŒUR de l'égalité (22) et la voie de preuve par extensionnalité.  On ne prétend donc
PAS l'égalité d'ensembles (==) — on prouve l'équivalence ⇔ d'appartenance du couple.

Briques (toutes déjà fermées, recollement pur — aucun axiome ajouté) :
  • couple_dans_produit_ssi  ((u,v)∈X×Y ⇔ u∈X et v∈Y)            [ensembles_produit, CLOS]
  • _instance_reunion  (z∈X∪Y ⇔ z∈X∨z∈Y)                        [AXIOME_REUNION]
  • _ou_et_distrib  (((Q∨Q') et P) ⇔ ((Q et P)∨(Q' et P)))      [local, CLOS, dual de et_ou_distrib]
  • congruences ∨ + transitivité de ⇔.

theorie_ensembles() INCHANGÉE (= 22) : aucun axiome ajouté.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import Terme, var, appartient, et, ou
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.ii_theorie_des_ensembles.ii_2_couples.ii_2_2_produit_deux_ensembles.ensembles_produit import couple_dans_produit_ssi
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_theoremes import _instance_reunion
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    ou_congruence, equivalence_symetrie, equivalence_transitivite,
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite, cas,
)


def _t(x):
    return x if isinstance(x, Terme) else var(x)


def _ou_et_distrib(q, qp, p):
    """⊢ ((Q ∨ Q') et P) ⇔ ((Q et P) ∨ (Q' et P)).   (distribution de et sur ∨,
    facteur commun P à DROITE — duale stricte de et_ou_distrib qui a P à gauche.
    Mêmes briques noyau : S2 (R⇒R∨S), S3 (R∨S⇒S∨R), cas, loi_deduction.)"""
    # ── ⇒ : ((Q∨Q') et P) ⇒ ((Q et P) ∨ (Q' et P)) ──────────────────────────
    h = N.assume(et(ou(q, qp), p))
    pp = conjonction_elim_droite(h)                        # P (conjoint droit cette fois)
    brQ = N.loi_deduction(q, N.modus_ponens(conjonction_intro(N.assume(q), pp),
                                            N.s2(et(q, p), et(qp, p))))   # (Q et P) ⇒ disj
    brQp = N.loi_deduction(qp, N.modus_ponens(N.modus_ponens(
        conjonction_intro(N.assume(qp), pp), N.s2(et(qp, p), et(q, p))),  # (Q'etP)⇒((Q'etP)∨(QetP))
        N.s3(et(qp, p), et(q, p))))                                       # ⇒ ((QetP)∨(Q'etP))
    fwd = N.loi_deduction(et(ou(q, qp), p), cas(conjonction_elim_gauche(h), brQ, brQp))
    # ── ⇐ : ((Q et P) ∨ (Q' et P)) ⇒ ((Q∨Q') et P) ──────────────────────────
    h2 = N.assume(ou(et(q, p), et(qp, p)))
    hq = N.assume(et(q, p))
    brQc = N.loi_deduction(et(q, p), conjonction_intro(
        N.modus_ponens(conjonction_elim_gauche(hq), N.s2(q, qp)),         # Q ⇒ (Q∨Q')
        conjonction_elim_droite(hq)))                                     # P
    hqp = N.assume(et(qp, p))
    brQpc = N.loi_deduction(et(qp, p), conjonction_intro(
        N.modus_ponens(N.modus_ponens(conjonction_elim_gauche(hqp), N.s2(qp, q)),  # Q'⇒(Q'∨Q)
                       N.s3(qp, q)),                                               # ⇒ (Q∨Q')
        conjonction_elim_droite(hqp)))                                    # P
    bwd = N.loi_deduction(ou(et(q, p), et(qp, p)), cas(h2, brQc, brQpc))
    return conjonction_intro(fwd, bwd)


# @livre Ch.II §R.3 Prop.22 | E.R.12 L.20-21 | PDF p.315
def couple_dans_produit_distrib_reunion_premier_facteur(
        u="u", v="v", a="X", b="Xp", c="Y"):
    """⊢ ((u,v) ∈ (X×Y)∪(X'×Y)) ⇔ ((u,v) ∈ (X∪X')×Y).

    CŒUR (forme couple-level) de la formule (22) :
        (X × Y) ∪ (X' × Y) = (X ∪ X') × Y      (E.R.12, §3, item 3c).
    Réunion sur le PREMIER facteur ; le second facteur Y (= c) est commun.
    """
    vu, vv, vX, vXp, vY = _t(u), _t(v), _t(a), _t(b), _t(c)
    vY_app = appartient(vv, vY)
    XX = E.reunion(vX, vXp)
    # (u,v)∈(X×Y)∪(X'×Y) ⇔ ((u,v)∈X×Y ou (u,v)∈X'×Y)
    e1 = _instance_reunion(E.produit(vX, vY), E.produit(vXp, vY), E.couple(vu, vv))
    # ((u,v)∈X×Y ou (u,v)∈X'×Y) ⇔ ((u∈X et v∈Y) ou (u∈X' et v∈Y))
    e2 = ou_congruence(couple_dans_produit_ssi(vu, vv, vX, vY),
                       couple_dans_produit_ssi(vu, vv, vXp, vY))
    # ((u∈X et v∈Y) ou (u∈X' et v∈Y)) ⇔ ((u∈X ou u∈X') et v∈Y)
    e3 = equivalence_symetrie(
        _ou_et_distrib(appartient(vu, vX), appartient(vu, vXp), vY_app))
    # ((u∈X ou u∈X') et v∈Y) ⇔ (u∈X∪X' et v∈Y)
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import et_congruence_gauche
    e4 = et_congruence_gauche(equivalence_symetrie(_instance_reunion(vX, vXp, vu)), vY_app)
    # (u∈X∪X' et v∈Y) ⇔ (u,v)∈(X∪X')×Y
    e5 = equivalence_symetrie(couple_dans_produit_ssi(vu, vv, XX, vY))
    return equivalence_transitivite(equivalence_transitivite(equivalence_transitivite(
        equivalence_transitivite(e1, e2), e3), e4), e5)


# Alias court, nom orienté « résultat » (formule 22).
produit_distrib_reunion_premier_facteur = couple_dans_produit_distrib_reunion_premier_facteur


__all__ = [
    "couple_dans_produit_distrib_reunion_premier_facteur",
    "produit_distrib_reunion_premier_facteur",
]
