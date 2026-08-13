"""§II.6.4 — Stabilité d'une FAMILLE de parties saturées (E II.43, énoncé général).

Module NEUF (vague II — saturation).  On NE MODIFIE AUCUN fichier existant ; on
RECOLLE des lemmes DÉJÀ CLOS (familles §II.4 + saturation §II.6.4) et les axiomes
de la théorie des ensembles (`theorie_ensembles()` reste à 22 axiomes — AUCUN
axiome neuf).

ÉNONCÉ (Bourbaki, E.II.43, §II.6 n°4 « Parties saturées », dernier alinéa) :

  « Si (X_ι)_{ι∈I} est une famille de parties saturées de E, les ensembles
    ⋃_{ι∈I} X_ι et ⋂_{ι∈I} X_ι sont saturés (II, p. 25, prop. 3 et 4). »

Le CAS BINAIRE A, B est fait dans `ensembles_saturees_stabilite.py` (même dossier).
Ici on formalise la VERSION FAMILLE générale (I quelconque) :

  `famille_de_saturees_reunion`  { (∀ι)(ι∈I ⇒ est_saturee(X_ι, G)) }
        ⊢ est_saturee( ⋃_{ι∈I} X_ι, G )
  `famille_de_saturees_inter`    { (∀ι)(ι∈I ⇒ est_saturee(X_ι, G)) }
        ⊢ est_saturee( ⋂_{ι∈I} X_ι, G )

où X_ι = E.valeur_famille(X, ι) et
   est_saturee(C, G) = E.est_saturee(C, G, C, x="x")
                     = (∀x)(∀y)( (x∈C et (x,y)∈G) ⇒ y∈C )  (liants x, y).

Le liant de la famille-hyp est « i », DISJOINT des liants x, y de est_saturee (la
généralisation/élimination en i est donc licite : i ne figure pas dans les liés x, y,
ni dans la conclusion, qui porte sur ⋃/⋂).

STRATÉGIE (calquée sur le cas binaire + lemmes famille de §II.4.1).  On déplie
est_saturee(C, G) et on prouve le corps instancié en deux points universels x, y.
Sous (x∈C et (x,y)∈G) :

  RÉUNION (C = ⋃X_ι).  `membre_reunion_famille` : x∈⋃X_ι ⇔ (∃i)(i∈I et x∈X_i).
    Sous le corps existentiel (i∈I et x∈X_i) :
      • famille-hyp instanciée en i, appliquée à i∈I ⇒ est_saturee(X_i, G) ;
      • celle-ci instanciée en (x, y), appliquée à (x∈X_i et (x,y)∈G) ⇒ y∈X_i ;
      • `reunion_famille_intro` (témoin i) appliqué à (i∈I et y∈X_i) ⇒ y∈⋃X_ι.
    loi_deduction (décharge le corps) puis `existe_elimination` en i (i absent de
    la conclusion y∈⋃X_ι et de la famille-hyp où il est lié) : (∃i)(…) ⇒ y∈⋃X_ι ;
    composé avec x∈⋃X_ι ⇒ (∃i)(…).

  INTERSECTION (C = ⋂X_ι).  Depuis la migration « ⋂ = SÉLECTION dans ⋃ » (Déf. 2,
    E II.22, cf. `ii_4_intersection_fondation`), x∈⋂X_ι ⇔ (x∈⋃X_ι et (∀i)(i∈I ⇒ x∈X_i)) :
    l'INTRODUCTION dans ⋂ réclame un TÉMOIN D'INDICE.  Il est ici GRATUIT — on ne
    suppose donc RIEN de plus (cf. « I = ∅ » ci-dessous) :
      • `temoin_indice_via_inter` : de l'antécédent x∈⋂X_ι on tire x∈⋃X_ι (⋂ ⊂ ⋃),
        d'où (∃i)(i∈I et x∈X_i) et le témoin canonique T₀ := τi(i∈I et x∈X_i), T₀∈I ;
      • `inter_elim` (projection DROITE, direction INCHANGÉE) : x∈⋂X_ι ⇒ (∀i)(i∈I ⇒ x∈X_i),
        instancié en i puis appliqué à i∈I ⇒ x∈X_i ;
      • famille-hyp en i ⇒ est_saturee(X_i, G), instanciée en (x, y) appliquée à
        (x∈X_i et (x,y)∈G) ⇒ y∈X_i ;
    loi_deduction (i∈I) + generalisation(i) ⇒ (∀i)(i∈I ⇒ y∈X_i) ;
    `inter_intro` (témoin T₀) ⇒ y∈⋂X_ι.

Puis loi_deduction (décharge l'antécédent x∈C et (x,y)∈G) et double généralisation
sur y, x — qui reconstruit EXACTEMENT E.est_saturee(C, G, C, x="x").

CAS I = ∅ — pourquoi AUCUNE hypothèse « I ≠ ∅ » (issue A, énoncé strictement
inchangé).  Avec la Déf. 2 réalisée par sélection, ⋂_{ι∈∅} X_ι = ∅ (et ⋃_{ι∈∅} X_ι = ∅),
et ∅ EST saturée : (∀x)(∀y)((x∈∅ et (x,y)∈G) ⇒ y∈∅) est vide-vraie, son antécédent
étant réfutable.  La preuve ci-dessus couvre ce cas sans le distinguer : elle ne
fabrique le témoin T₀ que SOUS l'antécédent x∈⋂X_ι, lequel est justement inhabitable
quand I = ∅.  Ajouter (∃i)(i∈I) serait un affaiblissement gratuit.

Les trois gestes ⋂ viennent de `ii_4_image_famille.ensembles_image_inter_pont_ii4`
(`inter_elim`, `temoin_indice_via_inter`, `inter_intro`) : malgré le dossier qui les
héberge, ils ne portent RIEN de spécifique aux images — ce sont les gestes génériques
de la sélection, CLOS, et on les recolle plutôt que de les dupliquer ici.

HYPOTHÈSE HONNÊTE (load-bearing, exactement dans le séquent — rien postulé, aucune
tautologie, conclusion ∉ hypothèses) :
  • (∀i)(i∈I ⇒ est_saturee(X_i, G))  — consommée par instanciation en le témoin i.
La conclusion porte sur ⋃/⋂ (≠ l'hypothèse) ; les liants x, y de la généralisation
ne figurent pas dans l'hypothèse (où ils sont liés par est_saturee), donc la double
généralisation est licite.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, et, impl, appartient, pourtout)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, instancie)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import existe_elimination
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_1_definitions_algebre.ensembles_familles import (
    membre_reunion_famille, reunion_famille_intro)
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_image_famille.ensembles_image_inter_pont_ii4 import (
    inter_elim, temoin_indice_via_inter, inter_intro)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def _nom(v):
    """Nom (str) d'une variable donnée par str ou Terme-var (pour les lemmes de ⋃,
    qui attendent des NOMS : membre_reunion_famille/reunion_famille_intro → var(·) ;
    les gestes ⋂ du pont, eux, acceptent des Termes)."""
    if isinstance(v, Terme):
        if v.tag != "var":
            raise ValueError("nom de variable attendu (str ou Terme-var simple)")
        return v.nom
    return v


def _hyp_famille(vX, vI, vg, i="i"):
    """(∀i)(i∈I ⇒ est_saturee(X_i, G))  — famille-hyp honnête (liant i)."""
    vi = var(i)
    Xi = E.valeur_famille(vX, vi)
    return pourtout(i, impl(appartient(vi, vI),
                            E.est_saturee(Xi, vg, Xi, x="x")))


def cible_reunion_famille_saturee(x="X", i="I", g="G"):
    """Cible Bourbaki : est_saturee( ⋃_{ι∈I} X_ι, G )  (forme dépliée, liants x, y).

    Construite EXACTEMENT comme les cibles du cas binaire :
    E.est_saturee(C, G, C, x="x") avec C = ⋃_{ι∈I} X_ι = E.reunion_famille(X, I)."""
    vX, vI, vg = _t(x), _t(i), _t(g)
    c = E.reunion_famille(vX, vI)
    return E.est_saturee(c, vg, c, x="x")


def cible_inter_famille_saturee(x="X", i="I", g="G"):
    """Cible Bourbaki : est_saturee( ⋂_{ι∈I} X_ι, G )  (forme dépliée, liants x, y)."""
    vX, vI, vg = _t(x), _t(i), _t(g)
    c = E.inter_famille(vX, vI)
    return E.est_saturee(c, vg, c, x="x")


# @livre Ch.II §6.4 Prop.- | E II.43 L.30-31 | PDF p.94
def famille_de_saturees_reunion(x="X", i="I", g="G"):
    """{(∀i)(i∈I ⇒ est_saturee(X_i, G))} ⊢ est_saturee( ⋃_{ι∈I} X_ι, G )
    (E.II.43, énoncé général famille — réunion ; clos mod. hyp.).

    « Si (X_ι)_{ι∈I} est une famille de parties saturées pour R, alors ⋃_{ι∈I} X_ι
    est saturée. »  (Bourbaki E.II.43, réf. prop. 3 de E.II.4.)  Preuve : membership
    de la réunion de famille (`membre_reunion_famille`) + témoin i existentiel, la
    famille-hyp instanciée en i fournissant la saturation de X_i, puis introduction
    dans la réunion (`reunion_famille_intro`) ; élimination de l'existentiel par
    `existe_elimination` (cf. en-tête).  Clos modulo {(∀i)(i∈I ⇒ est_saturee(X_i,G))}."""
    vX, vI, vg = _t(x), _t(i), _t(g)
    nX, nI = _nom(x), _nom(i)
    vx, vy, vi = var("x"), var("y"), var("i")
    union = E.reunion_famille(vX, vI)
    Xi = E.valeur_famille(vX, vi)

    # hypothèse honnête : la famille est saturée (liant i, disjoint de x, y)
    h_fam = N.assume(_hyp_famille(vX, vI, vg))

    # antécédent du corps instancié en (x, y) : (x∈⋃X_ι et (x,y)∈G)
    antec = et(appartient(vx, union), appartient(E.couple(vx, vy), vg))
    h_ant = N.assume(antec)
    x_in_U = conjonction_elim_gauche(h_ant)                # x∈⋃X_ι
    xy_G = conjonction_elim_droite(h_ant)                  # (x,y)∈G

    # corps existentiel (i∈I et x∈X_i) — sous lui on construit y∈⋃X_ι
    body = et(appartient(vi, vI), appartient(vx, Xi))
    h_body = N.assume(body)
    i_in_I = conjonction_elim_gauche(h_body)               # i∈I
    x_in_Xi = conjonction_elim_droite(h_body)              # x∈X_i

    # famille-hyp en i ⇒ est_saturee(X_i, G), instanciée en (x, y)
    satXi = N.modus_ponens(i_in_I, instancie(h_fam, vi))   # est_saturee(X_i, G)
    yXi = N.modus_ponens(conjonction_intro(x_in_Xi, xy_G),
                         instancie(instancie(satXi, vx), vy))   # y∈X_i

    # (i∈I et y∈X_i) ⇒ y∈⋃X_ι  (témoin i)
    yU = N.modus_ponens(conjonction_intro(i_in_I, yXi),
                        reunion_famille_intro(nX, nI, "i", "y"))   # y∈⋃X_ι
    imp_body = N.loi_deduction(body, yU)                   # (i∈I et x∈X_i) ⇒ y∈⋃X_ι

    # (∃i)(i∈I et x∈X_i) ⇒ y∈⋃X_ι  (i absent de la conclusion et lié dans h_fam)
    imp_ex = existe_elimination(imp_body, "i")
    x_to_ex = equivalence_avant(membre_reunion_famille(nX, nI, "x"))   # x∈⋃ ⇒ (∃i)(…)
    y_in_U = N.modus_ponens(N.modus_ponens(x_in_U, x_to_ex), imp_ex)  # y∈⋃X_ι

    body_imp = N.loi_deduction(antec, y_in_U)              # (x∈⋃ et (x,y)∈G) ⇒ y∈⋃
    return N.generalisation("x", N.generalisation("y", body_imp))


# @livre Ch.II §6.4 Prop.- | E II.43 L.30-31 | PDF p.94
def famille_de_saturees_inter(x="X", i="I", g="G"):
    """{(∀i)(i∈I ⇒ est_saturee(X_i, G))} ⊢ est_saturee( ⋂_{ι∈I} X_ι, G )
    (E.II.43, énoncé général famille — intersection ; clos mod. hyp.).

    « Si (X_ι)_{ι∈I} est une famille de parties saturées pour R, alors ⋂_{ι∈I} X_ι
    est saturée. »  (Bourbaki E.II.43, réf. prop. 4 de E.II.4.)  Preuve : le témoin
    d'indice T₀ est FABRIQUÉ à partir de l'antécédent x∈⋂X_ι (`temoin_indice_via_inter`) ;
    pour i∈I fixé, `inter_elim` donne x∈X_i, la famille-hyp en i fournit la saturation
    de X_i d'où y∈X_i ; généralisation sur i puis `inter_intro` (témoin T₀) recolle
    y∈⋂X_ι (cf. en-tête).  Clos modulo {(∀i)(i∈I ⇒ est_saturee(X_i,G))} — AUCUNE
    hypothèse « I ≠ ∅ » : l'énoncé reste STRICTEMENT celui d'avant la migration."""
    vX, vI, vg = _t(x), _t(i), _t(g)
    vx, vy, vi = var("x"), var("y"), var("i")
    inter = E.inter_famille(vX, vI)

    h_fam = N.assume(_hyp_famille(vX, vI, vg))

    antec = et(appartient(vx, inter), appartient(E.couple(vx, vy), vg))
    h_ant = N.assume(antec)
    x_in_inter = conjonction_elim_gauche(h_ant)            # x∈⋂X_ι
    xy_G = conjonction_elim_droite(h_ant)                  # (x,y)∈G

    # TÉMOIN D'INDICE GRATUIT : x∈⋂ ⊂ ⋃ donne (∃i)(i∈I et x∈X_i), d'où T₀∈I.
    T0, t0_in_I = temoin_indice_via_inter(vX, vI, vx, x_in_inter)

    # sous i∈I : x∈X_i (élimination, INCHANGÉE), puis y∈X_i (saturation de X_i)
    h_iI = N.assume(appartient(vi, vI))
    x_in_Xi = N.modus_ponens(h_iI,
        instancie(N.modus_ponens(x_in_inter, inter_elim(vX, vI, vx)), vi))   # x∈X_i
    satXi = N.modus_ponens(h_iI, instancie(h_fam, vi))     # est_saturee(X_i, G)
    yXi = N.modus_ponens(conjonction_intro(x_in_Xi, xy_G),
                         instancie(instancie(satXi, vx), vy))   # y∈X_i
    imp_iI = N.loi_deduction(appartient(vi, vI), yXi)      # (i∈I ⇒ y∈X_i)

    # (∀i)(i∈I ⇒ y∈X_i) + T₀∈I ⇒ y∈⋂X_ι  (introduction de la sélection)
    forall_i = N.generalisation("i", imp_iI)               # (∀i)(i∈I ⇒ y∈X_i)
    y_in_inter = inter_intro(vX, vI, T0, t0_in_I, forall_i, vy)      # y∈⋂X_ι

    body_imp = N.loi_deduction(antec, y_in_inter)          # (x∈⋂ et (x,y)∈G) ⇒ y∈⋂
    return N.generalisation("x", N.generalisation("y", body_imp))


__all__ = [
    "cible_reunion_famille_saturee",
    "cible_inter_famille_saturee",
    "famille_de_saturees_reunion",
    "famille_de_saturees_inter",
]
