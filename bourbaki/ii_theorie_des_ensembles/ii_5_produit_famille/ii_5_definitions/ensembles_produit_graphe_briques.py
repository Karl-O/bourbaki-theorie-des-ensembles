"""§II.5.3 Déf.1 — LES TROIS BRIQUES DU CONJOINT « F ⊂ I × ⋃_{ι∈I} X_ι ».

Depuis la réparation de `AXIOME_PRODUIT_FAM` (2026-07-26), la Déf. 1 (E II.32) est
encodée avec son conjoint de TÊTE, celui du livre :

    F ∈ ∏_{ι∈I} X_ι  ⇔  ( F ⊂ I × ⋃_{ι∈I} X_ι  ∧  F fonctionnel
                          ∧  dom F = I  ∧  (∀ι)(ι∈I ⇒ F(ι) ∈ X_ι) )

Tout site qui CONSTRUIT une appartenance au produit doit donc désormais produire ce
conjoint.  Ce module fournit les trois briques qui le rendent mécanique, et rien
d'autre — pas de notion du livre nouvelle, seulement l'outillage de la Déf. 1.

  (B1) `inclus_produit_est_graphe`      { G ⊂ E×F } ⊢ est_un_graphe(G)
  (B2) `pivot_inclusion_produit`  LE PIVOT
        { est_un_graphe(G), est_fonctionnel(G), dom G = I,
          (∀ι)(ι∈I ⇒ G(ι) ∈ X_ι) }  ⊢  G ⊂ I × ⋃_{ι∈I} X_ι
  (B3) `graphe_apres_adjonction`        { est_un_graphe(G) } ⊢ est_un_graphe(G ∪ {(j,x)})

RECETTE DE RÉ-ÉCRITURE D'UN SITE « ÉCRITURE » (celle appliquée dans tout le §II.5) :
  1. du produit SOURCE, lire le conjoint de tête `G ⊂ I × ⋃X_ι` (chemin g,g,g) ;
  2. B1 dessus ⟹ est_un_graphe(G)  (le fait que les points du produit soient des
     graphes n'est plus une hypothèse honnête : c'est un théorème) ;
  3. B2 avec la famille BUT ⟹ le conjoint de tête du produit CIBLE ;
  4. reconstruire le corps à QUATRE conjoints et refermer par `equivalence_arriere`.

⚠️ B1 EST ÉCRITE INLINE ICI, ET CE N'EST PAS UNE DUPLICATION GRATUITE.  Deux copies
existent ailleurs (`ii_5_2_ensemble_applications/ensembles_application_valeur`
et `iii_3_5/prop9_exp_somme/ensembles_prop9_close`) : les importer depuis
`ii_5_definitions` créerait un CYCLE D'IMPORT MESURÉ — la première charge
transitivement `ii_5_definitions.ensembles_produit_famille` via
`iii_3_equipotence/cantor/ensembles_cantor`.  B1 ne dépend donc que de
`ii_2_2.ensembles_produit._instance_produit` (AXIOME_PRODUIT), en amont strict.

Rien postulé : tout sort des primitives `N.*` et des axiomes déjà présents ;
`theorie_ensembles()` reste à 22 (asserté en test).  Noyau et `subst` intouchés.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, et, ou, impl, appartient, existe, inclus, pourtout, subst_f,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    cas, conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, instancie,
)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import (
    existe_elimination,
)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
    symetrie,
)
from bourbaki.ii_theorie_des_ensembles.ii_2_couples.ii_2_1_definition_couples.ensembles_couples import (
    singleton_membre,
)
from bourbaki.ii_theorie_des_ensembles.ii_2_couples.ii_2_2_produit_deux_ensembles.ensembles_produit import (
    _instance_produit, couple_dans_produit,
)
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_4_fonctions.ensembles_extensionnalite import (
    couple_dans_dom,
)
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_4_fonctions.ensembles_fonctions import (
    valeur_caracterisation,
)
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_1_definitions_algebre.ensembles_familles import (
    reunion_famille_intro,
)

#: Noms FRAIS des paramètres généralisés-puis-instanciés (term-safety des briques
#: dont les dépendances n'acceptent que des NOMS).  Exotiques par construction.
_NF, _NI, _NA = "fpv", "Ipv", "Apv"


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def _dech(hypothese, thm):
    """Décharge `hypothese` de `thm` (loi de déduction) — alias lisible."""
    return N.loi_deduction(hypothese, thm)


# ── B1 : un sous-ensemble d'un produit binaire est un graphe ──────────────────
# @livre Ch.II §3.1 Def.1 | E II.10 L.3-8 | PDF p.61
#   (« un GRAPHE est un ensemble dont tout élément est un couple » : c'est
#    exactement ce que donne l'inclusion dans un produit E×F.)
def inclus_produit_est_graphe(g="G", e="E", f="F"):
    """{ G ⊂ E×F } ⊢ est_un_graphe(G).   [1 hypothèse EXACTE ; g, e, f termes OU noms]

    z ∈ G ⊂ E×F donne z ∈ E×F, donc (∃p)(∃q)(z=(p,q) et p∈E et q∈F) par
    AXIOME_PRODUIT ; on retient z=(p,q), on ré-injecte (p, q) comme témoins des
    liants (x, y) de `est_un_couple`, puis on élimine p et q (ils ne figurent pas
    dans la conclusion) et on généralise z."""
    vG, vE, vF = _t(g), _t(e), _t(f)
    vz, vp, vq = var("z"), var("p"), var("q")
    h_incl = N.assume(inclus(vG, E.produit(vE, vF)))       # (∀z)(z∈G ⇒ z∈E×F)
    z_imp = instancie(h_incl, vz)                          # z∈G ⇒ z∈E×F
    car = _instance_produit(vE, vF, vz)                    # z∈E×F ⇔ (∃p)(∃q)(…)

    body = et(et(egal(vz, E.couple(vp, vq)), appartient(vp, vE)), appartient(vq, vF))
    hb = N.assume(body)
    z_pq = conjonction_elim_gauche(conjonction_elim_gauche(hb))      # z = (p,q)
    inner_xy = egal(vz, E.couple(var("x"), var("y")))                # z = (x,y)
    body_py = subst_f(vp, "x", inner_xy)                             # z = (p,y)
    ex_y = N.modus_ponens(z_pq, N.s5(body_py, vq, "y"))              # (∃y)(z=(p,y))
    ex_xy = N.modus_ponens(ex_y, N.s5(existe("y", inner_xy), vp, "x"))
    couple_de_body = existe_elimination(existe_elimination(
        _dech(body, ex_xy), "q"), "p")                     # (∃p)(∃q)(…) ⇒ est_un_couple(z)

    z_in = N.assume(appartient(vz, vG))
    ex_body = N.modus_ponens(N.modus_ponens(z_in, z_imp), equivalence_avant(car))
    couple_z = N.modus_ponens(ex_body, couple_de_body)     # est_un_couple(z)
    res = N.generalisation("z", _dech(appartient(vz, vG), couple_z))
    assert res.conclusion == E.est_un_graphe(vG), "B1 : conclusion ≠ est_un_graphe(G)"
    assert res.hypotheses == frozenset({inclus(vG, E.produit(vE, vF))}), "B1 : hypothèses"
    return res


# ── B2 : LE PIVOT — reconstruire le conjoint de tête de la Déf. 1 ─────────────
def _couple_dans_produit_t(vx, vy, vI, vA):
    """⊢ (x∈I et y∈A) ⇒ ((x,y) ∈ I×A)   pour des TERMES I, A quelconques.

    `couple_dans_produit` n'accepte que des NOMS : on l'instancie sur deux noms
    FRAIS puis on généralise-instancie (règles du noyau, aucune fabrication)."""
    cdp = couple_dans_produit("x", "y", _NI, _NA)
    gen = N.generalisation(_NI, N.generalisation(_NA, cdp))   # (∀Ipv)(∀Apv)…
    res = instancie(instancie(gen, vI), vA)
    assert res.conclusion == impl(et(appartient(vx, vI), appartient(vy, vA)),
                                  appartient(E.couple(vx, vy), E.produit(vI, vA))), \
        "_couple_dans_produit_t : capture de liant (I ou A contient p/q/x/y ?)"
    return res


def _reunion_famille_intro_t(vf, vI, vx, vy):
    """⊢ ((x∈I) et (y∈X_x)) ⇒ (y ∈ ⋃_{ι∈I} X_ι)   pour des TERMES f, I."""
    rfi = reunion_famille_intro(_NF, _NI, "x", "y")
    gen = N.generalisation(_NF, N.generalisation(_NI, rfi))   # (∀fpv)(∀Ipv)…
    res = instancie(instancie(gen, vf), vI)
    assert res.conclusion == impl(
        et(appartient(vx, vI), appartient(vy, E.valeur_famille(vf, vx))),
        appartient(vy, E.reunion_famille(vf, vI))), \
        "_reunion_famille_intro_t : capture de liant (f ou I contient « i » libre ?)"
    return res


def hypothese_valeurs(fam, i, idx="i", g="G"):
    """(∀ι)(ι∈I ⇒ G(ι) ∈ X_ι)  — la 4ᵉ clause de la Déf. 1 (liant « i » de l'axiome)."""
    vG, vf, vI, vi = _t(g), _t(fam), _t(i), var(idx)
    return pourtout(idx, impl(appartient(vi, vI),
                              appartient(E.valeur(vG, vi), E.valeur_famille(vf, vi))))


# @livre Ch.II §5.3 Def.1 | E II.32 L.10-15 | PDF p.83
#   (le PRÉAMBULE de la Déf. 1 : « F un graphe fonctionnel ayant I pour ensemble de
#    définition […] F est un élément de 𝔓(I × A) », A = ⋃_{ι∈I} X_ι.)
def pivot_inclusion_produit(g="G", fam="f", i="I", idx="i"):
    """LE PIVOT — ⊢ G ⊂ I × ⋃_{ι∈I} X_ι, sous les QUATRE hypothèses EXACTES

        { est_un_graphe(G), est_fonctionnel(G), dom G = I, (∀ι)(ι∈I ⇒ G(ι)∈X_ι) }.

    C'est la phrase que Bourbaki écrit en préambule de la Déf. 1 pour justifier la
    sélection S8 : un graphe fonctionnel de domaine I dont les valeurs tombent dans
    les X_ι est inclus dans I × A.  Sa réciproque est triviale ; c'est ce sens-ci
    que TOUT site « écriture » doit fournir depuis la réparation de l'axiome.

    PREUVE.  Soit z ∈ G.  G est un graphe donc z = (x,y).  Alors x ∈ dom G = I ;
    G étant fonctionnel et (x,y)∈G, C46 donne y = G(x) ; la 4ᵉ clause en x∈I donne
    G(x) ∈ X_x, donc y ∈ X_x, donc y ∈ ⋃_{ι∈I} X_ι ; d'où (x,y) ∈ I × ⋃X_ι, puis
    z ∈ I × ⋃X_ι par réécriture.  On élimine les témoins x, y et on généralise z.

    g, fam, i : noms OU TERMES (term-safe).  idx = liant de la 4ᵉ clause (« i »,
    celui de l'axiome)."""
    vG, vf, vI = _t(g), _t(fam), _t(i)
    vz, vx, vy = var("z"), var("x"), var("y")
    A = E.reunion_famille(vf, vI)
    PROD = E.produit(vI, A)

    h_graphe = N.assume(E.est_un_graphe(vG))
    h_func = N.assume(E.est_fonctionnel(vG))
    h_dom = N.assume(egal(E.dom(vG), vI))
    h_vals = N.assume(hypothese_valeurs(vf, vI, idx, vG))

    h_z = N.assume(appartient(vz, vG))
    couple_z = N.modus_ponens(h_z, instancie(h_graphe, vz))          # est_un_couple(z)

    # sous z = (x,y)
    EQ = egal(vz, E.couple(vx, vy))
    h_eq = N.assume(EQ)
    rw_G = N.modus_ponens(h_eq, N.s6(vz, E.couple(vx, vy), "w", appartient(var("w"), vG)))
    xy_in_G = N.modus_ponens(h_z, equivalence_avant(rw_G))           # (x,y) ∈ G

    # x ∈ dom G, puis x ∈ I  (Leibniz le long de dom G = I)
    x_dom = N.modus_ponens(xy_in_G, _dech(appartient(E.couple(vx, vy), vG),
                                          couple_dans_dom(vG, vx, vy)))
    rw_dom = N.modus_ponens(h_dom, N.s6(E.dom(vG), vI, "w", appartient(vx, var("w"))))
    x_in_I = N.modus_ponens(x_dom, equivalence_avant(rw_dom))        # x ∈ I

    # y = G(x)  (C46 : F fonctionnel et x dans le domaine)
    EX_Y = existe("y", appartient(E.couple(vx, var("y")), vG))
    ex_y = N.modus_ponens(xy_in_G, N.s5(appartient(E.couple(vx, var("y")), vG), vy, "y"))
    vc = valeur_caracterisation(vG, vx)                              # 2 hypothèses
    vc = N.modus_ponens(ex_y, _dech(EX_Y, vc))
    vc = N.modus_ponens(h_func, _dech(E.est_fonctionnel(vG), vc))
    y_eq = N.modus_ponens(xy_in_G, equivalence_avant(vc))            # y = G(x)

    # y ∈ X_x, puis y ∈ ⋃_{ι∈I} X_ι
    gx_in = N.modus_ponens(x_in_I, instancie(h_vals, vx))            # G(x) ∈ X_x
    sym = N.modus_ponens(y_eq, symetrie(vy, E.valeur(vG, vx)))       # G(x) = y
    rw_val = N.modus_ponens(sym, N.s6(E.valeur(vG, vx), vy, "w",
                                      appartient(var("w"), E.valeur_famille(vf, vx))))
    y_in_Xx = N.modus_ponens(gx_in, equivalence_avant(rw_val))       # y ∈ X_x
    y_in_A = N.modus_ponens(conjonction_intro(x_in_I, y_in_Xx),
                            _reunion_famille_intro_t(vf, vI, vx, vy))

    # (x,y) ∈ I × ⋃X_ι, puis retour à z
    xy_in_prod = N.modus_ponens(conjonction_intro(x_in_I, y_in_A),
                                _couple_dans_produit_t(vx, vy, vI, A))
    rw_back = N.modus_ponens(h_eq, N.s6(vz, E.couple(vx, vy), "w", appartient(var("w"), PROD)))
    z_in_prod = N.modus_ponens(xy_in_prod, equivalence_arriere(rw_back))

    # élimination des témoins x, y (absents de la conclusion), puis généralisation
    z_in = N.modus_ponens(couple_z, existe_elimination(
        existe_elimination(_dech(EQ, z_in_prod), "y"), "x"))
    res = N.generalisation("z", _dech(appartient(vz, vG), z_in))

    assert res.conclusion == inclus(vG, PROD), "B2 : conclusion ≠ G ⊂ I × ⋃X_ι"
    assert res.hypotheses == frozenset({
        E.est_un_graphe(vG), E.est_fonctionnel(vG), egal(E.dom(vG), vI),
        hypothese_valeurs(vf, vI, idx, vG)}), "B2 : les QUATRE hypothèses exactes"
    return res


# ── B3 : l'adjonction d'un couple préserve « être un graphe » ─────────────────
# @livre Ch.II §3.1 Def.1 | E II.10 L.3-8 | PDF p.61
def graphe_apres_adjonction(g="G", j="j", x="x0"):
    """{ est_un_graphe(G) } ⊢ est_un_graphe( G ∪ {(j,x)} ).   [1 hypothèse EXACTE]

    z ∈ G∪{(j,x)} donne z∈G ou z∈{(j,x)} (AXIOME_REUNION) ; à gauche l'hypothèse
    conclut, à droite z = (j,x) est un couple (témoins j, x des liants x, y de
    `est_un_couple`).  Disjonction des cas, puis généralisation de z.

    Nécessaire au site « écriture » du prolongement d'un point du produit par un
    indice de plus (`iii_3_6_familles`), où le graphe adjoint doit rester un graphe."""
    vG, vj, vx, vz = _t(g), _t(j), _t(x), var("z")
    S = E.singleton(E.couple(vj, vx))
    T = E.reunion(vG, S)

    axr = N.axiome(E.theorie_ensembles(), E.AXIOME_REUNION)
    inst_r = instancie(instancie(instancie(axr, vG), S), vz)
    h_gr = N.assume(E.est_un_graphe(vG))
    h_z = N.assume(appartient(vz, T))
    disj = N.modus_ponens(h_z, equivalence_avant(inst_r))            # z∈G ou z∈S

    brA = _dech(appartient(vz, vG),
                N.modus_ponens(N.assume(appartient(vz, vG)), instancie(h_gr, vz)))

    hS = N.assume(appartient(vz, S))
    z_eq = N.modus_ponens(hS, equivalence_avant(singleton_membre(vz, E.couple(vj, vx))))
    inner = egal(vz, E.couple(var("x"), var("y")))
    ex_y = N.modus_ponens(z_eq, N.s5(subst_f(vj, "x", inner), vx, "y"))
    ex_xy = N.modus_ponens(ex_y, N.s5(existe("y", inner), vj, "x"))
    brB = _dech(appartient(vz, S), ex_xy)

    res = N.generalisation("z", _dech(appartient(vz, T), cas(disj, brA, brB)))
    assert res.conclusion == E.est_un_graphe(T), "B3 : conclusion ≠ est_un_graphe(G∪{(j,x)})"
    assert res.hypotheses == frozenset({E.est_un_graphe(vG)}), "B3 : hypothèse unique"
    return res


__all__ = ["inclus_produit_est_graphe", "hypothese_valeurs", "pivot_inclusion_produit",
           "graphe_apres_adjonction"]
