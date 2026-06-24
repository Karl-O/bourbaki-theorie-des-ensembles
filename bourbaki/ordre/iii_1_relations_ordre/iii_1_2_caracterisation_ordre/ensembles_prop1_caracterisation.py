"""§III.1 n°2 — PROPOSITION 1 (E.III.2) : caractérisation d'un ordre par son graphe.

ÉNONCÉ DE BOURBAKI (verbatim, E.III.2, Proposition 1) :
    « Pour qu'une correspondance Γ = (G, E, E) entre E et E soit un ordre sur E,
      il faut et il suffit que son graphe G satisfasse aux conditions suivantes :
        a) On a  G ∘ G = G.
        b) L'ensemble  G ∩ G⁻¹  est la diagonale Δ de E × E. »
    Preuve (extrait) : « De G ∩ G⁻¹ = Δ on déduit Δ ⊆ G ; d'où G = Δ ∘ G ⊆ G ∘ G,
      ce qui, compte tenu de G ∘ G ⊆ G, entraîne G ∘ G = G. »

CE MODULE FORMALISE LE SENS DIRECT (la NÉCESSITÉ) : SI G est le graphe d'un ordre
sur E, ALORS  (a) G∘G = G  et  (b) G ∩ G⁻¹ = Δ_E.  Les deux égalités de graphes
sont certifiées par le noyau LCF (primitives N.* uniquement), CLOSES SOUS DEUX
HYPOTHÈSES HONNÊTES (les antécédents de Bourbaki) :

    H1 = est_ordre(G, E)        (réflexivité sur E, antisymétrie, transitivité,
                                 E.III.1.1, prédicat de ensembles_ordre_relation)
    H2 = G ⊆ E × E              (le CHAMP : condition INHÉRENTE à la correspondance
                                 Γ = (G, E, E) de Bourbaki — « G est une partie de
                                 E × E », E.II.3.1, Déf. 1).  Formalisé exactement
                                 par  inclus(G, produit(E, E)).

Pourquoi H2 (le champ) est load-bearing — il l'est pour LES DEUX égalités :
  • (a) ⊇ : pour montrer G ⊆ G∘G il faut décomposer un élément quelconque w∈G en
        un couple (a,b) avec a,b∈E, afin d'invoquer la réflexivité (b,b)∈G et de
        composer.  C'est la voie Bourbaki Δ⊆G ⇒ G=Δ∘G⊆G∘G : Δ vit sur E, donc le
        passage par Δ exige que les éléments de G soient des couples sur E.
  • (b) ⊆ : pour montrer w∈G∩G⁻¹ ⇒ w∈Δ_E il faut, après antisymétrie (a=b), savoir
        a∈E pour conclure (a,a)∈Δ_E (Δ_E = {(a,a) | a∈E}).
  Le prédicat est_ordre(G,E) seul N'encode PAS le champ ; H2 est donc ajoutée
  comme hypothèse honnête, sous la forme Bourbaki la plus simple : G ⊆ E×E.

STRATÉGIE (chaque égalité = double inclusion ponctuelle au niveau COUPLE, puis A1).
  (a) composee(G,G) = G :
      ⊆ : w∈G∘G ⇒(couple_composee) ∃y((p,y)∈G et (y,r)∈G) ⇒(transitivité) (p,r)∈G
          = w ;  ⊇ : w∈G ⇒(champ) w=(a,b), b∈E ⇒(réflexivité) (b,b)∈G ; témoin y:=b
          dans couple_composee ⇒ (a,b)∈G∘G = w.
  (b) inter(G, reciproque(G)) = graphe_identite(E) :
      ⊆ : w∈G∩G⁻¹ ⇒ (a,b)∈G et (b,a)∈G ⇒(antisymétrie) a=b ; +(champ) a∈E ⇒ w∈Δ_E ;
      ⊇ : w∈Δ_E ⇒ w=(a,a), a∈E ⇒(réflexivité) (a,a)∈G et (couple_reciproque)
          (a,a)∈G⁻¹ ⇒ w∈G∩G⁻¹.
  Assemblage : extensionnalite_appliquee (double inclusion ⇒ égalité, A1).

NOTE : graphe_identite(E) = graphe_terme(E, x) est, EN EXTENSION, la diagonale Δ_E
(E.III.3.1) ; son lemme d'appartenance est membre_graphe_terme : pour T = x,
((a,b) ∈ graphe_identite(E)) ⇔ (a∈E et b=a).  C'est le Δ de l'énoncé Bourbaki.

STATUT : les DEUX égalités sont bouclées, CLOSES sous {est_ordre(G,E), G⊆E×E}.
theorie_ensembles() reste à 22 axiomes (aucun axiome ajouté).
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (
    var, egal, et, impl, appartient, existe, Terme)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, equivalence_transitivite, instancie)
from bourbaki.logique.i_3_quantifies.tactiques_abrege_quantif import (
    existe_elimination, alpha_existe, congruence_existe)
from bourbaki.logique.i_4_egalitaires.tactiques_abrege_egalite import symetrie, congruence_terme

from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_theoremes import (
    extensionnalite_appliquee, _instance_intersection)
from bourbaki.ensembles.fonctions.ii_3_2_reciproque.ensembles_reciproque import (
    couple_reciproque, _inst_recip, _inst_produit)
from bourbaki.ensembles.fonctions.ii_3_3_composee_graphes.ensembles_composee import (
    couple_composee, _inst_composee)
from bourbaki.ensembles.fonctions.ii_3_6_fonction_terme.ensembles_fonction_terme import (
    membre_graphe_terme, _inst_axiome)
from bourbaki.ensembles.familles.ii_2_produit_deux_ensembles.ensembles_produit import (
    couple_dans_produit_ssi)
from bourbaki.ensembles.ii_3_correspondances.ensembles_fondations_notions import graphe_identite
from bourbaki.ordre.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_relation import est_ordre


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def _couple(a, b):
    return E.couple(a, b)


def _dans(a, b, S):
    return appartient(_couple(a, b), S)


def champ(g, e):
    """champ(G,E) := G ⊆ E×E.   (E.II.3.1, Déf. 1 : Γ=(G,E,E) correspondance.)

    Le CHAMP de Bourbaki : le graphe d'une correspondance entre E et E est une
    partie de E×E.  Formellement  inclus(G, produit(E,E)) = (∀z)(z∈G ⇒ z∈E×E)."""
    return E.inclus(_t(g), E.produit(_t(e), _t(e)))


# ════════════════════════════════════════════════════════════════════════════
#  (a)  composee(G,G) = G   (G ∘ G = G,  condition a) de la Proposition 1)
# ════════════════════════════════════════════════════════════════════════════
def composee_idempotente(g="G", e="E"):
    """{ est_ordre(G,E),  G⊆E×E } ⊢ composee(G,G) = G.   (Prop 1 a), sens direct.)

    ⊆ (transitivité) :  (p,r)∈G∘G ⇒ ∃y((p,y)∈G et (y,r)∈G) ⇒ (p,r)∈G.
    ⊇ (réflexivité + champ) :  w∈G ⇒ w=(a,b) avec b∈E (champ) ⇒ (b,b)∈G
        (réflexivité) ⇒ témoin y:=b dans couple_composee ⇒ (a,b)∈G∘G = w.
    Assemblage par extensionnalité A1.  (Voie Bourbaki Δ⊆G ⇒ G=Δ∘G⊆G∘G.)"""
    vG, vE = _t(g), _t(e)
    vz, va, vb, vy = var("z"), var("a"), var("b"), var("y")
    Comp, Prod = E.composee(vG, vG), E.produit(vE, vE)

    Hord = N.assume(est_ordre(vG, vE))
    Hfield = N.assume(champ(vG, vE))
    refl = conjonction_elim_gauche(conjonction_elim_gauche(Hord))   # (∀x)(x∈E⇒(x,x)∈G)
    trans = conjonction_elim_droite(Hord)                          # transitivité

    # ── ⊆ :  (∀z)(z∈G∘G ⇒ z∈G) ───────────────────────────────────────────────
    comp_elem = _inst_composee(vG, vG, vz)   # (z∈G∘G) ⇔ (∃p)(∃r)(z=(p,r) et (∃y)((p,y)∈G et (y,r)∈G))
    Hz_comp = N.assume(appartient(vz, Comp))
    ex_comp = N.modus_ponens(Hz_comp, equivalence_avant(comp_elem))
    vp, vr = var("p"), var("r")
    inner_y = existe("y", et(_dans(vp, vy, vG), _dans(vy, vr, vG)))
    bodyA = et(egal(vz, _couple(vp, vr)), inner_y)
    HbodyA = N.assume(bodyA)
    z_eq_pr = conjonction_elim_gauche(HbodyA)              # z=(p,r)
    hy = conjonction_elim_droite(HbodyA)                  # (∃y)((p,y)∈G et (y,r)∈G)
    bodyY = et(_dans(vp, vy, vG), _dans(vy, vr, vG))
    HbodyY = N.assume(bodyY)
    trans_pyr = instancie(instancie(instancie(trans, vp), vy), vr)   # ⇒ (p,r)∈G
    pr_G = N.modus_ponens(HbodyY, trans_pyr)
    impExy = existe_elimination(N.loi_deduction(bodyY, pr_G), "y")    # (∃y)bodyY ⇒ (p,r)∈G
    pr_G2 = N.modus_ponens(hy, impExy)                   # (p,r)∈G  (sous bodyA)
    leibA = N.modus_ponens(z_eq_pr, N.s6(vz, _couple(vp, vr), "t", appartient(var("t"), vG)))
    z_G = N.modus_ponens(pr_G2, equivalence_arriere(leibA))   # z∈G
    impExp = existe_elimination(existe_elimination(
        N.loi_deduction(bodyA, z_G), "r"), "p")          # (∃p)(∃r)bodyA ⇒ z∈G
    z_G_final = N.modus_ponens(ex_comp, impExp)
    incl_comp_G = N.generalisation("z", N.loi_deduction(appartient(vz, Comp), z_G_final))

    # ── ⊇ :  (∀z)(z∈G ⇒ z∈G∘G) ───────────────────────────────────────────────
    # champ : z∈G ⇒ z∈E×E ⇒ (∃a)(∃b)((z=(a,b) et a∈E) et b∈E)  (a,b ≠ binders p,r,y
    #         de couple_composee : on α-renomme les binders p,q du produit en a,b)
    prod_elem = _inst_produit(vE, vE, vz)
    ren1 = alpha_existe("p", "a", existe("q",
        et(et(egal(vz, _couple(var("p"), var("q"))), appartient(var("p"), vE)),
           appartient(var("q"), vE))))
    prod_ab = equivalence_transitivite(prod_elem, ren1)
    ren2 = congruence_existe(alpha_existe("q", "b",
        et(et(egal(vz, _couple(va, var("q"))), appartient(va, vE)),
           appartient(var("q"), vE))), "a")
    prod_ab = equivalence_transitivite(prod_ab, ren2)    # (z∈E×E) ⇔ (∃a)(∃b)((z=(a,b) et a∈E) et b∈E)
    Hz_G = N.assume(appartient(vz, vG))
    ex_prod = N.modus_ponens(N.modus_ponens(Hz_G, instancie(Hfield, vz)),
                             equivalence_avant(prod_ab))
    body3 = et(et(egal(vz, _couple(va, vb)), appartient(va, vE)), appartient(vb, vE))
    Hbody3 = N.assume(body3)
    z_eq_ab = conjonction_elim_gauche(conjonction_elim_gauche(Hbody3))   # z=(a,b)
    bE = conjonction_elim_droite(Hbody3)                                # b∈E
    leibAB = N.modus_ponens(z_eq_ab, N.s6(vz, _couple(va, vb), "t", appartient(var("t"), vG)))
    ab_G = N.modus_ponens(Hz_G, equivalence_avant(leibAB))   # (a,b)∈G
    bb_G = N.modus_ponens(bE, instancie(refl, vb))           # (b,b)∈G  (réflexivité en b∈E)
    cc_ab = couple_composee(vG, vG, "a", "b")                # ((a,b)∈G∘G) ⇔ (∃y)((a,y)∈G et (y,b)∈G)
    wit_ab = conjonction_intro(ab_G, bb_G)                   # (a,b)∈G et (b,b)∈G = (b|y)(...)
    ex_y_body = N.modus_ponens(wit_ab,
        N.s5(et(_dans(va, vy, vG), _dans(vy, vb, vG)), vb, "y"))
    ab_comp = N.modus_ponens(ex_y_body, equivalence_arriere(cc_ab))   # (a,b)∈G∘G
    leibCompZ = N.modus_ponens(z_eq_ab, N.s6(vz, _couple(va, vb), "t", appartient(var("t"), Comp)))
    z_comp = N.modus_ponens(ab_comp, equivalence_arriere(leibCompZ))   # z∈G∘G
    impExa = existe_elimination(existe_elimination(
        N.loi_deduction(body3, z_comp), "b"), "a")
    z_comp_final = N.modus_ponens(ex_prod, impExa)
    incl_G_comp = N.generalisation("z", N.loi_deduction(appartient(vz, vG), z_comp_final))

    ext = extensionnalite_appliquee(Comp, vG)
    return N.modus_ponens(conjonction_intro(incl_comp_G, incl_G_comp), ext)   # G∘G = G


# ════════════════════════════════════════════════════════════════════════════
#  (b)  inter(G, reciproque(G)) = graphe_identite(E)   (G ∩ G⁻¹ = Δ_E, cond. b)
# ════════════════════════════════════════════════════════════════════════════
def intersection_reciproque_est_diagonale(g="G", e="E"):
    """{ est_ordre(G,E),  G⊆E×E } ⊢ inter(G, reciproque(G)) = graphe_identite(E).

    C'est  G ∩ G⁻¹ = Δ_E  (condition b) de la Proposition 1, sens direct).
    ⊆ (antisymétrie + champ) :  w∈G∩G⁻¹ ⇒ (a,b)∈G et (b,a)∈G ⇒ a=b (antisym) ;
        a∈E (champ) ⇒ w=(a,a) avec a∈E ⇒ w∈Δ_E.
    ⊇ (réflexivité) :  w∈Δ_E ⇒ w=(a,a), a∈E ⇒ (a,a)∈G (réflexivité) et
        (a,a)∈G⁻¹ (couple_reciproque) ⇒ w∈G∩G⁻¹.
    Assemblage par extensionnalité A1."""
    vG, vE = _t(g), _t(e)
    vz, va, vb = var("z"), var("a"), var("b")
    Grec = E.reciproque(vG)
    Inter = E.intersection(vG, Grec)
    Id = graphe_identite(vE)                              # = graphe_terme(E, x) = Δ_E

    Hord = N.assume(est_ordre(vG, vE))
    Hfield = N.assume(champ(vG, vE))
    refl = conjonction_elim_gauche(conjonction_elim_gauche(Hord))   # réflexivité sur E
    antis = conjonction_elim_droite(conjonction_elim_gauche(Hord))  # antisymétrie

    inter_z = _instance_intersection(vG, Grec, vz)        # (z∈inter) ⇔ (z∈G et z∈G⁻¹)

    # ── ⊆ :  (∀z)(z∈G∩G⁻¹ ⇒ z∈Δ_E) ──────────────────────────────────────────
    # z∈G⁻¹ ⇔ (∃p)(∃q)(z=(p,q) et (q,p)∈G) ; α-renomme p,q → a,b (binders p,q
    # interdits par couple_dans_produit_ssi utilisé plus bas).
    rec0 = _inst_recip(vG, vz)
    r1 = alpha_existe("p", "a", existe("q",
        et(egal(vz, _couple(var("p"), var("q"))), _dans(var("q"), var("p"), vG))))
    rec_ab = equivalence_transitivite(rec0, r1)
    r2 = congruence_existe(alpha_existe("q", "b",
        et(egal(vz, _couple(va, var("q"))), _dans(var("q"), va, vG))), "a")
    rec_ab = equivalence_transitivite(rec_ab, r2)         # (z∈G⁻¹) ⇔ (∃a)(∃b)(z=(a,b) et (b,a)∈G)

    Hz_inter = N.assume(appartient(vz, Inter))
    z_pair = N.modus_ponens(Hz_inter, equivalence_avant(inter_z))   # z∈G et z∈G⁻¹
    zG = conjonction_elim_gauche(z_pair)                  # z∈G
    zGrec = conjonction_elim_droite(z_pair)               # z∈G⁻¹
    ex_body = N.modus_ponens(zGrec, equivalence_avant(rec_ab))      # (∃a)(∃b)(z=(a,b) et (b,a)∈G)
    body = et(egal(vz, _couple(va, vb)), _dans(vb, va, vG))
    Hbody = N.assume(body)
    z_eq_ab = conjonction_elim_gauche(Hbody)              # z=(a,b)
    ba_G = conjonction_elim_droite(Hbody)                 # (b,a)∈G
    leib_in = N.modus_ponens(z_eq_ab, N.s6(vz, _couple(va, vb), "t", appartient(var("t"), vG)))
    ab_G = N.modus_ponens(zG, equivalence_avant(leib_in)) # (a,b)∈G
    antis_ab = instancie(instancie(antis, va), vb)        # ((a,b)∈G et (b,a)∈G) ⇒ a=b
    a_eq_b = N.modus_ponens(conjonction_intro(ab_G, ba_G), antis_ab)   # a=b
    # champ : (a,b)∈G ⇒ (a,b)∈E×E ⇒ a∈E
    ab_prod = N.modus_ponens(ab_G, instancie(Hfield, _couple(va, vb)))
    aE_bE = N.modus_ponens(ab_prod, equivalence_avant(couple_dans_produit_ssi(va, vb, vE, vE)))
    aE = conjonction_elim_gauche(aE_bE)                   # a∈E
    mid_ab = membre_graphe_terme(vE, var("x"), "a", "b", "x", "y")   # ((a,b)∈Δ_E) ⇔ (a∈E et b=a)
    b_eq_a = N.modus_ponens(a_eq_b, symetrie(va, vb))     # b=a
    ab_Id = N.modus_ponens(conjonction_intro(aE, b_eq_a), equivalence_arriere(mid_ab))   # (a,b)∈Δ_E
    leib_id = N.modus_ponens(z_eq_ab, N.s6(vz, _couple(va, vb), "t", appartient(var("t"), Id)))
    z_Id = N.modus_ponens(ab_Id, equivalence_arriere(leib_id))   # z∈Δ_E
    impExa = existe_elimination(existe_elimination(
        N.loi_deduction(body, z_Id), "b"), "a")
    z_Id_final = N.modus_ponens(ex_body, impExa)
    incl_inter_id = N.generalisation("z", N.loi_deduction(appartient(vz, Inter), z_Id_final))

    # ── ⊇ :  (∀z)(z∈Δ_E ⇒ z∈G∩G⁻¹) ──────────────────────────────────────────
    # z∈Δ_E ⇔ (∃x)(∃y)((z=(x,y) et x∈E) et y=x)  (axiome graphe_terme, T=x)
    id_elem = _inst_axiome(vE, var("x"), vz, "x", "y")
    Hz_id = N.assume(appartient(vz, Id))
    ex_body2 = N.modus_ponens(Hz_id, equivalence_avant(id_elem))
    vx2, vy2 = var("x"), var("y")
    body2 = et(et(egal(vz, _couple(vx2, vy2)), appartient(vx2, vE)), egal(vy2, vx2))
    Hbody2 = N.assume(body2)
    z_eq_xy = conjonction_elim_gauche(conjonction_elim_gauche(Hbody2))   # z=(x,y)
    x_inE = conjonction_elim_droite(conjonction_elim_gauche(Hbody2))     # x∈E
    y_eq_x = conjonction_elim_droite(Hbody2)                            # y=x
    xx_G = N.modus_ponens(x_inE, instancie(refl, vx2))   # (x,x)∈G  (réflexivité)
    cr_xx = couple_reciproque(vG, "x", "x")              # ((x,x)∈G⁻¹) ⇔ ((x,x)∈G)
    xx_Grec = N.modus_ponens(xx_G, equivalence_arriere(cr_xx))   # (x,x)∈G⁻¹
    # (x,y)=(x,x)  par congruence depuis y=x ; transport (x,x)→(x,y) puis →z
    xy_eq_xx = N.modus_ponens(y_eq_x, congruence_terme(vy2, vx2, _couple(vx2, var("w"))))
    leib_G = N.modus_ponens(xy_eq_xx,
        N.s6(_couple(vx2, vy2), _couple(vx2, vx2), "t", appartient(var("t"), vG)))
    xy_G = N.modus_ponens(xx_G, equivalence_arriere(leib_G))   # (x,y)∈G
    leib_Grec = N.modus_ponens(xy_eq_xx,
        N.s6(_couple(vx2, vy2), _couple(vx2, vx2), "t", appartient(var("t"), Grec)))
    xy_Grec = N.modus_ponens(xx_Grec, equivalence_arriere(leib_Grec))   # (x,y)∈G⁻¹
    leibzG = N.modus_ponens(z_eq_xy, N.s6(vz, _couple(vx2, vy2), "t", appartient(var("t"), vG)))
    z_G = N.modus_ponens(xy_G, equivalence_arriere(leibzG))   # z∈G
    leibzGrec = N.modus_ponens(z_eq_xy, N.s6(vz, _couple(vx2, vy2), "t", appartient(var("t"), Grec)))
    z_Grec = N.modus_ponens(xy_Grec, equivalence_arriere(leibzGrec))   # z∈G⁻¹
    z_inter = N.modus_ponens(conjonction_intro(z_G, z_Grec), equivalence_arriere(inter_z))
    impExx = existe_elimination(existe_elimination(
        N.loi_deduction(body2, z_inter), "y"), "x")
    z_inter_final = N.modus_ponens(ex_body2, impExx)
    incl_id_inter = N.generalisation("z", N.loi_deduction(appartient(vz, Id), z_inter_final))

    ext = extensionnalite_appliquee(Inter, Id)
    return N.modus_ponens(conjonction_intro(incl_inter_id, incl_id_inter), ext)   # G∩G⁻¹ = Δ_E


def caracterisation_ordre_sens_direct(g="G", e="E"):
    """{ est_ordre(G,E), G⊆E×E } ⊢ (composee(G,G)=G  et  inter(G,G⁻¹)=Δ_E).

    Les DEUX conditions a) et b) de la Proposition 1 réunies (sens direct).
    Conjonction des deux égalités certifiées ci-dessus."""
    return conjonction_intro(composee_idempotente(g, e),
                             intersection_reciproque_est_diagonale(g, e))


__all__ = [
    "champ",
    "composee_idempotente",
    "intersection_reciproque_est_diagonale",
    "caracterisation_ordre_sens_direct",
]
