"""§II.5 — COMMUTATION du produit avec l'intersection (binaire), corollaire Prop. 9.

    ( (∀ι)(ι∈I ⇒ Z_ι = X_ι ∩ Y_ι) )  ⇒  ( ∏_{ι∈I} Z_ι = (∏_{ι∈I} X_ι) ∩ (∏_{ι∈I} Y_ι) ).

C'est la version BINAIRE (deux familles X, Y) de la commutation produit/intersection
(E.II.5.6, corollaire de la Prop. 9 ; cf. `produit_distrib_inter_membre` pour la
version intersection-de-famille, sens « ⊂ »).  Ici l'égalité COMPLÈTE est prouvée,
SANS récurrence, INCONDITIONNELLE modulo l'unique hypothèse HONNÊTE qui DÉFINIT la
famille-intersection Z (ι ↦ X_ι ∩ Y_ι) — exactement comme `produit_egal_si_facteurs_egaux`
prend (∀ι) X_ι=Y_ι.  Cette hypothèse est satisfiable, porteuse, et ∉ conclusion.

Preuve (DOUBLE INCLUSION + A1) :

  ⊂ :  G ∈ ∏Z  ⇒  G(ι) ∈ Z_ι = X_ι∩Y_ι  ⇒  G(ι)∈X_ι  et  G(ι)∈Y_ι
                ⇒  G ∈ ∏X  et  G ∈ ∏Y    ⇒  G ∈ (∏X)∩(∏Y).
  ⊃ :  G ∈ (∏X)∩(∏Y)  ⇒  G∈∏X et G∈∏Y  ⇒  G(ι)∈X_ι et G(ι)∈Y_ι
                       ⇒  G(ι)∈X_ι∩Y_ι = Z_ι  ⇒  G ∈ ∏Z.

Briques RÉUTILISÉES (toutes closes) :
  • `membre_produit_famille(f,I,F)`  ⊢ (G∈∏) ⇔ ( G fonct. ∧ dom G=I ∧ (∀ι)(ι∈I⇒G(ι)∈X_ι) ) ;
  • `_instance_inter(a,b,z)`         ⊢ (z∈a∩b) ⇔ (z∈a et z∈b)  (AXIOME_INTER) ;
  • `_congruence_appartient(t,a,b)`  ⊢ (a=b) ⇒ ((t∈a)⇒(t∈b))  (réécriture appartenance) ;
  • `extensionnalite_appliquee`      ⊢ (u⊂v et v⊂u) ⇒ u=v     (A1).

theorie_ensembles() RESTE à 22 axiomes (aucun axiome neuf).
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (var, et, impl, appartient, egal, inclus,
                                       pourtout)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    instancie, equivalence_avant, equivalence_arriere,
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import symetrie
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import alpha_pour_tout
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_theoremes import extensionnalite_appliquee
from bourbaki.ii_theorie_des_ensembles.ii_5_produit_famille.ii_5_definitions.ensembles_produit_famille import membre_produit_famille
from bourbaki.ii_theorie_des_ensembles.ii_5_produit_famille.ii_5_definitions.ensembles_produit_ecriture import (
    composants_membre, transporter_dans_produit)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ii_1_algebre_booleenne.ensembles_algebre_booleenne import _instance_inter
from bourbaki.ii_theorie_des_ensembles.ii_5_produit_famille.ii_5_6_7_algebre_produit.ensembles_produit_props2 import _congruence_appartient


# ── énoncé / cible ────────────────────────────────────────────────────────────
def _enonce(f="f", g="g", h="h", i="I"):
    """( (∀ι)(ι∈I ⇒ Z_ι = X_ι ∩ Y_ι) ) ⇒ ( ∏Z = (∏X) ∩ (∏Y) )."""
    vf, vg, vh, vI = var(f), var(g), var(h), var(i)
    vi = var("i")
    Xi = E.valeur_famille(vf, vi)
    Yi = E.valeur_famille(vg, vi)
    Zi = E.valeur_famille(vh, vi)
    hyp = pourtout("i", impl(appartient(vi, vI),
                             egal(Zi, E.intersection(Xi, Yi))))
    concl = egal(E.produit_famille(vh, vI),
                 E.intersection(E.produit_famille(vf, vI), E.produit_famille(vg, vI)))
    return impl(hyp, concl)


def _cible(f="f", g="g", h="h", i="I"):
    return _enonce(f, g, h, i)


# ── sens ⊂ :  ∏Z ⊂ (∏X) ∩ (∏Y)  (sous H) ─────────────────────────────────────
def _inclusion_avant(vf, vg, vh, vI, hH, ff="G", iota="i"):
    vG, viota = var(ff), var(iota)
    Xi = E.valeur_famille(vf, viota)
    Yi = E.valeur_famille(vg, viota)
    Zi = E.valeur_famille(vh, viota)
    Gi = E.valeur(vG, viota)
    prodX = E.produit_famille(vf, vI)
    prodY = E.produit_famille(vg, vI)
    prodZ = E.produit_famille(vh, vI)

    eq_X = membre_produit_famille(vf.nom, vI.nom, ff)
    eq_Y = membre_produit_famille(vg.nom, vI.nom, ff)
    eq_Z = membre_produit_famille(vh.nom, vI.nom, ff)

    hG = N.assume(appartient(vG, prodZ))                 # G ∈ ∏Z
    _incl_Z, _fonct, _dom, forall_Z = composants_membre(hG, vh, vI, vG)

    # build (∀ι)(ι∈I⇒G(ι)∈X_ι) and (∀ι)(ι∈I⇒G(ι)∈Y_ι)
    hi = N.assume(appartient(viota, vI))                 # ι∈I
    GinZ = N.modus_ponens(hi, instancie(forall_Z, viota))     # G(ι)∈Z_ι
    eqZ = N.modus_ponens(hi, instancie(hH, viota))            # Z_ι = X_ι∩Y_ι
    cong = N.modus_ponens(eqZ, _congruence_appartient(Gi, Zi, E.intersection(Xi, Yi)))
    GinInter = N.modus_ponens(GinZ, cong)                # G(ι)∈X_ι∩Y_ι
    pair = N.modus_ponens(GinInter, equivalence_avant(_instance_inter(Xi, Yi, Gi)))
    GinX = conjonction_elim_gauche(pair)                 # G(ι)∈X_ι
    GinY = conjonction_elim_droite(pair)                 # G(ι)∈Y_ι
    impX_i = N.loi_deduction(appartient(viota, vI), GinX)
    impY_i = N.loi_deduction(appartient(viota, vI), GinY)
    forall_X = N.generalisation(iota, impX_i)
    forall_Y = N.generalisation(iota, impY_i)

    GinPX = transporter_dans_produit(hG, forall_X, vG, vh, vf, vI, iota)   # G∈∏X
    GinPY = transporter_dans_produit(hG, forall_Y, vG, vh, vg, vI, iota)   # G∈∏Y
    # G ∈ (∏X)∩(∏Y)
    GinPInter = N.modus_ponens(conjonction_intro(GinPX, GinPY),
                               equivalence_arriere(_instance_inter(prodX, prodY, vG)))
    imp_G = N.loi_deduction(appartient(vG, prodZ), GinPInter)    # G∈∏Z ⇒ G∈(∏X∩∏Y)
    incl_G = N.generalisation(ff, imp_G)
    membre = impl(appartient(vG, prodZ),
                  appartient(vG, E.intersection(prodX, prodY)))
    return N.modus_ponens(incl_G, equivalence_avant(alpha_pour_tout(ff, "z", membre)))


# ── sens ⊃ :  (∏X) ∩ (∏Y) ⊂ ∏Z  (sous H) ─────────────────────────────────────
def _inclusion_arriere(vf, vg, vh, vI, hH, ff="G", iota="i"):
    vG, viota = var(ff), var(iota)
    Xi = E.valeur_famille(vf, viota)
    Yi = E.valeur_famille(vg, viota)
    Zi = E.valeur_famille(vh, viota)
    Gi = E.valeur(vG, viota)
    prodX = E.produit_famille(vf, vI)
    prodY = E.produit_famille(vg, vI)
    prodZ = E.produit_famille(vh, vI)

    eq_X = membre_produit_famille(vf.nom, vI.nom, ff)
    eq_Y = membre_produit_famille(vg.nom, vI.nom, ff)
    eq_Z = membre_produit_famille(vh.nom, vI.nom, ff)

    hG = N.assume(appartient(vG, E.intersection(prodX, prodY)))   # G ∈ ∏X∩∏Y
    pairG = N.modus_ponens(hG, equivalence_avant(_instance_inter(prodX, prodY, vG)))
    GinPX = conjonction_elim_gauche(pairG)               # G∈∏X
    GinPY = conjonction_elim_droite(pairG)               # G∈∏Y
    _incl_X, _fonct, _dom, forall_X = composants_membre(GinPX, vf, vI, vG)
    forall_Y = composants_membre(GinPY, vg, vI, vG)[3]   # (∀ι)(ι∈I⇒G(ι)∈Y_ι)

    hi = N.assume(appartient(viota, vI))                 # ι∈I
    GinX = N.modus_ponens(hi, instancie(forall_X, viota))     # G(ι)∈X_ι
    GinY = N.modus_ponens(hi, instancie(forall_Y, viota))     # G(ι)∈Y_ι
    GinInter = N.modus_ponens(conjonction_intro(GinX, GinY),
                              equivalence_arriere(_instance_inter(Xi, Yi, Gi)))  # G(ι)∈X∩Y
    eqZ = N.modus_ponens(hi, instancie(hH, viota))            # Z_ι = X_ι∩Y_ι
    eqZ_sym = N.modus_ponens(eqZ, symetrie(Zi, E.intersection(Xi, Yi)))   # X∩Y = Z_ι
    cong = N.modus_ponens(eqZ_sym, _congruence_appartient(Gi, E.intersection(Xi, Yi), Zi))
    GinZ = N.modus_ponens(GinInter, cong)                # G(ι)∈Z_ι
    imp_i = N.loi_deduction(appartient(viota, vI), GinZ)
    forall_Z = N.generalisation(iota, imp_i)
    GinPZ = transporter_dans_produit(GinPX, forall_Z, vG, vf, vh, vI, iota)   # G∈∏Z
    imp_G = N.loi_deduction(appartient(vG, E.intersection(prodX, prodY)), GinPZ)
    incl_G = N.generalisation(ff, imp_G)
    membre = impl(appartient(vG, E.intersection(prodX, prodY)),
                  appartient(vG, prodZ))
    return N.modus_ponens(incl_G, equivalence_avant(alpha_pour_tout(ff, "z", membre)))


# ── théorème principal ────────────────────────────────────────────────────────
# @livre Ch.II §5.6 Cor.- | E II.38 L.6-13 | PDF p.89
def produit_inter_egal_inter_produits(f="f", g="g", h="h", i="I"):
    """⊢ ( (∀ι)(ι∈I ⇒ Z_ι = X_ι ∩ Y_ι) ) ⇒ ( ∏Z = (∏X) ∩ (∏Y) ).
       (§II.5, corollaire Prop. 9 — commutation produit/intersection, version binaire.)

    X_ι = valeur_famille(f,ι), Y_ι = valeur_famille(g,ι), Z_ι = valeur_famille(h,ι).
    L'hypothèse identifie la famille-intersection Z à ι↦X_ι∩Y_ι (déf. de Z) ; sous
    elle, double inclusion (∏Z⊂(∏X)∩(∏Y) et réciproque) puis A1."""
    vf, vg, vh, vI = var(f), var(g), var(h), var(i)
    vi = var("i")
    Xi = E.valeur_famille(vf, vi)
    Yi = E.valeur_famille(vg, vi)
    Zi = E.valeur_famille(vh, vi)
    hyp = pourtout("i", impl(appartient(vi, vI),
                             egal(Zi, E.intersection(Xi, Yi))))
    hH = N.assume(hyp)

    incl_avant = _inclusion_avant(vf, vg, vh, vI, hH)     # ∏Z ⊂ (∏X)∩(∏Y)
    incl_arr = _inclusion_arriere(vf, vg, vh, vI, hH)     # (∏X)∩(∏Y) ⊂ ∏Z

    prodX = E.produit_famille(vf, vI)
    prodY = E.produit_famille(vg, vI)
    prodZ = E.produit_famille(vh, vI)
    ext = extensionnalite_appliquee(prodZ, E.intersection(prodX, prodY))
    eq = N.modus_ponens(conjonction_intro(incl_avant, incl_arr), ext)   # ∏Z = (∏X)∩(∏Y)

    res = N.loi_deduction(hyp, eq)
    assert res.conclusion == _cible(f, g, h, i), \
        "produit_inter_egal_inter_produits : conclusion ≠ cible"
    return res


__all__ = ["produit_inter_egal_inter_produits", "_cible", "_enonce"]
