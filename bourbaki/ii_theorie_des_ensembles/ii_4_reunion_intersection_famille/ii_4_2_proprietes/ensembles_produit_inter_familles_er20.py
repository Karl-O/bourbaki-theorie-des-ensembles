"""Résumé E.R.20 item 8 (n°92) — (⋂X_ι)×(⋂Y_ι) = ⋂(X_ι×Y_ι)  (mêmes indices).

Bourbaki (E.R.20, formule (44)) : pour deux familles (X_ι)_{ι∈I}, (Y_ι)_{ι∈I} de
même ensemble d'indices I ≠ ∅,  (⋂_ι X_ι)×(⋂_ι Y_ι) = ⋂_ι (X_ι×Y_ι).

ÉNONCÉ DÉRIVÉ (CLOS, 0 hyp ; la 3ᵉ famille H = ι↦X_ι×Y_ι et la non-vacuité sont
mises en ANTÉCÉDENT — graphe_terme_valeur vit en théorie dédiée ≠22, on ne construit
donc pas H mais on suppose « H est la famille des produits ») :

    ⊢ (  ¬(I=∅)
         et (∀i)(i∈I ⇒ H_i = X_i×Y_i)  )
      ⇒  ( (⋂X_ι)×(⋂Y_ι) = ⋂H_ι )

DÉMONSTRATION (extensionnalité, z générique ; témoins existentiels du produit) :
  ⇒ : z∈(⋂X)×(⋂Y) ⇒ (∃p,q)(z=(p,q), p∈⋂X, q∈⋂Y) ; ∀i∈I : p∈X_i, q∈Y_i
      [membre_inter_famille] ⇒ (p,q)∈X_i×Y_i=H_i ⇒ z∈H_i ⇒ z∈⋂H.
  ⇐ : z∈⋂H ⇒ z∈H_{i0} (i0 témoin de ¬(I=∅)) = X_{i0}×Y_{i0} ⇒ (∃p,q)(z=(p,q)…) ;
      ∀i∈I : (p,q)∈H_i=X_i×Y_i ⇒ p∈X_i, q∈Y_i ⇒ p∈⋂X, q∈⋂Y ⇒ z∈(⋂X)×(⋂Y).

Ce commit : SENS ⇒ (membership).  theorie_ensembles() inchangée (22 axiomes).

MIGRATION Déf. 2 (⋂ = sélection dans ⋃, E II.22) — ÉNONCÉ INCHANGÉ (issue A).
L'axiome d'appartenance à ⋂ donne désormais une CONJONCTION (z∈⋃ et (∀i)…) :
  • l'ÉLIMINATION reste GRATUITE et inconditionnelle (`inter_elim`, CLOS) — les
    sites qui ne font que projeter migrent SANS RIEN CHANGER ;
  • l'INTRODUCTION réclame un témoin d'indice — mais ce témoin ne coûte RIEN dès
    qu'on tient déjà un élément d'une intersection de MÊME ensemble d'indices :
    p∈⋂X ⊂ ⋃X donne (∃i)(i∈I et p∈X_i), d'où ⊢ T₀∈I (`temoin_indice_via_inter`).
C'est le cas du sens ⇒, dont le corps porte déjà p∈⋂X : il reste donc à SA SEULE
hypothèse d'avant-migration (`hyp_produit_famille`), sans ¬(I=∅).  Le sens ⇐
garde ¬(I=∅) — l'hypothèse que Bourbaki écrit en E.R.20 (44), qu'il portait DÉJÀ
avant la migration — et le théorème public la décharge exactement comme avant.
Énoncé public INCHANGÉ à l'octet près ; aucune conclusion affaiblie.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, egal, et, non, impl, appartient, pourtout)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    instancie, equivalence_avant, equivalence_arriere,
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import symetrie
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import existe_elimination, alpha_existe
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_intersection_fondation.ensembles_inter_migration_ii4 import (
    caracterisation_inter_famille_indices_non_vide)
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_image_famille.ensembles_image_inter_pont_ii4 import (
    inter_elim, inter_intro, temoin_indice_via_inter)
from bourbaki.ii_theorie_des_ensembles.ii_2_couples.ii_2_2_produit_deux_ensembles.ensembles_produit import (
    _instance_produit, couple_dans_produit_ssi)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_vide import non_vide_ssi_element
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_theoremes import extensionnalite_appliquee


def _cut(thm, preuve_hyp):
    H = preuve_hyp.conclusion
    return N.modus_ponens(preuve_hyp, N.loi_deduction(H, thm))


def hyp_produit_famille(f="f", g="g", h="H", i="I"):
    """« H est la famille des produits » := (∀i)(i∈I ⇒ H_i = X_i×Y_i)."""
    vf, vg, vh, vI, vi = var(f), var(g), var(h), var(i), var("i")
    return pourtout("i", impl(appartient(vi, vI),
                             egal(E.valeur_famille(vh, vi),
                                  E.produit(E.valeur_famille(vf, vi), E.valeur_famille(vg, vi)))))


def _interf(f, i):
    return E.inter_famille(var(f), var(i))


def _carac_inter(f, i, terme):
    """Sous l'hypothèse ¬(I=∅) :  ⊢ (T ∈ ⋂_{ι∈I} X_ι) ⇔ (∀i)((i∈I) ⇒ T∈X_i).

    RÉSERVÉ AUX DEUX SITES D'INTRODUCTION DU SENS ⇐ (p∈⋂X et q∈⋂Y reconstruits à
    partir du (∀i)).  Là, ¬(I=∅) est DÉJÀ assumée par `_dir_interH_vers_produit`
    — elle lui sert à produire l'indice i₀ — donc s'en servir ne coûte AUCUNE
    hypothèse supplémentaire, et le compteur du lemme reste celui d'avant la
    migration.  Elle est déchargée par `produit_inter_familles`, dont l'énoncé la
    portait DÉJÀ en antécédent (E.R.20 : « I ≠ ∅ »).

    NE PAS l'employer pour ÉLIMINER : `inter_elim` (projection droite de la
    conjonction de sélection) est CLOS et INCONDITIONNEL — l'élimination migre
    sans rien changer, l'appeler via ce pont facturerait ¬(I=∅) pour rien."""
    h_ne = N.assume(non(egal(var(i), E.VIDE)))
    carac = N.modus_ponens(h_ne, caracterisation_inter_famille_indices_non_vide(f, i, "z"))
    return instancie(carac, terme)


def _cpp_ssi(u, v, a, b):
    """⊢ ((u,v)∈a×b) ⇔ (u∈a et v∈b)  pour des TERMES u,v,a,b (évite la collision
    avec les liants internes « p,q » de couple_dans_produit_ssi via generalize+instancie)."""
    base = couple_dans_produit_ssi("s", "t", "A", "B")
    g = N.generalisation("s", N.generalisation("t", N.generalisation("A", N.generalisation("B", base))))
    return instancie(instancie(instancie(instancie(g, u), v), a), b)


# @livre Ch.R §4 Prop.- | E.R.20 item 8 (44) | PDF p.323  (sens ⇒ : (⋂X)×(⋂Y) ⊂ ⋂(X×Y))
def _dir_produit_vers_interH(f="f", g="g", h="H", i="I", z="z"):
    """⊢ {hyp_produit_famille}  z∈(⋂X)×(⋂Y) ⇒ z∈⋂H.   UNE seule hypothèse.

    Le témoin d'indice qu'exige désormais l'INTRODUCTION dans ⋂H est GRATUIT ici :
    le corps de l'existentiel du produit porte déjà p∈⋂_{ι∈I} X_ι, et ⋂ ⊂ ⋃ donne
    (∃i)(i∈I et p∈X_i), donc ⊢ T₀∈I par `temoin_indice_via_inter` — MÊME ensemble
    d'indices I que ⋂H, donc T₀ sert tel quel.  Supposer ¬(I=∅) serait un
    affaiblissement gratuit : ce lemme n'en a pas besoin, ni avant ni après la
    migration Déf. 2.  Les deux passages vers le (∀i) sont de pure ÉLIMINATION
    (`inter_elim`, CLOS, inconditionnel)."""
    vf, vg, vh, vI, vz = var(f), var(g), var(h), var(i), var(z)
    interf, interg = _interf(f, i), _interf(g, i)
    hHp = N.assume(hyp_produit_famille(f, g, h, i))
    hz = N.assume(appartient(vz, E.produit(interf, interg)))
    ex_pq = N.modus_ponens(hz, equivalence_avant(_instance_produit(interf, interg, vz)))  # (∃p∃q)(z=(p,q)∧p∈⋂X∧q∈⋂Y)

    vp, vq, vi = var("p"), var("q"), var("i")
    body = et(et(egal(vz, E.couple(vp, vq)), appartient(vp, interf)), appartient(vq, interg))
    hb = N.assume(body)
    z_eq = conjonction_elim_gauche(conjonction_elim_gauche(hb))     # z=(p,q)
    p_inter = conjonction_elim_droite(conjonction_elim_gauche(hb))  # p∈⋂X
    q_inter = conjonction_elim_droite(hb)                           # q∈⋂Y
    T0, T0_dans_I = temoin_indice_via_inter(vf, vI, vp, p_inter)    # ⊢ T₀∈I, sans ¬(I=∅)
    p_all = N.modus_ponens(p_inter, inter_elim(vf, vI, vp))         # ∀i(i∈I⇒p∈X_i)
    q_all = N.modus_ponens(q_inter, inter_elim(vg, vI, vq))         # ∀i(i∈I⇒q∈Y_i)

    hi = N.assume(appartient(vi, vI))
    p_fi = N.modus_ponens(hi, instancie(p_all, vi))                # p∈X_i
    q_gi = N.modus_ponens(hi, instancie(q_all, vi))                # q∈Y_i
    fi, gi = E.valeur_famille(vf, vi), E.valeur_famille(vg, vi)
    Hi = E.valeur_famille(vh, vi)
    pq_prod = N.modus_ponens(conjonction_intro(p_fi, q_gi),
                             equivalence_arriere(_cpp_ssi(vp, vq, fi, gi)))  # (p,q)∈X_i×Y_i
    Hi_eq = N.modus_ponens(hi, instancie(hHp, vi))                # H_i = X_i×Y_i
    prod_eq_Hi = N.modus_ponens(Hi_eq, symetrie(Hi, E.produit(fi, gi)))          # X_i×Y_i = H_i
    pq_Hi = N.modus_ponens(pq_prod, equivalence_avant(N.modus_ponens(prod_eq_Hi,
                N.s6(E.produit(fi, gi), Hi, "w", appartient(E.couple(vp, vq), var("w"))))))  # (p,q)∈H_i
    z_Hi = N.modus_ponens(pq_Hi, equivalence_arriere(N.modus_ponens(z_eq,
                N.s6(vz, E.couple(vp, vq), "w", appartient(var("w"), Hi)))))     # z∈H_i
    all_i = N.generalisation("i", N.loi_deduction(appartient(vi, vI), z_Hi))     # ∀i(i∈I⇒z∈H_i)
    z_interH = inter_intro(vh, vI, T0, T0_dans_I, all_i, vz)                     # z∈⋂H

    imp_body = N.loi_deduction(body, z_interH)                    # {hyp} body ⇒ z∈⋂H
    imp_ex = existe_elimination(existe_elimination(imp_body, "q"), "p")
    z_final = N.modus_ponens(ex_pq, imp_ex)
    return N.loi_deduction(appartient(vz, E.produit(interf, interg)), z_final)


# @livre Ch.R §4 Prop.- | E.R.20 item 8 (44) | PDF p.323  (sens ⇐ : ⋂(X×Y) ⊂ (⋂X)×(⋂Y))
def _dir_interH_vers_produit(f="f", g="g", h="H", i="I", z="z"):
    """⊢ {hyp_produit_famille, ¬(I=∅)}  z∈⋂H ⇒ z∈(⋂X)×(⋂Y).

    ¬(I=∅) est l'hypothèse même de Bourbaki en E.R.20 (44) ; ce lemme la portait
    DÉJÀ avant la migration Déf. 2 (il en tire l'indice i₀ qui décompose z en
    couple).  Rien n'a donc été ajouté ici : le passage z∈⋂H ⇝ (∀i)(…) est de
    pure ÉLIMINATION (`inter_elim`, CLOS, inconditionnel), et seuls les deux
    retours vers ⋂X / ⋂Y — des INTRODUCTIONS — passent par `_carac_inter`, à
    coût nul puisque ¬(I=∅) est déjà au compteur."""
    vf, vg, vh, vI, vz = var(f), var(g), var(h), var(i), var(z)
    interf, interg = _interf(f, i), _interf(g, i)
    hHp = N.assume(hyp_produit_famille(f, g, h, i))
    h_ne = N.assume(non(egal(vI, E.VIDE)))
    ex_z = N.modus_ponens(h_ne, equivalence_avant(non_vide_ssi_element(i)))       # (∃z)(z∈I)
    ex_i0 = N.modus_ponens(ex_z, equivalence_avant(                              # (∃i0)(i0∈I)
        alpha_existe("z", "i0", appartient(var("z"), vI))))

    hz = N.assume(appartient(vz, E.inter_famille(vh, vI)))
    z_all_H = N.modus_ponens(hz, inter_elim(vh, vI, vz))          # ∀i(i∈I⇒z∈H_i)

    vi0, vi, vp, vq = var("i0"), var("i"), var("p"), var("q")
    hi0 = N.assume(appartient(vi0, vI))
    fi0, gi0 = E.valeur_famille(vf, vi0), E.valeur_famille(vg, vi0)
    Hi0 = E.valeur_famille(vh, vi0)
    z_Hi0 = N.modus_ponens(hi0, instancie(z_all_H, vi0))                          # z∈H_{i0}
    Hi0_eq = N.modus_ponens(hi0, instancie(hHp, vi0))                             # H_{i0}=X_{i0}×Y_{i0}
    z_prod0 = N.modus_ponens(z_Hi0, equivalence_avant(N.modus_ponens(Hi0_eq,
                N.s6(Hi0, E.produit(fi0, gi0), "w", appartient(vz, var("w"))))))  # z∈X_{i0}×Y_{i0}
    ex_pq = N.modus_ponens(z_prod0, equivalence_avant(_instance_produit(fi0, gi0, vz)))  # (∃p∃q)(z=(p,q)∧p∈X_{i0}∧q∈Y_{i0})

    body0 = et(et(egal(vz, E.couple(vp, vq)), appartient(vp, fi0)), appartient(vq, gi0))
    hb0 = N.assume(body0)
    z_eq = conjonction_elim_gauche(conjonction_elim_gauche(hb0))                  # z=(p,q)

    # ∀i(i∈I ⇒ p∈X_i) et ∀i(i∈I ⇒ q∈Y_i)
    hi = N.assume(appartient(vi, vI))
    fi, gi = E.valeur_famille(vf, vi), E.valeur_famille(vg, vi)
    z_Hi = N.modus_ponens(hi, instancie(z_all_H, vi))                            # z∈H_i
    Hi_eq = N.modus_ponens(hi, instancie(hHp, vi))                              # H_i=X_i×Y_i
    z_prod_i = N.modus_ponens(z_Hi, equivalence_avant(N.modus_ponens(Hi_eq,
                N.s6(E.valeur_famille(vh, vi), E.produit(fi, gi), "w", appartient(vz, var("w"))))))  # z∈X_i×Y_i
    pq_prod_i = N.modus_ponens(z_prod_i, equivalence_avant(N.modus_ponens(z_eq,
                N.s6(vz, E.couple(vp, vq), "w", appartient(var("w"), E.produit(fi, gi))))))  # (p,q)∈X_i×Y_i
    pq_split = N.modus_ponens(pq_prod_i, equivalence_avant(_cpp_ssi(vp, vq, fi, gi)))  # p∈X_i ∧ q∈Y_i
    p_all = N.generalisation("i", N.loi_deduction(appartient(vi, vI), conjonction_elim_gauche(pq_split)))
    q_all = N.generalisation("i", N.loi_deduction(appartient(vi, vI), conjonction_elim_droite(pq_split)))
    p_interX = N.modus_ponens(p_all, equivalence_arriere(_carac_inter(f, i, vp)))  # p∈⋂X
    q_interY = N.modus_ponens(q_all, equivalence_arriere(_carac_inter(g, i, vq)))  # q∈⋂Y
    pq_in = N.modus_ponens(conjonction_intro(p_interX, q_interY),
                           equivalence_arriere(_cpp_ssi(vp, vq, interf, interg)))  # (p,q)∈(⋂X)×(⋂Y)
    z_in = N.modus_ponens(pq_in, equivalence_arriere(N.modus_ponens(z_eq,
                N.s6(vz, E.couple(vp, vq), "w", appartient(var("w"), E.produit(interf, interg))))))  # z∈(⋂X)×(⋂Y)

    imp_body0 = N.loi_deduction(body0, z_in)
    z_from_i0 = N.modus_ponens(ex_pq, existe_elimination(existe_elimination(imp_body0, "q"), "p"))
    z_final = N.modus_ponens(ex_i0, existe_elimination(N.loi_deduction(appartient(vi0, vI), z_from_i0), "i0"))
    return N.loi_deduction(appartient(vz, E.inter_famille(vh, vI)), z_final)


def enonce_produit_inter_familles(f="f", g="g", h="H", i="I"):
    vf, vg, vh, vI = var(f), var(g), var(h), var(i)
    ante = et(non(egal(vI, E.VIDE)), hyp_produit_famille(f, g, h, i))
    return impl(ante, egal(E.produit(_interf(f, i), _interf(g, i)), E.inter_famille(vh, vI)))


# @livre Ch.R §4 Prop.- | E.R.20 item 8 (44) | PDF p.323  ((⋂X_ι)×(⋂Y_ι)=⋂(X_ι×Y_ι), mêmes indices)
# @livre Ch.R §4 Demo.- | E.R.20 item 8 (44) | PDF p.323  (démo : extensionnalité, témoins existentiels du produit)
def produit_inter_familles(f="f", g="g", h="H", i="I"):
    """🎯 ⊢ (¬(I=∅) et (∀i)(i∈I ⇒ H_i=X_i×Y_i)) ⇒ (⋂X_ι)×(⋂Y_ι) = ⋂H_ι.   (E.R.20 (44), n°92.)"""
    vf, vg, vh, vI = var(f), var(g), var(h), var(i)
    prod = E.produit(_interf(f, i), _interf(g, i))
    interH = E.inter_famille(vh, vI)
    incl1 = N.generalisation("z", _dir_produit_vers_interH(f, g, h, i))   # {hyp} prod⊂⋂H
    incl2 = N.generalisation("z", _dir_interH_vers_produit(f, g, h, i))   # {hyp,¬I=∅} ⋂H⊂prod
    eq = N.modus_ponens(conjonction_intro(incl1, incl2),
                        extensionnalite_appliquee(prod, interH))          # prod=⋂H
    ante = et(non(egal(vI, E.VIDE)), hyp_produit_famille(f, g, h, i))
    hante = N.assume(ante)
    eq_c = _cut(_cut(eq, conjonction_elim_gauche(hante)),
                conjonction_elim_droite(hante))                          # {ante} prod=⋂H
    res = N.loi_deduction(ante, eq_c)
    assert res.conclusion == enonce_produit_inter_familles(f, g, h, i), \
        "produit_inter_familles : conclusion ≠ énoncé attendu"
    return res


__all__ = ["hyp_produit_famille", "_dir_produit_vers_interH", "_dir_interH_vers_produit",
           "enonce_produit_inter_familles", "produit_inter_familles"]
