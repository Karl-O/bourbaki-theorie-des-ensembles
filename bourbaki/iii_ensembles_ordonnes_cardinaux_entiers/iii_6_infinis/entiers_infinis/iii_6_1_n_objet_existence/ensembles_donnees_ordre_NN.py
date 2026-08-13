"""§III.6.1 — LES DONNÉES D'ORDRE DE ℕ, ∀-CLOSES SOUS Fini n   (brique N1).

Les quatre hypothèses H1..H4 de `factorielle_rs` (données de position, ∀-closes),
DÉRIVÉES sur les TERMES CLOS ℕ = ensemble_NN() et G≤ = G_ordre_NN() :

  • H1  ⊢ (∀n)( Fini n ⇒ successeur(n) ∈ ℕ )                       [CLOS]
        appartenance_NN (sens ⇐) + NN_clos_successeur.
  • H2  ⊢ (∀n)( Fini n ⇒ seg(ℕ, succ n) = [0,n] )                  [CLOS]
        le PONT `segment_succ_est_intervalle` {n∈ℕ}, déchargé par Fini n ⇒ n∈ℕ.
  • H3  ⊢ (∀n)( Fini n ⇒ ZERO ∈ seg(ℕ, succ n) )                   [CLOS]
        0∈[0,n] (axiome intervalle ⇐ : card 0 [fini_zero], 0≤0 [réflexivité],
        0≤n [zero_minore sous card n]) puis transport ARRIÈRE le long du pont.
  • H4  ⊢ (∀n)( Fini n ⇒ n ∈ seg(ℕ, succ n) )                      [CLOS]
        n∈[0,n] (RÉEMPLOI : conjonction gauche de `plus_grand_element_intervalle`,
        {card n} déchargée par Fini = et(card, ·)) puis même transport.

Chaque conclusion est assertée == à `donnees_ordre_closes(ensemble_NN(),
G_ordre_NN(), nb)` — le miroir EXACT de ce que `factorielle_rs` consomme (piège
variables vs termes clos, payé le 26 juil.).  Consommateur : l'instanciation ℕ du
capstone factoriel (brique N2) — bo se décharge par `bo_graphe_NN` [CLOS], ces
quatre-ci par le présent module ⇒ restent les données de la RÈGLE seules.

  • `seg_zero_vide`  ⊢ seg(ℕ, ZERO) = ∅  (« rien avant 0 »)           [CLOS]
        z∈seg(ℕ,0) ⇒ z≤0 (axiome S8 de G≤) ∧ z≠0 ; or 0≤z (z cardinal via
        z∈ℕ ⇔ Fini z) ⇒ antisymétrie ⇒ z=0 : ABSURDE, ex falso z∈∅ ; seg⊂∅ ⇒ =∅.
        (Indérivable à la VARIABLE (E,G) — mesuré au tick 1 ; le TERME la donne.)
INVARIANT : theorie_ensembles() = 22.  Noyau et subst INTOUCHÉS.  Rien postulé.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, appartient,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E

from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, instancie,
)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import symetrie
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (
    ZERO, successeur, est_fini, est_cardinal,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_fini_zero import fini_zero
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux_theoremes import inf_egal_reflexif
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_1_n_objet_existence.ensembles_ensemble_NN import (
    ensemble_NN, appartenance_NN, NN_clos_successeur,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_1_n_objet_existence.ensembles_ordre_NN_graphe import (
    G_ordre_NN, couple_dans_G_ordre,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.trichotomie_ordinaux.lemme4_segments.ensembles_segments_construction import membre_segment
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.ordre_cardinaux.ensembles_cardinaux_props_restantes_ordre import inf_egal_antisymetrique_card
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.recollement.ensembles_restriction_somme import _ex_falso
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_vide import sous_ensemble_vide_ssi_egal
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_intervalles_comptage.ensembles_pont_segment_iii5 import (
    segment_succ_NN, segment_succ_est_intervalle, _membre_intervalle, _zero_minore,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_intervalles_comptage.ensembles_max_intervalle_iii5 import (
    plus_grand_element_intervalle, intervalle_zero,
)

#: Liant canonique des H_i — celui de `factorielle_rs` (et de la relation (Rs)).
NB_DEFAUT = "nfac"


def _t(t):
    """Coercion str/Terme → Terme."""
    return t if isinstance(t, Terme) else var(t)


def _dech(thm, hyp, preuve_hyp):
    """De Γ∪{H}⊢C et Δ⊢H, déduit Γ∪Δ⊢C (loi_deduction puis modus_ponens)."""
    return N.modus_ponens(preuve_hyp, N.loi_deduction(hyp, thm))


def _cible(i, nb=NB_DEFAUT):
    """H_{i+1} attendue — le MIROIR : la formule que `factorielle_rs` consomme."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_8_factorielle.ensembles_factorielle_succ_vraie import donnees_ordre_closes
    return donnees_ordre_closes(ensemble_NN(), G_ordre_NN(), nb=nb)[i]


def _fini_dans_NN(t):
    """⊢ Fini T ⇒ T ∈ ℕ   pour un TERME T  (appartenance_NN, sens ⇐)."""
    return equivalence_arriere(instancie(appartenance_NN(), _t(t)))


def _fini_et_clos(nb, corps_sous_fini):
    """∀-clôture standard : de {Fini n, …clos…} ⊢ C(n), rend ⊢ (∀n)(Fini n ⇒ C(n))."""
    return N.generalisation(nb, N.loi_deduction(est_fini(var(nb)), corps_sous_fini))


# ══════════════════════════════════════════════════════════════════════════════
#  H1 :  (∀n)( Fini n ⇒ succ n ∈ ℕ )                                      [CLOS]
# ══════════════════════════════════════════════════════════════════════════════
# @livre Ch.III §4.1 Def.1 | E III.30 L.39-41 | PDF p.133  (un entier est un cardinal fini ; ℕ les collectivise et est clos par successeur — assemblage des théorèmes clos de §III.6.1)
def h1_succ_dans_NN(nb=NB_DEFAUT):
    """⊢ (∀n)( Fini n ⇒ successeur(n) ∈ ℕ ).                              [CLOS]"""
    vb = var(nb)
    h = N.assume(est_fini(vb))
    n_NN = N.modus_ponens(h, _fini_dans_NN(vb))                  # n∈ℕ
    s_NN = N.modus_ponens(n_NN, instancie(NN_clos_successeur(), vb))   # succ n∈ℕ
    res = _fini_et_clos(nb, s_NN)
    assert res.conclusion == _cible(0, nb), "h1 : ≠ miroir donnees_ordre_closes[0]"
    assert res.est_clos, "h1 : non clos"
    return res


# ══════════════════════════════════════════════════════════════════════════════
#  H2 :  (∀n)( Fini n ⇒ seg(ℕ, succ n) = [0,n] )   — le pont, ∀-clos      [CLOS]
# ══════════════════════════════════════════════════════════════════════════════
# @livre Ch.III §6.2 Rem.- | E III.46 L.12-13 | PDF p.149  (le raccord semi-ouvert/fermé, ∀-clos sous Fini n — le pont de §III.5 rendu consommable par (Rs))
def h2_seg_succ_intervalle(nb=NB_DEFAUT):
    """⊢ (∀n)( Fini n ⇒ seg(ℕ, succ n) = [0,n] ).                         [CLOS]"""
    vb = var(nb)
    h = N.assume(est_fini(vb))
    n_NN = N.modus_ponens(h, _fini_dans_NN(vb))                  # n∈ℕ
    pont = segment_succ_est_intervalle(vb)                       # {n∈ℕ} ⊢ seg=[0,n]
    pont = _dech(pont, appartient(vb, ensemble_NN()), n_NN)      # {Fini n} ⊢ seg=[0,n]
    res = _fini_et_clos(nb, pont)
    assert res.conclusion == _cible(1, nb), "h2 : ≠ miroir donnees_ordre_closes[1]"
    assert res.est_clos, "h2 : non clos"
    return res


# ══════════════════════════════════════════════════════════════════════════════
#  Transport ARRIÈRE :  z∈[0,n] → z∈seg(ℕ, succ n)  le long du pont.
# ══════════════════════════════════════════════════════════════════════════════
def _transport_dans_seg(vb, z, thm_z_in_I, thm_pont):
    """De Γ ⊢ z∈[0,n] et Δ ⊢ seg=[0,n] : Γ∪Δ ⊢ z∈seg   (s6 sur [0,n]=seg)."""
    seg, I0n = segment_succ_NN(vb), intervalle_zero(vb)
    inv = N.modus_ponens(thm_pont, symetrie(seg, I0n))           # [0,n] = seg
    eqv = N.modus_ponens(inv, N.s6(I0n, seg, "wtsg", appartient(_t(z), var("wtsg"))))
    return N.modus_ponens(thm_z_in_I, equivalence_avant(eqv))    # z∈seg


# ══════════════════════════════════════════════════════════════════════════════
#  H3 :  (∀n)( Fini n ⇒ ZERO ∈ seg(ℕ, succ n) )                           [CLOS]
# ══════════════════════════════════════════════════════════════════════════════
# @livre Ch.III §5.3 Rem.- | E III.37 L.22-26 | PDF p.140  (0 appartient à [0,n], donc au segment d'extrémité succ n via le pont)
def h3_zero_dans_seg(nb=NB_DEFAUT):
    """⊢ (∀n)( Fini n ⇒ ZERO ∈ seg(ℕ, succ n) ).                          [CLOS]"""
    vb = var(nb)
    h = N.assume(est_fini(vb))
    card_n = conjonction_elim_gauche(h)                          # card n  (Fini=et(card,·))
    card_0 = conjonction_elim_gauche(fini_zero())                # card 0        [CLOS]
    z00 = instancie(N.generalisation("X", inf_egal_reflexif("X")), ZERO)   # 0≤0
    z0n = N.modus_ponens(card_n, _zero_minore(vb))               # 0≤n
    corps = conjonction_intro(conjonction_intro(card_0, z00), z0n)
    z_in_I = N.modus_ponens(corps, equivalence_arriere(_membre_intervalle(vb, ZERO)))
    n_NN = N.modus_ponens(h, _fini_dans_NN(vb))
    pont = _dech(segment_succ_est_intervalle(vb),
                 appartient(vb, ensemble_NN()), n_NN)            # {Fini n} ⊢ seg=[0,n]
    res = _fini_et_clos(nb, _transport_dans_seg(vb, ZERO, z_in_I, pont))
    assert res.conclusion == _cible(2, nb), "h3 : ≠ miroir donnees_ordre_closes[2]"
    assert res.est_clos, "h3 : non clos"
    return res


# ══════════════════════════════════════════════════════════════════════════════
#  H4 :  (∀n)( Fini n ⇒ n ∈ seg(ℕ, succ n) )                              [CLOS]
# ══════════════════════════════════════════════════════════════════════════════
# @livre Ch.III §5.3 Rem.- | E III.37 L.22-26 | PDF p.140  (n appartient à [0,n] — réemploi du « plus grand élément » — donc au segment via le pont)
def h4_n_dans_seg(nb=NB_DEFAUT):
    """⊢ (∀n)( Fini n ⇒ n ∈ seg(ℕ, succ n) ).                             [CLOS]"""
    vb = var(nb)
    h = N.assume(est_fini(vb))
    card_n = conjonction_elim_gauche(h)                          # card n
    pge = plus_grand_element_intervalle(vb)                      # {card n} ⊢ pge(≤,[0,n],n)
    n_in_I = _dech(conjonction_elim_gauche(pge),
                   est_cardinal(vb), card_n)                     # {Fini n} ⊢ n∈[0,n]
    n_NN = N.modus_ponens(h, _fini_dans_NN(vb))
    pont = _dech(segment_succ_est_intervalle(vb),
                 appartient(vb, ensemble_NN()), n_NN)            # {Fini n} ⊢ seg=[0,n]
    res = _fini_et_clos(nb, _transport_dans_seg(vb, vb, n_in_I, pont))
    assert res.conclusion == _cible(3, nb), "h4 : ≠ miroir donnees_ordre_closes[3]"
    assert res.est_clos, "h4 : non clos"
    return res


def donnees_ordre_NN(nb=NB_DEFAUT):
    """Les quatre H_i DÉRIVÉES, dans l'ordre de `donnees_ordre_closes`.       [CLOSES]"""
    return [h1_succ_dans_NN(nb), h2_seg_succ_intervalle(nb),
            h3_zero_dans_seg(nb), h4_n_dans_seg(nb)]


# ══════════════════════════════════════════════════════════════════════════════
#  🎯 seg(ℕ, ZERO) = ∅   — « rien avant 0 » (l'ex-résidu nommé de N2)      [CLOS]
# ══════════════════════════════════════════════════════════════════════════════
# @livre Ch.III §5.8 Rem.- | E III.41 L.30-32 | PDF p.144  (la donnée de position du cas 0 — f(0)=T(f|∅) — dérivée sur le VRAI ℕ : aucun entier ne précède strictement 0)
def seg_zero_vide(z="zsg0"):
    """🎯 ⊢ seg(ℕ, ZERO) = ∅.                                             [CLOS]

    « Rien avant 0. »  z∈seg(ℕ,0) décompose en ((z∈ℕ ∧ (z,0)∈G_≤) ∧ z≠0)
    [`membre_segment`, inconditionnel] ; (z,0)∈G_≤ ⇔ ordre_induit_NN(z,0)
    [`couple_dans_G_ordre`, CLOS] donne z≤0 ; z∈ℕ ⇒ Fini z ⇒ card z, d'où 0≤z
    [`_zero_minore`] ; l'antisymétrie de ≤ sur les cardinaux force z=0 —
    contradiction avec z≠0, ex falso z∈∅ ; donc seg⊂∅, et X⊂∅ ⇔ X=∅ conclut.
    INDÉRIVABLE à la variable (E,G) — mesuré au tick 1 de la campagne : c'est
    une récompense propre au TERME clos."""
    NN, G = ensemble_NN(), G_ordre_NN()
    vz = var(z)
    seg0 = E.segment_extremite(G, NN, ZERO)

    h_z = N.assume(appartient(vz, seg0))
    corps = N.modus_ponens(h_z, equivalence_avant(membre_segment(G, NN, ZERO, vz)))
    z_NN = conjonction_elim_gauche(conjonction_elim_gauche(corps))    # z∈ℕ
    z_G0 = conjonction_elim_droite(conjonction_elim_gauche(corps))    # (z,0)∈G_≤
    z_ne0 = conjonction_elim_droite(corps)                            # z≠0

    ord0 = N.modus_ponens(z_G0, equivalence_avant(couple_dans_G_ordre(vz, ZERO)))
    z_le0 = conjonction_elim_gauche(conjonction_elim_gauche(ord0))    # z≤0
    fini_z = N.modus_ponens(z_NN, equivalence_avant(instancie(appartenance_NN(), vz)))
    card_z = conjonction_elim_gauche(fini_z)                          # card z
    zero_le = N.modus_ponens(card_z, _zero_minore(vz))                # 0≤z
    card_0 = conjonction_elim_gauche(fini_zero())                     # card 0

    anti = instancie(instancie(inf_egal_antisymetrique_card(), vz), ZERO)
    premisse = conjonction_intro(conjonction_intro(
        conjonction_intro(z_le0, zero_le), card_z), card_0)
    z_eq0 = N.modus_ponens(premisse, anti)                            # z=0  — ABSURDE
    z_vide = _ex_falso(z_eq0, z_ne0, appartient(vz, E.VIDE))          # z∈∅ (ex falso)

    sub = N.generalisation(z, N.loi_deduction(appartient(vz, seg0), z_vide))
    # Re-liant CANONIQUE « z » (motif segment_succ_est_intervalle) : l'exotique zsg0
    # a protégé la chaîne (inf_egal_card lie « z » EN INTERNE — l'employer direct
    # aurait fait renommer les liants à l'antisymétrie), mais `inclus` attend « z ».
    # Licite : sub est CLOS, et les occurrences de zsg0 sont hors de tout lieur.
    sub = N.generalisation("z", instancie(sub, var("z")))
    car = instancie(N.generalisation("X", sous_ensemble_vide_ssi_egal("X")), seg0)
    res = N.modus_ponens(sub, equivalence_avant(car))                 # seg(ℕ,0)=∅

    assert res.conclusion == egal(seg0, E.VIDE), "seg_zero_vide : ≠ seg(ℕ,0)=∅"
    assert res.est_clos, "seg_zero_vide : non clos"
    return res


__all__ = ["NB_DEFAUT", "h1_succ_dans_NN", "h2_seg_succ_intervalle",
           "h3_zero_dans_seg", "h4_n_dans_seg", "donnees_ordre_NN", "seg_zero_vide"]
