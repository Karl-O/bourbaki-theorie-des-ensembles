"""§III.3.3 Prop.5 b) / §III.5.8 — T1b-(3) : LA RÉCURSION DU PRODUIT FINI INDEXÉ.

  🎯 produit_fini_recursion(u, n) :
        { n∈ℕ, H2, H3 }  ⊢  Card( ∏_{seg(ℕ, n+1)} u )  =  Card( (∏_{seg(ℕ,n)} u) × u_n )

où seg(ℕ,t) := segment_extremite(≤_G, ℕ, t) = [0,t[ (le segment OUVERT partagé
avec la chaîne C62/factorielle, _seg_NN), et où le membre droit EST, terme à
terme, produit_cardinal_binaire(∏_{seg(ℕ,n)} u, u_n)  (asserté, comme en T1b-2).
Le membre gauche EST, terme à terme, produit_cardinal(u, seg(ℕ,n+1)) — le ∏ de
la Déf. 3 §III.3.3, celui-là même de factorielle_def2 (asserté aussi).

C'est le PAS DE RÉCURRENCE du produit fini : le cas « partition en deux blocs
(seg(n), {n}) » de l'associativité du produit cardinal (Prop. 5 b), E III.26),
l'infra du « (n+1)! = n!·(n+1) … par récurrence sur n » du livre (E III.41).

────────────────────────────────────────────────────────────────────────────────
ROUTE (pur ASSEMBLAGE par congruence des deux briques closes du dossier) :
  (1) T1b-1  segment_succ_decomposition(n)     {n∈ℕ} ⊢ seg(n+1) = seg(n)∪{n} ;
  (2) congruence-TROU sur X ↦ Card(∏_X u)  (motif _congruence_T / _rewrite :
      congruence_terme sur le trou EXOTIQUE « wpr », ∀-clos puis instancié)
        →  {n∈ℕ} ⊢ Card(∏_{seg(n+1)} u) = Card(∏_{seg(n)∪{n}} u) ;
  (3) T1b-2  produit_cardinal_adjonction INSTANCIÉE AUX TERMES I:=seg(ℕ,n), j:=n
      (les trois fichiers d'adjonction sont term-safe : tous les paramètres
      passent par _t — pas besoin d'_inst_gen)
        →  {H1,H2,H3} ⊢ Card(∏_{seg(n)∪{n}} u) = Card((∏_{seg(n)} u) × u_n) ;
  (4) chaîne composer_egalites (maillon central LITTÉRALEMENT identique :
      seg(n)∪{n} == indices_adjoints(seg(n), n), asserté) ;
  (5) DÉCHARGE de H1 = ¬(n ∈ seg(ℕ,n)) par point_hors_segment [CLOS, c60]
      instancié à G:=G_ordre_NN(), E:=ℕ, x:=n (conclusion == H1, asserté).

HYPOTHÈSES HONNÊTES restantes (exactement 3) :
  •  n ∈ ℕ                                       (héritée de T1b-1) ;
  •  H2 := (∀G)(G ∈ ∏_{seg(n)∪{n}} u ⇒ est_un_graphe(G))     (héritée de T1b-2) ;
  •  H3 := (∀G)(G ∈ ∏_{seg(n)} u   ⇒ est_un_graphe(G))       (héritée de T1b-2).
H2/H3 restent : AXIOME_PRODUIT_FAM n'expose pas « élément = couple » (le pont
membre-du-produit ⇒ graphe n'existe pas dans l'axiome encodé, cf. T1b-2).
H1 est DÉCHARGÉE : « n ∉ [0,n[ » est un théorème (point_hors_segment).

GARDE-FOUS.  Rien postulé ; noyau/subst intouchés ; theorie_ensembles()==22
(asserté au test) ; trou de congruence « wpr » EXOTIQUE ; les noms libres de u
et n sont vérifiés contre les liants internes de TOUTE la machinerie appelée
(_NOMS_RESERVES) ; asserts denses (cible exacte, maillon central, forme
produit_cardinal_binaire, hypothèses exactes, H1 absente, non-VACUOUS).

⚠️ PERF : T1b-1 déclenche N_existe (~5 min, mémoïsé une fois par session) — slow.
SUITE (T1c) : instancier u := famille_successeurs(n) pour la récursion de
factorielle_def2 et converger avec factorielle_zero / factorielle_succ_fallback.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, appartient, libres_t,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import instancie
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
    composer_egalites, congruence_terme,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_c60_existence_close import (
    point_hors_segment,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    cardinal, produit_cardinal,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_produit.ensembles_arith_cardinale import (
    produit_cardinal_binaire,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (
    successeur,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_1_n_objet_existence.ensembles_ensemble_NN import (
    ensemble_NN,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_1_n_objet_existence.ensembles_ordre_NN_graphe import (
    G_ordre_NN,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_6_familles.ensembles_famille_successeurs import _seg_NN
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_6_familles.ensembles_seg_successeur import (
    segment_succ_decomposition,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_6_familles.ensembles_produit_adjonction import (
    _dech, indices_adjoints, hypothese_indice_neuf,
    hypothese_graphes_total, hypothese_graphes_partiel,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_6_familles.ensembles_produit_adjonction_bij import (
    produit_cardinal_adjonction,
)

#: Trou EXOTIQUE de la congruence X ↦ Card(∏_X u)  (≠ « wct »/« wdu »/« wsi »).
_TROU = "wpr"

#: Liants internes de TOUTE la machinerie traversée (T1b-1 : isg/wsg*/xso/bso/z ;
#: adjonction P1-P7 : Fa/Fb/i/w/u/up/s/t/x/y/z/G/Fq/c/yb/zz/a/b/p/q ; cardinal :
#: Z ; _prop1_direct_t : X/Y ; famille : ifs/pess) — AUCUN nom libre de u ou n
#: ne doit les heurter (collision de nom d'argument = le piège post-fix subst).
_NOMS_RESERVES = frozenset({
    "isg", "wsg1", "wsg2", "wsg3", "xso", "bso",
    "Fa", "Fb", "i", "w", "u", "up", "s", "t", "x", "y", "z", "G",
    "Fq", "c", "yb", "zz", "a", "b", "p", "q",
    "X", "Y", "Z", "pess", _TROU, "wct",
})
# NB (25 juil, T1c) : « ifs » RETIRÉ des réservés — c'est le liant du graphe_terme de
# famille_successeurs, syntaxiquement LIBRE dans le terme-famille passé comme u ; or la
# machinerie traversée ICI (T1b-1 seg-successeur + T1b-2 adjonction + _prop1_direct_t)
# ne lie jamais « ifs » (il n'appartient qu'aux briques famille NON traversées :
# famille_successeurs_valeur). Le réserver interdisait exactement l'usage cible de la
# récursion (u := famille_successeurs). Vérifié : test T1b-3 re-vert après retrait.


def _t(t):
    """Coercion str/Terme → Terme."""
    return t if isinstance(t, Terme) else var(t)


def produit_fini_recursion_enonce(u="upr", n="npr"):
    """Formule cible :  Card(∏_{seg(ℕ,n+1)} u) = Card((∏_{seg(ℕ,n)} u) × u_n).

    Le membre droit est CONSTRUIT comme produit_cardinal_binaire(∏_{seg n} u, u_n)
    — la forme cardinale terme-à-terme, exactement comme en T1b-2."""
    vu, vn = _t(u), _t(n)
    return egal(cardinal(E.produit_famille(vu, _seg_NN(successeur(vn)))),
                produit_cardinal_binaire(E.produit_famille(vu, _seg_NN(vn)),
                                         E.valeur_famille(vu, vn)))


def hypotheses_graphes_recursion(u="upr", n="npr"):
    """(H2, H3) de T1b-2 instanciées à I := seg(ℕ,n), j := n  (les 2 restantes)."""
    vu, vn = _t(u), _t(n)
    I = _seg_NN(vn)
    return (hypothese_graphes_total(vu, I, vn), hypothese_graphes_partiel(vu, I, vn))


# @livre Ch.III §3.3 Prop.5 | E III.26 L.16-19 | PDF p.129  (b) « associativité … du produit » ∏_{ι∈I} = ∏_{λ∈L}(∏_{J_λ}) — LE CAS partition en deux blocs (seg(n), {n}) de seg(n+1), au niveau cardinal)
# @livre Ch.II §5.5 Rem.1 | E II.35 L.15-22 | PDF p.86  (la bijection ensembliste sous-jacente ∏_{I∪{j}} ≅ ∏_I × u_j — T1b-2)
# @livre Ch.III §5.8 Def.2 | E III.41 L.30-32 | PDF p.144  (« (n+1)! = n!(n+1). Cette dernière relation, jointe à 0!=1, caractérise le terme n!, … par récurrence sur n » — le pas de récurrence dont ce théorème est l'infra, u := (i+1)_{i<n} en T1c)
def produit_fini_recursion(u="upr", n="npr"):
    """🎯 { n∈ℕ, H2, H3 } ⊢ Card(∏_{seg(n+1)} u) = Card((∏_{seg(n)} u) × u_n).

    Conclusion ÉGALE LITTÉRALEMENT produit_fini_recursion_enonce(u, n).
    Assemblage : T1b-1 → congruence-trou Card∘∏ → T1b-2 (I:=seg(n), j:=n) →
    composer_egalites → décharge de H1 par point_hors_segment [CLOS].
    NON vacueux : la conclusion n'est aucune des hypothèses ; H1 est PROUVÉE."""
    vu, vn = _t(u), _t(n)
    assert not (_NOMS_RESERVES & (libres_t(vu) | libres_t(vn))), \
        "produit_fini_recursion : nom libre de u ou n heurtant un liant réservé"

    I = _seg_NN(vn)                              # [0,n[   (I de l'adjonction)
    A = _seg_NN(successeur(vn))                  # [0,n+1[ (l'index total)
    B = E.reunion(I, E.singleton(vn))            # seg(n)∪{n}
    assert B == indices_adjoints(I, vn), \
        "produit_fini_recursion : seg(n)∪{n} ≠ I∪{j} de l'adjonction (maillon central)"

    # (1) T1b-1 :  {n∈ℕ} ⊢ A = B
    seg_eq = segment_succ_decomposition(vn)

    # (2) congruence-TROU sur X ↦ Card(∏_X u)  :  {n∈ℕ} ⊢ Card(∏_A u) = Card(∏_B u)
    #     (motif _congruence_T/_rewrite : (wpr=B)⇒(T(wpr)=T(B)) ∀-clos, instancié à A ;
    #      substitution PURE — le τ-liant « Z » de Card n'est libre ni dans A ni dans B.)
    gabarit = cardinal(E.produit_famille(vu, var(_TROU)))
    imp = congruence_terme(var(_TROU), B, gabarit, _TROU)
    card_seg = N.modus_ponens(seg_eq, instancie(N.generalisation(_TROU, imp), A))

    # (3) T1b-2 AUX TERMES I:=seg(ℕ,n), j:=n  :  {H1,H2,H3} ⊢ Card(∏_B u) = Card(∏_I × u_n)
    card_adj = produit_cardinal_adjonction(vu, I, vn)

    # (4) chaîne :  {n∈ℕ, H1, H2, H3} ⊢ Card(∏_A u) = Card((∏_I u) × u_n)
    chaine = composer_egalites(card_seg, card_adj)

    # (5) DÉCHARGE de H1 = ¬(n ∈ seg(ℕ,n))  par point_hors_segment  [CLOS, c60]
    h1 = point_hors_segment(G_ordre_NN(), ensemble_NN(), vn)
    assert h1.conclusion == hypothese_indice_neuf(I, vn), \
        "produit_fini_recursion : point_hors_segment ≠ H1 (α-divergence inattendue)"
    res = _dech(chaine, h1)

    # ── asserts denses ────────────────────────────────────────────────────────
    assert res.conclusion == produit_fini_recursion_enonce(u, n), \
        "produit_fini_recursion : conclusion ≠ énoncé cible"
    assert res.conclusion.termes[1] == produit_cardinal_binaire(
        E.produit_famille(vu, I), E.valeur_famille(vu, vn)), \
        "produit_fini_recursion : RHS ≠ produit_cardinal_binaire(∏_{seg n} u, u_n)"
    assert res.conclusion.termes[0] == produit_cardinal(vu, A), \
        "produit_fini_recursion : LHS ≠ produit_cardinal(u, seg(n+1)) (Déf.3 §3.3)"
    h2, h3 = hypotheses_graphes_recursion(u, n)
    assert res.hypotheses == frozenset({appartient(vn, ensemble_NN()), h2, h3}), \
        "produit_fini_recursion : hypothèses ≠ { n∈ℕ, H2, H3 }"
    assert len(res.hypotheses) == 3, "produit_fini_recursion : nb hypothèses ≠ 3"
    assert hypothese_indice_neuf(I, vn) not in res.hypotheses, \
        "produit_fini_recursion : H1 non déchargée"
    assert res.conclusion not in res.hypotheses, "produit_fini_recursion : VACUOUS"
    return res


__all__ = ["produit_fini_recursion_enonce", "hypotheses_graphes_recursion",
           "produit_fini_recursion"]
