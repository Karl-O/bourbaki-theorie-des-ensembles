"""§III.5.8 Déf.2 — T1c : LA RÉCURSION DE LA FACTORIELLE-DÉF.2  (n+1)! = n!·(n+1).

  🎯 factorielle_def2_recursion(n) :
        { n∈ℕ, H2, H3, HW, HN }  ⊢
        factorielle_def2(succ n) = produit_cardinal_binaire(factorielle_def2(n), succ n)

Le livre (E III.41 L.30-32) : « (n+1)! = n!(n+1).  Cette dernière relation, jointe
à 0! = 1, caractérise le terme n!, … par récurrence sur n. »  Ici le PAS de cette
récurrence, sur le VRAI terme de la Déf. 2 (T1a : n! = ∏_{i<n}(i+1), produit de la
famille graphe_terme sur le segment OUVERT partagé avec la chaîne C62).

────────────────────────────────────────────────────────────────────────────────
ROUTE (fermeture de la boucle T1a→T1b→T1c) :
  (0) T1b-3 produit_fini_recursion INSTANCIÉE au terme u := W := (i+1)_{i<n+1}
      (famille LARGE)  →  {n∈ℕ,H2,H3} ⊢ (n+1)! = Card(∏_{seg n} W × W_n) ;
  (a) LEMME produits_famille_coincident : ∏_{seg n} W = ∏_{seg n} N où
      N := (i+1)_{i<n} (famille ÉTROITE de factorielle_def2(n)) — les DEUX
      graphe_terme coïncident au niveau du produit (double inclusion pointwise
      par AXIOME_PRODUIT_FAM + graphe_terme_valeur, antisymétrie de ⊂) ;
  (b) LEMME valeur_large_au_point : W_n = succ(n)  (famille_successeurs_valeur en
      n, l'hypothèse n∈seg(succ n) DÉRIVÉE de n∈ℕ via T1b-1 + j_dans_union) ;
  (c) INSERTION Card : Card(∏_N × succ n) = Card(Card(∏_N) × succ n)
      (produit_cardinal_bien_defini version terme _pcbd_t, avec Card(succ n) =
      succ n déchargé : n∈ℕ ⇒ succ n∈ℕ ⇒ est_cardinal ⇒ _card_de_card_t) ;
  chaîne composer_egalites + congruences-trou (« wfr » EXOTIQUE) ; le RHS final
  EST, terme à terme, produit_cardinal_binaire(factorielle_def2(n), succ n).

────────────────────────────────────────────────────────────────────────────────
⚠️ MUR STRUCTUREL DOCUMENTÉ — L'OPACITÉ DE valeur_famille (« fam »).
AXIOME_PRODUIT_FAM n'expose la famille QUE par le symbole OPAQUE
valeur_famille(f, ι) = app("fam", f, ι) : F ∈ ∏(f, I) ⇔ func ∧ dom ∧
(∀i)(i∈I ⇒ valeur(F,i) ∈ **valeur_famille(f, i)**).  AUCUN des 22 axiomes ne relie
« fam » à la valeur réelle valeur(f, ι) — « fam » est un symbole de fonction LIBRE :
tout modèle qui l'interprète arbitrairement satisfait la théorie, donc
« fam(W, n) = succ(n) » et « ∏(W, seg n) = ∏(N, seg n) » sont INDÉPENDANTS
(improuvables ET irréfutables).  Le pont manquant — l'axiome de définition de la
notation X_ι d'une famille-fonction (E II.4.1 : X_ι = f(ι)) — devrait vivre dans
l'ENCODAGE (ensembles_abrege : redéfinir valeur_famille := valeur, migration de
~40 fichiers, ou 23ᵉ axiome — interdit ici).  En attendant, DEUX HYPOTHÈSES
HONNÊTES (instances minimales du pont, mêmes statut/esprit que H2/H3 de T1b-2) :
  HW := (∀i)( i ∈ seg(succ n) ⇒ valeur_famille(W, i) = valeur(W, i) )
  HN := (∀i)( i ∈ seg(n)      ⇒ valeur_famille(N, i) = valeur(N, i) )

HYPOTHÈSES HONNÊTES (exactement 5, aucune autre) :
  •  n ∈ ℕ                                            (T1b-1/T1b-3) ;
  •  H2/H3 : « les membres des produits ∏(W, seg(n)∪{n}) / ∏(W, seg n) sont des
     graphes »                                         (héritées de T1b-2) ;
  •  HW/HN ci-dessus                                   (pont fam↔valeur).

GARDE-FOUS.  Rien postulé ; noyau/subst intouchés ; theorie_ensembles()==22
(asserté au test) ; trous/liants EXOTIQUES (wfr/wfd/jfd/Gfd/ifh) ; le liant « i »
de l'axiome est atteint par ∀-clôture sur jfd puis ré-instanciation (_inst_gen) ;
asserts denses (cible, maillons, formes du corps de l'axiome, hypothèses exactes).

⚠️ PERF : T1b-1 (appelée 3×) déclenche N_existe (~5 min, mémoïsé/session) — slow.
SUITE (rapport) : cas de base factorielle_def2(0)=1 (seg(ℕ,0)=∅ + ∏_∅={∅} sous
H-graphe + un_egale_card_singleton) ; puis convergence avec factorielle_zero /
factorielle_succ_fallback de la chaîne C62.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, egal, impl, appartient, pourtout, inclus, libres_t,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, equivalence_avant, equivalence_arriere, instancie,
)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
    symetrie, composer_egalites, congruence_terme,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_relation import (
    inclusion_antisymetrique,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    cardinal,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.props_restantes.ensembles_divisibilite_propre import (
    _pcbd_t, _card_de_card_t,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_produit.ensembles_arith_cardinale import (
    produit_cardinal_binaire,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (
    successeur,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_1_n_objet_existence.ensembles_ensemble_NN import (
    ensemble_NN, NN_clos_successeur,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_6_familles.ensembles_famille_successeurs import (
    _seg_NN, famille_successeurs, famille_successeurs_valeur, factorielle_def2,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_6_familles.ensembles_seg_successeur import (
    segment_succ_decomposition, _card_de_NN,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_6_familles.ensembles_produit_adjonction import (
    _dech, _inst_fam, _corps_membre, _leibniz_membre_arriere, i_dans_union, j_dans_union,
)
from bourbaki.ii_theorie_des_ensembles.ii_5_produit_famille.ii_5_definitions.ensembles_produit_ecriture import (
    transporter_dans_produit,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_6_familles.ensembles_produit_recursion import (
    produit_fini_recursion, hypotheses_graphes_recursion,
)

#: Trou EXOTIQUE des congruences X ↦ Card(∏ × ·)   (≠ « wpr »/« wct »/« w »).
_TROU = "wfr"
#: Liant pointwise EXOTIQUE de la double inclusion (≠ « i » de l'axiome).
_PT = "jfd"
#: Élément EXOTIQUE des produits (double inclusion).
_EL = "Gfd"
#: Trou du Leibniz fam(W,·)→fam(N,·).
_LB = "wfd"
#: Liant EXOTIQUE des hypothèses-ponts HW/HN.
_HB = "ifh"

#: Liants internes de TOUTE la machinerie traversée (T1b-1/2/3 + cardinal +
#: axiome produit + pcbd/idempotence) — le NOM de n ne doit en heurter aucun.
_NOMS_RESERVES = frozenset({
    "isg", "wsg1", "wsg2", "wsg3", "xso", "bso",
    "Fa", "Fb", "i", "w", "u", "up", "s", "t", "x", "y", "z", "G",
    "Fq", "c", "yb", "zz", "a", "b", "p", "q",
    "X", "Y", "Z", "F", "f", "I", "ifs", "pess", "wpr", "wct",
    "xpccd", "Xpcbd", "Ypcbd", "apcbd", "bpcbd",
    _TROU, _PT, _EL, _LB, _HB,
})


# ── Les termes de l'énoncé ────────────────────────────────────────────────────
def famille_large(n, iota="ifs"):
    """W := (i+1)_{i<succ n}  — la famille de factorielle_def2(succ n)."""
    return famille_successeurs(successeur(var(n) if isinstance(n, str) else n), iota)


# ── Les DEUX hypothèses-ponts honnêtes (cf. MUR en tête de module) ────────────
def hypothese_valuation_large(n="nfr", iota="ifs"):
    """HW := (∀i)( i ∈ seg(ℕ, succ n) ⇒ valeur_famille(W, i) = valeur(W, i) ).

    Instance minimale du pont fam↔valeur pour la famille LARGE (improuvable :
    « fam » est un symbole libre de l'encodage, cf. docstring du module)."""
    vn = var(n) if isinstance(n, str) else n
    W = famille_successeurs(successeur(vn), iota)
    vi = var(_HB)
    return pourtout(_HB, impl(appartient(vi, _seg_NN(successeur(vn))),
                              egal(E.valeur_famille(W, vi), E.valeur(W, vi))))


def hypothese_valuation_etroite(n="nfr", iota="ifs"):
    """HN := (∀i)( i ∈ seg(ℕ, n) ⇒ valeur_famille(N, i) = valeur(N, i) )   (idem, ÉTROITE)."""
    vn = var(n) if isinstance(n, str) else n
    Nw = famille_successeurs(vn, iota)
    vi = var(_HB)
    return pourtout(_HB, impl(appartient(vi, _seg_NN(vn)),
                              egal(E.valeur_famille(Nw, vi), E.valeur(Nw, vi))))


# ── (b) LA VALEUR DE LA FAMILLE LARGE EN n :  W_n = succ(n) ───────────────────
def valeur_large_au_point(n="nfr", iota="ifs"):
    """{ n∈ℕ, HW } ⊢ valeur_famille(W, n) = succ(n).            (route (b) de T1c.)

    n ∈ seg(succ n) est DÉRIVÉ : n ∈ seg(n)∪{n} (j_dans_union, CLOS) transporté
    par T1b-1 (seg(succ n) = seg(n)∪{n}, Leibniz S6) ; puis HW en n et
    famille_successeurs_valeur (graphe_terme_valeur, nom-basée en n)."""
    assert isinstance(n, str), "valeur_large_au_point : n doit être un NOM"
    vn = var(n)
    W = famille_successeurs(successeur(vn), iota)
    Sn = _seg_NN(vn)
    hw = N.assume(hypothese_valuation_large(n, iota))
    seg_eq = segment_succ_decomposition(vn)                 # {n∈ℕ} ⊢ seg(n+1)=seg(n)∪{n}
    n_un = j_dans_union(Sn, vn)                             # ⊢ n ∈ seg(n)∪{n}   [CLOS]
    n_ssn = _leibniz_membre_arriere(n_un, seg_eq, vn)       # {n∈ℕ} ⊢ n ∈ seg(n+1)
    val_n = _dech(famille_successeurs_valeur(successeur(vn), n, iota), n_ssn)
    fam_n = N.modus_ponens(n_ssn, instancie(hw, vn))        # fam(W,n) = valeur(W,n)
    res = composer_egalites(fam_n, val_n)                   # fam(W,n) = succ(n)
    assert res.conclusion == egal(E.valeur_famille(W, vn), successeur(vn)), \
        "valeur_large_au_point : conclusion ≠ fam(W,n)=succ(n)"
    assert res.hypotheses == frozenset({appartient(vn, ensemble_NN()),
                                        hypothese_valuation_large(n, iota)}), \
        "valeur_large_au_point : hypothèses ≠ { n∈ℕ, HW }"
    return res


# ── (a) LES DEUX PRODUITS COÏNCIDENT :  ∏_{seg n} W = ∏_{seg n} N ─────────────
# @livre Ch.II §5.3 Def.1 | E II.32 L.30-36 | PDF p.83  (le produit ne dépend de la famille que par les valeurs X_ι sur I — double inclusion via la caractérisation d'appartenance)
def produits_famille_coincident(n="nfr", iota="ifs"):
    """{ n∈ℕ, HW, HN } ⊢ produit_famille(W, seg n) = produit_famille(N, seg n).

    Les deux familles graphe_terme (segments succ n / n) donnent le MÊME produit
    sur seg(n) : pour i∈seg(n), fam(W,i) = valeur(W,i) = succ(i) = valeur(N,i)
    = fam(N,i) (HW/HN + graphe_terme_valeur des deux côtés, i∈seg(succ n) dérivé
    par T1b-1) ; l'appartenance AXIOME_PRODUIT_FAM se transfère par Leibniz S6 ;
    double inclusion (liant exotique jfd → liant « i » de l'axiome par
    ∀-clôture/ré-instanciation, élément Gfd → liant canonique « z » de ⊂) ;
    antisymétrie de ⊂ (A1) conclut."""
    assert isinstance(n, str), "produits_famille_coincident : n doit être un NOM"
    vn = var(n)
    W = famille_successeurs(successeur(vn), iota)
    Nw = famille_successeurs(vn, iota)
    Sn = _seg_NN(vn)
    PW, PN = E.produit_famille(W, Sn), E.produit_famille(Nw, Sn)
    hw = N.assume(hypothese_valuation_large(n, iota))
    hn = N.assume(hypothese_valuation_etroite(n, iota))
    seg_eq = segment_succ_decomposition(vn)                 # {n∈ℕ} ⊢ seg(n+1)=seg(n)∪{n}

    # ── pointwise (liant exotique jfd) : fam(W,j) = fam(N,j) sous j∈seg(n) ────
    vj = var(_PT)
    hj = N.assume(appartient(vj, Sn))
    j_un = i_dans_union(Sn, vn, vj)                         # {j∈seg n} ⊢ j∈seg(n)∪{n}
    j_ssn = _leibniz_membre_arriere(j_un, seg_eq, vj)       # {n∈ℕ, j∈seg n} ⊢ j∈seg(n+1)
    valW = _dech(famille_successeurs_valeur(successeur(vn), _PT, iota), j_ssn)
    valN = famille_successeurs_valeur(vn, _PT, iota)        # {j∈seg n} ⊢ val(N,j)=succ j
    famW = N.modus_ponens(j_ssn, instancie(hw, vj))         # fam(W,j) = valeur(W,j)
    famN = N.modus_ponens(hj, instancie(hn, vj))            # fam(N,j) = valeur(N,j)
    succ_to_valN = N.modus_ponens(valN, symetrie(E.valeur(Nw, vj), successeur(vj)))
    valN_to_famN = N.modus_ponens(famN, symetrie(E.valeur_famille(Nw, vj), E.valeur(Nw, vj)))
    eq_fam = composer_egalites(composer_egalites(famW, valW),
                               composer_egalites(succ_to_valN, valN_to_famN))
    assert eq_fam.conclusion == egal(E.valeur_famille(W, vj), E.valeur_famille(Nw, vj)), \
        "coincident : fam(W,j)=fam(N,j) mal formé"

    # Leibniz S6 (trou exotique wfd) : (val(F,j)∈fam(W,j)) ⇔ (val(F,j)∈fam(N,j))
    vF = var(_EL)
    leib = N.modus_ponens(eq_fam, N.s6(E.valeur_famille(W, vj), E.valeur_famille(Nw, vj),
                                       _LB, appartient(E.valeur(vF, vj), var(_LB))))

    def _sens(src, dst, imp_dir):
        """(F ∈ ∏(src, seg n)) ⇒ (F ∈ ∏(dst, seg n))   [sous n∈ℕ, HW, HN]."""
        PA = E.produit_famille(src, Sn)
        hF = N.assume(appartient(vF, PA))
        vals = _corps_membre(hF, src, Sn, vF)[3]
        mem = N.modus_ponens(hj, instancie(vals, vj))       # val(F,j) ∈ fam(src,j)
        mem2 = N.modus_ponens(mem, imp_dir)                 # val(F,j) ∈ fam(dst,j)
        imp_j = N.loi_deduction(appartient(vj, Sn), mem2)
        # liant « i » de l'axiome : ∀-clôture sur jfd puis ré-instanciation (_inst_gen)
        vals_dst = N.generalisation("i", instancie(N.generalisation(_PT, imp_j), var("i")))
        # Transport src → dst : depuis le 26 juil. 2026, le corps de la Déf. 1 a un
        # conjoint de TÊTE « F ⊂ seg n × ⋃_ι fam(dst,ι) », qu'il faut RECONSTRUIRE
        # (la réunion dépend de la famille) — `transporter_dans_produit` le fait, et
        # asserte au passage que `vals_dst` porte bien sur la famille dst.
        f_in = transporter_dans_produit(hF, vals_dst, vF, src, dst, Sn)
        assert f_in.conclusion == appartient(vF, E.produit_famille(dst, Sn)), \
            "coincident : conclusion ≠ F ∈ ∏(dst, seg n)"
        return N.loi_deduction(appartient(vF, PA), f_in)

    imp_WN = _sens(W, Nw, equivalence_avant(leib))
    imp_NW = _sens(Nw, W, equivalence_arriere(leib))

    def _inclusion(imp_thm, ta, tb):
        """(F∈A ⇒ F∈B) [F exotique] → ⊢ A ⊂ B  (liant canonique « z » de ⊂)."""
        incl = N.generalisation("z", instancie(N.generalisation(_EL, imp_thm), var("z")))
        assert incl.conclusion == inclus(ta, tb), "coincident : inclusion ≠ liant « z »"
        return incl

    res = N.modus_ponens(conjonction_intro(_inclusion(imp_WN, PW, PN),
                                           _inclusion(imp_NW, PN, PW)),
                         inclusion_antisymetrique(PW, PN))
    assert res.conclusion == egal(PW, PN), "coincident : conclusion ≠ ∏W=∏N"
    assert res.hypotheses == frozenset({appartient(vn, ensemble_NN()),
                                        hypothese_valuation_large(n, iota),
                                        hypothese_valuation_etroite(n, iota)}), \
        "coincident : hypothèses ≠ { n∈ℕ, HW, HN }"
    return res


def factorielle_def2_recursion_enonce(n="nfr", iota="ifs"):
    """Formule cible :  factorielle_def2(succ n) = pcb(factorielle_def2(n), succ n)."""
    vn = var(n) if isinstance(n, str) else n
    return egal(factorielle_def2(successeur(vn), iota),
                produit_cardinal_binaire(factorielle_def2(vn, iota), successeur(vn)))


# @livre Ch.III §5.8 Def.2 | E III.41 L.30-32 | PDF p.144  (« (n+1)! = n!(n+1).  Cette dernière relation, jointe à 0!=1, caractérise le terme n!, … par récurrence sur n » — LE PAS de la récurrence, sur le terme réel de la Déf. 2)
# @livre Ch.III §3.3 Prop.5 | E III.26 L.16-19 | PDF p.129  (b) associativité du produit — le cas (seg n, {n}) au niveau cardinal, via T1b-3)
def factorielle_def2_recursion(n="nfr", iota="ifs"):
    """🎯 { n∈ℕ, H2, H3, HW, HN } ⊢ (succ n)!_déf2 = (n!_déf2)·(succ n).

    Conclusion ÉGALE LITTÉRALEMENT factorielle_def2_recursion_enonce(n) ; le RHS
    est terme à terme produit_cardinal_binaire(factorielle_def2(n), succ n).
    Assemblage : T1b-3 (u := famille LARGE) → (a) coïncidence des produits →
    (b) W_n = succ n → insertion Card (produit_cardinal_bien_defini + Card(succ n)
    = succ n déchargé de n∈ℕ).  NON vacueux (la conclusion n'est aucune hyp.)."""
    assert isinstance(n, str), "factorielle_def2_recursion : n doit être un NOM"
    vn = var(n)
    assert not (_NOMS_RESERVES & libres_t(vn)), \
        "factorielle_def2_recursion : nom de n heurtant un liant réservé"
    W = famille_successeurs(successeur(vn), iota)
    Nw = famille_successeurs(vn, iota)
    Sn = _seg_NN(vn)
    PW, PN = E.produit_famille(W, Sn), E.produit_famille(Nw, Sn)
    sn = successeur(vn)

    # (0) T1b-3 au terme u := W :  {n∈ℕ,H2,H3} ⊢ (n+1)! = Card(∏_{seg n} W × W_n)
    rec = produit_fini_recursion(W, vn)
    assert rec.conclusion.termes[0] == factorielle_def2(sn, iota), \
        "factorielle_def2_recursion : LHS de T1b-3 ≠ factorielle_def2(succ n)"

    # (a) ∏_{seg n} W = ∏_{seg n} N  →  congruence-trou X ↦ Card(X × W_n)
    eq_pp = produits_famille_coincident(n, iota)
    gab1 = cardinal(E.produit(var(_TROU), E.valeur_famille(W, vn)))
    imp1 = congruence_terme(var(_TROU), PN, gab1, _TROU)
    c1 = N.modus_ponens(eq_pp, instancie(N.generalisation(_TROU, imp1), PW))
    chain = composer_egalites(rec, c1)

    # (b) W_n = succ(n)  →  congruence-trou X ↦ Card(∏_N × X)
    eq_vn = valeur_large_au_point(n, iota)
    gab2 = cardinal(E.produit(PN, var(_TROU)))
    imp2 = congruence_terme(var(_TROU), sn, gab2, _TROU)
    c2 = N.modus_ponens(eq_vn, instancie(N.generalisation(_TROU, imp2),
                                         E.valeur_famille(W, vn)))
    chain = composer_egalites(chain, c2)
    assert chain.conclusion == egal(factorielle_def2(sn, iota),
                                    produit_cardinal_binaire(PN, sn)), \
        "factorielle_def2_recursion : maillon (a)+(b) ≠ (n+1)! = Card(∏_N × succ n)"

    # (c) insertion Card :  Card(∏_N × succ n) = Card(Card(∏_N) × succ n)
    Hn = N.assume(appartient(vn, ensemble_NN()))            # n ∈ ℕ  (déjà hyp. de rec)
    sn_NN = N.modus_ponens(Hn, instancie(NN_clos_successeur(), vn))     # succ n ∈ ℕ
    _, card_sn = _card_de_NN(sn, sn_NN)                     # est_cardinal(succ n)
    card_eq = N.modus_ponens(card_sn, _card_de_card_t(sn))  # Card(succ n) = succ n
    bd = _pcbd_t(PN, sn, cardinal(PN), sn)
    ins = N.modus_ponens(conjonction_intro(N.reflexivite(cardinal(PN)), card_eq), bd)
    res = composer_egalites(chain, ins)

    # ── asserts denses ────────────────────────────────────────────────────────
    assert res.conclusion == factorielle_def2_recursion_enonce(n, iota), \
        "factorielle_def2_recursion : conclusion ≠ énoncé cible"
    assert res.conclusion.termes[1] == produit_cardinal_binaire(
        factorielle_def2(vn, iota), sn), \
        "factorielle_def2_recursion : RHS ≠ pcb(factorielle_def2(n), succ n)"
    h2, h3 = hypotheses_graphes_recursion(W, vn)
    assert res.hypotheses == frozenset({
        appartient(vn, ensemble_NN()), h2, h3,
        hypothese_valuation_large(n, iota), hypothese_valuation_etroite(n, iota)}), \
        "factorielle_def2_recursion : hypothèses ≠ { n∈ℕ, H2, H3, HW, HN }"
    assert len(res.hypotheses) == 5, "factorielle_def2_recursion : nb hypothèses ≠ 5"
    assert res.conclusion not in res.hypotheses, "factorielle_def2_recursion : VACUOUS"
    return res


__all__ = ["famille_large", "hypothese_valuation_large", "hypothese_valuation_etroite",
           "valeur_large_au_point", "produits_famille_coincident",
           "factorielle_def2_recursion_enonce", "factorielle_def2_recursion"]
