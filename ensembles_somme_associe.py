"""§III.3.3 — Associativité de la SOMME disjointe (équipotence) :
        Eq((A⊔B)⊔C, A⊔(B⊔C)).

Bijection de RÉASSOCIATION DES COPIES  K : (A⊔B)⊔C → A⊔(B⊔C).  Un élément de
(A⊔B)⊔C a la forme :
   ((u,0),0)  u∈A      ((v,1),0)  v∈B      (w,1)  w∈C
On l'envoie sur l'élément correspondant de A⊔(B⊔C) :
   ((u,0),0) ↦ (u,0)        ((v,1),0) ↦ ((v,0),1)        (w,1) ↦ ((w,1),1).

Le terme dispatche sur le marqueur EXTERNE ι=pr₂k puis (pour ι=0) sur le marqueur
INTERNE j=pr₂(pr₁k), via un SÉLECTEUR à trois disjoints (garde ι/j), chaque garde
fausse étant tuée par 0≠1.  MÊME machinerie liants a,b/c,d que la commutativité et
le produit, étendue au cas à trois copies (réduction des projections à DEUX
niveaux : pr externes a,b puis pr internes c,d).

ÉTAT — THÉORÈME COMPLET, tout CERTIFIÉ et TESTÉ (test_somme_associe.py) :
  • assoc_graphe_fonctionnel  (clos)        — K fonctionnel ;
  • assoc_graphe_domaine      (clos)        — dom K = (A⊔B)⊔C ;
  • assoc_graphe_valeur_A     {u∈A}         — K(((u,0),0)) = (u,0) ;
  • assoc_graphe_valeur_B     {v∈B}         — K(((v,1),0)) = ((v,0),1) ;
  • assoc_graphe_valeur_C     {w∈C}         — K((w,1)) = ((w,1),1) ;
  • membre_assoc3             (clos)        — s∈(A⊔B)⊔C ⇔ (caseA ou (caseB ou caseC))
        [caractérisation à 3 FEUILLES : caseA=(∃u)(u∈A et s=((u,0),0)),
         caseB=(∃v)(v∈B et s=((v,1),0)), caseC=(∃r)(r∈C et s=(r,1)) ; décomposition
         à 2 niveaux du marqueur — réutilisable] ;
  • assoc_graphe_injective    (clos)        — injective_dans(K, (A⊔B)⊔C)
        [analyse 3×3 : 3 paires homologues (composantes égales) + 6 hétérogènes tuées
         par contradiction de marqueur (0≠1)] ;
  • assoc_graphe_image        (clos)        — image(K, (A⊔B)⊔C) = A⊔(B⊔C)
        [surjectivité, 3 antécédents] ;
  • assoc_est_bijection       (clos)        — est_bijection_de(K, (A⊔B)⊔C, A⊔(B⊔C)) ;
  • eq_somme_associatif       (clos)        — Eq((A⊔B)⊔C, A⊔(B⊔C)) ;
  • somme_cardinale_associative (clos)      — Card((A⊔B)⊔C) = Card(A⊔(B⊔C))
        [a+(b+c) = (a+b)+c, Cor. de Prop. 5, via _prop1_direct_t].
"""
from __future__ import annotations

from formule import (Terme, var, egal, et, ou, non, appartient, existe,
                     subst_t, subst_f)
import noyau_abrege as N
import ensembles_abrege as E
from tactiques_abrege import a_implique_a, syllogisme
from tactiques_abrege2 import (conjonction_intro, conjonction_elim_gauche,
                               conjonction_elim_droite, equivalence_avant,
                               equivalence_arriere, equivalence_transitivite,
                               instancie, cas)
from tactiques_abrege_egalite import (symetrie, composer_egalites, congruence_terme)
from tactiques_abrege_quantif import (existe_elimination, alpha_existe)
from ensembles_fonction_terme import (membre_graphe_terme, graphe_terme_fonctionnel)
from ensembles_cantor import (graphe_terme_domaine, graphe_terme_valeur)
from ensembles_somme_disjointe import (somme_disjointe, ZERO, UN,
                                       injection_gauche_dans_somme,
                                       injection_droite_dans_somme,
                                       membre_somme_caracterise, _ou_congruence)
from ensembles_produit_commute import (_projection_premiere_ab, _projection_seconde_ab)
from ensembles_vide_singleton import vide_distinct_singleton
from ensembles_fonctions import valeur_caracterisation
from ensembles_couples import couple_egal_implique_composantes
from ensembles_somme_equipotence import _neg_un_egal_zero


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def _equiv_rhs(equiv_concl):
    """De la conclusion d'une équivalence P⇔Q (= et(P⇒Q, Q⇒P) = non(ou(...))),
    renvoie Q.  P⇒Q est à .sous[0].sous[0].sous[0] (= ou(non P, Q)), son cons. à .sous[1]."""
    return equiv_concl.sous[0].sous[0].sous[0].sous[1]


def _ren(ex_node, cible):
    """⊢ (∃src)R ⇔ (∃cible)R[src→cible], OU réflexivité si src==cible déjà.
    (Renommage-α tolérant : évite l'erreur identité-rename d'alpha_existe.)"""
    from tactiques_abrege_quantif import alpha_existe as _ax
    from tactiques_abrege2 import equivalence_avant as _eqav
    src = ex_node.lieur
    if src == cible:
        # identité : (∃src)R ⇔ (∃src)R  (réflexivité de l'équivalence)
        from tactiques_abrege import a_implique_a
        whole = existe(src, ex_node.sous[0])
        return conjonction_intro(a_implique_a(whole), a_implique_a(whole))
    return _ax(src, cible, ex_node.sous[0])


def _ABC_gauche(a, b, c):
    return somme_disjointe(somme_disjointe(_t(a), _t(b)), _t(c))   # (A⊔B)⊔C


def _ABC_droite(a, b, c):
    return somme_disjointe(_t(a), somme_disjointe(_t(b), _t(c)))   # A⊔(B⊔C)


# ═══════════════════════════════════════════════════════════════════════════════
# Le terme de réassociation  T(k) = τc( GA ou (GB ou GC) ),  cond(c,k) ci-dessous
# ═══════════════════════════════════════════════════════════════════════════════
def _cond(vc, pr1k, pr2k, pr1pr1k, pr2pr1k):
    """La condition cond(c) = GA ou (GB ou GC) en fonction des 4 projections de k."""
    GA = et(et(egal(pr2k, ZERO), egal(pr2pr1k, ZERO)), egal(vc, E.couple(pr1pr1k, ZERO)))
    GB = et(et(egal(pr2k, ZERO), egal(pr2pr1k, UN)),
            egal(vc, E.couple(E.couple(pr1pr1k, ZERO), UN)))
    GC = et(egal(pr2k, UN), egal(vc, E.couple(E.couple(pr1k, UN), UN)))
    return ou(GA, ou(GB, GC))


def _assoc_terme(k="k"):
    """T(k) := τc( GA ou (GB ou GC) ).   (pr externes a,b ; pr internes c,d.)"""
    vk = var(k)
    pr1k = E.pr1(vk, "a", "b")
    pr2k = E.pr2(vk, "a", "b")
    pr1pr1k = E.pr1(pr1k, "c", "d")
    pr2pr1k = E.pr2(pr1k, "c", "d")
    return E.tau("c", _cond(var("c"), pr1k, pr2k, pr1pr1k, pr2pr1k))


def _assoc_graphe(a, b, c, k="k"):
    """K := graphe_terme((A⊔B)⊔C, T, "k")."""
    return E.graphe_terme(_ABC_gauche(a, b, c), _assoc_terme(k), k)


# ── PALIER 1 : K fonctionnel ──────────────────────────────────────────────────
def assoc_graphe_fonctionnel(a="A", b="B", c="C"):
    """⊢ K est fonctionnel.   (cas C54, clos.)"""
    return graphe_terme_fonctionnel(_ABC_gauche(a, b, c), _assoc_terme("k"), "k", "t")


# ── PALIER 2 : dom K = (A⊔B)⊔C ────────────────────────────────────────────────
def assoc_graphe_domaine(a="A", b="B", c="C"):
    """⊢ dom(K) = (A⊔B)⊔C.   (clos.)"""
    return graphe_terme_domaine(_ABC_gauche(a, b, c), _assoc_terme("k"), "k", "y", "z")


# ═══════════════════════════════════════════════════════════════════════════════
# Sélecteur à 3 gardes : sous gA, ¬gB, ¬gC,
#   ((gA et c=vA) ou ((gB et c=vB) ou (gC et c=vC))) ⇔ (c=vA)
# ═══════════════════════════════════════════════════════════════════════════════
def _garde3(thm_gA, thm_ngB, thm_ngC, vA, vB, vC, vc):
    """{⊢gA, ⊢¬gB, ⊢¬gC} ⊢ (GA ou (GB ou GC)) ⇔ (c=vA),  Gᵢ=(gᵢ et c=vᵢ)."""
    gA = thm_gA.conclusion
    gB = thm_ngB.conclusion.sous[0]
    gC = thm_ngC.conclusion.sous[0]
    eqA, eqB, eqC = egal(vc, vA), egal(vc, vB), egal(vc, vC)
    GA, GB, GC = et(gA, eqA), et(gB, eqB), et(gC, eqC)
    GBC = ou(GB, GC)
    disj = ou(GA, GBC)
    brA = N.loi_deduction(GA, conjonction_elim_droite(N.assume(GA)))          # GA ⇒ c=vA
    hB = N.assume(GB)
    exfB = N.modus_ponens(conjonction_elim_gauche(hB),
                          N.modus_ponens(thm_ngB, N.s2(non(gB), eqA)))
    brB = N.loi_deduction(GB, exfB)
    hC = N.assume(GC)
    exfC = N.modus_ponens(conjonction_elim_gauche(hC),
                          N.modus_ponens(thm_ngC, N.s2(non(gC), eqA)))
    brC = N.loi_deduction(GC, exfC)
    brBC = N.loi_deduction(GBC, cas(N.assume(GBC), brB, brC))                 # (GB ou GC) ⇒ c=vA
    fwd = N.loi_deduction(disj, cas(N.assume(disj), brA, brBC))
    inj = N.modus_ponens(conjonction_intro(thm_gA, N.assume(eqA)), N.s2(GA, GBC))
    bwd = N.loi_deduction(eqA, inj)
    return conjonction_intro(fwd, bwd)


def _neg_conj_gauche(thm_neg_first, second):
    """⊢ ¬P ⟹ ⊢ ¬(P et Q)."""
    P = thm_neg_first.conclusion.sous[0]
    conj = et(P, second)
    h = N.assume(conj)
    falso = N.modus_ponens(conjonction_elim_gauche(h),
                           N.modus_ponens(thm_neg_first, N.s2(non(P), non(conj))))
    return N.modus_ponens(N.loi_deduction(conj, falso), N.s1(non(conj)))


def _neg_conj_droite(p, thm_neg_second):
    """⊢ ¬Q ⟹ ⊢ ¬(P et Q)."""
    Q = thm_neg_second.conclusion.sous[0]
    conj = et(p, Q)
    h = N.assume(conj)
    falso = N.modus_ponens(conjonction_elim_droite(h),
                           N.modus_ponens(thm_neg_second, N.s2(non(Q), non(conj))))
    return N.modus_ponens(N.loi_deduction(conj, falso), N.s1(non(conj)))


# ── Valeur du sélecteur sur chaque copie (réduction des projections à 2 niveaux) ─
def _selecteur_copie_A(u):
    """⊢ W[((u,0),0)] = (u, 0).   (copie A : externe 0, interne 0, clos.)"""
    vu = _t(u)
    vc = var("c")
    inn = E.couple(vu, ZERO)                  # (u,0)
    cpl = E.couple(inn, ZERO)                 # ((u,0),0)
    # projections NON réduites (telles qu'elles apparaissent dans W[cpl])
    pr1k = E.pr1(cpl, "a", "b"); pr2k = E.pr2(cpl, "a", "b")
    pr1pr1k = E.pr1(pr1k, "c", "d"); pr2pr1k = E.pr2(pr1k, "c", "d")
    cond0 = _cond(vc, pr1k, pr2k, pr1pr1k, pr2pr1k)
    # étape 1 : pr2k → 0,  pr1k → (u,0)
    pr2k_eq = _projection_seconde_ab(inn, ZERO, "a", "b")     # pr₂cpl = 0
    pr1k_eq = _projection_premiere_ab(inn, ZERO, "a", "b")    # pr₁cpl = (u,0)
    cond_a = _cond(vc, inn, ZERO, E.pr1(inn, "c", "d"), E.pr2(inn, "c", "d"))
    e_pr2 = N.modus_ponens(pr2k_eq, N.s6(pr2k, ZERO, "w",
            _cond(vc, pr1k, var("w"), pr1pr1k, pr2pr1k)))      # cond0 ⇔ cond(pr2k→0)
    cond_mid = _cond(vc, pr1k, ZERO, pr1pr1k, pr2pr1k)
    e_pr1 = N.modus_ponens(pr1k_eq, N.s6(pr1k, inn, "w",
            _cond(vc, var("w"), ZERO, E.pr1(var("w"), "c", "d"), E.pr2(var("w"), "c", "d"))))
    cond0_eq_a = equivalence_transitivite(e_pr2, e_pr1)        # cond0 ⇔ cond_a
    # étape 2 : pr₁inn → u, pr₂inn → 0
    pr1in_eq = _projection_premiere_ab(vu, ZERO, "c", "d")    # pr₁(u,0) = u
    pr2in_eq = _projection_seconde_ab(vu, ZERO, "c", "d")     # pr₂(u,0) = 0
    cond_b = _cond(vc, inn, ZERO, vu, ZERO)
    e_pr1in = N.modus_ponens(pr1in_eq, N.s6(E.pr1(inn, "c", "d"), vu, "w",
            _cond(vc, inn, ZERO, var("w"), E.pr2(inn, "c", "d"))))
    cond_mid2 = _cond(vc, inn, ZERO, vu, E.pr2(inn, "c", "d"))
    e_pr2in = N.modus_ponens(pr2in_eq, N.s6(E.pr2(inn, "c", "d"), ZERO, "w",
            _cond(vc, inn, ZERO, vu, var("w"))))
    cond_a_eq_b = equivalence_transitivite(e_pr1in, e_pr2in)   # cond_a ⇔ cond_b
    cond0_eq_b = equivalence_transitivite(cond0_eq_a, cond_a_eq_b)
    # cond_b = GA' ou (GB' ou GC') avec gA=(0=0 et 0=0), gB=(0=0 et 0=1), gC=(0=1)
    vA = E.couple(vu, ZERO)
    vB = E.couple(E.couple(vu, ZERO), UN)
    vC = E.couple(E.couple(inn, UN), UN)
    gA = et(egal(ZERO, ZERO), egal(ZERO, ZERO))
    gB = et(egal(ZERO, ZERO), egal(ZERO, UN))
    gC = egal(ZERO, UN)
    thm_gA = conjonction_intro(N.reflexivite(ZERO), N.reflexivite(ZERO))      # gA vrai
    thm_ngB = _neg_conj_droite(egal(ZERO, ZERO), vide_distinct_singleton())   # ¬gB (0≠1)
    thm_ngC = vide_distinct_singleton()                                       # ¬gC (0≠1)
    gd = _garde3(thm_gA, thm_ngB, thm_ngC, vA, vB, vC, vc)     # cond_b ⇔ (c=vA)
    chain = equivalence_transitivite(cond0_eq_b, gd)          # cond0 ⇔ (c=(u,0))
    return _finish(cond0, vc, vA, chain)


def _selecteur_copie_B(v):
    """⊢ W[((v,1),0)] = ((v,0),1).   (copie B : externe 0, interne 1, clos.)"""
    vv = _t(v)
    vc = var("c")
    inn = E.couple(vv, UN)                    # (v,1)
    cpl = E.couple(inn, ZERO)                 # ((v,1),0)
    pr1k = E.pr1(cpl, "a", "b"); pr2k = E.pr2(cpl, "a", "b")
    pr1pr1k = E.pr1(pr1k, "c", "d"); pr2pr1k = E.pr2(pr1k, "c", "d")
    cond0 = _cond(vc, pr1k, pr2k, pr1pr1k, pr2pr1k)
    pr2k_eq = _projection_seconde_ab(inn, ZERO, "a", "b")     # pr₂cpl = 0
    pr1k_eq = _projection_premiere_ab(inn, ZERO, "a", "b")    # pr₁cpl = (v,1)
    e_pr2 = N.modus_ponens(pr2k_eq, N.s6(pr2k, ZERO, "w",
            _cond(vc, pr1k, var("w"), pr1pr1k, pr2pr1k)))
    e_pr1 = N.modus_ponens(pr1k_eq, N.s6(pr1k, inn, "w",
            _cond(vc, var("w"), ZERO, E.pr1(var("w"), "c", "d"), E.pr2(var("w"), "c", "d"))))
    cond0_eq_a = equivalence_transitivite(e_pr2, e_pr1)        # cond0 ⇔ cond_a
    pr1in_eq = _projection_premiere_ab(vv, UN, "c", "d")      # pr₁(v,1) = v
    pr2in_eq = _projection_seconde_ab(vv, UN, "c", "d")       # pr₂(v,1) = 1
    e_pr1in = N.modus_ponens(pr1in_eq, N.s6(E.pr1(inn, "c", "d"), vv, "w",
            _cond(vc, inn, ZERO, var("w"), E.pr2(inn, "c", "d"))))
    e_pr2in = N.modus_ponens(pr2in_eq, N.s6(E.pr2(inn, "c", "d"), UN, "w",
            _cond(vc, inn, ZERO, vv, var("w"))))
    cond_a_eq_b = equivalence_transitivite(e_pr1in, e_pr2in)
    cond0_eq_b = equivalence_transitivite(cond0_eq_a, cond_a_eq_b)
    # cond_b avec gA=(0=0 et 1=0), gB=(0=0 et 1=1), gC=(0=1) → garde B active
    vA = E.couple(vv, ZERO)
    vB = E.couple(E.couple(vv, ZERO), UN)
    vC = E.couple(E.couple(inn, UN), UN)
    gA = et(egal(ZERO, ZERO), egal(UN, ZERO))
    gB = et(egal(ZERO, ZERO), egal(UN, UN))
    gC = egal(ZERO, UN)
    # ici la garde ACTIVE est B (pas A) → on construit la sélection de B :
    # ((gA et c=vA) ou ((gB et c=vB) ou (gC et c=vC))) ⇔ (c=vB)
    thm_gB = conjonction_intro(N.reflexivite(ZERO), N.reflexivite(UN))        # gB vrai
    thm_ngA = _neg_conj_droite(egal(ZERO, ZERO), _neg_un_egal_zero())         # ¬gA (1≠0)
    thm_ngC = vide_distinct_singleton()                                       # ¬gC (0≠1)
    gd = _garde3_milieu(thm_ngA, thm_gB, thm_ngC, vA, vB, vC, vc)  # cond_b ⇔ (c=vB)
    chain = equivalence_transitivite(cond0_eq_b, gd)
    return _finish(cond0, vc, vB, chain)


def _selecteur_copie_C(w):
    """⊢ W[(w,1)] = ((w,1),1).   (copie C : externe 1, clos.)"""
    vw = _t(w)
    vc = var("c")
    cpl = E.couple(vw, UN)                    # (w,1)
    pr1k = E.pr1(cpl, "a", "b"); pr2k = E.pr2(cpl, "a", "b")
    pr1pr1k = E.pr1(pr1k, "c", "d"); pr2pr1k = E.pr2(pr1k, "c", "d")
    cond0 = _cond(vc, pr1k, pr2k, pr1pr1k, pr2pr1k)
    pr2k_eq = _projection_seconde_ab(vw, UN, "a", "b")       # pr₂cpl = 1
    pr1k_eq = _projection_premiere_ab(vw, UN, "a", "b")      # pr₁cpl = w
    e_pr2 = N.modus_ponens(pr2k_eq, N.s6(pr2k, UN, "w",
            _cond(vc, pr1k, var("w"), pr1pr1k, pr2pr1k)))
    e_pr1 = N.modus_ponens(pr1k_eq, N.s6(pr1k, vw, "w",
            _cond(vc, var("w"), UN, E.pr1(var("w"), "c", "d"), E.pr2(var("w"), "c", "d"))))
    cond0_eq_a = equivalence_transitivite(e_pr2, e_pr1)       # cond0 ⇔ cond_a
    # cond_a : gA=(1=0 et pr2pr1=0), gB=(1=0 et ...), gC=(1=1) → garde C active.
    # Les projections internes pr₁(pr₁cpl)=pr₁w restent symboliques mais leurs disjoints
    # A,B sont tués par gardeC-externe 1=0.  vA,vB contiennent pr₁(w) (non réduit) — peu
    # importe car leurs gardes (1=0) sont fausses.
    pr1w = E.pr1(vw, "c", "d"); pr2w = E.pr2(vw, "c", "d")
    vA = E.couple(pr1w, ZERO)
    vB = E.couple(E.couple(pr1w, ZERO), UN)
    vC = E.couple(E.couple(vw, UN), UN)
    gA = et(egal(UN, ZERO), egal(pr2w, ZERO))
    gB = et(egal(UN, ZERO), egal(pr2w, UN))
    gC = egal(UN, UN)
    thm_gC = N.reflexivite(UN)                                               # gC vrai
    thm_ngA = _neg_conj_gauche(_neg_un_egal_zero(), egal(pr2w, ZERO))         # ¬gA (1≠0)
    thm_ngB = _neg_conj_gauche(_neg_un_egal_zero(), egal(pr2w, UN))           # ¬gB (1≠0)
    gd = _garde3_droite(thm_ngA, thm_ngB, thm_gC, vA, vB, vC, vc)  # cond_a ⇔ (c=vC)
    chain = equivalence_transitivite(cond0_eq_a, gd)
    return _finish(cond0, vc, vC, chain)


def _garde3_milieu(thm_ngA, thm_gB, thm_ngC, vA, vB, vC, vc):
    """{⊢¬gA, ⊢gB, ⊢¬gC} ⊢ (GA ou (GB ou GC)) ⇔ (c=vB)."""
    gA = thm_ngA.conclusion.sous[0]
    gB = thm_gB.conclusion
    gC = thm_ngC.conclusion.sous[0]
    eqA, eqB, eqC = egal(vc, vA), egal(vc, vB), egal(vc, vC)
    GA, GB, GC = et(gA, eqA), et(gB, eqB), et(gC, eqC)
    GBC = ou(GB, GC)
    disj = ou(GA, GBC)
    hA = N.assume(GA)
    exfA = N.modus_ponens(conjonction_elim_gauche(hA),
                          N.modus_ponens(thm_ngA, N.s2(non(gA), eqB)))
    brA = N.loi_deduction(GA, exfA)
    brB = N.loi_deduction(GB, conjonction_elim_droite(N.assume(GB)))          # GB ⇒ c=vB
    hC = N.assume(GC)
    exfC = N.modus_ponens(conjonction_elim_gauche(hC),
                          N.modus_ponens(thm_ngC, N.s2(non(gC), eqB)))
    brC = N.loi_deduction(GC, exfC)
    brBC = N.loi_deduction(GBC, cas(N.assume(GBC), brB, brC))
    fwd = N.loi_deduction(disj, cas(N.assume(disj), brA, brBC))
    # ⇐ : c=vB ⇒ GB ⇒ (GB ou GC) ⇒ (GA ou (GB ou GC))
    inj_into = N.modus_ponens(conjonction_intro(thm_gB, N.assume(eqB)), N.s2(GB, GC))  # (GB ou GC)
    GBC_or_GA = N.modus_ponens(inj_into, N.s2(GBC, GA))   # (GBC ou GA)
    disj_thm = N.modus_ponens(GBC_or_GA, N.s3(GBC, GA))  # (GA ou GBC)
    bwd = N.loi_deduction(eqB, disj_thm)
    return conjonction_intro(fwd, bwd)


def _garde3_droite(thm_ngA, thm_ngB, thm_gC, vA, vB, vC, vc):
    """{⊢¬gA, ⊢¬gB, ⊢gC} ⊢ (GA ou (GB ou GC)) ⇔ (c=vC)."""
    gA = thm_ngA.conclusion.sous[0]
    gB = thm_ngB.conclusion.sous[0]
    gC = thm_gC.conclusion
    eqA, eqB, eqC = egal(vc, vA), egal(vc, vB), egal(vc, vC)
    GA, GB, GC = et(gA, eqA), et(gB, eqB), et(gC, eqC)
    GBC = ou(GB, GC)
    disj = ou(GA, GBC)
    hA = N.assume(GA)
    exfA = N.modus_ponens(conjonction_elim_gauche(hA),
                          N.modus_ponens(thm_ngA, N.s2(non(gA), eqC)))
    brA = N.loi_deduction(GA, exfA)
    hB = N.assume(GB)
    exfB = N.modus_ponens(conjonction_elim_gauche(hB),
                          N.modus_ponens(thm_ngB, N.s2(non(gB), eqC)))
    brB = N.loi_deduction(GB, exfB)
    brC = N.loi_deduction(GC, conjonction_elim_droite(N.assume(GC)))          # GC ⇒ c=vC
    brBC = N.loi_deduction(GBC, cas(N.assume(GBC), brB, brC))
    fwd = N.loi_deduction(disj, cas(N.assume(disj), brA, brBC))
    # ⇐ : c=vC ⇒ GC ⇒ (GB ou GC) ⇒ (GA ou (GB ou GC))
    GC_thm = conjonction_intro(thm_gC, N.assume(eqC))        # GC
    # S2 : GC ⇒ (GC ou GB) ; S3 : (GC ou GB) ⇒ (GB ou GC)
    GC_or_GB = N.modus_ponens(GC_thm, N.s2(GC, GB))
    GBC_thm = N.modus_ponens(GC_or_GB, N.s3(GC, GB))         # (GB ou GC)
    GA_or = N.modus_ponens(GBC_thm, N.s2(GBC, GA))           # (GBC ou GA)
    disj_thm = N.modus_ponens(GA_or, N.s3(GBC, GA))          # (GA ou GBC)
    bwd = N.loi_deduction(eqC, disj_thm)
    return conjonction_intro(fwd, bwd)


def _finish(cond0, vc, val, chain):
    """De ⊢ cond0 ⇔ (c=val), conclure ⊢ τc(cond0) = val."""
    gen = N.generalisation("c", chain)
    tau_eq = N.modus_ponens(gen, N.s7(cond0, egal(vc, val), "c"))   # τc(cond0)=τc(c=val)
    tau_val = N.modus_ponens(
        N.modus_ponens(N.reflexivite(val), N.s5(egal(vc, val), val, "c")),
        N.existe_temoin(egal(vc, val), "c"))                       # τc(c=val)=val
    return composer_egalites(tau_eq, tau_val)                      # τc(cond0)=val


# ═══════════════════════════════════════════════════════════════════════════════
# Valeur de K en un couple CONCRET : K(cpl) = T[cpl]  (terme-tolérant)
# ═══════════════════════════════════════════════════════════════════════════════
def _assoc_graphe_valeur_t(a, b, c, cpl):
    """{cpl ∈ (A⊔B)⊔C} ⊢ K(cpl) = T[cpl],  cpl un TERME (couple concret)."""
    ABC = _ABC_gauche(a, b, c)
    T = _assoc_terme("k")
    K = E.graphe_terme(ABC, T, "k")
    Tcpl = subst_t(cpl, "k", T)                              # T[cpl]
    ax_K = N.axiome(E.theorie_graphe_terme(ABC, T, "k", "yb", "zz"),
                    E.axiome_graphe_terme(ABC, T, "k", "yb", "zz"))
    paire_cpl = E.couple(cpl, Tcpl)
    car = instancie(ax_K, paire_cpl)
    gbody_k = et(et(egal(paire_cpl, E.couple(var("k"), var("yb"))),
                    appartient(var("k"), ABC)), egal(var("yb"), T))
    body_k0 = subst_f(cpl, "k", gbody_k)
    h_in = N.assume(appartient(cpl, ABC))
    wit_yb = conjonction_intro(conjonction_intro(N.reflexivite(paire_cpl), h_in),
                               N.reflexivite(Tcpl))
    ex_yb = N.modus_ponens(wit_yb, N.s5(body_k0, Tcpl, "yb"))
    ex_kyb = N.modus_ponens(ex_yb, N.s5(existe("yb", gbody_k), cpl, "k"))
    cpl_in_K = N.modus_ponens(ex_kyb, equivalence_arriere(car))   # (cpl,T[cpl])∈K
    dom_membre = N.modus_ponens(cpl_in_K,
        N.s5(appartient(E.couple(cpl, var("y")), K), Tcpl, "y"))
    vc = valeur_caracterisation(K, cpl)
    vc_all = N.generalisation("y", vc)
    vc_Tcpl = instancie(vc_all, Tcpl)
    Tcpl_K = N.modus_ponens(cpl_in_K, equivalence_avant(vc_Tcpl))   # T[cpl]=K(cpl)
    K_Tcpl = N.modus_ponens(Tcpl_K, symetrie(Tcpl, E.valeur(K, cpl)))  # K(cpl)=T[cpl]
    K_Tcpl = N.modus_ponens(assoc_graphe_fonctionnel(a, b, c),
                            N.loi_deduction(E.est_fonctionnel(K), K_Tcpl))
    K_Tcpl = N.modus_ponens(dom_membre, N.loi_deduction(
        existe("y", appartient(E.couple(cpl, var("y")), K)), K_Tcpl))
    return K_Tcpl                                           # {cpl∈(A⊔B)⊔C} ⊢ K(cpl)=T[cpl]


# ── PALIER 3 : valeur de K sur chaque copie ───────────────────────────────────
def assoc_graphe_valeur_A(a="A", b="B", c="C", u="u"):
    """{u ∈ A} ⊢ K(((u,0),0)) = (u, 0).   (copie A.)"""
    vu = _t(u)
    va, vb, vc_ = _t(a), _t(b), _t(c)
    AB = somme_disjointe(va, vb)
    cpl = E.couple(E.couple(vu, ZERO), ZERO)               # ((u,0),0)
    ABC = _ABC_gauche(a, b, c)
    # {u∈A} ⊢ ((u,0),0)∈(A⊔B)⊔C : (u,0)∈A⊔B (inj gauche), puis inj gauche de niveau 2
    u0_in = N.modus_ponens(N.assume(appartient(vu, va)),
                           injection_gauche_dans_somme(vu, va, vb))   # {u∈A} ⊢ (u,0)∈A⊔B
    cpl_in = N.modus_ponens(u0_in,
        injection_gauche_dans_somme(E.couple(vu, ZERO), AB, vc_))     # {u∈A} ⊢ ((u,0),0)∈(A⊔B)⊔C
    Kval = N.modus_ponens(cpl_in, N.loi_deduction(appartient(cpl, ABC),
        _assoc_graphe_valeur_t(a, b, c, cpl)))             # {u∈A} ⊢ K(cpl)=T[cpl]
    sel = _selecteur_copie_A(vu)                           # W[cpl]=(u,0) ; T[cpl]=W[cpl]
    return composer_egalites(Kval, sel)                    # {u∈A} ⊢ K(cpl)=(u,0)


def assoc_graphe_valeur_B(a="A", b="B", c="C", v="v"):
    """{v ∈ B} ⊢ K(((v,1),0)) = ((v,0),1).   (copie B.)"""
    vv = _t(v)
    va, vb, vc_ = _t(a), _t(b), _t(c)
    AB = somme_disjointe(va, vb)
    cpl = E.couple(E.couple(vv, UN), ZERO)                 # ((v,1),0)
    ABC = _ABC_gauche(a, b, c)
    v1_in = N.modus_ponens(N.assume(appartient(vv, vb)),
                           injection_droite_dans_somme(vv, va, vb))    # {v∈B} ⊢ (v,1)∈A⊔B
    cpl_in = N.modus_ponens(v1_in,
        injection_gauche_dans_somme(E.couple(vv, UN), AB, vc_))        # {v∈B} ⊢ ((v,1),0)∈(A⊔B)⊔C
    Kval = N.modus_ponens(cpl_in, N.loi_deduction(appartient(cpl, ABC),
        _assoc_graphe_valeur_t(a, b, c, cpl)))
    sel = _selecteur_copie_B(vv)                           # W[cpl]=((v,0),1)
    return composer_egalites(Kval, sel)                    # {v∈B} ⊢ K(cpl)=((v,0),1)


def assoc_graphe_valeur_C(a="A", b="B", c="C", w="wc"):
    """{w ∈ C} ⊢ K((w,1)) = ((w,1),1).   (copie C ; élément « wc » par défaut, « w »
    collisionnant avec un trou interne de couple_egal_implique_composantes)."""
    vw = _t(w)
    va, vb, vc_ = _t(a), _t(b), _t(c)
    AB = somme_disjointe(va, vb)
    cpl = E.couple(vw, UN)                                 # (w,1)
    ABC = _ABC_gauche(a, b, c)
    cpl_in = N.modus_ponens(N.assume(appartient(vw, vc_)),
                            injection_droite_dans_somme(vw, AB, vc_))  # (w,1)∈(A⊔B)⊔C
    Kval = N.modus_ponens(cpl_in, N.loi_deduction(appartient(cpl, ABC),
        _assoc_graphe_valeur_t(a, b, c, cpl)))
    sel = _selecteur_copie_C(vw)                           # W[cpl]=((w,1),1)
    return composer_egalites(Kval, sel)                    # {w∈C} ⊢ K(cpl)=((w,1),1)


# ═══════════════════════════════════════════════════════════════════════════════
# CARACTÉRISATION À 3 FEUILLES :  s∈(A⊔B)⊔C ⇔ (caseA ou (caseB ou caseC))
#   caseA = (∃u)(u∈A et s=((u,0),0))   caseB = (∃v)(v∈B et s=((v,1),0))
#   caseC = (∃w)(w∈C et s=(w,1))
# Décomposition à DEUX NIVEAUX du marqueur : marqueur EXTERNE (membre_somme_caracterise
# sur A⊔B, C) puis, dans la copie gauche, marqueur INTERNE (membre_somme_caracterise
# sur A, B).  Construite directement par élimination de témoins emboîtée (pas de lemme
# de distributivité ∃/∨ séparé) : forward = 2+1 témoins, backward = 3 injections.
# ═══════════════════════════════════════════════════════════════════════════════
def _caseA(a, vs, u="u"):
    """caseA = (∃u)(u∈A et s=((u,0),0))."""
    va = _t(a); vu = var(u)
    return existe(u, et(appartient(vu, va),
                        egal(vs, E.couple(E.couple(vu, ZERO), ZERO))))


def _caseB(b, vs, v="v"):
    """caseB = (∃v)(v∈B et s=((v,1),0))."""
    vb = _t(b); vv = var(v)
    return existe(v, et(appartient(vv, vb),
                        egal(vs, E.couple(E.couple(vv, UN), ZERO))))


def _caseC(c, vs, w="r"):
    """caseC = (∃r)(r∈C et s=(r,1)).   (binder « r » ≠ trou « w » de congruence_terme.)"""
    vc = _t(c); vw = var(w)
    return existe(w, et(appartient(vw, vc), egal(vs, E.couple(vw, UN))))


def membre_assoc3(a="A", b="B", c="C", s="s"):
    """⊢ s∈(A⊔B)⊔C ⇔ (caseA ou (caseB ou caseC)).

    caseA=(∃u)(u∈A et s=((u,0),0)) ; caseB=(∃v)(v∈B et s=((v,1),0)) ;
    caseC=(∃w)(w∈C et s=(w,1)).  Décomposition à deux niveaux du marqueur."""
    from tactiques_abrege_quantif import alpha_existe as _ax
    va, vb, vc = _t(a), _t(b), _t(c)
    vs = _t(s)
    AB = somme_disjointe(va, vb)
    ABC = _ABC_gauche(a, b, c)
    cA, cB, cC = _caseA(a, vs), _caseB(b, vs), _caseC(c, vs)
    RHS = ou(cA, ou(cB, cC))

    # ── EXTERNE : s∈(A⊔B)⊔C ⇔ (exABm ou exC) ─────────────────────────────────
    ext = membre_somme_caracterise(AB, vc, vs)   # s∈(A⊔B)⊔C ⇔ ((∃m)(m∈A⊔B et s=(m,0)) ou (∃w)(w∈C et s=(w,1)))
    rhs_ext = _equiv_rhs(ext.conclusion)               # ou(exABm0, exC0)
    exABm0 = rhs_ext.sous[0]   # (∃u)(u∈A⊔B et s=(u,0))  [lieur défaut "u"]
    exC0 = rhs_ext.sous[1]      # (∃v)(v∈C et s=(v,1))    [lieur défaut "v"]
    renM = _ren(exABm0, "m")      # renomme le témoin externe en m
    renW = _ren(exC0, "r")        # renomme en r  → caseC
    ext2 = equivalence_transitivite(ext, _ou_congruence(renM, renW))
    # ext2 : s∈(A⊔B)⊔C ⇔ (exABm ou caseC),  exABm = (∃m)(m∈A⊔B et s=(m,0))
    rhs2 = _equiv_rhs(ext2.conclusion)             # ou(exABm, caseC)
    exABm = rhs2.sous[0]
    assert rhs2.sous[1] == cC

    vm = var("m")
    bodyM = et(appartient(vm, AB), egal(vs, E.couple(vm, ZERO)))   # m∈A⊔B et s=(m,0)

    # ── FORWARD : (exABm ou caseC) ⇒ RHS ─────────────────────────────────────
    # branche exABm : témoin m, m∈A⊔B décomposé en (p,0)/(q,1) → caseA/caseB
    hM = N.assume(bodyM)
    m_in = conjonction_elim_gauche(hM)              # m∈A⊔B
    s_eq_m0 = conjonction_elim_droite(hM)           # s=(m,0)
    inn = membre_somme_caracterise(va, vb, vm)      # m∈A⊔B ⇔ ((∃p)(p∈A et m=(p,0)) ou (∃q)(q∈B et m=(q,1)))
    dec_m0 = N.modus_ponens(m_in, equivalence_avant(inn))
    exP0, exQ0 = dec_m0.conclusion.sous[0], dec_m0.conclusion.sous[1]
    renP = _ren(exP0, "p")
    renQ = _ren(exQ0, "q")
    dec_m = N.modus_ponens(dec_m0, equivalence_avant(_ou_congruence(renP, renQ)))
    exP, exQ = dec_m.conclusion.sous[0], dec_m.conclusion.sous[1]
    vp, vq = var("p"), var("q")
    bP = exP.sous[0]     # p∈A et m=(p,0)
    bQ = exQ.sous[0]     # q∈B et m=(q,1)

    def fwd_P():
        hP = N.assume(bP)
        p_in = conjonction_elim_gauche(hP)          # p∈A
        m_eq = conjonction_elim_droite(hP)          # m=(p,0)
        # s=(m,0) ; m=(p,0) → s=((p,0),0)
        s_eq = composer_egalites(s_eq_m0,
            N.modus_ponens(m_eq, congruence_terme(vm, E.couple(vp, ZERO),
                                                  E.couple(var("w"), ZERO))))   # s=((p,0),0)
        wit = conjonction_intro(p_in, s_eq)         # p∈A et s=((p,0),0)
        ex = N.modus_ponens(wit, N.s5(et(appartient(var("u"), va),
            egal(vs, E.couple(E.couple(var("u"), ZERO), ZERO))), vp, "u"))      # caseA (témoin p)
        into = N.modus_ponens(ex, N.s2(cA, ou(cB, cC)))                         # caseA ⇒ RHS
        return N.loi_deduction(bP, into)

    def fwd_Q():
        hQ = N.assume(bQ)
        q_in = conjonction_elim_gauche(hQ)          # q∈B
        m_eq = conjonction_elim_droite(hQ)          # m=(q,1)
        s_eq = composer_egalites(s_eq_m0,
            N.modus_ponens(m_eq, congruence_terme(vm, E.couple(vq, UN),
                                                  E.couple(var("w"), ZERO))))   # s=((q,1),0)
        wit = conjonction_intro(q_in, s_eq)
        ex = N.modus_ponens(wit, N.s5(et(appartient(var("v"), vb),
            egal(vs, E.couple(E.couple(var("v"), UN), ZERO))), vq, "v"))        # caseB (témoin q)
        into_BC = N.modus_ponens(ex, N.s2(cB, cC))                             # (caseB ou caseC)
        return N.loi_deduction(bQ, _inject_BC(into_BC, cA, cB, cC))

    impP = existe_elimination(fwd_P(), "p")
    impQ = existe_elimination(fwd_Q(), "q")
    body_to_RHS = cas(dec_m, impP, impQ)            # bodyM ⇒ RHS (under no extra hyp, m free)
    impABm = existe_elimination(N.loi_deduction(bodyM, body_to_RHS), "m")   # exABm ⇒ RHS
    # branche caseC : caseC ⇒ RHS
    impC = _caseC_into(cA, cB, cC)                   # caseC ⇒ RHS
    disj_ext = rhs2                                  # (exABm ou caseC)
    fwd_disj = cas(N.assume(disj_ext), impABm, impC)
    fwd = syllogisme(equivalence_avant(ext2), N.loi_deduction(disj_ext, fwd_disj))  # s∈ABC ⇒ RHS

    # ── BACKWARD : RHS ⇒ s∈(A⊔B)⊔C ───────────────────────────────────────────
    def back_A():
        hu = N.assume(_caseA_body(a, vs, "u"))
        u_in = conjonction_elim_gauche(hu)          # u∈A
        s_eq = conjonction_elim_droite(hu)          # s=((u,0),0)
        u0_in = N.modus_ponens(u_in, injection_gauche_dans_somme(var("u"), va, vb))  # (u,0)∈A⊔B
        cpl_in = N.modus_ponens(u0_in, injection_gauche_dans_somme(
            E.couple(var("u"), ZERO), AB, vc))      # ((u,0),0)∈(A⊔B)⊔C
        s_in = N.modus_ponens(cpl_in, equivalence_arriere(N.modus_ponens(
            s_eq, N.s6(vs, E.couple(E.couple(var("u"), ZERO), ZERO), "w",
                       appartient(var("w"), ABC)))))
        return N.loi_deduction(_caseA_body(a, vs, "u"), s_in)

    def back_B():
        hv = N.assume(_caseB_body(b, vs, "v"))
        v_in = conjonction_elim_gauche(hv)          # v∈B
        s_eq = conjonction_elim_droite(hv)          # s=((v,1),0)
        v1_in = N.modus_ponens(v_in, injection_droite_dans_somme(var("v"), va, vb))  # (v,1)∈A⊔B
        cpl_in = N.modus_ponens(v1_in, injection_gauche_dans_somme(
            E.couple(var("v"), UN), AB, vc))        # ((v,1),0)∈(A⊔B)⊔C
        s_in = N.modus_ponens(cpl_in, equivalence_arriere(N.modus_ponens(
            s_eq, N.s6(vs, E.couple(E.couple(var("v"), UN), ZERO), "w",
                       appartient(var("w"), ABC)))))
        return N.loi_deduction(_caseB_body(b, vs, "v"), s_in)

    def back_C():
        hw = N.assume(_caseC_body(c, vs, "r"))
        w_in = conjonction_elim_gauche(hw)          # r∈C
        s_eq = conjonction_elim_droite(hw)          # s=(r,1)
        w1_in = N.modus_ponens(w_in, injection_droite_dans_somme(var("r"), AB, vc))  # (r,1)∈(A⊔B)⊔C
        s_in = N.modus_ponens(w1_in, equivalence_arriere(N.modus_ponens(
            s_eq, N.s6(vs, E.couple(var("r"), UN), "w2",
                       appartient(var("w2"), ABC)))))
        return N.loi_deduction(_caseC_body(c, vs, "r"), s_in)

    impbA = existe_elimination(back_A(), "u")
    impbB = existe_elimination(back_B(), "v")
    impbC = existe_elimination(back_C(), "r")
    impbBC = N.loi_deduction(ou(cB, cC), cas(N.assume(ou(cB, cC)), impbB, impbC))
    bwd = N.loi_deduction(RHS, cas(N.assume(RHS), impbA, impbBC))

    return conjonction_intro(fwd, bwd)


def _caseA_body(a, vs, u="u"):
    va = _t(a); vu = var(u)
    return et(appartient(vu, va), egal(vs, E.couple(E.couple(vu, ZERO), ZERO)))


def _caseB_body(b, vs, v="v"):
    vb = _t(b); vv = var(v)
    return et(appartient(vv, vb), egal(vs, E.couple(E.couple(vv, UN), ZERO)))


def _caseC_body(c, vs, w="r"):
    vc = _t(c); vw = var(w)
    return et(appartient(vw, vc), egal(vs, E.couple(vw, UN)))


def _caseC_into(cA, cB, cC):
    """⊢ caseC ⇒ (caseA ou (caseB ou caseC))."""
    h = N.assume(cC)
    into_BC = N.modus_ponens(N.modus_ponens(h, N.s2(cC, cB)), N.s3(cC, cB))   # (caseB ou caseC)
    return N.loi_deduction(cC, _inject_BC(into_BC, cA, cB, cC))


def _inject_BC(thm_BC, cA, cB, cC):
    """Γ⊢(caseB ou caseC) ⟹ Γ⊢(caseA ou (caseB ou caseC))."""
    BC = ou(cB, cC)
    return N.modus_ponens(N.modus_ponens(thm_BC, N.s2(BC, cA)), N.s3(BC, cA))


# ═══════════════════════════════════════════════════════════════════════════════
# PALIER 4 : injective_dans(K, (A⊔B)⊔C)  (analyse de cas 3×3)
# ═══════════════════════════════════════════════════════════════════════════════
def _ex_falso(thm_a, thm_na, z):
    """Γ⊢A, Δ⊢¬A ⟹ Γ∪Δ⊢Z.   (ex falso : ¬A ⇒ (A ⇒ Z), S2.)"""
    a = thm_a.conclusion
    return N.modus_ponens(thm_a, N.modus_ponens(thm_na, N.s2(non(a), z)))


def assoc_graphe_injective(a="A", b="B", c="C"):
    """⊢ injective_dans(K, (A⊔B)⊔C).   (la réassociation est injective.)

    Tout s∈(A⊔B)⊔C est ((p,0),0) (p∈A), ((q,1),0) (q∈B) ou (r,1) (r∈C).  Sous
    K(s)=K(s'), analyse 3×3 : 3 paires HOMOLOGUES (même feuille) → composantes
    égales ; 6 paires HÉTÉROGÈNES → contradiction de marqueur (0≠1 quelque part),
    ex falso."""
    va, vb, vc = _t(a), _t(b), _t(c)
    ABC = _ABC_gauche(a, b, c)
    K = _assoc_graphe(a, b, c, "k")
    vs, vsp = var("s"), var("sp")
    hyp = et(et(appartient(vs, ABC), appartient(vsp, ABC)),
             egal(E.valeur(K, vs), E.valeur(K, vsp)))
    h = N.assume(hyp)
    sin = conjonction_elim_gauche(conjonction_elim_gauche(h))    # s∈ABC
    spin = conjonction_elim_droite(conjonction_elim_gauche(h))   # s'∈ABC
    val_eq = conjonction_elim_droite(h)                          # K(s)=K(s')
    cible = egal(vs, vsp)

    # décompose s et s' en 3 feuilles.  membre_assoc3 réutilise les MÊMES binders u,v,r
    # pour s ET s' → on RENOMME ceux de s' en up,vp,rp pour éviter la capture quand on
    # élimine les témoins de s' alors que le corps de s (avec u,v,r) est encore supposé.
    dec_s = N.modus_ponens(sin, equivalence_avant(membre_assoc3(a, b, c, vs)))
    dec_sp0 = N.modus_ponens(spin, equivalence_avant(membre_assoc3(a, b, c, vsp)))
    sA = dec_s.conclusion.sous[0]; sBC = dec_s.conclusion.sous[1]
    sB = sBC.sous[0]; sC = sBC.sous[1]
    spA0 = dec_sp0.conclusion.sous[0]
    spB0 = dec_sp0.conclusion.sous[1].sous[0]
    spC0 = dec_sp0.conclusion.sous[1].sous[1]
    ren_sp = _ou_congruence(_ren(spA0, "up"),
                            _ou_congruence(_ren(spB0, "vp"), _ren(spC0, "rp")))
    dec_sp = N.modus_ponens(dec_sp0, equivalence_avant(ren_sp))
    spA = dec_sp.conclusion.sous[0]; spBC = dec_sp.conclusion.sous[1]
    spB = spBC.sous[0]; spC = spBC.sous[1]

    # valeurs de K sur chaque feuille (helpers)
    def Kval_at(s_eq_cpl_thm, Kcpl):
        """De (s=cpl) et K(cpl)=val, déduire K(s)=val."""
        cpl = s_eq_cpl_thm.conclusion.termes[1]
        s_side = s_eq_cpl_thm.conclusion.termes[0]
        Ks_Kcpl = N.modus_ponens(s_eq_cpl_thm,
            N.s6(s_side, cpl, "w", egal(E.valeur(K, s_side), E.valeur(K, var("w")))))
        Ks_Kcpl = N.modus_ponens(N.reflexivite(E.valeur(K, s_side)),
                                 equivalence_avant(Ks_Kcpl))   # K(s)=K(cpl)
        return composer_egalites(Ks_Kcpl, Kcpl)

    # ── pour chaque feuille de s : (témoin, K(s)=val, s=cpl) ─────────────────
    # on construit une fonction qui, sous le corps de la feuille, fournit K(s)=val et s=cpl.
    # Chaque feuille : corps, témoin∈·, s=cpl, K(s)=val, et les COMPOSANTES explicites
    #   (on garde les variables-témoins, JAMAIS extraites du terme couple qui est une paire).
    def leaf_A(vp_name, s_var):
        vp = var(vp_name)
        val = E.couple(vp, ZERO)                         # (p,0)
        cpl = E.couple(val, ZERO)                        # ((p,0),0)
        body = et(appartient(vp, va), egal(s_var, cpl))
        h = N.assume(body)
        p_in = conjonction_elim_gauche(h)
        s_eq = conjonction_elim_droite(h)
        Kcpl = N.modus_ponens(p_in, N.loi_deduction(appartient(vp, va),
            assoc_graphe_valeur_A(a, b, c, vp)))         # K(((p,0),0))=(p,0)
        Ks = Kval_at(s_eq, Kcpl)                         # K(s)=(p,0)
        return dict(body=body, s_eq=s_eq, Ks=Ks, val=val, cpl=cpl, w=vp,
                    kind='A', outer_mark=ZERO, inner=None, inner_mark=None)

    def leaf_B(vq_name, s_var):
        vq = var(vq_name)
        innerv = E.couple(vq, ZERO)                      # (q,0)
        val = E.couple(innerv, UN)                       # ((q,0),1)
        cpl = E.couple(E.couple(vq, UN), ZERO)           # ((q,1),0)
        body = et(appartient(vq, vb), egal(s_var, cpl))
        h = N.assume(body)
        q_in = conjonction_elim_gauche(h)
        s_eq = conjonction_elim_droite(h)
        Kcpl = N.modus_ponens(q_in, N.loi_deduction(appartient(vq, vb),
            assoc_graphe_valeur_B(a, b, c, vq)))         # K(((q,1),0))=((q,0),1)
        Ks = Kval_at(s_eq, Kcpl)                         # K(s)=((q,0),1)
        return dict(body=body, s_eq=s_eq, Ks=Ks, val=val, cpl=cpl, w=vq,
                    kind='B', outer_mark=UN, inner=innerv, inner_mark=ZERO)

    def leaf_C(vr_name, s_var):
        vr = var(vr_name)
        innerv = E.couple(vr, UN)                        # (r,1)
        val = E.couple(innerv, UN)                       # ((r,1),1)
        cpl = E.couple(vr, UN)                           # (r,1)
        body = et(appartient(vr, vc), egal(s_var, cpl))
        h = N.assume(body)
        r_in = conjonction_elim_gauche(h)
        s_eq = conjonction_elim_droite(h)
        Kcpl = N.modus_ponens(r_in, N.loi_deduction(appartient(vr, vc),
            assoc_graphe_valeur_C(a, b, c, vr)))         # K((r,1))=((r,1),1)
        Ks = Kval_at(s_eq, Kcpl)                         # K(s)=((r,1),1)
        return dict(body=body, s_eq=s_eq, Ks=Ks, val=val, cpl=cpl, w=vr,
                    kind='C', outer_mark=UN, inner=innerv, inner_mark=UN)

    # noms de témoins distincts pour s (p,q,r) et s' (pp,qq,rr)
    nP = sA.lieur; nQ = sB.lieur; nR = sC.lieur
    nPp = spA.lieur; nQp = spB.lieur; nRp = spC.lieur

    def make_branch(leaf_s, leaf_sp):
        """corps_s ⇒ (corps_sp ⇒ s=s'),  via K(s)=val_s, K(s')=val_sp, K(s)=K(s')."""
        val_s, val_sp = leaf_s['val'], leaf_sp['val']
        val_eq2 = composer_egalites(
            N.modus_ponens(leaf_s['Ks'], symetrie(E.valeur(K, vs), val_s)),
            composer_egalites(val_eq, leaf_sp['Ks']))    # val_s = val_sp
        ks, ksp = leaf_s['kind'], leaf_sp['kind']
        if ks == ksp:
            inner = _homologue_conclusion(leaf_s, leaf_sp, val_eq2, vs, vsp)
        else:
            inner = _heterogene_conclusion(leaf_s, leaf_sp, val_eq2, cible)
        return N.loi_deduction(leaf_s['body'], N.loi_deduction(leaf_sp['body'], inner))

    # assemble : cas(dec_s, [for s in A,B,C: existe_elim over s-witness of
    #            cas(dec_sp, [existe_elim over sp-witness of branch])])
    def s_branch(ks):
        # construire le corps de s pour la feuille ks et, dedans, faire le cas sur s'
        if ks == 'A':
            leaf_s = leaf_A(nP, vs); wit_s = nP
        elif ks == 'B':
            leaf_s = leaf_B(nQ, vs); wit_s = nQ
        else:
            leaf_s = leaf_C(nR, vs); wit_s = nR
        body_s = leaf_s['body']

        def sp_branch(ksp):
            if ksp == 'A':
                leaf_sp = leaf_A(nPp, vsp); wit_sp = nPp
            elif ksp == 'B':
                leaf_sp = leaf_B(nQp, vsp); wit_sp = nQp
            else:
                leaf_sp = leaf_C(nRp, vsp); wit_sp = nRp
            br = make_branch(leaf_s, leaf_sp)   # body_s ⇒ (body_sp ⇒ s=s')
            return wit_sp, br

        wpA, brA = sp_branch('A')
        wpB, brB = sp_branch('B')
        wpC, brC = sp_branch('C')
        h_bs = N.assume(body_s)
        innerA = N.modus_ponens(h_bs, brA)   # body_spA ⇒ cible
        innerB = N.modus_ponens(h_bs, brB)
        innerC = N.modus_ponens(h_bs, brC)
        eA = existe_elimination(innerA, wpA)
        eB = existe_elimination(innerB, wpB)
        eC = existe_elimination(innerC, wpC)
        eBC = N.loi_deduction(spBC, cas(N.assume(spBC), eB, eC))
        s_eq_sp = cas(dec_sp, eA, eBC)       # cible (under body_s assumed)
        return wit_s, N.loi_deduction(body_s, s_eq_sp)

    wsA, sbA = s_branch('A')
    wsB, sbB = s_branch('B')
    wsC, sbC = s_branch('C')
    eA = existe_elimination(sbA, wsA)
    eB = existe_elimination(sbB, wsB)
    eC = existe_elimination(sbC, wsC)
    eBC = N.loi_deduction(sBC, cas(N.assume(sBC), eB, eC))
    s_eq_sp = cas(dec_s, eA, eBC)
    inner = N.loi_deduction(hyp, s_eq_sp)
    return N.generalisation("s", N.generalisation("sp", inner))


def _homologue_conclusion(leaf_s, leaf_sp, val_eq2, vs, vsp):
    """Paire homologue (même feuille) : val_s=val_sp → composantes égales → s=s'.

      A : (w,0) vs (w',0)          → w=w' → ((w,0),0)=((w',0),0)=s' → s=s'
      B : ((w,0),1) vs ((w',0),1)  → (w,0)=(w',0) → w=w' → ((w,1),0)=… → s=s'
      C : ((w,1),1) vs ((w',1),1)  → (w,1)=(w',1) → w=w' → (w,1)=… → s=s'
    Toutes les composantes sont DONNÉES (témoins w des dicts), jamais extraites du
    terme couple (qui est une paire {{·},{·,·}})."""
    kind = leaf_s['kind']
    w, wp = leaf_s['w'], leaf_sp['w']
    s_eq, sp_eq = leaf_s['s_eq'], leaf_sp['s_eq']
    cpl_sp = leaf_sp['cpl']                       # s' = cpl_sp
    if kind == 'A':
        # val_s=(w,0), val_sp=(w',0)
        comps = N.modus_ponens(val_eq2, couple_egal_implique_composantes(w, ZERO, wp, ZERO))
        w_eq = conjonction_elim_gauche(comps)     # w=w'
        # cpl = ((w,0),0) ; rebuild via w=w'
        cpl_eq = N.modus_ponens(w_eq, congruence_terme(w, wp,
            E.couple(E.couple(var("w0"), ZERO), ZERO), "w0"))   # ((w,0),0)=((w',0),0)
    elif kind == 'B':
        inner_s, inner_sp = leaf_s['inner'], leaf_sp['inner']   # (w,0), (w',0)
        comps1 = N.modus_ponens(val_eq2, couple_egal_implique_composantes(
            inner_s, UN, inner_sp, UN))
        inner_eq = conjonction_elim_gauche(comps1)             # (w,0)=(w',0)
        comps2 = N.modus_ponens(inner_eq, couple_egal_implique_composantes(w, ZERO, wp, ZERO))
        w_eq = conjonction_elim_gauche(comps2)                 # w=w'
        cpl_eq = N.modus_ponens(w_eq, congruence_terme(w, wp,
            E.couple(E.couple(var("w0"), UN), ZERO), "w0"))    # ((w,1),0)=((w',1),0)
    else:  # 'C'
        inner_s, inner_sp = leaf_s['inner'], leaf_sp['inner']   # (w,1), (w',1)
        comps1 = N.modus_ponens(val_eq2, couple_egal_implique_composantes(
            inner_s, UN, inner_sp, UN))
        inner_eq = conjonction_elim_gauche(comps1)             # (w,1)=(w',1)
        comps2 = N.modus_ponens(inner_eq, couple_egal_implique_composantes(w, UN, wp, UN))
        w_eq = conjonction_elim_gauche(comps2)                 # w=w'
        cpl_eq = N.modus_ponens(w_eq, congruence_terme(w, wp,
            E.couple(var("w0"), UN), "w0"))                    # (w,1)=(w',1)
    # s = cpl_s = cpl_sp = s'
    s_to_cplsp = composer_egalites(s_eq, cpl_eq)               # s = cpl_sp
    return composer_egalites(s_to_cplsp,
        N.modus_ponens(sp_eq, symetrie(vsp, cpl_sp)))          # s = s'


def _heterogene_conclusion(leaf_s, leaf_sp, val_eq2, cible):
    """Paire hétérogène : val_s=val_sp impossible (marqueur contradictoire) → ex falso.

      A:(·,0)  B:((·,0),1)  C:((·,1),1).  Marqueurs EXTERNES : A=0, B=1, C=1.
      • A vs B/C (et symétriques) : marqueur externe 0≠1 → ex falso.
      • B vs C : externes égaux (1) ; marqueur INTERNE 2ᵉ comp : B=0, C=1 → ex falso."""
    ks, ksp = leaf_s['kind'], leaf_sp['kind']
    if leaf_s['outer_mark'] != leaf_sp['outer_mark']:
        # val_s=(X,m), val_sp=(X',m') avec m≠m' ; X=val sans le marqueur externe
        m_s, m_sp = leaf_s['outer_mark'], leaf_sp['outer_mark']
        X_s = leaf_s['inner'] if leaf_s['inner'] is not None else leaf_s['w']
        X_sp = leaf_sp['inner'] if leaf_sp['inner'] is not None else leaf_sp['w']
        comps = N.modus_ponens(val_eq2,
            couple_egal_implique_composantes(X_s, m_s, X_sp, m_sp))
        mk_eq = conjonction_elim_droite(comps)          # m_s = m_sp  (0=1 ou 1=0)
        return _ex_falso(mk_eq, _marker_neq(m_s, m_sp), cible)
    else:
        # B vs C : val_s=((·,j),1), val_sp=((·,j'),1) ; comparer le marqueur interne j
        inner_s, inner_sp = leaf_s['inner'], leaf_sp['inner']   # (·,j), (·,j')
        comps1 = N.modus_ponens(val_eq2, couple_egal_implique_composantes(
            inner_s, UN, inner_sp, UN))
        inner_eq = conjonction_elim_gauche(comps1)             # (·,j)=(·,j')
        j_s, j_sp = leaf_s['inner_mark'], leaf_sp['inner_mark']
        comps2 = N.modus_ponens(inner_eq, couple_egal_implique_composantes(
            leaf_s['w'], j_s, leaf_sp['w'], j_sp))
        jk_eq = conjonction_elim_droite(comps2)                # j=j'  (0=1 ou 1=0)
        return _ex_falso(jk_eq, _marker_neq(j_s, j_sp), cible)


def _marker_neq(m_s, m_sp):
    """⊢ ¬(m_s = m_sp) pour {m_s,m_sp}={0,1}."""
    if m_s == ZERO and m_sp == UN:
        return vide_distinct_singleton()        # ¬(0=1)
    if m_s == UN and m_sp == ZERO:
        return _neg_un_egal_zero()              # ¬(1=0)
    raise ValueError("marqueurs non contradictoires")


# ═══════════════════════════════════════════════════════════════════════════════
# PALIER 5 : image(K, (A⊔B)⊔C) = A⊔(B⊔C)   (surjectivité, 3 antécédents)
# ═══════════════════════════════════════════════════════════════════════════════
def _couple_dans_K(a, b, c, t0, vz, z_eq_Tt0, t0_in_thm):
    """De t0∈(A⊔B)⊔C et z=T[t0], déduire (t0,z)∈K  (via l'axiome du graphe)."""
    ABC = _ABC_gauche(a, b, c)
    T = _assoc_terme("k")
    K = E.graphe_terme(ABC, T, "k")
    ax_K = N.axiome(E.theorie_graphe_terme(ABC, T, "k", "yb", "zz"),
                    E.axiome_graphe_terme(ABC, T, "k", "yb", "zz"))
    cpl_z = E.couple(t0, vz)
    car_z = instancie(ax_K, cpl_z)
    gbody_k = et(et(egal(cpl_z, E.couple(var("k"), var("yb"))),
                    appartient(var("k"), ABC)), egal(var("yb"), T))
    body_k0 = subst_f(t0, "k", gbody_k)
    wit_yb = conjonction_intro(conjonction_intro(N.reflexivite(cpl_z), t0_in_thm), z_eq_Tt0)
    ex_yb = N.modus_ponens(wit_yb, N.s5(body_k0, vz, "yb"))
    ex_kyb = N.modus_ponens(ex_yb, N.s5(existe("yb", gbody_k), t0, "k"))
    return N.modus_ponens(ex_kyb, equivalence_arriere(car_z))      # (t0,z)∈K


def assoc_graphe_image(a="A", b="B", c="C"):
    """⊢ image(K, (A⊔B)⊔C) = A⊔(B⊔C).   (la réassociation est surjective.)

    z∈K⟨(A⊔B)⊔C⟩ ⇔ (∃t)(t∈(A⊔B)⊔C et z=T[t]).
    ⇒ : t feuille A/B/C → z=K(t) feuille (u,0)/((v,0),1)/((w,1),1) ∈ A⊔(B⊔C).
    ⇐ : z∈A⊔(B⊔C) feuille → antécédent dans (A⊔B)⊔C, K(antécédent)=z."""
    from tactiques_abrege_quantif import alpha_existe as _ax
    va, vb, vc = _t(a), _t(b), _t(c)
    ABC = _ABC_gauche(a, b, c)        # (A⊔B)⊔C
    ABCd = _ABC_droite(a, b, c)       # A⊔(B⊔C)
    BC = somme_disjointe(vb, vc)      # B⊔C
    T = _assoc_terme("k")
    K = E.graphe_terme(ABC, T, "k")
    vz = var("z")
    ax_img = N.axiome(E.theorie_ensembles(), E.AXIOME_IMAGE)
    img_car0 = instancie(instancie(instancie(ax_img, K), ABC), vz)
    inner_x = et(appartient(var("x"), ABC), appartient(E.couple(var("x"), vz), K))
    ren = _ax("x", "t", inner_x)
    img_car = equivalence_transitivite(img_car0, ren)   # z∈K⟨ABC⟩ ⇔ (∃t)(t∈ABC et (t,z)∈K)
    vt = var("t")

    # ── ⇒ : z∈K⟨ABC⟩ ⇒ z∈A⊔(B⊔C) ────────────────────────────────────────────
    bodyR = et(appartient(vt, ABC), appartient(E.couple(vt, vz), K))
    hbR = N.assume(bodyR)
    t_in = conjonction_elim_gauche(hbR)        # t∈ABC
    cpl_in = conjonction_elim_droite(hbR)      # (t,z)∈K
    mem = membre_graphe_terme(ABC, T, "t", "m", "k", "yb")   # ((t,m)∈K)⇔(t∈ABC et m=T[t])
    mem_z = instancie(N.generalisation("m", mem), vz)
    z_eq_Tt = conjonction_elim_droite(N.modus_ponens(cpl_in, equivalence_avant(mem_z)))  # z=T[t]
    dec_t = N.modus_ponens(t_in, equivalence_avant(membre_assoc3(a, b, c, vt)))
    tA = dec_t.conclusion.sous[0]; tBC = dec_t.conclusion.sous[1]
    tB = tBC.sous[0]; tC = tBC.sous[1]
    nP = tA.lieur; nQ = tB.lieur; nR = tC.lieur

    def z_eq_via(t_eq, cpl, val_thm_func, *val_args):
        """z=T[t] ; t=cpl → z=T[cpl]=K(cpl)=val (via assoc_graphe_valeur_*)."""
        # T[t]=T[cpl] par Leibniz
        Tt_Tcpl = N.modus_ponens(t_eq, N.s6(vt, cpl, "w",
            egal(subst_t(vt, "k", T), subst_t(var("w"), "k", T))))
        Tt_Tcpl = N.modus_ponens(N.reflexivite(subst_t(vt, "k", T)),
                                 equivalence_avant(Tt_Tcpl))      # T[t]=T[cpl]
        z_eq_Tcpl = composer_egalites(z_eq_Tt, Tt_Tcpl)           # z=T[cpl]
        return z_eq_Tcpl

    def fwd_A():
        vp = var(nP)
        body = tA.sous[0]                          # p∈A et t=((p,0),0)
        hw = N.assume(body)
        p_in = conjonction_elim_gauche(hw)         # p∈A
        t_eq = conjonction_elim_droite(hw)         # t=((p,0),0)
        cpl = E.couple(E.couple(vp, ZERO), ZERO)
        z_eq_Tcpl = z_eq_via(t_eq, cpl, None)      # z=T[cpl]
        # T[cpl]=K(cpl)=(p,0)  via valeur A : K(((p,0),0))=(p,0) ; and K(cpl)=T[cpl]
        Kcpl = N.modus_ponens(p_in, N.loi_deduction(appartient(vp, va),
            assoc_graphe_valeur_A(a, b, c, vp)))   # K(cpl)=(p,0)
        cpl_in = N.modus_ponens(p_in, _injA_cpl(a, b, c, vp))   # ((p,0),0)∈ABC
        KT = N.modus_ponens(cpl_in, N.loi_deduction(appartient(cpl, ABC),
            _assoc_graphe_valeur_t(a, b, c, cpl)))             # K(cpl)=T[cpl]
        Tcpl_K = N.modus_ponens(KT, symetrie(E.valeur(K, cpl), subst_t(cpl, "k", T)))  # T[cpl]=K(cpl)
        z_eq_Kcpl = composer_egalites(z_eq_Tcpl, Tcpl_K)       # z=K(cpl)
        z_eq_val = composer_egalites(z_eq_Kcpl, Kcpl)          # z=(p,0)
        val = E.couple(vp, ZERO)
        # (p,0)∈A⊔(B⊔C) : injection_gauche (copie gauche = A)
        val_in = N.modus_ponens(p_in, injection_gauche_dans_somme(vp, va, BC))  # (p,0)∈A⊔(B⊔C)
        z_in = N.modus_ponens(val_in, equivalence_arriere(N.modus_ponens(
            z_eq_val, N.s6(vz, val, "w", appartient(var("w"), ABCd)))))
        return N.loi_deduction(body, z_in)

    def fwd_B():
        vq = var(nQ)
        body = tB.sous[0]                          # q∈B et t=((q,1),0)
        hw = N.assume(body)
        q_in = conjonction_elim_gauche(hw)
        t_eq = conjonction_elim_droite(hw)
        cpl = E.couple(E.couple(vq, UN), ZERO)
        z_eq_Tcpl = z_eq_via(t_eq, cpl, None)
        Kcpl = N.modus_ponens(q_in, N.loi_deduction(appartient(vq, vb),
            assoc_graphe_valeur_B(a, b, c, vq)))   # K(cpl)=((q,0),1)
        cpl_in = N.modus_ponens(q_in, _injB_cpl(a, b, c, vq))
        KT = N.modus_ponens(cpl_in, N.loi_deduction(appartient(cpl, ABC),
            _assoc_graphe_valeur_t(a, b, c, cpl)))
        Tcpl_K = N.modus_ponens(KT, symetrie(E.valeur(K, cpl), subst_t(cpl, "k", T)))
        z_eq_Kcpl = composer_egalites(z_eq_Tcpl, Tcpl_K)
        z_eq_val = composer_egalites(z_eq_Kcpl, Kcpl)          # z=((q,0),1)
        val = E.couple(E.couple(vq, ZERO), UN)
        # ((q,0),1)∈A⊔(B⊔C) : copie droite = B⊔C, et (q,0)∈B⊔C (injection_gauche de B⊔C)
        q0_in_BC = N.modus_ponens(q_in, injection_gauche_dans_somme(vq, vb, vc))   # (q,0)∈B⊔C
        val_in = N.modus_ponens(q0_in_BC, injection_droite_dans_somme(
            E.couple(vq, ZERO), va, BC))           # ((q,0),1)∈A⊔(B⊔C)
        z_in = N.modus_ponens(val_in, equivalence_arriere(N.modus_ponens(
            z_eq_val, N.s6(vz, val, "w", appartient(var("w"), ABCd)))))
        return N.loi_deduction(body, z_in)

    def fwd_C():
        vr = var(nR)
        body = tC.sous[0]                          # r∈C et t=(r,1)
        hw = N.assume(body)
        r_in = conjonction_elim_gauche(hw)
        t_eq = conjonction_elim_droite(hw)
        cpl = E.couple(vr, UN)
        z_eq_Tcpl = z_eq_via(t_eq, cpl, None)
        Kcpl = N.modus_ponens(r_in, N.loi_deduction(appartient(vr, vc),
            assoc_graphe_valeur_C(a, b, c, vr)))   # K(cpl)=((r,1),1)
        cpl_in = N.modus_ponens(r_in, injection_droite_dans_somme(vr,
            somme_disjointe(va, vb), vc))          # (r,1)∈(A⊔B)⊔C
        KT = N.modus_ponens(cpl_in, N.loi_deduction(appartient(cpl, ABC),
            _assoc_graphe_valeur_t(a, b, c, cpl)))
        Tcpl_K = N.modus_ponens(KT, symetrie(E.valeur(K, cpl), subst_t(cpl, "k", T)))
        z_eq_Kcpl = composer_egalites(z_eq_Tcpl, Tcpl_K)
        z_eq_val = composer_egalites(z_eq_Kcpl, Kcpl)          # z=((r,1),1)
        val = E.couple(E.couple(vr, UN), UN)
        # ((r,1),1)∈A⊔(B⊔C) : copie droite = B⊔C, et (r,1)∈B⊔C (injection_droite de B⊔C)
        r1_in_BC = N.modus_ponens(r_in, injection_droite_dans_somme(vr, vb, vc))   # (r,1)∈B⊔C
        val_in = N.modus_ponens(r1_in_BC, injection_droite_dans_somme(
            E.couple(vr, UN), va, BC))             # ((r,1),1)∈A⊔(B⊔C)
        z_in = N.modus_ponens(val_in, equivalence_arriere(N.modus_ponens(
            z_eq_val, N.s6(vz, val, "w", appartient(var("w"), ABCd)))))
        return N.loi_deduction(body, z_in)

    impA = existe_elimination(fwd_A(), nP)
    impB = existe_elimination(fwd_B(), nQ)
    impC = existe_elimination(fwd_C(), nR)
    impBC = N.loi_deduction(tBC, cas(N.assume(tBC), impB, impC))
    z_in_sum = cas(dec_t, impA, impBC)
    fwd = existe_elimination(N.loi_deduction(bodyR, z_in_sum), "t")
    fwd_full = syllogisme(equivalence_avant(img_car), fwd)   # z∈K⟨ABC⟩ ⇒ z∈A⊔(B⊔C)

    # ── ⇐ : z∈A⊔(B⊔C) ⇒ z∈K⟨ABC⟩ ────────────────────────────────────────────
    # décompose z∈A⊔(B⊔C) en 3 feuilles (mais l' ordre est A externe-gauche,
    #   puis B⊔C externe-droite décomposé en B,C).
    dec_z = N.modus_ponens(N.assume(appartient(vz, ABCd)),
                           equivalence_avant(_membre_droite3(a, b, c, vz)))
    zA = dec_z.conclusion.sous[0]; zBC = dec_z.conclusion.sous[1]
    zB = zBC.sous[0]; zC = zBC.sous[1]
    mP = zA.lieur; mQ = zB.lieur; mR = zC.lieur

    def back_A():
        vp = var(mP)
        body = zA.sous[0]                          # p∈A et z=(p,0)
        hw = N.assume(body)
        p_in = conjonction_elim_gauche(hw)         # p∈A
        z_eq = conjonction_elim_droite(hw)         # z=(p,0)
        t0 = E.couple(E.couple(vp, ZERO), ZERO)    # ((p,0),0)
        t0_in = N.modus_ponens(p_in, _injA_cpl(a, b, c, vp))   # ((p,0),0)∈ABC
        Kt0 = N.modus_ponens(p_in, N.loi_deduction(appartient(vp, va),
            assoc_graphe_valeur_A(a, b, c, vp)))   # K(t0)=(p,0)
        KT = N.modus_ponens(t0_in, N.loi_deduction(appartient(t0, ABC),
            _assoc_graphe_valeur_t(a, b, c, t0)))  # K(t0)=T[t0]
        z_eq_Kt0 = composer_egalites(z_eq, N.modus_ponens(Kt0,
            symetrie(E.valeur(K, t0), E.couple(vp, ZERO))))    # z=K(t0)
        z_eq_Tt0 = composer_egalites(z_eq_Kt0, KT)             # z=T[t0]
        memb = _couple_dans_K(a, b, c, t0, vz, z_eq_Tt0, t0_in)
        wit = conjonction_intro(t0_in, memb)
        ex_t = N.modus_ponens(wit, N.s5(et(appartient(vt, ABC),
            appartient(E.couple(vt, vz), K)), t0, "t"))
        z_in = N.modus_ponens(ex_t, equivalence_arriere(img_car))
        return N.loi_deduction(body, z_in)

    def back_B():
        vq = var(mQ)
        body = zB.sous[0]                          # q∈B et z=((q,0),1)
        hw = N.assume(body)
        q_in = conjonction_elim_gauche(hw)
        z_eq = conjonction_elim_droite(hw)         # z=((q,0),1)
        t0 = E.couple(E.couple(vq, UN), ZERO)      # ((q,1),0)
        t0_in = N.modus_ponens(q_in, _injB_cpl(a, b, c, vq))
        Kt0 = N.modus_ponens(q_in, N.loi_deduction(appartient(vq, vb),
            assoc_graphe_valeur_B(a, b, c, vq)))   # K(t0)=((q,0),1)
        KT = N.modus_ponens(t0_in, N.loi_deduction(appartient(t0, ABC),
            _assoc_graphe_valeur_t(a, b, c, t0)))
        z_eq_Kt0 = composer_egalites(z_eq, N.modus_ponens(Kt0,
            symetrie(E.valeur(K, t0), E.couple(E.couple(vq, ZERO), UN))))   # z=K(t0)
        z_eq_Tt0 = composer_egalites(z_eq_Kt0, KT)
        memb = _couple_dans_K(a, b, c, t0, vz, z_eq_Tt0, t0_in)
        wit = conjonction_intro(t0_in, memb)
        ex_t = N.modus_ponens(wit, N.s5(et(appartient(vt, ABC),
            appartient(E.couple(vt, vz), K)), t0, "t"))
        z_in = N.modus_ponens(ex_t, equivalence_arriere(img_car))
        return N.loi_deduction(body, z_in)

    def back_C():
        vr = var(mR)
        body = zC.sous[0]                          # r∈C et z=((r,1),1)
        hw = N.assume(body)
        r_in = conjonction_elim_gauche(hw)
        z_eq = conjonction_elim_droite(hw)         # z=((r,1),1)
        t0 = E.couple(vr, UN)                       # (r,1)
        t0_in = N.modus_ponens(r_in, injection_droite_dans_somme(vr,
            somme_disjointe(va, vb), vc))           # (r,1)∈ABC
        Kt0 = N.modus_ponens(r_in, N.loi_deduction(appartient(vr, vc),
            assoc_graphe_valeur_C(a, b, c, vr)))    # K(t0)=((r,1),1)
        KT = N.modus_ponens(t0_in, N.loi_deduction(appartient(t0, ABC),
            _assoc_graphe_valeur_t(a, b, c, t0)))
        z_eq_Kt0 = composer_egalites(z_eq, N.modus_ponens(Kt0,
            symetrie(E.valeur(K, t0), E.couple(E.couple(vr, UN), UN))))     # z=K(t0)
        z_eq_Tt0 = composer_egalites(z_eq_Kt0, KT)
        memb = _couple_dans_K(a, b, c, t0, vz, z_eq_Tt0, t0_in)
        wit = conjonction_intro(t0_in, memb)
        ex_t = N.modus_ponens(wit, N.s5(et(appartient(vt, ABC),
            appartient(E.couple(vt, vz), K)), t0, "t"))
        z_in = N.modus_ponens(ex_t, equivalence_arriere(img_car))
        return N.loi_deduction(body, z_in)

    impbA = existe_elimination(back_A(), mP)
    impbB = existe_elimination(back_B(), mQ)
    impbC = existe_elimination(back_C(), mR)
    impbBC = N.loi_deduction(zBC, cas(N.assume(zBC), impbB, impbC))
    z_in_img = cas(dec_z, impbA, impbBC)
    bwd_full = N.loi_deduction(appartient(vz, ABCd), z_in_img)   # z∈A⊔(B⊔C) ⇒ z∈K⟨ABC⟩

    equiv_z = conjonction_intro(fwd_full, bwd_full)
    char_u = N.generalisation("z", equiv_z)
    selfABCd = N.generalisation("z", conjonction_intro(
        a_implique_a(appartient(vz, ABCd)), a_implique_a(appartient(vz, ABCd))))
    from ensembles_theoremes import egalite_par_extension
    return egalite_par_extension(char_u, selfABCd, E.image(K, ABC), ABCd, "z")


# ── helpers d'appartenance pour l'image ───────────────────────────────────────
def _injA_cpl(a, b, c, vp):
    """⊢ (p∈A) ⇒ ((p,0),0)∈(A⊔B)⊔C  (injection feuille A, 2 niveaux gauche)."""
    va, vb, vc = _t(a), _t(b), _t(c)
    AB = somme_disjointe(va, vb)
    h = N.assume(appartient(vp, va))
    p0 = N.modus_ponens(h, injection_gauche_dans_somme(vp, va, vb))        # (p,0)∈A⊔B
    cpl = N.modus_ponens(p0, injection_gauche_dans_somme(E.couple(vp, ZERO), AB, vc))
    return N.loi_deduction(appartient(vp, va), cpl)


def _injB_cpl(a, b, c, vq):
    """⊢ (q∈B) ⇒ ((q,1),0)∈(A⊔B)⊔C  (injection feuille B)."""
    va, vb, vc = _t(a), _t(b), _t(c)
    AB = somme_disjointe(va, vb)
    h = N.assume(appartient(vq, vb))
    q1 = N.modus_ponens(h, injection_droite_dans_somme(vq, va, vb))        # (q,1)∈A⊔B
    cpl = N.modus_ponens(q1, injection_gauche_dans_somme(E.couple(vq, UN), AB, vc))
    return N.loi_deduction(appartient(vq, vb), cpl)


def _membre_droite3(a, b, c, s="s"):
    """⊢ s∈A⊔(B⊔C) ⇔ (dA ou (dB ou dC)),  dA=(∃u)(u∈A et s=(u,0)),
    dB=(∃v)(v∈B et s=((v,0),1)), dC=(∃r)(r∈C et s=((r,1),1)).

    Décomposition externe (A, B⊔C) puis interne (B,C) du membre DROIT A⊔(B⊔C).
    Binders u,v,r : « p »/« q » sont les liants internes de couple_dans_produit_ssi
    (collision si passés comme valeur à injection_*), « w » est le trou de
    congruence_terme — tous évités."""
    from tactiques_abrege_quantif import alpha_existe as _ax
    va, vb, vc = _t(a), _t(b), _t(c)
    vs = _t(s)
    BC = somme_disjointe(vb, vc)
    dA = existe("u", et(appartient(var("u"), va), egal(vs, E.couple(var("u"), ZERO))))
    dB = existe("v", et(appartient(var("v"), vb),
                        egal(vs, E.couple(E.couple(var("v"), ZERO), UN))))
    dC = existe("r", et(appartient(var("r"), vc),
                        egal(vs, E.couple(E.couple(var("r"), UN), UN))))
    RHS = ou(dA, ou(dB, dC))

    ext = membre_somme_caracterise(va, BC, vs)   # s∈A⊔(B⊔C) ⇔ ((∃u)(u∈A et s=(u,0)) ou (∃m)(m∈B⊔C et s=(m,1)))
    rhs_ext = _equiv_rhs(ext.conclusion)
    exA0 = rhs_ext.sous[0]
    exM0 = rhs_ext.sous[1]
    renA = _ren(exA0, "u")
    renM = _ren(exM0, "m")
    ext2 = equivalence_transitivite(ext, _ou_congruence(renA, renM))
    rhs2 = _equiv_rhs(ext2.conclusion)            # ou(dA, exM)
    assert rhs2.sous[0] == dA
    exM = rhs2.sous[1]                            # (∃m)(m∈B⊔C et s=(m,1))
    vm = var("m")
    bodyM = et(appartient(vm, BC), egal(vs, E.couple(vm, UN)))

    # FORWARD
    hM = N.assume(bodyM)
    m_in = conjonction_elim_gauche(hM)
    s_eq_m1 = conjonction_elim_droite(hM)         # s=(m,1)
    inn = membre_somme_caracterise(vb, vc, vm)    # m∈B⊔C ⇔ ((∃v)(v∈B et m=(v,0)) ou (∃r)(r∈C et m=(r,1)))
    dec_m0 = N.modus_ponens(m_in, equivalence_avant(inn))
    exQ0, exR0 = dec_m0.conclusion.sous[0], dec_m0.conclusion.sous[1]
    renQ = _ren(exQ0, "v")
    renR = _ren(exR0, "r")
    dec_m = N.modus_ponens(dec_m0, equivalence_avant(_ou_congruence(renQ, renR)))
    exQ, exR = dec_m.conclusion.sous[0], dec_m.conclusion.sous[1]
    bQ = exQ.sous[0]; bR = exR.sous[0]
    vq, vr = var("v"), var("r")

    def fwd_Q():
        hQ = N.assume(bQ)
        q_in = conjonction_elim_gauche(hQ)
        m_eq = conjonction_elim_droite(hQ)        # m=(v,0)
        s_eq = composer_egalites(s_eq_m1,
            N.modus_ponens(m_eq, congruence_terme(vm, E.couple(vq, ZERO),
                                                  E.couple(var("w"), UN))))   # s=((v,0),1)
        wit = conjonction_intro(q_in, s_eq)
        ex = N.modus_ponens(wit, N.s5(et(appartient(var("v"), vb),
            egal(vs, E.couple(E.couple(var("v"), ZERO), UN))), vq, "v"))
        into_BC = N.modus_ponens(ex, N.s2(dB, dC))                             # (dB ou dC)
        return N.loi_deduction(bQ, _inject_BC(into_BC, dA, dB, dC))

    def fwd_R():
        hR = N.assume(bR)
        r_in = conjonction_elim_gauche(hR)
        m_eq = conjonction_elim_droite(hR)        # m=(r,1)
        s_eq = composer_egalites(s_eq_m1,
            N.modus_ponens(m_eq, congruence_terme(vm, E.couple(vr, UN),
                                                  E.couple(var("w"), UN))))   # s=((r,1),1)
        wit = conjonction_intro(r_in, s_eq)
        ex = N.modus_ponens(wit, N.s5(et(appartient(var("r"), vc),
            egal(vs, E.couple(E.couple(var("r"), UN), UN))), vr, "r"))
        into_BC = N.modus_ponens(N.modus_ponens(ex, N.s2(dC, dB)), N.s3(dC, dB))  # (dB ou dC)
        return N.loi_deduction(bR, _inject_BC(into_BC, dA, dB, dC))

    impQ = existe_elimination(fwd_Q(), "v")
    impR = existe_elimination(fwd_R(), "r")
    body_to_RHS = cas(dec_m, impQ, impR)
    impM = existe_elimination(N.loi_deduction(bodyM, body_to_RHS), "m")
    impA = N.loi_deduction(dA, N.modus_ponens(N.assume(dA), N.s2(dA, ou(dB, dC))))
    disj_ext = rhs2                                  # (dA ou exM)
    fwd_disj = cas(N.assume(disj_ext), impA, impM)
    fwd = syllogisme(equivalence_avant(ext2), N.loi_deduction(disj_ext, fwd_disj))

    # BACKWARD
    def back_A():
        hp = N.assume(et(appartient(var("u"), va), egal(vs, E.couple(var("u"), ZERO))))
        p_in = conjonction_elim_gauche(hp)
        s_eq = conjonction_elim_droite(hp)        # s=(u,0)
        p0_in = N.modus_ponens(p_in, injection_gauche_dans_somme(var("u"), va, BC))  # (u,0)∈A⊔(B⊔C)
        s_in = N.modus_ponens(p0_in, equivalence_arriere(N.modus_ponens(
            s_eq, N.s6(vs, E.couple(var("u"), ZERO), "w", appartient(var("w"), somme_disjointe(va, BC))))))
        return N.loi_deduction(et(appartient(var("u"), va), egal(vs, E.couple(var("u"), ZERO))), s_in)

    def back_B():
        hq = N.assume(et(appartient(var("v"), vb),
                         egal(vs, E.couple(E.couple(var("v"), ZERO), UN))))
        q_in = conjonction_elim_gauche(hq)
        s_eq = conjonction_elim_droite(hq)        # s=((v,0),1)
        q0_BC = N.modus_ponens(q_in, injection_gauche_dans_somme(var("v"), vb, vc))  # (v,0)∈B⊔C
        s_cpl_in = N.modus_ponens(q0_BC, injection_droite_dans_somme(
            E.couple(var("v"), ZERO), va, BC))    # ((v,0),1)∈A⊔(B⊔C)
        s_in = N.modus_ponens(s_cpl_in, equivalence_arriere(N.modus_ponens(
            s_eq, N.s6(vs, E.couple(E.couple(var("v"), ZERO), UN), "w",
                       appartient(var("w"), somme_disjointe(va, BC))))))
        return N.loi_deduction(et(appartient(var("v"), vb),
            egal(vs, E.couple(E.couple(var("v"), ZERO), UN))), s_in)

    def back_C():
        hr = N.assume(et(appartient(var("r"), vc),
                         egal(vs, E.couple(E.couple(var("r"), UN), UN))))
        r_in = conjonction_elim_gauche(hr)
        s_eq = conjonction_elim_droite(hr)        # s=((r,1),1)
        r1_BC = N.modus_ponens(r_in, injection_droite_dans_somme(var("r"), vb, vc))  # (r,1)∈B⊔C
        s_cpl_in = N.modus_ponens(r1_BC, injection_droite_dans_somme(
            E.couple(var("r"), UN), va, BC))      # ((r,1),1)∈A⊔(B⊔C)
        s_in = N.modus_ponens(s_cpl_in, equivalence_arriere(N.modus_ponens(
            s_eq, N.s6(vs, E.couple(E.couple(var("r"), UN), UN), "w",
                       appartient(var("w"), somme_disjointe(va, BC))))))
        return N.loi_deduction(et(appartient(var("r"), vc),
            egal(vs, E.couple(E.couple(var("r"), UN), UN))), s_in)

    impbA = existe_elimination(back_A(), "u")
    impbB = existe_elimination(back_B(), "v")
    impbC = existe_elimination(back_C(), "r")
    impbBC = N.loi_deduction(ou(dB, dC), cas(N.assume(ou(dB, dC)), impbB, impbC))
    bwd = N.loi_deduction(RHS, cas(N.assume(RHS), impbA, impbBC))
    return conjonction_intro(fwd, bwd)


# ═══════════════════════════════════════════════════════════════════════════════
# PALIER 6 : est_bijection_de(K, (A⊔B)⊔C, A⊔(B⊔C))  puis  Eq((A⊔B)⊔C, A⊔(B⊔C))
# ═══════════════════════════════════════════════════════════════════════════════
def _corps_pourtout(concl):
    return concl.sous[0].sous[0].sous[0]


def _renomme_injective(c3):
    """⊢ injective_dans(K,(A⊔B)⊔C) [liants s,sp]  →  forme défaut u,up."""
    from tactiques_abrege_quantif import alpha_pour_tout, congruence_pour_tout
    R_outer = _corps_pourtout(c3.conclusion)
    ren_outer = alpha_pour_tout("s", "u", R_outer)
    step1 = N.modus_ponens(c3, equivalence_avant(ren_outer))
    Rin = _corps_pourtout(step1.conclusion)
    body2 = _corps_pourtout(Rin)
    ren_inner = alpha_pour_tout("sp", "up", body2)
    cong = congruence_pour_tout(ren_inner, "u")
    return N.modus_ponens(step1, equivalence_avant(cong))


def assoc_est_bijection(a="A", b="B", c="C"):
    """⊢ est_bijection_de(K, (A⊔B)⊔C, A⊔(B⊔C)).   (la réassociation est une bijection.)"""
    c1 = assoc_graphe_fonctionnel(a, b, c)                  # K fonctionnel
    c2 = assoc_graphe_domaine(a, b, c)                      # dom K = (A⊔B)⊔C
    c3 = _renomme_injective(assoc_graphe_injective(a, b, c))  # inj K (liants u,up)
    c4 = assoc_graphe_image(a, b, c)                       # image K = A⊔(B⊔C)
    return conjonction_intro(conjonction_intro(c1, c2), conjonction_intro(c3, c4))


def eq_somme_associatif(a="A", b="B", c="C"):
    """⊢ Eq((A⊔B)⊔C, A⊔(B⊔C)).   (ASSOCIATIVITÉ de la somme à équipotence près, §III.3.3.)"""
    from ensembles_cardinaux import est_bijection_de
    va, vb, vc = _t(a), _t(b), _t(c)
    ABC = _ABC_gauche(a, b, c)
    ABCd = _ABC_droite(a, b, c)
    K = _assoc_graphe(a, b, c, "k")
    bij = assoc_est_bijection(a, b, c)
    return N.modus_ponens(bij, N.s5(est_bijection_de(var("F"), ABC, ABCd), K, "F"))


def somme_cardinale_associative(a="A", b="B", c="C"):
    """⊢ Card((A⊔B)⊔C) = Card(A⊔(B⊔C)).   (associativité a+(b+c)=(a+b)+c, Cor. de Prop. 5.)

    eq_somme_associatif ⊢ Eq((A⊔B)⊔C, A⊔(B⊔C)) ; la Proposition 1 (sens direct,
    version TERME) conclut l'égalité des cardinaux."""
    from ensembles_arith_somme import _prop1_direct_t
    va, vb, vc = _t(a), _t(b), _t(c)
    ABC = _ABC_gauche(a, b, c)
    ABCd = _ABC_droite(a, b, c)
    eq = eq_somme_associatif(a, b, c)              # Eq((A⊔B)⊔C, A⊔(B⊔C))
    prop1 = _prop1_direct_t(ABC, ABCd)             # Eq ⇒ Card=Card
    return N.modus_ponens(eq, prop1)


__all__ = ["assoc_graphe_fonctionnel", "assoc_graphe_domaine",
           "assoc_graphe_valeur_A", "assoc_graphe_valeur_B",
           "assoc_graphe_valeur_C", "membre_assoc3",
           "assoc_graphe_injective", "assoc_graphe_image",
           "assoc_est_bijection", "eq_somme_associatif",
           "somme_cardinale_associative"]
