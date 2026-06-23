"""§III.3.3 — Invariance de la SOMME par équipotence (miroir de eq_produit_invariant,
fondation de l'arithmétique cardinale, E.III.3.3) :

        ⊢ (Eq(A, A₁) et Eq(B, B₁))  ⇒  Eq(A ⊔ B, A₁ ⊔ B₁).

À partir d'une bijection  F : A → A₁  et  G : B → B₁,  on construit la bijection
SOMME  K : A⊔B → A₁⊔B₁  qui agit selon le MARQUEUR de la copie :

        (u, 0) ↦ (F(u), 0)      (u ∈ A,  copie de gauche,  marqueur 0 = ∅)
        (v, 1) ↦ (G(v), 1)      (v ∈ B,  copie de droite,  marqueur 1 = {∅})

Son graphe est  K := graphe_terme(A⊔B, T, "k")  où T est le terme qui, sur un
couple k = (·, ι), garde le marqueur ι = pr₂k et envoie la 1ʳᵉ coordonnée pr₁k
sur F(pr₁k) si ι = 0, sur G(pr₁k) si ι = 1 :

        W(k) := τc( (pr₂k=0 et c=F(pr₁k)) ou (pr₂k=1 et c=G(pr₁k)) )
        T(k) := (W(k), pr₂k).

La DISJONCTION des copies (0 ≠ 1, vide_distinct_singleton) rend W bien défini : sur
A×{0} le 2ᵉ disjoint est faux (pr₂k=1 impossible), donc W(k)=F(pr₁k) ; symétriquement
sur B×{1}.  C'est la machinerie liants a,b du produit (ensembles_produit_equipotence /
ensembles_produit_commute), étendue au cas-marqueur.

ÉTAT — THÉORÈME COMPLET, tout CERTIFIÉ et TESTÉ (test_somme_equipotence.py) :
  • somme_graphe_fonctionnel  (clos)        — K est fonctionnel         (PALIER 1) ;
  • somme_graphe_domaine      (clos)        — dom K = A⊔B               (PALIER 2) ;
  • somme_graphe_valeur       {u∈A⊔B}       — K(u) = T[u]               (PALIER 3a) ;
  • somme_graphe_valeur_gauche {u∈A}        — K((u,0)) = (F(u),0)       (PALIER 3) ;
  • somme_graphe_valeur_droite {v∈B}        — K((v,1)) = (G(v),1)       (PALIER 3) ;
  • somme_graphe_injective    {inj F/A, inj G/B}   — injective_dans(K,A⊔B)  (PALIER 4) ;
  • somme_graphe_image        {F,G func+dom+image}  — image(K,A⊔B)=A₁⊔B₁ (PALIER 5) ;
  • somme_est_bijection       {bij F, bij G}        — est_bijection_de(K,A⊔B,A₁⊔B₁) ;
  • eq_somme_invariant        (clos)        — (Eq(A,A₁) et Eq(B,B₁)) ⇒
                                              Eq(A⊔B, A₁⊔B₁)            (PALIER 6) ;
  • somme_cardinale_bien_definie (clos)     — (Eq(A,A₁) et Eq(B,B₁)) ⇒
                                              Card(A⊔B)=Card(A₁⊔B₁)  (bien-définition).

Le sélecteur W (le cas-marqueur du terme) est rendu par `_selecteur_valeur` :
W[(u,0)]=F(u), W[(v,1)]=G(v) — la garde fausse (0=1, resp. 1=0) du second disjoint
est tuée par 0≠1 (vide_distinct_singleton), c'est la DISJONCTION des copies.
Ponts τc↔τy : la valeur sélectionnée s'écrit τc ; injective/image l'apparient en τy
via `_valeur_cy` (= primitive noyau alpha_tau, reflet de CS1), comme pour le produit.

Les marqueurs 0=∅, 1={∅} sont importés d'ensembles_somme_disjointe (ZERO, UN).
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (Terme, var, egal, et, ou, non, appartient, existe,
                     subst_t, subst_f)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege import a_implique_a, syllogisme
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (conjonction_intro, conjonction_elim_gauche,
                               conjonction_elim_droite, equivalence_avant,
                               equivalence_arriere, equivalence_transitivite,
                               instancie, cas)
from bourbaki.logique.i_4_egalitaires.tactiques_abrege_egalite import (symetrie, composer_egalites, congruence_terme)
from bourbaki.logique.i_3_quantifies.tactiques_abrege_quantif import (existe_elimination, alpha_existe)
from bourbaki.ensembles.fonctions.ii_3_6_fonction_terme.ensembles_fonction_terme import membre_graphe_terme, graphe_terme_fonctionnel
from bourbaki.cardinaux.ensembles_cantor import (graphe_terme_domaine, graphe_terme_valeur)
from bourbaki.ensembles.familles.ii_4_reunion_intersection_familles.ii_4_recollement_somme.ensembles_somme_disjointe import (somme_disjointe, ZERO, UN,
                                       injection_gauche_dans_somme,
                                       injection_droite_dans_somme)
from bourbaki.cardinaux.arithmetique.iii_3_3_produit.ensembles_produit_commute import (_projection_premiere_ab, _projection_seconde_ab)
from bourbaki.cardinaux.ensembles_vide_singleton import vide_distinct_singleton
from bourbaki.ensembles.fonctions.ii_3_4_fonctions_valeur.ensembles_fonctions import valeur_caracterisation
from bourbaki.ensembles.ii_2_couples_produit.ensembles_couples import couple_egal_implique_composantes


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# ── Lemme propositionnel : sous P et ¬Q,  ((P et R) ou (Q et S)) ⇔ R ───────────
def _garde_disjonction(thm_P, thm_nQ, R, S):
    """{Γ⊢P, Δ⊢¬Q} ⊢ ((P et R) ou (Q et S)) ⇔ R.   (la garde vraie P sélectionne R ;
    la garde fausse Q tue le second disjoint — c'est la disjonction des marqueurs.)"""
    P = thm_P.conclusion
    Q = thm_nQ.conclusion.sous[0]
    left, right = et(P, R), et(Q, S)
    disj = ou(left, right)
    # ⇒ : disj ⇒ R  (cas : P et R ⇒ R ; Q et S ⇒ R par ex falso ¬Q)
    brL = N.loi_deduction(left, conjonction_elim_droite(N.assume(left)))
    hR = N.assume(right)
    exf = N.modus_ponens(conjonction_elim_gauche(hR),
                         N.modus_ponens(thm_nQ, N.s2(non(Q), R)))   # R par ex falso
    brR = N.loi_deduction(right, exf)
    fwd = N.loi_deduction(disj, cas(N.assume(disj), brL, brR))
    # ⇐ : R ⇒ disj  (R ⇒ (P et R) ⇒ disj via S2)
    inj = N.modus_ponens(conjonction_intro(thm_P, N.assume(R)), N.s2(left, right))
    bwd = N.loi_deduction(R, inj)
    return conjonction_intro(fwd, bwd)


# ── Le terme somme  T(k) = (W(k), pr₂k)  (liants pr a,b ; valeurs τc ; sélecteur τc) ─
def _sel_terme(f, g, k="k"):
    """W(k) := τc( (pr₂k=0 et c=F(pr₁k)) ou (pr₂k=1 et c=G(pr₁k)) ).

    Sélecteur de la 1ʳᵉ coordonnée selon le marqueur pr₂k : F(pr₁k) si 0, G(pr₁k)
    si 1.  Liants des projections a,b ; liant « c » de la valeur sélectionnée
    (anti-collision avec « y » des axiomes dom/image) ; liant interne « c » du τ
    sélecteur (le même rôle de variable choisie).  La 2ᵉ coordonnée garde le
    marqueur pr₂k."""
    vk = var(k)
    pr1k = E.pr1(vk, "a", "b")
    pr2k = E.pr2(vk, "a", "b")
    Fpr1 = E.valeur(_t(f), pr1k, "c")
    Gpr1 = E.valeur(_t(g), pr1k, "c")
    cond = ou(et(egal(pr2k, ZERO), egal(var("c"), Fpr1)),
              et(egal(pr2k, UN), egal(var("c"), Gpr1)))
    return E.tau("c", cond)


def _somme_terme(f, g, k="k"):
    """T(k) = (W(k), pr₂k)  (image du couple k par la bijection somme K)."""
    vk = var(k)
    return E.couple(_sel_terme(f, g, k), E.pr2(vk, "a", "b"))


def _somme_graphe(f, g, a, b, k="k"):
    """K := graphe_terme(A⊔B, T, "k")  (graphe de la bijection somme)."""
    return E.graphe_terme(somme_disjointe(_t(a), _t(b)), _somme_terme(f, g, k), k)


# ── PALIER 1 : K est fonctionnel  (CERTIFIÉ, clos) ────────────────────────────
def somme_graphe_fonctionnel(f="F", g="G", a="A", b="B"):
    """⊢ K est fonctionnel,  K = graphe de la bijection somme.   (cas C54, clos.)

    Application directe de graphe_terme_fonctionnel au graphe défini par le terme
    T(k)=(W(k),pr₂k) sur l'ensemble A⊔B : le graphe d'une fonction définie par un
    terme est toujours fonctionnel (au plus une valeur par antécédent), E.II.46."""
    AB = somme_disjointe(_t(a), _t(b))
    return graphe_terme_fonctionnel(AB, _somme_terme(f, g, "k"), "k", "t")


# ── PALIER 2 : dom K = A⊔B  (CERTIFIÉ, clos) ──────────────────────────────────
def somme_graphe_domaine(f="F", g="G", a="A", b="B"):
    """⊢ dom(K) = A⊔B.   (la bijection somme est définie sur tout A⊔B ; clos.)

    z∈dom K ⇔ (∃y)((z,y)∈K) ⇔ (∃y)(z∈A⊔B et y=T[z]) ⇔ z∈A⊔B.  Application directe
    de graphe_terme_domaine au terme somme (le liant « c » des valeurs évite la
    collision avec le ∃y du domaine)."""
    AB = somme_disjointe(_t(a), _t(b))
    return graphe_terme_domaine(AB, _somme_terme(f, g, "k"), "k", "y", "z")


# ── Valeur du sélecteur W sur chaque copie : W[(u,0)]=F(u),  W[(v,1)]=G(v) ─────
def _selecteur_valeur(f, g, w, gauche=True):
    """⊢ W[(w, m)] = (F ou G)(w),   m = 0 si gauche sinon 1.   (clos.)

    W[(w,m)] = τc( (pr₂(w,m)=0 et c=F(pr₁(w,m))) ou (pr₂(w,m)=1 et c=G(pr₁(w,m))) ).
    Réécriture pr₁(w,m)→w, pr₂(w,m)→m (projections), puis : sur la copie GAUCHE
    (m=0) la 1ʳᵉ garde 0=0 est vraie et la 2ᵉ garde 0=1 est fausse (0≠1,
    vide_distinct_singleton) ⇒ cond ⇔ (c=F(w)) ⇒ W=F(w) (S7 + tau_egal).
    Symétriquement à droite (m=1), 1≠0."""
    vF, vG, vw = _t(f), _t(g), _t(w)
    m = ZERO if gauche else UN
    pr1c = E.pr1(E.couple(vw, m), "a", "b")
    pr2c = E.pr2(E.couple(vw, m), "a", "b")
    Fpr1 = E.valeur(vF, pr1c, "c")
    Gpr1 = E.valeur(vG, pr1c, "c")
    vc = var("c")
    # cond[(w,m)] avec projections non réduites
    cond0 = ou(et(egal(pr2c, ZERO), egal(vc, Fpr1)),
               et(egal(pr2c, UN), egal(vc, Gpr1)))
    # réécrire pr₁(w,m)=w et pr₂(w,m)=m  (sous le « ou », au niveau formule, S6)
    pr1_eq = _projection_premiere_ab(vw, m, "a", "b")          # pr₁(w,m)=w
    pr2_eq = _projection_seconde_ab(vw, m, "a", "b")           # pr₂(w,m)=m
    Fw = E.valeur(vF, vw, "c")
    Gw = E.valeur(vG, vw, "c")
    # cond1 : cond0 avec pr₁→w  (F(pr₁)→F(w), G(pr₁)→G(w))
    cond1 = ou(et(egal(pr2c, ZERO), egal(vc, Fw)),
               et(egal(pr2c, UN), egal(vc, Gw)))
    # cond2 : cond1 avec pr₂→m
    cond2 = ou(et(egal(m, ZERO), egal(vc, Fw)),
               et(egal(m, UN), egal(vc, Gw)))
    # congruence cond0 ⇔ cond1 (réécriture des deux F(pr₁),G(pr₁) via Leibniz trou w)
    #   on réécrit pr₁c → w dans le terme entier cond0 → cond1
    eq01 = N.modus_ponens(pr1_eq, N.s6(pr1c, vw, "w",
        ou(et(egal(pr2c, ZERO), egal(vc, E.valeur(vF, var("w"), "c"))),
           et(egal(pr2c, UN), egal(vc, E.valeur(vG, var("w"), "c"))))))   # cond0 ⇔ cond1
    eq12 = N.modus_ponens(pr2_eq, N.s6(pr2c, m, "w",
        ou(et(egal(var("w"), ZERO), egal(vc, Fw)),
           et(egal(var("w"), UN), egal(vc, Gw)))))                        # cond1 ⇔ cond2
    cond0_eq_cond2 = equivalence_transitivite(eq01, eq12)                 # cond0 ⇔ cond2
    # cond2 ⇔ (c=valeur)  par garde_disjonction selon le côté
    if gauche:
        # m=0 : P=(0=0) vrai, Q=(0=1) faux
        gd = _garde_disjonction(N.reflexivite(ZERO), vide_distinct_singleton(),
                                egal(vc, Fw), egal(vc, Gw))                # cond2 ⇔ (c=F(w))
        cible_eq = egal(vc, Fw)
        val = Fw
    else:
        # m=1 : P=(1=1) vrai, Q=(1=0) faux  → ¬(1=0) via symétrie de ¬(0=1)
        n10 = _neg_un_egal_zero()
        gd = _garde_disjonction(N.reflexivite(UN), n10,
                                egal(vc, Gw), egal(vc, Fw))                # ((1=1 et c=G) ou (1=0 et c=F)) ⇔ (c=G(w))
        # gd a la forme ((1=1 et c=G(w)) ou (1=0 et c=F(w))) ⇔ (c=G(w)) ;
        # mais cond2 = ((1=0 et c=F(w)) ou (1=1 et c=G(w))) — disjonction commutée.
        cible_eq = egal(vc, Gw)
        val = Gw
    chain = equivalence_transitivite(cond0_eq_cond2, gd) if gauche \
            else equivalence_transitivite(cond0_eq_cond2, _ou_commute_gd(gd, cond2))
    # (∀c)(cond0 ⇔ (c=val))  → τc(cond0) = τc(c=val) = val
    gen = N.generalisation("c", chain)
    tau_eq = N.modus_ponens(gen, N.s7(cond0, cible_eq, "c"))   # τc(cond0)=τc(c=val)
    from bourbaki.ensembles.fonctions.hors_ii_3.ii_2_projections.ensembles_projections import tau_egal
    tau_val = N.modus_ponens(
        N.modus_ponens(N.reflexivite(val), N.s5(egal(vc, val), val, "c")),
        N.existe_temoin(egal(vc, val), "c"))                  # τc(c=val)=val
    return composer_egalites(tau_eq, tau_val)                 # W[(w,m)] = val


def _neg_un_egal_zero():
    """⊢ ¬(1 = 0).   (1≠0, par symétrie de l'égalité depuis ¬(0=1).)"""
    n01 = vide_distinct_singleton()                           # ¬(∅={∅}) = ¬(0=1)
    # ¬(1=0) : sous 1=0, symétrie → 0=1, contredit ¬(0=1)
    h = N.assume(egal(UN, ZERO))
    z01 = N.modus_ponens(h, symetrie(UN, ZERO))               # 0=1
    falso = N.modus_ponens(z01, N.modus_ponens(n01, N.s2(non(egal(ZERO, UN)),
                                                         non(egal(UN, ZERO)))))
    return N.modus_ponens(N.loi_deduction(egal(UN, ZERO), falso),
                          N.s1(non(egal(UN, ZERO))))


def _ou_commute_gd(gd, cond2):
    """De ⊢ (D' ⇔ R), construire ⊢ (D ⇔ R) où D = (D' avec les 2 disjoints commutés).

    gd : ((1=1 et c=G) ou (1=0 et c=F)) ⇔ (c=G)  ;  cond2 = ((1=0 et c=F) ou (1=1 et c=G)).
    On préfixe la commutativité du « ou » : cond2 ⇔ gd-gauche, puis transitivité."""
    from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import comm_ou
    gd_gauche = gd.conclusion.sous[0].sous[0].sous[0]   # récupère D' (membre gauche de l'équiv)
    # comm_ou(P,Q) ⊢ (P ou Q) ⇔ (Q ou P) ; cond2 = (P ou Q), D' = (Q ou P)
    P = cond2.sous[0]   # 1ᵉʳ disjoint de cond2 = (1=0 et c=F)
    Q = cond2.sous[1]   # 2ᵉ disjoint = (1=1 et c=G)
    cm = comm_ou(P, Q)                                  # (P ou Q) ⇔ (Q ou P) = cond2 ⇔ D'
    return equivalence_transitivite(cm, gd)             # cond2 ⇔ (c=G)


# ── PALIER 3a : K(u) = T[u]  pour u∈A⊔B  (CERTIFIÉ, hyp u∈A⊔B) ────────────────
def somme_graphe_valeur(f="F", g="G", a="A", b="B", u="u"):
    """{u ∈ A⊔B} ⊢ K(u) = T[u].   (la valeur de la fonction somme sur un élément.)

    Application directe de graphe_terme_valeur au terme somme : (u,T[u])∈K donne
    u dans le domaine ; valeur_caracterisation (C46, sous « K fonctionnel »
    déchargé) donne T[u]=K(u) ; symétrie conclut.  T[u]=(W[u],pr₂u)."""
    AB = somme_disjointe(_t(a), _t(b))
    return graphe_terme_valeur(AB, _somme_terme(f, g, "k"), u, "k", "y")


# ── Valeur de K en un couple CONCRET (terme) : K(cpl) = T[cpl] ────────────────
def _somme_graphe_valeur_t(f, g, a, b, cpl):
    """{cpl ∈ A⊔B} ⊢ K(cpl) = T[cpl],  cpl un TERME (couple concret).

    (cpl,T[cpl])∈K directement via l'axiome du graphe (témoins k:=cpl, yb:=T[cpl]),
    puis valeur_caracterisation (C46, sous « K fonctionnel » déchargé par le palier
    1) donne T[cpl]=K(cpl) ; symétrie conclut.  Term-tolérant (cpl quelconque)."""
    va, vb = _t(a), _t(b)
    AB = somme_disjointe(va, vb)
    T = _somme_terme(f, g, "k")
    K = E.graphe_terme(AB, T, "k")
    Tcpl = subst_t(cpl, "k", T)                              # T[cpl]
    # (cpl, T[cpl]) ∈ K  via l'axiome du graphe
    ax_K = N.axiome(E.theorie_graphe_terme(AB, T, "k", "yb", "zz"),
                    E.axiome_graphe_terme(AB, T, "k", "yb", "zz"))   # (∀zz)(zz∈K ⇔ (∃k)(∃yb)body)
    paire_cpl = E.couple(cpl, Tcpl)                          # (cpl, T[cpl])
    car = instancie(ax_K, paire_cpl)                        # (cpl,T[cpl])∈K ⇔ (∃k)(∃yb)body
    gbody_k = et(et(egal(paire_cpl, E.couple(var("k"), var("yb"))),
                    appartient(var("k"), AB)), egal(var("yb"), T))
    body_k0 = subst_f(cpl, "k", gbody_k)                    # (k|→cpl) body  (libre yb)
    h_in = N.assume(appartient(cpl, AB))
    wit_yb = conjonction_intro(conjonction_intro(N.reflexivite(paire_cpl), h_in),
                               N.reflexivite(Tcpl))
    ex_yb = N.modus_ponens(wit_yb, N.s5(body_k0, Tcpl, "yb"))   # (∃yb)body[k:=cpl]
    ex_kyb = N.modus_ponens(ex_yb, N.s5(existe("yb", gbody_k), cpl, "k"))  # (∃k)(∃yb)body
    cpl_in_K = N.modus_ponens(ex_kyb, equivalence_arriere(car))   # (cpl,T[cpl])∈K   [hyp cpl∈A⊔B]
    # cpl dans le domaine : (∃y)((cpl,y)∈K), témoin y:=T[cpl]
    dom_membre = N.modus_ponens(cpl_in_K,
        N.s5(appartient(E.couple(cpl, var("y")), K), Tcpl, "y"))   # (∃y)((cpl,y)∈K)
    # valeur_caracterisation(K, cpl) : sous {K func, (∃y)…} ⊢ ((cpl,T[cpl])∈K) ⇔ (T[cpl]=K(cpl))
    vc = valeur_caracterisation(K, cpl)                     # y libre
    vc_all = N.generalisation("y", vc)
    vc_Tcpl = instancie(vc_all, Tcpl)                       # ((cpl,T[cpl])∈K) ⇔ (T[cpl]=K(cpl))
    Tcpl_K = N.modus_ponens(cpl_in_K, equivalence_avant(vc_Tcpl))   # T[cpl]=K(cpl)
    K_Tcpl = N.modus_ponens(Tcpl_K, symetrie(Tcpl, E.valeur(K, cpl)))  # K(cpl)=T[cpl]
    # décharger « K fonctionnel » et « (∃y)((cpl,y)∈K) »
    K_Tcpl = N.modus_ponens(somme_graphe_fonctionnel(f, g, a, b),
                            N.loi_deduction(E.est_fonctionnel(K), K_Tcpl))
    K_Tcpl = N.modus_ponens(dom_membre, N.loi_deduction(
        existe("y", appartient(E.couple(cpl, var("y")), K)), K_Tcpl))
    return K_Tcpl                                           # {cpl∈A⊔B} ⊢ K(cpl)=T[cpl]


# ── PALIER 3 : valeur de K sur chaque copie ───────────────────────────────────
def somme_graphe_valeur_gauche(f="F", g="G", a="A", b="B", u="u"):
    """{u ∈ A} ⊢ K((u, 0)) = (F(u), 0).   (la bijection somme sur la copie gauche.)

    (u,0)∈A⊔B (injection_gauche), donc K((u,0))=T[(u,0)] (somme_graphe_valeur) ;
    T[(u,0)]=(W[(u,0)], pr₂(u,0))=(F(u), 0) (sélecteur gauche + projection)."""
    vF, vu = _t(f), _t(u)
    va, vb = _t(a), _t(b)
    cpl = E.couple(vu, ZERO)                                   # (u,0)
    AB = somme_disjointe(va, vb)
    K = _somme_graphe(f, g, a, b, "k")
    T = _somme_terme(f, g, "k")
    Tcpl = subst_t(cpl, "k", T)                               # T[(u,0)] = (W[(u,0)], pr₂(u,0))
    # K((u,0)) = T[(u,0)]   (valeur en couple concret, sous (u,0)∈A⊔B)
    val0 = _somme_graphe_valeur_t(f, g, a, b, cpl)            # {(u,0)∈A⊔B} ⊢ K((u,0))=T[(u,0)]
    in_AB = injection_gauche_dans_somme(vu, va, vb)           # (u∈A) ⇒ (u,0)∈A⊔B
    in_AB = N.modus_ponens(N.assume(appartient(vu, va)), in_AB)   # {u∈A} ⊢ (u,0)∈A⊔B
    Kval = N.modus_ponens(in_AB, N.loi_deduction(appartient(cpl, AB), val0))  # {u∈A} ⊢ K((u,0))=T[(u,0)]
    # T[(u,0)] = (F(u), 0)   :  W[(u,0)]=F(u),  pr₂(u,0)=0
    Wc = subst_t(cpl, "k", _sel_terme(f, g, "k"))            # W[(u,0)]
    pr2c = E.pr2(cpl, "a", "b")                               # pr₂(u,0)
    Fc = E.valeur(vF, vu, "c")                                # F(u) [τc]
    sel = _selecteur_valeur(f, g, vu, gauche=True)           # W[(u,0)] = F(u)
    pr2_eq = _projection_seconde_ab(vu, ZERO, "a", "b")      # pr₂(u,0) = 0
    # (W,pr₂) = (F(u),pr₂)  puis  (F(u),pr₂) = (F(u),0)
    c1 = N.modus_ponens(sel, congruence_terme(Wc, Fc, E.couple(var("w"), pr2c)))
    c2 = N.modus_ponens(pr2_eq, congruence_terme(pr2c, ZERO, E.couple(Fc, var("w"))))
    T_eq = composer_egalites(c1, c2)                         # T[(u,0)] = (F(u),0)
    return composer_egalites(Kval, T_eq)                     # {u∈A} ⊢ K((u,0))=(F(u),0)


def somme_graphe_valeur_droite(f="F", g="G", a="A", b="B", v="v"):
    """{v ∈ B} ⊢ K((v, 1)) = (G(v), 1).   (la bijection somme sur la copie droite.)"""
    vG, vv = _t(g), _t(v)
    va, vb = _t(a), _t(b)
    cpl = E.couple(vv, UN)                                    # (v,1)
    AB = somme_disjointe(va, vb)
    T = _somme_terme(f, g, "k")
    Tcpl = subst_t(cpl, "k", T)
    val0 = _somme_graphe_valeur_t(f, g, a, b, cpl)          # {(v,1)∈A⊔B} ⊢ K((v,1))=T[(v,1)]
    in_AB = injection_droite_dans_somme(vv, va, vb)          # (v∈B) ⇒ (v,1)∈A⊔B
    in_AB = N.modus_ponens(N.assume(appartient(vv, vb)), in_AB)
    Kval = N.modus_ponens(in_AB, N.loi_deduction(appartient(cpl, AB), val0))
    Wc = subst_t(cpl, "k", _sel_terme(f, g, "k"))
    pr2c = E.pr2(cpl, "a", "b")
    Gc = E.valeur(vG, vv, "c")
    sel = _selecteur_valeur(f, g, vv, gauche=False)          # W[(v,1)] = G(v)
    pr2_eq = _projection_seconde_ab(vv, UN, "a", "b")        # pr₂(v,1) = 1
    c1 = N.modus_ponens(sel, congruence_terme(Wc, Gc, E.couple(var("w"), pr2c)))
    c2 = N.modus_ponens(pr2_eq, congruence_terme(pr2c, UN, E.couple(Gc, var("w"))))
    T_eq = composer_egalites(c1, c2)                         # T[(v,1)] = (G(v),1)
    return composer_egalites(Kval, T_eq)


# ── PALIER 4 : injective_dans(K, A⊔B)  (sous F, G injectives) ──────────────────
def _ex_falso(thm_a, thm_na, z):
    """Γ⊢A, Δ⊢¬A ⟹ Γ∪Δ⊢Z.   (ex falso : ¬A ⇒ (A ⇒ Z), S2.)"""
    a = thm_a.conclusion
    return N.modus_ponens(thm_a, N.modus_ponens(thm_na, N.s2(non(a), z)))


def somme_graphe_injective(f="F", g="G", a="A", b="B"):
    """{F injective sur A, G injective sur B} ⊢ injective_dans(K, A⊔B).

    Tout u∈A⊔B est (p,0) avec p∈A ou (q,1) avec q∈B (membre_somme_caracterise).
    Sous K(u)=K(u'), cas-analyse 2×2 :
      • même copie GAUCHE : K((p,0))=(F(p),0), K((p',0))=(F(p'),0) ⇒ F(p)=F(p')
        ⇒ p=p' (F inj/A) ⇒ (p,0)=(p',0), soit u=u' ;
      • même copie DROITE : symétrique (G inj/B) ;
      • copies DIFFÉRENTES : K(u)=(·,0)=(·,1)=K(u') ⇒ 0=1 (couple_egal) —
        CONTRADICTION (0≠1, vide_distinct_singleton), ex falso ⇒ u=u'.
    """
    vF, vG = _t(f), _t(g)
    va, vb = _t(a), _t(b)
    AB = somme_disjointe(va, vb)
    K = _somme_graphe(f, g, a, b, "k")
    # élément liants « s », « sp » (≠ u,v internes de membre_somme_caracterise,
    # ≠ p,q,pp,qp témoins, ≠ a,b,c,w,k,yb des termes)
    vu, vup = var("s"), var("sp")

    hyp = et(et(appartient(vu, AB), appartient(vup, AB)),
             egal(E.valeur(K, vu), E.valeur(K, vup)))
    h = N.assume(hyp)
    uinAB = conjonction_elim_gauche(conjonction_elim_gauche(h))     # s∈A⊔B
    upinAB = conjonction_elim_droite(conjonction_elim_gauche(h))    # s'∈A⊔B
    val_eq = conjonction_elim_droite(h)                            # K(s)=K(s')
    cible = egal(vu, vup)

    from bourbaki.ensembles.familles.ii_4_reunion_intersection_familles.ii_4_recollement_somme.ensembles_somme_disjointe import membre_somme_caracterise
    from bourbaki.ensembles.familles.ii_4_reunion_intersection_familles.ii_4_recollement_somme.ensembles_somme_disjointe import _ou_congruence
    from bourbaki.logique.i_3_quantifies.tactiques_abrege_quantif import alpha_existe as _ax
    # décomposition de s : (∃p)(p∈A et s=(p,0)) ou (∃q)(q∈B et s=(q,1))  (renommer u→p, v→q)
    dec_u0 = N.modus_ponens(uinAB, equivalence_avant(membre_somme_caracterise(a, b, vu)))
    # décomposition de s' avec témoins DISTINCTS pp, qp (≠ p,q de s)
    dec_up0 = N.modus_ponens(upinAB, equivalence_avant(membre_somme_caracterise(a, b, vup)))
    exA_u0, exB_u0 = dec_u0.conclusion.sous[0], dec_u0.conclusion.sous[1]
    exA_up0, exB_up0 = dec_up0.conclusion.sous[0], dec_up0.conclusion.sous[1]
    # renommer les binders en témoins DISTINCTS multi-caractères (≠ p,q,u,v,a,b,c,w
    # internes des machineries produit/somme/couple) : m1,m2 (côté s) ; m3,m4 (côté s')
    renA_u = _ax(exA_u0.lieur, "m1", exA_u0.sous[0])         # (∃u)bodyA ⇔ (∃m1)bodyA'
    renB_u = _ax(exB_u0.lieur, "m2", exB_u0.sous[0])
    renA_up = _ax(exA_up0.lieur, "m3", exA_up0.sous[0])
    renB_up = _ax(exB_up0.lieur, "m4", exB_up0.sous[0])
    dec_u = N.modus_ponens(dec_u0, equivalence_avant(_ou_congruence(renA_u, renB_u)))
    dec_up = N.modus_ponens(dec_up0, equivalence_avant(_ou_congruence(renA_up, renB_up)))
    exA_u, exB_u = dec_u.conclusion.sous[0], dec_u.conclusion.sous[1]
    exA_up, exB_up = dec_up.conclusion.sous[0], dec_up.conclusion.sous[1]
    nA_u, bA_u = exA_u.lieur, exA_u.sous[0]      # p ; (p∈A et s=(p,0))
    nB_u, bB_u = exB_u.lieur, exB_u.sous[0]      # q ; (q∈B et s=(q,1))
    nA_up, bA_up = exA_up.lieur, exA_up.sous[0]  # pp
    nB_up, bB_up = exB_up.lieur, exB_up.sous[0]  # qp

    def Kval_at(u_eq_cpl_thm, mk_value_lemma, witness, marker, fn_label):
        """De (u=(w,m)) et le lemme K((w,m))=(fn(w),m), déduire K(u)=(fn(w),m)."""
        cpl = u_eq_cpl_thm.conclusion.termes[1]      # (witness, marker)
        u_side = u_eq_cpl_thm.conclusion.termes[0]   # u ou u'
        Kcpl = mk_value_lemma                        # K(cpl)=(fn(witness),marker)
        # K(u)=K(cpl) (Leibniz u=cpl), puis compose
        Ku_Kcpl = N.modus_ponens(u_eq_cpl_thm,
            N.s6(u_side, cpl, "w", egal(E.valeur(K, u_side), E.valeur(K, var("w")))))
        Ku_Kcpl = N.modus_ponens(N.reflexivite(E.valeur(K, u_side)),
                                 equivalence_avant(Ku_Kcpl))   # K(u)=K(cpl)
        return composer_egalites(Ku_Kcpl, Kcpl)      # K(u)=(fn(witness),marker)

    # valeurs sur chaque copie (instanciées aux témoins)
    vp, vq, vpp, vqp = var(nA_u), var(nB_u), var(nA_up), var(nB_up)
    Fp = E.valeur(vF, vp, "c"); Fpp = E.valeur(vF, vpp, "c")
    Gq = E.valeur(vG, vq, "c"); Gqp = E.valeur(vG, vqp, "c")

    # ── BRANCHE u dans la copie GAUCHE (témoin p, p∈A, u=(p,0)) ────────────────
    def branch_uA():
        hpA = N.assume(bA_u)
        pinA = conjonction_elim_gauche(hpA)               # p∈A
        u_eq = conjonction_elim_droite(hpA)               # u=(p,0)
        Klu = somme_graphe_valeur_gauche(f, g, a, b, vp)  # {p∈A} ⊢ K((p,0))=(F(p),0)
        Klu = N.modus_ponens(pinA, N.loi_deduction(appartient(vp, va), Klu))  # K((p,0))=(F(p),0)
        Ku = Kval_at(u_eq, Klu, vp, ZERO, "F")            # K(u)=(F(p),0)

        # sous-cas u' GAUCHE (p', p'∈A, u'=(p',0))
        def branch_upA():
            hppA = N.assume(bA_up)
            ppinA = conjonction_elim_gauche(hppA)         # p'∈A
            up_eq = conjonction_elim_droite(hppA)         # u'=(p',0)
            Klup = somme_graphe_valeur_gauche(f, g, a, b, vpp)
            Klup = N.modus_ponens(ppinA, N.loi_deduction(appartient(vpp, va), Klup))  # K((p',0))=(F(p'),0)
            Kup = Kval_at(up_eq, Klup, vpp, ZERO, "F")    # K(u')=(F(p'),0)
            # K(u)=K(u') ⇒ (F(p),0)=(F(p'),0) ⇒ F(p)=F(p')
            lhs_eq = composer_egalites(N.modus_ponens(Ku, symetrie(E.valeur(K, vu), E.couple(Fp, ZERO))),
                                       composer_egalites(val_eq, Kup))   # (F(p),0)=(F(p'),0)
            comps = N.modus_ponens(lhs_eq, couple_egal_implique_composantes(Fp, ZERO, Fpp, ZERO))
            F_eq_c = conjonction_elim_gauche(comps)       # F(p)=F(p')  [τc]
            # τc→τy pour injective_dans (forme valeur défaut)
            F_eq = _val_cy_eq(vF, vp, vpp, F_eq_c)        # Fy(p)=Fy(p')
            injF = N.assume(E.injective_dans(vF, va))
            injF_i = instancie(instancie(injF, vp), vpp)
            p_eq = N.modus_ponens(conjonction_intro(conjonction_intro(pinA, ppinA), F_eq), injF_i)  # p=p'
            # u=(p,0)=(p',0)=u'
            cpl_eq = N.modus_ponens(p_eq, congruence_terme(vp, vpp, E.couple(var("w"), ZERO)))  # (p,0)=(p',0)
            u_up = composer_egalites(composer_egalites(u_eq, cpl_eq),
                                     N.modus_ponens(up_eq, symetrie(vup, E.couple(vpp, ZERO))))
            return N.loi_deduction(bA_up, u_up)           # bA_up ⇒ u=u'

        # sous-cas u' DROITE (q', u'=(q',1)) : marqueur 0≠1 → ex falso
        def branch_upB():
            hqpB = N.assume(bB_up)
            up_eq = conjonction_elim_droite(hqpB)         # u'=(q',1)
            qpinB = conjonction_elim_gauche(hqpB)         # q'∈B
            Krup = somme_graphe_valeur_droite(f, g, a, b, vqp)
            Krup = N.modus_ponens(qpinB, N.loi_deduction(appartient(vqp, vb), Krup))  # K((q',1))=(G(q'),1)
            Kup = Kval_at(up_eq, Krup, vqp, UN, "G")      # K(u')=(G(q'),1)
            # (F(p),0)=(G(q'),1) ⇒ 0=1
            lhs_eq = composer_egalites(N.modus_ponens(Ku, symetrie(E.valeur(K, vu), E.couple(Fp, ZERO))),
                                       composer_egalites(val_eq, Kup))   # (F(p),0)=(G(q'),1)
            comps = N.modus_ponens(lhs_eq, couple_egal_implique_composantes(Fp, ZERO, Gqp, UN))
            zero_un = conjonction_elim_droite(comps)      # 0=1
            falso = _ex_falso(zero_un, vide_distinct_singleton(), cible)  # u=u'
            return N.loi_deduction(bB_up, falso)          # bB_up ⇒ u=u'

        impA = existe_elimination(branch_upA(), nA_up)    # exA_up ⇒ u=u'
        impB = existe_elimination(branch_upB(), nB_up)    # exB_up ⇒ u=u'
        inner = cas(dec_up, impA, impB)                   # u=u'
        return N.loi_deduction(bA_u, inner)               # bA_u ⇒ u=u'

    # ── BRANCHE u dans la copie DROITE (témoin q, q∈B, u=(q,1)) ────────────────
    def branch_uB():
        hqB = N.assume(bB_u)
        qinB = conjonction_elim_gauche(hqB)               # q∈B
        u_eq = conjonction_elim_droite(hqB)               # u=(q,1)
        Kru = somme_graphe_valeur_droite(f, g, a, b, vq)
        Kru = N.modus_ponens(qinB, N.loi_deduction(appartient(vq, vb), Kru))  # K((q,1))=(G(q),1)
        Ku = Kval_at(u_eq, Kru, vq, UN, "G")              # K(u)=(G(q),1)

        def branch_upA():
            hppA = N.assume(bA_up)
            ppinA = conjonction_elim_gauche(hppA)
            up_eq = conjonction_elim_droite(hppA)         # u'=(p',0)
            Klup = somme_graphe_valeur_gauche(f, g, a, b, vpp)
            Klup = N.modus_ponens(ppinA, N.loi_deduction(appartient(vpp, va), Klup))
            Kup = Kval_at(up_eq, Klup, vpp, ZERO, "F")    # K(u')=(F(p'),0)
            # (G(q),1)=(F(p'),0) ⇒ 1=0 → ex falso
            lhs_eq = composer_egalites(N.modus_ponens(Ku, symetrie(E.valeur(K, vu), E.couple(Gq, UN))),
                                       composer_egalites(val_eq, Kup))   # (G(q),1)=(F(p'),0)
            comps = N.modus_ponens(lhs_eq, couple_egal_implique_composantes(Gq, UN, Fpp, ZERO))
            un_zero = conjonction_elim_droite(comps)      # 1=0
            falso = _ex_falso(un_zero, _neg_un_egal_zero(), cible)
            return N.loi_deduction(bA_up, falso)

        def branch_upB():
            hqpB = N.assume(bB_up)
            qpinB = conjonction_elim_gauche(hqpB)         # q'∈B
            up_eq = conjonction_elim_droite(hqpB)         # u'=(q',1)
            Krup = somme_graphe_valeur_droite(f, g, a, b, vqp)
            Krup = N.modus_ponens(qpinB, N.loi_deduction(appartient(vqp, vb), Krup))
            Kup = Kval_at(up_eq, Krup, vqp, UN, "G")      # K(u')=(G(q'),1)
            lhs_eq = composer_egalites(N.modus_ponens(Ku, symetrie(E.valeur(K, vu), E.couple(Gq, UN))),
                                       composer_egalites(val_eq, Kup))   # (G(q),1)=(G(q'),1)
            comps = N.modus_ponens(lhs_eq, couple_egal_implique_composantes(Gq, UN, Gqp, UN))
            G_eq_c = conjonction_elim_gauche(comps)       # G(q)=G(q')  [τc]
            G_eq = _val_cy_eq(vG, vq, vqp, G_eq_c)
            injG = N.assume(E.injective_dans(vG, vb))
            injG_i = instancie(instancie(injG, vq), vqp)
            q_eq = N.modus_ponens(conjonction_intro(conjonction_intro(qinB, qpinB), G_eq), injG_i)
            cpl_eq = N.modus_ponens(q_eq, congruence_terme(vq, vqp, E.couple(var("w"), UN)))
            u_up = composer_egalites(composer_egalites(u_eq, cpl_eq),
                                     N.modus_ponens(up_eq, symetrie(vup, E.couple(vqp, UN))))
            return N.loi_deduction(bB_up, u_up)

        impA = existe_elimination(branch_upA(), nA_up)
        impB = existe_elimination(branch_upB(), nB_up)
        inner = cas(dec_up, impA, impB)
        return N.loi_deduction(bB_u, inner)

    impA_u = existe_elimination(branch_uA(), nA_u)        # exA_s ⇒ s=s'
    impB_u = existe_elimination(branch_uB(), nB_u)        # exB_s ⇒ s=s'
    s_eq_sp = cas(dec_u, impA_u, impB_u)                  # s=s'
    inner = N.loi_deduction(hyp, s_eq_sp)
    return N.generalisation("s", N.generalisation("sp", inner))   # injective_dans(K, A⊔B) [liants s,sp]


def _somme_image_backward(f, g, a, b, a1, b1, vz, K, AB, A1B1, T,
                          img_car, hFdom, hGdom, hFimg, hGimg):
    """z∈A₁⊔B₁ ⇒ z∈K⟨AB⟩  (surjectivité, sens réciproque).

    z=(c,0)∈A₁⊔B₁ (c∈A₁=F⟨A⟩) → antécédent a∈A, (a,c)∈F → F(a)=c (F func, a∈dom F) ;
    t:=(a,0)∈A⊔B, K((a,0))=(F(a),0)=(c,0)=z → (t,z)∈K → z∈K⟨AB⟩.  Symétrique à droite."""
    from bourbaki.cardinaux.arithmetique.iii_3_3_produit.ensembles_produit_equipotence import _antecedent_image, _valeur_cy
    from bourbaki.ensembles.familles.ii_4_reunion_intersection_familles.ii_4_recollement_somme.ensembles_somme_disjointe import (membre_somme_caracterise, _ou_congruence,
                                           injection_gauche_dans_somme,
                                           injection_droite_dans_somme)
    from bourbaki.ensembles.fonctions.ii_3_4_fonctions_valeur.ensembles_fonctions import valeur_caracterisation
    from bourbaki.logique.i_3_quantifies.tactiques_abrege_quantif import alpha_existe as _ax
    vF, vG = _t(f), _t(g)
    va, vb, va1, vb1 = _t(a), _t(b), _t(a1), _t(b1)
    # décomposer z∈A₁⊔B₁
    dec_z0 = N.modus_ponens(N.assume(appartient(vz, A1B1)),
                            equivalence_avant(membre_somme_caracterise(a1, b1, vz)))
    exC0, exD0 = dec_z0.conclusion.sous[0], dec_z0.conclusion.sous[1]
    renC = _ax(exC0.lieur, "n1", exC0.sous[0])
    renD = _ax(exD0.lieur, "n2", exD0.sous[0])
    dec_z = N.modus_ponens(dec_z0, equivalence_avant(_ou_congruence(renC, renD)))
    exC, exD = dec_z.conclusion.sous[0], dec_z.conclusion.sous[1]
    nC, bC = exC.lieur, exC.sous[0]        # n1 ; (n1∈A₁ et z=(n1,0))
    nD, bD = exD.lieur, exD.sous[0]        # n2 ; (n2∈B₁ et z=(n2,1))
    vc, vd = var(nC), var(nD)

    def back_copy(fn, witness_set, c_var, marker, body_c, hImg, hdom, val_lemma_maker,
                  inj_into_sum, dom_set, img_axiom_set):
        """copie : c∈img_set, z=(c,marker) ⊢ z∈K⟨AB⟩."""
        hc = N.assume(body_c)
        c_in = conjonction_elim_gauche(hc)         # c∈img_set (=A₁ ou B₁)
        z_eq = conjonction_elim_droite(hc)         # z=(c,marker)
        # c∈img_set=fn⟨dom_set⟩  → antécédent a∈dom_set, (a,c)∈fn
        c_in_img = N.modus_ponens(c_in, equivalence_arriere(N.modus_ponens(
            hImg, N.s6(E.image(fn, dom_set), img_axiom_set, "w", appartient(c_var, var("w"))))))
        # img_axiom_set = A₁(=img) ; on a besoin c∈fn⟨dom_set⟩
        ante = N.modus_ponens(c_in_img, _antecedent_image(fn, dom_set, c_var, "ww"))   # (∃ww)(ww∈dom_set et (ww,c)∈fn)
        body_a = et(appartient(var("ww"), dom_set), appartient(E.couple(var("ww"), c_var), fn))
        ha = N.assume(body_a)
        a_in = conjonction_elim_gauche(ha)         # ww∈dom_set
        ac_in = conjonction_elim_droite(ha)        # (ww,c)∈fn
        va_w = var("ww")
        # fn(ww)=c (fn func, ww∈dom fn)
        a_dom = N.modus_ponens(ac_in, N.s5(appartient(E.couple(va_w, var("y")), fn), c_var, "y"))
        vcF = valeur_caracterisation(fn, va_w)
        vcF_c = instancie(N.generalisation("y", vcF), c_var)   # ((ww,c)∈fn)⇔(c=fn(ww))
        c_eq_fa = N.modus_ponens(ac_in, equivalence_avant(vcF_c))   # c=fn(ww)
        c_eq_fa = N.modus_ponens(N.assume(E.est_fonctionnel(fn)),
            N.loi_deduction(E.est_fonctionnel(fn), c_eq_fa))
        c_eq_fa = N.modus_ponens(a_dom, N.loi_deduction(
            existe("y", appartient(E.couple(va_w, var("y")), fn)), c_eq_fa))   # c=fn(ww)
        fa_eq_c = N.modus_ponens(c_eq_fa, symetrie(c_var, E.valeur(fn, va_w)))  # fn(ww)=c
        # t0=(ww,marker)∈AB
        if marker is ZERO:
            t0_in = N.modus_ponens(a_in, injection_gauche_dans_somme(va_w, va, vb))   # (ww,0)∈AB
        else:
            t0_in = N.modus_ponens(a_in, injection_droite_dans_somme(va_w, va, vb))   # (ww,1)∈AB
        t0 = E.couple(va_w, marker)
        # K(t0)=(fn(ww)[τc],marker)  via val_lemma sous ww∈dom_set
        Kt0 = N.modus_ponens(a_in, N.loi_deduction(appartient(va_w, dom_set),
                                                   val_lemma_maker(va_w)))   # K((ww,m))=(fn(ww)[τc],m)
        # (fn(ww)[τc],m)=(c,m)=z :  fn(ww)[τc]=fn(ww)[τy]=c
        fnc = E.valeur(fn, va_w, "c"); fny = E.valeur(fn, va_w)
        fnc_fny = _valeur_cy(fn, va_w)                          # fn(ww)[τc]=fn(ww)[τy]
        fnc_eq_c = composer_egalites(fnc_fny, fa_eq_c)          # fn(ww)[τc]=c
        Kt0_cm = N.modus_ponens(fnc_eq_c, congruence_terme(fnc, c_var,
                                                           E.couple(var("w"), marker)))   # (fn[τc],m)=(c,m)
        Kt0_eq_z = composer_egalites(composer_egalites(Kt0, Kt0_cm),
                                     N.modus_ponens(z_eq, symetrie(vz, E.couple(c_var, marker))))  # K(t0)=z
        # (t0,z)∈K : z=K(t0) → on construit (t0,z)∈K via membre_graphe_terme ⇐ (t0∈AB et z=T[t0])
        # mais on a K(t0)=T[t0] et z=K(t0) ⇒ z=T[t0]
        Tt0 = subst_t(t0, "k", T)
        # K(t0)=T[t0] (term value), sous t0∈AB
        Kt0_Tt0 = N.modus_ponens(t0_in, N.loi_deduction(appartient(t0, AB),
                                                        _somme_graphe_valeur_t(f, g, a, b, t0)))
        z_eq_Kt0 = N.modus_ponens(Kt0_eq_z, symetrie(E.valeur(K, t0), vz))   # z=K(t0)
        z_eq_Tt0 = composer_egalites(z_eq_Kt0, Kt0_Tt0)        # z=T[t0]
        # (t0,z)∈K  via membre_graphe_terme ⇐
        memb = _couple_dans_K(f, g, a, b, t0, vz, z_eq_Tt0, t0_in)   # (t0,z)∈K
        # z∈K⟨AB⟩  via img_car ⇐ : (∃t)(t∈AB et (t,z)∈K)
        wit = conjonction_intro(t0_in, memb)                  # t0∈AB et (t0,z)∈K
        ex_t = N.modus_ponens(wit, N.s5(et(appartient(var("t"), AB),
                                           appartient(E.couple(var("t"), vz), K)), t0, "t"))
        z_in_img = N.modus_ponens(ex_t, equivalence_arriere(img_car))   # z∈K⟨AB⟩
        # éliminer témoin ww
        return existe_elimination(N.loi_deduction(body_a, z_in_img), "ww"), ante

    # GAUCHE
    inner_imp_L, anteC = back_copy(vF, va1, vc, ZERO, bC, hFimg, hFdom,
                                   lambda w: somme_graphe_valeur_gauche(f, g, a, b, w),
                                   None, va, va1)
    impC = N.loi_deduction(bC, N.modus_ponens(anteC, inner_imp_L))   # bC ⇒ z∈K⟨AB⟩
    impC = existe_elimination(impC, nC)                              # exC ⇒ z∈K⟨AB⟩
    # DROITE
    inner_imp_R, anteD = back_copy(vG, vb1, vd, UN, bD, hGimg, hGdom,
                                   lambda w: somme_graphe_valeur_droite(f, g, a, b, w),
                                   None, vb, vb1)
    impD = N.loi_deduction(bD, N.modus_ponens(anteD, inner_imp_R))
    impD = existe_elimination(impD, nD)
    z_in_img = cas(dec_z, impC, impD)                              # z∈K⟨AB⟩  [sous z∈A₁⊔B₁, hyps]
    return N.loi_deduction(appartient(vz, A1B1), z_in_img)        # z∈A₁⊔B₁ ⇒ z∈K⟨AB⟩


def _couple_dans_K(f, g, a, b, t0, vz, z_eq_Tt0, t0_in_thm):
    """De t0∈AB et z=T[t0], déduire (t0,z)∈K   (via l'axiome du graphe, témoins k:=t0, yb:=z)."""
    va, vb = _t(a), _t(b)
    AB = somme_disjointe(va, vb)
    T = _somme_terme(f, g, "k")
    K = E.graphe_terme(AB, T, "k")
    ax_K = N.axiome(E.theorie_graphe_terme(AB, T, "k", "yb", "zz"),
                    E.axiome_graphe_terme(AB, T, "k", "yb", "zz"))
    cpl_z = E.couple(t0, vz)
    car_z = instancie(ax_K, cpl_z)                                 # (t0,z)∈K ⇔ (∃k)(∃yb)body
    gbody_k = et(et(egal(cpl_z, E.couple(var("k"), var("yb"))),
                    appartient(var("k"), AB)), egal(var("yb"), T))
    body_k0 = subst_f(t0, "k", gbody_k)
    wit_yb = conjonction_intro(conjonction_intro(N.reflexivite(cpl_z), t0_in_thm), z_eq_Tt0)
    ex_yb = N.modus_ponens(wit_yb, N.s5(body_k0, vz, "yb"))
    ex_kyb = N.modus_ponens(ex_yb, N.s5(existe("yb", gbody_k), t0, "k"))
    return N.modus_ponens(ex_kyb, equivalence_arriere(car_z))      # (t0,z)∈K


def _val_cy_eq(fF, t1, t2, eq_c):
    """De ⊢ F(t1)[τc]=F(t2)[τc], déduire ⊢ F(t1)[τy]=F(t2)[τy].   (passage τc→τy.)"""
    from bourbaki.cardinaux.arithmetique.iii_3_3_produit.ensembles_produit_equipotence import _valeur_cy
    Fc1, Fy1 = E.valeur(fF, t1, "c"), E.valeur(fF, t1, "y")
    Fc2 = E.valeur(fF, t2, "c")
    Fy1_Fc1 = N.modus_ponens(_valeur_cy(fF, t1), symetrie(Fc1, Fy1))   # Fy(t1)=Fc(t1)
    return composer_egalites(composer_egalites(Fy1_Fc1, eq_c), _valeur_cy(fF, t2))   # Fy(t1)=Fy(t2)


# ── PALIER 5 : image(K, A⊔B) = A₁⊔B₁  (surjectivité) ──────────────────────────
def somme_graphe_image(f="F", g="G", a="A", b="B", a1="A1", b1="B1"):
    """{F func, dom F=A, F⟨A⟩=A₁, G func, dom G=B, G⟨B⟩=B₁} ⊢ image(K, A⊔B) = A₁⊔B₁.

    z∈K⟨A⊔B⟩ ⇔ (∃t)(t∈A⊔B et (t,z)∈K) ⇔ (∃t)(t∈A⊔B et z=T[t]).
    ⇒ : t=(p,0)∈A⊔B (p∈A) ⇒ z=T[(p,0)]=(F(p),0) avec F(p)∈F⟨A⟩=A₁ ⇒ z∈A₁⊔B₁
        (injection_gauche) ; symétrique pour t=(q,1).
    ⇐ : z=(c,0)∈A₁⊔B₁ (c∈A₁=F⟨A⟩) ⇒ antécédent a∈A, F(a)=c ; t:=(a,0)∈A⊔B,
        K((a,0))=(F(a),0)=(c,0)=z ; symétrique pour z=(d,1)∈B₁ copie."""
    from bourbaki.cardinaux.arithmetique.iii_3_3_produit.ensembles_produit_equipotence import _valeur_dans_image, _antecedent_image
    from bourbaki.ensembles.familles.ii_4_reunion_intersection_familles.ii_4_recollement_somme.ensembles_somme_disjointe import membre_somme_caracterise, _ou_congruence
    from bourbaki.ensembles.fonctions.ii_3_4_fonctions_valeur.ensembles_fonctions import valeur_caracterisation
    from bourbaki.logique.i_3_quantifies.tactiques_abrege_quantif import alpha_existe as _ax
    vF, vG = _t(f), _t(g)
    va, vb, va1, vb1 = _t(a), _t(b), _t(a1), _t(b1)
    AB = somme_disjointe(va, vb)
    A1B1 = somme_disjointe(va1, vb1)
    T = _somme_terme(f, g, "k")
    K = E.graphe_terme(AB, T, "k")
    vz = var("z")
    # caractérisation de l'image (liant t)
    ax_img = N.axiome(E.theorie_ensembles(), E.AXIOME_IMAGE)
    img_car0 = instancie(instancie(instancie(ax_img, K), AB), vz)
    inner_x = et(appartient(var("x"), AB), appartient(E.couple(var("x"), vz), K))
    ren = _ax("x", "t", inner_x)
    img_car = equivalence_transitivite(img_car0, ren)      # z∈K⟨AB⟩ ⇔ (∃t)(t∈AB et (t,z)∈K)
    vt = var("t")
    # hypothèses
    hFdom = N.assume(egal(E.dom(vF), va))
    hGdom = N.assume(egal(E.dom(vG), vb))
    hFimg = N.assume(egal(E.image(vF, va), va1))
    hGimg = N.assume(egal(E.image(vG, vb), vb1))

    # ── ⇒ : z∈K⟨AB⟩ ⇒ z∈A₁⊔B₁ ─────────────────────────────────────────────────
    bodyR = et(appartient(vt, AB), appartient(E.couple(vt, vz), K))
    hbR = N.assume(bodyR)
    t_in = conjonction_elim_gauche(hbR)                    # t∈AB
    cpl_in = conjonction_elim_droite(hbR)                  # (t,z)∈K
    mem = membre_graphe_terme(AB, T, "t", "m", "k", "yb")  # ((t,m)∈K)⇔(t∈AB et m=T[t]) ; coord m≠y
    mem_z = instancie(N.generalisation("m", mem), vz)      # ((t,z)∈K)⇔(t∈AB et z=T[t])
    z_eq_Tt = conjonction_elim_droite(N.modus_ponens(cpl_in, equivalence_avant(mem_z)))  # z=T[t]
    # décomposer t∈AB
    dec_t0 = N.modus_ponens(t_in, equivalence_avant(membre_somme_caracterise(a, b, vt)))
    exA0, exB0 = dec_t0.conclusion.sous[0], dec_t0.conclusion.sous[1]
    renA = _ax(exA0.lieur, "m1", exA0.sous[0])
    renB = _ax(exB0.lieur, "m2", exB0.sous[0])
    dec_t = N.modus_ponens(dec_t0, equivalence_avant(_ou_congruence(renA, renB)))
    exA, exB = dec_t.conclusion.sous[0], dec_t.conclusion.sous[1]
    nA, bA = exA.lieur, exA.sous[0]          # m1 ; (m1∈A et t=(m1,0))
    nB, bB = exB.lieur, exB.sous[0]          # m2 ; (m2∈B et t=(m2,1))
    vp, vq = var(nA), var(nB)

    def fwd_copy(fn, fnG, witness, marker, in_set, img_set, hImg, body_w, val_lemma):
        """copie : témoin w∈in_set, t=(w,marker) ⊢ z∈A₁⊔B₁."""
        hw = N.assume(body_w)
        w_in = conjonction_elim_gauche(hw)                 # w∈in_set
        t_eq = conjonction_elim_droite(hw)                 # t=(w,marker)
        # z=T[t]=T[(w,marker)]=(fn(w)[τc], marker)  via val_lemma sous w∈in_set
        Kval = N.modus_ponens(w_in, N.loi_deduction(appartient(witness, in_set), val_lemma))  # K((w,m))=(fn(w),m)
        # mais on a z=T[t] ; et T[t]=K-value only modulo… on veut z=(fn(w),m).
        # z=T[t] et t=(w,m) ⇒ z=T[(w,m)] ; T[(w,m)] = (fn(w)[τc],m) (par construction du terme)
        Twm = subst_t(E.couple(witness, marker), "k", T)   # T[(w,m)]
        # T[t]=T[(w,m)] via Leibniz t=(w,m)
        Tt_Twm = N.modus_ponens(t_eq, N.s6(vt, E.couple(witness, marker), "w",
                                            egal(subst_t(vt, "k", T), subst_t(var("w"), "k", T))))
        Tt_Twm = N.modus_ponens(N.reflexivite(subst_t(vt, "k", T)), equivalence_avant(Tt_Twm))  # T[t]=T[(w,m)]
        z_eq_Twm = composer_egalites(z_eq_Tt, Tt_Twm)      # z=T[(w,m)]
        # T[(w,m)]=(fn(w)[τc],m)  via sélecteur + projection (réutilise val lemmas) :
        sel = _selecteur_valeur(f, g, witness, gauche=(marker is ZERO))   # W[(w,m)]=fn(w)[τc]
        Wwm = subst_t(E.couple(witness, marker), "k", _sel_terme(f, g, "k"))
        pr2wm = E.pr2(E.couple(witness, marker), "a", "b")
        fnc = E.valeur(fn, witness, "c")
        pr2_eq = _projection_seconde_ab(witness, marker, "a", "b")        # pr₂(w,m)=m
        c1 = N.modus_ponens(sel, congruence_terme(Wwm, fnc, E.couple(var("w"), pr2wm)))
        c2 = N.modus_ponens(pr2_eq, congruence_terme(pr2wm, marker, E.couple(fnc, var("w"))))
        Twm_eq = composer_egalites(c1, c2)                 # T[(w,m)]=(fn(w)[τc],m)
        z_eq_fnwm = composer_egalites(z_eq_Twm, Twm_eq)    # z=(fn(w)[τc],m)
        # fn(w)∈img_set  (τy) : _valeur_dans_image sous {w∈in_set,(∃y)(w,y)∈fn}
        # puis rewrite img(fn,in_set)=img_set
        return hw, w_in, z_eq_fnwm, fnc

    # GAUCHE (marker 0) : t=(m1,0), m1∈A
    def fwd_left():
        val_lemma = somme_graphe_valeur_gauche(f, g, a, b, vp)   # {m1∈A}⊢K((m1,0))=(F(m1),0)
        hw, w_in, z_eq_fnwm, Fpc = fwd_copy(vF, vG, vp, ZERO, va, va1, hFimg, bA, val_lemma)
        # F(m1)∈F⟨A⟩ (τy) sous m1∈A, (∃y)((m1,y)∈F)=m1∈dom F (de dom F=A)
        m1_domF = N.modus_ponens(w_in, equivalence_arriere(N.modus_ponens(
            hFdom, N.s6(E.dom(vF), va, "w", appartient(vp, var("w"))))))
        domF_car = instancie(instancie(N.axiome(E.theorie_ensembles(), E.AXIOME_DOM), vF), vp)
        m1_ex = N.modus_ponens(m1_domF, equivalence_avant(domF_car))   # (∃y)((m1,y)∈F)
        Fm1_img = _valeur_dans_image(vF, vp, va)            # {m1∈A,(∃y)…}⊢F(m1)∈F⟨A⟩  (τy)
        Fm1_img = N.modus_ponens(w_in, N.loi_deduction(appartient(vp, va),
            N.modus_ponens(m1_ex, N.loi_deduction(
                existe("y", appartient(E.couple(vp, var("y")), vF)), Fm1_img))))
        Fm1_inA1 = N.modus_ponens(Fm1_img, equivalence_avant(N.modus_ponens(
            hFimg, N.s6(E.image(vF, va), va1, "w", appartient(E.valeur(vF, vp), var("w"))))))   # F(m1)[τy]∈A₁
        # τy→τc : F(m1)[τc]∈A₁
        Fy1, Fc1 = E.valeur(vF, vp), E.valeur(vF, vp, "c")
        from bourbaki.cardinaux.arithmetique.iii_3_3_produit.ensembles_produit_equipotence import _valeur_cy
        Fy_Fc = N.modus_ponens(_valeur_cy(vF, vp), symetrie(Fc1, Fy1))   # Fy=Fc
        Fc1_inA1 = N.modus_ponens(Fm1_inA1, equivalence_avant(N.modus_ponens(
            Fy_Fc, N.s6(Fy1, Fc1, "w", appartient(var("w"), va1)))))     # F(m1)[τc]∈A₁
        # (F(m1)[τc],0)∈A₁⊔B₁  via injection_gauche
        inj = injection_gauche_dans_somme(Fpc, va1, vb1)    # F(m1)[τc]∈A₁ ⇒ (F(m1),0)∈A₁⊔B₁
        cpl_in_sum = N.modus_ponens(Fc1_inA1, inj)          # (F(m1)[τc],0)∈A₁⊔B₁
        # z=(F(m1)[τc],0) ⇒ z∈A₁⊔B₁
        z_in = N.modus_ponens(cpl_in_sum, equivalence_arriere(N.modus_ponens(
            z_eq_fnwm, N.s6(vz, E.couple(Fpc, ZERO), "w", appartient(var("w"), A1B1)))))
        return N.loi_deduction(bA, z_in)                    # bA ⇒ z∈A₁⊔B₁

    def fwd_right():
        val_lemma = somme_graphe_valeur_droite(f, g, a, b, vq)
        hw, w_in, z_eq_fnwm, Gqc = fwd_copy(vG, vF, vq, UN, vb, vb1, hGimg, bB, val_lemma)
        m2_domG = N.modus_ponens(w_in, equivalence_arriere(N.modus_ponens(
            hGdom, N.s6(E.dom(vG), vb, "w", appartient(vq, var("w"))))))
        domG_car = instancie(instancie(N.axiome(E.theorie_ensembles(), E.AXIOME_DOM), vG), vq)
        m2_ex = N.modus_ponens(m2_domG, equivalence_avant(domG_car))
        Gm2_img = _valeur_dans_image(vG, vq, vb)
        Gm2_img = N.modus_ponens(w_in, N.loi_deduction(appartient(vq, vb),
            N.modus_ponens(m2_ex, N.loi_deduction(
                existe("y", appartient(E.couple(vq, var("y")), vG)), Gm2_img))))
        Gm2_inB1 = N.modus_ponens(Gm2_img, equivalence_avant(N.modus_ponens(
            hGimg, N.s6(E.image(vG, vb), vb1, "w", appartient(E.valeur(vG, vq), var("w"))))))
        Gy1, Gc1 = E.valeur(vG, vq), E.valeur(vG, vq, "c")
        from bourbaki.cardinaux.arithmetique.iii_3_3_produit.ensembles_produit_equipotence import _valeur_cy
        Gy_Gc = N.modus_ponens(_valeur_cy(vG, vq), symetrie(Gc1, Gy1))
        Gc1_inB1 = N.modus_ponens(Gm2_inB1, equivalence_avant(N.modus_ponens(
            Gy_Gc, N.s6(Gy1, Gc1, "w", appartient(var("w"), vb1)))))
        inj = injection_droite_dans_somme(Gqc, va1, vb1)
        cpl_in_sum = N.modus_ponens(Gc1_inB1, inj)
        z_in = N.modus_ponens(cpl_in_sum, equivalence_arriere(N.modus_ponens(
            z_eq_fnwm, N.s6(vz, E.couple(Gqc, UN), "w", appartient(var("w"), A1B1)))))
        return N.loi_deduction(bB, z_in)

    impL = existe_elimination(fwd_left(), nA)
    impR = existe_elimination(fwd_right(), nB)
    z_in_sum = cas(dec_t, impL, impR)                      # z∈A₁⊔B₁  [sous bodyR, hyps]
    fwd = existe_elimination(N.loi_deduction(bodyR, z_in_sum), "t")
    fwd_full = syllogisme(equivalence_avant(img_car), fwd)  # z∈K⟨AB⟩ ⇒ z∈A₁⊔B₁

    # ── ⇐ : z∈A₁⊔B₁ ⇒ z∈K⟨AB⟩ ─────────────────────────────────────────────────
    bwd_full = _somme_image_backward(f, g, a, b, a1, b1, vz, K, AB, A1B1, T,
                                     img_car, hFdom, hGdom, hFimg, hGimg)

    equiv_z = conjonction_intro(fwd_full, bwd_full)
    char_u = N.generalisation("z", equiv_z)
    selfYX = N.generalisation("z", conjonction_intro(
        a_implique_a(appartient(vz, A1B1)), a_implique_a(appartient(vz, A1B1))))
    from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_theoremes import egalite_par_extension
    return egalite_par_extension(char_u, selfYX, E.image(K, AB), A1B1, "z")


# ── PALIER 6 : est_bijection_de(K, A⊔B, A₁⊔B₁) puis Eq(A⊔B, A₁⊔B₁) ────────────
def _corps_pourtout(concl):
    """R tel que concl = pourtout(x, R)  (pourtout(x,R)=¬∃x¬R)."""
    return concl.sous[0].sous[0].sous[0]


def _renomme_injective(c3):
    """⊢ injective_dans(K,A⊔B) [liants s,sp]  →  même avec liants u,up (forme défaut).

    Renomme-α les deux ∀ (s→u puis sp→up) pour aligner sur est_bijection_de."""
    from bourbaki.logique.i_3_quantifies.tactiques_abrege_quantif import alpha_pour_tout, congruence_pour_tout
    R_outer = _corps_pourtout(c3.conclusion)              # (∀sp)body
    ren_outer = alpha_pour_tout("s", "u", R_outer)        # (∀s)R_outer ⇔ (∀u)(u|s)R_outer
    step1 = N.modus_ponens(c3, equivalence_avant(ren_outer))   # (∀u)(∀sp)body'
    Rin = _corps_pourtout(step1.conclusion)               # (∀sp)body' (sous u)
    body2 = _corps_pourtout(Rin)                          # body' (sous sp)
    ren_inner = alpha_pour_tout("sp", "up", body2)        # (∀sp)body2 ⇔ (∀up)…
    cong = congruence_pour_tout(ren_inner, "u")           # (∀u)(∀sp)… ⇔ (∀u)(∀up)…
    return N.modus_ponens(step1, equivalence_avant(cong))  # injective_dans(K,A⊔B) [u,up]


def _cut(thm, pairs):
    """Remplace dans `thm` chaque hypothèse `formule` par les hyps de sa `preuve`."""
    for formule, preuve in pairs:
        thm = N.modus_ponens(preuve, N.loi_deduction(formule, thm))
    return thm


def somme_est_bijection(f="F", g="G", a="A", b="B", a1="A1", b1="B1"):
    """{F bijection A→A₁, G bijection B→B₁} ⊢ est_bijection_de(K, A⊔B, A₁⊔B₁).

    Les 4 conjoints (fonctionnel, domaine, injectif, image) sont fournis par les
    paliers 1/2/4/5 ; on coupe leurs hypothèses (injectivité, fonctionnalité,
    domaines, images de F et G) par les conjoints de est_bijection_de(F,A,A₁) et
    est_bijection_de(G,B,B₁).

    NB : le palier injectif a pour conclusion injective_dans(K,A⊔B) avec liants s,sp
    (≠ u,up internes de membre_somme_caracterise) — α-équivalent à la forme défaut ;
    on l'aligne sur la forme défaut u,up de est_bijection_de via alpha (canon_f)."""
    from bourbaki.cardinaux.ensembles_cardinaux import est_bijection_de
    vF, vG = _t(f), _t(g)
    va, vb, va1, vb1 = _t(a), _t(b), _t(a1), _t(b1)
    AB = somme_disjointe(va, vb)
    A1B1 = somme_disjointe(va1, vb1)
    K = _somme_graphe(f, g, a, b, "k")
    hF = N.assume(est_bijection_de(vF, va, va1))
    hG = N.assume(est_bijection_de(vG, vb, vb1))
    Ffunc = conjonction_elim_gauche(conjonction_elim_gauche(hF))
    Fdom = conjonction_elim_droite(conjonction_elim_gauche(hF))
    Finj = conjonction_elim_gauche(conjonction_elim_droite(hF))
    Fimg = conjonction_elim_droite(conjonction_elim_droite(hF))
    Gfunc = conjonction_elim_gauche(conjonction_elim_gauche(hG))
    Gdom = conjonction_elim_droite(conjonction_elim_gauche(hG))
    Ginj = conjonction_elim_gauche(conjonction_elim_droite(hG))
    Gimg = conjonction_elim_droite(conjonction_elim_droite(hG))
    pFf = (E.est_fonctionnel(vF), Ffunc); pFd = (egal(E.dom(vF), va), Fdom)
    pFi = (E.injective_dans(vF, va), Finj); pFm = (egal(E.image(vF, va), va1), Fimg)
    pGf = (E.est_fonctionnel(vG), Gfunc); pGd = (egal(E.dom(vG), vb), Gdom)
    pGi = (E.injective_dans(vG, vb), Ginj); pGm = (egal(E.image(vG, vb), vb1), Gimg)
    c1 = somme_graphe_fonctionnel(f, g, a, b)                  # K fonctionnel  (clos)
    c2 = somme_graphe_domaine(f, g, a, b)                      # dom K = A⊔B    (clos)
    c3 = _renomme_injective(somme_graphe_injective(f, g, a, b))  # inj K (liants u,up)
    c3 = _cut(c3, [pFi, pGi])
    c4 = _cut(somme_graphe_image(f, g, a, b, a1, b1),
              [pFf, pFd, pFm, pGf, pGd, pGm])                  # image K = A₁⊔B₁
    return conjonction_intro(conjonction_intro(c1, c2), conjonction_intro(c3, c4))


def eq_somme_invariant(f="F", g="G", a="A", b="B", a1="A1", b1="B1"):
    """⊢ (Eq(A,A₁) et Eq(B,B₁)) ⇒ Eq(A⊔B, A₁⊔B₁).   (INVARIANCE DE LA SOMME CARDINALE,
    miroir de eq_produit_invariant, E.III.3.3.)

    Témoin = le graphe somme K ; S5 sur est_bijection_de(F',A⊔B,A₁⊔B₁) donne
    (∃F')bij = Eq(A⊔B, A₁⊔B₁), sous les bijections F:A→A₁, G:B→B₁ extraites de
    Eq(A,A₁), Eq(B,B₁) par élimination des deux témoins existentiels."""
    from bourbaki.cardinaux.ensembles_cardinaux import est_bijection_de, equipotent
    from bourbaki.logique.i_3_quantifies.tactiques_abrege_quantif import alpha_existe as _alpha
    vF, vG = _t(f), _t(g)
    va, vb, va1, vb1 = _t(a), _t(b), _t(a1), _t(b1)
    AB = somme_disjointe(va, vb)
    A1B1 = somme_disjointe(va1, vb1)
    K = _somme_graphe(f, g, a, b, "k")
    bij = somme_est_bijection(f, g, a, b, a1, b1)             # bij(K,A⊔B,A₁⊔B₁)  [hyps bij F, bij G]
    eq_somme = N.modus_ponens(bij, N.s5(est_bijection_de(var("F"), AB, A1B1), K, "F"))  # Eq(A⊔B,A₁⊔B₁)
    # éliminer le témoin G de Eq(B,B₁)
    stepG = N.loi_deduction(est_bijection_de(vG, vb, vb1), eq_somme)
    elimG = existe_elimination(stepG, "G")                    # (∃G)bij(G,B,B₁) ⇒ Eq(A⊔B,A₁⊔B₁)
    alphaG = _alpha("G", "F", est_bijection_de(var("G"), vb, vb1))  # (∃G)bij ⇔ equipotent(B,B₁)
    elimG = syllogisme(equivalence_arriere(alphaG), elimG)   # equipotent(B,B₁) ⇒ Eq(A⊔B,A₁⊔B₁)
    # éliminer le témoin F de Eq(A,A₁)
    stepF = N.loi_deduction(est_bijection_de(vF, va, va1), elimG)
    elimF = existe_elimination(stepF, "F")                    # Eq(A,A₁) ⇒ (Eq(B,B₁) ⇒ Eq(A⊔B,A₁⊔B₁))
    # importation : A⇒(B⇒C) ⟹ (A et B)⇒C
    hab = N.assume(et(equipotent(va, va1), equipotent(vb, vb1)))
    c = N.modus_ponens(conjonction_elim_droite(hab),
                       N.modus_ponens(conjonction_elim_gauche(hab), elimF))
    return N.loi_deduction(et(equipotent(va, va1), equipotent(vb, vb1)), c)


# ── BIEN-DÉFINITION de la somme cardinale binaire (E.III.3.3, Déf. 3) ──────────
def somme_cardinale_bien_definie(a="A", b="B", a1="A1", b1="B1"):
    """⊢ (Eq(A,A₁) et Eq(B,B₁)) ⇒ (Card(A⊔B) = Card(A₁⊔B₁)).

    Conséquence directe de l'invariance (eq_somme_invariant : Eq(A⊔B,A₁⊔B₁)) et de
    la Proposition 1 sens direct (cardinal_egal_si_equipotent : Eq ⇒ Card=Card).
    C'est la BIEN-DÉFINITION de a+b := Card(A⊔B) : la somme cardinale ne dépend que
    des cardinaux Card A, Card B (pas des représentants A, B)."""
    from bourbaki.cardinaux.arithmetique.iii_3_3_produit.ensembles_arith_cardinale import _prop1_direct_t
    va, vb, va1, vb1 = _t(a), _t(b), _t(a1), _t(b1)
    from bourbaki.cardinaux.ensembles_cardinaux import equipotent
    AB = somme_disjointe(va, vb)
    A1B1 = somme_disjointe(va1, vb1)
    hyp = et(equipotent(va, va1), equipotent(vb, vb1))
    eq_inv = eq_somme_invariant(a=a, b=b, a1=a1, b1=b1)      # (Eq(A,A₁)et Eq(B,B₁))⇒Eq(A⊔B,A₁⊔B₁)
    prop1 = _prop1_direct_t(AB, A1B1)                       # Eq(A⊔B,A₁⊔B₁)⇒Card(A⊔B)=Card(A₁⊔B₁)
    return syllogisme(eq_inv, prop1)                        # hyp ⇒ Card(A⊔B)=Card(A₁⊔B₁)


# NB — `somme_disjointe_cardinal` ⊢ Card(A⊔B)=(Card A)+(Card B) (= la forme finale
# « a+b:=Card(A⊔B) bien définie sur les cardinaux représentés par Card A, Card B »)
# est REPORTÉE : elle instancie toute la machinerie de l'image au CARDINAL Card A
# (un τ-terme τ_Z Eq(A,Z)) comme ensemble-cible A₁ ; le liant interne « Z » du
# cardinal entre alors en collision avec les substitutions Leibniz du palier image
# (« mineure ≠ antécédent »).  Le pont est `somme_cardinale_bien_definie` (ci-dessus,
# CLOS) qui établit l'indépendance vis-à-vis des représentants ; le reste est une
# instanciation aux τ-cardinaux à durcir (même verrou « cardinaux-paramètres » que
# pour le produit, cf. note liants A,B d'ensembles_arith_cardinale).


__all__ = ["somme_graphe_fonctionnel", "somme_graphe_domaine",
           "somme_graphe_valeur", "somme_graphe_valeur_gauche",
           "somme_graphe_valeur_droite", "somme_graphe_injective",
           "somme_graphe_image", "somme_est_bijection", "eq_somme_invariant",
           "somme_cardinale_bien_definie"]
