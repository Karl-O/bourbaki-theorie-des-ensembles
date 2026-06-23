"""§III.3.3 — Commutativité de la SOMME disjointe (équipotence) : Eq(A⊔B, B⊔A).

L'application témoin est l'ÉCHANGE DES COPIES  k ↦ (pr₁k, flip(pr₂k))  de A⊔B dans
B⊔A, qui garde la 1ʳᵉ coordonnée (la valeur) et FLIPPE le marqueur :

        (u, 0) ↦ (u, 1)      (u ∈ A,  copie gauche de A⊔B  →  copie droite de B⊔A)
        (v, 1) ↦ (v, 0)      (v ∈ B,  copie droite de A⊔B  →  copie gauche de B⊔A)

car  A⊔B = (A×{0})∪(B×{1})  et  B⊔A = (B×{0})∪(A×{1}) : un u∈A marqué 0 dans A⊔B
devient u∈A marqué 1 dans B⊔A (∈ A×{1}), et symétriquement.  Son graphe est
        K := graphe_terme(A⊔B, (pr₁k, M(k)), "k")
où M(k) = τc( (pr₂k=0 et c=1) ou (pr₂k=1 et c=0) ) FLIPPE le marqueur (0↔1).

MÊME machinerie que ensembles_somme_equipotence (sélecteur τc + garde-disjonction
0≠1), mais le terme est PLUS SIMPLE : la valeur pr₁k est identité (pas de F, G).

ÉTAT — THÉORÈME COMPLET, tout CERTIFIÉ et TESTÉ (test_somme_commute.py) :
  • commute_graphe_fonctionnel  (clos)        — K fonctionnel ;
  • commute_graphe_domaine      (clos)        — dom K = A⊔B ;
  • commute_graphe_valeur_gauche {u∈A}        — K((u,0)) = (u,1) ;
  • commute_graphe_valeur_droite {v∈B}        — K((v,1)) = (v,0) ;
  • commute_graphe_injective    (clos)        — injective_dans(K, A⊔B) ;
  • commute_graphe_image        (clos)        — image(K, A⊔B) = B⊔A ;
  • commute_est_bijection       (clos)        — est_bijection_de(K, A⊔B, B⊔A) ;
  • eq_somme_commute            (clos)        — Eq(A⊔B, B⊔A).
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
from bourbaki.ensembles.fonctions.ii_3_6_fonction_terme.ensembles_fonction_terme import (membre_graphe_terme, graphe_terme_fonctionnel)
from bourbaki.cardinaux.ensembles_cantor import (graphe_terme_domaine, graphe_terme_valeur)
from bourbaki.ensembles.familles.ii_4_reunion_intersection_familles.ii_4_recollement_somme.ensembles_somme_disjointe import (somme_disjointe, ZERO, UN,
                                       injection_gauche_dans_somme,
                                       injection_droite_dans_somme,
                                       membre_somme_caracterise, _ou_congruence)
from bourbaki.cardinaux.arithmetique.ensembles_produit_commute import (_projection_premiere_ab, _projection_seconde_ab)
from bourbaki.cardinaux.ensembles_vide_singleton import vide_distinct_singleton
from bourbaki.ensembles.fonctions.ii_3_4_fonctions_valeur.ensembles_fonctions import valeur_caracterisation
from bourbaki.ensembles.ii_2_couples_produit.ensembles_couples import couple_egal_implique_composantes
from bourbaki.cardinaux.arithmetique.ensembles_somme_equipotence import (_garde_disjonction, _neg_un_egal_zero,
                                         _ou_commute_gd)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# ── Le terme commute  T(k) = (pr₁k, M(k))  (flip du marqueur) ─────────────────
def _flip_terme(k="k"):
    """M(k) := τc( (pr₂k=0 et c=1) ou (pr₂k=1 et c=0) ).   (flip du marqueur 0↔1.)

    Liants des projections a,b ; liant « c » de la valeur sélectionnée (le marqueur
    flippé).  Sur la copie 0 : 1ʳᵉ garde (0=0) vraie, 2ᵉ (0=1) fausse ⇒ M=1.  Sur
    la copie 1 : symétrique, M=0."""
    vk = var(k)
    pr2k = E.pr2(vk, "a", "b")
    cond = ou(et(egal(pr2k, ZERO), egal(var("c"), UN)),
              et(egal(pr2k, UN), egal(var("c"), ZERO)))
    return E.tau("c", cond)


def _commute_terme(f=None, g=None, k="k"):
    """T(k) = (pr₁k, M(k))   (image du couple k par l'échange des copies K)."""
    vk = var(k)
    return E.couple(E.pr1(vk, "a", "b"), _flip_terme(k))


def _commute_graphe(a, b, k="k"):
    """K := graphe_terme(A⊔B, (pr₁k, M(k)), "k")  (graphe de l'échange des copies)."""
    return E.graphe_terme(somme_disjointe(_t(a), _t(b)), _commute_terme(k=k), k)


# ── PALIER 1 : K fonctionnel  (CERTIFIÉ, clos) ────────────────────────────────
def commute_graphe_fonctionnel(a="A", b="B"):
    """⊢ K est fonctionnel,  K = graphe de l'échange des copies.   (cas C54, clos.)"""
    AB = somme_disjointe(_t(a), _t(b))
    return graphe_terme_fonctionnel(AB, _commute_terme(k="k"), "k", "t")


# ── PALIER 2 : dom K = A⊔B  (CERTIFIÉ, clos) ──────────────────────────────────
def commute_graphe_domaine(a="A", b="B"):
    """⊢ dom(K) = A⊔B.   (l'échange est défini sur tout A⊔B ; clos.)"""
    AB = somme_disjointe(_t(a), _t(b))
    return graphe_terme_domaine(AB, _commute_terme(k="k"), "k", "y", "z")


# ── Valeur du sélecteur M sur chaque copie : M[(w,0)]=1,  M[(w,1)]=0 ──────────
def _flip_valeur(w, gauche=True):
    """⊢ M[(w, m)] = (1 si m=0 sinon 0),   m = 0 si gauche sinon 1.   (clos.)

    M[(w,m)] = τc( (pr₂(w,m)=0 et c=1) ou (pr₂(w,m)=1 et c=0) ).  Réécriture
    pr₂(w,m)→m (projection), puis garde-disjonction : sur la copie GAUCHE (m=0) la
    1ʳᵉ garde 0=0 est vraie, la 2ᵉ 0=1 fausse (0≠1) ⇒ cond ⇔ (c=1) ⇒ M=1.
    Symétriquement à droite (m=1) ⇒ M=0."""
    vw = _t(w)
    m = ZERO if gauche else UN
    pr2c = E.pr2(E.couple(vw, m), "a", "b")
    vc = var("c")
    # cond[(w,m)] avec projection non réduite
    cond0 = ou(et(egal(pr2c, ZERO), egal(vc, UN)),
               et(egal(pr2c, UN), egal(vc, ZERO)))
    # réécrire pr₂(w,m)=m  (S6, sous le « ou »)
    pr2_eq = _projection_seconde_ab(vw, m, "a", "b")           # pr₂(w,m)=m
    # cond1 : cond0 avec pr₂→m
    cond1 = ou(et(egal(m, ZERO), egal(vc, UN)),
               et(egal(m, UN), egal(vc, ZERO)))
    eq01 = N.modus_ponens(pr2_eq, N.s6(pr2c, m, "w",
        ou(et(egal(var("w"), ZERO), egal(vc, UN)),
           et(egal(var("w"), UN), egal(vc, ZERO)))))           # cond0 ⇔ cond1
    if gauche:
        # m=0 : P=(0=0) vrai, Q=(0=1) faux  → cond1 ⇔ (c=1)
        gd = _garde_disjonction(N.reflexivite(ZERO), vide_distinct_singleton(),
                                egal(vc, UN), egal(vc, ZERO))   # cond1 ⇔ (c=1)
        chain = equivalence_transitivite(eq01, gd)
        cible_eq = egal(vc, UN)
        val = UN
    else:
        # m=1 : la 1ʳᵉ garde (1=0) fausse, la 2ᵉ (1=1) vraie ; cond1 = ((1=0 et c=1) ou (1=1 et c=0))
        # garde_disjonction veut le disjoint VRAI en tête → on l'applique sur le second
        # ordre ((1=1 et c=0) ou (1=0 et c=1)) puis on commute.
        gd = _garde_disjonction(N.reflexivite(UN), _neg_un_egal_zero(),
                                egal(vc, ZERO), egal(vc, UN))   # ((1=1 et c=0) ou (1=0 et c=1)) ⇔ (c=0)
        chain = equivalence_transitivite(eq01, _ou_commute_gd(gd, cond1))
        cible_eq = egal(vc, ZERO)
        val = ZERO
    # (∀c)(cond0 ⇔ (c=val))  → τc(cond0) = τc(c=val) = val
    gen = N.generalisation("c", chain)
    tau_eq = N.modus_ponens(gen, N.s7(cond0, cible_eq, "c"))   # τc(cond0)=τc(c=val)
    tau_val = N.modus_ponens(
        N.modus_ponens(N.reflexivite(val), N.s5(egal(vc, val), val, "c")),
        N.existe_temoin(egal(vc, val), "c"))                   # τc(c=val)=val
    return composer_egalites(tau_eq, tau_val)                  # M[(w,m)] = val


# ── Valeur de K en un couple CONCRET (terme) : K(cpl) = T[cpl] ────────────────
def _commute_graphe_valeur_t(a, b, cpl):
    """{cpl ∈ A⊔B} ⊢ K(cpl) = T[cpl],  cpl un TERME (couple concret).  Term-tolérant."""
    va, vb = _t(a), _t(b)
    AB = somme_disjointe(va, vb)
    T = _commute_terme(k="k")
    K = E.graphe_terme(AB, T, "k")
    Tcpl = subst_t(cpl, "k", T)                              # T[cpl]
    ax_K = N.axiome(E.theorie_graphe_terme(AB, T, "k", "yb", "zz"),
                    E.axiome_graphe_terme(AB, T, "k", "yb", "zz"))
    paire_cpl = E.couple(cpl, Tcpl)
    car = instancie(ax_K, paire_cpl)
    gbody_k = et(et(egal(paire_cpl, E.couple(var("k"), var("yb"))),
                    appartient(var("k"), AB)), egal(var("yb"), T))
    body_k0 = subst_f(cpl, "k", gbody_k)
    h_in = N.assume(appartient(cpl, AB))
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
    K_Tcpl = N.modus_ponens(commute_graphe_fonctionnel(a, b),
                            N.loi_deduction(E.est_fonctionnel(K), K_Tcpl))
    K_Tcpl = N.modus_ponens(dom_membre, N.loi_deduction(
        existe("y", appartient(E.couple(cpl, var("y")), K)), K_Tcpl))
    return K_Tcpl                                           # {cpl∈A⊔B} ⊢ K(cpl)=T[cpl]


# ── PALIER 3 : valeur de K sur chaque copie ───────────────────────────────────
def commute_graphe_valeur_gauche(a="A", b="B", u="u"):
    """{u ∈ A} ⊢ K((u, 0)) = (u, 1).   (échange de la copie gauche vers droite.)

    (u,0)∈A⊔B (injection_gauche), donc K((u,0))=T[(u,0)] ; T[(u,0)]=(pr₁(u,0),M[(u,0)])
    =(u, 1) (projection + sélecteur gauche)."""
    vu = _t(u)
    va, vb = _t(a), _t(b)
    cpl = E.couple(vu, ZERO)                                   # (u,0)
    AB = somme_disjointe(va, vb)
    T = _commute_terme(k="k")
    val0 = _commute_graphe_valeur_t(a, b, cpl)               # {(u,0)∈A⊔B} ⊢ K((u,0))=T[(u,0)]
    in_AB = injection_gauche_dans_somme(vu, va, vb)           # (u∈A) ⇒ (u,0)∈A⊔B
    in_AB = N.modus_ponens(N.assume(appartient(vu, va)), in_AB)
    Kval = N.modus_ponens(in_AB, N.loi_deduction(appartient(cpl, AB), val0))  # K((u,0))=T[(u,0)]
    # T[(u,0)] = (pr₁(u,0), M[(u,0)]) ;  pr₁(u,0)=u,  M[(u,0)]=1  →  (u,1)
    pr1c = E.pr1(cpl, "a", "b")                               # pr₁(u,0)
    Mc = subst_t(cpl, "k", _flip_terme("k"))                  # M[(u,0)]
    pr1_eq = _projection_premiere_ab(vu, ZERO, "a", "b")      # pr₁(u,0)=u
    sel = _flip_valeur(vu, gauche=True)                       # M[(u,0)]=1
    c1 = N.modus_ponens(pr1_eq, congruence_terme(pr1c, vu, E.couple(var("w"), Mc)))
    c2 = N.modus_ponens(sel, congruence_terme(Mc, UN, E.couple(vu, var("w"))))
    T_eq = composer_egalites(c1, c2)                         # T[(u,0)] = (u,1)
    return composer_egalites(Kval, T_eq)                     # {u∈A} ⊢ K((u,0))=(u,1)


def commute_graphe_valeur_droite(a="A", b="B", v="v"):
    """{v ∈ B} ⊢ K((v, 1)) = (v, 0).   (échange de la copie droite vers gauche.)"""
    vv = _t(v)
    va, vb = _t(a), _t(b)
    cpl = E.couple(vv, UN)                                    # (v,1)
    AB = somme_disjointe(va, vb)
    T = _commute_terme(k="k")
    val0 = _commute_graphe_valeur_t(a, b, cpl)
    in_AB = injection_droite_dans_somme(vv, va, vb)          # (v∈B) ⇒ (v,1)∈A⊔B
    in_AB = N.modus_ponens(N.assume(appartient(vv, vb)), in_AB)
    Kval = N.modus_ponens(in_AB, N.loi_deduction(appartient(cpl, AB), val0))
    pr1c = E.pr1(cpl, "a", "b")
    Mc = subst_t(cpl, "k", _flip_terme("k"))
    pr1_eq = _projection_premiere_ab(vv, UN, "a", "b")       # pr₁(v,1)=v
    sel = _flip_valeur(vv, gauche=False)                     # M[(v,1)]=0
    c1 = N.modus_ponens(pr1_eq, congruence_terme(pr1c, vv, E.couple(var("w"), Mc)))
    c2 = N.modus_ponens(sel, congruence_terme(Mc, ZERO, E.couple(vv, var("w"))))
    T_eq = composer_egalites(c1, c2)                         # T[(v,1)] = (v,0)
    return composer_egalites(Kval, T_eq)


# ── PALIER 4 : injective_dans(K, A⊔B) ─────────────────────────────────────────
def _ex_falso(thm_a, thm_na, z):
    """Γ⊢A, Δ⊢¬A ⟹ Γ∪Δ⊢Z.   (ex falso : ¬A ⇒ (A ⇒ Z), S2.)"""
    a = thm_a.conclusion
    return N.modus_ponens(thm_a, N.modus_ponens(thm_na, N.s2(non(a), z)))


def commute_graphe_injective(a="A", b="B"):
    """⊢ injective_dans(K, A⊔B).   (l'échange des copies est injectif sur A⊔B.)

    Tout s∈A⊔B est (p,0) (p∈A) ou (q,1) (q∈B).  Sous K(s)=K(s'), cas 2×2 :
      • même copie GAUCHE : K((p,0))=(p,1), K((p',0))=(p',1) ⇒ (p,1)=(p',1) ⇒ p=p'
        ⇒ (p,0)=(p',0), soit s=s' ;
      • même copie DROITE : symétrique ;
      • copies DIFFÉRENTES : K(s)=(·,1)=(·,0)=K(s') ⇒ 1=0 — CONTRADICTION, ex falso."""
    va, vb = _t(a), _t(b)
    AB = somme_disjointe(va, vb)
    K = _commute_graphe(a, b, "k")
    vu, vup = var("s"), var("sp")
    hyp = et(et(appartient(vu, AB), appartient(vup, AB)),
             egal(E.valeur(K, vu), E.valeur(K, vup)))
    h = N.assume(hyp)
    uinAB = conjonction_elim_gauche(conjonction_elim_gauche(h))     # s∈A⊔B
    upinAB = conjonction_elim_droite(conjonction_elim_gauche(h))    # s'∈A⊔B
    val_eq = conjonction_elim_droite(h)                            # K(s)=K(s')
    cible = egal(vu, vup)
    from bourbaki.logique.i_3_quantifies.tactiques_abrege_quantif import alpha_existe as _ax
    dec_u0 = N.modus_ponens(uinAB, equivalence_avant(membre_somme_caracterise(a, b, vu)))
    dec_up0 = N.modus_ponens(upinAB, equivalence_avant(membre_somme_caracterise(a, b, vup)))
    exA_u0, exB_u0 = dec_u0.conclusion.sous[0], dec_u0.conclusion.sous[1]
    exA_up0, exB_up0 = dec_up0.conclusion.sous[0], dec_up0.conclusion.sous[1]
    renA_u = _ax(exA_u0.lieur, "m1", exA_u0.sous[0])
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
    vp, vq, vpp, vqp = var(nA_u), var(nB_u), var(nA_up), var(nB_up)

    def Kval_at(u_eq_cpl_thm, Kcpl):
        """De (s=(w,m)) et K((w,m))=val, déduire K(s)=val."""
        cpl = u_eq_cpl_thm.conclusion.termes[1]
        u_side = u_eq_cpl_thm.conclusion.termes[0]
        Ku_Kcpl = N.modus_ponens(u_eq_cpl_thm,
            N.s6(u_side, cpl, "w", egal(E.valeur(K, u_side), E.valeur(K, var("w")))))
        Ku_Kcpl = N.modus_ponens(N.reflexivite(E.valeur(K, u_side)),
                                 equivalence_avant(Ku_Kcpl))   # K(s)=K(cpl)
        return composer_egalites(Ku_Kcpl, Kcpl)

    def branch_uA():
        hpA = N.assume(bA_u)
        pinA = conjonction_elim_gauche(hpA)               # p∈A
        u_eq = conjonction_elim_droite(hpA)               # s=(p,0)
        Klu = commute_graphe_valeur_gauche(a, b, vp)
        Klu = N.modus_ponens(pinA, N.loi_deduction(appartient(vp, va), Klu))  # K((p,0))=(p,1)
        Ku = Kval_at(u_eq, Klu)                           # K(s)=(p,1)

        def branch_upA():
            hppA = N.assume(bA_up)
            ppinA = conjonction_elim_gauche(hppA)         # p'∈A
            up_eq = conjonction_elim_droite(hppA)         # s'=(p',0)
            Klup = commute_graphe_valeur_gauche(a, b, vpp)
            Klup = N.modus_ponens(ppinA, N.loi_deduction(appartient(vpp, va), Klup))  # K((p',0))=(p',1)
            Kup = Kval_at(up_eq, Klup)                    # K(s')=(p',1)
            # (p,1)=(p',1) ⇒ p=p'
            lhs_eq = composer_egalites(N.modus_ponens(Ku, symetrie(E.valeur(K, vu), E.couple(vp, UN))),
                                       composer_egalites(val_eq, Kup))   # (p,1)=(p',1)
            comps = N.modus_ponens(lhs_eq, couple_egal_implique_composantes(vp, UN, vpp, UN))
            p_eq = conjonction_elim_gauche(comps)         # p=p'
            cpl_eq = N.modus_ponens(p_eq, congruence_terme(vp, vpp, E.couple(var("w"), ZERO)))  # (p,0)=(p',0)
            u_up = composer_egalites(composer_egalites(u_eq, cpl_eq),
                                     N.modus_ponens(up_eq, symetrie(vup, E.couple(vpp, ZERO))))
            return N.loi_deduction(bA_up, u_up)

        def branch_upB():
            hqpB = N.assume(bB_up)
            up_eq = conjonction_elim_droite(hqpB)         # s'=(q',1)
            qpinB = conjonction_elim_gauche(hqpB)         # q'∈B
            Krup = commute_graphe_valeur_droite(a, b, vqp)
            Krup = N.modus_ponens(qpinB, N.loi_deduction(appartient(vqp, vb), Krup))  # K((q',1))=(q',0)
            Kup = Kval_at(up_eq, Krup)                    # K(s')=(q',0)
            # (p,1)=(q',0) ⇒ 1=0  → ex falso
            lhs_eq = composer_egalites(N.modus_ponens(Ku, symetrie(E.valeur(K, vu), E.couple(vp, UN))),
                                       composer_egalites(val_eq, Kup))   # (p,1)=(q',0)
            comps = N.modus_ponens(lhs_eq, couple_egal_implique_composantes(vp, UN, vqp, ZERO))
            un_zero = conjonction_elim_droite(comps)      # 1=0
            falso = _ex_falso(un_zero, _neg_un_egal_zero(), cible)
            return N.loi_deduction(bB_up, falso)

        impA = existe_elimination(branch_upA(), nA_up)
        impB = existe_elimination(branch_upB(), nB_up)
        inner = cas(dec_up, impA, impB)
        return N.loi_deduction(bA_u, inner)

    def branch_uB():
        hqB = N.assume(bB_u)
        qinB = conjonction_elim_gauche(hqB)               # q∈B
        u_eq = conjonction_elim_droite(hqB)               # s=(q,1)
        Kru = commute_graphe_valeur_droite(a, b, vq)
        Kru = N.modus_ponens(qinB, N.loi_deduction(appartient(vq, vb), Kru))  # K((q,1))=(q,0)
        Ku = Kval_at(u_eq, Kru)                           # K(s)=(q,0)

        def branch_upA():
            hppA = N.assume(bA_up)
            ppinA = conjonction_elim_gauche(hppA)
            up_eq = conjonction_elim_droite(hppA)         # s'=(p',0)
            Klup = commute_graphe_valeur_gauche(a, b, vpp)
            Klup = N.modus_ponens(ppinA, N.loi_deduction(appartient(vpp, va), Klup))  # K((p',0))=(p',1)
            Kup = Kval_at(up_eq, Klup)                    # K(s')=(p',1)
            # (q,0)=(p',1) ⇒ 0=1 → ex falso
            lhs_eq = composer_egalites(N.modus_ponens(Ku, symetrie(E.valeur(K, vu), E.couple(vq, ZERO))),
                                       composer_egalites(val_eq, Kup))   # (q,0)=(p',1)
            comps = N.modus_ponens(lhs_eq, couple_egal_implique_composantes(vq, ZERO, vpp, UN))
            zero_un = conjonction_elim_droite(comps)      # 0=1
            falso = _ex_falso(zero_un, vide_distinct_singleton(), cible)
            return N.loi_deduction(bA_up, falso)

        def branch_upB():
            hqpB = N.assume(bB_up)
            qpinB = conjonction_elim_gauche(hqpB)         # q'∈B
            up_eq = conjonction_elim_droite(hqpB)         # s'=(q',1)
            Krup = commute_graphe_valeur_droite(a, b, vqp)
            Krup = N.modus_ponens(qpinB, N.loi_deduction(appartient(vqp, vb), Krup))  # K((q',1))=(q',0)
            Kup = Kval_at(up_eq, Krup)                    # K(s')=(q',0)
            # (q,0)=(q',0) ⇒ q=q'
            lhs_eq = composer_egalites(N.modus_ponens(Ku, symetrie(E.valeur(K, vu), E.couple(vq, ZERO))),
                                       composer_egalites(val_eq, Kup))   # (q,0)=(q',0)
            comps = N.modus_ponens(lhs_eq, couple_egal_implique_composantes(vq, ZERO, vqp, ZERO))
            q_eq = conjonction_elim_gauche(comps)         # q=q'
            cpl_eq = N.modus_ponens(q_eq, congruence_terme(vq, vqp, E.couple(var("w"), UN)))
            u_up = composer_egalites(composer_egalites(u_eq, cpl_eq),
                                     N.modus_ponens(up_eq, symetrie(vup, E.couple(vqp, UN))))
            return N.loi_deduction(bB_up, u_up)

        impA = existe_elimination(branch_upA(), nA_up)
        impB = existe_elimination(branch_upB(), nB_up)
        inner = cas(dec_up, impA, impB)
        return N.loi_deduction(bB_u, inner)

    impA_u = existe_elimination(branch_uA(), nA_u)
    impB_u = existe_elimination(branch_uB(), nB_u)
    s_eq_sp = cas(dec_u, impA_u, impB_u)
    inner = N.loi_deduction(hyp, s_eq_sp)
    return N.generalisation("s", N.generalisation("sp", inner))   # injective_dans(K, A⊔B) [s,sp]


# ── PALIER 5 : image(K, A⊔B) = B⊔A  (surjectivité) ────────────────────────────
def _couple_dans_K(a, b, t0, vz, z_eq_Tt0, t0_in_thm):
    """De t0∈AB et z=T[t0], déduire (t0,z)∈K  (via l'axiome du graphe)."""
    va, vb = _t(a), _t(b)
    AB = somme_disjointe(va, vb)
    T = _commute_terme(k="k")
    K = E.graphe_terme(AB, T, "k")
    ax_K = N.axiome(E.theorie_graphe_terme(AB, T, "k", "yb", "zz"),
                    E.axiome_graphe_terme(AB, T, "k", "yb", "zz"))
    cpl_z = E.couple(t0, vz)
    car_z = instancie(ax_K, cpl_z)
    gbody_k = et(et(egal(cpl_z, E.couple(var("k"), var("yb"))),
                    appartient(var("k"), AB)), egal(var("yb"), T))
    body_k0 = subst_f(t0, "k", gbody_k)
    wit_yb = conjonction_intro(conjonction_intro(N.reflexivite(cpl_z), t0_in_thm), z_eq_Tt0)
    ex_yb = N.modus_ponens(wit_yb, N.s5(body_k0, vz, "yb"))
    ex_kyb = N.modus_ponens(ex_yb, N.s5(existe("yb", gbody_k), t0, "k"))
    return N.modus_ponens(ex_kyb, equivalence_arriere(car_z))      # (t0,z)∈K


def commute_graphe_image(a="A", b="B"):
    """⊢ image(K, A⊔B) = B⊔A.   (l'échange des copies est surjectif sur B⊔A.)

    z∈K⟨A⊔B⟩ ⇔ (∃t)(t∈A⊔B et z=T[t]).
    ⇒ : t=(p,0)∈A⊔B (p∈A) ⇒ z=T[(p,0)]=(p,1) ∈ A×{1} ⊆ B⊔A (injection_droite de B⊔A,
        copie droite = A) ; t=(q,1) (q∈B) ⇒ z=(q,0) ∈ B×{0} ⊆ B⊔A (injection_gauche).
    ⇐ : z=(c,0)∈B⊔A (c∈B copie gauche) ⇒ antécédent t₀=(c,1)∈A⊔B, K((c,1))=(c,0)=z ;
        z=(d,1)∈B⊔A (d∈A copie droite) ⇒ antécédent t₀=(d,0)∈A⊔B, K((d,0))=(d,1)=z."""
    from bourbaki.logique.i_3_quantifies.tactiques_abrege_quantif import alpha_existe as _ax
    va, vb = _t(a), _t(b)
    AB = somme_disjointe(va, vb)
    BA = somme_disjointe(vb, va)
    T = _commute_terme(k="k")
    K = E.graphe_terme(AB, T, "k")
    vz = var("z")
    ax_img = N.axiome(E.theorie_ensembles(), E.AXIOME_IMAGE)
    img_car0 = instancie(instancie(instancie(ax_img, K), AB), vz)
    inner_x = et(appartient(var("x"), AB), appartient(E.couple(var("x"), vz), K))
    ren = _ax("x", "t", inner_x)
    img_car = equivalence_transitivite(img_car0, ren)      # z∈K⟨AB⟩ ⇔ (∃t)(t∈AB et (t,z)∈K)
    vt = var("t")

    # ── ⇒ : z∈K⟨AB⟩ ⇒ z∈B⊔A ──────────────────────────────────────────────────
    bodyR = et(appartient(vt, AB), appartient(E.couple(vt, vz), K))
    hbR = N.assume(bodyR)
    t_in = conjonction_elim_gauche(hbR)                    # t∈AB
    cpl_in = conjonction_elim_droite(hbR)                  # (t,z)∈K
    mem = membre_graphe_terme(AB, T, "t", "m", "k", "yb")  # ((t,m)∈K)⇔(t∈AB et m=T[t])
    mem_z = instancie(N.generalisation("m", mem), vz)
    z_eq_Tt = conjonction_elim_droite(N.modus_ponens(cpl_in, equivalence_avant(mem_z)))  # z=T[t]
    dec_t0 = N.modus_ponens(t_in, equivalence_avant(membre_somme_caracterise(a, b, vt)))
    exA0, exB0 = dec_t0.conclusion.sous[0], dec_t0.conclusion.sous[1]
    renA = _ax(exA0.lieur, "m1", exA0.sous[0])
    renB = _ax(exB0.lieur, "m2", exB0.sous[0])
    dec_t = N.modus_ponens(dec_t0, equivalence_avant(_ou_congruence(renA, renB)))
    exA, exB = dec_t.conclusion.sous[0], dec_t.conclusion.sous[1]
    nA, bA = exA.lieur, exA.sous[0]          # m1 ; (m1∈A et t=(m1,0))
    nB, bB = exB.lieur, exB.sous[0]          # m2 ; (m2∈B et t=(m2,1))
    vp, vq = var(nA), var(nB)

    def fwd_left():
        # t=(p,0), p∈A → z=T[t]=K((p,0))=(p,1)∈B⊔A  (copie droite de B⊔A = A)
        hw = N.assume(bA)
        w_in = conjonction_elim_gauche(hw)                 # p∈A
        t_eq = conjonction_elim_droite(hw)                 # t=(p,0)
        cpl = E.couple(vp, ZERO)
        # z=T[t] ; T[t]=T[(p,0)] (Leibniz) ; T[(p,0)]=(p,1) via valeur gauche & somme_graphe_valeur_t
        # plus simple : K((p,0))=(p,1) (commute_graphe_valeur_gauche), et z=T[t], T[t]=K[t]?  Non:
        # on a z=T[t] ; et T[(p,0)]=(p,1) calculé via construction du terme. On réécrit T[t]→T[(p,0)].
        Tcpl = subst_t(cpl, "k", T)
        Tt_Tcpl = N.modus_ponens(t_eq, N.s6(vt, cpl, "w",
                                            egal(subst_t(vt, "k", T), subst_t(var("w"), "k", T))))
        Tt_Tcpl = N.modus_ponens(N.reflexivite(subst_t(vt, "k", T)), equivalence_avant(Tt_Tcpl))  # T[t]=T[(p,0)]
        z_eq_Tcpl = composer_egalites(z_eq_Tt, Tt_Tcpl)    # z=T[(p,0)]
        # T[(p,0)]=(p,1) : (pr₁(p,0), M[(p,0)]) = (p, 1)
        pr1c = E.pr1(cpl, "a", "b")
        Mc = subst_t(cpl, "k", _flip_terme("k"))
        pr1_eq = _projection_premiere_ab(vp, ZERO, "a", "b")
        sel = _flip_valeur(vp, gauche=True)
        c1 = N.modus_ponens(pr1_eq, congruence_terme(pr1c, vp, E.couple(var("w"), Mc)))
        c2 = N.modus_ponens(sel, congruence_terme(Mc, UN, E.couple(vp, var("w"))))
        Tcpl_eq = composer_egalites(c1, c2)                # T[(p,0)]=(p,1)
        z_eq_p1 = composer_egalites(z_eq_Tcpl, Tcpl_eq)    # z=(p,1)
        # (p,1)∈B⊔A  via injection_droite (copie droite de B⊔A est A)
        inj = injection_droite_dans_somme(vp, vb, va)      # (p∈A) ⇒ (p,1)∈B⊔A
        cpl_in_sum = N.modus_ponens(w_in, inj)             # (p,1)∈B⊔A
        z_in = N.modus_ponens(cpl_in_sum, equivalence_arriere(N.modus_ponens(
            z_eq_p1, N.s6(vz, E.couple(vp, UN), "w", appartient(var("w"), BA)))))
        return N.loi_deduction(bA, z_in)                   # bA ⇒ z∈B⊔A

    def fwd_right():
        # t=(q,1), q∈B → z=(q,0)∈B⊔A  (copie gauche de B⊔A = B)
        hw = N.assume(bB)
        w_in = conjonction_elim_gauche(hw)                 # q∈B
        t_eq = conjonction_elim_droite(hw)                 # t=(q,1)
        cpl = E.couple(vq, UN)
        Tcpl = subst_t(cpl, "k", T)
        Tt_Tcpl = N.modus_ponens(t_eq, N.s6(vt, cpl, "w",
                                            egal(subst_t(vt, "k", T), subst_t(var("w"), "k", T))))
        Tt_Tcpl = N.modus_ponens(N.reflexivite(subst_t(vt, "k", T)), equivalence_avant(Tt_Tcpl))
        z_eq_Tcpl = composer_egalites(z_eq_Tt, Tt_Tcpl)    # z=T[(q,1)]
        pr1c = E.pr1(cpl, "a", "b")
        Mc = subst_t(cpl, "k", _flip_terme("k"))
        pr1_eq = _projection_premiere_ab(vq, UN, "a", "b")
        sel = _flip_valeur(vq, gauche=False)
        c1 = N.modus_ponens(pr1_eq, congruence_terme(pr1c, vq, E.couple(var("w"), Mc)))
        c2 = N.modus_ponens(sel, congruence_terme(Mc, ZERO, E.couple(vq, var("w"))))
        Tcpl_eq = composer_egalites(c1, c2)                # T[(q,1)]=(q,0)
        z_eq_q0 = composer_egalites(z_eq_Tcpl, Tcpl_eq)    # z=(q,0)
        inj = injection_gauche_dans_somme(vq, vb, va)      # (q∈B) ⇒ (q,0)∈B⊔A
        cpl_in_sum = N.modus_ponens(w_in, inj)             # (q,0)∈B⊔A
        z_in = N.modus_ponens(cpl_in_sum, equivalence_arriere(N.modus_ponens(
            z_eq_q0, N.s6(vz, E.couple(vq, ZERO), "w", appartient(var("w"), BA)))))
        return N.loi_deduction(bB, z_in)                   # bB ⇒ z∈B⊔A

    impL = existe_elimination(fwd_left(), nA)
    impR = existe_elimination(fwd_right(), nB)
    z_in_sum = cas(dec_t, impL, impR)
    fwd = existe_elimination(N.loi_deduction(bodyR, z_in_sum), "t")
    fwd_full = syllogisme(equivalence_avant(img_car), fwd)  # z∈K⟨AB⟩ ⇒ z∈B⊔A

    # ── ⇐ : z∈B⊔A ⇒ z∈K⟨AB⟩ ──────────────────────────────────────────────────
    dec_z0 = N.modus_ponens(N.assume(appartient(vz, BA)),
                            equivalence_avant(membre_somme_caracterise(vb, va, vz)))
    exC0, exD0 = dec_z0.conclusion.sous[0], dec_z0.conclusion.sous[1]
    renC = _ax(exC0.lieur, "n1", exC0.sous[0])
    renD = _ax(exD0.lieur, "n2", exD0.sous[0])
    dec_z = N.modus_ponens(dec_z0, equivalence_avant(_ou_congruence(renC, renD)))
    exC, exD = dec_z.conclusion.sous[0], dec_z.conclusion.sous[1]
    nC, bC = exC.lieur, exC.sous[0]        # n1 ; (n1∈B et z=(n1,0))  [copie gauche de B⊔A]
    nD, bD = exD.lieur, exD.sous[0]        # n2 ; (n2∈A et z=(n2,1))  [copie droite de B⊔A]
    vc, vd = var(nC), var(nD)

    def back_left():
        # z=(c,0), c∈B → antécédent t₀=(c,1)∈A⊔B, K((c,1))=(c,0)=z
        hc = N.assume(bC)
        c_in = conjonction_elim_gauche(hc)         # c∈B
        z_eq = conjonction_elim_droite(hc)         # z=(c,0)
        t0 = E.couple(vc, UN)                       # (c,1)
        t0_in = N.modus_ponens(c_in, injection_droite_dans_somme(vc, va, vb))   # (c,1)∈A⊔B
        Kt0 = N.modus_ponens(c_in, N.loi_deduction(appartient(vc, vb),
                                                   commute_graphe_valeur_droite(a, b, vc)))  # K((c,1))=(c,0)
        Tt0 = subst_t(t0, "k", T)
        Kt0_Tt0 = N.modus_ponens(t0_in, N.loi_deduction(appartient(t0, AB),
                                                        _commute_graphe_valeur_t(a, b, t0)))  # K((c,1))=T[(c,1)]
        # z=(c,0)=K((c,1))=T[(c,1)]
        z_eq_Kt0 = composer_egalites(z_eq, N.modus_ponens(Kt0, symetrie(E.valeur(K, t0), E.couple(vc, ZERO))))  # z=K((c,1))
        z_eq_Tt0 = composer_egalites(z_eq_Kt0, Kt0_Tt0)   # z=T[(c,1)]
        memb = _couple_dans_K(a, b, t0, vz, z_eq_Tt0, t0_in)   # (t0,z)∈K
        wit = conjonction_intro(t0_in, memb)
        ex_t = N.modus_ponens(wit, N.s5(et(appartient(var("t"), AB),
                                           appartient(E.couple(var("t"), vz), K)), t0, "t"))
        z_in_img = N.modus_ponens(ex_t, equivalence_arriere(img_car))   # z∈K⟨AB⟩
        return N.loi_deduction(bC, z_in_img)

    def back_right():
        # z=(d,1), d∈A → antécédent t₀=(d,0)∈A⊔B, K((d,0))=(d,1)=z
        hd = N.assume(bD)
        d_in = conjonction_elim_gauche(hd)         # d∈A
        z_eq = conjonction_elim_droite(hd)         # z=(d,1)
        t0 = E.couple(vd, ZERO)                     # (d,0)
        t0_in = N.modus_ponens(d_in, injection_gauche_dans_somme(vd, va, vb))   # (d,0)∈A⊔B
        Kt0 = N.modus_ponens(d_in, N.loi_deduction(appartient(vd, va),
                                                   commute_graphe_valeur_gauche(a, b, vd)))  # K((d,0))=(d,1)
        Tt0 = subst_t(t0, "k", T)
        Kt0_Tt0 = N.modus_ponens(t0_in, N.loi_deduction(appartient(t0, AB),
                                                        _commute_graphe_valeur_t(a, b, t0)))  # K((d,0))=T[(d,0)]
        z_eq_Kt0 = composer_egalites(z_eq, N.modus_ponens(Kt0, symetrie(E.valeur(K, t0), E.couple(vd, UN))))  # z=K((d,0))
        z_eq_Tt0 = composer_egalites(z_eq_Kt0, Kt0_Tt0)   # z=T[(d,0)]
        memb = _couple_dans_K(a, b, t0, vz, z_eq_Tt0, t0_in)
        wit = conjonction_intro(t0_in, memb)
        ex_t = N.modus_ponens(wit, N.s5(et(appartient(var("t"), AB),
                                           appartient(E.couple(var("t"), vz), K)), t0, "t"))
        z_in_img = N.modus_ponens(ex_t, equivalence_arriere(img_car))
        return N.loi_deduction(bD, z_in_img)

    impC = existe_elimination(back_left(), nC)
    impD = existe_elimination(back_right(), nD)
    z_in_img = cas(dec_z, impC, impD)
    bwd_full = N.loi_deduction(appartient(vz, BA), z_in_img)   # z∈B⊔A ⇒ z∈K⟨AB⟩

    equiv_z = conjonction_intro(fwd_full, bwd_full)
    char_u = N.generalisation("z", equiv_z)
    selfBA = N.generalisation("z", conjonction_intro(
        a_implique_a(appartient(vz, BA)), a_implique_a(appartient(vz, BA))))
    from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_theoremes import egalite_par_extension
    return egalite_par_extension(char_u, selfBA, E.image(K, AB), BA, "z")


# ── PALIER 6 : est_bijection_de(K, A⊔B, B⊔A) puis Eq(A⊔B, B⊔A) ────────────────
def _corps_pourtout(concl):
    return concl.sous[0].sous[0].sous[0]


def _renomme_injective(c3):
    """⊢ injective_dans(K,A⊔B) [liants s,sp]  →  forme défaut u,up."""
    from bourbaki.logique.i_3_quantifies.tactiques_abrege_quantif import alpha_pour_tout, congruence_pour_tout
    R_outer = _corps_pourtout(c3.conclusion)
    ren_outer = alpha_pour_tout("s", "u", R_outer)
    step1 = N.modus_ponens(c3, equivalence_avant(ren_outer))
    Rin = _corps_pourtout(step1.conclusion)
    body2 = _corps_pourtout(Rin)
    ren_inner = alpha_pour_tout("sp", "up", body2)
    cong = congruence_pour_tout(ren_inner, "u")
    return N.modus_ponens(step1, equivalence_avant(cong))


def commute_est_bijection(a="A", b="B"):
    """⊢ est_bijection_de(K, A⊔B, B⊔A).   (l'échange des copies est une bijection.)

    Les 4 conjoints (fonctionnel, domaine, injectif, image) sont fournis par les
    paliers 1/2/4/5.  Tous CLOS (pas d'hypothèse, contrairement au cas F,G)."""
    from bourbaki.cardinaux.ensembles_cardinaux import est_bijection_de
    c1 = commute_graphe_fonctionnel(a, b)                  # K fonctionnel
    c2 = commute_graphe_domaine(a, b)                      # dom K = A⊔B
    c3 = _renomme_injective(commute_graphe_injective(a, b))  # inj K (liants u,up)
    c4 = commute_graphe_image(a, b)                       # image K = B⊔A
    return conjonction_intro(conjonction_intro(c1, c2), conjonction_intro(c3, c4))


def eq_somme_commute(a="A", b="B"):
    """⊢ Eq(A⊔B, B⊔A).   (COMMUTATIVITÉ de la somme à équipotence près, §III.3.3.)

    Témoin = le graphe d'échange des copies K ; S5 sur est_bijection_de(F,·,·)
    donne (∃F)bij = Eq(A⊔B, B⊔A)."""
    from bourbaki.cardinaux.ensembles_cardinaux import est_bijection_de
    va, vb = _t(a), _t(b)
    AB = somme_disjointe(va, vb)
    BA = somme_disjointe(vb, va)
    K = _commute_graphe(a, b, "k")
    bij = commute_est_bijection(a, b)                     # est_bijection_de(K, A⊔B, B⊔A)
    return N.modus_ponens(bij, N.s5(est_bijection_de(var("F"), AB, BA), K, "F"))


__all__ = ["commute_graphe_fonctionnel", "commute_graphe_domaine",
           "commute_graphe_valeur_gauche", "commute_graphe_valeur_droite",
           "commute_graphe_injective", "commute_graphe_image",
           "commute_est_bijection", "eq_somme_commute"]
