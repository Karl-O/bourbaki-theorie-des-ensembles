"""§III.3 — La TRANSPOSITION τ_{S,p,q} est INJECTIVE sur S.

injective_dans(τ, S) := (∀u)(∀u')((u∈S et u'∈S et τ(u)=τ(u')) ⇒ u=u').

PRINCIPE (involution).  Sous p,q∈S, on a dom(τ)=S (transpo_domaine), donc pour
u∈S, (u, τ(u)) ∈ τ (valeur_dans_graphe).  De τ(u)=τ(u') on tire alors
(u, c) ∈ τ ET (u', c) ∈ τ  avec  c := τ(u)  (même 2ᵉ coordonnée).  La brique
`_inj_membre` (calquée sur transpo_fonctionnel/_ech_ech_vz mais coordonnée FIXÉE
À DROITE) conclut u=u' par analyse de cas FIX/ECH sur les deux appartenances ;
¬(p=q) écarte les croisements ECH/ECH où c=p et c=q forceraient p=q.
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (Terme, var, egal, et, ou, non, appartient,
                                       existe)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite, cas)
from bourbaki.logique.i_4_egalitaires.tactiques_abrege_egalite import (
    symetrie, composer_egalites)
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    equivalence_avant, instancie)
from bourbaki.ensembles.fonctions.ii_3_4_fonctions_valeur.ensembles_fonctions import valeur_dans_graphe
from bourbaki.cardinaux.arithmetique.iii_3_4_prop8_successeur.transposition._membre import (
    transpo, transpo_membre)
from bourbaki.cardinaux.arithmetique.iii_3_4_prop8_successeur.transposition._bijection import (
    _disj, _fix, _ech, transpo_domaine)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def _ex_falso(thm_a, thm_na, cible):
    """Γ⊢A, Δ⊢¬A ⟹ Γ∪Δ⊢ cible.   (ex falso quodlibet via S2.)"""
    a = thm_a.conclusion
    return N.modus_ponens(thm_a, N.modus_ponens(thm_na, N.s2(non(a), cible)))


# ═══════════════════════════════════════════════════════════════════════════════
# BRIQUE :  {¬(p=q)} ⊢ ((u,c)∈τ et (u',c)∈τ) ⇒ u=u'   (involution, 2ᵉ coord. fixée)
# ═══════════════════════════════════════════════════════════════════════════════
def _ech_contredit_fix_c(vp, vq, vu, vc, fix_nuv, cible):
    """{¬(u=p) et ¬(u=q)} ⊢ ECH(u,c) ⇒ cible.   (ECH force u=p ou u=q, contradiction.)

    fix_nuv : preuve de (¬(u=p) et ¬(u=q)).  ECH(u,c)=(u=p et c=q) ou (u=q et c=p)
    ⇒ u=p ou u=q ⇒ ex falso ⇒ cible."""
    nup = conjonction_elim_gauche(fix_nuv)                  # ¬(u=p)
    nuq = conjonction_elim_droite(fix_nuv)                  # ¬(u=q)
    hl = N.assume(et(egal(vu, vp), egal(vc, vq)))
    brL = N.loi_deduction(et(egal(vu, vp), egal(vc, vq)),
                          _ex_falso(conjonction_elim_gauche(hl), nup, cible))
    hr = N.assume(et(egal(vu, vq), egal(vc, vp)))
    brR = N.loi_deduction(et(egal(vu, vq), egal(vc, vp)),
                          _ex_falso(conjonction_elim_gauche(hr), nuq, cible))
    hech = N.assume(_ech(vp, vq, vu, vc))
    return N.loi_deduction(_ech(vp, vq, vu, vc), cas(hech, brL, brR))


def _ech_ech_uu(vp, vq, vu, vup, vc, hnpq, hec_u):
    """{¬(p=q), ECH(u,c)} ⊢ ECH(u',c) ⇒ u=u'.   (analyse croisée, coord. droite fixée.)

    ECH(u,c)=(u=p,c=q) ou (u=q,c=p) ; ECH(u',c) idem.  Combinaisons :
      • (u=p,c=q)&(u'=p,c=q) ⇒ u=p=u' ;     • (u=p,c=q)&(u'=q,c=p) ⇒ c=q et c=p ⇒ p=q (ex falso) ;
      • (u=q,c=p)&(u'=p,c=q) ⇒ p=q (ex falso) ; • (u=q,c=p)&(u'=q,c=p) ⇒ u=q=u'."""
    cible = egal(vu, vup)
    hecz = N.assume(_ech(vp, vq, vup, vc))

    # ECH(u,c) gauche : u=p, c=q
    hvl = N.assume(et(egal(vu, vp), egal(vc, vq)))
    u_eq_p, c_eq_q = conjonction_elim_gauche(hvl), conjonction_elim_droite(hvl)
    #   ECH(u',c) gauche : u'=p, c=q ⇒ u=u' (u=p, u'=p)
    hzl1 = N.assume(et(egal(vup, vp), egal(vc, vq)))
    up_eq_p1 = conjonction_elim_gauche(hzl1)               # u'=p
    uu_ll = N.loi_deduction(et(egal(vup, vp), egal(vc, vq)),
                            composer_egalites(u_eq_p, N.modus_ponens(up_eq_p1, symetrie(vup, vp))))
    #   ECH(u',c) droite : u'=q, c=p ⇒ c=q et c=p ⇒ q=p ⇒ p=q (ex falso)
    hzr1 = N.assume(et(egal(vup, vq), egal(vc, vp)))
    c_eq_p1 = conjonction_elim_droite(hzr1)                # c=p
    q_eq_c = N.modus_ponens(c_eq_q, symetrie(vc, vq))      # q=c
    q_eq_p1 = composer_egalites(q_eq_c, c_eq_p1)           # q=p
    p_eq_q1 = N.modus_ponens(q_eq_p1, symetrie(vq, vp))    # p=q
    uu_lr = N.loi_deduction(et(egal(vup, vq), egal(vc, vp)), _ex_falso(p_eq_q1, hnpq, cible))
    uu_underVL = N.loi_deduction(et(egal(vu, vp), egal(vc, vq)), cas(hecz, uu_ll, uu_lr))

    # ECH(u,c) droite : u=q, c=p
    hvr = N.assume(et(egal(vu, vq), egal(vc, vp)))
    u_eq_q, c_eq_p = conjonction_elim_gauche(hvr), conjonction_elim_droite(hvr)
    #   ECH(u',c) gauche : u'=p, c=q ⇒ c=p et c=q ⇒ p=q (ex falso)
    hzl2 = N.assume(et(egal(vup, vp), egal(vc, vq)))
    c_eq_q2 = conjonction_elim_droite(hzl2)                # c=q
    p_eq_c = N.modus_ponens(c_eq_p, symetrie(vc, vp))      # p=c
    p_eq_q2 = composer_egalites(p_eq_c, c_eq_q2)           # p=q
    uu_rl = N.loi_deduction(et(egal(vup, vp), egal(vc, vq)), _ex_falso(p_eq_q2, hnpq, cible))
    #   ECH(u',c) droite : u'=q, c=p ⇒ u=u' (u=q, u'=q)
    hzr2 = N.assume(et(egal(vup, vq), egal(vc, vp)))
    up_eq_q2 = conjonction_elim_gauche(hzr2)               # u'=q
    uu_rr = N.loi_deduction(et(egal(vup, vq), egal(vc, vp)),
                            composer_egalites(u_eq_q, N.modus_ponens(up_eq_q2, symetrie(vup, vq))))
    uu_underVR = N.loi_deduction(et(egal(vu, vq), egal(vc, vp)), cas(hecz, uu_rl, uu_rr))

    return N.loi_deduction(_ech(vp, vq, vup, vc), cas(hec_u, uu_underVL, uu_underVR))


def _inj_membre(s, p, q, vu, vup, vc):
    """{¬(p=q)} ⊢ ((u,c)∈τ et (u',c)∈τ) ⇒ u=u'.   (involution : même image ⇒ même antécédent.)

    Calque de transpo_fonctionnel, COORDONNÉE FIXÉE À DROITE (c).  Par transpo_membre,
    (u,c)∈τ ⇒ FIX(u,c) ou ECH(u,c) (idem (u',c)) ; les 4 combinaisons concluent u=u'
    (FIX/FIX par u=c=u' ; FIX/ECH par ex falso ; ECH/ECH par _ech_ech_uu)."""
    vS, vp, vq = _t(s), _t(p), _t(q)
    T = transpo(vS, vp, vq)
    npq = non(egal(vp, vq))
    cible = egal(vu, vup)

    ante = et(appartient(E.couple(vu, vc), T), appartient(E.couple(vup, vc), T))
    h = N.assume(ante)
    du = N.modus_ponens(conjonction_elim_gauche(h), _disj(s, p, q, vu, vc))    # FIX(u,c) ou ECH(u,c)
    dup = N.modus_ponens(conjonction_elim_droite(h), _disj(s, p, q, vup, vc))  # FIX(u',c) ou ECH(u',c)
    hnpq = N.assume(npq)

    # — sous FIX(u,c) : u=c ; conclure u=u' par cas sur dup —
    hfu = N.assume(_fix(vS, vp, vq, vu, vc))
    u_eq_c = conjonction_elim_droite(conjonction_elim_gauche(hfu))   # u=c
    nuv = conjonction_elim_droite(hfu)                              # ¬(u=p) et ¬(u=q)
    #   FIX(u',c) : u'=c ⇒ u=c=u'  (u=c, c=u')
    hfup = N.assume(_fix(vS, vp, vq, vup, vc))
    up_eq_c = conjonction_elim_droite(conjonction_elim_gauche(hfup))   # u'=c
    c_eq_up = N.modus_ponens(up_eq_c, symetrie(vup, vc))           # c=u'
    uu_fixfix = N.loi_deduction(_fix(vS, vp, vq, vup, vc), composer_egalites(u_eq_c, c_eq_up))
    #   ECH(u',c) : contradiction via ¬(u=p),¬(u=q)?  NON — ECH porte sur u', pas u.
    #   On utilise plutôt : FIX(u,c) donne u=c, et ECH(u',c) donne c=q ou c=p ⇒ u=q ou u=p,
    #   contredisant ¬(u=q)/¬(u=p) (via u=c).  _ech_contredit_fix_c attend ECH(u,·) : on
    #   reconstruit ECH(u,c) depuis ECH(u',c) ? non.  Direct : ECH(u',c) ⇒ c=p ou c=q.
    uu_fixech = _fix_ech_c(vp, vq, vu, vup, vc, u_eq_c, nuv, cible)
    uu_underFIXu = N.loi_deduction(_fix(vS, vp, vq, vu, vc), cas(dup, uu_fixfix, uu_fixech))

    # — sous ECH(u,c) : conclure u=u' par cas sur dup —
    heu = N.assume(_ech(vp, vq, vu, vc))
    #   FIX(u',c) : u'=c, et ¬(u'=p),¬(u'=q) ; ECH(u,c) ⇒ c=p ou c=q ⇒ u'=p ou u'=q (ex falso)
    hfup2 = N.assume(_fix(vS, vp, vq, vup, vc))
    up_eq_c2 = conjonction_elim_droite(conjonction_elim_gauche(hfup2))   # u'=c
    nuv2 = conjonction_elim_droite(hfup2)                          # ¬(u'=p) et ¬(u'=q)
    cible_sym = egal(vup, vu)
    echu_falso = N.modus_ponens(heu, _fix_ech_c(vp, vq, vup, vu, vc, up_eq_c2, nuv2, cible_sym))  # u'=u
    uu_echfix = N.loi_deduction(_fix(vS, vp, vq, vup, vc),
                                N.modus_ponens(echu_falso, symetrie(vup, vu)))   # u=u'
    #   ECH(u',c) : analyse croisée
    uu_echech = _ech_ech_uu(vp, vq, vu, vup, vc, hnpq, heu)
    uu_underECHu = N.loi_deduction(_ech(vp, vq, vu, vc), cas(dup, uu_echfix, uu_echech))

    uu_final = cas(du, uu_underFIXu, uu_underECHu)                 # u=u'   [hyps ante, ¬(p=q)]
    return N.loi_deduction(ante, uu_final)                        # ((u,c)∈τ et (u',c)∈τ)⇒u=u'  [hyp ¬(p=q)]


def _fix_ech_c(vp, vq, vu, vup, vc, u_eq_c, fix_nuv, cible):
    """{u=c, ¬(u=p) et ¬(u=q)} ⊢ ECH(u',c) ⇒ cible.

    ECH(u',c)=(u'=p,c=q) ou (u'=q,c=p) ⇒ c=q ou c=p ⇒ (u=q ou u=p, via u=c) ⇒ ex falso.
    On NE consulte PAS u' ; on utilise seulement c (= image partagée) et les négations
    sur u via u=c."""
    nup = conjonction_elim_gauche(fix_nuv)                  # ¬(u=p)
    nuq = conjonction_elim_droite(fix_nuv)                  # ¬(u=q)
    # branche u'=p, c=q : c=q et u=c ⇒ u=q ⇒ contredit ¬(u=q)
    hl = N.assume(et(egal(vup, vp), egal(vc, vq)))
    c_eq_q = conjonction_elim_droite(hl)                    # c=q
    u_eq_q = composer_egalites(u_eq_c, c_eq_q)              # u=q
    brL = N.loi_deduction(et(egal(vup, vp), egal(vc, vq)), _ex_falso(u_eq_q, nuq, cible))
    # branche u'=q, c=p : c=p et u=c ⇒ u=p ⇒ contredit ¬(u=p)
    hr = N.assume(et(egal(vup, vq), egal(vc, vp)))
    c_eq_p = conjonction_elim_droite(hr)                    # c=p
    u_eq_p = composer_egalites(u_eq_c, c_eq_p)              # u=p
    brR = N.loi_deduction(et(egal(vup, vq), egal(vc, vp)), _ex_falso(u_eq_p, nup, cible))
    hech = N.assume(_ech(vp, vq, vup, vc))
    return N.loi_deduction(_ech(vp, vq, vup, vc), cas(hech, brL, brR))


# ═══════════════════════════════════════════════════════════════════════════════
# (u, τ(u)) ∈ τ   pour u ∈ S   (sous p,q∈S : u ∈ dom τ = S, donc image définie)
# ═══════════════════════════════════════════════════════════════════════════════
def _couple_u_val(s, p, q, vu):
    """{p∈S, q∈S, u∈S} ⊢ (u, τ(u)) ∈ τ.   (u ∈ dom τ = S ⇒ (u,τ(u)) dans le graphe.)

    transpo_domaine donne dom τ = S sous (p∈S et q∈S) ; u∈S ⇒ u∈dom τ (Leibniz S→dom τ) ;
    AXIOME_DOM ⇒ (∃y)((u,y)∈τ) ; valeur_dans_graphe ⇒ (u, τ(u))∈τ."""
    vS, vp, vq = _t(s), _t(p), _t(q)
    T = transpo(vS, vp, vq)
    vy = var("y")
    pin, qin = appartient(vp, vS), appartient(vq, vS)
    # dom τ = S  (sous p∈S, q∈S)
    dom_eq = N.modus_ponens(conjonction_intro(N.assume(pin), N.assume(qin)),
                            transpo_domaine(s, p, q))          # dom τ = S   [hyps p∈S,q∈S]
    S_eq_dom = N.modus_ponens(dom_eq, symetrie(E.dom(T), vS))  # S = dom τ
    # u∈S ⇒ u∈dom τ  (Leibniz : S = dom τ)
    huin = N.assume(appartient(vu, vS))
    u_in_dom = N.modus_ponens(huin, equivalence_avant(N.modus_ponens(
        S_eq_dom, N.s6(vS, E.dom(T), "w", appartient(vu, var("w"))))))   # u ∈ dom τ
    # AXIOME_DOM : u∈dom τ ⇔ (∃y)((u,y)∈τ)
    ax_dom = N.axiome(E.theorie_ensembles(), E.AXIOME_DOM)
    car = instancie(instancie(ax_dom, T), vu)                  # u∈dom τ ⇔ (∃y)((u,y)∈τ)
    exy = N.modus_ponens(u_in_dom, equivalence_avant(car))     # (∃y)((u,y)∈τ)
    # (u, τ(u)) ∈ τ
    vdg = valeur_dans_graphe(T, vu)                            # {(∃y)((u,y)∈τ)} ⊢ (u,τ(u))∈τ
    return N.modus_ponens(exy, N.loi_deduction(
        existe("y", appartient(E.couple(vu, vy), T)), vdg))     # (u, τ(u))∈τ   [hyps p∈S,q∈S,u∈S]


# ═══════════════════════════════════════════════════════════════════════════════
# transpo_injective :  ¬(p=q) ⇒ injective_dans(τ, S)   (sous p,q∈S)
# ═══════════════════════════════════════════════════════════════════════════════
def transpo_injective(s="S", p="p", q="q"):
    """⊢ (p∈S et q∈S et ¬(p=q)) ⇒ injective_dans(τ_{S,p,q}, S).

    injective_dans(τ,S) = (∀u)(∀u')((u∈S et u'∈S et τ(u)=τ(u')) ⇒ u=u').  Pour u,u'∈S,
    (u,τ(u))∈τ et (u',τ(u'))∈τ (_couple_u_val) ; de τ(u)=τ(u') on réécrit τ(u')→τ(u),
    d'où (u',τ(u))∈τ.  Avec c:=τ(u), _inj_membre (sous ¬(p=q)) conclut u=u'."""
    vS, vp, vq = _t(s), _t(p), _t(q)
    vu, vup = var("u"), var("up")
    T = transpo(vS, vp, vq)
    pin, qin, npq = appartient(vp, vS), appartient(vq, vS), non(egal(vp, vq))
    hyp = et(et(pin, qin), npq)
    c = E.valeur(T, vu)                                        # τ(u)
    cp = E.valeur(T, vup)                                      # τ(u')

    # corps de injective_dans : (u∈S et u'∈S et τ(u)=τ(u')) ⇒ u=u'
    inner_ante = et(et(appartient(vu, vS), appartient(vup, vS)), egal(c, cp))
    hh = N.assume(inner_ante)
    uin = conjonction_elim_gauche(conjonction_elim_gauche(hh))    # u∈S
    upin = conjonction_elim_droite(conjonction_elim_gauche(hh))   # u'∈S
    val_eq = conjonction_elim_droite(hh)                         # τ(u)=τ(u')

    # contexte p,q∈S
    hpq = N.assume(et(pin, qin))
    hp = conjonction_elim_gauche(hpq)
    hq = conjonction_elim_droite(hpq)

    # (u, τ(u)) ∈ τ   [hyps p∈S,q∈S,u∈S]
    uc = _couple_u_val(s, p, q, vu)
    uc = N.modus_ponens(hp, N.loi_deduction(pin, uc))
    uc = N.modus_ponens(hq, N.loi_deduction(qin, uc))
    uc = N.modus_ponens(uin, N.loi_deduction(appartient(vu, vS), uc))   # (u, τ(u))∈τ
    # (u', τ(u')) ∈ τ   [hyps p∈S,q∈S,u'∈S]
    upc = _couple_u_val(s, p, q, vup)
    upc = N.modus_ponens(hp, N.loi_deduction(pin, upc))
    upc = N.modus_ponens(hq, N.loi_deduction(qin, upc))
    upc = N.modus_ponens(upin, N.loi_deduction(appartient(vup, vS), upc))   # (u', τ(u'))∈τ
    # réécrire τ(u') → τ(u) dans (u', τ(u'))∈τ via τ(u)=τ(u')  (Leibniz)
    cp_eq_c = N.modus_ponens(val_eq, symetrie(c, cp))           # τ(u')=τ(u)
    upc_c = N.modus_ponens(upc, equivalence_avant(N.modus_ponens(
        cp_eq_c, N.s6(cp, c, "w", appartient(E.couple(vup, var("w")), T)))))   # (u', τ(u))∈τ

    # _inj_membre avec c=τ(u) : {¬(p=q)} ⊢ ((u,τ(u))∈τ et (u',τ(u))∈τ) ⇒ u=u'
    imm = _inj_membre(s, p, q, vu, vup, c)
    uu = N.modus_ponens(conjonction_intro(uc, upc_c), imm)     # u=u'  [hyps inner_ante,p∈S,q∈S,¬(p=q)]

    body = N.loi_deduction(inner_ante, uu)                     # corps  [hyps (p∈S et q∈S),¬(p=q)]
    gen = N.generalisation("u", N.generalisation("up", body))  # injective_dans(τ,S)  [hyps (p∈S et q∈S),¬(p=q)]
    # décharger les hypothèses (p∈S et q∈S) et ¬(p=q) puis les ré-introduire depuis hyp
    g1 = N.loi_deduction(et(pin, qin), gen)                    # (p∈S et q∈S) ⇒ injective_dans  [hyp ¬(p=q)]
    g2 = N.loi_deduction(npq, g1)                              # ⊢ ¬(p=q) ⇒ ((p∈S et q∈S) ⇒ injective_dans)
    hfull = N.assume(hyp)
    pq2 = conjonction_elim_gauche(hfull)                       # (p∈S et q∈S)
    npq2 = conjonction_elim_droite(hfull)                      # ¬(p=q)
    inj = N.modus_ponens(pq2, N.modus_ponens(npq2, g2))        # injective_dans(τ,S)  [hyp hyp]
    return N.loi_deduction(hyp, inj)                           # (p∈S et q∈S et ¬(p=q)) ⇒ injective_dans(τ,S)


__all__ = ["_inj_membre", "transpo_injective"]
