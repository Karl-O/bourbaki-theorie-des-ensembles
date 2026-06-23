"""§III.3 — La TRANSPOSITION τ_{S,p,q} est une BIJECTION de S sur S.

Les 4 conjoints de est_bijection_de(τ, S, S) par ANALYSE DE CAS sur la
caractérisation `transpo_membre`, sous p,q∈S et p≠q :

  • transpo_fonctionnel : (∀u)(∀v)(∀z)(((u,v)∈τ et (u,z)∈τ)⇒v=z) ;
  • transpo_domaine     : dom(τ) = S ;
  • transpo_injective   : injective_dans(τ, S) ;
  • transpo_image       : image(τ, S) = S ;
  • transpo_valeur_q    : τ(q) = p ;
  • transposition_existe(S,p,q) : (p∈S et q∈S et ¬(p=q)) ⇒
        (∃τ)(est_bijection_de(τ,S,S) et τ(q)=p).

Modèle : ensembles_equipotence (Δ_S).  La transposition échange p↔q et fixe le
reste — chaque conjoint se ramène, par transpo_membre, à des cas d'égalités.
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (Terme, var, egal, et, ou, non, appartient,
                                       existe, pourtout)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege import a_implique_a, syllogisme
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, equivalence_transitivite,
    instancie, cas)
from bourbaki.logique.i_4_egalitaires.tactiques_abrege_egalite import (
    symetrie, composer_egalites, congruence_terme)
from bourbaki.cardinaux.ensembles_cardinaux import est_bijection_de
from bourbaki.cardinaux.arithmetique.ensembles_transposition._membre import (
    transpo, transpo_membre)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def _ex_falso(thm_a, thm_na, cible):
    """Γ⊢A, Δ⊢¬A ⟹ Γ∪Δ⊢ cible.   (ex falso quodlibet via S2.)"""
    a = thm_a.conclusion
    return N.modus_ponens(thm_a, N.modus_ponens(thm_na, N.s2(non(a), cible)))


# ── clauses de transpo_membre (réutilisées partout) ───────────────────────────
def _fix(vS, vp, vq, vu, vv):
    """FIX(u,v) := ((u∈S et u=v) et (¬(u=p) et ¬(u=q)))."""
    return et(et(appartient(vu, vS), egal(vu, vv)), et(non(egal(vu, vp)), non(egal(vu, vq))))


def _ech(vp, vq, vu, vv):
    """ECH(u,v) := ((u=p et v=q) ou (u=q et v=p))."""
    return ou(et(egal(vu, vp), egal(vv, vq)), et(egal(vu, vq), egal(vv, vp)))


def _disj(s, p, q, u, v):
    """⊢ ((u,v)∈τ) ⇒ (FIX(u,v) ou ECH(u,v))   (sens ⇒ de transpo_membre)."""
    return equivalence_avant(transpo_membre(s, p, q, u, v))


def _into(s, p, q, u, v):
    """⊢ (FIX(u,v) ou ECH(u,v)) ⇒ ((u,v)∈τ)   (sens ⇐ de transpo_membre)."""
    return equivalence_arriere(transpo_membre(s, p, q, u, v))


# ═══════════════════════════════════════════════════════════════════════════════
# CONJOINT 1 :  est_fonctionnel(τ)
# ═══════════════════════════════════════════════════════════════════════════════
def _ech_contredit_fix(vp, vq, vu, vv, fix_thm, cible):
    """{FIX(u,·) donne ¬(u=p) et ¬(u=q)} ⊢ ECH(u,v) ⇒ cible   (ECH force u=p ou u=q).

    fix_thm : preuve de (¬(u=p) et ¬(u=q)) (le 2ᵉ conjoint de FIX).  ECH(u,v) =
    (u=p et v=q) ou (u=q et v=p) ⇒ u=p ou u=q ⇒ contradiction ⇒ cible (ex falso)."""
    nup = conjonction_elim_gauche(fix_thm)                  # ¬(u=p)
    nuq = conjonction_elim_droite(fix_thm)                  # ¬(u=q)
    # branche u=p et v=q : u=p contredit ¬(u=p)
    hl = N.assume(et(egal(vu, vp), egal(vv, vq)))
    brL = N.loi_deduction(et(egal(vu, vp), egal(vv, vq)),
                          _ex_falso(conjonction_elim_gauche(hl), nup, cible))
    # branche u=q et v=p : u=q contredit ¬(u=q)
    hr = N.assume(et(egal(vu, vq), egal(vv, vp)))
    brR = N.loi_deduction(et(egal(vu, vq), egal(vv, vp)),
                          _ex_falso(conjonction_elim_gauche(hr), nuq, cible))
    hech = N.assume(_ech(vp, vq, vu, vv))
    return N.loi_deduction(_ech(vp, vq, vu, vv), cas(hech, brL, brR))


def transpo_fonctionnel(s="S", p="p", q="q"):
    """⊢ est_fonctionnel(τ_{S,p,q}).   (sous p≠q : au plus une image par antécédent.)

    {¬(p=q)} ⊢ (∀u)(∀v)(∀z)(((u,v)∈τ et (u,z)∈τ)⇒v=z).  Par transpo_membre, (u,v)∈τ
    donne FIX(u,v) ou ECH(u,v) (idem (u,z)) ; analyse des 4 combinaisons :
      • FIX/FIX : u=v, u=z ⇒ v=z ;        • FIX/ECH ou ECH/FIX : ¬(u=p),¬(u=q) vs ECH (u=p ou u=q) ⇒ ex falso ;
      • ECH/ECH : (u=p,v=q)/(u=q,v=p) croisés ; le cas croisé force p=q (réfuté par ¬(p=q))."""
    vS, vp, vq = _t(s), _t(p), _t(q)
    vu, vv, vz = var("u"), var("v"), var("z")
    T = transpo(vS, vp, vq)
    npq = non(egal(vp, vq))
    cible = egal(vv, vz)

    ante = et(appartient(E.couple(vu, vv), T), appartient(E.couple(vu, vz), T))
    h = N.assume(ante)
    dv = N.modus_ponens(conjonction_elim_gauche(h), _disj(s, p, q, "u", "v"))   # FIX(u,v) ou ECH(u,v)
    dz = N.modus_ponens(conjonction_elim_droite(h), _disj(s, p, q, "u", "z"))   # FIX(u,z) ou ECH(u,z)
    hnpq = N.assume(npq)

    # — sous FIX(u,v) : conclure v=z par cas sur dz —
    hfv = N.assume(_fix(vS, vp, vq, vu, vv))
    u_eq_v = conjonction_elim_droite(conjonction_elim_gauche(hfv))   # u=v
    nuv = conjonction_elim_droite(hfv)                              # ¬(u=p) et ¬(u=q)
    #   branche FIX(u,z) : u=z ⇒ v=z   (v=u=z)
    hfz = N.assume(_fix(vS, vp, vq, vu, vz))
    u_eq_z = conjonction_elim_droite(conjonction_elim_gauche(hfz))   # u=z
    v_eq_u = N.modus_ponens(u_eq_v, symetrie(vu, vv))               # v=u
    vz_fixfix = N.loi_deduction(_fix(vS, vp, vq, vu, vz), composer_egalites(v_eq_u, u_eq_z))
    #   branche ECH(u,z) : ¬(u=p),¬(u=q) contredit ECH ⇒ v=z (ex falso)
    vz_fixech = _ech_contredit_fix(vp, vq, vu, vz, nuv, cible)
    vz_underFIXv = N.loi_deduction(_fix(vS, vp, vq, vu, vv), cas(dz, vz_fixfix, vz_fixech))

    # — sous ECH(u,v) : conclure v=z par cas sur dz —
    hev = N.assume(_ech(vp, vq, vu, vv))
    #   branche FIX(u,z) : ¬(u=p),¬(u=q) contredit ECH(u,v) ⇒ v=z (ex falso, via FIX(u,z))
    hfz2 = N.assume(_fix(vS, vp, vq, vu, vz))
    nuv2 = conjonction_elim_droite(hfz2)                           # ¬(u=p) et ¬(u=q)  (depuis FIX(u,z))
    echv_falso = N.modus_ponens(hev, _ech_contredit_fix(vp, vq, vu, vv, nuv2, cible))   # v=z
    vz_echfix = N.loi_deduction(_fix(vS, vp, vq, vu, vz), echv_falso)
    #   branche ECH(u,z) : analyse croisée
    vz_echech = _ech_ech_vz(vp, vq, vu, vv, vz, hnpq, hev)
    vz_underECHv = N.loi_deduction(_ech(vp, vq, vu, vv), cas(dz, vz_echfix, vz_echech))

    vz_final = cas(dv, vz_underFIXv, vz_underECHv)                 # v=z   [hyps ante, ¬(p=q)]
    inner = N.loi_deduction(ante, vz_final)                       # ((u,v)∈τ et (u,z)∈τ)⇒v=z  [hyp ¬(p=q)]
    gen = N.generalisation("u", N.generalisation("v", N.generalisation("z", inner)))
    return N.loi_deduction(npq, gen)                              # ⊢ ¬(p=q) ⇒ est_fonctionnel(τ)


def _ech_ech_vz(vp, vq, vu, vv, vz, hnpq, hev):
    """{¬(p=q), ECH(u,v)} ⊢ ECH(u,z) ⇒ v=z.   (analyse croisée des deux échanges.)

    ECH(u,v) = (u=p,v=q) ou (u=q,v=p).  ECH(u,z) idem en z.  Combinaisons :
      • (u=p,v=q) & (u=p,z=q) ⇒ v=q=z ;       • (u=p,v=q) & (u=q,z=p) ⇒ u=p et u=q ⇒ p=q (ex falso) ;
      • (u=q,v=p) & (u=p,z=q) ⇒ p=q (ex falso) ; • (u=q,v=p) & (u=q,z=p) ⇒ v=p=z."""
    cible = egal(vv, vz)
    hez = N.assume(_ech(vp, vq, vu, vz))

    # On déroule explicitement les 4 sous-cas :
    # ECH(u,v) gauche : u=p, v=q
    hvl = N.assume(et(egal(vu, vp), egal(vv, vq)))
    u_eq_p, v_eq_q = conjonction_elim_gauche(hvl), conjonction_elim_droite(hvl)
    #   ECH(u,z) gauche : u=p, z=q ⇒ v=z (v=q, z=q)
    hzl1 = N.assume(et(egal(vu, vp), egal(vz, vq)))
    z_eq_q1 = conjonction_elim_droite(hzl1)
    vz_ll = N.loi_deduction(et(egal(vu, vp), egal(vz, vq)),
                            composer_egalites(v_eq_q, N.modus_ponens(z_eq_q1, symetrie(vz, vq))))
    #   ECH(u,z) droite : u=q, z=p ⇒ u=p et u=q ⇒ p=q (ex falso)
    hzr1 = N.assume(et(egal(vu, vq), egal(vz, vp)))
    u_eq_q1 = conjonction_elim_gauche(hzr1)
    p_eq_u = N.modus_ponens(u_eq_p, symetrie(vu, vp))          # p=u
    p_eq_q1 = composer_egalites(p_eq_u, u_eq_q1)               # p=q
    vz_lr = N.loi_deduction(et(egal(vu, vq), egal(vz, vp)), _ex_falso(p_eq_q1, hnpq, cible))
    vz_underVL = N.loi_deduction(et(egal(vu, vp), egal(vv, vq)), cas(hez, vz_ll, vz_lr))

    # ECH(u,v) droite : u=q, v=p
    hvr = N.assume(et(egal(vu, vq), egal(vv, vp)))
    u_eq_q, v_eq_p = conjonction_elim_gauche(hvr), conjonction_elim_droite(hvr)
    #   ECH(u,z) gauche : u=p, z=q ⇒ u=q et u=p ⇒ q=p ⇒ p=q (ex falso)
    hzl2 = N.assume(et(egal(vu, vp), egal(vz, vq)))
    u_eq_p2 = conjonction_elim_gauche(hzl2)
    q_eq_u = N.modus_ponens(u_eq_q, symetrie(vu, vq))         # q=u
    q_eq_p = composer_egalites(q_eq_u, u_eq_p2)               # q=p
    p_eq_q2 = N.modus_ponens(q_eq_p, symetrie(vq, vp))        # p=q
    vz_rl = N.loi_deduction(et(egal(vu, vp), egal(vz, vq)), _ex_falso(p_eq_q2, hnpq, cible))
    #   ECH(u,z) droite : u=q, z=p ⇒ v=z (v=p, z=p)
    hzr2 = N.assume(et(egal(vu, vq), egal(vz, vp)))
    z_eq_p2 = conjonction_elim_droite(hzr2)
    vz_rr = N.loi_deduction(et(egal(vu, vq), egal(vz, vp)),
                            composer_egalites(v_eq_p, N.modus_ponens(z_eq_p2, symetrie(vz, vp))))
    vz_underVR = N.loi_deduction(et(egal(vu, vq), egal(vv, vp)), cas(hez, vz_rl, vz_rr))

    return N.loi_deduction(_ech(vp, vq, vu, vz), cas(hev, vz_underVL, vz_underVR))


# ═══════════════════════════════════════════════════════════════════════════════
# CONJOINT 2 :  dom(τ) = S
# ═══════════════════════════════════════════════════════════════════════════════
def _couple_in_ech_gauche(s, p, q, va, vb):
    """⊢ (a,b)∈τ  quand (a,b)=(p,q)  (témoin ECH gauche : a=p et b=q, ici réflexif).

    Construit ECH(a,b) par sa branche GAUCHE (a=p et b=q) — avec a=p, b=q ce sont des
    réflexivités —, l'injecte dans (FIX ou ECH), puis dans τ via _into."""
    vS, vp, vq = _t(s), _t(p), _t(q)
    ech_g = conjonction_intro(N.reflexivite(va), N.reflexivite(vb))   # a=p et b=q  (a=p,b=q réflexifs)
    ech = N.modus_ponens(ech_g, N.s2(et(egal(va, vp), egal(vb, vq)),
                                     et(egal(va, vq), egal(vb, vp))))   # ECH(a,b)
    fix_or_ech = _ech_dans_fix_ou_ech(vS, vp, vq, va, vb, ech)
    return N.modus_ponens(fix_or_ech, _into(s, p, q, va, vb))         # (a,b)∈τ


def _ech_dans_fix_ou_ech(vS, vp, vq, va, vb, ech_thm):
    """{ECH(a,b)} ⊢ (FIX(a,b) ou ECH(a,b))   (injection à droite : ECH⇒(ECH∨FIX)⇒(FIX∨ECH))."""
    ech_f, fix_f = _ech(vp, vq, va, vb), _fix(vS, vp, vq, va, vb)
    return N.modus_ponens(N.modus_ponens(ech_thm, N.s2(ech_f, fix_f)), N.s3(ech_f, fix_f))


def _couple_in_ech_droite(s, p, q, va, vb):
    """⊢ (a,b)∈τ  quand (a,b)=(q,p)  (témoin ECH droite : a=q et b=p, ici réflexif)."""
    vS, vp, vq = _t(s), _t(p), _t(q)
    ech_d = conjonction_intro(N.reflexivite(va), N.reflexivite(vb))   # a=q et b=p
    ech = N.modus_ponens(ech_d, syllogisme(
        N.s2(et(egal(va, vq), egal(vb, vp)), et(egal(va, vp), egal(vb, vq))),
        N.s3(et(egal(va, vq), egal(vb, vp)), et(egal(va, vp), egal(vb, vq)))))   # ECH(a,b) (droite)
    fix_or_ech = _ech_dans_fix_ou_ech(vS, vp, vq, va, vb, ech)
    return N.modus_ponens(fix_or_ech, _into(s, p, q, va, vb))         # (a,b)∈τ


def transpo_domaine(s="S", p="p", q="q"):
    """⊢ (p∈S et q∈S) ⇒ (dom(τ_{S,p,q}) = S).

    z∈dom τ ⇔ (∃y)((z,y)∈τ) ⇔ z∈S.  ⇐ : z∈S a une image (z=p↦q, z=q↦p, sinon z↦z) ;
    ⇒ : (z,y)∈τ donne FIX (z∈S direct) ou ECH (z=p ou z=q, ∈S car p,q∈S).  Par
    extension (egalite_par_extension)."""
    from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_theoremes import egalite_par_extension
    from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import tiers_exclu
    from bourbaki.logique.i_3_quantifies.tactiques_abrege_quantif import existe_elimination
    vS, vp, vq = _t(s), _t(p), _t(q)
    vz, vy = var("z"), var("y")
    T = transpo(vS, vp, vq)
    pin, qin = appartient(vp, vS), appartient(vq, vS)
    hyp = et(pin, qin)
    hpq = N.assume(hyp)
    hp_in = conjonction_elim_gauche(hpq)                    # p∈S
    hq_in = conjonction_elim_droite(hpq)                    # q∈S

    inS = appartient(vz, vS)
    ex_zy = existe("y", appartient(E.couple(vz, vy), T))    # (∃y)((z,y)∈τ)

    # ── ⇒ : (∃y)((z,y)∈τ) ⇒ z∈S ──────────────────────────────────────────────
    body = appartient(E.couple(vz, vy), T)
    hb = N.assume(body)
    dj = N.modus_ponens(hb, _disj(s, p, q, "z", "y"))       # FIX(z,y) ou ECH(z,y)
    #   FIX(z,y) : z∈S direct
    hf = N.assume(_fix(vS, vp, vq, vz, vy))
    z_in_fix = conjonction_elim_gauche(conjonction_elim_gauche(hf))   # z∈S
    brF = N.loi_deduction(_fix(vS, vp, vq, vz, vy), z_in_fix)
    #   ECH(z,y) : z=p ou z=q ⇒ z∈S
    he = N.assume(_ech(vp, vq, vz, vy))
    hel = N.assume(et(egal(vz, vp), egal(vy, vq)))          # z=p
    z_in_l = N.modus_ponens(conjonction_elim_gauche(hel), _eq_in(vz, vp, vS, hp_in))   # z∈S
    brEL = N.loi_deduction(et(egal(vz, vp), egal(vy, vq)), z_in_l)
    her = N.assume(et(egal(vz, vq), egal(vy, vp)))          # z=q
    z_in_r = N.modus_ponens(conjonction_elim_gauche(her), _eq_in(vz, vq, vS, hq_in))   # z∈S
    brER = N.loi_deduction(et(egal(vz, vq), egal(vy, vp)), z_in_r)
    z_in_ech = N.loi_deduction(_ech(vp, vq, vz, vy), cas(he, brEL, brER))
    z_in_body = cas(dj, brF, z_in_ech)                     # z∈S  [hyps body, p∈S, q∈S]
    fwd = existe_elimination(N.loi_deduction(body, z_in_body), "y")   # (∃y)((z,y)∈τ) ⇒ z∈S

    # ── ⇐ : z∈S ⇒ (∃y)((z,y)∈τ)  (tiers exclu sur z=p, z=q) ──────────────────
    hzin = N.assume(inS)
    #   branche z=p : témoin y:=q,  (p,q)∈τ  (réécrit p→z)
    pq_in = _couple_in_ech_gauche(s, p, q, vp, vq)         # (p,q)∈τ
    hzp = N.assume(egal(vz, vp))
    p_eq_z = N.modus_ponens(hzp, symetrie(vz, vp))         # p=z
    zq_in = N.modus_ponens(pq_in, _rewrite_couple_gauche(vp, vz, vq, T, p_eq_z))   # (z,q)∈τ
    ex_p = N.modus_ponens(zq_in, N.s5(appartient(E.couple(vz, vy), T), vq, "y"))   # (∃y)((z,y)∈τ)
    brZP = N.loi_deduction(egal(vz, vp), ex_p)
    #   branche ¬(z=p) : sous-cas z=q / ¬(z=q)
    hnzp = N.assume(non(egal(vz, vp)))
    #     z=q : témoin y:=p, (q,p)∈τ rewrite q→z
    qp_in = _couple_in_ech_droite(s, p, q, vq, vp)         # (q,p)∈τ
    hzq = N.assume(egal(vz, vq))
    q_eq_z = N.modus_ponens(hzq, symetrie(vz, vq))         # q=z
    zp_in = N.modus_ponens(qp_in, _rewrite_couple_gauche(vq, vz, vp, T, q_eq_z))   # (z,p)∈τ
    ex_q = N.modus_ponens(zp_in, N.s5(appartient(E.couple(vz, vy), T), vp, "y"))
    brZQ = N.loi_deduction(egal(vz, vq), ex_q)
    #     ¬(z=q) : z fixe, (z,z)∈τ via FIX
    hnzq = N.assume(non(egal(vz, vq)))
    fix_zz = conjonction_intro(conjonction_intro(hzin, N.reflexivite(vz)),
                               conjonction_intro(hnzp, hnzq))   # FIX(z,z)
    fix_or_ech = N.modus_ponens(fix_zz, N.s2(_fix(vS, vp, vq, vz, vz), _ech(vp, vq, vz, vz)))
    zz_in = N.modus_ponens(fix_or_ech, _into(s, p, q, vz, vz))   # (z,z)∈τ
    ex_fix = N.modus_ponens(zz_in, N.s5(appartient(E.couple(vz, vy), T), vz, "y"))
    brNZQ = N.loi_deduction(non(egal(vz, vq)), ex_fix)
    # combiner les sous-cas de ¬(z=p)
    sous_nzp = cas(tiers_exclu(egal(vz, vq)), brZQ, brNZQ)   # (∃y)…   [hyps z∈S, ¬(z=p)]
    brNZP = N.loi_deduction(non(egal(vz, vp)), sous_nzp)
    ex_all = cas(tiers_exclu(egal(vz, vp)), brZP, brNZP)     # (∃y)…   [hyp z∈S]
    bwd = N.loi_deduction(inS, ex_all)

    # ── extensionnalité : z∈dom τ ⇔ (∃y)((z,y)∈τ) ⇔ z∈S ──────────────────────
    ax_dom = N.axiome(E.theorie_ensembles(), E.AXIOME_DOM)
    dom_car = instancie(instancie(ax_dom, T), vz)          # z∈dom τ ⇔ (∃y)((z,y)∈τ)
    ex_iff_inS = conjonction_intro(fwd, bwd)               # (∃y)((z,y)∈τ) ⇔ z∈S
    chain = equivalence_transitivite(dom_car, ex_iff_inS)  # z∈dom τ ⇔ z∈S  [hyps p∈S,q∈S]
    char_dom = N.generalisation("z", chain)
    selfS = N.generalisation("z", conjonction_intro(a_implique_a(inS), a_implique_a(inS)))
    eq = egalite_par_extension(char_dom, selfS, E.dom(T), vS)   # dom τ = S  [hyps p∈S,q∈S]
    return N.loi_deduction(hyp, eq)


def _eq_in(vz, va, vS, thm_a_in):
    """{a∈S} ⊢ z=a ⇒ z∈S   (Leibniz : z=a réécrit a∈S en z∈S)."""
    hza = N.assume(egal(vz, va))
    a_eq_z = N.modus_ponens(hza, symetrie(vz, va))         # a=z
    leib = N.modus_ponens(a_eq_z, N.s6(va, vz, "w", appartient(var("w"), vS)))   # (a∈S)⇔(z∈S)
    return N.loi_deduction(egal(vz, va), N.modus_ponens(thm_a_in, equivalence_avant(leib)))


def _rewrite_couple_gauche(va, vz, vimg, T, thm_a_eq_z):
    """{a=z} ⊢ (a,img)∈τ ⇒ (z,img)∈τ   (Leibniz sur la 1ʳᵉ coordonnée du couple)."""
    leib = N.modus_ponens(thm_a_eq_z,
        N.s6(va, vz, "w", appartient(E.couple(var("w"), vimg), T)))   # (a,img)∈τ ⇔ (z,img)∈τ
    return equivalence_avant(leib)


__all__ = ["transpo", "transpo_membre", "transpo_fonctionnel", "transpo_domaine",
           "transpo_injective", "transpo_image", "transpo_valeur_q",
           "transposition_existe"]
