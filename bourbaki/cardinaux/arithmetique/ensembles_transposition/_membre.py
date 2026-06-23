"""§III.3 — Appartenance au graphe de la TRANSPOSITION τ_{S,p,q}.

τ := (Δ_S ∖ {(p,p),(q,q)}) ∪ {(p,q),(q,p)}.

LEMME CLÉ (`transpo_membre`) :
    (x,y) ∈ τ  ⇔  ( ((x∈S et x=y) et (¬(x=p) et ¬(x=q)))   « point fixe ≠ p,q »
                    ou ((x=p et y=q) ou (x=q et y=p)) ).    « échange p↔q »

Dérivé via AXIOME_REUNION (∪), AXIOME_DIFF (∖), diagonale_membre (Δ_S), AXIOME_PAIRE
({a,b}), et la Proposition 1 sur les couples (couple_egal_implique_composantes).
On simplifie ¬((x,y)=(p,p)) sous x=y en ¬(x=p) (et de même q).
"""
from __future__ import annotations

from bourbaki.logique.formule import Terme, var, egal, et, ou, non, appartient
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.tactiques.tactiques_abrege import a_implique_a
from bourbaki.logique.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, equivalence_transitivite,
    equivalence_symetrie, et_congruence_gauche, et_congruence_droite,
    ou_congruence, instancie, cas)
from bourbaki.logique.tactiques.tactiques_abrege_egalite import (
    symetrie, composer_egalites, congruence_terme)
from bourbaki.ensembles.ii_2_couples_produit.ensembles_couples import (
    couple_egal_implique_composantes, membre_paire_gauche, membre_paire_droite)
from bourbaki.cardinaux.ensembles_equipotence import diagonale_membre


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def transpo(s, p, q):
    """τ_{S,p,q} := (Δ_S ∖ {(p,p),(q,q)}) ∪ {(p,q),(q,p)}   (terme de la transposition).

    Δ_S MODIFIÉE en 2 points : on retire les paires fixes de p, q et on ajoute les
    deux paires croisées.  Termes p, q ; S nom ou terme."""
    vS, vp, vq = _t(s), _t(p), _t(q)
    DS = E.diagonale(vS)
    enleves = E.paire(E.couple(vp, vp), E.couple(vq, vq))   # {(p,p),(q,q)}
    ajoutes = E.paire(E.couple(vp, vq), E.couple(vq, vp))   # {(p,q),(q,p)}
    return E.reunion(E.difference(DS, enleves), ajoutes)


def _couple_eg_si(vx, vy, va, vb):
    """⊢ (x=a et y=b) ⇒ ((x,y)=(a,b))  (sens facile Prop 1, version TERME, congruence)."""
    w = var("w")
    hyp = et(egal(vx, va), egal(vy, vb))
    h = N.assume(hyp)
    exx = conjonction_elim_gauche(h)                        # x=a
    eyy = conjonction_elim_droite(h)                        # y=b
    e1 = N.modus_ponens(exx, congruence_terme(vx, va, E.couple(w, vy)))   # (x,y)=(a,y)
    e2 = N.modus_ponens(eyy, congruence_terme(vy, vb, E.couple(va, w)))   # (a,y)=(a,b)
    return N.loi_deduction(hyp, composer_egalites(e1, e2))  # (x=a et y=b) ⇒ (x,y)=(a,b)


def _paire_couple_membre(z, c1, c2):
    """⊢ (z ∈ {c1,c2}) ⇔ (z=c1 ou z=c2).   (instance de AXIOME_PAIRE.)"""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_PAIRE)
    return instancie(instancie(instancie(ax, c1), c2), z)


def _eq_couple_simplifie(x, y, a):
    """⊢ ((x,y) = (a,a)) ⇔ (x=a et y=a).   (Proposition 1 sur les couples, ⇔.)

    ⇒ : couple_egal_implique_composantes ; ⇐ : couple_egal_si_composantes."""
    vx, vy, va = _t(x), _t(y), _t(a)
    fwd = couple_egal_implique_composantes(vx, vy, va, va)   # (x,y)=(a,a) ⇒ (x=a et y=a)
    bwd = _couple_eg_si(vx, vy, va, va)                      # (x=a et y=a) ⇒ (x,y)=(a,a)
    return conjonction_intro(fwd, bwd)


def transpo_membre(s="S", p="p", q="q", x="x", y="y"):
    """⊢ ((x,y) ∈ τ) ⇔ ( ((x∈S et x=y) et (¬(x=p) et ¬(x=q)))
                          ou ((x=p et y=q) ou (x=q et y=p)) ).

    LEMME CLÉ.  τ = (Δ_S∖{(p,p),(q,q)}) ∪ {(p,q),(q,p)}.  Par AXIOME_REUNION,
    (x,y)∈τ ⇔ (x,y)∈(Δ_S∖…) ou (x,y)∈{(p,q),(q,p)}.  Membre gauche : AXIOME_DIFF +
    diagonale_membre + AXIOME_PAIRE + de Morgan, et la simplification ¬((x,y)=(p,p))
    ⇔ ¬(x=p) (sous x=y, _sous_eq_neg_simplifie).  Membre droit : AXIOME_PAIRE +
    Proposition 1 sur les couples ((x,y)=(p,q) ⇔ (x=p et y=q))."""
    vS, vp, vq = _t(s), _t(p), _t(q)
    vx, vy = _t(x), _t(y)
    z = E.couple(vx, vy)
    DS = E.diagonale(vS)
    enleves = E.paire(E.couple(vp, vp), E.couple(vq, vq))   # {(p,p),(q,q)}
    ajoutes = E.paire(E.couple(vp, vq), E.couple(vq, vp))   # {(p,q),(q,p)}
    M = E.difference(DS, enleves)
    T = E.reunion(M, ajoutes)

    # (1) AXIOME_REUNION : z∈τ ⇔ (z∈M ou z∈{(p,q),(q,p)})
    ax_reu = N.axiome(E.theorie_ensembles(), E.AXIOME_REUNION)
    reu = instancie(instancie(instancie(ax_reu, M), ajoutes), z)   # z∈M∪aj ⇔ (z∈M ou z∈aj)

    # (2) membre GAUCHE : z∈M ⇔ ((x∈S et x=y) et (¬(x=p) et ¬(x=q)))
    # 2a. AXIOME_DIFF : z∈M ⇔ (z∈Δ_S et ¬(z∈{(p,p),(q,q)}))
    ax_diff = N.axiome(E.theorie_ensembles(), E.AXIOME_DIFF)
    diff = instancie(instancie(instancie(ax_diff, DS), enleves), z)   # z∈M ⇔ (z∈Δ et ¬(z∈enl))
    # 2b. diagonale_membre : z∈Δ_S ⇔ (x∈S et x=y)
    dm = _diag_membre_terme(vS, vx, vy)
    # 2c. z∈{(p,p),(q,q)} ⇔ (z=(p,p) ou z=(q,q))
    paire_enl = _paire_couple_membre(z, E.couple(vp, vp), E.couple(vq, vq))
    # ¬(z∈enl) ⇔ ¬(z=(p,p) ou z=(q,q)) ⇔ (¬(z=(p,p)) et ¬(z=(q,q)))   [de Morgan]
    from bourbaki.logique.tactiques.tactiques_abrege2 import equiv_neg, demorgan_ou
    neg_paire = equiv_neg(paire_enl)                        # ¬(z∈enl) ⇔ ¬(z=(p,p) ou z=(q,q))
    dem = demorgan_ou(egal(z, E.couple(vp, vp)), egal(z, E.couple(vq, vq)))  # ¬(.. ou ..) ⇔ (¬.. et ¬..)
    neg_enl = equivalence_transitivite(neg_paire, dem)      # ¬(z∈enl) ⇔ (¬(z=(p,p)) et ¬(z=(q,q)))
    # assemble : z∈M ⇔ ((x∈S et x=y) et (¬(z=(p,p)) et ¬(z=(q,q))))
    left1 = et_congruence_gauche(dm, non(appartient(z, enleves)))   # (z∈Δ et ¬(z∈enl)) ⇔ ((x∈S et x=y) et ¬(z∈enl))
    left2 = et_congruence_droite(et(appartient(vx, vS), egal(vx, vy)), neg_enl)
    #   ((x∈S et x=y) et ¬(z∈enl)) ⇔ ((x∈S et x=y) et (¬(z=(p,p)) et ¬(z=(q,q))))
    M_raw = equivalence_transitivite(diff, equivalence_transitivite(left1, left2))
    #   z∈M ⇔ ((x∈S et x=y) et (¬((x,y)=(p,p)) et ¬((x,y)=(q,q))))

    # 2d. simplifier ¬((x,y)=(p,p)) ⇔ ¬(x=p) sous x=y, idem q ; conditionner sur x=y
    #     (x∈S et x=y) garantit x=y.  On prouve l'équivalence du conjoint droit SOUS x=y,
    #     puis on l'intègre (et_congruence_droite avec antécédent (x∈S et x=y)).
    # Forme à transformer : ((x∈S et x=y) et (¬((x,y)=(p,p)) et ¬((x,y)=(q,q))))
    #                     ⇔ ((x∈S et x=y) et (¬(x=p) et ¬(x=q)))
    Pleft = et(appartient(vx, vS), egal(vx, vy))            # x∈S et x=y
    np_pp = non(egal(z, E.couple(vp, vp)))
    np_qq = non(egal(z, E.couple(vq, vq)))
    np_p = non(egal(vx, vp))
    np_q = non(egal(vx, vq))
    # sous hypothèse Pleft (qui donne x=y) : (¬((x,y)=(p,p)) et ¬((x,y)=(q,q))) ⇔ (¬(x=p) et ¬(x=q))
    hP = N.assume(Pleft)
    xy = conjonction_elim_droite(hP)                        # x=y
    simp_p = _neg_couple_eq_via_xy(vx, vy, vp, xy)          # ¬((x,y)=(p,p)) ⇔ ¬(x=p)
    simp_q = _neg_couple_eq_via_xy(vx, vy, vq, xy)          # ¬((x,y)=(q,q)) ⇔ ¬(x=q)
    cong_droit = equivalence_transitivite(
        et_congruence_gauche(simp_p, np_qq),               # (¬pp et ¬qq) ⇔ (¬p et ¬qq)
        et_congruence_droite(np_p, simp_q))                # (¬p et ¬qq) ⇔ (¬p et ¬q)
    # cong_droit : {x=y} ⊢ (¬pp et ¬qq) ⇔ (¬p et ¬q)
    # Intègre dans la conjonction avec Pleft : sous Pleft on a x=y, donc:
    # ((x∈S et x=y) et (¬pp et ¬qq)) ⇔ ((x∈S et x=y) et (¬p et ¬q))
    simp_full = _et_congruence_droite_sous(Pleft, et(np_pp, np_qq), et(np_p, np_q), cong_droit)
    M_eq = equivalence_transitivite(M_raw, simp_full)       # z∈M ⇔ ((x∈S et x=y) et (¬(x=p) et ¬(x=q)))

    # (3) membre DROIT : z∈{(p,q),(q,p)} ⇔ ((x=p et y=q) ou (x=q et y=p))
    paire_aj = _paire_couple_membre(z, E.couple(vp, vq), E.couple(vq, vp))   # ⇔ (z=(p,q) ou z=(q,p))
    eq_pq = _eq_couple_general(vx, vy, vp, vq)              # (x,y)=(p,q) ⇔ (x=p et y=q)
    eq_qp = _eq_couple_general(vx, vy, vq, vp)              # (x,y)=(q,p) ⇔ (x=q et y=p)
    aj_eq = equivalence_transitivite(paire_aj, ou_congruence(eq_pq, eq_qp))
    #   z∈aj ⇔ ((x=p et y=q) ou (x=q et y=p))

    # (4) recoller : z∈τ ⇔ (z∈M ou z∈aj) ⇔ (Mcible ou ajcible)
    big = ou_congruence(M_eq, aj_eq)                        # (z∈M ou z∈aj) ⇔ (Mcible ou ajcible)
    return equivalence_transitivite(reu, big)


def _diag_membre_terme(vS, vx, vy):
    """⊢ ((x,y) ∈ Δ_S) ⇔ (x∈S et x=y)  pour S terme quelconque.

    diagonale_membre n'accepte qu'un NOM pour S ; on généralise sur X puis instancie
    au terme S (les liants internes u,v,d0 de l'énoncé ne figurent pas dans S)."""
    # généraliser diagonale_membre sur X, u, v puis instancier (X, x, y)
    gen = N.generalisation("X", N.generalisation("u", N.generalisation("v",
        diagonale_membre("X", "u", "v"))))
    return instancie(instancie(instancie(gen, vS), vx), vy)


def _eq_couple_general(x, y, a, b):
    """⊢ ((x,y) = (a,b)) ⇔ (x=a et y=b).   (Proposition 1, version ⇔, termes.)"""
    vx, vy, va, vb = _t(x), _t(y), _t(a), _t(b)
    fwd = couple_egal_implique_composantes(vx, vy, va, vb)
    bwd = _couple_eg_si(vx, vy, va, vb)
    return conjonction_intro(fwd, bwd)


def _neg_couple_eq_via_xy(vx, vy, va, thm_xy):
    """{x=y} ⊢ ¬((x,y)=(a,a)) ⇔ ¬(x=a).   (thm_xy : preuve de x=y, déjà sous hyp.)

    (x,y)=(a,a) ⇔ (x=a et y=a) [Prop 1] ; sous x=y, (x=a et y=a) ⇔ x=a ; congruence ¬."""
    from bourbaki.logique.tactiques.tactiques_abrege2 import equiv_neg
    eq_simp = _eq_couple_simplifie(vx, vy, va)              # (x,y)=(a,a) ⇔ (x=a et y=a)
    # sous x=y : (x=a et y=a) ⇔ x=a, en utilisant thm_xy (déjà dérivé sous hyp)
    h1 = N.assume(et(egal(vx, va), egal(vy, va)))
    fwd = N.loi_deduction(et(egal(vx, va), egal(vy, va)), conjonction_elim_gauche(h1))
    h2 = N.assume(egal(vx, va))
    y_eq_x = N.modus_ponens(thm_xy, symetrie(vx, vy))       # y=x   [hyp x=y]
    y_eq_a = composer_egalites(y_eq_x, h2)                  # y=a
    bwd = N.loi_deduction(egal(vx, va), conjonction_intro(h2, y_eq_a))
    sous = conjonction_intro(fwd, bwd)                     # {x=y} ⊢ (x=a et y=a) ⇔ x=a
    chain = equivalence_transitivite(eq_simp, sous)        # {x=y} ⊢ (x,y)=(a,a) ⇔ x=a
    return equiv_neg(chain)                                # ¬((x,y)=(a,a)) ⇔ ¬(x=a)


def _et_congruence_droite_sous(p, q, qp, thm_eq_sous_p):
    """⊢ (P et Q) ⇔ (P et Q')  où la preuve de (Q⇔Q') a P comme hypothèse.

    Variante de et_congruence_droite tolérant que l'équivalence du conjoint droit
    dépende de P : sous P on a Q⇔Q', donc (P et Q)⇒(P et Q') et réciproquement.
    thm_eq_sous_p : {P} ⊢ (Q ⇔ Q')."""
    hf = N.assume(et(p, q))
    pf = conjonction_elim_gauche(hf)                       # P  (décharge l'hyp P de thm_eq)
    eq_f = N.modus_ponens(pf, N.loi_deduction(p, thm_eq_sous_p))   # ⊢ (Q⇔Q')  [hyp (P et Q)]
    fwd = N.loi_deduction(et(p, q), conjonction_intro(
        pf, N.modus_ponens(conjonction_elim_droite(hf), equivalence_avant(eq_f))))
    hb = N.assume(et(p, qp))
    pb = conjonction_elim_gauche(hb)
    eq_b = N.modus_ponens(pb, N.loi_deduction(p, thm_eq_sous_p))
    bwd = N.loi_deduction(et(p, qp), conjonction_intro(
        pb, N.modus_ponens(conjonction_elim_droite(hb), equivalence_arriere(eq_b))))
    return conjonction_intro(fwd, bwd)


__all__ = ["transpo", "transpo_membre"]
