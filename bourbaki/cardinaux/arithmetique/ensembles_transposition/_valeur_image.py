"""§III.3 — La TRANSPOSITION τ_{S,p,q} : valeur τ(q)=p et image(τ,S)=S.

  • transpo_valeur_q : (p∈S et q∈S et ¬(p=q)) ⇒ τ(q) = p   (l'échange envoie q sur p) ;
  • transpo_image    : (p∈S et q∈S et ¬(p=q)) ⇒ image(τ, S) = S   (τ surjective sur S).

Calques :  transpo_valeur_q ← diagonale_valeur (caractérisation de la valeur C46) ;
           transpo_image    ← diagonale_image (double inclusion par extension).

(q,p)∈τ par la branche ECH droite (réutilisée de _bijection : _couple_in_ech_droite),
les égalités q=q, p=p étant réflexives.  De là τ(q)=p (fonctionnalité + C46) et la
surjectivité (tout y∈S est atteint : p←q, q←p, sinon y←y)."""
from __future__ import annotations

from bourbaki.logique.formule import (Terme, var, egal, et, ou, non, appartient,
                                       existe)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.tactiques.tactiques_abrege import a_implique_a
from bourbaki.logique.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, equivalence_transitivite,
    instancie, cas, tiers_exclu)
from bourbaki.logique.tactiques.tactiques_abrege_egalite import (
    symetrie, composer_egalites)
from bourbaki.logique.tactiques.tactiques_abrege_quantif import existe_elimination
from bourbaki.ensembles.fonctions.ii_3_4_fonctions_valeur.ensembles_fonctions import valeur_caracterisation
from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_theoremes import egalite_par_extension
from bourbaki.cardinaux.arithmetique.ensembles_transposition._membre import (
    transpo, transpo_membre)
from bourbaki.cardinaux.arithmetique.ensembles_transposition._bijection import (
    transpo_fonctionnel, _disj, _into, _fix, _ech,
    _couple_in_ech_gauche, _couple_in_ech_droite, _eq_in, _rewrite_couple_gauche)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# ═══════════════════════════════════════════════════════════════════════════════
# transpo_valeur_q :  (p∈S et q∈S et ¬(p=q)) ⇒ τ(q) = p
# ═══════════════════════════════════════════════════════════════════════════════
def transpo_valeur_q(s="S", p="p", q="q"):
    """⊢ (p∈S et q∈S et ¬(p=q)) ⇒ (τ_{S,p,q}(q) = p).   (l'échange envoie q sur p.)

    (q,p)∈τ (branche ECH droite, q=q/p=p réflexifs) ⇒ (∃y)((q,y)∈τ) ; sous τ
    fonctionnel (transpo_fonctionnel, via ¬(p=q)), C46 donne ((q,p)∈τ) ⇔ (p=τ(q)),
    d'où p=τ(q), symétrie ⇒ τ(q)=p.  (p,q∈S non requis pour (q,p)∈τ, mais conservés
    pour la signature uniforme.)"""
    vS, vp, vq = _t(s), _t(p), _t(q)
    T = transpo(vS, vp, vq)
    vy = var("y")
    pin, qin, npq = appartient(vp, vS), appartient(vq, vS), non(egal(vp, vq))
    hyp = et(et(pin, qin), npq)

    qp_in = _couple_in_ech_droite(s, p, q, vq, vp)             # (q,p)∈τ   (inconditionnel)
    exy = N.modus_ponens(qp_in, N.s5(appartient(E.couple(vq, vy), T), vp, "y"))   # (∃y)((q,y)∈τ)
    # C46 : {τ fonctionnel, (∃y)((q,y)∈τ)} ⊢ ((q,y)∈τ) ⇔ (y=τ(q))  → instancier y:=p
    vc = instancie(N.generalisation("y", valeur_caracterisation(T, vq)), vp)   # ((q,p)∈τ)⇔(p=τ(q))  [hyps]
    p_eq = N.modus_ponens(qp_in, equivalence_avant(vc))        # p=τ(q)   [hyps: τ func, (∃y)…]
    # couper (∃y)…  (de (q,p)∈τ)
    p_eq = N.modus_ponens(exy, N.loi_deduction(
        existe("y", appartient(E.couple(vq, vy), T)), p_eq))   # p=τ(q)   [hyp: τ func]
    # couper τ fonctionnel  (transpo_fonctionnel : ¬(p=q) ⇒ est_fonctionnel(τ))
    func = N.modus_ponens(N.assume(npq), transpo_fonctionnel(s, p, q))   # est_fonctionnel(τ)  [hyp ¬(p=q)]
    p_eq = N.modus_ponens(func, N.loi_deduction(E.est_fonctionnel(T), p_eq))   # p=τ(q)  [hyp ¬(p=q)]
    val_eq = N.modus_ponens(p_eq, symetrie(vp, E.valeur(T, vq)))   # τ(q)=p   [hyp ¬(p=q)]
    # décharger ¬(p=q), ré-introduire depuis hyp
    g = N.loi_deduction(npq, val_eq)                           # ⊢ ¬(p=q) ⇒ (τ(q)=p)
    hfull = N.assume(hyp)
    npq2 = conjonction_elim_droite(hfull)
    return N.loi_deduction(hyp, N.modus_ponens(npq2, g))       # (p∈S et q∈S et ¬(p=q)) ⇒ τ(q)=p


# ═══════════════════════════════════════════════════════════════════════════════
# transpo_image :  (p∈S et q∈S et ¬(p=q)) ⇒ image(τ, S) = S
# ═══════════════════════════════════════════════════════════════════════════════
def _eq_couple_in(s, p, q, va, vb, vz, thm_b_eq_z, ab_in):
    """{b=z} ⊢ (a,z)∈τ   à partir de (a,b)∈τ  (Leibniz sur la 2ᵉ coordonnée).

    thm_b_eq_z : preuve de b=z ;  ab_in : preuve de (a,b)∈τ.  Réécrit b→z."""
    vS = _t(s)
    T = transpo(vS, _t(p), _t(q))
    leib = N.modus_ponens(thm_b_eq_z,
        N.s6(vb, vz, "w", appartient(E.couple(va, var("w")), T)))   # (a,b)∈τ ⇔ (a,z)∈τ
    return N.modus_ponens(ab_in, equivalence_avant(leib))          # (a,z)∈τ


def transpo_image(s="S", p="p", q="q"):
    """⊢ (p∈S et q∈S et ¬(p=q)) ⇒ (image(τ_{S,p,q}, S) = S).   (τ surjective sur S.)

    z∈τ⟨S⟩ ⇔ (∃t)(t∈S et (t,z)∈τ) ⇔ z∈S, par extension.
      ⊂ : (t,z)∈τ ⇒ FIX(t,z) (z=t∈S) ou ECH(t,z) (z=q ou z=p, ∈S) ;
      ⊃ : z∈S est atteint — z=p←q (q,p)∈τ ; z=q←p (p,q)∈τ ; sinon z←z (z,z)∈τ (FIX)."""
    from bourbaki.logique.tactiques.tactiques_abrege_quantif import (alpha_existe,
                                                                     congruence_existe)
    vS, vp, vq = _t(s), _t(p), _t(q)
    vz, vt, vy = var("z"), var("t"), var("y")
    T = transpo(vS, vp, vq)
    pin, qin, npq = appartient(vp, vS), appartient(vq, vS), non(egal(vp, vq))
    hyp = et(et(pin, qin), npq)
    inS = appartient(vz, vS)

    hp = N.assume(pin)
    hq = N.assume(qin)

    # caractérisation de l'image : z∈τ⟨S⟩ ⇔ (∃t)(t∈S et (t,z)∈τ)   (AXIOME_IMAGE, renommé x→t)
    ax_img = N.axiome(E.theorie_ensembles(), E.AXIOME_IMAGE)
    img0 = instancie(instancie(instancie(ax_img, T), vS), vz)      # z∈τ⟨S⟩ ⇔ (∃x)(x∈S et (x,z)∈τ)
    inner_x = et(appartient(var("x"), vS), appartient(E.couple(var("x"), vz), T))
    ren = alpha_existe("x", "t", inner_x)                          # (∃x)… ⇔ (∃t)…
    img_car = equivalence_transitivite(img0, ren)                  # z∈τ⟨S⟩ ⇔ (∃t)(t∈S et (t,z)∈τ)

    # ── ⇒ : (∃t)(t∈S et (t,z)∈τ) ⇒ z∈S ──────────────────────────────────────────
    body = et(appartient(vt, vS), appartient(E.couple(vt, vz), T))
    hb = N.assume(body)
    t_inS = conjonction_elim_gauche(hb)                            # t∈S
    dj = N.modus_ponens(conjonction_elim_droite(hb), _disj(s, p, q, vt, vz))   # FIX(t,z) ou ECH(t,z)
    #   FIX(t,z) : t=z, t∈S ⇒ z∈S  (z=t)
    hf = N.assume(_fix(vS, vp, vq, vt, vz))
    t_eq_z = conjonction_elim_droite(conjonction_elim_gauche(hf))  # t=z
    z_inS_fix = N.modus_ponens(t_inS, equivalence_avant(N.modus_ponens(
        t_eq_z, N.s6(vt, vz, "w", appartient(var("w"), vS)))))     # z∈S
    brF = N.loi_deduction(_fix(vS, vp, vq, vt, vz), z_inS_fix)
    #   ECH(t,z) : (t=p,z=q) ⇒ z=q∈S ; (t=q,z=p) ⇒ z=p∈S
    he = N.assume(_ech(vp, vq, vt, vz))
    hel = N.assume(et(egal(vt, vp), egal(vz, vq)))                 # z=q
    z_in_l = N.modus_ponens(conjonction_elim_droite(hel), _eq_in(vz, vq, vS, hq))   # z∈S
    brEL = N.loi_deduction(et(egal(vt, vp), egal(vz, vq)), z_in_l)
    her = N.assume(et(egal(vt, vq), egal(vz, vp)))                 # z=p
    z_in_r = N.modus_ponens(conjonction_elim_droite(her), _eq_in(vz, vp, vS, hp))   # z∈S
    brER = N.loi_deduction(et(egal(vt, vq), egal(vz, vp)), z_in_r)
    z_in_ech = N.loi_deduction(_ech(vp, vq, vt, vz), cas(he, brEL, brER))
    z_in_body = cas(dj, brF, z_in_ech)                             # z∈S  [hyps body, p∈S, q∈S]
    fwd = existe_elimination(N.loi_deduction(body, z_in_body), "t")   # (∃t)(t∈S et (t,z)∈τ) ⇒ z∈S

    # ── ⇐ : z∈S ⇒ (∃t)(t∈S et (t,z)∈τ)   (cas z=p / z=q / sinon) ─────────────────
    hzin = N.assume(inS)
    #   z=p : témoin t:=q, (q,p)∈τ → (q,z)∈τ ; q∈S
    qp_in = _couple_in_ech_droite(s, p, q, vq, vp)                 # (q,p)∈τ
    hzp = N.assume(egal(vz, vp))
    p_eq_z = N.modus_ponens(hzp, symetrie(vz, vp))                 # p=z
    qz_in = _eq_couple_in(s, p, q, vq, vp, vz, p_eq_z, qp_in)      # (q,z)∈τ
    wit_p = conjonction_intro(hq, qz_in)                           # q∈S et (q,z)∈τ
    ex_p = N.modus_ponens(wit_p, N.s5(et(appartient(vt, vS), appartient(E.couple(vt, vz), T)), vq, "t"))
    brZP = N.loi_deduction(egal(vz, vp), ex_p)
    #   ¬(z=p) : sous-cas z=q / ¬(z=q)
    hnzp = N.assume(non(egal(vz, vp)))
    #     z=q : témoin t:=p, (p,q)∈τ → (p,z)∈τ ; p∈S
    pq_in = _couple_in_ech_gauche(s, p, q, vp, vq)                 # (p,q)∈τ
    hzq = N.assume(egal(vz, vq))
    q_eq_z = N.modus_ponens(hzq, symetrie(vz, vq))                 # q=z
    pz_in = _eq_couple_in(s, p, q, vp, vq, vz, q_eq_z, pq_in)      # (p,z)∈τ
    wit_q = conjonction_intro(hp, pz_in)                           # p∈S et (p,z)∈τ
    ex_q = N.modus_ponens(wit_q, N.s5(et(appartient(vt, vS), appartient(E.couple(vt, vz), T)), vp, "t"))
    brZQ = N.loi_deduction(egal(vz, vq), ex_q)
    #     ¬(z=q) : z fixe, (z,z)∈τ via FIX ; z∈S
    hnzq = N.assume(non(egal(vz, vq)))
    fix_zz = conjonction_intro(conjonction_intro(hzin, N.reflexivite(vz)),
                               conjonction_intro(hnzp, hnzq))      # FIX(z,z)
    fix_or_ech = N.modus_ponens(fix_zz, N.s2(_fix(vS, vp, vq, vz, vz), _ech(vp, vq, vz, vz)))
    zz_in = N.modus_ponens(fix_or_ech, _into(s, p, q, vz, vz))     # (z,z)∈τ
    wit_z = conjonction_intro(hzin, zz_in)                         # z∈S et (z,z)∈τ
    ex_z = N.modus_ponens(wit_z, N.s5(et(appartient(vt, vS), appartient(E.couple(vt, vz), T)), vz, "t"))
    brNZQ = N.loi_deduction(non(egal(vz, vq)), ex_z)
    sous_nzp = cas(tiers_exclu(egal(vz, vq)), brZQ, brNZQ)         # (∃t)…  [hyps z∈S,¬(z=p),p∈S,q∈S]
    brNZP = N.loi_deduction(non(egal(vz, vp)), sous_nzp)
    ex_all = cas(tiers_exclu(egal(vz, vp)), brZP, brNZP)           # (∃t)…  [hyps z∈S,p∈S,q∈S]
    bwd = N.loi_deduction(inS, ex_all)                             # z∈S ⇒ (∃t)(t∈S et (t,z)∈τ)

    # ── extensionnalité : z∈τ⟨S⟩ ⇔ (∃t)(t∈S et (t,z)∈τ) ⇔ z∈S ───────────────────
    ex_iff_inS = conjonction_intro(fwd, bwd)                       # (∃t)… ⇔ z∈S
    chain = equivalence_transitivite(img_car, ex_iff_inS)          # z∈τ⟨S⟩ ⇔ z∈S  [hyps p∈S,q∈S]
    char_img = N.generalisation("z", chain)
    selfS = N.generalisation("z", conjonction_intro(a_implique_a(inS), a_implique_a(inS)))
    eq = egalite_par_extension(char_img, selfS, E.image(T, vS), vS)   # image(τ,S)=S  [hyps p∈S,q∈S]
    # décharger p∈S, q∈S puis ré-introduire depuis hyp
    g1 = N.loi_deduction(qin, N.loi_deduction(pin, eq))            # ⊢ q∈S ⇒ (p∈S ⇒ image(τ,S)=S)
    hfull = N.assume(hyp)
    pin2 = conjonction_elim_gauche(conjonction_elim_gauche(hfull))
    qin2 = conjonction_elim_droite(conjonction_elim_gauche(hfull))
    img = N.modus_ponens(pin2, N.modus_ponens(qin2, g1))           # image(τ,S)=S  [hyp hyp]
    return N.loi_deduction(hyp, img)                               # (p∈S et q∈S et ¬(p=q)) ⇒ image(τ,S)=S


__all__ = ["transpo_valeur_q", "transpo_image"]
