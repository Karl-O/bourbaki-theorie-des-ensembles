"""§III.7.6 Prop. 6, 3° — critère d'injectivité de u : lim→ E_α → F.

────────────────────────────────────────────────────────────────────────────────
« Pour que u soit injective, il faut et il suffit que pour tout α∈I, les
relations x∈E_α, y∈E_α, u_α(x)=u_α(y) entraînent qu'il existe β≥α pour lequel
f_βα(x)=f_βα(y) »  (E III.62-63).  Démontré ICI DANS LES DEUX SENS :

  { (24) au point,  f_α⟨E_α⟩⊂E,
    lemme 1 apparié « deux éléments de E s'écrivent f_α(x), f_α(y) MÊME α »,
    lemme 2 « f_α(x)=f_α(y) ⇔ (∃β≥α) f_βα(x)=f_βα(y) » }
      ⊢  injective_ponctuelle(u, E)  ⇔  critere_injectivite(u_α, f)

⇒ : u_α(x)=u_α(y) donne u(f_α(x))=u(f_α(y)) [(24)] donc f_α(x)=f_α(y)
    [injectivité, les deux étant dans E], donc ∃β [lemme 2, sens →].
⇐ : z,z'∈E s'écrivent f_α(x), f_α(y) MÊME α [lemme 1 apparié — c'est là que
    sert « I filtrant »] ; u(z)=u(z') donne u_α(x)=u_α(y) [(24)], le critère
    donne ∃β, le lemme 2 (sens ←) rend f_α(x)=f_α(y), d'où z=z'.
⚠️ liants : témoins « ai »/« xi »/« yi », universelles « zi »/« zj », trous
« w6a »/« w6b » (jamais « y » : valeur(G,·) est un τy).
INVARIANT : theorie_ensembles()=22 ; rien postulé.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, et, impl, equiv, appartient, existe, pourtout,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, instancie,
)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import (
    existe_elimination,
)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
    symetrie, composer_egalites, congruence_terme,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.fondations.ensembles_graphe_de import (
    graphe_de,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites import (
    ensembles_limites as L, ensembles_limites_canoniques as C,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites.prop6.ensembles_prop6_unicite import (
    relation_24_au_point,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites.prop6.ensembles_prop6_surjectif import (
    hyp_canonique_arrive,
)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def _prem3(vE, vi, va, vx, vy):
    """a∈I et x∈E_a et y∈E_a  (associée à gauche)."""
    Ea = E.valeur_famille(vE, va)
    return et(et(appartient(va, vi), appartient(vx, Ea)), appartient(vy, Ea))


def _ex_beta(vf, vi, leq, va, vx, vy, b="bi"):
    """(∃b)( (b∈I et a≤b) et f_ba(x) = f_ba(y) )  — la conclusion du critère."""
    vb = var(b)
    fba = L.appl_ind(vf, vb, va)                       # f_{βα}
    return existe(b, et(et(appartient(vb, vi), leq(va, vb)),
                        egal(L.transition_valeur(fba, vx),
                             L.transition_valeur(fba, vy))))


def injective_ponctuelle(u, lim, z="zi", zp="zj"):
    """(∀z)(∀z')( (z∈E et z'∈E et u(z)=u(z')) ⇒ z=z' )  — u injective sur E."""
    vu, vlim = _t(u), _t(lim)
    vz, vzp = var(z), var(zp)
    gu = graphe_de(vu)
    return pourtout(z, pourtout(zp, impl(
        et(et(appartient(vz, vlim), appartient(vzp, vlim)),
           egal(E.valeur(gu, vz), E.valeur(gu, vzp))),
        egal(vz, vzp))))


# @livre Ch.III §7.6 Prop.6 | E III.62 L.36-40 | PDF p.165  (condition 3° : u_α(x)=u_α(y) ⇒ (∃β≥α) f_βα(x)=f_βα(y))
def critere_injectivite(uf, f, Efam, i, leq=None, a="ai", x="xi", y="yi"):
    """(∀a)(∀x)(∀y)( (a∈I et x∈E_a et y∈E_a et u_a(x)=u_a(y)) ⇒ (∃b≥a) … )."""
    if leq is None:
        leq = C._gleq()
    vuf, vf, vE, vi = _t(uf), _t(f), _t(Efam), _t(i)
    va, vx, vy = var(a), var(x), var(y)
    ua = C.u_indice(vuf, va)
    prem = et(_prem3(vE, vi, va, vx, vy),
              egal(E.valeur(ua, vx), E.valeur(ua, vy)))
    return pourtout(a, pourtout(x, pourtout(y, impl(
        prem, _ex_beta(vf, vi, leq, va, vx, vy)))))


# @livre Ch.III §7.6 Lem.1 | E III.62 L.7-12 | PDF p.165  (lemme 1, 2e partie : f_α(x)=f_α(y) ⇔ (∃β≥α) f_βα(x)=f_βα(y) — hypothèse honnête)
def hyp_lemme2(Efam, f, i, leq=None, gleq=None, a="ai", x="xi", y="yi"):
    """(∀a)(∀x)(∀y)( prem ⇒ ( f_a(x)=f_a(y) ⇔ (∃b≥a) f_ba(x)=f_ba(y) ) )."""
    if leq is None:
        leq = C._gleq()
    vf, vE, vi = _t(f), _t(Efam), _t(i)
    va, vx, vy = var(a), var(x), var(y)
    fa_x = C.application_canonique_ind_valeur(vE, vf, vi, va, vx, gleq)
    fa_y = C.application_canonique_ind_valeur(vE, vf, vi, va, vy, gleq)
    return pourtout(a, pourtout(x, pourtout(y, impl(
        _prem3(vE, vi, va, vx, vy),
        equiv(egal(fa_x, fa_y), _ex_beta(vf, vi, leq, va, vx, vy))))))


# @livre Ch.III §7.6 Lem.1 | E III.62 L.1-6 | PDF p.165  (lemme 1 apparié : deux éléments de E s'écrivent f_α(x), f_α(y) pour un MÊME α — c'est ici que sert « I filtrant à droite »)
def hyp_lemme1_paire(Efam, f, i, gleq=None, z="zi", zp="zj",
                     a="ai", x="xi", y="yi"):
    """(∀z)(∀z')( (z∈E et z'∈E) ⇒ (∃a)(∃x)(∃y)( prem et (z=f_a(x) et z'=f_a(y)) ) )."""
    vE, vf, vi = _t(Efam), _t(f), _t(i)
    va, vx, vy, vz, vzp = var(a), var(x), var(y), var(z), var(zp)
    lim = C.lim_ind(vE, vf, vi, gleq)
    fa_x = C.application_canonique_ind_valeur(vE, vf, vi, va, vx, gleq)
    fa_y = C.application_canonique_ind_valeur(vE, vf, vi, va, vy, gleq)
    corps = et(_prem3(vE, vi, va, vx, vy),
               et(egal(vz, fa_x), egal(vzp, fa_y)))
    return pourtout(z, pourtout(zp, impl(
        et(appartient(vz, lim), appartient(vzp, lim)),
        existe(a, existe(x, existe(y, corps))))))


# @livre Ch.III §7.6 Prop.6 | E III.62 L.36-40 | PDF p.165  (Prop. 6, 3° : u injective ⇔ le critère — LES DEUX SENS)
def prop6_injectif(u="u", Efam="E", f="f", i="I", uf="uf", leq=None, gleq=None):
    """{ (24), f_α⟨E_α⟩⊂E, lemme 1 apparié, lemme 2 }
        ⊢ ( u injective sur E  ⇔  critère d'injectivité 3° )."""
    if leq is None:
        leq = C._gleq()
    vu, vE, vf, vi, vuf = _t(u), _t(Efam), _t(f), _t(i), _t(uf)
    va, vx, vy = var("ai"), var("xi"), var("yi")
    vz, vzp = var("zi"), var("zj")
    lim = C.lim_ind(vE, vf, vi, gleq)
    gu = graphe_de(vu)
    fa_x = C.application_canonique_ind_valeur(vE, vf, vi, va, vx, gleq)
    fa_y = C.application_canonique_ind_valeur(vE, vf, vi, va, vy, gleq)
    ua = C.u_indice(vuf, va)

    h24 = N.assume(relation_24_au_point(vu, vE, vf, vi, vuf, gleq))
    hcan = N.assume(hyp_canonique_arrive(vE, vf, vi, gleq))
    hl1 = N.assume(hyp_lemme1_paire(vE, vf, vi, gleq))
    hl2 = N.assume(hyp_lemme2(vE, vf, vi, leq, gleq))
    inj = injective_ponctuelle(vu, lim)
    crit = critere_injectivite(vuf, vf, vE, vi, leq)

    def _u24(pt_x):
        """{prem} ⊢ u(f_a(pt)) = u_a(pt)   (instance de (24) en (a, pt))."""
        return instancie(instancie(h24, va), pt_x)

    def _prem_paire(hprem):
        """De prem3 (a∈I, x∈E_a, y∈E_a) extraire les deux prémisses (a,x) et (a,y)."""
        aI = conjonction_elim_gauche(conjonction_elim_gauche(hprem))
        xE = conjonction_elim_droite(conjonction_elim_gauche(hprem))
        yE = conjonction_elim_droite(hprem)
        return conjonction_intro(aI, xE), conjonction_intro(aI, yE)

    # ── ⇒ : u injective ⇒ critère ──────────────────────────────────────────
    hinj = N.assume(inj)
    hp = N.assume(et(_prem3(vE, vi, va, vx, vy),
                     egal(E.valeur(ua, vx), E.valeur(ua, vy))))
    prem3 = conjonction_elim_gauche(hp)
    px, py = _prem_paire(prem3)
    e_x = N.modus_ponens(px, _u24(vx))                 # u(f_a(x)) = u_a(x)
    e_y = N.modus_ponens(py, _u24(vy))                 # u(f_a(y)) = u_a(y)
    ufx_ufy = composer_egalites(composer_egalites(
        e_x, conjonction_elim_droite(hp)),
        N.modus_ponens(e_y, symetrie(E.valeur(gu, fa_y), E.valeur(ua, vy))))
    #     u(f_a(x)) = u(f_a(y))
    inX = N.modus_ponens(px, instancie(instancie(hcan, va), vx))
    inY = N.modus_ponens(py, instancie(instancie(hcan, va), vy))
    eq_fa = N.modus_ponens(conjonction_intro(conjonction_intro(inX, inY), ufx_ufy),
                           instancie(instancie(hinj, fa_x), fa_y))   # f_a(x)=f_a(y)
    ex_b = N.modus_ponens(eq_fa, equivalence_avant(N.modus_ponens(
        prem3, instancie(instancie(instancie(hl2, va), vx), vy))))
    fwd = N.loi_deduction(inj, N.generalisation("ai", N.generalisation(
        "xi", N.generalisation("yi", N.loi_deduction(hp.conclusion, ex_b)))))

    # ── ⇐ : critère ⇒ u injective   (lemme 1 apparié : MÊME α) ─────────────
    hcrit = N.assume(crit)
    hz = N.assume(et(et(appartient(vz, lim), appartient(vzp, lim)),
                     egal(E.valeur(gu, vz), E.valeur(gu, vzp))))
    ex3 = N.modus_ponens(conjonction_elim_gauche(hz),
                         instancie(instancie(hl1, vz), vzp))
    corps = et(_prem3(vE, vi, va, vx, vy), et(egal(vz, fa_x), egal(vzp, fa_y)))
    hb = N.assume(corps)
    prem3b = conjonction_elim_gauche(hb)
    pxb, pyb = _prem_paire(prem3b)
    z_eq, zp_eq = (conjonction_elim_gauche(conjonction_elim_droite(hb)),
                   conjonction_elim_droite(conjonction_elim_droite(hb)))
    cg = N.modus_ponens(z_eq, congruence_terme(vz, fa_x,
                                               E.valeur(gu, var("w6a")), w="w6a"))
    cd = N.modus_ponens(zp_eq, congruence_terme(vzp, fa_y,
                                                E.valeur(gu, var("w6b")), w="w6b"))
    #     u(z)=u(f_a(x)) ; u(z')=u(f_a(y))
    ua_eq = composer_egalites(composer_egalites(composer_egalites(
        N.modus_ponens(cg, symetrie(E.valeur(gu, vz), E.valeur(gu, fa_x))),
        conjonction_elim_droite(hz)), cd),
        N.modus_ponens(pyb, _u24(vy)))                 # u(f_a(x)) = u_a(y)
    ua_x_y = composer_egalites(N.modus_ponens(
        N.modus_ponens(pxb, _u24(vx)),
        symetrie(E.valeur(gu, fa_x), E.valeur(ua, vx))), ua_eq)
    #     u_a(x) = u_a(y)
    ex_b2 = N.modus_ponens(conjonction_intro(prem3b, ua_x_y),
                           instancie(instancie(instancie(hcrit, va), vx), vy))
    eq_fa2 = N.modus_ponens(ex_b2, equivalence_arriere(N.modus_ponens(
        prem3b, instancie(instancie(instancie(hl2, va), vx), vy))))
    z_zp = composer_egalites(composer_egalites(
        z_eq, eq_fa2), N.modus_ponens(zp_eq, symetrie(vzp, fa_y)))
    imp3 = existe_elimination(existe_elimination(existe_elimination(
        N.loi_deduction(corps, z_zp), "yi"), "xi"), "ai")
    bwd = N.loi_deduction(crit, N.generalisation("zi", N.generalisation(
        "zj", N.loi_deduction(hz.conclusion, N.modus_ponens(ex3, imp3)))))

    res = conjonction_intro(fwd, bwd)
    assert res.conclusion == equiv(inj, crit), "prop6_injectif : ≠ équivalence 3°"
    assert set(res.hypotheses) == {h24.conclusion, hcan.conclusion,
                                   hl1.conclusion, hl2.conclusion}, \
        "prop6_injectif : hyps"
    return res


__all__ = ["injective_ponctuelle", "critere_injectivite", "hyp_lemme2",
           "hyp_lemme1_paire", "prop6_injectif"]
