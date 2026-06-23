"""Tests §III.7.2 — Propriété universelle (cône) de la limite projective (Prop. 1).

Chaque test vérifie que la conclusion certifiée par le noyau est EXACTEMENT la
cible attendue ET le statut HONNÊTE des hypothèses résiduelles (non vacuous : la
conclusion ne figure JAMAIS dans les hypothèses).  theorie_ensembles() reste à 22.
"""
from bourbaki.logique.formule import var, egal, et, impl, appartient, pourtout
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.ensembles.familles.iii_7_limites import ensembles_limites as L
from bourbaki.ensembles.familles.iii_7_limites import ensembles_limites_iii7 as I7


def _leq():
    return lambda u, v: appartient(E.couple(u, v), var("Gleq"))


def _ctx():
    return (var("E"), var("f"), var("u"), var("I"), var("F"),
            var("yy"), var("a"), var("b"))


# ── theorie reste à 22 axiomes (aucun axiome de membership ajouté au noyau) ────
def test_theorie_inchangee_22():
    assert len(E.theorie_ensembles().axiomes) == 22


# ── la définition de compatibilité (relation (5)) se construit ────────────────
def test_cone_compatible_se_construit():
    vE, vf, vu, vi, vF, vy, va, vb = _ctx()
    d = I7.cone_compatible(vf, vu, _leq(), vi, vF, "a", "b", "yy")
    # c'est un (∀a)(∀b)(∀yy)(impl(...))
    assert d is not None
    ax = I7.axiome_cone_canonique(vE, vf, vu, _leq(), vi, vF)
    assert ax is not None


# ── cone_compatibilite : lecture de (5) en (α,β,y) fixés ──────────────────────
def test_cone_compatibilite():
    vE, vf, vu, vi, vF, vy, va, vb = _ctx()
    th = I7.cone_compatibilite("f", "u", _leq(), "I", "F", "a", "b", "yy")
    fab = L.appl_proj(vf, va, vb)
    ub_y = I7.cone_u_valeur(vu, vb, vy)
    ua_y = I7.cone_u_valeur(vu, va, vy)
    prem = et(et(et(appartient(va, vi), appartient(vb, vi)), _leq()(va, vb)),
              appartient(vy, vF))
    concl = egal(E.valeur(fab, ub_y), ua_y)
    assert th.conclusion == impl(prem, concl)
    assert I7.cone_compatible(vf, vu, _leq(), vi, vF, "a", "b", "yy") in th.hypotheses


# ── cone_coordonnee_valeur : (★) instancié — pr_α(u(y)) = u_α(y) ───────────────
def test_cone_coordonnee_valeur():
    vE, vf, vu, vi, vF, vy, va, vb = _ctx()
    th = I7.cone_coordonnee_valeur("E", "f", "u", _leq(), "I", "F", "a", "yy")
    u_y = I7.cone_canonique_valeur(vE, vf, vu, vy)
    attendu = egal(E.projection_indice(u_y, va), I7.cone_u_valeur(vu, va, vy))
    assert th.conclusion == attendu
    # hypothèses HONNÊTES : α∈I, y∈F (domaines)
    assert appartient(va, vi) in th.hypotheses
    assert appartient(vy, vF) in th.hypotheses
    # NON vacuous : la conclusion ne figure pas dans les hypothèses
    assert attendu not in th.hypotheses


# ── cone_condition_1 : le point u(y) vérifie la condition (1) ──────────────────
def test_cone_condition_1():
    vE, vf, vu, vi, vF, vy, va, vb = _ctx()
    th = I7.cone_condition_1("E", "f", "u", _leq(), "I", "F", "a", "b", "yy")
    u_y = I7.cone_canonique_valeur(vE, vf, vu, vy)
    fab = L.appl_proj(vf, va, vb)
    pr_a = E.projection_indice(u_y, va)
    pr_b = E.projection_indice(u_y, vb)
    attendu = egal(pr_a, E.valeur(fab, pr_b))
    assert th.conclusion == attendu
    # compatibilité (5) figure parmi les hypothèses (l'hypothèse de la Prop. 1)
    assert I7.cone_compatible(vf, vu, _leq(), vi, vF, "a", "b", "yy") in th.hypotheses
    assert attendu not in th.hypotheses


# ── cone_image_dans_limite : u(y) ∈ lim←  (CŒUR de l'existence) ────────────────
def test_cone_image_dans_limite():
    vE, vf, vu, vi, vF, vy, va, vb = _ctx()
    th = I7.cone_image_dans_limite("E", "f", "u", _leq(), "I", "F", "yy", "a", "b")
    u_y = I7.cone_canonique_valeur(vE, vf, vu, vy)
    attendu = appartient(u_y, L.lim_proj(vE, vf))
    assert th.conclusion == attendu
    # hypothèses HONNÊTES exactes : compatibilité, u(y)∈∏ (bonne-déf), y∈F
    compat = I7.cone_compatible(vf, vu, _leq(), vi, vF, "a", "b", "yy")
    Hprod = appartient(u_y, E.produit_famille(vE, vi))
    Hy = appartient(vy, vF)
    assert compat in th.hypotheses
    assert Hprod in th.hypotheses
    assert Hy in th.hypotheses
    assert len(th.hypotheses) == 3
    assert attendu not in th.hypotheses


# ── cone_relation_6 : f_α(u(y)) = u_α(y)  (relation (6), requiert u(y)∈lim←) ───
def test_cone_relation_6():
    vE, vf, vu, vi, vF, vy, va, vb = _ctx()
    th = I7.cone_relation_6("E", "f", "u", _leq(), "I", "F", "a", "yy")
    u_y = I7.cone_canonique_valeur(vE, vf, vu, vy)
    fa = E.valeur(__import__("bourbaki.ordre.iii_7_limites.ensembles_limites_canoniques",
                             fromlist=["f_canon_proj"]).f_canon_proj(vE, vf, va), u_y)
    ua_y = I7.cone_u_valeur(vu, va, vy)
    attendu = egal(fa, ua_y)
    assert th.conclusion == attendu
    # u(y)∈lim← figure en hypothèse (requis pour f_α=pr_α)
    assert appartient(u_y, L.lim_proj(vE, vf)) in th.hypotheses
    assert appartient(va, vi) in th.hypotheses
    assert appartient(vy, vF) in th.hypotheses
    assert attendu not in th.hypotheses


# ── cone_existence : EXISTENCE du cône (Prop. 1, 1°), u(y)∈lim DÉCHARGÉ ─────────
def test_cone_existence():
    vE, vf, vu, vi, vF, vy, va, vb = _ctx()
    th = I7.cone_existence("E", "f", "u", _leq(), "I", "F", "a", "b", "yy")
    u_y = I7.cone_canonique_valeur(vE, vf, vu, vy)
    fa = E.valeur(__import__("bourbaki.ordre.iii_7_limites.ensembles_limites_canoniques",
                             fromlist=["f_canon_proj"]).f_canon_proj(vE, vf, va), u_y)
    ua_y = I7.cone_u_valeur(vu, va, vy)
    attendu = egal(fa, ua_y)
    assert th.conclusion == attendu
    # hypothèses HONNÊTES exactes : compatibilité (5), u(y)∈∏, α∈I, y∈F
    compat = I7.cone_compatible(vf, vu, _leq(), vi, vF, "a", "b", "yy")
    Hprod = appartient(u_y, E.produit_famille(vE, vi))
    assert compat in th.hypotheses
    assert Hprod in th.hypotheses
    assert appartient(va, vi) in th.hypotheses
    assert appartient(vy, vF) in th.hypotheses
    assert len(th.hypotheses) == 4
    # u(y)∈lim← est DÉCHARGÉ (prouvé via cone_image_dans_limite), pas une hypothèse
    assert appartient(u_y, L.lim_proj(vE, vf)) not in th.hypotheses
    # NON vacuous
    assert attendu not in th.hypotheses


# ── cone_existence_forall : relation (6) « pour tout α » (forme Bourbaki) ──────
def test_cone_existence_forall():
    vE, vf, vu, vi, vF, vy, va, vb = _ctx()
    th = I7.cone_existence_forall("E", "f", "u", _leq(), "I", "F", "a", "b", "yy")
    u_y = I7.cone_canonique_valeur(vE, vf, vu, vy)
    fa = E.valeur(__import__("bourbaki.ordre.iii_7_limites.ensembles_limites_canoniques",
                             fromlist=["f_canon_proj"]).f_canon_proj(vE, vf, va), u_y)
    ua_y = I7.cone_u_valeur(vu, va, vy)
    eq6 = egal(fa, ua_y)
    attendu = pourtout("a", impl(appartient(va, vi), eq6))
    assert th.conclusion == attendu
    # α∈I est DÉCHARGÉ (généralisation sur α réussie) ; 3 hyps honnêtes restantes
    assert appartient(va, vi) not in th.hypotheses
    compat = I7.cone_compatible(vf, vu, _leq(), vi, vF, "a", "b", "yy")
    Hprod = appartient(u_y, E.produit_famille(vE, vi))
    assert compat in th.hypotheses
    assert Hprod in th.hypotheses
    assert appartient(vy, vF) in th.hypotheses
    assert len(th.hypotheses) == 3


# ── REPORTES bien renseigné (honnêteté) ───────────────────────────────────────
def test_reportes():
    assert isinstance(I7.REPORTES, list) and len(I7.REPORTES) >= 1
    assert any("UNICIT" in r.upper() for r in I7.REPORTES)
