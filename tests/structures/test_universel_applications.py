"""Tests §IV.3 — Applications universelles (représentation paramétrée).

Vérifie la fidélité des DÉFINITIONS et la certification par le noyau des THÉORÈMES
logiques directs (critère (AU) ⟺ (AU_I′)+(AU_II′)).
"""
from bourbaki.logique.formule import (var, et, ou, non, impl, equiv, pourtout,
                                       existe, appartient, egal, app, alpha_egal)
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.structures import ensembles_universel_applications as U


# ── données (Σ, σ, α) ─────────────────────────────────────────────────────────
def test_donnees_probleme_contient_trois_predicats():
    d = U.donnees_probleme(var("E"))
    assert set(d.keys()) == {"E", "sigma_ens", "morph", "alpha"}
    assert d["E"] == var("E")
    # les trois prédicats sont callables
    assert callable(d["sigma_ens"]) and callable(d["morph"]) and callable(d["alpha"])


def test_axiome_QM_I_forme():
    alpha = U._alpha_defaut()
    ax = U.axiome_QM_I(var("E"), var("F"), var("S"), alpha)
    # (∀φ)(alpha ⇒ φ ∈ 𝓕(E;F)) : tête pourtout = non
    assert ax.tag == "non"
    assert "applications" in repr(ax)   # 𝓕(E;F) = applications(E,F)


def test_axiome_QM_II_implication():
    alpha = U._alpha_defaut()
    mor = U._morph_defaut()
    ax = U.axiome_QM_II(var("E"), var("F"), var("Fp"), var("S"), var("Sp"),
                        var("f"), alpha, mor)
    # impl(morph(...) , (∀φ)(...)) : tête = ou (impl = ¬A ∨ B)
    assert ax.tag == "ou"


def test_est_alpha_application_definition():
    alpha = U._alpha_defaut()
    d = U.est_alpha_application(var("E"), var("F"), var("S"), var("phi"), alpha)
    assert alpha_egal(d, alpha(var("F"), var("S"), var("phi")))


# ── (AU) / (AU_I′) / (AU_II′) ─────────────────────────────────────────────────
def test_est_universel_est_conjonction_existence_unicite():
    mor = U._morph_defaut()
    au = U.est_universel(var("FE"), var("SE"), var("phiE"), var("F"), var("S"),
                         var("phi"), morph=mor)
    ex = U.AU_corps(var("FE"), var("SE"), var("phiE"), var("F"), var("S"),
                    var("phi"), morph=mor)
    un = U.AU_unicite(var("FE"), var("SE"), var("phiE"), var("F"), var("S"),
                      var("phi"), morph=mor)
    assert alpha_egal(au, et(ex, un))


def test_au_implique_existence_certifie():
    """{(AU)} ⊢ (AU_I′)."""
    t = U.au_implique_existence()
    ex = U.AU_corps(var("FE"), var("SE"), var("phiE"), var("F"), var("S"),
                    var("phi"), morph=U._morph_defaut())
    # conditionnel ⊢ (AU) ⇒ (AU_I′) : clos, conclusion = impl(au, ex)
    assert t.est_clos
    assert t.conclusion.tag == "ou"   # impl
    assert t.conclusion.sous[1] == ex


def test_au_implique_unicite_certifie():
    """{(AU)} ⊢ (AU_II′)."""
    t = U.au_implique_unicite()
    un = U.AU_unicite(var("FE"), var("SE"), var("phiE"), var("F"), var("S"),
                      var("phi"), morph=U._morph_defaut())
    assert t.est_clos
    assert t.conclusion.sous[1] == un


def test_existence_et_unicite_impliquent_au_certifie():
    """⊢ ((AU_I′) et (AU_II′)) ⇒ (AU) — sens reconstructif du critère."""
    t = U.existence_et_unicite_impliquent_au()
    assert t.est_clos
    assert t.conclusion.tag == "ou"   # impl


# ── CST23 : séparation / injectivité de φ_E ───────────────────────────────────
def test_separent_les_elements_forme():
    s = U.separent_les_elements(var("E"))
    assert s.tag == "non"   # (∀x)(∀y)(…)
    # contient bien la clause de séparation φ(x) ≠ φ(y) : repérée par le τ de valeur
    assert "tau" in repr(s) and "phi" in repr(s)   # φ(x), φ(y) sont des τ_y((x,y)∈φ)


def test_phi_E_injective_forme():
    inj = U.phi_E_injective(var("E"), var("phiE"))
    assert inj.tag == "non"   # (∀x)(∀y)(…)


# ── Σ-ensemble libre engendré ─────────────────────────────────────────────────
def test_alpha_libre_est_applications():
    al = U.alpha_libre(var("E"))
    f = al(var("F"), var("S"), var("phi"))
    assert alpha_egal(f, appartient(var("phi"), E.applications(var("E"), var("F"))))


def test_est_libre_engendre_est_solution_avec_alpha_libre():
    mor = U._morph_defaut()
    se = U._sigma_ens_defaut()
    libre = U.est_libre_engendre(var("E"), var("FE"), var("SE"), var("phiE"),
                                 sigma_ens=se, morph=mor)
    cible = U.est_solution(var("FE"), var("SE"), var("phiE"),
                           sigma_ens=se, morph=mor, alpha=U.alpha_libre(var("E")))
    assert alpha_egal(libre, cible)


# ── exemples illustratifs (termes opaques) ────────────────────────────────────
def test_exemples_opaques():
    assert U.corps_des_fractions(var("E"), var("S")).tag == "app"
    assert U.produit_tensoriel(var("A"), var("B"), var("C")).tag == "app"
    assert U.compactifie_stone_cech(var("X")).tag == "app"
