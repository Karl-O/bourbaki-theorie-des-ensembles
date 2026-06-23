"""Tests ISOLÉS — §III.3.5 Corollaire 3 (de la Prop. 10) : a^(b·c) = (a^b)^c.

PALIERS SÛRS certifiés par le noyau (la bijection de currying complète est REPORTÉE,
cf. docstring du module).  On vérifie que chaque lemme livré est un Theoreme du noyau,
CLOS, et que sa conclusion a la FORME exacte attendue (définitions / caractérisations
membership / réduction à l'équipotence)."""
from bourbaki.logique.i_1_termes_relations.formule import var, egal, et, impl, equiv, inclus, appartient, existe
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.cardinaux.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import cardinal, equipotent
from bourbaki.cardinaux.arithmetique.iii_3_5_exposant.prop10_currying import ensembles_exposant_produit as XP


def _est_theoreme_clos(thm):
    assert isinstance(thm, N.Theoreme), f"pas un Theoreme : {type(thm)}"
    assert thm.est_clos, f"théorème non clos, hyps = {thm.hypotheses}"


# ── PALIER 1 : les deux cardinaux du Corollaire 3 ─────────────────────────────
def test_supports_definis():
    src = XP.support_source("A", "B", "C")        # 𝓕(B×C;A)
    but = XP.support_but("A", "B", "C")           # 𝓕(C;𝓕(B;A))
    assert src == E.applications(E.produit(var("B"), var("C")), var("A"))
    assert but == E.applications(var("C"), E.applications(var("B"), var("A")))


def test_exposant_produit_gauche_droit():
    g = XP.exposant_produit_gauche("A", "B", "C")     # a^(b·c) = Card(𝓕(B×C;A))
    d = XP.exposant_produit_droit("A", "B", "C")      # (a^b)^c = Card(𝓕(C;𝓕(B;A)))
    assert g == cardinal(E.applications(E.produit(var("B"), var("C")), var("A")))
    assert d == cardinal(E.applications(var("C"), E.applications(var("B"), var("A"))))


# ── PALIER 2 : membership de la SOURCE 𝓕(B×C;A) ───────────────────────────────
def test_membre_curry_source():
    thm = XP.membre_curry_source("A", "B", "C", "t", "G")
    _est_theoreme_clos(thm)
    BC = E.produit(var("B"), var("C"))
    lhs = appartient(var("t"), E.applications(BC, var("A")))
    triple = E.couple(E.couple(var("G"), BC), var("A"))
    rhs = existe("G", et(egal(var("t"), triple),
                         appartient(var("G"), E.exposant(BC, var("A")))))
    assert thm.conclusion == equiv(lhs, rhs)


def test_membre_curry_source_graphe():
    thm = XP.membre_curry_source_graphe("A", "B", "C", "G")
    _est_theoreme_clos(thm)
    BC = E.produit(var("B"), var("C"))
    lhs = appartient(var("G"), E.exposant(BC, var("A")))
    rhs = et(et(inclus(var("G"), E.produit(BC, var("A"))),
                E.est_fonctionnel(var("G"))),
             egal(E.dom(var("G")), BC))
    assert thm.conclusion == equiv(lhs, rhs)


# ── PALIER 3 : membership du BUT 𝓕(C;𝓕(B;A))  (double étage) ───────────────────
def test_membre_curry_but():
    thm = XP.membre_curry_but("A", "B", "C", "t", "H")
    _est_theoreme_clos(thm)
    FBA = E.applications(var("B"), var("A"))
    lhs = appartient(var("t"), E.applications(var("C"), FBA))
    triple = E.couple(E.couple(var("H"), var("C")), FBA)
    rhs = existe("H", et(egal(var("t"), triple),
                         appartient(var("H"), E.exposant(var("C"), FBA))))
    assert thm.conclusion == equiv(lhs, rhs)


def test_membre_curry_but_graphe():
    thm = XP.membre_curry_but_graphe("A", "B", "C", "H")
    _est_theoreme_clos(thm)
    FBA = E.applications(var("B"), var("A"))
    lhs = appartient(var("H"), E.exposant(var("C"), FBA))
    rhs = et(et(inclus(var("H"), E.produit(var("C"), FBA)),
                E.est_fonctionnel(var("H"))),
             egal(E.dom(var("H")), var("C")))
    assert thm.conclusion == equiv(lhs, rhs)


# ── PALIER 4 : équipotence support / cardinal ─────────────────────────────────
def test_eq_source_son_cardinal():
    thm = XP.eq_source_son_cardinal("A", "B", "C")
    _est_theoreme_clos(thm)
    src = XP.support_source("A", "B", "C")
    assert thm.conclusion == equipotent(src, cardinal(src))


def test_eq_but_son_cardinal():
    thm = XP.eq_but_son_cardinal("A", "B", "C")
    _est_theoreme_clos(thm)
    but = XP.support_but("A", "B", "C")
    assert thm.conclusion == equipotent(but, cardinal(but))


# ── PALIER 5 : réduction du Corollaire 3 à l'équipotence des supports ──────────
def test_curry_but_egale_via_eq():
    thm = XP.curry_but_egale_via_eq("A", "B", "C")
    _est_theoreme_clos(thm)
    src = XP.support_source("A", "B", "C")
    but = XP.support_but("A", "B", "C")
    # conclusion = (Eq(src,but) ⇒ (Card src = Card but)) = a^(b·c) = (a^b)^c sous Eq
    assert thm.conclusion == impl(equipotent(src, but),
                                  egal(cardinal(src), cardinal(but)))
