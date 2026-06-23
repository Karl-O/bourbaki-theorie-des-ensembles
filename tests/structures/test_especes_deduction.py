"""Tests §IV.1.6–IV.1.7 — termes intrinsèques, procédés de déduction, structures
sous-jacentes, espèces plus riches, espèces équivalentes (notions auparavant
ABSENTES).   REPRÉSENTATIONNEL (formes VERBATIM) + un LEMME DIRECT clos.
theorie_ensembles() = 22 axiomes ; aucune définition vacuux/inventée."""
import pytest

from bourbaki.logique.formule import var, app, egal, et, impl, appartient
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.structures.iv_1_structures_isomorphismes import ensembles_especes_echelon as Ech
from bourbaki.structures.iv_1_structures_isomorphismes import ensembles_especes as Sp
from bourbaki.structures.iv_1_structures_isomorphismes import ensembles_especes_deduction as Ded


def _espece_relationnelle(nom="RelBin"):
    """Σ : 1 base principale, 0 auxiliaire, schéma S(E)=𝔓(E×E), axiome trivial."""
    R = lambda bases, s: egal(bases[0], bases[0])
    return Sp.Espece(nom=nom, n=1, auxiliaires=(),
                     schema=Ech.schema_relation(), axiome=R)


# ── §IV.1.6 — TERME INTRINSÈQUE ───────────────────────────────────────────────
def test_terme_intrinseque_type_forme():
    sigma = _espece_relationnelle()
    vE, vs = var("E"), var("s")
    V = lambda bases, s: s                       # V{x,s} := s (structure générique)
    Tj = Ech.schema_relation()
    out = Ded.terme_intrinseque_type(V, sigma, [vE], vs, Tj)
    # condition 1° : V{x,s} ∈ T(E) = 𝔓(E×E)
    assert out == appartient(vs, Ech.echelon(Tj, [vE]))


def test_terme_intrinseque_equivariance_forme():
    sigma = _espece_relationnelle()
    vE, vy, vs, vf = var("E"), var("y"), var("s"), var("f")
    V = lambda bases, s: s
    Tj = Ech.schema_relation()
    out = Ded.terme_intrinseque_equivariance(V, sigma, [vE], [vy], vs, [vf], Tj)
    s_prime = Sp.structure_transportee(sigma, [vf], vs)
    ext = Ech.extension_canonique(Tj, [vf])
    assert out == egal(s_prime, E.valeur(ext, vs))


def test_est_terme_intrinseque_conjonction():
    sigma = _espece_relationnelle()
    vE, vy, vs, vf = var("E"), var("y"), var("s"), var("f")
    V = lambda bases, s: s
    Tj = Ech.schema_relation()
    out = Ded.est_terme_intrinseque(V, sigma, [vE], [vy], vs, [vf], Tj)
    c1 = Ded.terme_intrinseque_type(V, sigma, [vE], vs, Tj)
    c2 = Ded.terme_intrinseque_equivariance(V, sigma, [vE], [vy], vs, [vf], Tj)
    assert out == et(c1, c2)


# ── §IV.1.6 — PROCÉDÉ DE DÉDUCTION ────────────────────────────────────────────
def test_structure_deduite_terme():
    vE, vs = var("E"), var("s")
    P = lambda bases, s: app("P", bases[0], s)
    assert Ded.structure_deduite(P, [vE], vs) == app("P", vE, vs)


def test_est_procede_deduction_forme():
    theta = _espece_relationnelle("Theta")
    vE, vs = var("E"), var("s")
    U1 = lambda bases, s: bases[0]                # U_1 = x (la base elle-même)
    P = lambda bases, s: s                        # P = s (structure déduite)
    out = Ded.est_procede_deduction(theta, P, [U1], [vE], vs)
    # « P{x,s} est une structure d'espèce Θ sur U_1{x,s} »
    assert out == Sp.est_structure_espece(theta, [vE], vs)


# ── §IV.1.6 — STRUCTURE SOUS-JACENTE ──────────────────────────────────────────
def test_projection_base():
    vE = var("E")
    assert Ded.projection_base(1)([vE], var("s")) == vE


def test_est_structure_sous_jacente_forme():
    theta = _espece_relationnelle("Theta")
    vE, vs = var("E"), var("s")
    P = lambda bases, s: s
    out = Ded.est_structure_sous_jacente(theta, P, [1], [vE], vs)
    assert out == Ded.est_procede_deduction(theta, P, [Ded.projection_base(1)],
                                            [vE], vs)


def test_structure_sous_jacente_intrinseque_close():
    sigma = _espece_relationnelle()
    thm = Ded.structure_sous_jacente_intrinseque(1, sigma)
    assert thm.est_clos
    # conclusion : réflexivité d'une égalité T = T (membre droit de l'équivariance)
    c = thm.conclusion
    assert c.tag == "="
    assert c.termes[0] == c.termes[1]


# ── §IV.1.6, Ex 3 — ESPÈCE PLUS RICHE ─────────────────────────────────────────
def test_espece_plus_riche_axiome_forme():
    sigma = _espece_relationnelle("Sig")
    theta = Sp.Espece(nom="Theta", n=1, auxiliaires=(),
                      schema=Ech.schema_relation(),
                      axiome=lambda bases, s: egal(bases[0], bases[0]))
    vE, vs = var("E"), var("s")
    out = Ded.espece_plus_riche_axiome(sigma, theta, [vE], vs)
    assert out == impl(sigma.axiome([vE], vs), theta.axiome([vE], vs))


def test_est_plus_riche_ok():
    sigma = _espece_relationnelle("Sig")
    theta = Sp.Espece(nom="Theta", n=1, auxiliaires=(),
                      schema=Ech.schema_relation(),
                      axiome=lambda bases, s: egal(bases[0], bases[0]))
    vE, vs = var("E"), var("s")
    out = Ded.est_plus_riche(sigma, theta, [vE], vs)
    assert out == impl(sigma.axiome([vE], vs), theta.axiome([vE], vs))


def test_est_plus_riche_bases_incompatibles():
    sigma = _espece_relationnelle("Sig")          # n=1
    theta = Sp.Espece(nom="Theta", n=2, auxiliaires=(),
                      schema=Ech.schema_produit(),
                      axiome=lambda bases, s: egal(bases[0], bases[0]))
    with pytest.raises(ValueError):
        Ded.est_plus_riche(sigma, theta, [var("E")], var("s"))


# ── §IV.1.7 — ESPÈCES ÉQUIVALENTES ────────────────────────────────────────────
def test_equivalence_especes_aller_forme():
    vE, vs = var("E"), var("s")
    P = lambda bases, s: app("P", bases[0], s)
    Q = lambda bases, s: app("Q", bases[0], s)
    out = Ded.equivalence_especes_aller(P, Q, [vE], vs)
    Ps = app("P", vE, vs)
    assert out == egal(app("Q", vE, Ps), vs)


def test_equivalence_especes_retour_forme():
    vE, vt = var("E"), var("t")
    P = lambda bases, s: app("P", bases[0], s)
    Q = lambda bases, s: app("Q", bases[0], s)
    out = Ded.equivalence_especes_retour(P, Q, [vE], vt)
    Qt = app("Q", vE, vt)
    assert out == egal(app("P", vE, Qt), vt)


def test_sont_especes_equivalentes_conjonction():
    vE, vs, vt = var("E"), var("s"), var("t")
    P = lambda bases, s: app("P", bases[0], s)
    Q = lambda bases, s: app("Q", bases[0], s)
    out = Ded.sont_especes_equivalentes(P, Q, [vE], vs, vt)
    assert out == et(Ded.equivalence_especes_aller(P, Q, [vE], vs),
                     Ded.equivalence_especes_retour(P, Q, [vE], vt))


# ── garde-fou theorie ─────────────────────────────────────────────────────────
def test_theorie_22():
    assert len(E.theorie_ensembles().axiomes) == 22
