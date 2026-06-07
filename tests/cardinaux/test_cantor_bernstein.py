"""Tests — Cantor–Bernstein via Knaster–Tarski (point fixe de φ).

Vérifie, à chaque palier, que la CONCLUSION est exactement la cible et que le
théorème est CLOS (aucune hypothèse résiduelle) là où il doit l'être.
"""
from bourbaki.logique.formule import var, et, non, impl, appartient, inclus, egal, equiv
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.cardinaux import ensembles_cantor_bernstein as CB


# ── PALIER 1 : φ + caractérisation membre ─────────────────────────────────────

def test_phi_terme():
    """φ(S) est bien A ∖ g⟨B∖f⟨S⟩⟩."""
    vA, vB, vf, vg, vS = var("A"), var("B"), var("f"), var("g"), var("S")
    attendu = E.difference(vA, E.image(vg, E.difference(vB, E.image(vf, vS))))
    assert CB.phi(vA, vB, vf, vg, vS) == attendu


def test_phi_membre():
    """⊢ (z∈φ(S)) ⇔ (z∈A et ¬(z∈g⟨B∖f⟨S⟩⟩)), clos."""
    thm = CB.phi_membre()
    vA, vB, vf, vg, vS, vz = (var("A"), var("B"), var("f"), var("g"),
                              var("S"), var("z"))
    gbfs = E.image(vg, E.difference(vB, E.image(vf, vS)))
    cible_g = appartient(vz, CB.phi(vA, vB, vf, vg, vS))
    cible_d = et(appartient(vz, vA), non(appartient(vz, gbfs)))
    assert thm.est_clos
    assert thm.conclusion == equiv(cible_g, cible_d)


# ── différence anti-monotone ──────────────────────────────────────────────────

def test_difference_anti_monotone():
    """⊢ (X⊂Y) ⇒ ((E∖Y)⊂(E∖X)), clos."""
    thm = CB.difference_anti_monotone()
    vE, vX, vY = var("E"), var("X"), var("Y")
    cible = impl(inclus(vX, vY),
                 inclus(E.difference(vE, vY), E.difference(vE, vX)))
    assert thm.est_clos
    assert thm.conclusion == cible


# ── PALIER 2 : φ croissant (lemme CLÉ) ────────────────────────────────────────

def test_phi_monotone():
    """⊢ (S⊂S′) ⇒ (φ(S)⊂φ(S′)), clos."""
    thm = CB.phi_monotone()
    vA, vB, vf, vg = var("A"), var("B"), var("f"), var("g")
    vS, vSp = var("S"), var("Sp")
    cible = impl(inclus(vS, vSp),
                 inclus(CB.phi(vA, vB, vf, vg, vS), CB.phi(vA, vB, vf, vg, vSp)))
    assert thm.est_clos
    assert thm.conclusion == cible


# ── PALIER 3 : D + caractérisation ────────────────────────────────────────────

def test_D_terme():
    """D est bien app('D_kt', A, B, f, g)."""
    vA, vB, vf, vg = var("A"), var("B"), var("f"), var("g")
    assert CB.D(vA, vB, vf, vg) == E.app("D_kt", vA, vB, vf, vg)


def test_D_membre():
    """⊢ (z∈D) ⇔ (z∈A et (∀S)((S⊂A et φ(S)⊂S)⇒z∈S)), clos."""
    thm = CB.D_membre()
    vA, vB, vf, vg, vz = (var("A"), var("B"), var("f"), var("g"), var("z"))
    cible_g = appartient(vz, CB.D(vA, vB, vf, vg))
    cible_d = CB._corps_D(vA, vB, vf, vg, vz)
    assert thm.est_clos
    assert thm.conclusion == equiv(cible_g, cible_d)


def test_D_inclus_A():
    """⊢ D ⊂ A, clos."""
    thm = CB.D_inclus_A()
    vA, vB, vf, vg = var("A"), var("B"), var("f"), var("g")
    assert thm.est_clos
    assert thm.conclusion == inclus(CB.D(vA, vB, vf, vg), vA)


def test_D_inclus():
    """⊢ ((S⊂A et φ(S)⊂S)) ⇒ (D⊂S), clos."""
    thm = CB.D_inclus()
    vA, vB, vf, vg, vS = var("A"), var("B"), var("f"), var("g"), var("S")
    cible = impl(CB._phi_clos(vA, vB, vf, vg, vS), inclus(CB.D(vA, vB, vf, vg), vS))
    assert thm.est_clos
    assert thm.conclusion == cible


def test_phi_D_inclus_A():
    """⊢ φ(D) ⊂ A, clos."""
    thm = CB.phi_D_inclus_A()
    vA, vB, vf, vg = var("A"), var("B"), var("f"), var("g")
    dterm = CB.D(vA, vB, vf, vg)
    assert thm.est_clos
    assert thm.conclusion == inclus(CB.phi(vA, vB, vf, vg, dterm), vA)


# ── PALIER 4 : φ(D) = D  (KNASTER–TARSKI) ─────────────────────────────────────

def test_phi_D_inclus_D():
    """⊢ φ(D) ⊂ D, clos."""
    thm = CB.phi_D_inclus_D()
    vA, vB, vf, vg = var("A"), var("B"), var("f"), var("g")
    dterm = CB.D(vA, vB, vf, vg)
    assert thm.est_clos
    assert thm.conclusion == inclus(CB.phi(vA, vB, vf, vg, dterm), dterm)


def test_D_inclus_phi_D():
    """⊢ D ⊂ φ(D), clos."""
    thm = CB.D_inclus_phi_D()
    vA, vB, vf, vg = var("A"), var("B"), var("f"), var("g")
    dterm = CB.D(vA, vB, vf, vg)
    assert thm.est_clos
    assert thm.conclusion == inclus(dterm, CB.phi(vA, vB, vf, vg, dterm))


def test_phi_point_fixe():
    """⊢ φ(D) = D  (THÉORÈME DE KNASTER–TARSKI), clos."""
    thm = CB.phi_point_fixe()
    vA, vB, vf, vg = var("A"), var("B"), var("f"), var("g")
    dterm = CB.D(vA, vB, vf, vg)
    assert thm.est_clos
    assert thm.conclusion == egal(CB.phi(vA, vB, vf, vg, dterm), dterm)
