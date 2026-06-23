"""Tests §IV.1.1–IV.1.2 — schémas d'échelon, échelon S(E₁,…,Eₙ), extension
canonique ⟨f₁,…,fₙ⟩^S.   REPRÉSENTATIONNEL : on vérifie que les def renvoient les
bons OBJETS/TERMES, fidèlement aux énoncés VERBATIM de IV.1.1–IV.1.2."""
from bourbaki.logique.formule import var
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.structures.iv_1_structures_isomorphismes import ensembles_especes_echelon as Ech


# ── §IV.1.1 — schémas : validité et nombre de termes ──────────────────────────
def test_schema_validite_exemples():
    assert Ech.schema_valide(Ech.schema_base(1))
    assert Ech.schema_valide(Ech.schema_parties())
    assert Ech.schema_valide(Ech.schema_produit())
    assert Ech.schema_valide(Ech.schema_relation())


def test_schema_invalide_renvoi_avant():
    # c_2=(2,0) référence A_2 qui n'existe pas encore (a doit être ≤ i−1) : invalide
    mauvais = Ech.Schema(((0, 1), (2, 0)))
    assert not Ech.schema_valide(mauvais)
    # couple (0,0) ne désigne aucun terme de base : invalide
    assert not Ech.schema_valide(Ech.Schema(((0, 0),)))
    # produit (1,2) en position 2 référence A_2 (=i) interdit
    assert not Ech.schema_valide(Ech.Schema(((0, 1), (1, 2))))


def test_schema_nb_termes():
    # n = plus grand b_i des couples (0,b_i)
    assert Ech.schema_nb_termes(Ech.schema_base(1)) == 1
    assert Ech.schema_nb_termes(Ech.schema_parties()) == 1
    assert Ech.schema_nb_termes(Ech.schema_produit()) == 2   # bases E₁,E₂
    assert Ech.schema_nb_termes(Ech.schema_relation()) == 1


# ── §IV.1.1 — construction d'échelon et échelon S(E₁,…,Eₙ) ────────────────────
def test_echelon_base_identite():
    vE = var("E")
    # schéma à un seul terme (0,1) : S(E) = E
    assert Ech.echelon(Ech.schema_base(1), [vE]) == vE


def test_echelon_parties():
    vE = var("E")
    # S(E) = 𝔓(E)
    assert Ech.echelon(Ech.schema_parties(), [vE]) == E.parties(vE)


def test_echelon_produit():
    vE1, vE2 = var("E1"), var("E2")
    # S(E₁,E₂) = E₁ × E₂
    assert Ech.echelon(Ech.schema_produit(), [vE1, vE2]) == E.produit(vE1, vE2)


def test_echelon_relation_powerset_produit():
    vE = var("E")
    # S(E) = 𝔓(E×E)
    attendu = E.parties(E.produit(vE, vE))
    assert Ech.echelon(Ech.schema_relation(), [vE]) == attendu


def test_construction_echelon_suite_complete():
    vE = var("E")
    # construction de schema_relation : [A₁=E, A₂=E×E, A₃=𝔓(E×E)]
    A = Ech.construction_echelon(Ech.schema_relation(), [vE])
    assert A == [vE, E.produit(vE, vE), E.parties(E.produit(vE, vE))]


# ── §IV.1.2 — extension canonique ⟨f₁,…,fₙ⟩^S ─────────────────────────────────
def test_extension_base_est_f():
    vf = var("f")
    # schéma (0,1) : ⟨f⟩^S = f
    assert Ech.extension_canonique(Ech.schema_base(1), [vf]) == vf


def test_extension_parties():
    vf = var("f")
    # schéma 𝔓 : ⟨f⟩^S = f̄ (extension aux parties)
    assert Ech.extension_canonique(Ech.schema_parties(), [vf]) == Ech.ext_parties(vf)


def test_extension_produit():
    vf1, vf2 = var("f1"), var("f2")
    # schéma produit : ⟨f₁,f₂⟩^S = f₁ × f₂
    out = Ech.extension_canonique(Ech.schema_produit(), [vf1, vf2])
    assert out == Ech.produit_applications(vf1, vf2)


def test_extension_relation():
    vf = var("f")
    # schéma relationnel : ⟨f⟩^S = (f × f) puis extension aux parties
    out = Ech.extension_canonique(Ech.schema_relation(), [vf])
    assert out == Ech.ext_parties(Ech.produit_applications(vf, vf))
