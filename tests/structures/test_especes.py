"""Tests §IV.1.4–IV.1.5 — espèce de structure, structure d'espèce, isomorphisme,
transport, automorphisme, structures isomorphes.   REPRÉSENTATIONNEL pour les
définitions ; LEMMES DIRECTS clos pour transport_egalite / transport_donne_isomorphisme.
Fidèle aux énoncés VERBATIM de IV.1.4–IV.1.5 ; theorie_ensembles() = 22 axiomes."""
from bourbaki.logique.formule import var, egal, et, existe, appartient
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.cardinaux.ensembles_cardinaux import est_bijection_de
from bourbaki.structures import ensembles_especes_echelon as Ech
from bourbaki.structures import ensembles_especes as Sp


def _espece_relationnelle():
    """Σ relationnelle : 1 base principale, 0 auxiliaire, schéma S(E)=𝔓(E×E),
    axiome R{E,s} trivial (⊤ représenté par E=E) — espèce « ensemble muni d'une
    relation binaire »."""
    R = lambda bases, s: egal(bases[0], bases[0])    # axiome trivialement transportable
    return Sp.Espece(nom="RelBin", n=1, auxiliaires=(),
                     schema=Ech.schema_relation(), axiome=R)


# ── §IV.1.4 — caractérisation typique et structure d'espèce ───────────────────
def test_caracterisation_typique():
    sigma = _espece_relationnelle()
    vE, vs = var("E"), var("s")
    # T{E,s} : s ∈ 𝔓(E×E)
    assert Sp.caracterisation_typique(sigma, [vE], vs) == \
        appartient(vs, E.parties(E.produit(vE, vE)))


def test_est_structure_espece():
    sigma = _espece_relationnelle()
    vE, vU = var("E"), var("U")
    # « T{E,U} et R{E,U} »
    attendu = et(Sp.caracterisation_typique(sigma, [vE], vU), egal(vE, vE))
    assert Sp.est_structure_espece(sigma, [vE], vU) == attendu


# ── §IV.1.5 — transport de structure ──────────────────────────────────────────
def test_structure_transportee():
    sigma = _espece_relationnelle()
    vf, vU = var("f"), var("U")
    # U' = ⟨f⟩^S(U) = valeur(ext_parties(f×f), U)
    ext = Ech.ext_parties(Ech.produit_applications(vf, vf))
    assert Sp.structure_transportee(sigma, [vf], vU) == E.valeur(ext, vU)


# ── §IV.1.5 — isomorphisme (relation (4)) ─────────────────────────────────────
def test_est_isomorphisme_forme():
    sigma = _espece_relationnelle()
    vf, vE, vEp, vU, vUp = var("f"), var("E"), var("Ep"), var("U"), var("Up")
    iso = Sp.est_isomorphisme(sigma, [vf], [vE], [vEp], vU, vUp)
    bij = est_bijection_de(vf, vE, vEp)
    eq4 = egal(Sp.structure_transportee(sigma, [vf], vU), vUp)
    assert iso == et(bij, eq4)


# ── §IV.1.5 — sont_isomorphes / structures isomorphes ─────────────────────────
def test_sont_isomorphes_existentiel():
    sigma = _espece_relationnelle()
    vE, vEp, vU, vUp = var("E"), var("Ep"), var("U"), var("Up")
    out = Sp.sont_isomorphes(sigma, [vE], [vEp], vU, vUp, noms_f=["f1"])
    corps = Sp.est_isomorphisme(sigma, [var("f1")], [vE], [vEp], vU, vUp)
    assert out == existe("f1", corps)
    # « structures isomorphes » est un synonyme
    assert Sp.structures_isomorphes(sigma, [vE], [vEp], vU, vUp, ["f1"]) == out


# ── §IV.1.5 — automorphisme (cas E=E', U=U') ──────────────────────────────────
def test_est_automorphisme():
    sigma = _espece_relationnelle()
    vf, vE, vU = var("f"), var("E"), var("U")
    assert Sp.est_automorphisme(sigma, [vf], [vE], vU) == \
        Sp.est_isomorphisme(sigma, [vf], [vE], [vE], vU, vU)


# ── §IV.1.5 — univalente (représentationnel, reporté) ─────────────────────────
def test_est_univalente_marqueur():
    sigma = _espece_relationnelle()
    info = Sp.est_univalente(sigma)
    assert info["representationnel"] is True and info["reporte"] is True
    assert info["espece"] == "RelBin"


# ── LEMME DIRECT : la structure transportée fait de f un isomorphisme ─────────
def test_transport_egalite_close():
    sigma = _espece_relationnelle()
    vf, vU = var("f"), var("U")
    thm = Sp.transport_egalite(sigma, [vf], vU)
    assert thm.est_clos
    Ut = Sp.structure_transportee(sigma, [vf], vU)
    assert thm.conclusion == egal(Ut, Ut)


def test_transport_donne_isomorphisme_close():
    sigma = _espece_relationnelle()
    vf, vE, vEp, vU = var("f"), var("E"), var("Ep"), var("U")
    thm = Sp.transport_donne_isomorphisme(sigma, [vf], [vE], [vEp], vU)
    assert thm.est_clos
    # conclusion : (f bij de E sur E') ⇒ est_isomorphisme(Σ,f,E,E',U,U')
    from bourbaki.logique.formule import impl
    Up = Sp.structure_transportee(sigma, [vf], vU)
    bij = est_bijection_de(vf, vE, vEp)
    iso = Sp.est_isomorphisme(sigma, [vf], [vE], [vEp], vU, Up)
    assert thm.conclusion == impl(bij, iso)


# ── garde-fou : theorie_ensembles() reste à 22 axiomes ────────────────────────
def test_theorie_ensembles_22():
    assert len(E.theorie_ensembles().axiomes) == 22
