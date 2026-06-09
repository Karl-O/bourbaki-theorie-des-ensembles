"""Tests §IV.1.3 — typification, structures transportées, transportabilité
(instance objet).   REPRÉSENTATIONNEL : on vérifie la forme des Formules/Termes
renvoyés, fidèlement aux énoncés VERBATIM de IV.1.3."""
from bourbaki.logique.formule import var, et, impl, equiv, appartient
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.cardinaux.ensembles_cardinaux import est_bijection_de
from bourbaki.structures import ensembles_especes_echelon as Ech
from bourbaki.structures import ensembles_especes_typification as Typ


# ── §IV.1.3 — typification T{x,s} = conjonction d'appartenances à des échelons ──
def test_typification_une_lettre():
    vE, vs = var("E"), var("s")
    # s ∈ 𝔓(E×E) (échelon relationnel) : T{E,s} = appartenance unique
    T = Typ.typification([vs], [Ech.schema_relation()], [vE])
    assert T == appartient(vs, E.parties(E.produit(vE, vE)))


def test_typification_deux_lettres_conjonction():
    vE, vs1, vs2 = var("E"), var("s1"), var("s2")
    # deux structures : s₁∈E (schéma base) et s₂∈𝔓(E×E)
    T = Typ.typification([vs1, vs2],
                         [Ech.schema_base(1), Ech.schema_relation()], [vE])
    clause1 = appartient(vs1, vE)
    clause2 = appartient(vs2, E.parties(E.produit(vE, vE)))
    assert T == et(clause1, clause2)


def test_typification_avec_auxiliaires():
    vE, vA, vs = var("E"), var("A"), var("s")
    # schéma sur n+m=2 termes : base 2 désigne l'auxiliaire A → s ∈ A
    T = Typ.typification([vs], [Ech.schema_base(2)], [vE], [vA])
    assert T == appartient(vs, vA)


# ── §IV.1.3 — structures transportées (relation (3)) ──────────────────────────
def test_structures_transportees():
    vf, vE, vs = var("f"), var("E"), var("s")
    # s_j' = ⟨f⟩^{S_relation}(s) = valeur(ext_parties(f×f), s)
    out = Typ.structures_transportees([vs], [Ech.schema_relation()], [vf])
    ext = Ech.ext_parties(Ech.produit_applications(vf, vf))
    assert out == [E.valeur(ext, vs)]


def test_structures_transportees_avec_id_auxiliaire():
    vf, vA, vs = var("f"), var("A"), var("s")
    # schéma base 2 (= auxiliaire A) : ⟨f,Id_A⟩^S = Id_A = Δ_A, appliqué à s
    out = Typ.structures_transportees([vs], [Ech.schema_base(2)], [vf], [vA])
    assert out == [E.valeur(E.diagonale(vA), vs)]


# ── §IV.1.3 — instance objet de la transportabilité (1)⇒(2) ───────────────────
def test_relation_transportable_instance_forme():
    vf, vx, vy, vs = var("f"), var("x"), var("y"), var("s")
    # R abstrait : R(bases, structs) := (struct₁) ∈ (base₁)
    R = lambda bases, structs: appartient(structs[0], bases[0])
    schemas = [Ech.schema_relation()]
    form = Typ.relation_transportable_instance(
        R, [vs], schemas, [vx], [vy], [vf])
    # forme attendue : (T{x,s} et f bij de x sur y) ⇒ (R{x,s} ⇔ R{y,s'})
    T = Typ.typification([vs], schemas, [vx])
    hyp = et(T, est_bijection_de(vf, vx, vy))
    sp = Typ.structures_transportees([vs], schemas, [vf])
    concl = equiv(R([vx], [vs]), R([vy], sp))
    assert form == impl(hyp, concl)
