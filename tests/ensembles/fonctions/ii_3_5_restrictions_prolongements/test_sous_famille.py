"""Tests §II.3.5 — sous-famille (notion auparavant absente).

Définitions fidèles + propriétés cheap closes (miroir du prolongement).
theorie_ensembles() = 22 axiomes ; aucune définition vacuux/inventée."""
from bourbaki.logique.i_1_termes_relations.formule import var, et, impl, inclus, appartient, pourtout
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.ensembles.fonctions.ii_3_5_restrictions_prolongements import ensembles_sous_famille as SF


# ── DÉFINITIONS ───────────────────────────────────────────────────────────────
def test_est_sous_famille_forme():
    vF, vG = var("F"), var("G")
    # f sous-famille de g := F ⊂ G
    assert SF.est_sous_famille(vF, vG) == inclus(vF, vG)


def test_est_sous_famille_buts_forme():
    vF, vG, vB, vD = var("F"), var("G"), var("B"), var("D")
    assert SF.est_sous_famille_buts(vF, vG, vB, vD) == \
        et(inclus(vF, vG), inclus(vB, vD))


# ── PROPRIÉTÉS CLOSES ─────────────────────────────────────────────────────────
def test_sous_famille_reflexive_close():
    vF, vz = var("F"), var("z")
    thm = SF.sous_famille_reflexive("F")
    assert thm.est_clos
    assert thm.conclusion == pourtout("z", impl(appartient(vz, vF), appartient(vz, vF)))


def test_sous_famille_transitive_close():
    vF, vG, vH = var("F"), var("G"), var("H")
    thm = SF.sous_famille_transitive("F", "G", "H")
    assert thm.est_clos
    assert thm.conclusion == impl(et(inclus(vF, vG), inclus(vG, vH)), inclus(vF, vH))


def test_sous_famille_converse_prolongement_close():
    vF, vG = var("F"), var("G")
    thm = SF.sous_famille_est_prolongement_converse("F", "G")
    assert thm.est_clos
    # est_sous_famille(f,g) ⇔ prolonge(g,f) — les deux membres sont F⊂G, mais la
    # propriété relie deux NOTIONS distinctes (sous-famille de f vs prolongement par g).
    from bourbaki.logique.i_1_termes_relations.formule import equiv
    assert thm.conclusion == equiv(SF.est_sous_famille(vF, vG), E.prolonge(vG, vF))


# ── garde-fou theorie ─────────────────────────────────────────────────────────
def test_theorie_22():
    assert len(E.theorie_ensembles().axiomes) == 22
