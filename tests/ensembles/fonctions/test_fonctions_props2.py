"""Tests §II.3 — composition : propositions restantes (mission II3-fonctions-restant).

Module testé : bourbaki.ensembles.fonctions.ii_3_general.ensembles_fonctions_props2.
Chaque théorème est vérifié sur sa CONCLUSION EXACTE (== cible construite
indépendamment).  Les théorèmes INCONDITIONNELS sont contrôlés sur `.est_clos` ;
les théorèmes CONDITIONNELS (composée surjective/bijective, valeur 2 arg.) le sont
sur l'ENSEMBLE EXACT de leurs hypothèses (jamais postulées).
"""
from bourbaki.logique.formule import var, egal, et, impl, appartient, existe, equiv
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.ensembles.fonctions.ii_3_general import ensembles_fonctions_props2 as P2


# ── THÉORÈME 1 b) — composée de deux surjections est une surjection ────────────
def test_composee_surjections_conclusion():
    th = P2.composee_surjections()
    assert th.est_clos
    assert th.conclusion == P2.cible_composee_surjections()


def test_composee_surjections_forme():
    vF, vG, vX, vY, vZ = var("F"), var("G"), var("X"), var("Y"), var("Z")
    comp = E.composee(vG, vF)
    attendu = impl(et(E.est_surjective(vF, vX, vY), E.est_surjective(vG, vY, vZ)),
                   E.est_surjective(comp, vX, vZ))
    assert P2.composee_surjections().conclusion == attendu


def test_composee_surjections_non_triviale():
    # antécédent ≠ conséquent (ce n'est pas P⇒P) ; impl(A,B) = ou(non(A), B)
    c = P2.composee_surjections().conclusion
    ante = c.sous[0].sous[0]      # A  dans  ou(non(A), B)
    cons = c.sous[1]              # B
    assert ante != cons


def test_composee_surjections_autres_lettres():
    th = P2.composee_surjections("u", "v", "E", "Ep", "Epp")
    assert th.est_clos
    assert th.conclusion == P2.cible_composee_surjections("u", "v", "E", "Ep", "Epp")


# ── THÉORÈME 1 a+b) — composée de deux bijectives (au sens §II.49) ─────────────
def test_composee_bijectives_conclusion():
    th = P2.composee_bijectives()
    assert th.conclusion == P2.cible_composee_bijectives()


def test_composee_bijectives_hypotheses_structurelles():
    # données « f:X→Y, f':Y→Z applications » : F,G func, dom F=X, dom G=Y.
    th = P2.composee_bijectives()
    assert set(th.hypotheses) == P2.hypotheses_composee_bijectives()


def test_composee_bijectives_forme():
    vF, vG, vX, vY, vZ = var("F"), var("G"), var("X"), var("Y"), var("Z")
    comp = E.composee(vG, vF)
    attendu = impl(et(E.est_bijective(vF, vX, vY), E.est_bijective(vG, vY, vZ)),
                   E.est_bijective(comp, vX, vZ))
    assert P2.composee_bijectives().conclusion == attendu


def test_composee_bijectives_non_triviale():
    c = P2.composee_bijectives().conclusion
    ante = c.sous[0].sous[0]      # A  dans  ou(non(A), B)
    cons = c.sous[1]              # B
    assert ante != cons


# ── §II.3.3 — image directe par une composée de correspondances (ponctuel) ─────
def test_image_composee_membre_conclusion():
    th = P2.image_composee_membre()
    assert th.est_clos
    assert th.conclusion == P2.cible_image_composee_membre()


def test_image_composee_membre_forme():
    vGp, vG, vA = var("Gp"), var("G"), var("A")
    vy, vz = var("y"), var("z")
    comp = E.composee(vGp, vG)
    attendu = equiv(appartient(vz, E.image(comp, vA)),
                    existe("y", et(appartient(vy, E.image(vG, vA)),
                                   appartient(E.couple(vy, vz), vGp))))
    assert P2.image_composee_membre().conclusion == attendu


def test_image_composee_membre_autres_lettres():
    th = P2.image_composee_membre("Hp", "H", "B")
    assert th.est_clos
    assert th.conclusion == P2.cible_image_composee_membre("Hp", "H", "B")


# ── §II.3 — lien fonction de deux arguments ↔ application partielle (valeur) ────
def test_coupe_couple_membre_conclusion():
    th = P2.coupe_couple_membre()
    assert th.est_clos
    assert th.conclusion == P2.cible_coupe_couple_membre()


def test_coupe_couple_membre_forme():
    vG, va, vb, vz = var("G"), var("a"), var("b"), var("z")
    pair = E.couple(va, vb)
    attendu = equiv(appartient(vz, E.image(vG, E.singleton(pair))),
                    appartient(E.couple(pair, vz), vG))
    assert P2.coupe_couple_membre().conclusion == attendu


def test_coupe_couple_membre_autres_lettres():
    th = P2.coupe_couple_membre("H", "u", "v")
    assert th.est_clos
    assert th.conclusion == P2.cible_coupe_couple_membre("H", "u", "v")


def test_valeur_deux_arguments_conclusion():
    th = P2.valeur_deux_arguments()
    assert th.conclusion == P2.cible_valeur_deux_arguments()


def test_valeur_deux_arguments_hypotheses():
    # hyps C46 : G fonctionnel, (a,b) dans le domaine.
    th = P2.valeur_deux_arguments()
    vG, va, vb = var("G"), var("a"), var("b")
    pair = E.couple(va, vb)
    attendu = {
        E.est_fonctionnel(vG),
        existe("y", appartient(E.couple(pair, var("y")), vG)),
    }
    assert set(th.hypotheses) == attendu


def test_valeur_deux_arguments_forme():
    vG, va, vb, vy = var("G"), var("a"), var("b"), var("y")
    pair = E.couple(va, vb)
    attendu = equiv(appartient(E.couple(pair, vy), vG),
                    egal(vy, E.valeur(vG, pair)))
    assert P2.valeur_deux_arguments().conclusion == attendu


# ── Garde-fou global : les 5 conclusions sont distinctes (aucune tautologie vide) ─
def test_cinq_theoremes_distincts():
    concls = {
        P2.composee_surjections().conclusion,
        P2.composee_bijectives().conclusion,
        P2.image_composee_membre().conclusion,
        P2.coupe_couple_membre().conclusion,
        P2.valeur_deux_arguments().conclusion,
    }
    assert len(concls) == 5
