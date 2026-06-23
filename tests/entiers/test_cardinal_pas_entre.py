"""Tests §III.4 — LEMME N : « pas de cardinal strictement entre c et c+1 ».

Discipline LCF stricte : chaque test vérifie la CONCLUSION EXACTE et l'ensemble des
HYPOTHÈSES (clos pour les paliers INCONDITIONNELS ; reports ISOLÉS et précis pour le
maillon dur).

INVARIANT vérifié : theorie_ensembles() = 22 (aucun axiome nouveau ; rien postulé).

PALIERS :
  ✅ INCONDITIONNELS (.est_clos) :
       injection_surjective_est_bijection, bijection_implique_equipotent,
       card_succ_egale_succ.
  ⚙️ CONDITIONNELS (report ISOLÉ, jamais postulé) :
       branche_surjective         (sous est_cardinal(b)) ;
       cardinal_pas_entre_assemble (sous est_cardinal(b) ET retrait_point_hyp_universel),
                                   conclusion == cardinal_pas_entre(b,c) LITTÉRALEMENT ;
       cardinal_pas_entre_conditionnel (CLOS 0 hyp : les 2 reports en antécédent explicite).
"""
from bourbaki.logique.i_1_termes_relations.formule import var, egal, et, ou, impl, non, pourtout
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege import antecedent_consequent
from bourbaki.cardinaux.ensembles_cardinaux import (
    est_cardinal, est_injection_de, est_bijection_de, equipotent, cardinal,
    inf_egal_card,
)
from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import successeur
from bourbaki.entiers.iii_4_entiers_finis.iii_4_recurrence_c61_existence_n.ensembles_recurrence_C61 import cardinal_pas_entre
from bourbaki.entiers.iii_4_entiers_finis.iii_4_recurrence_c61_existence_n import ensembles_cardinal_pas_entre as L


# ── INVARIANT : theorie_ensembles() intangible = 22 ──────────────────────────
def test_theorie_ensembles_reste_22():
    assert len(E.theorie_ensembles().axiomes) == 22


# ── LEMMES INCONDITIONNELS ────────────────────────────────────────────────────
def test_injection_surjective_est_bijection_clos():
    """⊢ ( est_injection_de(F,X,Y) et image(F,X)=Y ) ⇒ est_bijection_de(F,X,Y) — CLOS."""
    vF, vX, vY = var("F"), var("X"), var("Y")
    thm = L.injection_surjective_est_bijection("F", "X", "Y")
    assert thm.est_clos
    ante, cons = antecedent_consequent(thm.conclusion)
    assert ante == et(est_injection_de(vF, vX, vY), egal(E.image(vF, vX), vY))
    assert cons == est_bijection_de(vF, vX, vY)


def test_bijection_implique_equipotent_clos():
    """⊢ est_bijection_de(F,X,Y) ⇒ Eq(X,Y) — CLOS (témoin F)."""
    vF, vX, vY = var("F"), var("X"), var("Y")
    thm = L.bijection_implique_equipotent("F", "X", "Y")
    assert thm.est_clos
    ante, cons = antecedent_consequent(thm.conclusion)
    assert ante == est_bijection_de(vF, vX, vY)
    assert cons == equipotent(vX, vY)


def test_card_succ_egale_succ_clos():
    """⊢ Card(c+1) = c+1 — CLOS (le successeur est un cardinal)."""
    vc = var("c")
    thm = L.card_succ_egale_succ("c")
    assert thm.est_clos
    assert thm.conclusion == egal(cardinal(successeur(vc)), successeur(vc))


# ── BRANCHE SURJECTIVE (conditionnelle à est_cardinal(b)) ─────────────────────
def test_branche_surjective_structure():
    """⊢ { est_cardinal(b) } ⊢ ( est_injection_de(f,b,c+1) et image(f,b)=c+1 ) ⇒ b=c+1.

    Une seule hypothèse résiduelle : est_cardinal(b) (jamais postulée comme théorème)."""
    vb, vc, vf = var("b"), var("c"), var("F")
    succ_c = successeur(vc)
    thm = L.branche_surjective("b", "c", "F")
    # exactement une hypothèse : est_cardinal(b)
    assert thm.hypotheses == frozenset({est_cardinal(vb)})
    ante, cons = antecedent_consequent(thm.conclusion)
    assert ante == et(est_injection_de(vf, vb, succ_c), egal(E.image(vf, vb), succ_c))
    assert cons == egal(vb, succ_c)


# ── ASSEMBLAGE = cardinal_pas_entre(b,c) modulo 2 reports ISOLÉS ──────────────
def test_cardinal_pas_entre_assemble_conclusion_litterale():
    """⊢ { est_cardinal(b), (∀F)retrait_point_hyp } ⊢ cardinal_pas_entre(b,c)
       — conclusion ÉGALE LITTÉRALEMENT à l'énoncé reporté de ensembles_recurrence_C61."""
    thm = L.cardinal_pas_entre_assemble("b", "c", "F")
    assert thm.conclusion == cardinal_pas_entre("b", "c")


def test_cardinal_pas_entre_assemble_reports_isoles():
    """Les hypothèses résiduelles sont EXACTEMENT les deux reports isolés :
       est_cardinal(b) et la surgery universelle retrait_point_hyp_universel(b,c)."""
    vb = var("b")
    thm = L.cardinal_pas_entre_assemble("b", "c", "F")
    ec = est_cardinal(vb)
    rp = L.retrait_point_hyp_universel("b", "c", "F")
    assert thm.hypotheses == frozenset({ec, rp})
    # le report dur n'est PAS clos (honnêteté : non postulé)
    assert not thm.est_clos


def test_retrait_point_hyp_enonce():
    """Énoncé exact du report dur (branche non surjective)."""
    vb, vc, vf = var("b"), var("c"), var("F")
    succ_c = successeur(vc)
    enonce = L.retrait_point_hyp("b", "c", "F")
    expected = impl(et(est_injection_de(vf, vb, succ_c),
                       non(egal(E.image(vf, vb), succ_c))),
                    inf_egal_card(vb, vc))
    assert enonce == expected
    # forme universelle = (∀F) de l'énoncé ponctuel
    assert L.retrait_point_hyp_universel("b", "c", "F") == pourtout("F", expected)


# ── FORME CONDITIONNELLE CLOSE (les 2 reports en antécédent explicite) ────────
def test_cardinal_pas_entre_conditionnel_clos():
    """⊢ ( est_cardinal(b) et (∀F)retrait_point_hyp ) ⇒ cardinal_pas_entre(b,c) — CLOS 0 hyp."""
    vb = var("b")
    thm = L.cardinal_pas_entre_conditionnel("b", "c", "F")
    assert thm.est_clos
    assert len(thm.hypotheses) == 0
    ante, cons = antecedent_consequent(thm.conclusion)
    expected_ante = et(est_cardinal(vb), L.retrait_point_hyp_universel("b", "c", "F"))
    assert ante == expected_ante
    # la conséquence EST l'énoncé verbatim du report de ensembles_recurrence_C61
    assert cons == cardinal_pas_entre("b", "c")
