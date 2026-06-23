"""Tests MIROIR — ensembles_realisation_segment_close : GATE ℕ réduit au SEUL maillon
HONNÊTE, PUREMENT ORDRE-THÉORIQUE `subset_realise_segment(Ro,a)`

    (∀B)( B ⊂ a ⇒ (∃t)( t∈a et Eq( B , seg(a,Ro,t) ) ) ).

On vérifie :
  • iso_implique_equipotent et injection_donne_equipotent_image : CLOSED (0 hyp) ;
  • realisation_garde_depuis_subset : { subset } ⊢ realisation_segment_garde ;
  • pullback_onto_garde / pullback_non_vide_garde / corps_garde : MÊME conclusion que
    leurs miroirs HTP (la garde est_cardinal est déchargée par c∈[0,a]) ;
  • bon_ordre_intervalle_depuis_subset : { subset } ⊢ bon_ordre_intervalle(a) ;
  • cardinaux_bien_ordonnes_depuis_subset : { subset } ⊢ cardinaux_bien_ordonnes(a).

INVARIANT vérifié partout : theorie_ensembles() = 22.
Anti-tautologie : aucune conclusion n'est l'une de ses hypothèses.
Hypothèses EXACTES contrôlées (test miroir).
"""
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E

import bourbaki.cardinaux.iii_4_ordinal_cardinal.realisation_segment.ensembles_realisation_segment_close as M
import bourbaki.cardinaux.iii_4_ordinal_cardinal.realisation_segment.ensembles_hyp_transport_ordinal_preuve as HTP
from bourbaki.cardinaux.iii_4_ordinal_cardinal.ordinal_cardinal_correspondance.ensembles_ordinal_cardinal_correspondance import bon_ordre_intervalle
from bourbaki.entiers.iii_4_entiers_finis.iii_4_recurrence_c61_existence_n.ensembles_recurrence_C61 import cardinaux_bien_ordonnes


# ─────────────────────────────────────────────────────────────────────────────
#  theorie_ensembles INTANGIBLE = 22
# ─────────────────────────────────────────────────────────────────────────────
def test_theorie_ensembles_22():
    assert len(E.theorie_ensembles().axiomes) == 22


# ─────────────────────────────────────────────────────────────────────────────
#  ✅ BRIQUE 1 — iso_implique_equipotent : CLOSED (récupération func/dom ⇒ Eq).
# ─────────────────────────────────────────────────────────────────────────────
def test_iso_implique_equipotent_conclusion():
    t = M.iso_implique_equipotent()
    assert t.conclusion == M.iso_implique_equipotent_cible()


def test_iso_implique_equipotent_CLOS():
    t = M.iso_implique_equipotent()
    assert len(t.hypotheses) == 0
    assert t.est_clos
    assert len(E.theorie_ensembles().axiomes) == 22


def test_iso_implique_equipotent_non_vacueux():
    t = M.iso_implique_equipotent()
    assert t.conclusion not in set(t.hypotheses)


# ─────────────────────────────────────────────────────────────────────────────
#  ✅ BRIQUE 2 — injection_donne_equipotent_image : CLOSED.
# ─────────────────────────────────────────────────────────────────────────────
def test_injection_donne_equipotent_image_conclusion():
    t = M.injection_donne_equipotent_image()
    assert t.conclusion == M.injection_donne_equipotent_image_cible()


def test_injection_donne_equipotent_image_CLOS():
    t = M.injection_donne_equipotent_image()
    assert len(t.hypotheses) == 0
    assert t.est_clos
    assert len(E.theorie_ensembles().axiomes) == 22


# ─────────────────────────────────────────────────────────────────────────────
#  🎯 realisation_garde_depuis_subset : { subset } ⊢ realisation_segment_garde.
# ─────────────────────────────────────────────────────────────────────────────
def test_realisation_garde_depuis_subset_conclusion():
    t = M.realisation_garde_depuis_subset()
    assert t.conclusion == M.realisation_segment_garde()


def test_realisation_garde_depuis_subset_unique_hyp():
    t = M.realisation_garde_depuis_subset()
    assert len(t.hypotheses) == 1
    assert set(t.hypotheses) == {M.subset_realise_segment()}


def test_realisation_garde_depuis_subset_non_vacueux():
    t = M.realisation_garde_depuis_subset()
    assert t.conclusion not in set(t.hypotheses)
    assert len(E.theorie_ensembles().axiomes) == 22


# ─────────────────────────────────────────────────────────────────────────────
#  🎯 ONTO / ≠∅ / corps GARDÉS — MÊME conclusion que les miroirs HTP.
# ─────────────────────────────────────────────────────────────────────────────
def test_pullback_onto_garde_meme_conclusion_que_HTP():
    g = M.pullback_onto_garde()
    o = HTP.pullback_onto()
    assert g.conclusion == o.conclusion


def test_pullback_non_vide_garde_meme_conclusion_que_HTP():
    g = M.pullback_non_vide_garde()
    o = HTP.pullback_non_vide()
    assert g.conclusion == o.conclusion


def test_corps_garde_conclusion():
    g = M.corps_garde()
    assert g.conclusion == HTP.hyp_transport_corps_cible()


def test_corps_garde_hypotheses():
    g = M.corps_garde()
    # { S⊂[0,a], S≠∅, realisation_segment_garde } — 3 hypothèses honnêtes
    assert len(g.hypotheses) == 3
    assert M.realisation_segment_garde() in set(g.hypotheses)
    assert len(E.theorie_ensembles().axiomes) == 22


# ─────────────────────────────────────────────────────────────────────────────
#  🎯🎯 LE GATE ℕ — bon_ordre_intervalle(a) sous { subset_realise_segment } SEUL.
# ─────────────────────────────────────────────────────────────────────────────
def test_bon_ordre_intervalle_depuis_subset_conclusion():
    t = M.bon_ordre_intervalle_depuis_subset("a")
    assert t.conclusion == bon_ordre_intervalle("a")
    assert t.conclusion == M.bon_ordre_intervalle_depuis_subset_cible("a")


def test_bon_ordre_intervalle_depuis_subset_unique_hyp():
    t = M.bon_ordre_intervalle_depuis_subset("a")
    assert len(t.hypotheses) == 1
    assert set(t.hypotheses) == M.hypothese_unique("a")


def test_bon_ordre_intervalle_depuis_subset_hyp_est_subset():
    t = M.bon_ordre_intervalle_depuis_subset("a")
    (h,) = tuple(t.hypotheses)
    assert h == M.subset_realise_segment("Ro", "a")


def test_bon_ordre_intervalle_depuis_subset_non_vacueux():
    t = M.bon_ordre_intervalle_depuis_subset("a")
    assert t.conclusion not in set(t.hypotheses)
    assert len(E.theorie_ensembles().axiomes) == 22


def test_bon_ordre_intervalle_depuis_subset_pas_de_liant_terme():
    # conclusion et hypothèse BIEN FORMÉES : tout liant est une chaîne.
    t = M.bon_ordre_intervalle_depuis_subset("a")

    def composite_lieurs(g):
        out = []
        lieur = getattr(g, "lieur", None)
        if lieur is not None and not isinstance(lieur, str):
            out.append(getattr(g, "tag", "?"))
        for s in getattr(g, "sous", ()) or ():
            out += composite_lieurs(s)
        return out

    assert composite_lieurs(t.conclusion) == []
    for h in t.hypotheses:
        assert composite_lieurs(h) == []


# ─────────────────────────────────────────────────────────────────────────────
#  🎯🎯 cardinaux_bien_ordonnes(a) sous { subset_realise_segment } SEUL.
# ─────────────────────────────────────────────────────────────────────────────
def test_cardinaux_bien_ordonnes_depuis_subset_conclusion():
    t = M.cardinaux_bien_ordonnes_depuis_subset("a")
    assert t.conclusion == cardinaux_bien_ordonnes("a")
    assert t.conclusion == M.cardinaux_bien_ordonnes_depuis_subset_cible("a")


def test_cardinaux_bien_ordonnes_depuis_subset_unique_hyp():
    t = M.cardinaux_bien_ordonnes_depuis_subset("a")
    assert len(t.hypotheses) == 1
    assert set(t.hypotheses) == M.hypothese_unique("a")


def test_cardinaux_bien_ordonnes_depuis_subset_non_vacueux():
    t = M.cardinaux_bien_ordonnes_depuis_subset("a")
    assert t.conclusion not in set(t.hypotheses)
    assert len(E.theorie_ensembles().axiomes) == 22


# ─────────────────────────────────────────────────────────────────────────────
#  La cible se DÉCHARGE-t-elle dans bon_ordre_intervalle_depuis_realisation ?
#  (Le maillon subset est STRICTEMENT plus honnête que la fausse (∀c)realisation.)
# ─────────────────────────────────────────────────────────────────────────────
def test_garde_est_Ro_independante():
    # realisation_segment_garde et subset_realise_segment sont Ro-INDÉPENDANTES
    # (seg(a,·,t) = seg_ext(a,t) ne porte pas Ro), condition de l'élimination ∃Ro.
    from bourbaki.logique.i_1_termes_relations.formule import libres_f
    assert "Ro" not in libres_f(M.realisation_segment_garde())
    assert "Ro" not in libres_f(M.subset_realise_segment())
