"""Tests MIROIR — ensembles_realisation_segment_close : GATE ℕ réduit au SEUL maillon
HONNÊTE, PUREMENT ORDRE-THÉORIQUE `subset_realise_segment(Ro,a)`

    (∀B)( B ⊂ a ⇒ (∃t)( t∈a et Eq( B , seg(a,Ro,t) ) ) ).

On vérifie :
  • iso_implique_equipotent et injection_donne_equipotent_image : CLOSED (0 hyp) ;
  • realisation_garde_depuis_subset : { subset } ⊢ realisation_segment_garde ;
  • pullback_onto_garde / pullback_non_vide_garde / corps_garde : MÊME conclusion que
    leurs miroirs HTP (la garde est_cardinal est déchargée par c∈[0,a]) ;
  • bon_ordre_intervalle_depuis_subset : { (∃Ro)(bo_form ∧ subset) } ⊢ bon_ordre_intervalle(a) ;
  • cardinaux_bien_ordonnes_depuis_subset : idem ⊢ cardinaux_bien_ordonnes(a).
    ⚠️ MIGRATION seg_ext (2026-07-31) : l'hypothèse est passée de `subset_realise_segment(Ro,a)`
    (Ro LIBRE) à sa forme Ro-CLOSE sous ∃ — le segment porte désormais son graphe.

INVARIANT vérifié partout : theorie_ensembles() = 22.
Anti-tautologie : aucune conclusion n'est l'une de ses hypothèses.
Hypothèses EXACTES contrôlées (test miroir).
"""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import existe, et, libres_f
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E

import bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.ordinal_cardinal.realisation_segment.ensembles_realisation_segment_close as M
import bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.ordinal_cardinal.realisation_segment.ensembles_hyp_transport_ordinal_preuve as HTP
import bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.ordinal_cardinal.bon_ordre_intervalle.ensembles_bon_ordre_intervalle_ordinal as BOIO
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.ordinal_cardinal.ordinal_cardinal_correspondance.ensembles_ordinal_cardinal_correspondance import bon_ordre_intervalle
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_recurrence_c61_existence_n.ensembles_recurrence_C61 import cardinaux_bien_ordonnes


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
#  L'HYPOTHÈSE ATTENDUE, RÉASSEMBLÉE ICI (hors du module) depuis les primitives.
#  ⚠️ MIGRATION seg_ext (2026-07-31) : elle est désormais Ro-CLOSE.  Le segment
#  portant son graphe, `subset_realise_segment(Ro,a)` a Ro LIBRE ; la laisser en
#  hypothèse résiduelle ferait échouer C27 lors de l'élimination du ∃Ro.  Le bon
#  ordre et la propriété demandée vivent donc sous LE MÊME ∃ (idiome déjà en place
#  au dépôt : `hyp_transport_ordinal`, E III.24).
# ─────────────────────────────────────────────────────────────────────────────
def _hyp_close_main(a="a", Ro="Ro"):
    """(∃Ro)( bo_form(Ro,a) ∧ subset_realise_segment(Ro,a) ) — RÉASSEMBLÉE.

    N'appelle PAS `M.subset_realise_segment_close` : comparer le module à son propre
    constructeur ne prouverait rien.  On rebâtit ∃/∧ depuis les primitives, sur les
    DEUX énoncés de base (bo_form canonique et le maillon subset)."""
    bo = BOIO._bo_form_canon(a, Ro, M._TPB, M._BM, M._BX)
    return existe(Ro, et(bo, M.subset_realise_segment(Ro, a)))


# ─────────────────────────────────────────────────────────────────────────────
#  🎯🎯 LE GATE ℕ — bon_ordre_intervalle(a) sous l'UNIQUE hypothèse Ro-CLOSE.
# ─────────────────────────────────────────────────────────────────────────────
def test_bon_ordre_intervalle_depuis_subset_conclusion():
    t = M.bon_ordre_intervalle_depuis_subset("a")
    assert t.conclusion == bon_ordre_intervalle("a")
    assert t.conclusion == M.bon_ordre_intervalle_depuis_subset_cible("a")


def test_bon_ordre_intervalle_depuis_subset_unique_hyp():
    t = M.bon_ordre_intervalle_depuis_subset("a")
    # frozenset RÉASSEMBLÉ (jamais un len() seul, jamais la sortie du module).
    assert len(t.hypotheses) == 1
    assert frozenset(t.hypotheses) == frozenset({_hyp_close_main("a")})
    assert M.hypothese_unique("a") == {_hyp_close_main("a")}


def test_bon_ordre_intervalle_depuis_subset_hyp_est_subset():
    """L'hypothèse EST la forme Ro-CLOSE, et l'ancienne forme Ro-libre NE SUFFIT PLUS.

    ⚠️ TEST REMPLACÉ (migration seg_ext, 2026-07-31) : il assertait
    `h == subset_realise_segment("Ro","a")`, forme à Ro LIBRE, qui n'était éliminable
    sous ∃Ro que parce que le terme de segment n'embarquait pas l'ordre."""
    t = M.bon_ordre_intervalle_depuis_subset("a")
    (h,) = tuple(t.hypotheses)
    assert h == _hyp_close_main("a")
    assert "Ro" not in libres_f(h)                       # Ro est LIÉ par le ∃
    ancienne = M.subset_realise_segment("Ro", "a")
    assert "Ro" in libres_f(ancienne)                    # l'ancienne, elle, a Ro LIBRE
    assert h != ancienne


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
    assert frozenset(t.hypotheses) == frozenset({_hyp_close_main("a")})


def test_cardinaux_bien_ordonnes_depuis_subset_non_vacueux():
    t = M.cardinaux_bien_ordonnes_depuis_subset("a")
    assert t.conclusion not in set(t.hypotheses)
    assert len(E.theorie_ensembles().axiomes) == 22


# ─────────────────────────────────────────────────────────────────────────────
#  🎯 LA GARANTIE NOUVELLE — le segment PORTE son ordre, donc la garde en DÉPEND.
# ─────────────────────────────────────────────────────────────────────────────
def test_garde_depend_bien_de_Ro_et_le_GATE_la_clot_sous_existe():
    """REMPLACE `test_garde_est_Ro_independante` (migration seg_ext, 2026-07-31).

    L'ANCIEN test épinglait « realisation_segment_garde et subset_realise_segment sont
    Ro-INDÉPENDANTES (seg(a,·,t) = seg_ext(a,t) ne porte pas Ro) », présentée comme la
    CONDITION de l'élimination du ∃Ro.  Cette Ro-indépendance était un ARTEFACT du
    défaut réparé : le terme de segment oubliait son ordre, si bien que deux ordres
    opposés partageaient un même terme muni d'axiomes contradictoires (⊢ ∅∈∅ ; cf.
    docs/journal/ANOMALIES.md, 2026-07-31).  L'objet du test a donc DISPARU.

    On épingle à la place la garantie NOUVELLE, en trois points :
      (a) le segment PORTE le graphe ⇒ garde et maillon DÉPENDENT de Ro (Ro libre) ;
      (b) le GATE les referme donc sous un ∃Ro, et son hypothèse est Ro-CLOSE ;
      (c) l'axiome de segment est lui-même CLOS (aucune variable libre) — plus aucune
          constante de théorie ne peut naître de ce site (défaut C27 éteint ici)."""
    # (a) DÉPENDANCE en Ro — mesurée, plus supposée.
    assert "Ro" in libres_f(M.realisation_segment_garde())
    assert "Ro" in libres_f(M.subset_realise_segment())
    # (b) le GATE referme Ro sous ∃ : son unique hypothèse n'a plus Ro libre.
    (h,) = tuple(M.bon_ordre_intervalle_depuis_subset("a").hypotheses)
    assert "Ro" not in libres_f(h)
    assert h == _hyp_close_main("a")
    # (c) l'axiome de segment est CLOS, et la fabrique de théorie n'a plus de paramètre.
    assert libres_f(E.axiome_segment_extremite()) == set()
    assert len(E.theorie_segment_extremite().axiomes) == 1
    assert len(E.theorie_ensembles().axiomes) == 22
