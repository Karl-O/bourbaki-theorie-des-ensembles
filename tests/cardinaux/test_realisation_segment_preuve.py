"""Tests MIROIR — ensembles_realisation_segment_preuve : FERMETURE du GATE ℕ.

`bon_ordre_intervalle(a)` est DÉRIVÉ de l'UNIQUE hypothèse HONNÊTE
`(∀c) realisation_segment(Ro,a,c)`, en CONTOURNANT le liant-TERME dégénéré de
`hyp_transport_ordinal` / `bo_form_artefact` (le pullback est tenu comme VARIABLE
FRAÎCHE « Tpb » puis ÉLIMINÉ par ∃Tpb ; bo_form bien formé déchargé par Zermelo).

INVARIANT vérifié partout : theorie_ensembles() = 22.
Anti-tautologie : aucune conclusion n'est l'une de ses hypothèses.
Hypothèses EXACTES contrôlées (test miroir).
"""
from bourbaki.logique.formule import var, pourtout, libres_f
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E

import bourbaki.cardinaux.ensembles_realisation_segment_preuve as RSP
import bourbaki.cardinaux.ensembles_hyp_transport_ordinal_preuve as HTP
import bourbaki.cardinaux.ensembles_bon_ordre_intervalle_ordinal as BOIO
from bourbaki.cardinaux.ensembles_ordinal_cardinal_correspondance import (
    bon_ordre_intervalle, cardinaux_bien_ordonnes_de_bon_ordre,
)


# ─────────────────────────────────────────────────────────────────────────────
#  theorie_ensembles INTANGIBLE = 22
# ─────────────────────────────────────────────────────────────────────────────
def test_theorie_ensembles_22():
    assert len(E.theorie_ensembles().axiomes) == 22


# ─────────────────────────────────────────────────────────────────────────────
#  🎯 ZERMELO BIEN FORMÉ : (∃Ro) bo_form(Ro,a)  CLOS (binders alignés bo_form).
# ─────────────────────────────────────────────────────────────────────────────
def test_zermelo_bo_form_conclusion():
    t = RSP.zermelo_bo_form("a")
    assert t.conclusion == RSP.zermelo_bo_form_cible("a")


def test_zermelo_bo_form_CLOS():
    t = RSP.zermelo_bo_form("a")
    assert len(t.hypotheses) == 0
    assert len(E.theorie_ensembles().axiomes) == 22


def test_zermelo_bo_form_pas_de_liant_terme():
    # la forme de bon ordre déposée par Zermelo est BIEN FORMÉE : tout liant est une
    # chaîne (le contournement du liant-TERME de bo_form_artefact).
    t = RSP.zermelo_bo_form("a")

    def composite_lieurs(g, path="root"):
        out = []
        lieur = getattr(g, "lieur", None)
        if lieur is not None and not isinstance(lieur, str):
            out.append(path)
        for i, s in enumerate(getattr(g, "sous", ()) or ()):
            out += composite_lieurs(s, f"{path}.{g.tag}[{i}]")
        return out

    assert composite_lieurs(t.conclusion) == []


# ─────────────────────────────────────────────────────────────────────────────
#  🎯 La CLAUSE pour S, SANS liant-TERME (pullback tenu comme variable Tpb).
# ─────────────────────────────────────────────────────────────────────────────
def test_clause_pour_S_sans_terme_hyps_bien_formees():
    cs = RSP.clause_pour_S_sans_terme("Ro", "a", "S")

    def composite_lieurs(g):
        out = []
        lieur = getattr(g, "lieur", None)
        if lieur is not None and not isinstance(lieur, str):
            out.append(g.tag)
        for s in getattr(g, "sous", ()) or ():
            out += composite_lieurs(s)
        return out

    # AUCUNE hypothèse ni la conclusion ne porte de liant-TERME.
    assert composite_lieurs(cs.conclusion) == []
    for h in cs.hypotheses:
        assert composite_lieurs(h) == []
    assert len(E.theorie_ensembles().axiomes) == 22


# ─────────────────────────────────────────────────────────────────────────────
#  🎯🎯 LE GATE ℕ — bon_ordre_intervalle(a) sous {realisation_segment} SEUL.
# ─────────────────────────────────────────────────────────────────────────────
def test_bon_ordre_intervalle_depuis_realisation_conclusion():
    t = RSP.bon_ordre_intervalle_depuis_realisation("a")
    assert t.conclusion == bon_ordre_intervalle("a")


def test_bon_ordre_intervalle_depuis_realisation_unique_hyp():
    t = RSP.bon_ordre_intervalle_depuis_realisation("a")
    # UNE SEULE hypothèse survivante : (∀c) realisation_segment(Ro,a,c).
    assert len(t.hypotheses) == 1
    assert set(t.hypotheses) == RSP.bon_ordre_intervalle_depuis_realisation_hypotheses("a")


def test_bon_ordre_intervalle_depuis_realisation_hyp_est_realisation():
    t = RSP.bon_ordre_intervalle_depuis_realisation("a")
    (hyp,) = t.hypotheses
    assert hyp == RSP.realisation_hypothese("Ro", "a")
    # l'hypothèse est Ro-INDÉPENDANTE (seg(a,·,t) ne porte pas Ro).
    assert "Ro" not in libres_f(hyp)


def test_bon_ordre_intervalle_depuis_realisation_pas_de_liant_terme():
    # PLUS de liant-TERME nulle part (ni conclusion ni hypothèse).
    t = RSP.bon_ordre_intervalle_depuis_realisation("a")

    def composite_lieurs(g):
        out = []
        lieur = getattr(g, "lieur", None)
        if lieur is not None and not isinstance(lieur, str):
            out.append(g.tag)
        for s in getattr(g, "sous", ()) or ():
            out += composite_lieurs(s)
        return out

    assert composite_lieurs(t.conclusion) == []
    for h in t.hypotheses:
        assert composite_lieurs(h) == []


def test_bon_ordre_intervalle_depuis_realisation_non_vacueux():
    # la conclusion n'est PAS l'une de ses hypothèses (anti-tautologie).
    t = RSP.bon_ordre_intervalle_depuis_realisation("a")
    assert t.conclusion not in set(t.hypotheses)


def test_bon_ordre_intervalle_depuis_realisation_theorie_22():
    RSP.bon_ordre_intervalle_depuis_realisation("a")
    assert len(E.theorie_ensembles().axiomes) == 22


# ─────────────────────────────────────────────────────────────────────────────
#  🎯 CHAÎNAGE — sous realisation, cardinaux_bien_ordonnes(a) est dérivable.
#  (bon_ordre_intervalle(a) → cardinaux_bien_ordonnes(a) via la réduction CLOSE.)
# ─────────────────────────────────────────────────────────────────────────────
def test_chaine_cardinaux_bien_ordonnes_sous_realisation():
    from bourbaki.logique import noyau_abrege as N
    boi = RSP.bon_ordre_intervalle_depuis_realisation("a")     # [realisation]
    red = cardinaux_bien_ordonnes_de_bon_ordre("a")            # { bon_ordre_intervalle(a) } ⊢ cardinaux_bien_ordonnes(a)
    # décharge bon_ordre_intervalle(a) par boi
    chained = N.modus_ponens(boi, N.loi_deduction(bon_ordre_intervalle("a"), red))
    # cardinaux_bien_ordonnes(a) sous l'UNIQUE hypothèse realisation
    assert len(chained.hypotheses) == 1
    assert set(chained.hypotheses) == RSP.bon_ordre_intervalle_depuis_realisation_hypotheses("a")
    assert len(E.theorie_ensembles().axiomes) == 22
