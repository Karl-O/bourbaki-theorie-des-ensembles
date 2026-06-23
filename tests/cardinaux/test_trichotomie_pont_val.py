"""Tests §III.2 — PONT « valeur d'un iso de segments dans F » (maillon val_dans_F DÉRIVÉ).

On certifie que le fait de CODOMAINE φ(p)∈F — que ensembles_trichotomie_dom_segment
postulait via l'hypothèse OPAQUE val_dans_F — est DÉRIVÉ des seules hypothèses de
STRUCTURE DE GRAPHE (φ⊂S×T, dom φ=S, p∈S) plus « T segment de F ».  theorie=22 ;
conclusions non tautologiques (φ(p)∈T / φ(p)∈F ∉ hypothèses) ; rien postulé.
"""
from bourbaki.logique.formule import (
    var, et, impl, egal, appartient, pourtout, inclus, Formule,
)
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.ordre.iii_1_relations_ordre.ordre_treillis import ensembles_ordre_vocab as V
from bourbaki.cardinaux import ensembles_trichotomie_pont_val as PV
from bourbaki.cardinaux import ensembles_trichotomie_dom_segment as DS


def _R_de(R):
    vR = var(R)
    return lambda a, b: appartient(E.couple(a, b), vR)


def _contient_sous_formule(f, cible):
    """True si `cible` apparaît (récursivement) comme sous-formule de `f`."""
    if f == cible:
        return True
    return any(_contient_sous_formule(s, cible) for s in getattr(f, "sous", ()))


# ── (1) valeur_iso_dans_T : φ(p) ∈ T depuis structure de graphe ───────────────
def test_valeur_iso_dans_T():
    """{ φ⊂S×T, dom φ=S, p∈S } ⊢ φ(p) ∈ T — CONDITIONNEL (structure), NON vacueux."""
    th = PV.valeur_iso_dans_T()
    assert not th.est_clos                                  # 3 hypothèses de structure
    vphi, vS, vT, vp = var("phi"), var("S"), var("T"), var("pt")
    assert th.conclusion == PV.valeur_iso_dans_T_cible()
    assert th.conclusion == appartient(E.valeur(vphi, vp), vT)
    hyps = list(th.hypotheses)
    assert inclus(vphi, E.produit(vS, vT)) in hyps          # φ ⊂ S×T
    assert egal(E.dom(vphi), vS) in hyps                    # dom φ = S
    assert appartient(vp, vS) in hyps                       # p ∈ S
    assert len(hyps) == 3
    assert th.conclusion not in th.hypotheses               # NON vacueux


# ── (2) valeur_iso_dans_F : maillon val_dans_F DÉRIVÉ ─────────────────────────
def test_valeur_iso_dans_F():
    """{ φ⊂S×T, dom φ=S, p∈S, seg(T,Rp,F) } ⊢ φ(p) ∈ F — le maillon DÉRIVÉ."""
    th = PV.valeur_iso_dans_F()
    assert not th.est_clos                                  # 4 hypothèses de structure
    vphi, vS, vT, vF, vp = var("phi"), var("S"), var("T"), var("F"), var("pt")
    Rpf = _R_de("Rp")
    assert th.conclusion == PV.valeur_iso_dans_F_cible()
    assert th.conclusion == appartient(E.valeur(vphi, vp), vF)
    hyps = list(th.hypotheses)
    assert inclus(vphi, E.produit(vS, vT)) in hyps          # φ ⊂ S×T
    assert egal(E.dom(vphi), vS) in hyps                    # dom φ = S
    assert appartient(vp, vS) in hyps                       # p ∈ S
    assert E.est_segment(vT, Rpf, vF) in hyps               # est_segment(T,Rp,F)
    assert len(hyps) == 4
    assert th.conclusion not in th.hypotheses               # NON vacueux : ∈F dérivé


def test_valeur_iso_dans_F_ne_postule_pas_la_conclusion():
    """La conclusion φ(p)∈F n'est aucune des 4 hypothèses (ce ne serait pas dérivé)."""
    th = PV.valeur_iso_dans_F()
    for h in th.hypotheses:
        assert h != th.conclusion


# ── (3) version universelle : DÉCHARGE le schéma val_dans_F ───────────────────
def test_val_dans_F_depuis_structure_close():
    """⊢ (∀p,S,T,φ)( STRUCT ⇒ φ(p)∈F ) — CLOS (0 hyp), NON vacueux."""
    th = PV.val_dans_F_depuis_structure()
    assert th.est_clos                                      # INCONDITIONNEL (sous le ⇒)
    assert len(th.hypotheses) == 0
    assert th.conclusion == PV.val_dans_F_depuis_structure_cible()


def test_struct_contient_la_structure_de_graphe():
    """STRUCT(p,S,T,φ) PORTE bien φ⊂S×T et dom φ=S (le maillon que l'iso n'a pas)."""
    vp, vS, vT, vphi = var("p"), var("S"), var("T"), var("phi")
    Rf, Rpf = _R_de("R"), _R_de("Rp")
    vE, vF = var("E"), var("F")
    struct = PV.struct_iso_segment("E", "R", "F", "Rp", vp, vS, vT, vphi)
    base = et(et(et(et(appartient(vp, vE), E.est_segment(vS, Rf, vE)),
                     E.est_segment(vT, Rpf, vF)),
                  V.est_isomorphisme_ordre(vphi, vS, vT, Rf, Rpf)),
              appartient(vp, vS))
    # STRUCT = ((base et φ⊂S×T) et dom φ=S) — les deux conjoints de structure de graphe
    attendu = et(et(base, inclus(vphi, E.produit(vS, vT))), egal(E.dom(vphi), vS))
    assert struct == attendu
    # la structure de graphe est BIEN présente comme sous-formules
    assert _contient_sous_formule(struct, inclus(vphi, E.produit(vS, vT)))   # φ ⊂ S×T
    assert _contient_sous_formule(struct, egal(E.dom(vphi), vS))            # dom φ = S


def test_struct_etend_la_premisse_de_val_dans_F():
    """La prémisse de val_dans_F (dom_segment) est INCLUSE dans STRUCT (5 premiers
    conjoints) : la version DÉRIVÉE est donc une EXTENSION fidèle (mêmes témoins)."""
    vp, vS, vT, vphi = var("p"), var("S"), var("T"), var("phi")
    Rf, Rpf = _R_de("R"), _R_de("Rp")
    vE, vF = var("E"), var("F")
    premisse_val_dans_F = et(et(et(et(
        appartient(vp, vE),
        E.est_segment(vS, Rf, vE)),
        E.est_segment(vT, Rpf, vF)),
        V.est_isomorphisme_ordre(vphi, vS, vT, Rf, Rpf)),
        appartient(vp, vS))
    struct = PV.struct_iso_segment("E", "R", "F", "Rp", vp, vS, vT, vphi)
    # la prémisse de val_dans_F est une SOUS-FORMULE de STRUCT (extension fidèle)
    assert _contient_sous_formule(struct, premisse_val_dans_F)


# ── invariants ────────────────────────────────────────────────────────────────
def test_theorie_intacte():
    assert len(E.theorie_ensembles().axiomes) == 22


def test_parametrable():
    th = PV.valeur_iso_dans_F("ph", "Sa", "Tb", "Bu", "Rb", "pt")
    assert not th.est_clos
    vphi, vS, vT, vF, vp = var("ph"), var("Sa"), var("Tb"), var("Bu"), var("pt")
    assert th.conclusion == appartient(E.valeur(vphi, vp), vF)
    assert len(th.hypotheses) == 4
