"""Tests §III.2 — COR 1 / UNICITÉ, variante SOUS-DOMAINE S ⊆ E.

On certifie le CŒUR de l'unicité généralisé à un SOUS-DOMAINE : un automorphisme
d'ordre h : S → S (S⊆E, ordre AMBIANT de E) est l'identité sur S
(point_fixe_automorphisme_sous_domaine, dérivé de lemme_4_sous_domaine +
antisymétrie AMBIANTE).  On vérifie : 7 hypothèses STRUCTURELLES EXACTES (dont
inclus(S,E), JAMAIS bo(R,S)), conclusion fidèle (= cible), non tautologique ;
auto_iso_est_identite_sous_domaine en miroir ; theorie_ensembles() reste = 22.
"""
from bourbaki.logique.formule import var, egal, impl, appartient, pourtout, inclus
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.cardinaux import ensembles_iso_unicite_sous_domaine as U
from bourbaki.cardinaux.ensembles_lemme4_croissante import _R_de, _val
from bourbaki.cardinaux.ensembles_lemme4_sous_domaine import _f_dans_S
from bourbaki.ordre.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_monotone import est_strictement_croissante


def test_point_fixe_sous_domaine():
    """{ bo(R,E), inclus(S,E), h:S→S, h scr, k:S→S, k scr, k∘h=id_S }
            ⊢ (∀x)(x∈S ⇒ h(x)=x)."""
    pf = U.point_fixe_automorphisme_sous_domaine()
    assert not pf.est_clos
    assert len(pf.hypotheses) == 7
    assert pf.conclusion == U.point_fixe_automorphisme_sous_domaine_cible()
    assert pf.conclusion not in pf.hypotheses           # non tautologique


def test_point_fixe_sous_domaine_hypotheses_structurelles():
    """Les 7 hypothèses sont EXACTEMENT les attendues (rien en trop, rien postulé)."""
    pf = U.point_fixe_automorphisme_sous_domaine()
    hyps = set(pf.hypotheses)
    vR, vE, vS, vh, vk = var("R"), var("E"), var("S"), var("h"), var("k")
    Rf = _R_de("R")
    vx = var("x")
    hx = _val(vh, vx)
    expected = {
        E.est_bien_ordonne(Rf, vE),                                       # bon ordre AMBIANT (R,E)
        inclus(vS, vE),                                                   # inclus(S,E)
        _f_dans_S(vh, vS),                                               # h : S→S
        est_strictement_croissante(vR, vR, vh, vS, vS),                  # h strict croissante S→S
        _f_dans_S(vk, vS),                                               # k : S→S
        est_strictement_croissante(vR, vR, vk, vS, vS),                  # k strict croissante S→S
        pourtout("x", impl(appartient(vx, vS), egal(_val(vk, hx), vx))),  # k∘h = id_S
    }
    assert hyps == expected
    # 🎯 le bon ordre est l'AMBIANT bo(R,E), JAMAIS bo(R,S) (faux pour S⊊E !)
    assert E.est_bien_ordonne(Rf, vE) in hyps
    assert E.est_bien_ordonne(Rf, vS) not in hyps
    assert inclus(vS, vE) in hyps                                         # inclus(S,E) réellement requis
    # la stricte croissance SUR S des DEUX applications est réellement requise
    assert est_strictement_croissante(vR, vR, vh, vS, vS) in hyps
    assert est_strictement_croissante(vR, vR, vk, vS, vS) in hyps


def test_point_fixe_sous_domaine_parametrable():
    pf = U.point_fixe_automorphisme_sous_domaine("Rp", "F", "T", "phi", "psi")
    assert len(pf.hypotheses) == 7
    assert pf.conclusion == U.point_fixe_automorphisme_sous_domaine_cible(
        "Rp", "F", "T", "phi", "psi")
    # toujours pas de bon ordre sur le sous-domaine T
    Rf = _R_de("Rp")
    assert E.est_bien_ordonne(Rf, var("T")) not in set(pf.hypotheses)
    assert E.est_bien_ordonne(Rf, var("F")) in set(pf.hypotheses)


def test_auto_iso_est_identite_sous_domaine():
    """Emballage Cor 1 (sous-domaine) : mêmes 7 hypothèses, même conclusion fidèle."""
    ai = U.auto_iso_est_identite_sous_domaine()
    assert not ai.est_clos
    assert len(ai.hypotheses) == 7
    assert ai.conclusion == U.auto_iso_est_identite_sous_domaine_cible()
    assert ai.conclusion not in ai.hypotheses
    # mêmes hypothèses que le cœur (réutilise point_fixe_automorphisme_sous_domaine)
    pf = U.point_fixe_automorphisme_sous_domaine()
    assert set(ai.hypotheses) == set(pf.hypotheses)
    assert ai.conclusion == pf.conclusion


def test_theorie_intacte():
    assert len(E.theorie_ensembles().axiomes) == 22
