"""Tests §III.2 — décharge de la géométrie de coincidence (vers clôture trichotomie).

BRIQUE 1 — `composee_dans_S` : c=g∘f : S→S (codomaine de la composée).
Honnêteté LCF : conditionnel propre (hyps structurelles f⊂S×T/dom/func + g⊂T×S/dom/func),
conclusion == cible fidèle, NON vacueux (concl ∉ hyps), theorie = 22.
"""
from bourbaki.ensembles import ensembles_abrege as E
import bourbaki.cardinaux.ensembles_coincidence_geometrie as G


def test_composee_dans_S_conclusion():
    t = G.composee_dans_S()
    assert not t.est_clos                              # conditionnel honnête
    assert t.conclusion == G.composee_dans_S_cible()  # (∀t)(t∈S ⇒ (g∘f)(t)[j]∈S)
    assert t.conclusion not in t.hypotheses           # NON tautologique


def test_composee_dans_S_hyps_structurelles():
    """Les 6 hypothèses sont exactement les données structurelles d'iso (graphe⊂produit,
    domaine, fonctionnel) pour f et g — aucune cachée, aucune géométrique postulée."""
    t = G.composee_dans_S()
    assert len(t.hypotheses) == 6


def test_raccord_phip_conclusion():
    """BRIQUE 4 — raccord φ'(c(u))=φ(u), c=φ'⁻¹∘φ.  Conditionnel propre, fidèle, non vacueux."""
    t = G.raccord_phip()
    assert not t.est_clos
    assert t.conclusion == G.raccord_phip_cible()
    assert t.conclusion not in t.hypotheses


def test_raccord_phip_hyps():
    t = G.raccord_phip()
    assert len(t.hypotheses) == 5


def test_retraction_phi_conclusion():
    """Sous-lemme BRIQUE 3 — φ⁻¹(φ(x))=x (retraction de φ).  Point φ(x) en « j » pour
    éviter la capture du liant « y » de valeur_caracterisation.  2 hyps {dom φ=S, φ⁻¹ func}."""
    t = G.retraction_phi()
    assert not t.est_clos
    assert t.conclusion == G.retraction_phi_cible()
    assert t.conclusion not in t.hypotheses
    assert len(t.hypotheses) == 2


def test_retraction_kc_conclusion():
    """BRIQUE 3 — k∘c=id (rétraction).  k(c(x))=φ⁻¹(φ'(φ'⁻¹(φ(x))))=φ⁻¹(φ(x))=x via
    composition_valeur_t (×2) + section_reciproque + retraction_phi.  Conditionnel fidèle."""
    t = G.retraction_kc()
    assert not t.est_clos
    assert t.conclusion == G.retraction_kc_cible()
    assert t.conclusion not in t.hypotheses


def test_composee_dans_S_t_termes():
    """Version TERMES de composee_dans_S (pour c=composee(reciproque φ',φ), g terme).
    composition_valeur_t au lieu de composition_valeur → 1 hyp comp-func en plus."""
    from bourbaki.logique.formule import var
    t = G.composee_dans_S_t(E.reciproque(var("phip")), var("phi"), var("S"), var("T"))
    assert not t.est_clos
    # même cible que composee_dans_S mais avec le terme composé
    c = E.composee(E.reciproque(var("phip")), var("phi"))
    from bourbaki.logique.formule import pourtout, impl, appartient
    cible = pourtout("t", impl(appartient(var("t"), var("S")),
                               appartient(E.valeur(c, var("t"), b="j"), var("S"))))
    assert t.conclusion == cible
    assert t.conclusion not in t.hypotheses


def test_coincidence_close_assemblage():
    """🎯 ASSEMBLAGE : coïncidence (Lemme 1) avec les 4 familles de géométrie DÉCHARGÉES.
    Conditionnel sur {bon ordre, c/k strict. croissantes, structurelles iso} SEULEMENT —
    le résidu géométrique (c,k:S→S, k∘c=id, raccord) n'est PLUS une hypothèse."""
    from bourbaki.logique.formule import var, pourtout, impl, appartient
    t = G.coincidence_close()
    assert not t.est_clos
    assert t.conclusion == G.coincidence_close_cible()      # (∀u)(u∈S ⇒ φ(u)=φ'(u))
    assert t.conclusion not in t.hypotheses                 # NON tautologique
    # les 4 familles de géométrie sont ABSENTES des hypothèses (déchargées) :
    vphi, vphip, vS = var("phi"), var("phip"), var("S")
    c = E.composee(E.reciproque(vphip), vphi)
    cod_c = pourtout("t", impl(appartient(var("t"), vS),
                               appartient(E.valeur(c, var("t"), b="j"), vS)))
    assert cod_c not in t.hypotheses                        # cod_c DÉCHARGÉE


def test_coincidence_close_isos_strict_dechargee():
    """🎯🎯 STRICTE CROISSANCE DÉCHARGÉE : coincidence_close_isos dérive la stricte
    croissance de c=φ'⁻¹∘φ et k=φ⁻¹∘φ' depuis les isos (auto_de_deux_isos +
    strict_croissante_depuis_iso) — il ne reste AUCUNE hyp de stricte croissance."""
    t = G.coincidence_close_isos()
    assert not t.est_clos
    assert t.conclusion == G.coincidence_close_cible()         # conclusion préservée
    assert t.conclusion not in t.hypotheses                    # NON tautologique
    # AUCUNE hypothèse de stricte croissance ne subsiste (toutes dérivées des isos) :
    assert all("croissante" not in repr(h) for h in t.hypotheses)


def test_coincidence_univ_close_nestee():
    """🎯 VERSION NESTÉE : φ1:S1≅T1, φ2 sur segment ⊃ S1 (S1⊂dom φ2) coïncident sur S1.
    coincidence_close(φ1, φ2|S1) + restriction_valeur → (∀u)(u∈S1⇒φ1(u)=φ2(u)).
    C'est la forme consommée par fusion_hyp (Lemme 1 §III.2)."""
    t = G.coincidence_univ_close()
    assert not t.est_clos
    assert t.conclusion == G.coincidence_univ_close_cible()    # (∀u)(u∈S1 ⇒ φ1(u)=φ2(u))
    assert t.conclusion not in t.hypotheses                    # NON tautologique


def test_coincidence_univ_close_isos_nestee_strict_dechargee():
    """🎯🎯 VERSION NESTÉE + STRICTE CROISSANCE DÉCHARGÉE : φ1:S1≅T1, φ2 sur segment ⊃ S1
    coïncident sur S1, SANS hyp de stricte croissance (via coincidence_close_isos)."""
    t = G.coincidence_univ_close_isos()
    assert not t.est_clos
    assert t.conclusion == G.coincidence_univ_close_cible()    # (∀u)(u∈S1 ⇒ φ1(u)=φ2(u))
    assert t.conclusion not in t.hypotheses                    # NON tautologique
    assert all("croissante" not in repr(h) for h in t.hypotheses)


def test_theorie_inchangee_22():
    G.composee_dans_S()
    G.raccord_phip()
    G.retraction_phi()
    G.retraction_kc()
    G.coincidence_close()
    G.coincidence_close_isos()
    G.coincidence_univ_close()
    G.coincidence_univ_close_isos()
    assert len(E.theorie_ensembles().axiomes) == 22
