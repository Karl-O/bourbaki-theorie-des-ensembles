"""Tests §III.2 — Théorème 3 (TRICHOTOMIE) : EXTENSION-ISO de l'adjonction du sommet.

On certifie (ensembles_trichotomie_extension_iso) le CŒUR D'ORDRE / SURJECTION reporté
par temoin_est_iso_segments_report : h⁺ = h ∪ {(a,b)} est un ISO D'ORDRE de S∪{a}=]←,a]
sur T∪{b}=]←,b] pour relation_adjoint, SACHANT que h:S≅T est iso de segments et que
a/b sont les sommets.

  ✅ INCONDITIONNELS (theorie=22, 0 hyp) :
     • point_graphe_injectif : injective_dans({(a,b)}, dom{(a,b)}).
     • image_point_graphe    : image({(a,b)}, {a}) = {b}.
  ⚠️ CONDITIONNELS (hypothèses EXPLICITES, REPORTÉ précis) :
     • compat_extension_sous_iso     : compatible_ordre(h⁺, S∪{a}, ≤'_a, ≤'_b)  [maillon B].
     • injectivite_extension_sous    : injective_dans(h⁺, S∪{a})                [maillon A].
     • surjectivite_extension_sous   : est_surjective(h⁺, S∪{a}, T∪{b})         [maillon A].
     • bijection_extension_sous      : est_bijective(h⁺, S∪{a}, T∪{b}).
     • extension_est_iso_segments    : est_isomorphisme_ordre(h⁺, S∪{a}, T∪{b}, ≤'_a, ≤'_b).
     • extension_iso_depuis_iso_h    : idem, hypothèse centrale = h iso de S sur T (capture-free).

theorie_ensembles() reste = 22 ; rien postulé ; conclusions non tautologiques.

⚠️ NUANCE DE FIDÉLITÉ : temoin_est_iso_segments_report utilise est_isomorphisme_ordre avec
les binders PAR DÉFAUT x='x', y='y', or compatible_ordre y forme valeur(f,y)=τy((y,y)∈f)
— le « y » y est CAPTURÉ par le τ interne (bug latent de binder). Ce module prouve la
version CORRECTE (capture-free, binders xa/ya), qui est l'INTENTION du report.
"""
from bourbaki.logique.formule import var, egal, appartient, non, Formule
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.cardinaux import ensembles_trichotomie_scaffold as TS
from bourbaki.cardinaux import ensembles_trichotomie_extension_iso as X


_hg = TS.h_iso_max("E", "R", "F", "Rp")
_func_h = E.est_fonctionnel(_hg)
_a_hors = non(appartient(var("a"), E.dom(_hg)))


# ════════════════════════════════════════════════════════════════════════════
#  ✅ INCONDITIONNELS.
# ════════════════════════════════════════════════════════════════════════════
def test_point_graphe_injectif():
    thm = X.point_graphe_injectif()
    assert thm.est_clos and not thm.hypotheses
    assert thm.conclusion == X.point_graphe_injectif_cible()


def test_image_point_graphe():
    thm = X.image_point_graphe()
    assert thm.est_clos and not thm.hypotheses
    assert thm.conclusion == X.image_point_graphe_cible()
    assert thm.conclusion.tag == "="


# ════════════════════════════════════════════════════════════════════════════
#  ⚠️ (B) COMPATIBILITÉ D'ORDRE — CŒUR substantiel, 7 hyps explicites.
# ════════════════════════════════════════════════════════════════════════════
def test_compat_extension_sous_iso():
    thm = X.compat_extension_sous_iso()
    assert not thm.est_clos
    assert thm.conclusion == X.compat_extension_cible()
    assert thm.conclusion not in thm.hypotheses
    expected = {
        X.hyp_compat_h(),
        X.hyp_h_envoie_S_dans_T(),
        X.hyp_S_inclus_dom_h(),
        X.hyp_a_sommet_de_S(),
        X.hyp_b_sommet_de_T(),
        _func_h,
        _a_hors,
    }
    assert set(thm.hypotheses) == expected


# ════════════════════════════════════════════════════════════════════════════
#  ⚠️ (A) BIJECTION — injectivité / surjectivité / bijection.
# ════════════════════════════════════════════════════════════════════════════
def test_injectivite_extension_sous():
    thm = X.injectivite_extension_sous()
    assert not thm.est_clos
    assert thm.conclusion == X.injectivite_extension_cible()
    assert thm.conclusion not in thm.hypotheses
    expected = {
        _func_h, _a_hors,
        X.hyp_h_injective_sur_S(),
        X.hyp_images_disjointes(),
        X.hyp_dom_h_egale_S(),
    }
    assert set(thm.hypotheses) == expected


def test_surjectivite_extension_sous():
    thm = X.surjectivite_extension_sous()
    assert not thm.est_clos
    assert thm.conclusion == X.surjectivite_extension_cible()
    assert thm.conclusion.tag == "="
    expected = {X.hyp_dom_h_egale_S(), X.hyp_h_surjective_sur_S()}
    assert set(thm.hypotheses) == expected


def test_bijection_extension_sous():
    thm = X.bijection_extension_sous()
    assert not thm.est_clos
    assert thm.conclusion == X.bijection_extension_cible()
    assert thm.conclusion not in thm.hypotheses
    assert len(thm.hypotheses) == 6


# ════════════════════════════════════════════════════════════════════════════
#  🎯 ASSEMBLAGE — h⁺ est un ISO D'ORDRE des segments adjoints.
# ════════════════════════════════════════════════════════════════════════════
def test_extension_est_iso_segments():
    thm = X.extension_est_iso_segments()
    assert not thm.est_clos
    assert thm.conclusion == X.extension_est_iso_segments_cible()
    assert thm.conclusion not in thm.hypotheses
    assert set(thm.hypotheses) == set(X.extension_hypotheses())
    assert len(thm.hypotheses) == 11
    # la conclusion est bien un est_isomorphisme_ordre (et = bijective ∧ compatible)
    assert thm.conclusion.tag == "non"   # et encodé ¬(¬∨¬)


def test_extension_iso_depuis_iso_h():
    thm = X.extension_iso_depuis_iso_h()
    assert not thm.est_clos
    assert thm.conclusion == X.extension_est_iso_segments_cible()
    assert thm.conclusion not in thm.hypotheses
    assert set(thm.hypotheses) == set(X.extension_iso_depuis_iso_h_hypotheses())
    assert len(thm.hypotheses) == 9
    # l'hypothèse centrale EST bien l'iso de segments capture-free
    assert X.iso_segments_capture_free() in thm.hypotheses


# ════════════════════════════════════════════════════════════════════════════
#  NON-VACUITÉ : aucune conclusion conditionnelle n'est l'une de ses hypothèses.
# ════════════════════════════════════════════════════════════════════════════
def test_non_vacuite():
    for f in (X.compat_extension_sous_iso, X.injectivite_extension_sous,
              X.surjectivite_extension_sous, X.bijection_extension_sous,
              X.extension_est_iso_segments, X.extension_iso_depuis_iso_h):
        thm = f()
        assert thm.conclusion not in thm.hypotheses


# ════════════════════════════════════════════════════════════════════════════
#  INVARIANT global : theorie_ensembles() intacte = 22.
# ════════════════════════════════════════════════════════════════════════════
def test_theorie_intacte():
    X.point_graphe_injectif()
    X.image_point_graphe()
    X.compat_extension_sous_iso()
    X.injectivite_extension_sous()
    X.surjectivite_extension_sous()
    X.extension_est_iso_segments()
    X.extension_iso_depuis_iso_h()
    assert len(E.theorie_ensembles().axiomes) == 22
