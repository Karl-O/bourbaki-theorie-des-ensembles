"""Tests §IV.1.6–IV.2 — CRITÈRES DE STRUCTURES (CST), SUITE.

Vérifie pour chaque critère certifié dans `ensembles_cst_criteres_suite` :
  • la CLÔTURE conditionnelle (hypothèses EXPLICITES = axiomes-schémas instanciés :
    transport de la déduction CST6, antisymétrie MO_III, relations de transport
    induit IV.2 — JAMAIS des axiomes de la théorie) ;
  • l'ANTI-VACUITÉ : la conclusion N'EST PAS l'une des hypothèses ; pour CST7, l'on
    vérifie en outre que ce n'est PAS un P⇔P (les deux membres de l'équivalence sont
    des notions DISTINCTES est_isomorphisme(Σ,…) ≠ est_isomorphisme(Θ,…)) ;
  • l'IDENTITÉ LITTÉRALE de la conclusion à la cible fidèle ;
  • theorie_ensembles() reste à 22 axiomes (aucun axiome créé).
"""
from bourbaki.logique.i_1_termes_relations.formule import var, egal, et, equiv
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.cardinaux.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import est_bijection_de
from bourbaki.structures.iv_1_structures_isomorphismes.ensembles_especes import (
    Espece, est_isomorphisme, structure_transportee)
from bourbaki.structures.iv_1_structures_isomorphismes.ensembles_especes_echelon import Schema, schema_parties
from bourbaki.structures.iv_2_morphismes_structures_derivees.cst_criteres.ensembles_CST_criteres import (
    initiales_mutuellement_plus_fines)
import bourbaki.structures.iv_2_morphismes_structures_derivees.cst_criteres.ensembles_cst_criteres_suite as S


# ── espèces de test ──────────────────────────────────────────────────────────
def _sigma():
    """Espèce Σ minimale : 1 base, schéma identité S(E)=E."""
    return Espece(nom="Sig", n=1, auxiliaires=(), schema=Schema(((0, 1),)),
                  axiome=lambda bases, s: var("R"))


def _theta():
    """Espèce Θ déduite : schéma NON trivial T(E)=𝔓(E) (≠ S, pour la non-vacuité)."""
    return Espece(nom="Theta", n=1, auxiliaires=(), schema=schema_parties(),
                  axiome=lambda bases, s: var("RT"))


# ════════════════════════════════════════════════════════════════════════════
#  theorie = 22 (invariant intangible)
# ════════════════════════════════════════════════════════════════════════════
def test_theorie_reste_22():
    th = E.theorie_ensembles()
    assert len(th.axiomes) == 22


# ════════════════════════════════════════════════════════════════════════════
#  CST6 — fonctorialité de la déduction (IV.1.6)
# ════════════════════════════════════════════════════════════════════════════
def test_cst6_deduction_isomorphisme_certifie():
    """{h bijection, ⟨h,Id⟩^T(P{E,𝒮})=P{E',𝒮'}} ⊢ est_iso(Θ,(h),F,F',P{E,𝒮},P{E',𝒮'})."""
    theta = _theta()
    t = S.cst6_deduction_isomorphisme(theta)
    assert not t.est_clos
    assert len(t.hypotheses) == 2          # bijection h + clause (4) de la déduction
    cible = est_isomorphisme(theta, [var("h")], [var("F")], [var("Fp")],
                             var("P_ES"), var("P_EpSp"))
    assert t.conclusion == cible
    # non dégénéré
    assert t.conclusion not in t.hypotheses


def test_cst6_hypotheses_sont_les_axiomes_attendus():
    theta = _theta()
    t = S.cst6_deduction_isomorphisme(theta)
    bij = est_bijection_de(var("h"), var("F"), var("Fp"))
    eq4 = egal(structure_transportee(theta, [var("h")], var("P_ES")), var("P_EpSp"))
    assert bij in t.hypotheses
    assert eq4 in t.hypotheses


# ════════════════════════════════════════════════════════════════════════════
#  CST7 — isomorphismes et espèces équivalentes (IV.1.7)
# ════════════════════════════════════════════════════════════════════════════
def test_cst7_iso_ssi_deduit_certifie():
    """{clause(4)_Σ ⟺ clause(4)_Θ} ⊢ est_iso(Σ,…) ⟺ est_iso(Θ,…)."""
    sigma, theta = _sigma(), _theta()
    t = S.cst7_iso_ssi_deduit(sigma, theta)
    assert not t.est_clos
    assert len(t.hypotheses) == 1          # l'équivalence des clauses (4)
    iso_s = est_isomorphisme(sigma, [var("f")], [var("E")], [var("Ep")],
                             var("U"), var("Up"))
    iso_t = est_isomorphisme(theta, [var("f")], [var("E")], [var("Ep")],
                             var("P_U"), var("P_Up"))
    assert t.conclusion == equiv(iso_s, iso_t)
    # non dégénéré
    assert t.conclusion not in t.hypotheses


def test_cst7_PAS_un_P_ssi_P():
    """⚠ NON-VACUITÉ : CST7 relie DEUX notions DISTINCTES (Σ ≠ Θ), pas P⇔P (≠ piège mo3)."""
    sigma, theta = _sigma(), _theta()
    iso_s = est_isomorphisme(sigma, [var("f")], [var("E")], [var("Ep")],
                             var("U"), var("Up"))
    iso_t = est_isomorphisme(theta, [var("f")], [var("E")], [var("Ep")],
                             var("P_U"), var("P_Up"))
    # les deux membres de l'équivalence sont des formules DIFFÉRENTES
    assert iso_s != iso_t
    # l'unique hypothèse (équivalence des clauses 4) DIFFÈRE de la conclusion
    t = S.cst7_iso_ssi_deduit(sigma, theta)
    (hyp,) = tuple(t.hypotheses)
    assert hyp != t.conclusion


# ════════════════════════════════════════════════════════════════════════════
#  CST10 — transitivité des structures initiales (palier d'unicité, IV.2)
# ════════════════════════════════════════════════════════════════════════════
def test_cst10_initiales_egales_certifie():
    """{(IN_𝓘),(IN_𝓘'),2×id-morph,ANTISYM} ⊢ 𝓘 = 𝓘'."""
    t = S.cst10_initiales_egales()
    assert not t.est_clos
    assert t.conclusion == egal(var("I"), var("J"))
    # non dégénéré
    assert t.conclusion not in t.hypotheses
    # l'antisymétrie (MO_III) est une hypothèse explicite, identique au schéma CST9
    mut = initiales_mutuellement_plus_fines()
    from bourbaki.logique.i_1_termes_relations.formule import impl
    antisym = impl(mut.conclusion, egal(var("I"), var("J")))
    assert antisym in t.hypotheses
    # 5 hyps : 2 (IN) + 2 id-morph + ANTISYM
    assert len(t.hypotheses) == 5


# ════════════════════════════════════════════════════════════════════════════
#  CST11 — transitivité des structures induites (IV.2)
# ════════════════════════════════════════════════════════════════════════════
def test_cst11_induites_egales_certifie():
    """{ind_AC=⟨j_C⟩^S(𝒮), ind_BC=⟨j_C⟩^S(𝒮)} ⊢ ind_AC = ind_BC."""
    t = S.cst11_induites_egales()
    assert not t.est_clos
    assert len(t.hypotheses) == 2
    assert t.conclusion == egal(var("indAC"), var("indBC"))
    # non dégénéré : l'égalité finale n'est PAS une hypothèse
    assert t.conclusion not in t.hypotheses
    # les hyps relient chaque induite au TRANSPORTÉ commun
    from bourbaki.logique.i_1_termes_relations.formule import app
    T = app("transporte_induit", var("jC"), var("S"))
    assert egal(var("indAC"), T) in t.hypotheses
    assert egal(var("indBC"), T) in t.hypotheses


# ════════════════════════════════════════════════════════════════════════════
#  CST14 — compatibilité produit / sous-structure (IV.2)
# ════════════════════════════════════════════════════════════════════════════
def test_cst14_produit_induite_egales_certifie():
    """{S_indB=S_commun, S_prodB=S_commun} ⊢ S_indB = S_prodB."""
    t = S.cst14_produit_induite_egales()
    assert not t.est_clos
    assert len(t.hypotheses) == 2
    assert t.conclusion == egal(var("SindB"), var("SprodB"))
    # non dégénéré
    assert t.conclusion not in t.hypotheses
    from bourbaki.logique.i_1_termes_relations.formule import app
    assert egal(var("SindB"), var("Scommun")) in t.hypotheses
    assert egal(var("SprodB"), var("Scommun")) in t.hypotheses
