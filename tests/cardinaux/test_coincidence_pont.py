"""Tests §III.2 — Lemme 1 : PONT « valeur d'application » qui DÉCHARGE le RÉSIDU
REPRÉSENTATIONNEL (stricte croissance τ_j) de `coincidence_depuis_isos`.

Certifie que `ensembles_coincidence_pont` livre :

  ✅ compat_y_vers_jv         : { compatible_ordre(c,S,R,R) [τ_y] } ⊢ _compat_yv(c,S,R) [τ_j]
     — PONT b=y ↔ b=j sur la compatibilité d'ordre (Leibniz S6 + valeur_y_egal_j).
  ✅ inj_y_vers_jv            : { injective_dans(c,S) [τ_y] } ⊢ _inj_hyp(c,S) [τ_j]
     — PONT b=y ↔ b=j sur l'injectivité gardée.
  ✅ strict_croissante_depuis_iso : { iso(c,S,S,R,R) } ⊢ est_strictement_croissante(R,R,c,S,S)
     — la STRICTE CROISSANCE τ_j est DÉRIVÉE d'UN SEUL iso d'ordre (gain « modulo isos »).
  ✅ coincidence_depuis_isos_compat : coincidence avec c_scr,k_scr REMPLACÉS par iso(c),iso(k)
     ⊢ (∀u)(u∈S ⇒ φ(u)=φ'(u))  — le résidu stricte croissance est DÉCHARGÉ.

Aucune conclusion n'est tautologie / postulée ; theorie=22 ; aucun fichier modifié.
"""
from bourbaki.logique.i_1_termes_relations.formule import var, egal, appartient, libres_f
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.ordre.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_vocab import (
    compatible_ordre, est_isomorphisme_ordre,
)
from bourbaki.ordre.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_monotone import est_strictement_croissante
from bourbaki.cardinaux.ensembles_iso_unicite_finale import _compat_yv, _inj_hyp
from bourbaki.cardinaux.ensembles_lemme4_croissante import _R_de
from bourbaki.cardinaux import ensembles_coincidence_pont as P
from bourbaki.cardinaux.ensembles_coincidence_decharge import (
    coincidence_depuis_isos, coincidence_depuis_isos_cible,
)


def _R(nom):
    return lambda a, b: appartient(E.couple(a, b), var(nom))


# ════════════════════════════════════════════════════════════════════════════
#  PONT (1) — compatible_ordre [τ_y] ⊢ _compat_yv [τ_j]
# ════════════════════════════════════════════════════════════════════════════
def test_compat_y_vers_jv_conclusion():
    """⊢ _compat_yv(c,S,R)  (conclusion == cible, τ_j)."""
    t = P.compat_y_vers_jv()
    assert not t.est_clos
    assert t.conclusion == P.compat_y_vers_jv_cible()
    assert t.conclusion == _compat_yv(var("c"), var("S"), _R_de("R"))
    assert t.conclusion not in t.hypotheses           # non tautologique


def test_compat_y_vers_jv_une_seule_hyp_compat_y():
    """L'UNIQUE hypothèse est la compatibilité d'ordre τ_y (liants frais a,b)."""
    t = P.compat_y_vers_jv()
    Rf = _R_de("R")
    src = compatible_ordre(var("c"), var("S"), Rf, Rf, x="a", y="b")
    assert list(t.hypotheses) == [src]
    # le pont est RÉEL : conclusion τ_j ≠ hypothèse τ_y
    assert t.conclusion != src


def test_compat_y_vers_jv_parametrable():
    t = P.compat_y_vers_jv("g", "A", "Q")
    assert t.conclusion == P.compat_y_vers_jv_cible("g", "A", "Q")
    assert sorted(libres_f(t.conclusion)) == ["A", "Q", "g"]


# ════════════════════════════════════════════════════════════════════════════
#  PONT (2) — injective_dans [τ_y] ⊢ _inj_hyp [τ_j]
# ════════════════════════════════════════════════════════════════════════════
def test_inj_y_vers_jv_conclusion():
    """⊢ _inj_hyp(c,S)  (conclusion == cible, τ_j)."""
    t = P.inj_y_vers_jv()
    assert not t.est_clos
    assert t.conclusion == P.inj_y_vers_jv_cible()
    assert t.conclusion == _inj_hyp(var("c"), var("S"))
    assert t.conclusion not in t.hypotheses


def test_inj_y_vers_jv_une_seule_hyp_inj_y():
    """L'UNIQUE hypothèse est l'injectivité gardée τ_y (injective_dans)."""
    t = P.inj_y_vers_jv()
    src = E.injective_dans(var("c"), var("S"))
    assert list(t.hypotheses) == [src]
    assert t.conclusion != src                        # pont réel


# ════════════════════════════════════════════════════════════════════════════
#  CHAÎNAGE — stricte croissance τ_j DÉRIVÉE d'UN SEUL iso d'ordre
# ════════════════════════════════════════════════════════════════════════════
def test_strict_croissante_depuis_iso_conclusion():
    """⊢ est_strictement_croissante(R,R,c,S,S)  (τ_j) depuis UN iso d'ordre."""
    t = P.strict_croissante_depuis_iso()
    assert not t.est_clos
    assert t.conclusion == P.strict_croissante_depuis_iso_cible()
    assert t.conclusion == est_strictement_croissante(
        var("R"), var("R"), var("c"), var("S"), var("S"))
    assert t.conclusion not in t.hypotheses           # non tautologique


def test_strict_croissante_depuis_iso_une_seule_hyp_iso():
    """L'UNIQUE hypothèse est « c est un iso d'ordre de (S,R) » (clean, liants a,b)."""
    t = P.strict_croissante_depuis_iso()
    Rf = _R_de("R")
    iso = est_isomorphisme_ordre(var("c"), var("S"), var("S"), Rf, Rf, x="a", y="b")
    assert list(t.hypotheses) == [iso]
    # l'iso est RÉELLEMENT consommé (sa stricte croissance n'était PAS une hyp)
    assert t.conclusion != iso


def test_strict_croissante_depuis_iso_parametrable():
    t = P.strict_croissante_depuis_iso("k", "S", "R")
    assert t.conclusion == est_strictement_croissante(
        var("R"), var("R"), var("k"), var("S"), var("S"))
    assert len(t.hypotheses) == 1


# ════════════════════════════════════════════════════════════════════════════
#  RÉ-ASSEMBLAGE — coïncidence depuis isos, résidu STRICTE CROISSANCE DÉCHARGÉ
# ════════════════════════════════════════════════════════════════════════════
def test_coincidence_depuis_isos_compat_conclusion():
    """⊢ (∀u)(u∈S ⇒ φ(u)=φ'(u))  (même conclusion que coincidence_depuis_isos)."""
    t = P.coincidence_depuis_isos_compat()
    assert not t.est_clos
    assert t.conclusion == P.coincidence_depuis_isos_compat_cible()
    assert t.conclusion == coincidence_depuis_isos_cible()
    assert t.conclusion not in t.hypotheses           # non tautologique


def test_coincidence_depuis_isos_compat_decharge_stricte_croissance():
    """Les 2 hyps de STRICTE CROISSANCE τ_j (c_scr,k_scr) ne sont PLUS dans le séquent,
    et sont REMPLACÉES par 2 hyps d'ISO d'ordre (langage uniforme des isos)."""
    base = coincidence_depuis_isos()
    t = P.coincidence_depuis_isos_compat()
    H = set(t.hypotheses)
    Hbase = set(base.hypotheses)

    c_scr = est_strictement_croissante(var("R"), var("R"), var("c"), var("S"), var("S"))
    k_scr = est_strictement_croissante(var("R"), var("R"), var("k"), var("S"), var("S"))
    # présentes dans la base, ABSENTES après décharge
    assert c_scr in Hbase and k_scr in Hbase
    assert c_scr not in H and k_scr not in H

    Rf = _R_de("R")
    iso_c = est_isomorphisme_ordre(var("c"), var("S"), var("S"), Rf, Rf, x="a", y="b")
    iso_k = est_isomorphisme_ordre(var("k"), var("S"), var("S"), Rf, Rf, x="a", y="b")
    # les ISOS d'ordre de c,k ATTESTENT désormais la stricte croissance
    assert iso_c in H and iso_k in H


def test_coincidence_depuis_isos_compat_garde_le_reste():
    """Toutes les AUTRES hypothèses de coincidence_depuis_isos sont CONSERVÉES
    (on n'a touché QUE les deux conjoints de stricte croissance)."""
    base = coincidence_depuis_isos()
    t = P.coincidence_depuis_isos_compat()
    Hbase = set(base.hypotheses)
    H = set(t.hypotheses)
    c_scr = est_strictement_croissante(var("R"), var("R"), var("c"), var("S"), var("S"))
    k_scr = est_strictement_croissante(var("R"), var("R"), var("k"), var("S"), var("S"))
    reste = Hbase - {c_scr, k_scr}
    assert reste.issubset(H)                          # rien d'autre n'a disparu


def test_coincidence_depuis_isos_compat_parametrable():
    t = P.coincidence_depuis_isos_compat(
        "f", "fp", "g", "h", "A", "B", "cc", "kk", "v", "Ga", "Gb")
    assert t.conclusion == P.coincidence_depuis_isos_compat_cible(
        "f", "fp", "g", "h", "A", "B", "cc", "kk", "v", "Ga", "Gb")
    assert t.conclusion not in t.hypotheses


# ════════════════════════════════════════════════════════════════════════════
#  INVARIANT — theorie_ensembles() reste = 22
# ════════════════════════════════════════════════════════════════════════════
def test_theorie_inchangee_22():
    """theorie_ensembles reste à 22 axiomes (alpha_tau = primitive, pas un axiome)."""
    P.compat_y_vers_jv()
    P.inj_y_vers_jv()
    P.strict_croissante_depuis_iso()
    P.coincidence_depuis_isos_compat()
    assert len(E.theorie_ensembles().axiomes) == 22
