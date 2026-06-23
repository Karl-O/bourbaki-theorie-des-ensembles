"""Tests §IV.3.1 — Applications universelles (fragment objet, propriété universelle).

Chaque test vérifie que la CONCLUSION du théorème renvoyé par le noyau est
EXACTEMENT la cible visée (et qu'il est clos pour les théorèmes inconditionnels,
ou que ses hypothèses sont les conditions attendues pour les conditionnels).

Les prédicats `morph` / `fact` sont des prédicats CONCRETS de test (callables
Terme→Formule) : f morphisme := f∈M  (M graphe générique) ;  φ=f∘φ_E := égalité
fixe.  Les théorèmes prouvés valent quel que soit le contenu de ces prédicats.
"""
from bourbaki.logique.i_1_termes_relations.formule import var, egal, et, impl, existe, pourtout, appartient
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.ensembles.fonctions.hors_ii_3.iv_structures import ensembles_applications_universelles as U


# ── prédicats de test ─────────────────────────────────────────────────────────
_M = var("M")          # « graphe des morphismes » générique
_PHI = var("phi")      # φ (l'α-application donnée)
_PHIE = var("phiE")    # φ_E
_F = var("Fc")         # F_E


def _morph(f):
    """f morphisme de F_E dans F := f ∈ M  (clause σ-morphisme concrète de test)."""
    return appartient(f, _M)


def _fact(f):
    """φ = f∘φ_E  (clause de factorisation concrète de test)."""
    return egal(_PHI, E.composee(f, _PHIE))


def _corps(f):
    return et(_morph(var(f)), _fact(var(f)))


# ── (AU) ⟹ (AU_I′) ─────────────────────────────────────────────────────────────
def test_au_implique_au_i_prime():
    t = U.au_implique_au_i_prime(_morph, _fact)
    assert t.est_clos
    cible = impl(U.est_universel(_morph, _fact),
                 U.au_i_prime(_morph, _fact))
    assert t.conclusion == cible


# ── (AU) ⟹ (AU_II′) ─────────────────────────────────────────────────────────────
def test_au_implique_au_ii_prime():
    t = U.au_implique_au_ii_prime(_morph, _fact)
    assert t.est_clos
    cible = impl(U.est_universel(_morph, _fact),
                 U.au_ii_prime(_morph, _fact))
    assert t.conclusion == cible


# ── ((AU_I′) et (AU_II′)) ⟹ (AU) ────────────────────────────────────────────────
def test_au_i_et_ii_implique_au():
    t = U.au_i_et_ii_implique_au(_morph, _fact)
    assert t.est_clos
    cible = impl(et(U.au_i_prime(_morph, _fact), U.au_ii_prime(_morph, _fact)),
                 U.est_universel(_morph, _fact))
    assert t.conclusion == cible


# ── (AU) ⟹ ((AU_I′) et (AU_II′))  (l'autre sens du critère équivalent) ──────────
def test_au_implique_au_i_et_ii():
    t = U.au_implique_au_i_et_ii(_morph, _fact)
    assert t.est_clos
    cible = impl(U.est_universel(_morph, _fact),
                 et(U.au_i_prime(_morph, _fact), U.au_ii_prime(_morph, _fact)))
    assert t.conclusion == cible


# ── (AU) ⟹ existence d'une factorisation ───────────────────────────────────────
def test_factorisation_existe():
    t = U.factorisation_existe(_morph, _fact)
    assert t.est_clos
    # = au_implique_au_i_prime
    cible = impl(U.est_universel(_morph, _fact), U.au_i_prime(_morph, _fact))
    assert t.conclusion == cible


# ── {(AU)} ⊢ (corps{S} et corps{T}) ⇒ S=T  (unicité appliquée à deux témoins) ──
def test_factorisation_unique():
    S, T = var("S"), var("T")
    t = U.factorisation_unique(_morph, _fact, S, T)
    # hypothèse : (AU)
    assert U.est_universel(_morph, _fact) in t.hypotheses
    # conclusion : (corps{S} et corps{T}) ⇒ S=T
    cible = impl(et(et(_morph(S), egal(_PHI, E.composee(S, _PHIE))),
                    et(_morph(T), egal(_PHI, E.composee(T, _PHIE)))),
                 egal(S, T))
    assert t.conclusion == cible


# ── cohérence structurelle : (AU) EST (AU_I′) et (AU_II′) ───────────────────────
def test_est_universel_est_conjonction_des_criteres():
    """(AU) = (AU_I′) et (AU_II′) par définition (critère équivalent du Texte.tex)."""
    au = U.est_universel(_morph, _fact)
    assert au == et(U.au_i_prime(_morph, _fact), U.au_ii_prime(_morph, _fact))
