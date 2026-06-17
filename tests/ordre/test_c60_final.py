"""Tests — §III.2 C60 EXISTENCE, ASSEMBLAGE FINAL (`bourbaki.ordre.ensembles_c60_final`).

Vérifie :
  • la brique graphe→valeur `couple_donne_valeur` (le chunk reporté de c60_coeur) ;
  • 🎯 LE PONT `famille_compatible_depuis_coincidence`
        { membres_fonctionnels(𝔇), coincidence_membres(𝔇) } ⊢ famille_compatible(𝔇) ;
  • le corollaire ⋃𝔇 fonctionnel sous la cohésion-valeur ;
  • 🎯 l'extension d'un pas sous la cohésion-valeur (recollement complet, fonctionnalité).

INVARIANT vérifié partout : theorie_ensembles() = 22 ; conclusions non vacuous.
"""
from bourbaki.logique.formule import var, egal, appartient
from bourbaki.ensembles import ensembles_abrege as E
import bourbaki.ordre.ensembles_c60_final as F
from bourbaki.ordre.ensembles_c60_coeur import famille_compatible, union_famille
from bourbaki.ordre.ensembles_recurrence_transfinie import _graphe_R


def test_theorie_reste_22():
    """L'import et l'usage du module n'altèrent PAS theorie_ensembles() (=22)."""
    assert len(E.theorie_ensembles().axiomes) == 22
    F.couple_donne_valeur()
    F.famille_compatible_depuis_coincidence()
    F.union_fonctionnelle_depuis_coincidence()
    F.extension_un_pas_depuis_coincidence()
    assert len(E.theorie_ensembles().axiomes) == 22


def test_couple_donne_valeur():
    """{ func p, (a,b)∈p } ⊢ b = valeur(p,a)  [2 hyps honnêtes]."""
    r = F.couple_donne_valeur()
    vp, va, vb = var("p"), var("a"), var("b")
    assert r.conclusion == egal(vb, E.valeur(vp, va))
    assert len(r.hypotheses) == 2
    assert appartient(E.couple(va, vb), vp) in r.hypotheses
    assert E.est_fonctionnel(vp) in r.hypotheses
    assert r.conclusion not in r.hypotheses


def test_pont_famille_compatible_depuis_coincidence():
    """🎯 LE PONT : { membres_fonctionnels(𝔇), coincidence_membres(𝔇) } ⊢ famille_compatible(𝔇)."""
    r = F.famille_compatible_depuis_coincidence()
    vD = var("Df")
    # conclusion EXACTE = famille_compatible(𝔇)
    assert r.conclusion == famille_compatible(vD)
    # DEUX hypothèses honnêtes EXACTES
    assert len(r.hypotheses) == 2
    assert F.membres_fonctionnels(vD) in r.hypotheses
    assert F.coincidence_membres(vD) in r.hypotheses
    # non vacuous
    assert r.conclusion not in r.hypotheses
    assert len(E.theorie_ensembles().axiomes) == 22


def test_union_fonctionnelle_depuis_coincidence():
    """⋃𝔇 fonctionnel sous { membres_fonctionnels, coincidence_membres } (PONT + (i))."""
    r = F.union_fonctionnelle_depuis_coincidence()
    vD = var("Df")
    assert r.conclusion == E.est_fonctionnel(union_famille(vD))
    assert len(r.hypotheses) == 2
    assert F.membres_fonctionnels(vD) in r.hypotheses
    assert F.coincidence_membres(vD) in r.hypotheses
    assert r.conclusion not in r.hypotheses


def test_extension_un_pas_depuis_coincidence():
    """🎯 Recollement complet + extension d'un pas sous cohésion-valeur (fonctionnalité)."""
    r = F.extension_un_pas_depuis_coincidence()
    vD = var("Df")
    U = union_famille(vD)
    seg = E.segment_extremite(_graphe_R("G"), var("E"), var("x0"))
    cible = E.est_fonctionnel(E.reunion(U, E.singleton(E.couple(var("x0"), var("v0")))))
    assert r.conclusion == cible
    # TROIS hypothèses honnêtes : essais fonctionnels, cohésion-valeur, dom(⋃𝔇)=seg
    assert len(r.hypotheses) == 3
    assert F.membres_fonctionnels(vD) in r.hypotheses
    assert F.coincidence_membres(vD) in r.hypotheses
    assert egal(E.dom(U), seg) in r.hypotheses
    assert r.conclusion not in r.hypotheses
    assert len(E.theorie_ensembles().axiomes) == 22
