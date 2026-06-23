"""Tests — §III.2 C60 EXISTENCE, LE CŒUR (recollement d'une famille d'essais).

Vérifie le module `bourbaki.ordre.iii_2_bon_ordre.recurrence_transfinie.ensembles_c60_coeur` :
  • (ii)  collectivisation ⋃𝔇 en THÉORIE DÉDIÉE (theorie_ensembles reste 22) ;
  • (i)   🎯 family-union-functional : famille compatible ⇒ ⋃𝔇 fonctionnel
          (1 hyp honnête, conclusion exacte, non vacuous) ;
  • (iii) 🎯 recollement-famille + extension d'un pas (2 hyps honnêtes).

INVARIANT vérifié partout : theorie_ensembles() = 22.
"""
from bourbaki.logique.formule import var, egal
from bourbaki.ensembles import ensembles_abrege as E
import bourbaki.ordre.iii_2_bon_ordre.recurrence_transfinie.ensembles_c60_coeur as C
from bourbaki.ordre.iii_2_bon_ordre.recurrence_transfinie.ensembles_recurrence_transfinie import _graphe_R


def test_theorie_reste_22():
    """L'import et l'usage du module n'altèrent PAS theorie_ensembles() (=22)."""
    assert len(E.theorie_ensembles().axiomes) == 22
    # appel des constructions principales
    C.union_famille_fonctionnelle()
    C.valeur_union_famille()
    C.extension_un_pas_union_fonctionnelle()
    assert len(E.theorie_ensembles().axiomes) == 22


def test_union_famille_theorie_dediee():
    """(ii) La collectivisation ⋃𝔇 vit dans une THÉORIE DÉDIÉE (1 axiome isolé)."""
    th = C.theorie_union_famille()
    assert len(th.axiomes) == 1
    # membership : w∈⋃𝔇 ⇔ (∃p)(p∈𝔇 et w∈p)  — l'équivalence est CLOSE (axiome instancié)
    mem = C.membre_union_famille()
    assert mem.est_clos
    assert len(E.theorie_ensembles().axiomes) == 22


def test_union_famille_fonctionnelle():
    """(i) 🎯 famille_compatible(𝔇) ⊢ est_fonctionnel(⋃𝔇)  [1 hyp honnête]."""
    r = C.union_famille_fonctionnelle()
    vD = var("Df")
    U = C.union_famille(vD)
    # conclusion EXACTE
    assert r.conclusion == E.est_fonctionnel(U)
    # UNE hypothèse honnête, EXACTEMENT famille_compatible(𝔇)
    assert len(r.hypotheses) == 1
    assert C.famille_compatible(vD) in r.hypotheses
    # non vacuous
    assert r.conclusion not in r.hypotheses
    assert len(E.theorie_ensembles().axiomes) == 22


def test_valeur_union_famille():
    """Transfert de valeur : { compat, p∈𝔇, u∈dom p } ⊢ valeur(⋃𝔇,u)=valeur(p,u)  [3 hyps]."""
    r = C.valeur_union_famille()
    vD, vp, vu = var("Df"), var("pcf"), var("u")
    U = C.union_famille(vD)
    # conclusion EXACTE
    assert r.conclusion == egal(E.valeur(U, vu), E.valeur(vp, vu))
    # TROIS hypothèses honnêtes
    assert len(r.hypotheses) == 3
    from bourbaki.logique.formule import appartient
    assert C.famille_compatible(vD) in r.hypotheses
    assert appartient(vp, vD) in r.hypotheses
    assert appartient(vu, E.dom(vp)) in r.hypotheses
    # non vacuous
    assert r.conclusion not in r.hypotheses
    assert len(E.theorie_ensembles().axiomes) == 22


def test_extension_un_pas_union_fonctionnelle():
    """(iii) 🎯 { famille_compatible(𝔇), dom(⋃𝔇)=seg } ⊢ func(⋃𝔇 ∪ {(x,v)})  [2 hyps]."""
    r = C.extension_un_pas_union_fonctionnelle()
    vD = var("Df")
    U = C.union_famille(vD)
    seg = E.segment_extremite(_graphe_R("G"), var("E"), var("x0"))
    cible = E.est_fonctionnel(E.reunion(U, E.singleton(E.couple(var("x0"), var("v0")))))
    # conclusion EXACTE
    assert r.conclusion == cible
    # DEUX hypothèses honnêtes : compatibilité + dom(⋃𝔇)=seg
    assert len(r.hypotheses) == 2
    assert C.famille_compatible(vD) in r.hypotheses
    assert egal(E.dom(U), seg) in r.hypotheses
    # non vacuous
    assert r.conclusion not in r.hypotheses
    assert len(E.theorie_ensembles().axiomes) == 22
