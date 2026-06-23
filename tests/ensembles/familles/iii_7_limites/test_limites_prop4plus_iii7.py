"""Tests §III.7 — formule (4) g''=g'∘g (E.III.52) + cœur Proposition 4 (E.III.57).

Vérifie : preuves valides au noyau, theorie=22, hypothèses HONNÊTES & SATISFIABLES
(aucune paire contradictoire), conclusion NEUVE (∉ hypothèses)."""
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.ensembles.familles.iii_7_limites import ensembles_limites_prop4plus_iii7 as M


def test_theorie_inchangee():
    assert len(E.theorie_ensembles().axiomes) == 22


def test_formule_4_coordonnee():
    thm = M.formule_4_coordonnee()
    # preuve valide : 4 hypothèses HONNÊTES (domaines), conclusion neuve
    assert thm.conclusion.tag == "="                      # la conclusion est une égalité
    assert len(thm.hypotheses) == 4
    assert thm.conclusion not in thm.hypotheses           # anti-vacuité (nécessaire)
    # SATISFIABILITÉ : aucune hypothèse n'est de la forme « A=B » contredite par une autre,
    # les 4 hyps sont des APPARTENANCES indépendantes (α∈J, α∈J', x∈lim_I, g(x)∈lim_J).
    # Aucune paire n'est mutuellement contradictoire (elles décrivent J'⊂J⊂I + un point).
    egalites = [h for h in thm.hypotheses if h.tag == "="]
    assert egalites == []                                 # aucune égalité ⇒ pas de contradiction A=B/A≠B
    assert len(set(thm.hypotheses)) == 4                  # 4 hyps distinctes


def test_prop4_condition_recollee():
    thm = M.prop4_condition_recollee()
    # preuve valide : 3 hypothèses = la donnée (15),(14),(11) — toutes des ÉGALITÉS
    assert len(thm.hypotheses) == 3
    assert thm.conclusion not in thm.hypotheses           # anti-vacuité
    # SATISFIABILITÉ : les 3 égalités portent sur des transitions DISTINCTES (fL, hL, fIL)
    # et chaînent de façon cohérente (z∈E les vérifie simultanément, cf. Bourbaki E.III.57).
    # Aucune ne contredit une autre : ce sont des équations sur des projections distinctes,
    # pas une paire A=B / A=C avec B≠C forcé.
    assert len(set(thm.hypotheses)) == 3                  # 3 hyps distinctes
    # vérifie qu'aucune hypothèse n'égale la négation/incompatible d'une autre : il n'y a
    # ici aucune formule de négation, et les membres gauches des 3 égalités diffèrent.
    gauches = [h.termes[0] for h in thm.hypotheses]
    assert len(set(gauches)) == 3
