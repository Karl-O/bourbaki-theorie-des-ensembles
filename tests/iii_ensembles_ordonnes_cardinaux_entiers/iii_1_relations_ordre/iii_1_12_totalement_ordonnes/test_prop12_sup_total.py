"""Tests — §III.1 n°12 Proposition 12 (E.III.1.14) : critère de borne supérieure
dans un ensemble TOTALEMENT ordonné.

Vérifie que le théorème `borne_sup_critere_total` est CERTIFIÉ par le noyau
(construction sans erreur), que sa conclusion est EXACTEMENT l'ÉQUIVALENCE visée
(reconstruite avec les mêmes constructeurs : borne_superieure, majorant, pourtout,
impl, et, appartient, egal, non, existe, _couple_dans), qu'il porte EXACTEMENT ses
TROIS hypothèses HONNÊTES (totalement_ordonne, X⊂E, b∈E ; jamais la conclusion-
équivalence parmi les hypothèses → jamais vacuité), et que theorie_ensembles reste
= 22 axiomes."""
from __future__ import annotations

import bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_1_relations_ordre.iii_1_12_totalement_ordonnes.ensembles_prop12_sup_total as M
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, egal, et, non, impl, appartient, existe, pourtout,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_relation import (
    totalement_ordonne, majorant, borne_superieure, _couple_dans, inclus,
)


# noms par défaut utilisés par borne_sup_critere_total
_G, _X, _B, _Ed = "Gs12", "Xs12", "bs12", "Es12"
_x, _y, _z = "xs12tot", "ys12tot", "zs12tot"
_XMAJ, _YPP, _CCRIT, _XEX = "xs12", "ys12", "cs12", "xe12"


def _cible_attendue():
    """Reconstruit l'équivalence visée À LA MAIN (mêmes constructeurs que l'énoncé),
    INDÉPENDAMMENT des helpers du module, pour valider la fidélité."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import equiv
    vb, vc, vx = var(_B), var(_CCRIT), var(_XEX)
    vX, vE = var(_X), var(_Ed)
    gauche = borne_superieure(_G, _X, vb, _Ed, _XMAJ, _YPP)
    maj_b = majorant(_G, _X, vb, _Ed, _XMAJ)
    c_lt_b = et(et(appartient(vc, vE), _couple_dans(vc, vb, _G)), non(egal(vc, vb)))
    temoin = et(et(et(appartient(vx, vX), _couple_dans(vc, vx, _G)), non(egal(vc, vx))),
                _couple_dans(vx, vb, _G))
    crit2 = pourtout(_CCRIT, impl(c_lt_b, existe(_XEX, temoin)))
    return equiv(gauche, et(maj_b, crit2))


def test_theorie_inchangee_22():
    assert len(E.theorie_ensembles().axiomes) == 22


def test_prop12_se_construit():
    # le simple fait que la construction aboutisse = certification noyau
    t = M.borne_sup_critere_total()
    assert t is not None


def test_prop12_conclusion_est_equivalence_visee():
    t = M.borne_sup_critere_total()
    assert t.conclusion == M._cible()                # cohérence interne (helper)
    assert t.conclusion == _cible_attendue()         # fidélité (reconstruction à la main)


def test_prop12_trois_hypotheses_honnetes():
    t = M.borne_sup_critere_total()
    # EXACTEMENT trois hypothèses honnêtes
    assert len(t.hypotheses) == 3
    # la conclusion-équivalence n'est JAMAIS une hypothèse (pas de vacuité)
    assert t.conclusion not in t.hypotheses
    honnetes = frozenset({
        totalement_ordonne(_G, _Ed, _x, _y, _z),
        inclus(var(_X), var(_Ed)),
        appartient(var(_B), var(_Ed)),
    })
    assert t.hypotheses == honnetes


def test_prop12_est_clos_sous_les_trois_hyps():
    t = M.borne_sup_critere_total()
    # clos « modulo » les 3 hypothèses honnêtes : aucune hypothèse parasite
    honnetes = frozenset({
        totalement_ordonne(_G, _Ed, _x, _y, _z),
        inclus(var(_X), var(_Ed)),
        appartient(var(_B), var(_Ed)),
    })
    assert t.hypotheses <= honnetes
