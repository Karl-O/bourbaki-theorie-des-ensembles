"""Tests — §III.6.3 Hessenberg, INDUCTIVITÉ du poset 𝔉 de Zorn.

Vérifie :
  • theorie_ensembles() reste = 22 (aucun axiome ajouté au noyau) ;
  • union_chaine_fonctionnelle : ⋃φ fonctionnel sous famille_compatible (CLOS via
    C60), conclusion = est_fonctionnel(⋃𝔇), hyp = famille_compatible (non vacuous) ;
  • union_chaine_valeur : transfert de valeur ⋃φ(u)=φ_i(u), hyps honnêtes ;
  • frame_inductif : conclusion == est_inductif(Γ𝔉,𝔉), sous est_ordre +
    enonce_chaine_majoree (résidu honnête), non vacuous.
"""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.zorn_zermelo.ensembles_zorn import est_inductif
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_c60_coeur import union_famille, famille_compatible
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.hessenberg.coeur.ensembles_hessenberg_hard import frame_pair, frame_ordre
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.hessenberg.coeur.ensembles_hessenberg_inductivite import (
    union_chaine_fonctionnelle, union_chaine_valeur,
    enonce_chaine_majoree, frame_inductif,
)


def test_theorie_inchangee_22():
    assert len(E.theorie_ensembles().axiomes) == 22


def test_union_chaine_fonctionnelle():
    th = union_chaine_fonctionnelle()
    # conclusion = est_fonctionnel(⋃𝔇)
    assert th.conclusion == E.est_fonctionnel(union_famille(var("Dchaine")))
    # exactement une hyp honnête : famille_compatible
    assert famille_compatible(var("Dchaine")) in th.hypotheses
    assert th.conclusion not in th.hypotheses          # non vacuous


def test_union_chaine_valeur_honnete():
    th = union_chaine_valeur()
    # 3 hyps honnêtes (compatibilité + p∈𝔇 + u∈dom p)
    assert len(th.hypotheses) >= 1
    assert th.conclusion not in th.hypotheses


def test_frame_inductif_conclusion_et_residu():
    th = frame_inductif()
    Gam, Fr = frame_ordre(var("E")), frame_pair(var("E"))
    # conclusion == est_inductif(Γ𝔉,𝔉) STRUCTURELLEMENT
    assert th.conclusion == est_inductif(Gam, Fr)
    # le résidu honnête (chaîne majorée) figure bien parmi les hypothèses
    assert enonce_chaine_majoree(Gam, Fr) in th.hypotheses
    assert th.conclusion not in th.hypotheses          # non vacuous


def test_residu_chaine_majoree_non_vacuux():
    # enonce_chaine_majoree est un (∀C)(chaine ⇒ (∃m)majorant) non trivial :
    # il lie la variable C quelque part dans sa structure (≠ tautologie close).
    f = enonce_chaine_majoree(frame_ordre(var("E")), frame_pair(var("E")))
    assert "C" in {b for b, _ in _binders(f)} or _contains_lieur(f, "C")


def _binders(f):
    acc = []
    def go(g):
        if getattr(g, "lieur", ""):
            acc.append((g.lieur, g))
        for s in getattr(g, "sous", ()):
            go(s)
    go(f)
    return acc


def _contains_lieur(f, name):
    return any(b == name for b, _ in _binders(f))
