"""Tests de ensembles_prop2_galois.py — PROPOSITION 2 (E.III.7-8), u∘v∘u = u.

Vérifie, en APPELANT réellement le théorème (leçon prop10 : un import ne prouve
rien) :
  • la conclusion EXACTE (∀x)(x∈E ⇒ w(x)=u(x)), construite indépendamment avec les
    constructeurs formule ;
  • le jeu d'hypothèses EXACT (les 7 antécédents honnêtes load-bearing), via une
    comparaison ENSEMBLISTE thm.hypotheses == {…} : aucune hypothèse parasite, et la
    conclusion w(x)=u(x) n'y figure PAS ;
  • l'invariant theorie_ensembles == 22 (aucun axiome ajouté).
"""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, egal, impl, appartient, pourtout,
)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_relation import (
    antisymetrie,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_monotone import (
    est_decroissante,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_1_relations_ordre.iii_1_5_applications_croissantes import (
    ensembles_prop2_galois as P,
)


G, Gp = var("G"), var("Gp")
Es, Ep = var("E"), var("Ep")
# w := composite u∘v∘u ; nom par défaut "wc" (évite la collision avec le trou "w"
# des tactiques égalitaires symetrie/composer_egalites).
u, v, w = var("u"), var("v"), var("wc")


def _couple_dans(t, s, Gr):
    return appartient(E.couple(t, s), Gr)


def _val(fn, x):
    return E.valeur(fn, x, b="j")


def _conclusion_cible():
    """(∀x)(x∈E ⇒ w(x)=u(x)), construite indépendamment de l'implémentation."""
    vx = var("x")
    return pourtout("x", impl(appartient(vx, Es),
                              egal(_val(w, vx), _val(u, vx))))


def _hyps_cibles():
    """Les 7 hypothèses honnêtes attendues, construites indépendamment."""
    vt, vx = var("t"), var("x")
    return {
        # 1. u décroissante E→E'
        est_decroissante(G, Gp, u, "E", "Ep", "x", "y"),
        # 2. u envoie E dans E'
        pourtout("t", impl(appartient(vt, Es), appartient(_val(u, vt), Ep))),
        # 3. v envoie E' dans E
        pourtout("t", impl(appartient(vt, Ep), appartient(_val(v, vt), Es))),
        # 4. v(u(x)) ≥ x
        pourtout("x", impl(appartient(vx, Es),
                           _couple_dans(vx, _val(v, _val(u, vx)), G))),
        # 5. u(v(x')) ≥ x'
        pourtout("x", impl(appartient(vx, Ep),
                           _couple_dans(vx, _val(u, _val(v, vx)), Gp))),
        # 6. w = u∘v∘u sur E
        pourtout("x", impl(appartient(vx, Es),
                           egal(_val(w, vx), _val(u, _val(v, _val(u, vx)))))),
        # 7. antisymétrie de l'ordre de E'
        antisymetrie(Gp, "x", "y"),
    }


def test_conclusion_exacte():
    t = P.galois_uvu_egale_u()
    assert t.conclusion == _conclusion_cible()


def test_hypotheses_exactes_7_honnetes():
    t = P.galois_uvu_egale_u()
    cibles = _hyps_cibles()
    assert t.hypotheses == cibles, (
        f"hyps inattendues : en trop {t.hypotheses - cibles} ; manquantes {cibles - t.hypotheses}"
    )
    assert len(t.hypotheses) == 7


def test_conclusion_pas_dans_hypotheses():
    # anti-triche : la conclusion w(x)=u(x) ne doit PAS être une hypothèse.
    t = P.galois_uvu_egale_u()
    assert _conclusion_cible() not in t.hypotheses


def test_theoreme_certifie_par_noyau():
    # justification issue d'une règle du noyau (généralisation C27), pas fabriquée.
    t = P.galois_uvu_egale_u()
    assert "généralisation" in t.justification


def test_theorie_ensembles_intacte_22():
    assert len(E.theorie_ensembles().axiomes) == 22
