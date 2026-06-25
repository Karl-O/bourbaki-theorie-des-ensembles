"""Tests de ensembles_prop2_galois_dual.py — PROPOSITION 2 (E.III.7-8), v∘u∘v = v.

DUALE EXACTE (miroir) de test_prop2_galois.py par échange u↔v, E↔E', G↔G'.
Vérifie, en APPELANT réellement le théorème (leçon prop10 : un import ne prouve
rien) :
  • la conclusion EXACTE (∀x')(x'∈E' ⇒ w(x')=v(x')), construite indépendamment
    avec les constructeurs formule (et confrontée à cible_galois_vuv_egale_v) ;
  • le jeu d'hypothèses EXACT (les 7 antécédents honnêtes load-bearing), via une
    comparaison ENSEMBLISTE thm.hypotheses == {…} : aucune hypothèse parasite, et la
    conclusion w(x')=v(x') n'y figure PAS ;
  • le théorème est certifié par le noyau (justification = généralisation C27) ;
  • l'invariant theorie_ensembles == 22 (aucun axiome ajouté).
"""
from bourbaki.logique.i_1_termes_relations.formule import (
    var, egal, impl, appartient, pourtout,
)
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.ordre.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_relation import (
    antisymetrie,
)
from bourbaki.ordre.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_monotone import (
    est_decroissante,
)
from bourbaki.ordre.iii_1_relations_ordre.iii_1_5_applications_croissantes import (
    ensembles_prop2_galois_dual as P,
)


G, Gp = var("G"), var("Gp")
Es, Ep = var("E"), var("Ep")
# w := composite v∘u∘v ; nom par défaut "wc" (évite la collision avec le trou "w"
# des tactiques égalitaires symetrie/composer_egalites).
u, v, w = var("u"), var("v"), var("wc")


def _couple_dans(t, s, Gr):
    return appartient(E.couple(t, s), Gr)


def _val(fn, x):
    return E.valeur(fn, x, b="j")


def _conclusion_cible():
    """(∀x')(x'∈E' ⇒ w(x')=v(x')), construite indépendamment de l'implémentation."""
    vx = var("x")
    return pourtout("x", impl(appartient(vx, Ep),
                              egal(_val(w, vx), _val(v, vx))))


def _hyps_cibles():
    """Les 7 hypothèses honnêtes attendues, construites indépendamment (duales)."""
    vt, vx = var("t"), var("x")
    return {
        # 1. v décroissante E'→E
        est_decroissante(Gp, G, v, "Ep", "E", "x", "y"),
        # 2. u envoie E dans E'
        pourtout("t", impl(appartient(vt, Es), appartient(_val(u, vt), Ep))),
        # 3. v envoie E' dans E
        pourtout("t", impl(appartient(vt, Ep), appartient(_val(v, vt), Es))),
        # 4. u(v(x')) ≥ x'
        pourtout("x", impl(appartient(vx, Ep),
                           _couple_dans(vx, _val(u, _val(v, vx)), Gp))),
        # 5. v(u(x)) ≥ x
        pourtout("x", impl(appartient(vx, Es),
                           _couple_dans(vx, _val(v, _val(u, vx)), G))),
        # 6. w = v∘u∘v sur E'
        pourtout("x", impl(appartient(vx, Ep),
                           egal(_val(w, vx), _val(v, _val(u, _val(v, vx)))))),
        # 7. antisymétrie de l'ordre de E
        antisymetrie(G, "x", "y"),
    }


def test_conclusion_exacte():
    t = P.galois_vuv_egale_v()
    assert t.conclusion == _conclusion_cible()


def test_conclusion_cible_helper_coherente():
    # la fonction cible_* exposée par le module reconstruit la même conclusion.
    assert P.cible_galois_vuv_egale_v() == _conclusion_cible()


def test_hypotheses_exactes_7_honnetes():
    t = P.galois_vuv_egale_v()
    cibles = _hyps_cibles()
    assert t.hypotheses == cibles, (
        f"hyps inattendues : en trop {t.hypotheses - cibles} ; manquantes {cibles - t.hypotheses}"
    )
    assert len(t.hypotheses) == 7


def test_hypotheses_helper_coherent():
    # le frozenset exposé par le module == jeu d'hypothèses attendu.
    assert set(P.hypotheses_galois_vuv()) == _hyps_cibles()


def test_conclusion_pas_dans_hypotheses():
    # anti-triche : la conclusion w(x')=v(x') ne doit PAS être une hypothèse.
    t = P.galois_vuv_egale_v()
    assert _conclusion_cible() not in t.hypotheses


def test_theoreme_certifie_par_noyau():
    # justification issue d'une règle du noyau (généralisation C27), pas fabriquée.
    t = P.galois_vuv_egale_v()
    assert "généralisation" in t.justification


def test_theorie_ensembles_intacte_22():
    assert len(E.theorie_ensembles().axiomes) == 22
