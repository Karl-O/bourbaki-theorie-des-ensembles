"""Tests — §III.2 C60 EXISTENCE, ASSEMBLAGE FINAL (`bourbaki.ordre.iii_2_bon_ordre.recurrence_transfinie.ensembles_c60_final`).

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
import bourbaki.ordre.iii_2_bon_ordre.recurrence_transfinie.ensembles_c60_final as F
from bourbaki.ordre.iii_2_bon_ordre.recurrence_transfinie.ensembles_c60_coeur import famille_compatible, union_famille
from bourbaki.ordre.iii_2_bon_ordre.recurrence_transfinie.ensembles_recurrence_transfinie import _graphe_R


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


# ── valeur de l'essai trivial / domaine et valeur de l'essai prolongé ───────────
def _vh(t):
    """Règle-test vh(t) := valeur(Hh, t)  (fonction-valeur de la règle)."""
    return E.valeur(var("Hh"), t)


def test_valeur_singleton_couple_clos():
    """valeur({(x,v)}, x) = v  [CLOS, 0 hyp]."""
    r = F.valeur_singleton_couple()
    vx, vv = var("x0"), var("v0")
    S = E.singleton(E.couple(vx, vv))
    assert r.conclusion == egal(E.valeur(S, vx), vv)
    assert r.est_clos


def test_dom_extension_un_pas():
    """dom(⋃𝔇 ∪ {(x,v)}) = seg∪{x}  [1 hyp honnête dom(⋃𝔇)=seg]."""
    from bourbaki.ordre.iii_2_bon_ordre.recurrence_transfinie.ensembles_c60_existence_close import dom_essai
    r = F.dom_extension_un_pas()
    vD = var("Df")
    U = union_famille(vD)
    seg = E.segment_extremite(_graphe_R("G"), var("E"), var("x0"))
    S = E.singleton(E.couple(var("x0"), var("v0")))
    assert r.conclusion == egal(E.dom(E.reunion(U, S)), dom_essai(_graphe_R("G"), var("E"), var("x0")))
    assert len(r.hypotheses) == 1
    assert egal(E.dom(U), seg) in r.hypotheses
    assert r.conclusion not in r.hypotheses


def test_valeur_nouveau_point():
    """valeur(⋃𝔇 ∪ {(x,v)}, x) = v  [3 hyps honnêtes]."""
    r = F.valeur_nouveau_point()
    vD = var("Df")
    U = union_famille(vD)
    S = E.singleton(E.couple(var("x0"), var("v0")))
    seg = E.segment_extremite(_graphe_R("G"), var("E"), var("x0"))
    assert r.conclusion == egal(E.valeur(E.reunion(U, S), var("x0")), var("v0"))
    assert len(r.hypotheses) == 3
    assert F.membres_fonctionnels(vD) in r.hypotheses
    assert F.coincidence_membres(vD) in r.hypotheses
    assert egal(E.dom(U), seg) in r.hypotheses
    assert r.conclusion not in r.hypotheses


def test_recursion_essai_prolonge():
    """🎯 (∀z∈dom(p_x'))(valeur(p_x',z)=vh(z))  [5 hyps honnêtes]."""
    r = F.recursion_essai_prolonge(_vh)
    vD = var("Df")
    U = union_famille(vD)
    seg = E.segment_extremite(_graphe_R("G"), var("E"), var("x0"))
    assert len(r.hypotheses) == 5
    assert F.membres_fonctionnels(vD) in r.hypotheses
    assert F.coincidence_membres(vD) in r.hypotheses
    assert egal(E.dom(U), seg) in r.hypotheses
    assert F.recursion_sur_segment(vD, _vh, "G", "E", "x0") in r.hypotheses
    assert F.equation_au_point(var("v0"), _vh, var("x0")) in r.hypotheses
    assert r.conclusion not in r.hypotheses
    assert len(E.theorie_ensembles().axiomes) == 22


def test_couvert_essai_depuis_famille():
    """🎯 DÉCHARGE COMPLÈTE en x : construit l'essai p_x' ⇒ couvert_essai(x)  [5 hyps]."""
    from bourbaki.ordre.iii_2_bon_ordre.recurrence_transfinie.ensembles_c60_existence_close import couvert_essai
    r = F.couvert_essai_depuis_famille(_vh)
    vD = var("Df")
    couvert = couvert_essai(_vh, _graphe_R("G"), var("E"), "pess", "zess")(var("x0"))
    assert r.conclusion == couvert
    assert len(r.hypotheses) == 5
    assert F.membres_fonctionnels(vD) in r.hypotheses
    assert F.coincidence_membres(vD) in r.hypotheses
    assert F.recursion_sur_segment(vD, _vh, "G", "E", "x0") in r.hypotheses
    assert F.equation_au_point(var("v0"), _vh, var("x0")) in r.hypotheses
    assert r.conclusion not in r.hypotheses
    assert len(E.theorie_ensembles().axiomes) == 22


# ── 🎯 ÉTAPE 3 — existence C60 via la réalisation de la famille ─────────────────
def _Dfam(x):
    """Famille des essais des y<x au point x (terme paramétré)."""
    return E.app("Dfam_c60", x)


def _vval(x):
    """Valeur posée au nouveau point x (terme paramétré)."""
    return E.app("vval_c60", x)


def test_heredite_couverture_realisee():
    """🎯 { realisation_famille } ⊢ heredite_couverture(couvert_essai)  [1 hyp honnête]."""
    from bourbaki.ordre.iii_2_bon_ordre.recurrence_transfinie.ensembles_recursion_transfinie_existence import heredite_couverture
    from bourbaki.ordre.iii_2_bon_ordre.recurrence_transfinie.ensembles_c60_existence_close import couvert_essai
    r = F.heredite_couverture_realisee(_Dfam, _vval, _vh)
    R = _graphe_R("G")
    couvert = couvert_essai(_vh, R, var("E"))
    assert r.conclusion == heredite_couverture(couvert, R, var("E"), "x0tf", "ytf")
    assert len(r.hypotheses) == 1
    assert F.realisation_famille(_Dfam, _vval, _vh) in r.hypotheses
    assert r.conclusion not in r.hypotheses
    assert len(E.theorie_ensembles().axiomes) == 22


def test_recursion_transfinie_existence():
    """🎯🎯 EXISTENCE C60 : { bon ordre, realisation_famille } ⊢ (∀x∈E)(∃p)(est_essai(p,x))."""
    from bourbaki.ordre.iii_2_bon_ordre.recurrence_transfinie.ensembles_recursion_transfinie_existence import couverture_totale
    from bourbaki.ordre.iii_2_bon_ordre.recurrence_transfinie.ensembles_c60_existence_close import couvert_essai
    r = F.recursion_transfinie_existence(_Dfam, _vval, _vh)
    R = _graphe_R("G")
    ve = var("E")
    couvert = couvert_essai(_vh, R, ve)
    # conclusion EXACTE = couverture totale par essais (l'existence de la solution)
    assert r.conclusion == couverture_totale(couvert, ve, "x0tf")
    # DEUX hypothèses honnêtes : bon ordre + résidu de réalisation de la famille
    assert len(r.hypotheses) == 2
    assert E.est_bien_ordonne(R, ve) in r.hypotheses
    assert F.realisation_famille(_Dfam, _vval, _vh) in r.hypotheses
    # non vacuous + theorie intangible
    assert r.conclusion not in r.hypotheses
    assert len(E.theorie_ensembles().axiomes) == 22
