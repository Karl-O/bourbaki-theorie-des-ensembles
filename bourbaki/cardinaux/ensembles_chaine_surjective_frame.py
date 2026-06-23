"""§III.6.3 — Théorème 2 (HESSENBERG) : SURJECTIVITÉ et DOMAINE du recollement d'une
CHAÎNE de bijections (le majorant-recollement de l'argument de Zorn, E.III.48).

Suite de `ensembles_union_chaine_bijection` (fonctionnalité + injectivité COUPLE
closes) : ce module ferme les DEUX dernières moitiés COUPLE-NATIVES du recollement
de chaîne — la SURJECTIVITÉ de ⋃φ sur ⋃S et la couverture du DOMAINE
dom(⋃φ)=(⋃S)×(⋃S) — au niveau des COUPLES (comme `union_famille_injective`, ce qui
contourne le mur de capture de la variable de valeur).

────────────────────────────────────────────────────────────────────────────────
CE QUI EST GENUINEMENT CLOS ICI (réutilisation de l'infra FAMILLE de C60) :

  (4) SURJECTIVITÉ couple-native — `union_chaine_surjective` :
        { recollement_surjectif(𝔇,US) } ⊢ (∀w)( w∈US ⇒ (∃a)((a,w)∈⋃𝔇) ).
      Tout w∈⋃S est dans un morceau S_i = img(φ_i) (φ_i surjective), donc atteint
      par un antécédent a dans CE membre p=φ_i, donc (a,w)∈⋃φ (introduction réunion).
      L'hyp HONNÊTE recollement_surjectif EMPAQUETTE « w∈S_i et φ_i surjective ».

  (5) DOMAINE couple-native — `union_chaine_dom` :
        { recollement_domaine(𝔇,Dom) } ⊢ (∀ab)( ab∈Dom ⇒ (∃w)((ab,w)∈⋃𝔇) ).
      Tout ab∈(⋃S)×(⋃S) a ses deux coordonnées dans un même S_k (chaîne DIRIGÉE),
      donc ab∈dom(φ_k), donc φ_k(ab) défini : (ab,w)∈φ_k⊂⋃φ.  L'hyp HONNÊTE
      recollement_domaine EMPAQUETTE « ab couvert par un membre dirigé ».

────────────────────────────────────────────────────────────────────────────────
OBSTRUCTION HONNÊTE (NON close — REPORTÉE, jamais postulée) :

  FRAME-MEMBERSHIP (⋃S,⋃φ)∈𝔉(E) via l'axiome OPAQUE `axiome_frame` exige le corps
  `est_bijection_de(⋃φ,(⋃S)×(⋃S),⋃S)`, lequel est défini avec :
      • `est_surjective` = ÉGALITÉ D'ENSEMBLES image(⋃φ,(⋃S)×(⋃S)) = ⋃S ;
      • `injective_dans` = injectivité GARDÉE PAR VALEUR (∀u,u'∈A)(f(u)=f(u')⇒u=u') ;
      • `dom(⋃φ) = (⋃S)×(⋃S)` = ÉGALITÉ D'ENSEMBLES.
  Or ce module (et l'amont) ne produit que les versions COUPLE-NATIVES (image
  couple-niveau (∃a)(a,w)∈⋃φ ; injectif_graphe ; couverture couple-niveau du
  domaine).  Le PONT couple→valeur/couple→égalité-d'ensembles (injectif_graphe →
  injective_dans ; (∀w∈US)(∃a)(a,w)∈⋃φ → image(⋃φ,·)=US par double inclusion +
  axiome image E.II.39) n'est PAS construit dans le dépôt en version recollement.
  C'est l'obstruction EXACTE : la frame-membership et donc la décharge
  INCONDITIONNELLE de `enonce_chaine_majoree` restent hors d'atteinte ici.  Ces deux
  lemmes COUPLE-NATIFS sont les briques manquantes pour cette décharge ; voir RAPPORT.

INVARIANT : theorie_ensembles() reste = 22.  Aucun axiome nouveau ; rien postulé ;
ni la bijection complète ni l'inductivité ne sont supposées vraies (antécédent).
"""
from __future__ import annotations

from bourbaki.logique.formule import (
    Terme, var, egal, et, impl, existe, pourtout, appartient, inclus,
)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.logique.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_arriere, instancie,
)
from bourbaki.logique.tactiques.tactiques_abrege_quantif import (
    existe_elimination, alpha_existe,
)
from bourbaki.ordre.iii_2_bon_ordre.recurrence_transfinie.ensembles_c60_coeur import (
    union_famille, _inst_union_famille,
)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# ════════════════════════════════════════════════════════════════════════════
#  PRÉDICATS HONNÊTES de recollement (couple-natifs).
# ════════════════════════════════════════════════════════════════════════════
def recollement_surjectif(D, US, w="wsj", p="psj", a="asj"):
    """recollement_surjectif(𝔇,US) :=
        (∀w)( w∈US ⇒ (∃p)( p∈𝔇 et (∃a)( (a,w)∈p ) ) ).

    « Chaque w∈⋃S est ATTEINT par un membre de la chaîne » : w est dans le morceau
    S_i = img(φ_i) d'un certain membre p=φ_i de 𝔇 (φ_i SURJECTIVE sur S_i), donc
    possède un antécédent a dans CE membre.  C'est exactement la donnée « union des
    images = ⋃S » au niveau COUPLE — l'hypothèse minimale qui fait passer la
    surjectivité à la réunion ⋃φ.  HONNÊTE (jamais postulée vraie)."""
    vD, vUS = _t(D), _t(US)
    vw, vp, va = var(w), var(p), var(a)
    return pourtout(w, impl(appartient(vw, vUS),
        existe(p, et(appartient(vp, vD),
                     existe(a, appartient(E.couple(va, vw), vp))))))


def recollement_domaine(D, Dom, ab="abdm", p="pdm", w="wdm"):
    """recollement_domaine(𝔇,Dom) :=
        (∀ab)( ab∈Dom ⇒ (∃p)( p∈𝔇 et (∃w)( (ab,w)∈p ) ) ).

    « Chaque ab∈(⋃S)×(⋃S) est COUVERT par un membre de la chaîne » : les deux
    coordonnées de ab tombent dans un même morceau S_k (chaîne DIRIGÉE), donc
    ab∈S_k×S_k = dom(φ_k), et φ_k étant fonctionnelle (totale sur S_k×S_k) lui
    associe une valeur w : (ab,w)∈φ_k.  C'est la couverture du domaine au niveau
    COUPLE — l'hypothèse qui fait passer dom=(⋃S)×(⋃S) à la réunion.  HONNÊTE."""
    vD, vDom = _t(D), _t(Dom)
    vab, vp, vw = var(ab), var(p), var(w)
    return pourtout(ab, impl(appartient(vab, vDom),
        existe(p, et(appartient(vp, vD),
                     existe(w, appartient(E.couple(vab, vw), vp))))))


# ════════════════════════════════════════════════════════════════════════════
#  Introduction réunion-famille au niveau COUPLE (motif _membre_dans_union de C60,
#  mais avec témoin p ENCORE EXISTENTIEL — on travaille sous élimination).
# ════════════════════════════════════════════════════════════════════════════
def _couple_dans_union(D, p, c, hpD, hcp):
    """De ⊢ p∈𝔇 [hpD] et ⊢ c∈p [hcp] déduit ⊢ c∈⋃𝔇  (introduction réunion-famille)."""
    vD, vp, vc = _t(D), _t(p), _t(c)
    corps_temoin = conjonction_intro(hpD, hcp)                  # p∈𝔇 et c∈p
    R = et(appartient(var("punion"), vD), appartient(vc, var("punion")))
    ex = N.modus_ponens(corps_temoin, N.s5(R, vp, "punion"))   # (∃p)(p∈𝔇 et c∈p)
    return N.modus_ponens(ex, equivalence_arriere(_inst_union_famille(vD, vc)))  # c∈⋃𝔇


# ════════════════════════════════════════════════════════════════════════════
#  (4) 🎯 SURJECTIVITÉ couple-native du recollement de chaîne.
# ════════════════════════════════════════════════════════════════════════════
def union_chaine_surjective(D="Dchaine", US="USchaine"):
    """{ recollement_surjectif(𝔇,US) } ⊢ (∀w)( w∈US ⇒ (∃a)( (a,w)∈⋃𝔇 ) ).
                                                              [1 hyp HONNÊTE].

    🎯 SURJECTIVITÉ (niveau COUPLE) du recollement de chaîne : tout w∈⋃S est une
    VALEUR de ⋃φ.  Témoin p∈𝔇 (= φ_i) avec antécédent a : (a,w)∈p ⊂ ⋃φ par
    introduction réunion-famille.  L'hyp recollement_surjectif est HONNÊTE (empaquette
    « w∈img φ_i pour un i ») ; jamais postulée vraie ; conclusion ∉ hyps ; theorie=22."""
    vD, vUS = _t(D), _t(US)
    U = union_famille(vD)
    vw, va = var("wsj"), var("asj")

    hsurj = N.assume(recollement_surjectif(vD, vUS))          # [HONNÊTE]

    # hypothèse de l'implication-but : w∈US
    h_w = N.assume(appartient(vw, vUS))
    # instancie l'hyp en w :  w∈US ⇒ (∃p)(p∈𝔇 et (∃a)((a,w)∈p))
    surj_w = N.modus_ponens(h_w, instancie(hsurj, vw))        # (∃p)(p∈𝔇 et (∃a)((a,w)∈p))

    cible_w = existe("asj", appartient(E.couple(va, vw), U))  # (∃a)((a,w)∈⋃𝔇)

    # ── corps du témoin p :  p∈𝔇 et (∃a)((a,w)∈p) ────────────────────────────
    vp = var("psj")
    corps_p = et(appartient(vp, vD), existe("asj", appartient(E.couple(va, vw), vp)))
    Hp = N.assume(corps_p)
    pD = conjonction_elim_gauche(Hp)                          # p∈𝔇
    ex_a = conjonction_elim_droite(Hp)                        # (∃a)((a,w)∈p)

    # ── corps du témoin a :  (a,w)∈p  ⇒  (a,w)∈⋃𝔇  ⇒  (∃a)((a,w)∈⋃𝔇) ─────────
    H_aw = N.assume(appartient(E.couple(va, vw), vp))         # (a,w)∈p
    aw_U = _couple_dans_union(vD, vp, E.couple(va, vw), pD, H_aw)   # (a,w)∈⋃𝔇
    ex_aw_U = N.modus_ponens(aw_U, N.s5(appartient(E.couple(va, vw), U), va, "asj"))  # (∃a)((a,w)∈⋃𝔇)

    # élimine le témoin a (asj non libre dans cible_w)
    wit_a = N.loi_deduction(appartient(E.couple(va, vw), vp), ex_aw_U)
    after_a = N.modus_ponens(ex_a, existe_elimination(wit_a, "asj"))   # (∃a)((a,w)∈⋃𝔇)  [Hp, ...]

    # élimine le témoin p (psj non libre dans cible_w)
    wit_p = N.loi_deduction(corps_p, after_a)
    after_p = N.modus_ponens(surj_w, existe_elimination(wit_p, "psj"))  # (∃a)((a,w)∈⋃𝔇)  [h_w, hsurj]

    impl_w = N.loi_deduction(appartient(vw, vUS), after_p)
    res = N.generalisation("wsj", impl_w)

    cible = pourtout("wsj", impl(appartient(vw, vUS), cible_w))
    assert res.conclusion == cible, "union_chaine_surjective : conclusion ≠ cible"
    assert recollement_surjectif(vD, vUS) in res.hypotheses, "surjective : hyp absente"
    assert res.conclusion not in res.hypotheses, "union_chaine_surjective : VACUOUS"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  (5) 🎯 DOMAINE couple-native du recollement de chaîne.
# ════════════════════════════════════════════════════════════════════════════
def union_chaine_dom(D="Dchaine", Dom="Domchaine"):
    """{ recollement_domaine(𝔇,Dom) } ⊢ (∀ab)( ab∈Dom ⇒ (∃w)( (ab,w)∈⋃𝔇 ) ).
                                                              [1 hyp HONNÊTE].

    🎯 COUVERTURE DU DOMAINE (niveau COUPLE) du recollement de chaîne : tout
    ab∈(⋃S)×(⋃S) est dans le domaine de ⋃φ.  Témoin p∈𝔇 (= φ_k, S_k contenant les
    deux coordonnées, chaîne DIRIGÉE) avec valeur w : (ab,w)∈p ⊂ ⋃φ par introduction
    réunion-famille.  L'hyp recollement_domaine est HONNÊTE (empaquette « ab couvert
    par un membre dirigé ») ; jamais postulée vraie ; conclusion ∉ hyps ; theorie=22."""
    vD, vDom = _t(D), _t(Dom)
    U = union_famille(vD)
    vab, vw = var("abdm"), var("wdm")

    hdom = N.assume(recollement_domaine(vD, vDom))            # [HONNÊTE]

    h_ab = N.assume(appartient(vab, vDom))                    # ab∈Dom
    dom_ab = N.modus_ponens(h_ab, instancie(hdom, vab))       # (∃p)(p∈𝔇 et (∃w)((ab,w)∈p))

    cible_ab = existe("wdm", appartient(E.couple(vab, vw), U))  # (∃w)((ab,w)∈⋃𝔇)

    vp = var("pdm")
    corps_p = et(appartient(vp, vD), existe("wdm", appartient(E.couple(vab, vw), vp)))
    Hp = N.assume(corps_p)
    pD = conjonction_elim_gauche(Hp)                          # p∈𝔇
    ex_w = conjonction_elim_droite(Hp)                        # (∃w)((ab,w)∈p)

    H_abw = N.assume(appartient(E.couple(vab, vw), vp))       # (ab,w)∈p
    abw_U = _couple_dans_union(vD, vp, E.couple(vab, vw), pD, H_abw)   # (ab,w)∈⋃𝔇
    ex_abw_U = N.modus_ponens(abw_U, N.s5(appartient(E.couple(vab, vw), U), vw, "wdm"))

    wit_w = N.loi_deduction(appartient(E.couple(vab, vw), vp), ex_abw_U)
    after_w = N.modus_ponens(ex_w, existe_elimination(wit_w, "wdm"))   # (∃w)((ab,w)∈⋃𝔇)

    wit_p = N.loi_deduction(corps_p, after_w)
    after_p = N.modus_ponens(dom_ab, existe_elimination(wit_p, "pdm"))

    impl_ab = N.loi_deduction(appartient(vab, vDom), after_p)
    res = N.generalisation("abdm", impl_ab)

    cible = pourtout("abdm", impl(appartient(vab, vDom), cible_ab))
    assert res.conclusion == cible, "union_chaine_dom : conclusion ≠ cible"
    assert recollement_domaine(vD, vDom) in res.hypotheses, "dom : hyp absente"
    assert res.conclusion not in res.hypotheses, "union_chaine_dom : VACUOUS"
    return res


__all__ = [
    "recollement_surjectif", "recollement_domaine",
    "union_chaine_surjective", "union_chaine_dom",
]
