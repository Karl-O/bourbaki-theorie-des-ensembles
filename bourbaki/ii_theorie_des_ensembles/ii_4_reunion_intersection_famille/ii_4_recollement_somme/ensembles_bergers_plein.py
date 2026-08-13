"""§III.3.4 / §II.4.8 — T2 LE PRINCIPE DES BERGERS PLEIN : f : E→F dont chaque
fibre EST c  ⇒  Card(E) = Card(c×F)  — l'assemblage final du chantier S3.

CHAÎNE (deux maillons, tous deux CLOS ailleurs, rien de neuf n'est postulé) :
  Card(E) = Card(⊔_{y∈F} f⁻¹⟨{y}⟩)      [recollement S3, card_decomposition_fibres]
  ⊔Xfib   = c×F                          [cœur T3b : fibres ponctuellement = c]
  Card(⊔Xfib) = Card(c×F)                [CONGRUENCE de Card sur l'égalité
                                          d'ENSEMBLES — même terme, pas d'invariance]
d'où Card(E) = Card(c×F) = produit_cardinal_binaire(c, F), terme-à-terme.
C'est EXACTEMENT la fermeture des obstructions (iii)-(iv) rapportées en tête de
iii_5_5_caracteristique_combinatoire/ensembles_prop9_bergers_iii5.py.

PALIERS CERTIFIÉS (un test chacun, cf. test_bergers_plein.py) :
  P5 fam_fibre_constante Γ⊢t∈F ⟹ Γ∪{HF,Hc} ⊢ valeur_famille(Xfib,t) = c
  P6 somme_fibres_egale_produit {HF,Hc}     ⊢ ⊔(Xfib, F) = c×F
  P7 bergers_plein {Hf1,Hf2,Hf3,HF,Hc}      ⊢ Card(E) = Card(c×F)       🎯 T2

HYPOTHÈSES HONNÊTES (exactement 5) :
  Hf1/Hf2/Hf3/HF : celles de S3 (cf. ensembles_fibres_famille) ;
  Hc := (∀ych∈F) valeur(Xfib,ych) = c — « chaque fibre EST l'ensemble c » :
        lecture ENSEMBLISTE (stratégie 2 du brief) de « f⁻¹(y) a exactement c
        éléments » (E III.27, Cor. 2 : a_ι = a pour tout ι).  La version où les
        fibres sont seulement ÉQUIPOTENTES à c demande la FONCTORIALITÉ de ⊔
        sur une famille de bijections (τ-témoins b_y par fibre, motif à liants
        frais) — OUVERTE, non forcée ici, documentée pour la suite.

LIANTS EXOTIQUES locaux : ych (liant de Hc), cbg (le cardinal-fibre), wcs (trou
Leibniz-Card) ; le cœur traverse {i, p, q, ics, ucs, pcs, qcs, wcs, zcs, yfb} —
les termes fournis (f, E, F, c) ne doivent contenir AUCUN de ces noms libre.
Rien postulé ; noyau/subst intouchés ; theorie_ensembles()==22 (asserté en test).
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, egal, impl, appartient, pourtout)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    instancie)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
    composer_egalites, congruence_terme)
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_recollement_somme.ensembles_fibres_famille import (
    _t, famille_fibres, somme_fibres, hypothese_fonctionnelle,
    hypothese_domaine, hypothese_valeurs, hypothese_pont_fam)
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_recollement_somme.ensembles_somme_constante import (
    _somme_ponctuelle_produit)


# ── Hc : l'hypothèse « fibres constantes » ───────────────────────────────────
def hypothese_fibres_constantes(f="ffb", b="Ffb", c="cbg"):
    """Hc := (∀ych)((ych∈F) ⇒ (valeur(Xfib,ych) = c)) — « chaque fibre EST c ».

    Lecture ENSEMBLISTE de « f⁻¹(y) a exactement c éléments » (cf. docstring de
    module : la version purement ÉQUIPOTENTE reste ouverte, fonctorialité de ⊔)."""
    X = famille_fibres(f, b)
    vy = var("ych")
    return pourtout("ych", impl(appartient(vy, _t(b)),
                                egal(E.valeur(X, vy), _t(c))))


# ── P5 : la valeur_famille des fibres au TERME vaut c ────────────────────────
def fam_fibre_constante(thm_in_F, tt, f="ffb", b="Ffb", c="cbg"):
    """P5 : Γ ⊢ t∈F  ⟹  Γ∪{HF, Hc} ⊢ valeur_famille(Xfib, t) = c.  (t TERME.)

    (α) HF : fam(Xfib,t) = valeur(Xfib,t) ; (β) Hc : valeur(Xfib,t) = c ;
    (γ) composition.  t sans « yfh »/« ych » libres (liants des hypothèses)."""
    X = famille_fibres(f, b)
    hf = N.assume(hypothese_pont_fam(f, b))
    fam_eq = N.modus_ponens(thm_in_F, instancie(hf, tt))   # fam = valeur
    hc = N.assume(hypothese_fibres_constantes(f, b, c))
    val_eq = N.modus_ponens(thm_in_F, instancie(hc, tt))   # valeur = c
    res = composer_egalites(fam_eq, val_eq)
    assert res.conclusion == egal(E.valeur_famille(X, tt), _t(c)), "P5 : forme"
    return res


# ── P6 : la somme des fibres est c×F ─────────────────────────────────────────
def somme_fibres_egale_produit(f="ffb", b="Ffb", c="cbg"):
    """P6 {HF, Hc} ⊢ somme_famille(Xfib, F) = c × F.   (le cœur, fibres = c.)"""
    X, vb, vc = famille_fibres(f, b), _t(b), _t(c)
    res = _somme_ponctuelle_produit(X, vb, vc,
        lambda tt, thm: fam_fibre_constante(thm, tt, f, b, c))
    assert res.conclusion == egal(somme_fibres(f, b), E.produit(vc, vb)), "P6 : forme"
    assert res.hypotheses == frozenset({
        hypothese_pont_fam(f, b),
        hypothese_fibres_constantes(f, b, c)}), "P6 : hyps"
    return res


# ── P7 = T2 : LE PRINCIPE DES BERGERS PLEIN ──────────────────────────────────
# @livre Ch.III §3.4 Cor.2 | E III.27 L.27-29 | PDF p.130
#   (LE PRINCIPE DES BERGERS PLEIN = recollement E ≅ ⊔ fibres (Rem. E II.30
#    L.11-14, card_decomposition_fibres) ∘ Cor. 2 (somme constante = produit) ;
#    les obstructions (iii)-(iv) de ensembles_prop9_bergers_iii5.py sont
#    EXACTEMENT les deux briques fermées ici et par S3.)
def bergers_plein(f="ffb", e="Efb", b="Ffb", c="cbg"):
    """🎯 T2 {Hf1, Hf2, Hf3, HF, Hc} ⊢ Card(E) = Card(c×F)   [= c·Card(F)].

    f : E→F dont chaque fibre EST c ⇒ Card(E) = Card(c×F) = produit_cardinal_
    binaire(c, F) (terme-à-terme, asserté).  Chaîne : Card(E) = Card(⊔Xfib)
    [card_decomposition_fibres, S3] puis Card(⊔Xfib) = Card(c×F) [congruence de
    Card sur l'égalité d'ensembles P6]."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
        cardinal)
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_produit.ensembles_arith_cardinale import (
        produit_cardinal_binaire)
    from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_recollement_somme.ensembles_decomposition_fibres_bij import (
        card_decomposition_fibres)
    ve, vb, vc = _t(e), _t(b), _t(c)
    S, P = somme_fibres(f, b), E.produit(vc, vb)
    base = card_decomposition_fibres(f, e, b)              # Card(E) = Card(⊔Xfib)
    step = N.modus_ponens(somme_fibres_egale_produit(f, b, c),
                          congruence_terme(S, P, cardinal(var("wcs")), "wcs"))
    res = composer_egalites(base, step)                    # Card(E) = Card(c×F)
    assert res.conclusion == egal(cardinal(ve), cardinal(P)), "T2 : forme"
    assert cardinal(P) == produit_cardinal_binaire(vc, vb), "T2 : RHS ≠ c·F"
    assert res.hypotheses == frozenset({
        hypothese_fonctionnelle(f), hypothese_domaine(f, e),
        hypothese_valeurs(f, e, b), hypothese_pont_fam(f, b),
        hypothese_fibres_constantes(f, b, c)}), "T2 : hyps"
    return res


__all__ = ["hypothese_fibres_constantes", "fam_fibre_constante",
           "somme_fibres_egale_produit", "bergers_plein"]
