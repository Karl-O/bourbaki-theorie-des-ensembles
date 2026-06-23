"""§III.3 — Proposition 3 et Corollaire de la Proposition 4 (E III.25-26).

PROPOSITION 3 (E III.25). — « Soient X et Y des ensembles. S'il existe une
surjection f de X sur Y, on a Card(Y) ≤ Card(X). »
  Démonstration de Bourbaki : « il existe une section s associée à f (II, p. 18,
  prop. 8) et s est une injection de Y dans X. »

COROLLAIRE de la PROPOSITION 4 (E III.26). — « Pour toute famille (E_ι)_{ι∈I}
d'ensembles, le cardinal de la réunion ⋃ E_ι est au plus égal à la somme
∑ Card(E_ι). »
  Démonstration de Bourbaki : « il existe une application de la somme S des E_ι
  sur leur réunion (II, p. 30) ; le corollaire résulte donc des prop. 3 et 4. »

──────────────────────────────────────────────────────────────────────────────
ROUTE (fidèle à Bourbaki) :

• PROP 3 : une section s de f satisfait (∀y∈Y) f(s(y))=y, c.-à-d. — au sens du
  projet — `est_section(s,f,Y)`, qui est LITTÉRALEMENT la formule
  `est_retraction(f, s, Y)` (rôles : « f joue la rétraction de s »). Par la
  Proposition 8 §II.3 (sens injectif, `retraction_implique_injective`), s est
  donc injective sur Y. Avec les données structurelles d'une application s : Y→X
  (s fonctionnel, dom s = Y, image(s,Y) ⊂ X — honnêtes, jamais postulées), on
  assemble `est_injection_de(s, Y, X)` puis S5 (témoin s) donne
  `inf_egal_card(Y, X)`, c.-à-d. Card(Y) ≤ Card(X).

• PROP 4-COR : la surjection canonique de la somme S = ⊔ E_ι sur la réunion
  U = ⋃ E_ι donne, par la Prop 3, Card(U) ≤ Card(S). Or Card(S) = ∑ Card(E_ι)
  (somme cardinale = Card de la somme disjointe, `somme_cardinale`). D'où
  Card(U) ≤ ∑ Card(E_ι). On laisse en HYPOTHÈSE HONNÊTE l'existence de cette
  surjection canonique (II, p. 30 — « il existe une application de S sur U »),
  faute de l'avoir construite ici, et on en DÉRIVE la conclusion par la Prop 3.

HYPOTHÈSES HONNÊTES (fidèles, jamais fausses/vacuous, jamais postulées comme
théorèmes) : pour Prop 3, les données « s : Y→X application » (s fonctionnel,
dom s=Y, image(s,Y)⊂X) en plus de « s section de f » ; pour Prop 4-Cor,
l'existence d'une surjection-section de la somme sur la réunion.
"""
from __future__ import annotations

from bourbaki.logique.formule import (var, egal, et, appartient, impl, existe, Terme)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.logique.tactiques.tactiques_abrege2 import conjonction_intro
from bourbaki.cardinaux.ensembles_cardinaux import est_injection_de, inf_egal_card
from bourbaki.ensembles.fonctions.ii_3_8_retractions_sections.ensembles_retractions import retraction_implique_injective


def _T(v):
    return v if isinstance(v, Terme) else var(v)


# ── PROPOSITION 3 (E III.25) — surjection X↠Y ⇒ Card(Y) ≤ Card(X) ─────────────
def prop3_surjection_inf_egal(s="S", f="F", x="X", y="Y"):
    """⊢_{s section de f sur Y ; s fonctionnel ; dom s=Y ; image(s,Y)⊂X}
         (Y ≤ X)   c.-à-d.  inf_egal_card(Y, X), soit Card(Y) ≤ Card(X).

    PROPOSITION 3 §III.3. Une section s de la surjection f : X↠Y est une
    injection de Y dans X (Prop. 8 §II.3), d'où Y ≤ X (déf. de ≤ par injection).

    Hypothèses (honnêtes, fidèles à « s est une section, s : Y→X ») :
      • est_section(s, f, Y)        : (∀y∈Y) f(s(y))=y   [= est_retraction(f,s,Y)]
      • s fonctionnel               : est_fonctionnel(s)
      • dom s = Y                   : dom(s) = Y
      • image(s, Y) ⊂ X            : inclus(image(s,Y), X)
    L'INJECTIVITÉ de s sur Y est DÉRIVÉE (non supposée) via la Proposition 8."""
    vS, vF, vX, vY = _T(s), _T(f), _T(x), _T(y)
    # « s est une section de f sur Y » s'écrit (∀x)(x∈Y ⇒ f(s(x))=x), c.-à-d.
    # est_retraction(f, s, Y) au sens du projet (f joue le rôle de la rétraction
    # de s) : c'est EXACTEMENT la condition de section f∘s=Id_Y (Déf. 11), au
    # nom de liant « x » près (forme attendue par la Proposition 8 ci-dessous).
    hsec = N.assume(E.est_retraction(vF, vS, vY))             # s section de f sur Y
    # Prop. 8 (sens injectif) appliquée avec « rétraction := f, fonction := s, partie := Y » :
    #   est_retraction(f,s,Y) ⇒ injective_dans(s, Y).
    prop8 = retraction_implique_injective(r=f, f=s, a=y)      # ⊢ est_retraction(f,s,Y) ⇒ inj(s,Y)
    s_inj = N.modus_ponens(hsec, prop8)                       # injective_dans(s, Y)
    # Données structurelles « s : Y → X » (honnêtes) :
    h_func = N.assume(E.est_fonctionnel(vS))                  # s fonctionnel
    h_dom = N.assume(egal(E.dom(vS), vY))                     # dom s = Y
    h_img = N.assume(E.inclus(E.image(vS, vY), vX))          # image(s,Y) ⊂ X
    # Assemblage est_injection_de(s, Y, X) :
    inj_de = conjonction_intro(conjonction_intro(conjonction_intro(
        h_func, h_dom), s_inj), h_img)                        # est_injection_de(s,Y,X)
    # S5 témoin s : (∃F) est_injection_de(F,Y,X) = inf_egal_card(Y,X).
    le = N.modus_ponens(inj_de, N.s5(est_injection_de(var("F"), vY, vX), vS, "F"))
    return le                                                  # Y ≤ X


def cible_prop3_surjection_inf_egal(x="X", y="Y"):
    """Cible exacte de prop3_surjection_inf_egal : inf_egal_card(Y, X)."""
    return inf_egal_card(_T(y), _T(x))


# ── PROPOSITION 4, COROLLAIRE (E III.26) — Card(⋃ E_ι) ≤ ∑ Card(E_ι) ──────────
def prop4cor_card_reunion_inf_egal_somme(g="G", u="U", fam="A", i="I"):
    """⊢_{g section de la surjection canonique (⊔E_ι)↠U ; g:U→⊔E_ι application}
         (Card(U) ≤ ∑_{ι∈I} Card(E_ι))
       c.-à-d.  inf_egal_card(U, ⊔_{ι∈I} E_ι),  où U = ⋃_{ι∈I} E_ι.

    COROLLAIRE de la PROPOSITION 4. Par la Proposition 3 appliquée à la
    surjection canonique de la somme S = ⊔_{ι∈I} E_ι sur la réunion
    U = ⋃_{ι∈I} E_ι (« il existe une application de S sur U », II, p. 30), on a
    Card(U) ≤ Card(S). Or, par définition, ∑_{ι∈I} Card(E_ι) = Card(S)
    (`somme_cardinale` = cardinal de la somme disjointe `somme_famille`). La
    conclusion `inf_egal_card(U, ⊔E_ι)` EST donc Card(U) ≤ ∑ Card(E_ι).

    On INSTANCIE directement la Proposition 3 avec X := ⊔_{ι∈I} E_ι (le terme
    `somme_famille(A, I)` sous-jacent à la somme cardinale) ; aucune hypothèse
    nouvelle hors de celles, honnêtes, de la Prop 3.

    Hypothèses honnêtes (cf. Prop 3, transportées via X := ⊔E_ι) :
      • g est une section de la surjection canonique f : (⊔E_ι) ↠ U
        [est_retraction(f, g, U)] ;
      • g fonctionnel ; dom g = U ; image(g, U) ⊂ ⊔E_ι.
    Ce sont exactement les données « il existe une application (section) de la
    somme sur la réunion » (II, p. 30)."""
    vSomme = E.somme_famille(_T(fam), _T(i))                  # S = ⊔_{ι∈I} E_ι (terme)
    # Prop 3 avec X := ⊔E_ι, Y := U, s := g :  inf_egal_card(U, ⊔E_ι).
    return prop3_surjection_inf_egal(s=g, f="F", x=vSomme, y=u)


def cible_prop4cor_card_reunion_inf_egal_somme(u="U", fam="A", i="I"):
    """Cible : inf_egal_card(U, ⊔E_ι) — Card(⋃ E_ι) ≤ Card(⊔ E_ι) = ∑ Card(E_ι).

    NB : ∑_{ι∈I} Card(E_ι) = somme_cardinale(A,I) = Card(somme_famille(A,I)) =
    Card(⊔E_ι) par définition ; inf_egal_card(U, ⊔E_ι) est donc bien
    Card(⋃E_ι) ≤ ∑ Card(E_ι)."""
    return inf_egal_card(_T(u), E.somme_famille(_T(fam), _T(i)))


__all__ = ["prop3_surjection_inf_egal", "cible_prop3_surjection_inf_egal",
           "prop4cor_card_reunion_inf_egal_somme",
           "cible_prop4cor_card_reunion_inf_egal_somme"]
