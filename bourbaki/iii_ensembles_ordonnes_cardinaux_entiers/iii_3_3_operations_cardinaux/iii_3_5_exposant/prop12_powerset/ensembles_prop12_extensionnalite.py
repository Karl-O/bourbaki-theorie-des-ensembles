# -*- coding: utf-8 -*-
"""§III.3.5 Prop.12, brique (iii) — χ∘ρ = id sur 𝓕(X;2) : χ_{Pre(f)} = f.

CHANTIER OUVERT (21 août 2026, file Cantor rectifiée, DECISIONS 21h30) :
c'est LE verrou de Card 𝔓X = 2^Card X, donc du Théorème 2 (Cantor, 2^a > a,
E III.30 L.20-21, scan lu). Rien n'est encore dérivé ici — ce module pose le
PLAN VÉRIFIÉ CONTRE LES PIÈCES EXISTANTES, et se remplit sous-lemme par
sous-lemme, chacun testé.

OUTIL-CLÉ (clos) : `graphe_egal_par_valeurs` (II.3.4, extensionnalité
fonctionnelle) — six conjoints à établir pour F := graphe(χ_{Pre₁(f)}) et
G := graphe sous-jacent de f (= pr₁(pr₁ f) si f est le triple (G, X, 2)) :

  (a) χ_{Pre(f)} FONCTIONNEL      — existe (rounds χ précédents) ;
  (b) G_f FONCTIONNEL             — depuis f ∈ 𝓕(X;2) (le triple est une
                                    application : son graphe est fonctionnel) ;
  (c) χ graphe / (d) G_f graphe   — idem, structurel ;
  (e) dom χ_{Pre(f)} = dom G_f    — les deux valent X (dom χ_Y = X connu ;
                                    dom G_f = X depuis le triple) ;
  (f) (∀z)(z ∈ X ⇒ χ_{Pre(f)}(z) = G_f(z)) — LE CŒUR : par cas z∈Pre(f) /
      z∉Pre(f) : χ vaut 1 resp. 0 (valeurs de χ, rounds précédents) ; f vaut
      1 ⇔ (z,1)∈G_f ⇔ z∈Pre(f) (définition de Pre, preimage_membre) et f ne
      prend que les valeurs 0/1 (f à valeurs dans 2 = {0,1} : dichotomie
      depuis l'image ⊂ 2 — sous-lemme deux_valeurs à écrire).

ORDRE D'ÉCRITURE (un sous-lemme = un commit testé) :
  1. `f_graphe_fonctionnel(f, x)`   — (b)+(d) depuis f ∈ 𝓕(X;2) ;
  2. `f_domaine(f, x)`              — (e) côté f ;
  3. `f_deux_valeurs(f, x, z)`      — f(z) ∈ {0,1} (dichotomie image ⊂ 2) ;
  4. `valeurs_coincident(f, x, z)`  — (f), par cas via 3 + valeurs de χ ;
  5. `chi_rho_identite(f, x)`       — l'assemblage par graphe_egal_par_valeurs.

FORMES EXACTES vérifiées (21 août, 22h00) :
  · axiome_exposant (via N.axiome(E.theorie_exposant(X, deux()), …) puis
    instancie à G) : G ∈ 2^X ⇔ (G ⊂ X×2 et G fonctionnel et dom G = X) —
    l'équivalence-avant sous assume(G∈2^X) donne d'un coup les sous-lemmes
    1 (fonctionnel) et 2 (dom = X) ;
  · _conjonction_hypotheses de graphe_egal_par_valeurs exige AUSSI
    est_un_graphe(F) et est_un_graphe(G) : pour G, à dériver de G ⊂ X×2
    (un ensemble de couples est un graphe — lemme-pont « inclus dans un
    produit ⇒ graphe » : TROUVÉ — _inclus_produit_est_graphe(vG, vE, vF)
    (ii_5_2/ensembles_application_valeur l.163, {G⊂E×F} ⊢ est_un_graphe(G),
    prend des TERMES) ;
    pour F = χ_{Pre(f)} : chi_inclus_produit + le même pont ;
  · l'ordre de la conjonction (gauche-associée) : ((((fonct F et fonct G)
    et graphe F) et graphe G) et dom=dom) et ∀-valeurs.

Pièces existantes vérifiées ce jour : chi_dans_applications (χ_Y ∈ 𝓕(X;2)),
rho_chi_identite (Pre(χ_Y) = Y), preimage_membre, chi_inclus_produit,
graphe_egal_par_valeurs (clos, 6 conjoints).
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, inclus, appartient)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_elim_gauche, conjonction_elim_droite, instancie, equivalence_avant)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.ii_theorie_des_ensembles.ii_5_produit_famille.ii_5_2_ensemble_applications.ensembles_application_valeur import (
    _inclus_produit_est_graphe)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_5_exposant.prop12_powerset.ensembles_powerset_deux import (
    deux)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def _cut(thm, P, pr):
    """Décharge l'hypothèse P de `thm` en la remplaçant par sa preuve `pr`."""
    return N.modus_ponens(pr, N.loi_deduction(P, thm))


# Sous-lemmes 1+2 (+graphe) — (b), (d), (e) du plan, d'un coup.
def g_decompose(g="Gext", x="Xext"):
    """{G ∈ 2^X} ⊢ le quadruplet (G ⊂ X×2, G fonctionnel, dom G = X,
    est_un_graphe(G)) — tuple de quatre théorèmes, chacun sous la seule
    hypothèse d'appartenance à l'exposant.

    axiome_exposant (E.II.5.2, via theorie_exposant) : G ∈ 2^X ⇔
    (G ⊂ X×2 et G fonctionnel et dom G = X) ; le quatrième membre vient du
    pont `_inclus_produit_est_graphe` (un ensemble de couples est un graphe),
    son hypothèse d'inclusion étant coupée par la première conclusion."""
    vg, vx = _t(g), _t(x)
    deux_ens = deux()
    ax = N.axiome(E.theorie_exposant(vx, deux_ens),
                  E.axiome_exposant(vx, deux_ens))       # (∀G)(G∈2^X ⇔ …)
    car = instancie(ax, vg)                              # G∈2^X ⇔ (⊂ et fonct et dom)
    h = N.assume(appartient(vg, E.exposant(vx, deux_ens)))
    corps = N.modus_ponens(h, equivalence_avant(car))    # (G⊂X×2 et fonct) et dom=X
    dom_eq = conjonction_elim_droite(corps)              # dom G = X
    gauche = conjonction_elim_gauche(corps)
    incl = conjonction_elim_gauche(gauche)               # G ⊂ X×2
    fonct = conjonction_elim_droite(gauche)              # est_fonctionnel(G)
    graphe = _cut(_inclus_produit_est_graphe(vg, vx, deux_ens),
                  inclus(vg, E.produit(vx, deux_ens)), incl)   # est_un_graphe(G)
    return incl, fonct, dom_eq, graphe


__all__ = ["g_decompose"]
