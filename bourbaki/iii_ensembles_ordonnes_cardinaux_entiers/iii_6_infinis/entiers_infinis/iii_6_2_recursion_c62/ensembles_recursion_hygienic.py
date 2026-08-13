"""Récursion C62 — WRAPPER α-HYGIÉNIQUE autour du gluing déposé (O3).

════════════════════════════════════════════════════════════════════════════════
BUT.  Le gluing de récursion déposé (`recursion_transfinie_existence_final`, via
`c62_recursion_sur_N` / `c63_iteration_sur_N`) REJETTE par τ-capture toute règle
NON triviale (factorielle) ou valeur initiale τ-valuée : `modus ponens : mineure ≠
antécédent` levé au fond de `antecedent_dans_domaine` (ensembles_restriction_somme).
Ce module DIAGNOSTIQUE précisément la capture, FOURNIT un correctif α-hygiénique du
SEUL site réellement réparable par α, et DOCUMENTE honnêtement la partie irréductible.

Le noyau (formule.py, noyau*) est INTACT ; theorie_ensembles = 22 axiomes.  Aucun
fichier déposé n'est modifié.  Toutes les briques sont DÉRIVÉES.

════════════════════════════════════════════════════════════════════════════════
DIAGNOSTIC EXACT (reproduit, localisé au nœud `modus_ponens`).

La capture qui bloque la factorielle se produit en UN point unique :

    iii_3_equipotence_cardinaux/recollement/ensembles_restriction_somme.py:76
        ex = N.modus_ponens(huv, N.s5(body, vv, "y"))   # (∃y)((u,y)∈F)

appelé depuis `reunion_graphes_fonctionnelle` (ligne 118, `adH_v`), elle-même
appelée par `extension_un_pas_fonctionnelle` (gluing déposé) sur F = H = ⋃𝔇 ∪ {(x,v)}
(le graphe-union d'un pas de récursion).

Il y a DEUX classes de collision DISTINCTES sous ce même nœud :

  (A) CLASSE-QUANTIFICATEUR  (« y-class ») — réparable par α.
      AXIOME_DOM code en dur le liant « y » :  u∈domF ⇔ (∃y)((u,y)∈F).
      Si F lie INTERNEMENT un « y » (τ-terme), le PAS S5 `subst_f(v,"y",body)`
      renomme ce « y » interne en « @k » → l'antécédent S5 n'est plus `== (u,v)∈F`
      (ils restent α-égaux).  FIX : faire le S5 sur un liant FRAIS-TOTAL (évitant
      AUSSI les liants internes, cf. `_fraiche_totale`), puis α-convertir le
      `(∃frais)…` résultant vers le `(∃y)…` exigé par AXIOME_DOM via `alpha_bridge`
      (renommage de liant ∃ — DANS la portée du pont).  ⇒ `antecedent_dans_domaine_hygienic`.

  (B) CLASSE-VALEUR  (« value-class ») — IRRÉDUCTIBLE par α au niveau wrapper.
      Le TÉMOIN du S5 est le TERME-VALEUR `v = var("v")` (2ᵉ projection, liant libre
      FIXÉ par `reunion_graphes_fonctionnelle` ligne 96).  Or H = ⋃𝔇∪{(x,v)} LIE
      internement « v » (52× : les `(∃v)` des couples dans `est_fonctionnel` /
      `couvert_essai` sont sous des τ-termes de H).  `subst_f(var("v"),·,·)` est alors
      CAPTURÉ par ces liants internes → renommage → antécédent ≠ mineure.
      Ici « v » N'EST PAS LIBRE dans H (libres(H)={x0tf}) : le conflit est purement
      un conflit de NOM entre la VARIABLE-OBJET « v » (fixée par le gluing déposé) et
      des liants INTERNES de H.  α-renommer « v » rendrait la preuve saine — MAIS « v »
      est tissé STRUCTURELLEMENT dans tout `reunion_graphes_fonctionnelle` et au-dessus
      (jusqu'à c62) ; le corriger = RE-DÉRIVER la chaîne déposée.  `alpha_bridge` NE
      PEUT PAS réparer après coup : la différence est portée par un τ-liant INTERNE à
      un terme d'un atome `∈` — hors de portée DOCUMENTÉE du pont (il lève ValueError).

CONCLUSION HONNÊTE (O3).  L'α-hygiène RÉSOUT la classe-quantificateur (y-class) — le
correctif `antecedent_dans_domaine_hygienic` ci-dessous CLÔT le cas où F lie « y ».
Mais la FACTORIELLE bute sur la classe-VALEUR (B) : le verrou réel n'est pas le NOM du
quantificateur ∃ mais le NOM de la variable-objet-valeur « v » captée par les liants
internes du graphe-union.  CE point est IRRÉDUCTIBLE par α seule au niveau wrapper ;
il confirme que franchir O3 pour la factorielle exige une chirurgie du gluing déposé
(rendre `reunion_graphes_fonctionnelle` / le S5 de `antecedent_dans_domaine`
hygiéniques EN AMONT — variable-valeur fraîche-totale propagée), pas une simple
α-conversion en aval.

Ce module expose les deux faits par des fonctions vérifiables (CASE A clôt, CASE B
lève), sans rien postuler ni asserter de faux.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, Terme, Formule
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    instancie, equivalence_arriere,
)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.outil_alpha_bridge import (
    alpha_bridge, _fraiche_totale,
)
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege import appartient


def _t(t):
    return t if isinstance(t, Terme) else var(t)


# ════════════════════════════════════════════════════════════════════════════
#  CORRECTIF α-HYGIÉNIQUE du SITE de capture (classe-quantificateur, y-class).
# ════════════════════════════════════════════════════════════════════════════
# @livre Ch.III §6.2 Demo.C63 | E III.46 L.25-33 | PDF p.149  (déduction de C63 depuis C62 : maillon α-hygiénique du gluing)
# @livre Ch.III §6.2 Demo.C63 | E III.47 L.1-3 | PDF p.150  (fin de la déduction de C63)
def antecedent_dans_domaine_hygienic(u="u", v="v", f="F"):
    """⊢ ((u,v) ∈ F) ⇒ (u ∈ dom F),  α-HYGIÉNIQUE sur le liant ∃ « y ».   (DÉRIVÉ.)

    Identique en CONCLUSION à `antecedent_dans_domaine` déposé, mais le pas S5 utilise
    un liant FRAIS-TOTAL (évitant aussi les liants internes de F), puis α-convertit le
    `(∃frais)((u,frais)∈F)` obtenu vers la forme `(∃y)((u,y)∈F)` exigée par AXIOME_DOM
    (via `alpha_bridge`, renommage de liant ∃ — dans la portée du pont).

    RÉSOUT la classe-QUANTIFICATEUR : F peut lier internement « y » sans déclencher la
    τ-capture du S5 déposé.  NE résout PAS la classe-VALEUR : si le TERME-valeur `v`
    porte un nom qu'un liant interne de F capture, le S5 (qui substitue `v`) est capturé
    AVANT toute α-conversion → lève `ValueError` (cf. docstring module, point B).

    SOUND : S5, AXIOME_DOM, equivalence_arriere, loi_deduction, alpha_bridge sont tous
    DÉRIVÉS/certifiés ; aucune confiance ajoutée ; theorie inchangée (22)."""
    vu, vv, vf = _t(u), _t(v), _t(f)
    cpl = E.couple(vu, vv)
    huv_f = appartient(cpl, vf)
    huv = N.assume(huv_f)                                      # (u,v)∈F

    ax_dom = N.axiome(E.theorie_ensembles(), E.AXIOME_DOM)
    car = instancie(instancie(ax_dom, vf), vu)                # u∈domF ⇔ (∃y)((u,y)∈F)

    # Cible : le (∃y)…∈F porté par le membre droit de AXIOME_DOM (liant fixé « y »).
    out = []
    def _collect(fm: Formule):
        if fm.tag == "exists" and fm.lieur == "y":
            out.append(fm)
        for s in fm.sous:
            _collect(s)
    _collect(car.conclusion)
    if not out:
        raise ValueError("antecedent_dans_domaine_hygienic : (∃y) introuvable dans AXIOME_DOM")
    car_exists = out[0]                                        # (∃y)((u,y)∈F)  forme exacte

    # S5 sur liant FRAIS-TOTAL (évite y ET tout liant interne de F) → pas de @k-injection.
    frais = _fraiche_totale([car.conclusion, huv_f])
    body_frais = appartient(E.couple(vu, var(frais)), vf)     # (u,frais)∈F
    ex_frais = N.modus_ponens(huv, N.s5(body_frais, vv, frais))   # (∃frais)((u,frais)∈F)

    # α-convertit (∃frais)… vers (∃y)…  (renommage de liant ∃ — DANS la portée du pont).
    ex_y = (ex_frais if ex_frais.conclusion == car_exists
            else alpha_bridge(ex_frais, car_exists))           # (∃y)((u,y)∈F)

    u_in_dom = N.modus_ponens(ex_y, equivalence_arriere(car))  # u∈domF
    return N.loi_deduction(huv_f, u_in_dom)


__all__ = ["antecedent_dans_domaine_hygienic"]
