# -*- coding: utf-8 -*-
"""PREUVE MACHINE : `theorie_ensembles()` ÉTAIT CONTRADICTOIRE — RÉPARÉ LE 26 JUIL. 2026.

╔══════════════════════════════════════════════════════════════════════════════╗
║ ⚠️  CE SCRIPT DOIT ÉCHOUER.  C'est un TEST DE NON-RÉGRESSION inversé : tant   ║
║ qu'il lève `ValueError: modus ponens : mineure ≠ antécédent` APRÈS avoir      ║
║ affiché ses deux contrôles « OK », la théorie est saine.  S'il RÉUSSIT un     ║
║ jour, l'incohérence est revenue — tout arrêter et lire ce fichier en entier.  ║
║                                                                              ║
║ ⚠️  L'INVARIANT EST 22, PAS 21.  La réparation a REMPLACÉ `AXIOME_INTER_FAM`  ║
║ par sa forme de sélection, elle n'en a PAS retiré : `theorie_ensembles()`     ║
║ vaut 22 avant comme après.  Ne « corrige » JAMAIS 22 vers 21 : ce serait      ║
║ retirer un axiome vivant.  (Le texte ci-dessous décrit l'état AVANT la        ║
║ réparation ; il est conservé intact comme récit de l'incident.)               ║
╚══════════════════════════════════════════════════════════════════════════════╝

Découvert le 26 juil. 2026 en transposant l'avertissement de José Grimm
(`@source sources/grimm_gaia/RR-6999-v7.pdf p.35 §2.7`) :

    « If the family is empty, then Bourbaki defines the intersection to be E.
      We do not like this definition, since it depends on the context.
      Taking for E the union of the family solves the problem. »

────────────────────────────────────────────────────────────────────────────────
LA FAUTE.  `AXIOME_INTER_FAM` (ensembles_abrege.py) est posé SANS RESTRICTION :

    (∀f)(∀I)(∀z)( z ∈ ⋂_{ι∈I} X_ι  ⇔  (∀i)(i∈I ⇒ z ∈ X_i) )

Or la Déf. 2 de Bourbaki (E.II.4.1) EXIGE I ≠ ∅ — la restriction est écrite en
PROSE dans la docstring de `inter_famille` (« ; I ≠ ∅ ») mais n'a JAMAIS été
encodée dans la formule.  Pour I = ∅ le membre droit est vide-vrai pour TOUT z,
donc ⋂_{ι∈∅} X_ι contient tout objet : c'est un ENSEMBLE UNIVERSEL.

LA CONTRADICTION.  Le corpus prouve déjà, CLOS, le contraire (Russell, E.II.6
Rem.) : `ii_1_collectivisantes/ensembles_pas_ensemble_universel.py`.
Les deux théorèmes sont clos et vivent dans la même théorie ⇒ elle est
contradictoire, donc TOUT y est démontrable.

PORTÉE.  Le NOYAU est hors de cause (il refuse bien les non-axiomes : contrôle 1
ci-dessous) ; c'est le JEU D'AXIOMES qui est fautif.  32 fichiers utilisent
`AXIOME_INTER_FAM`.  Leurs énoncés restent moralement corrects (ils s'en servent
avec I ≠ ∅), mais leur CERTIFICATION ne vaut plus tant que la faute n'est pas
réparée.

LE CORRECTIF (route Grimm, B5).  Remplacer l'AXIOME par une DÉFINITION :
⋂_{ι∈I} X_ι := { z ∈ ⋃_{ι∈I} X_ι | (∀i)(i∈I ⇒ z ∈ X_i) }  (sélection S8 dans la
réunion, unicité A1).  On obtient ⋂_{ι∈∅} = ∅ gratuitement, et l'hypothèse I ≠ ∅
ne subsiste que dans les énoncés de Bourbaki qui l'exigent réellement.

⚠️ CE PARAGRAPHE ANNONÇAIT « `theorie_ensembles()` passe de 22 à 21 axiomes ».
C'ÉTAIT LE PLAN, PAS CE QUI A ÉTÉ FAIT.  La route retenue est un REMPLACEMENT de
l'axiome par sa forme de sélection (strictement plus faible dans le cas I = ∅,
donc sans perte), pas une suppression : **l'invariant reste 22**, et le contrôle 2
ci-dessous l'asserte.  Cette phrase est corrigée le 26 juil. 2026 parce qu'un
lecteur pressé y aurait lu l'ordre de « réparer » 22 en 21 — c'est-à-dire de
retirer un axiome dont tout le §II.4 dépend.

────────────────────────────────────────────────────────────────────────────────
ÉTAT APRÈS RÉPARATION (26 juil. 2026, mesuré) : zone II.4+II.5+II.6 = 415 verts /
0 échec ; amont II.1+II.2+II.3 = 381 verts ; chapitre II entier = 796 verts ;
`theorie_ensembles()` = 22 ; 47 théorèmes migrés (40 inchangés, 7 renforcés, 0
irréparable) ; 18/18 modules déclarés honnêtes par audit adversarial `.bak`
contre courant.  Récit complet : `outils_ia/corpus/CAMPAGNE_DEMOS.md` (en tête)
et `outils_ia/traces/events.jsonl` (type `INCOHERENCE`).

Exécuter :  python outils_ia/audit/preuve_incoherence_inter_vide.py
            → doit AFFICHER les 2 contrôles OK puis ÉCHOUER (code de sortie 1).
"""
from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))   # racine V9

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, appartient, non, pourtout, existe)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    equivalence_arriere, instancie)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ii_1_collectivisantes.ensembles_pas_ensemble_universel import (
    pas_ensemble_universel)


def ensemble_universel_par_inter_vide(fam="Fam"):
    """⊢ (∀x)( x ∈ ⋂_{ι∈∅} Fam_ι ).   CLOS — c'est un ensemble universel.

    Route : AXIOME_INTER_FAM instancié à I := ∅, membre droit vide-vrai par
    AXIOME_VIDE (ex falso via le schéma s2)."""
    vFam, vx, vi = var(fam), var("x"), var("i")   # liant « i » imposé par l'axiome
    U = E.inter_famille(vFam, E.VIDE)

    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_INTER_FAM)
    eq = instancie(instancie(instancie(ax, vFam), E.VIDE), vx)

    nvide = instancie(N.axiome(E.theorie_ensembles(), E.AXIOME_VIDE), vi)   # ¬(i∈∅)
    P = appartient(vi, E.VIDE)
    Q = appartient(vx, E.valeur_famille(vFam, vi))
    imp = N.modus_ponens(nvide, N.s2(non(P), Q))       # (i∈∅) ⇒ (x∈Fam_i)  [ex falso]
    allg = N.generalisation("i", imp)
    membre = N.modus_ponens(allg, equivalence_arriere(eq))
    return N.generalisation("x", membre)


def existe_ensemble_universel(fam="Fam"):
    """⊢ (∃X)(∀x)(x ∈ X).   CLOS — la NÉGATION de `pas_ensemble_universel`."""
    inner = pourtout("x", appartient(var("x"), var("X")))
    U = E.inter_famille(var(fam), E.VIDE)
    return N.modus_ponens(ensemble_universel_par_inter_vide(fam),
                          N.s5(inner, U, "X"))


def main():
    inner = pourtout("x", appartient(var("x"), var("X")))
    cible = existe("X", inner)

    # Contrôle 1 — le noyau refuse bien une formule qui n'est pas un axiome.
    try:
        N.axiome(E.theorie_ensembles(), appartient(var("a"), var("b")))
        raise SystemExit("CONTROLE 1 ECHOUE : le noyau accepte un non-axiome !")
    except ValueError:
        print("controle 1 : le noyau refuse les non-axiomes .......... OK")

    # Contrôle 2 — AXIOME_INTER_FAM est bien l'un des 22.
    ths = E.theorie_ensembles()
    assert E.AXIOME_INTER_FAM in ths.axiomes and len(ths.axiomes) == 22
    print("controle 2 : AXIOME_INTER_FAM parmi les 22 axiomes ...... OK")

    pos = existe_ensemble_universel()
    neg = pas_ensemble_universel()
    assert pos.conclusion == cible and pos.est_clos
    assert neg.conclusion == non(cible) and neg.est_clos

    print()
    print("  |-  (exists X)(forall x)(x in X)      clos=%s hyps=%d" % (pos.est_clos, len(pos.hypotheses)))
    print("  |- non (exists X)(forall x)(x in X)   clos=%s hyps=%d" % (neg.est_clos, len(neg.hypotheses)))
    print()
    print("=> theorie_ensembles() est CONTRADICTOIRE (A et non-A, tous deux clos).")
    print("   Cause : AXIOME_INTER_FAM pose sans la restriction I != vide.")
    print("   Correctif : definir l'intersection par selection dans la reunion (Grimm B5).")


if __name__ == "__main__":
    main()
