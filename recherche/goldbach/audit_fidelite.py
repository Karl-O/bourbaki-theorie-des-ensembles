# -*- coding: utf-8 -*-
"""Goldbach — L'AUDIT DE FIDÉLITÉ : ce que `est_premier` ne dit pas.

CE MODULE NE DÉMONTRE RIEN SUR GOLDBACH. Il démontre un DÉFAUT DE L'ÉNONCÉ —
et c'est pour cela qu'il compte. Le noyau garantit la *soundness* (aucun faux
théorème) mais pas la *fidélité* (l'énoncé formalisé == celui qu'on croit
écrire). Ici la fidélité était en défaut, et la machine l'a établi.

🎯 LE DÉFAUT, certifié par `indivisible_implique_premier` :

    ⊢ ( p ≠ 1  ∧  (∀d) ¬ divise_propre(d, p) )  ⇒  est_premier(p)

Autrement dit : **tout objet ≠ 1 que rien ne divise est « premier »** au sens
du dépôt. Or `divise_propre(d, p)` exige `p = Card(d × q)` : un `p` qui n'est
PAS un cardinal n'est divisible par rien du tout, la clause universelle de
`est_premier` est donc vraie à vide, et « premier » s'y réduit à `p ≠ 1`.

CONSÉQUENCE SUR LA CONJECTURE. `goldbach()` quantifie sur des témoins `p, q`
sans exiger qu'ils soient des entiers. L'énoncé formalisé est donc **plus
faible** que la conjecture : il pourrait être satisfait par des témoins qui
n'ont aucun sens arithmétique. La garde `est_fini` porte, dans `est_premier`,
sur le DIVISEUR `d` — jamais sur `p`.

LA CORRECTION est `premier_ent(p) := Fini(p) ∧ est_premier(p)`, adoptée par
`crible`. `premier_ent_deux` établit qu'elle ne coûte RIEN sur les numéraux :
la garde est gratuite là où l'on sait déjà calculer.

⚠️ SENS DE LECTURE. Ce module ne dit pas que le dépôt est faux — il dit qu'un
énoncé était plus permissif que son nom. Le sens `DEC_ent ⇒ DEP` est démontré
(`synthese.gardee_implique_depot`) ; **la réciproque ne l'est pas**, et c'est
précisément ce que l'audit explique.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    egal, et, impl, non, pourtout, var,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import (
    noyau_abrege as N,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_elim_droite, conjonction_elim_gauche, conjonction_intro,
    instancie,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.props_restantes.ensembles_divisibilite_propre import (
    divise_propre,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (
    est_fini,
)
from outils_ia.arithmetique.machine_num import NUM, fini_num
from outils_ia.conjectures.goldbach import _ou, est_premier, un
#   ⚠️ `est_premier_num` vit sous `conjectures`, JAMAIS sous `arithmetique`
#   (`outils_ia.arithmetique.primalite` n'existe pas — piège mesuré, masqué
#   dans les scripts d'origine par un try/except qui avalait l'erreur).
from outils_ia.conjectures.primalite import est_premier_num

_mp = N.modus_ponens


def indivisible_implique_premier(p="paud", d="dgb", q="qgb"):
    """🎯 ⊢ ( p ≠ 1 ∧ (∀d)¬divise_propre(d, p) ) ⇒ est_premier(p).  [CLOS]

    LE THÉORÈME DE DÉFAUT. `p` est LIBRE : l'énoncé vaut pour n'importe quel
    objet, entier ou non — c'est tout le propos.

    ROUTE. Sous l'hypothèse, la clause `(∀d)( (Fini d ∧ d|p) ⇒ (d=1 ∨ d=p) )`
    se démontre **par l'absurde à antécédent vide** : de `d | p` et de
    `¬(d | p)` on tire n'importe quoi. Le noyau n'a pas d'ex falso général —
    on passe par le schéma S2 (`¬D ⇒ (¬D ∨ ccl)`), en remarquant que
    `¬D ∨ ccl` **est** `D ⇒ ccl` par définition de l'implication.

    ⚠️ `_ou` du module Goldbach vaut `¬(¬a ∧ ¬b)` et n'est PAS le `ou`
    primitif : la conclusion de `est_premier` est bâtie avec `_ou`, la
    reconstruire autrement produit une formule différente et casse le MP."""
    vp, vd = var(p), var(d)
    cible = est_premier(vp, d=d, q=q)

    NODIV = pourtout(d, non(divise_propre(vd, vp, q=q)))
    HYP = et(non(egal(vp, un())), NODIV)
    h = N.assume(HYP)
    hne, hnd = conjonction_elim_gauche(h), conjonction_elim_droite(h)

    #   RECONSTRUCTION VÉRIFIÉE : l'extraction par `.sous` est fragile ici
    #   (quatre niveaux) — on reconstruit et l'on exige l'égalité.
    ante = et(est_fini(vd), divise_propre(vd, vp, q=q))
    ccl = _ou(egal(vd, un()), egal(vd, vp))
    assert pourtout(d, impl(ante, ccl)) == cible.sous[0].sous[1].sous[0], \
        "audit : la clause reconstruite ≠ celle de est_premier"

    ha = N.assume(ante)
    div_d = conjonction_elim_droite(ha)
    nod_d = instancie(hnd, vd)
    #   S2 : ¬D ⇒ (¬D ∨ ccl) ; et (¬D ∨ ccl) EST (D ⇒ ccl).
    absurde = _mp(div_d, _mp(nod_d, N.s2(non(div_d.conclusion), ccl)))
    corps = N.generalisation(d, N.loi_deduction(ante, absurde))
    th = N.loi_deduction(HYP, conjonction_intro(hne, corps))
    assert th.conclusion == impl(HYP, cible), "audit : conclusion ≠ cible"
    assert th.est_clos and not th.hypotheses, "audit : non clos"
    return th


def premier_ent_deux():
    """⊢ Fini(2) ∧ est_premier(2)   — « la garde ne coûte rien ».  [CLOS]

    NON-RÉGRESSION de la correction. Ajouter la garde `Fini` à l'énoncé ne
    fait rien perdre des acquis numéraux : `premier_ent(2)` se démontre sans
    aucun coût supplémentaire, par simple conjonction de deux théorèmes clos
    du dépôt.

    Ne dit rien sur la conjecture — dit que la correction est indolore."""
    deux = NUM(2)
    th = conjonction_intro(fini_num(2), est_premier_num(2, d="d1", q="q1"))
    assert th.conclusion == et(est_fini(deux),
                               est_premier(deux, d="d1", q="q1")), \
        "garde gratuite : conclusion ≠ premier_ent(2)"
    assert th.est_clos and not th.hypotheses, "garde gratuite : non clos"
    return th


__all__ = ["indivisible_implique_premier", "premier_ent_deux"]
