"""Lemmes DÉCOUVERTS PAR LA MACHINE (conjectureur, 6 août 2026) — redérivés, nommés.

────────────────────────────────────────────────────────────────────────────────
PROVENANCE — ce que ces quatre lemmes ont de particulier.

Ils n'ont pas été écrits par un humain : le conjectureur (transitivité +
détachement σ, noyau seul juge — ev.275-276) les a trouvés en chaînant les
implications universelles de l'îlot Goldbach, parmi 60 théorèmes certifiés en
trois tours d'itération.  Ce sont exactement les « lemmes de colle » que la
campagne Goldbach avait dû écrire À LA MAIN (les chaînes fic_t) : la machine a
retrouvé seule la glu dont ses preuves avaient eu besoin.

Ils sont promus ici parce qu'ils SERVENT — chaque futur chantier arithmétique
refera ces trois pas ; autant qu'ils portent un nom.  La redérivation suit les
mêmes chaînages que la découverte, en pas de noyau explicites, et chaque
conclusion est vérifiée à la construction.

    fini_somme_cardinal(a, b)     ⊢ (Fini a et Fini b) ⇒ est_cardinal(a+b)
    fini_somme_successeur(a, b)   ⊢ (Fini a et Fini b) ⇒ Fini((a+b)+1)
    prop2_sous_fini(a, b, c)      ⊢ Fini a ⇒ ( b = a+c ⇒ a ≤ b )
    fini_descendant_sous_fini(a)  ⊢ Fini a ⇒ (∀x)( (a ≤ x et Fini x) ⇒ Fini a )

⚠️ COÛT : les quatre reposent sur `somme_binaire_entier` (Prop. 1 §III.5.1) ou le
fini-descendant, qui paient la machinerie de récurrence C61 (~200 s au premier
appel d'un process frais).  Les tests portent le marqueur `slow`.

INVARIANT : primitives du noyau uniquement ; theorie_ensembles() reste à 22.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, egal, et, impl, pourtout,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    instancie,
)
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_recollement_somme.ensembles_somme_disjointe import (
    somme_cardinale_binaire as SC,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    est_cardinal, inf_egal_card,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (
    est_fini, successeur,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_fini_successeur import (
    fini_implique_fini_successeur,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_1_somme_produit_entiers.ensembles_calcul_entiers_props import (
    prop2_somme_implique_inf_egal,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_1_somme_produit_entiers.ensembles_combinatoire_iii5 import (
    somme_binaire_entier,
)

from outils_ia.arithmetique.machine_num import fic_t

mp = N.modus_ponens

_FIFS_GEN = None


def _fifs_t(t):
    """⊢ Fini(T) ⇒ Fini(T+1), pour un TERME T (généralisé une fois, cf. machine_num)."""
    global _FIFS_GEN
    if _FIFS_GEN is None:
        base = fini_implique_fini_successeur("alcj")
        assert base.est_clos
        _FIFS_GEN = N.generalisation("alcj", base)
    return instancie(_FIFS_GEN, t)


def fini_somme_cardinal(a="a", b="b"):
    """⊢ (Fini a et Fini b) ⇒ est_cardinal(a+b).      [découverte machine, transit.σ]

    Chaînage de la découverte : somme_binaire_entier puis fini_implique_cardinal
    instancié au terme a+b."""
    va, vb = var(a), var(b)
    ab = SC(va, vb)
    h = N.assume(et(est_fini(va), est_fini(vb)))
    fini_ab = mp(h, somme_binaire_entier(a, b))            # Fini(a+b)
    r = N.loi_deduction(et(est_fini(va), est_fini(vb)), mp(fini_ab, fic_t(ab)))
    assert r.conclusion == impl(et(est_fini(va), est_fini(vb)), est_cardinal(ab))
    assert r.est_clos
    return r


def fini_somme_successeur(a="a", b="b"):
    """⊢ (Fini a et Fini b) ⇒ Fini((a+b)+1).          [découverte machine, transit.σ]"""
    va, vb = var(a), var(b)
    ab = SC(va, vb)
    h = N.assume(et(est_fini(va), est_fini(vb)))
    fini_ab = mp(h, somme_binaire_entier(a, b))
    r = N.loi_deduction(et(est_fini(va), est_fini(vb)), mp(fini_ab, _fifs_t(ab)))
    assert r.conclusion == impl(et(est_fini(va), est_fini(vb)),
                                est_fini(successeur(ab)))
    assert r.est_clos
    return r


def prop2_sous_fini(a="a", b="b", c="c"):
    """⊢ Fini a ⇒ ( b = a+c ⇒ a ≤ b ).                [découverte machine, transit.]

    La Proposition 2 §III.5.2 demande est_cardinal(a) ; sous Fini a, cette garde
    est GRATUITE (fini_implique_cardinal).  C'est la forme que les chantiers
    consomment.

    ⚠️ PIÈGE MESURÉ : la DOCSTRING de `prop2_somme_implique_inf_egal` annonce un
    antécédent CONJONCTIF « (est_cardinal a et b = a+c) ⇒ … » ; son CODE rend la
    forme CURRYFIÉE est_cardinal a ⇒ ((b = a+c) ⇒ a ≤ b) — deux loi_deduction
    imbriquées.  Assembler la conjonction fait échouer le modus ponens ; il faut
    ENCHAÎNER.  La prose n'est pas un contrat, le code l'est."""
    va, vb, vc = var(a), var(b), var(c)
    h_fini = N.assume(est_fini(va))
    card_a = mp(h_fini, fic_t(va))                          # est_cardinal(a)
    inner = mp(card_a, prop2_somme_implique_inf_egal(a, b, c))   # (b=a+c) ⇒ a≤b
    r = N.loi_deduction(est_fini(va), inner)
    assert r.conclusion == impl(est_fini(va),
                                impl(egal(vb, SC(va, vc)), inf_egal_card(va, vb)))
    assert r.est_clos
    return r


def fini_descendant_sous_fini(a="a"):
    """⊢ Fini a ⇒ (∀x)( (a ≤ x et Fini x) ⇒ Fini a ). [découverte machine, transit.]

    Le fini-descendant (goldbach_reduction.fini_downward_clos) est gardé par
    est_cardinal(a) ; sous Fini a la garde tombe.  Version que les preuves à
    hypothèse de finitude consomment sans détour."""
    from outils_ia.conjectures.goldbach_reduction import fini_downward_clos
    va = var(a)
    h_fini = N.assume(est_fini(va))
    card_a = mp(h_fini, fic_t(va))
    tous_x = mp(card_a, instancie(fini_downward_clos(), va))
    r = N.loi_deduction(est_fini(va), tous_x)
    assert r.conclusion.tag == "non" or r.est_clos          # forme : impl vers (∀x)…
    assert r.est_clos
    corps = impl(et(inf_egal_card(va, var("x")), est_fini(var("x"))), est_fini(va))
    assert r.conclusion == impl(est_fini(va), pourtout("x", corps))
    return r


# Compagnes du gate (7 août 2026) : énoncés par combinateurs, jamais en re-prouvant.
# Les quatre prouveurs ont tous leurs paramètres PAR DÉFAUT → le chemin zéro-arg
# du gate s'applique tel quel ; il ne manquait que la cible.
def fini_somme_cardinal_cible():
    """Énoncé visé : (Fini a et Fini b) ⇒ est_cardinal(a+b)."""
    va, vb = var("a"), var("b")
    return impl(et(est_fini(va), est_fini(vb)), est_cardinal(SC(va, vb)))


def fini_somme_successeur_cible():
    """Énoncé visé : (Fini a et Fini b) ⇒ Fini((a+b)+1)."""
    va, vb = var("a"), var("b")
    return impl(et(est_fini(va), est_fini(vb)), est_fini(successeur(SC(va, vb))))


def prop2_sous_fini_cible():
    """Énoncé visé : Fini a ⇒ ( b = a+c ⇒ a ≤ b )."""
    va, vb, vc = var("a"), var("b"), var("c")
    return impl(est_fini(va), impl(egal(vb, SC(va, vc)), inf_egal_card(va, vb)))


def fini_descendant_sous_fini_cible():
    """Énoncé visé : Fini a ⇒ (∀x)( (a ≤ x et Fini x) ⇒ Fini a )."""
    va = var("a")
    corps = impl(et(inf_egal_card(va, var("x")), est_fini(var("x"))), est_fini(va))
    return impl(est_fini(va), pourtout("x", corps))


__all__ = ["fini_somme_cardinal", "fini_somme_successeur", "prop2_sous_fini",
           "fini_descendant_sous_fini",
           "fini_somme_cardinal_cible", "fini_somme_successeur_cible",
           "prop2_sous_fini_cible", "fini_descendant_sous_fini_cible"]
