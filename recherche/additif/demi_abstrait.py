# -*- coding: utf-8 -*-
"""LA MOITIÉ SUFFIT — pour TOUT ensemble additif, pas seulement les premiers.

🎯 ⊢ (∀k)[ Fini k ⇒ ( rencontre_S(2k) ⟺ (∃m)( m ∈ P₂ₖ ∩ Q₂ₖ ∧ m ≤ k ) ) ]

Suite de `crible_abstrait`. La symétrie y montrait que les solutions vont par
paires ; ici on en tire que **l'une des deux tombe dans la première moitié**.

CE QUE CE MODULE AJOUTE À LA THÈSE. Le demi-intervalle
(`recherche/goldbach/demi.py`) est déjà, dans sa forme arithmétique, sans
aucun nombre premier : « d'une paire sommant à `b`, l'un des deux est `≤ b/2` »
ne parle que de cardinaux finis. Ce qui restait à vérifier, c'est que
l'ASSEMBLAGE — symétrie + demi-intervalle ⟹ restriction — ne réintroduit pas
d'arithmétique. Il n'en réintroduit pas : `S` reste un paramètre.

Conclusion, pour la carte : **des quatre grandes réductions certifiées de
Goldbach (composés, crible, symétrie, demi-intervalle), aucune ne distingue
les nombres premiers d'un ensemble sans structure.**

⚠️ HISTORIQUE DE CETTE PHRASE — elle a été FAUSSE pendant une semaine. Écrite
ici le 12 août, elle annonçait QUATRE réductions alors que `recherche/additif/`
n'en établissait que DEUX : la symétrie (`crible_abstrait`) et le
demi-intervalle (ce module). Ni la forme crible ni la réduction aux composés
n'existaient sous forme paramétrique. L'écart a été trouvé le 19 août en
relisant le code contre notre propre prose, à l'occasion de la rédaction de
l'article A3, et refermé le jour même par `equivalence_abstraite`. La phrase
est vraie depuis — et c'est `equivalence_abstraite`, pas ce module-ci, qui
porte les deux réductions manquantes. *Aucun test n'aurait attrapé ça : le
noyau garantit la soundness, jamais la fidélité d'un commentaire.*

⚠️ ON TRAVAILLE SUR `b = 2k`, et c'est un choix assumé. Pour un `b` QUELCONQUE
la conclusion s'écrirait `m + m ≤ b` (les cardinaux n'ont pas de division par
deux), et le lemme arithmétique correspondant reste à démontrer — il demande
la monotonie de la somme sous une forme que le dépôt n'expose pas telle quelle.
En restant sur `b = k + k`, on réutilise `demi_intervalle`, déjà clos, et la
thèse est établie sans dette : c'est le PARAMÈTRE `S` qui est en jeu ici, pas
la généralité de la borne.

⚠️ `demi_intervalle` est importé depuis `recherche/goldbach/demi.py` pour des
raisons historiques — c'est là qu'il a été démontré. Il ne contient AUCUNE
primalité : c'est un énoncé sur les cardinaux finis. Sa place logique est dans
ce dossier-ci ou dans `outils_ia/arithmetique/` ; le déplacement est une dette
consignée, pas un oubli.

[CLOS au sens du noyau, SOUS les 2 axiomes de la théorie additive.]
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    appartient, egal, et, existe, impl, ou, pourtout, var,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import (
    noyau_abrege as N,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    cas, conjonction_elim_droite, conjonction_elim_gauche, conjonction_intro,
    instancie,
)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import (
    existe_elimination,
)
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_recollement_somme.ensembles_somme_disjointe import (
    somme_cardinale_binaire as SC,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    inf_egal_card,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (
    est_fini,
)
from recherche.additif.crible_abstrait import (
    LIANT_B, LIANT_M, LIANT_PARTENAIRE, appartenance, elements_bornes,
    membre_P, miroir_additif, symetrie_additive,
)


def rencontre_sur(tb, m=LIANT_M):
    """(∃m)( m ∈ P_b ∧ m ∈ Q_b ) pour un TERME `b` quelconque."""
    vm = var(m)
    return existe(m, et(appartient(vm, elements_bornes(tb)),
                        appartient(vm, miroir_additif(tb))))

_mp = N.modus_ponens
_cg, _cd = conjonction_elim_gauche, conjonction_elim_droite


def rencontre_demi(b=LIANT_B, m=LIANT_M):
    """(∃m)( ( m ∈ P₂ₖ ∧ m ∈ Q₂ₖ ) ∧ m ≤ k )  — la rencontre dans la MOITIÉ.

    `b` nomme ici le `k` dont on prend le double : la borne des ensembles est
    `2k`, et le témoin est cherché sous `k`."""
    vk, vm = var(b), var(m)
    vb = SC(vk, vk)
    return existe(m, et(et(appartient(vm, elements_bornes(vb)),
                           appartient(vm, miroir_additif(vb))),
                        inf_egal_card(vm, vk)))


def _fini_du_membre(S, vb, vx, th_in_P):
    """De `x ∈ P_b` tirer `Fini x` — la garde vit dans l'axiome de P."""
    return _cg(_cg(_mp(th_in_P, _cg(membre_P(S, vb, vx)))))


def restriction_a_la_moitie(S=appartenance, b=LIANT_B, m=LIANT_M):
    """🎯 ⊢ (∀b)[ Fini b ⇒ ( rencontre_S(b) ⇒ rencontre_demi_S(b) ) ].

    Assemblage : la symétrie donne le partenaire `m'` avec `b = m + m'` ; le
    demi-intervalle (arithmétique pure) donne `m + m ≤ b` OU `m' + m' ≤ b`.
    Chaque branche fournit son témoin.

    `S` n'est jamais ouvert — c'est tout le propos."""
    from recherche.goldbach.demi import demi_intervalle

    vk, vm = var(b), var(m)
    vb = SC(vk, vk)                                    # b := 2k
    vmp = var(LIANT_PARTENAIRE)
    CIBLE = rencontre_demi(b, m)
    mat_cible = CIBLE.sous[0]

    h_fini_b = N.assume(est_fini(vk))
    mat_renc = et(appartient(vm, elements_bornes(vb)),
                  appartient(vm, miroir_additif(vb)))
    hm = N.assume(mat_renc)
    fini_m = _fini_du_membre(S, vb, vm, _cg(hm))

    sym = instancie(instancie(symetrie_additive(S, b, m), vb), vm)
    ex_mp = _mp(hm, sym)
    matp = ex_mp.conclusion.sous[0]
    hmp = N.assume(matp)
    mp_in_PQ, somme = _cg(hmp), _cd(hmp)
    fini_mp = _fini_du_membre(S, vb, vmp, _cg(mp_in_PQ))

    #   ⚠️ ORDRE D'INSTANCIATION : le lemme généralise m' EN DERNIER, c'est
    #   donc le ∀ le plus EXTERNE — on l'instancie en premier.
    di = instancie(instancie(instancie(demi_intervalle(), vmp), vm), vk)
    ou_th = _mp(conjonction_intro(conjonction_intro(
        conjonction_intro(h_fini_b, fini_m), fini_mp), somme), di)

    LE_M, LE_MP = inf_egal_card(vm, vk), inf_egal_card(vmp, vk)
    br1 = N.loi_deduction(LE_M, _mp(conjonction_intro(hm, N.assume(LE_M)),
                                    N.s5(mat_cible, vm, m)))
    br2 = N.loi_deduction(LE_MP, _mp(conjonction_intro(mp_in_PQ,
                                                       N.assume(LE_MP)),
                                     N.s5(mat_cible, vmp, m)))
    concl = cas(ou_th, br1, br2)
    assert concl.conclusion == CIBLE, "restriction abstraite : cible"

    sous_m = _mp(ex_mp, existe_elimination(N.loi_deduction(matp, concl),
                                           LIANT_PARTENAIRE))
    imp = existe_elimination(N.loi_deduction(mat_renc, sous_m), m)
    th = N.generalisation(b, N.loi_deduction(est_fini(vk), imp))
    assert th.est_clos and not th.hypotheses, "restriction abstraite : non clos"
    return th


def moitie_implique_rencontre(b=LIANT_B, m=LIANT_M):
    """⊢ (∀k)( rencontre_demi_S(k) ⇒ rencontre_S(2k) ) — l'affaiblissement.

    On oublie la borne. Avec `restriction_a_la_moitie`, c'est l'ÉQUIVALENCE."""
    vk, vm = var(b), var(m)
    vb = SC(vk, vk)
    src = rencontre_demi(b, m)
    mat_src = src.sous[0]
    h = N.assume(mat_src)
    mat_renc = et(appartient(vm, elements_bornes(vb)),
                  appartient(vm, miroir_additif(vb)))
    ex = _mp(_cg(h), N.s5(mat_renc, vm, m))
    assert ex.conclusion == rencontre_sur(vb, m), "moitié ⇒ rencontre : cible"
    th = N.generalisation(b, existe_elimination(
        N.loi_deduction(mat_src, ex), m))
    assert th.est_clos and not th.hypotheses, "moitié ⇒ rencontre : non clos"
    return th


__all__ = ["rencontre_demi", "restriction_a_la_moitie",
           "moitie_implique_rencontre"]
