# -*- coding: utf-8 -*-
"""L'ÉQUIVALENCE CRIBLE, ET LA BRANCHE FACILE — sans aucune arithmétique.

Ce module ferme l'écart signalé par l'article A3 (`article/goldbach/`, §5.3).

🎯 CE QUI RESTAIT À MESURER. `crible_abstrait` et `demi_abstrait` avaient montré
que DEUX des quatre grandes réductions de la carte Goldbach — la symétrie et le
demi-intervalle — valent pour un prédicat `S` quelconque. Les deux autres — la
**forme crible** (GG19) et la **réduction aux composés** (GG22) — étaient
annoncées sans contenu arithmétique dans `docs/articles/CARTE_GOLDBACH.md` §12,
mais **rien ne l'établissait en code**. On le fait ici.

    GG19 abstrait   ⊢ (∀b)[ rencontre_S(b)  ⟺  (∃p)(∃q)( S⁺(p) ∧ S⁺(q) ∧ b = p+q ) ]
    GG22 abstrait   ⊢ (∀k)[ S⁺(k)  ⇒  rencontre_S(k+k) ]

avec `S⁺(t) := Fini t ∧ S(t)` — la garde de finitude, qui est la correction du
défaut de fidélité de `est_premier` (cf. `recherche/goldbach/audit_fidelite.py`)
et qui, elle, ne dépend pas non plus de `S`.

CE QUE LE PORTAGE APPREND. Il est **mécanique** : les preuves concrètes de
`recherche/goldbach/crible.py` et `synthese.py` ne se servent de la primalité
QUE comme d'un conjoint opaque, transporté d'un bout à l'autre sans jamais être
ouvert. Tout le travail réel y est de l'arithmétique cardinale sans premiers —
`prop2_sous_fini` pour `p ≤ b`, l'appartenance à `[0,b]`, la réflexivité pour le
témoin du miroir. Le portage ne demande donc aucune idée neuve, et c'est
précisément le résultat : *il n'y avait rien d'arithmétique à porter.*

⚠️ GÉNÉRALITÉ GAGNÉE AU PASSAGE. La version concrète travaille sur `b = 2k`
parce que `decomposition_gardee` est écrite sur `2k` ; aucune de ses étapes
n'utilise le fait que `b` est un double. L'équivalence abstraite est donc
énoncée sur un `b` QUELCONQUE. Seul GG22 a besoin de `b = k + k`, et pour une
raison précise : le témoin `m := k` doit être dans le miroir, ce qui exige
`k + k = k + k` — une réflexivité, la seule chose que « double » apporte.

⚠️ AUCUN PONT D'HABIT α, comme dans `crible_abstrait`. La version concrète de
GG22 doit traduire entre deux graphies de `est_premier` (`premier₁`/`premier₂`)
imposées par l'énoncé du dépôt ; avec un prédicat unique il n'y a rien à
traduire. Le pont concret était un artefact de notation, pas une étape.

[CLOS au sens du noyau, SOUS les 2 axiomes de la théorie additive.]
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    appartient, egal, et, existe, subst_f, var,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import (
    noyau_abrege as N,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_elim_droite, conjonction_elim_gauche, conjonction_intro,
    instancie,
)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import (
    existe_elimination,
)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import (
    ensembles_abrege as E,
)
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_recollement_somme.ensembles_somme_disjointe import (
    somme_cardinale_binaire as SC,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    est_cardinal,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (
    est_fini,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_intervalles_comptage.ensembles_prop5_intervalle import (
    membre_intervalle_entiers_t,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_1_n_objet_existence.ensembles_N_collectivise import (
    zero_inf_egal_cardinal,
)
from outils_ia.arithmetique.lemmes_conjectures import prop2_sous_fini
from outils_ia.arithmetique.machine_num import NUM, fic_t
from recherche.additif.crible_abstrait import (
    AXIOMES_ADDITIF, LIANT_B, LIANT_M, appartenance, elements_bornes, membre_P,
    membre_Q, miroir_additif,
)

_mp = N.modus_ponens
_cg, _cd = conjonction_elim_gauche, conjonction_elim_droite
ZERO = NUM(0)

#: liants FIXÉS de ce module — frais vis-à-vis de `crible_abstrait`
LIANT_P, LIANT_Q, LIANT_K = "pequ", "qequ", "kequ"


def garde(S, t):
    """`S⁺(t) := Fini t ∧ S(t)` — l'élément GARDÉ.

    Exactement la forme de `premier_ent` dans la version concrète, avec la
    primalité remplacée par le paramètre. La garde `Fini` n'est pas de la
    prudence : sans elle, `prop2_sous_fini` ne s'applique pas et le sens ⇒
    ci-dessous n'est pas démontrable."""
    return et(est_fini(t), S(t))


def decomposition_abstraite(S, tb, p=LIANT_P, q=LIANT_Q):
    """`DEC_S(b) := (∃p)(∃q)( ( S⁺(p) ∧ S⁺(q) ) ∧ b = p + q )`.

    « `b` est somme de deux éléments gardés de `S` ». Pour `S = est_premier`
    et `b = 2k`, c'est mot pour mot `crible.decomposition_gardee`."""
    vp, vq = var(p), var(q)
    return existe(p, existe(q, et(et(garde(S, vp), garde(S, vq)),
                                  egal(tb, SC(vp, vq)))))


def rencontre_sur(tb, m=LIANT_M):
    """`(∃m)( m ∈ P_b ∧ m ∈ Q_b )` pour un TERME `b`.

    Même formule que `demi_abstrait.rencontre_sur` ; redéfinie ici pour ne pas
    faire dépendre l'équivalence (plus primitive) du demi-intervalle (qui la
    suppose). Un test verrouille l'égalité des deux."""
    vm = var(m)
    return existe(m, et(appartient(vm, elements_bornes(tb)),
                        appartient(vm, miroir_additif(tb))))


def _place_dans_P(S, tb, vx, garde_x, somme):
    """De `S⁺(x)` et `b = x + ...` conclure `x ∈ P_b`.

    LE SEUL VRAI TRAVAIL des deux sens, et il est purement cardinal :
    `prop2_sous_fini` (curryfié) donne `x ≤ b` depuis `Fini x` et la somme ;
    `fic_t` et `zero_inf_egal_cardinal` placent `x` dans `[0,b]`. `S` n'y
    intervient que porté par `garde_x`."""
    fini_x = _cg(garde_x)
    p2 = instancie(instancie(instancie(
        N.generalisation("a", N.generalisation("b", N.generalisation(
            "c", prop2_sous_fini("a", "b", "c")))), vx), tb), somme[1])
    le_x = _mp(somme[0], _mp(fini_x, p2))
    card_x = _mp(fini_x, fic_t(vx))
    zero_le_x = _mp(card_x, N.loi_deduction(est_cardinal(vx),
                                            zero_inf_egal_cardinal(vx)))
    x_in_int = _mp(conjonction_intro(conjonction_intro(card_x, zero_le_x), le_x),
                   _cd(membre_intervalle_entiers_t(ZERO, tb, vx)))
    return _mp(conjonction_intro(garde_x, x_in_int), _cd(membre_P(S, tb, vx)))


def _place_dans_Q(S, tb, vx, temoin, fourni):
    """De la matrice fournie conclure `x ∈ Q_b`, en LISANT le liant du noyau.

    ⚠️ `temoin` est le `y` INTERNE du miroir, et il est distinct de `x` : dans
    l'équivalence c'est l'autre sommant (`y := q`), dans GG22 c'est `x`
    lui-même (`y := k`, car `2k = k + k`). Les confondre fait échouer
    l'assertion ci-dessous — c'est arrivé, et c'est elle qui l'a attrapé.

    ⚠️ PIÈGE DES LIANTS : ne jamais reconstruire la matrice du `∃` du miroir —
    le noyau a pu α-renommer son liant. On lit celui qu'il a produit, et on
    vérifie que ce qu'on fournit lui est identique."""
    impQ = _cd(membre_Q(S, tb, vx))
    exY = impQ.conclusion.sous[0].sous[0]
    assert getattr(exY, "tag", None) == "exists", "miroir : forme du ∃ inattendue"
    assert fourni.conclusion == subst_f(temoin, exY.lieur, exY.sous[0]), \
        "miroir : matrice fournie ≠ matrice attendue"
    return _mp(_mp(fourni, N.s5(exY.sous[0], temoin, exY.lieur)), impQ)


def _clot_la_rencontre(tb, vx, th_in_P, th_in_Q):
    """De `x ∈ P_b` et `x ∈ Q_b` conclure `rencontre_S(b)` — `s5` sur `x`."""
    vm = var(LIANT_M)
    mat = et(appartient(vm, elements_bornes(tb)),
             appartient(vm, miroir_additif(tb)))
    th = _mp(conjonction_intro(th_in_P, th_in_Q), N.s5(mat, vx, LIANT_M))
    assert th.conclusion == rencontre_sur(tb), "rencontre : forme inattendue"
    return th


def rencontre_implique_decomposition(S=appartenance, b=LIANT_B):
    """🎯 ⊢ (∀b)( rencontre_S(b) ⇒ DEC_S(b) ).   [CLOS, 2 axiomes ad hoc]

    Sens (⇐), le gratuit. Sous un point `m` de la rencontre : `S⁺(m)` sort de
    `P_b` ; le témoin `y` (gardé, `b = m + y`) sort de `Q_b` ; la route-témoin
    `s5` ×2 referme le double `∃`, `existe_elimination` décharge `y` puis `m`.
    Aucune propriété de `S` n'est invoquée : les deux gardes sont recopiées."""
    vb, vm = var(b), var(LIANT_M)
    DEC = decomposition_abstraite(S, vb)
    inner = DEC.sous[0]

    hm = N.assume(et(appartient(vm, elements_bornes(vb)),
                     appartient(vm, miroir_additif(vb))))
    garde_m = _cg(_mp(_cg(hm), _cg(membre_P(S, vb, vm))))
    corps_Q = _mp(_cd(hm), _cg(membre_Q(S, vb, vm)))

    exY = corps_Q.conclusion
    assert exY.tag == "exists", "crible abstrait : corps du miroir n'est pas un ∃"
    ly, maty = exY.lieur, exY.sous[0]
    hy = N.assume(maty)

    mat_my = subst_f(vm, LIANT_P, inner).sous[0]
    c_b = conjonction_intro(conjonction_intro(garde_m, _cg(hy)), _cd(hy))
    assert c_b.conclusion == subst_f(var(ly), LIANT_Q, mat_my), \
        "crible abstrait : matrice reconstruite ≠ matrice substituée"
    dec_y = _mp(_mp(c_b, N.s5(mat_my, var(ly), LIANT_Q)),
                N.s5(inner, vm, LIANT_P))
    assert dec_y.conclusion == DEC, "crible abstrait (⇐) : ≠ DEC"
    dec_m = _mp(corps_Q, existe_elimination(N.loi_deduction(maty, dec_y), ly))
    th = N.generalisation(
        b, existe_elimination(N.loi_deduction(hm.conclusion, dec_m), LIANT_M))
    assert th.est_clos and not th.hypotheses, "crible abstrait (⇐) non clos"
    return th


def decomposition_implique_rencontre(S=appartenance, b=LIANT_B):
    """🎯 ⊢ (∀b)( DEC_S(b) ⇒ rencontre_S(b) ).   [CLOS, 2 axiomes ad hoc]

    Sens (⇒), CELUI QUI CONSOMME LA GARDE. De `b = p + q` et `Fini p`,
    `prop2_sous_fini` donne `p ≤ b`, donc `p ∈ [0,b]`, donc `p ∈ P_b` ; et
    `p ∈ Q_b` avec le témoin interne `q`. Sans `Fini p`, aucune de ces étapes
    n'est disponible — c'est exactement le défaut de fidélité de la version
    concrète (`audit_fidelite.py`), ici évité par construction."""
    vb, vp, vq = var(b), var(LIANT_P), var(LIANT_Q)
    DEC = decomposition_abstraite(S, vb)
    inner = DEC.sous[0]
    mat = inner.sous[0]

    h = N.assume(mat)
    garde_p = _cg(_cg(h))
    garde_q = _cd(_cg(h))
    somme = _cd(h)

    p_in_P = _place_dans_P(S, vb, vp, garde_p, (somme, vq))
    p_in_Q = _place_dans_Q(S, vb, vp, vq, conjonction_intro(garde_q, somme))
    ex_m = _clot_la_rencontre(vb, vp, p_in_P, p_in_Q)

    imp_q = existe_elimination(N.loi_deduction(mat, ex_m), LIANT_Q)
    imp_p = existe_elimination(
        N.loi_deduction(inner, _mp(N.assume(inner), imp_q)), LIANT_P)
    th = N.generalisation(b, imp_p)
    assert th.est_clos and not th.hypotheses, "crible abstrait (⇒) non clos"
    return th


def equivalence_abstraite(S=appartenance, b=LIANT_B):
    """🎯🎯 GG19 ABSTRAIT — les deux sens, tous deux clos.

    Pour `S = est_premier` c'est, à la garde près, `crible.equivalence_crible`.
    Pour un `S` opaque, c'est le même théorème : la forme crible ne contient
    aucune arithmétique."""
    return (rencontre_implique_decomposition(S, b),
            decomposition_implique_rencontre(S, b))


def rencontre_des_elements(S=appartenance, k=LIANT_K):
    """🎯 GG22 ABSTRAIT — ⊢ (∀k)( S⁺(k) ⇒ rencontre_S(k+k) ).

    LA BRANCHE FACILE, et la mesure la plus nette du module : dans la version
    concrète, « si `k` est premier alors `2k` se décompose » ; ici, « si `k`
    est dans `S` alors `k+k` est somme de deux éléments de `S` ». La primalité
    n'y jouait aucun rôle — seulement l'appartenance.

    Le témoin est `m := k` : il est dans `P₂ₖ` (gardé, et `k ≤ k+k` par
    `prop2_sous_fini`), et dans `Q₂ₖ` avec le témoin interne `y := k`, puisque
    `k + k = k + k` — une réflexivité. C'est la SEULE chose que le fait d'être
    un double apporte, et c'est pourquoi GG22 est le seul énoncé de ce module
    qui ne vaille pas pour un `b` quelconque."""
    vk = var(k)
    M = SC(vk, vk)
    HYP = garde(S, vk)
    h = N.assume(HYP)

    k_in_P = _place_dans_P(S, M, vk, h, (N.reflexivite(M), vk))
    k_in_Q = _place_dans_Q(S, M, vk, vk, conjonction_intro(h, N.reflexivite(M)))
    ex_m = _clot_la_rencontre(M, vk, k_in_P, k_in_Q)

    th = N.generalisation(k, N.loi_deduction(HYP, ex_m))
    assert th.est_clos and not th.hypotheses, "GG22 abstrait : non clos"
    return th


__all__ = [
    "AXIOMES_ADDITIF", "LIANT_P", "LIANT_Q", "LIANT_K",
    "garde", "decomposition_abstraite", "rencontre_sur",
    "rencontre_implique_decomposition", "decomposition_implique_rencontre",
    "equivalence_abstraite", "rencontre_des_elements",
]
