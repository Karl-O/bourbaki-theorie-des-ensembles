# -*- coding: utf-8 -*-
"""LE CRIBLE ABSTRAIT — ce qui, dans Goldbach, n'est PAS de l'arithmétique.

🎯 LA QUESTION. La campagne Goldbach a produit une carte d'équivalences
certifiées : réduction aux composés, forme crible, symétrie des solutions,
restriction au demi-intervalle. Combien d'arithmétique y a-t-il là-dedans ?

🎯 LA RÉPONSE, et c'est le propos de ce module : **aucune**. Ces résultats ne
parlent pas des nombres premiers. Ils valent pour un ensemble `S` d'entiers
QUELCONQUE, et Goldbach n'en est qu'une instance.

    P_b := { x : Fini x ∧ S(x) ∧ x ∈ [0,b] }        les éléments de S sous b
    Q_b := { x : (∃y)( Fini y ∧ S(y) ∧ b = x + y ) } son miroir additif

    « b est somme de deux éléments de S »  ⟺  P_b rencontre Q_b

Le prédicat `S` est un PARAMÈTRE — une fonction Python `Terme → Formule`. En
lui passant la primalité, on retrouve littéralement les théorèmes de
`recherche/goldbach/` ; en lui passant n'importe quoi d'autre (les carrés, les
cubes, une partie arbitraire), on obtient les mêmes énoncés. « Goldbach en est
une instance » n'est donc pas une affirmation de la prose : c'est une
exécution.

CE QUE ÇA ÉTABLIT, ET POURQUOI C'EST UTILE. Un résultat qui vaut pour tout `S`
ne peut pas distinguer les nombres premiers d'un ensemble sans structure. Il ne
peut donc PAS servir à démontrer Goldbach — et ce n'est pas un défaut de nos
preuves, c'est une propriété de ces réformulations. Cela **délimite** la
conjecture : ce qui est structurel d'un côté, ce qui est arithmétique de
l'autre, avec la frontière tracée en code plutôt qu'à l'estime.

C'est aussi cohérent avec les deux voies déjà refermées par la négative
(`CARTE_GOLDBACH.md` §7 et §8) : le comptage brut et le raisonnement
équationnel échouent tous deux, et pour la même raison — ils ne regardent
jamais *quels* entiers sont dans `S`.

⚠️ UN EFFET DE BORD RÉVÉLATEUR. Dans la version concrète, la symétrie exige un
pont d'habit α (`premier₂ ⇒ premier₁` et retour), parce que `decomposition`
impose deux graphies de `est_premier`. Ici, avec un prédicat UNIQUE, ce pont
**disparaît entièrement**. C'est la preuve que ce pont n'était pas
mathématique : c'était un artefact de notation.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    app, appartient, egal, equiv, et, existe, pourtout, var,
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
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
    composer_egalites, symetrie as _sym_eq,
)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import (
    ensembles_abrege as E,
)
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_recollement_somme.ensembles_somme_disjointe import (
    somme_cardinale_binaire as SC,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_somme.ensembles_arith_somme import (
    somme_cardinale_commutative,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    cardinal, est_cardinal, inf_egal_card,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.ordre_cardinaux.ensembles_cardinaux_props_restantes_ordre import (
    _cardinal_est_son_cardinal,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (
    est_fini,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_1_somme_produit_entiers.ensembles_calcul_entiers_props import (
    inf_egal_somme_droite_binaire,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_intervalles_comptage.ensembles_prop5_intervalle import (
    membre_intervalle_entiers_t,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_1_n_objet_existence.ensembles_N_collectivise import (
    zero_inf_egal_cardinal,
)
from outils_ia.arithmetique.machine_num import NUM, fic_t

_mp = N.modus_ponens
_cg, _cd = conjonction_elim_gauche, conjonction_elim_droite
ZERO = NUM(0)

#: liants du module — frais vis-à-vis de tout ce qui existe ailleurs
LIANT_B, LIANT_M, LIANT_Y = "badd", "madd", "yadd"
LIANT_PARTENAIRE = "mpadd"
#: l'ensemble opaque du prédicat par défaut
ENSEMBLE_S = "Sadd"

#: les axiomes ad hoc de la théorie du crible abstrait
AXIOMES_ADDITIF = ("axiome_P_additif", "axiome_Q_additif")


def appartenance(x):
    """Le prédicat par défaut : `S(x) := x ∈ 𝕊`, pour un `𝕊` totalement opaque.

    C'est le cas le plus général possible — aucune propriété n'est supposée."""
    return appartient(x, var(ENSEMBLE_S))


def elements_bornes(b):
    """P_b — terme opaque, caractérisé par l'axiome."""
    return app("elements_S_bornes", b)


def miroir_additif(b):
    """Q_b — terme opaque, caractérisé par l'axiome."""
    return app("miroir_S", b)


def axiome_P(S=appartenance, b=LIANT_B, x="xadd"):
    """(∀b)(∀x)( x ∈ P_b ⇔ ( (Fini x ∧ S(x)) ∧ x ∈ [0,b] ) ).

    Sélection BORNÉE par `[0,b]` — jamais de compréhension non bornée."""
    vb, vx = var(b), var(x)
    return pourtout(b, pourtout(x, equiv(
        appartient(vx, elements_bornes(vb)),
        et(et(est_fini(vx), S(vx)),
           appartient(vx, E.intervalle_entiers(ZERO, vb))))))


def axiome_Q(S=appartenance, b=LIANT_B, x="xadd", y=LIANT_Y):
    """(∀b)(∀x)( x ∈ Q_b ⇔ (∃y)( (Fini y ∧ S(y)) ∧ b = x + y ) )."""
    vb, vx = var(b), var(x)
    return pourtout(b, pourtout(x, equiv(
        appartient(vx, miroir_additif(vb)),
        existe(y, et(et(est_fini(var(y)), S(var(y))),
                     egal(vb, SC(vx, var(y))))))))


def theorie_additive(S=appartenance):
    """La théorie DÉDIÉE au crible abstrait — séparée de theorie_ensembles()."""
    return N.Theorie("Crible-Additif", [axiome_P(S), axiome_Q(S)])


def membre_P(S, b, x):
    """⊢ x ∈ P_b ⇔ ( (Fini x ∧ S(x)) ∧ x ∈ [0,b] )   pour des TERMES."""
    return instancie(instancie(N.axiome(theorie_additive(S), axiome_P(S)), b), x)


def membre_Q(S, b, x):
    """⊢ x ∈ Q_b ⇔ (∃y)( (Fini y ∧ S(y)) ∧ b = x + y )   pour des TERMES."""
    return instancie(instancie(N.axiome(theorie_additive(S), axiome_Q(S)), b), x)


def rencontre(b=LIANT_B, m=LIANT_M):
    """(∃m)( m ∈ P_b ∧ m ∈ Q_b )  — « b est somme de deux éléments de S »."""
    vb, vm = var(b), var(m)
    return existe(m, et(appartient(vm, elements_bornes(vb)),
                        appartient(vm, miroir_additif(vb))))


def cible_partenaire(b=LIANT_B, m=LIANT_M):
    """(∃m')( ( m' ∈ P_b ∧ m' ∈ Q_b ) ∧ b = m + m' )."""
    vb, vmp = var(b), var(LIANT_PARTENAIRE)
    return existe(LIANT_PARTENAIRE,
                  et(et(appartient(vmp, elements_bornes(vb)),
                        appartient(vmp, miroir_additif(vb))),
                     egal(vb, SC(var(m), vmp))))


def symetrie_additive(S=appartenance, b=LIANT_B, m=LIANT_M):
    """🎯 ⊢ (∀b)(∀m)[ m ∈ P_b ∩ Q_b ⇒ (∃m')( m' ∈ P_b ∩ Q_b ∧ b = m + m' ) ].

    LA SYMÉTRIE, SANS AUCUNE ARITHMÉTIQUE. Le partenaire de `m` est le témoin
    `y` du miroir : il est dans `S` (c'est le miroir qui le dit), il est borné
    par `y ≤ m + y = b`, et `m` rejoue dans le miroir de `y` par commutativité
    de la somme cardinale. `S` n'est jamais ouvert.

    ⚠️ AUCUN PONT D'HABIT α ICI, contrairement à la version concrète : avec un
    prédicat unique il n'y a rien à traduire. Le pont concret était un artefact
    de notation, pas une étape mathématique.

    [CLOS au sens du noyau, SOUS les 2 axiomes de la théorie additive.]"""
    vb, vm = var(b), var(m)

    hm = N.assume(et(appartient(vm, elements_bornes(vb)),
                     appartient(vm, miroir_additif(vb))))
    ap_m = _cg(_mp(_cg(hm), _cg(membre_P(S, vb, vm))))       # Fini m ∧ S(m)
    corps_Q = _mp(_cd(hm), _cg(membre_Q(S, vb, vm)))
    exY = corps_Q.conclusion
    assert getattr(exY, "tag", None) == "exists", "crible abstrait : miroir sans ∃"
    ly, maty = exY.lieur, exY.sous[0]
    vy = var(ly)

    hy = N.assume(maty)
    ap_y, somme_my = _cg(hy), _cd(hy)                        # (Fini y ∧ S y) ; b = m+y
    fini_y = _cg(ap_y)

    #   ── y ∈ P_b : la borne y ≤ b, par le membre DROIT de la somme ───────
    card_y = _mp(fini_y, fic_t(vy))
    zero_le_y = _mp(card_y, N.loi_deduction(est_cardinal(vy),
                                            zero_inf_egal_cardinal(vy)))
    somme_sym = _mp(somme_my, _sym_eq(vb, SC(vm, vy)))       # m+y = b
    s6b = N.s6(SC(vm, vy), vb, "wadd", inf_egal_card(cardinal(vy), var("wadd")))
    cardy_le_b = _mp(inf_egal_somme_droite_binaire(vm, vy),
                     _cg(_mp(somme_sym, s6b)))
    s6y = N.s6(cardinal(vy), vy, "wad2", inf_egal_card(var("wad2"), vb))
    y_le_b = _mp(cardy_le_b,
                 _cg(_mp(_mp(card_y, _cardinal_est_son_cardinal(vy)), s6y)))
    y_in_int = _mp(conjonction_intro(conjonction_intro(card_y, zero_le_y),
                                     y_le_b),
                   _cd(membre_intervalle_entiers_t(ZERO, vb, vy)))
    y_in_P = _mp(conjonction_intro(ap_y, y_in_int), _cd(membre_P(S, vb, vy)))

    #   ── m ∈ Q_b (le miroir de y) : b = y + m par commutativité ─────────
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
        subst_f,
    )
    somme_ym = composer_egalites(somme_my, somme_cardinale_commutative(vm, vy))
    impQ_y = _cd(membre_Q(S, vb, vy))
    exZ = impQ_y.conclusion.sous[0].sous[0]
    assert getattr(exZ, "tag", None) == "exists", "crible abstrait : ∃ du miroir"
    fourni = conjonction_intro(ap_m, somme_ym)
    assert fourni.conclusion == subst_f(vm, exZ.lieur, exZ.sous[0]), \
        "crible abstrait : matrice du miroir de y ≠ attendue"
    m_in_Q = _mp(_mp(fourni, N.s5(exZ.sous[0], vm, exZ.lieur)), impQ_y)

    CIBLE = cible_partenaire(b, m)
    ex_mp = _mp(conjonction_intro(conjonction_intro(y_in_P, m_in_Q), somme_my),
                N.s5(CIBLE.sous[0], vy, LIANT_PARTENAIRE))
    assert ex_mp.conclusion == CIBLE, "crible abstrait : cible partenaire"

    imp_y = existe_elimination(N.loi_deduction(maty, ex_mp), ly)
    th = N.generalisation(b, N.generalisation(
        m, N.loi_deduction(hm.conclusion, _mp(corps_Q, imp_y))))
    assert th.est_clos and not th.hypotheses, "symétrie additive : non clos"
    return th


__all__ = [
    "LIANT_B", "LIANT_M", "LIANT_Y", "LIANT_PARTENAIRE", "ENSEMBLE_S",
    "AXIOMES_ADDITIF", "appartenance", "elements_bornes", "miroir_additif",
    "axiome_P", "axiome_Q", "theorie_additive", "membre_P", "membre_Q",
    "rencontre", "cible_partenaire", "symetrie_additive",
]
