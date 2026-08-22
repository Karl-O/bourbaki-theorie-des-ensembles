# -*- coding: utf-8 -*-
"""§III.6.3 — LEMME 2 (E III.48) : « L'ensemble ℕ×ℕ est équipotent à ℕ. »

🎯 W6+W7, la CLÔTURE du Lemme 2 :
  • F := graphe_terme(ℕ×ℕ, 2^(pr₁x)·3^(pr₂x))  — le graphe du couplage ;
  • pairing_graphe_fonctionnel / _domaine    (C54) ;
  • pairing_graphe_injectif                  (W5 sur les projections) ;
  • pairing_graphe_image_incluse             (les valeurs 2^m·3^n sont dans ℕ) ;
  • NN_carre_inf_egal_NN   ⊢ ℕ×ℕ ≤ ℕ         (est_injection_de + S5) ;
  • lemme_deux_NN          ⊢ Eq(ℕ×ℕ, ℕ)      (Cantor–Bernstein + direction A).

ÉCART DE DÉMONSTRATION (énoncé IDENTIQUE, consigné dans ANOMALIES.md) : Bourbaki
construit l'injection par ENTRELACEMENT des développements dyadiques (E III.48,
prop. 8 p. E III.40) ; le dépôt utilise le couplage (m,n) ↦ 2^m·3^n dont
l'injectivité (2-valuation W3 + 3-injectivité W4) est élémentaire sur les
briques §III.5 déjà closes.  Le noyau certifie le MÊME énoncé Eq(ℕ×ℕ, ℕ).

theorie_ensembles INCHANGÉE (22).  Noyau INTACT.  Aucun axiome nouveau.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, et, appartient, inclus,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    instancie, conjonction_intro, conjonction_elim_gauche as elg,
    conjonction_elim_droite as eld, equivalence_avant, equivalence_arriere,
    equivalence_transitivite,
)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import (
    alpha_existe, existe_elimination,
)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
    symetrie, composer_egalites, congruence_terme,
)
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_6_fonction_terme.ensembles_fonction_terme import (
    graphe_terme_fonctionnel, membre_graphe_terme,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.cantor.ensembles_cantor import (
    graphe_terme_domaine, graphe_terme_valeur,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    est_injection_de, inf_egal_card, equipotent,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_produit.ensembles_produit_commute import (
    membre_produit_pr1, membre_produit_pr2, membre_produit_egal_couple,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (
    est_fini,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_1_somme_produit_entiers.ensembles_prop3_produit_entier_iii5 import (
    produit_binaire_entier,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.entiers_cardinaux.ensembles_puissance_deux_trois_NN import (
    deux_puissance_dans_NN, trois_puissance_dans_NN,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_1_n_objet_existence.ensembles_ensemble_NN import (
    ensemble_NN, appartenance_NN_instanciee,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.denombrable.ensembles_denombrable_pairing import (
    pairing_terme, pairing_injectif,
)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def _cut(thm, P, pr):
    return N.modus_ponens(pr, N.loi_deduction(P, thm))


def _NN():
    return ensemble_NN()


def _T():
    """Le terme de couplage en la variable FRAÎCHE « zgp ».

    ⚠️ PAS « x » : pr₁/pr₂ sont des τ à lieurs internes x/y — la convention C54
    par défaut CAPTURERAIT la variable du terme (leçon n°11).  Tous les lemmes
    C54 sont appelés avec x="zgp" (y garde son défaut « y » :
    valeur_caracterisation a « y » codé en dur — leçon n°11bis)."""
    return pairing_terme(E.pr1(var("zgp")), E.pr2(var("zgp")))


def pairing_graphe():
    """F := graphe_terme(ℕ×ℕ, 2^(pr₁x)·3^(pr₂x))."""
    NN = _NN()
    return E.graphe_terme(E.produit(NN, NN), _T())


def _fini_de_NN(tz, in_thm):
    """{in_thm ⊢ z∈ℕ} ⊢ Fini z   (pont appartenance_NN, sens avant)."""
    return N.modus_ponens(in_thm, equivalence_avant(appartenance_NN_instanciee(_t(tz))))


def _NN_de_fini(tz, fini_thm):
    """{fini_thm ⊢ Fini z} ⊢ z∈ℕ   (pont, sens arrière)."""
    return N.modus_ponens(fini_thm, equivalence_arriere(appartenance_NN_instanciee(_t(tz))))


# ── (a)+(b) : fonctionnel, domaine ────────────────────────────────────────────
def pairing_graphe_fonctionnel():
    """⊢ F fonctionnel   (C54)."""
    NN = _NN()
    return graphe_terme_fonctionnel(E.produit(NN, NN), _T(), x="zgp")


def pairing_graphe_domaine():
    """⊢ dom F = ℕ×ℕ   (C54)."""
    NN = _NN()
    return graphe_terme_domaine(E.produit(NN, NN), _T(), x="zgp")


# ── (c) : injectif sur ℕ×ℕ ────────────────────────────────────────────────────
def pairing_graphe_injectif():
    """⊢ injective_dans(F, ℕ×ℕ).   (W5 sur les projections + reconstruction.)

    Preuve en lieurs frais ug/upg puis α-passage vers les lieurs u/up
    d'injective_dans (patron bijection_injective, prop12)."""
    NN = _NN()
    P = E.produit(NN, NN)
    F = pairing_graphe()
    vu, vup = var("ug"), var("upg")
    Tu = pairing_terme(E.pr1(vu), E.pr2(vu))
    Tup = pairing_terme(E.pr1(vup), E.pr2(vup))

    corps = et(et(appartient(vu, P), appartient(vup, P)),
               egal(E.valeur(F, vu), E.valeur(F, vup)))
    h = N.assume(corps)
    h_u = elg(elg(h))
    h_up = eld(elg(h))
    h_eq = eld(h)

    v_u = _cut(graphe_terme_valeur(P, _T(), "ug", x="zgp"), appartient(vu, P), h_u)
    v_up = _cut(graphe_terme_valeur(P, _T(), "upg", x="zgp"), appartient(vup, P), h_up)
    eq_T = composer_egalites(composer_egalites(
        N.modus_ponens(v_u, symetrie(E.valeur(F, vu), Tu)), h_eq), v_up)
    #   2^(pr₁u)·3^(pr₂u) = 2^(pr₁u')·3^(pr₂u')

    #   composantes dans ℕ, donc finies
    f_m = _fini_de_NN(E.pr1(vu), _cut(membre_produit_pr1(NN, NN, vu),
                                      appartient(vu, P), h_u))
    f_n = _fini_de_NN(E.pr2(vu), _cut(membre_produit_pr2(NN, NN, vu),
                                      appartient(vu, P), h_u))
    f_mp = _fini_de_NN(E.pr1(vup), _cut(membre_produit_pr1(NN, NN, vup),
                                        appartient(vup, P), h_up))
    f_np = _fini_de_NN(E.pr2(vup), _cut(membre_produit_pr2(NN, NN, vup),
                                        appartient(vup, P), h_up))

    #   W5 ∀-clos aux termes (signature m, mp, n, np)
    g5 = N.generalisation("mpg", N.generalisation("mppg", N.generalisation(
        "npg", N.generalisation("nppg", pairing_injectif()))))
    w5 = instancie(instancie(instancie(instancie(g5,
        E.pr1(vu)), E.pr1(vup)), E.pr2(vu)), E.pr2(vup))
    ante5 = conjonction_intro(
        conjonction_intro(conjonction_intro(f_m, f_mp),
                          conjonction_intro(f_n, f_np)), eq_T)
    r5 = N.modus_ponens(ante5, w5)
    m_eq, n_eq = elg(r5), eld(r5)                        # pr₁u=pr₁u' ; pr₂u=pr₂u'

    #   reconstruction : u = (pr₁u, pr₂u) = (pr₁u', pr₂u') = u'
    mec_u = _cut(membre_produit_egal_couple(NN, NN, vu), appartient(vu, P), h_u)
    mec_up = _cut(membre_produit_egal_couple(NN, NN, vup), appartient(vup, P), h_up)
    c1 = N.modus_ponens(m_eq, congruence_terme(
        E.pr1(vu), E.pr1(vup), E.couple(var("wgp"), E.pr2(vu)), "wgp"))
    c2 = N.modus_ponens(n_eq, congruence_terme(
        E.pr2(vu), E.pr2(vup), E.couple(E.pr1(vup), var("wgp")), "wgp"))
    u_eq = composer_egalites(composer_egalites(composer_egalites(
        mec_u, c1), c2),
        N.modus_ponens(mec_up, symetrie(vup, E.couple(E.pr1(vup), E.pr2(vup)))))

    inner = N.loi_deduction(corps, u_eq)
    gen = N.generalisation("ug", N.generalisation("upg", inner))
    t1 = instancie(gen, var("u"))
    t2 = instancie(t1, var("up"))
    res = N.generalisation("u", N.generalisation("up", t2))
    assert res.conclusion == E.injective_dans(F, P), \
        "pairing_graphe_injectif : forme inattendue"
    return res


# ── (d) : image ⊂ ℕ ───────────────────────────────────────────────────────────
def pairing_graphe_image_incluse():
    """⊢ image(F, ℕ×ℕ) ⊂ ℕ.   (les valeurs 2^m·3^n sont des entiers.)"""
    NN = _NN()
    P = E.produit(NN, NN)
    F = pairing_graphe()
    vz = var("z")

    ax_img = N.axiome(E.theorie_ensembles(), E.AXIOME_IMAGE)
    img_car0 = instancie(instancie(instancie(ax_img, F), P), vz)
    impl_LtoEX = img_car0.conclusion.sous[0].sous[0].sous[0]
    rhs_ex = impl_LtoEX.sous[1]
    assert rhs_ex.tag == "exists"
    nom_lie = rhs_ex.lieur
    inner0 = et(appartient(var(nom_lie), P),
                appartient(E.couple(var(nom_lie), vz), F))
    img_car = equivalence_transitivite(
        img_car0, alpha_existe(nom_lie, "tg", inner0))
    vtg = var("tg")
    corps = et(appartient(vtg, P), appartient(E.couple(vtg, vz), F))

    mem = membre_graphe_terme(P, _T(), "tg", "z", "zgp", "y")
    hb = N.assume(corps)
    t_inP = elg(hb)
    cond = N.modus_ponens(eld(hb), equivalence_avant(mem))
    z_eq = eld(cond)                                     # z = 2^(pr₁t)·3^(pr₂t)
    #   la valeur est FINIE
    f_m = _fini_de_NN(E.pr1(vtg), _cut(membre_produit_pr1(NN, NN, vtg),
                                       appartient(vtg, P), t_inP))
    f_n = _fini_de_NN(E.pr2(vtg), _cut(membre_produit_pr2(NN, NN, vtg),
                                       appartient(vtg, P), t_inP))
    g2 = N.generalisation("npdt", deux_puissance_dans_NN("npdt"))
    f_e2 = N.modus_ponens(f_m, instancie(g2, E.pr1(vtg)))
    g3 = N.generalisation("npdt", trois_puissance_dans_NN("npdt"))
    f_e3 = N.modus_ponens(f_n, instancie(g3, E.pr2(vtg)))
    gp = N.generalisation("apbe", N.generalisation("bpbe",
        produit_binaire_entier("apbe", "bpbe")))
    f_T = N.modus_ponens(conjonction_intro(f_e2, f_e3),
                         instancie(instancie(gp, _e2h(vtg)), _e3h(vtg)))
    #   Fini(2^pr₁t · 3^pr₂t)
    f_z = N.modus_ponens(f_T, equivalence_arriere(N.modus_ponens(
        z_eq, N.s6(vz, pairing_terme(E.pr1(vtg), E.pr2(vtg)), "wgp",
                   est_fini(var("wgp"))))))             # Fini z
    z_inNN = _NN_de_fini(vz, f_z)
    ex_imp = existe_elimination(N.loi_deduction(corps, z_inNN), "tg")
    h_img = N.assume(appartient(vz, E.image(F, P)))
    z_in2 = N.modus_ponens(N.modus_ponens(h_img, equivalence_avant(img_car)), ex_imp)
    return N.generalisation("z", N.loi_deduction(
        appartient(vz, E.image(F, P)), z_in2))


def _e2h(vt):
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_5_exposant.definition.ensembles_exposant_cardinal import (
        exposant_cardinal_binaire)
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import DEUX
    return exposant_cardinal_binaire(DEUX, E.pr1(vt))


def _e3h(vt):
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_5_exposant.definition.ensembles_exposant_cardinal import (
        exposant_cardinal_binaire)
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import TROIS
    return exposant_cardinal_binaire(TROIS, E.pr2(vt))


# ── (e) : ℕ×ℕ ≤ ℕ puis le LEMME 2 ────────────────────────────────────────────
# @livre Ch.III §6.3 Demo.Lem2 | E III.48 L.4-16 | PDF p.151  (N×N ≤ N — la direction dure du Lemme 2)
def NN_carre_inf_egal_NN():
    """🎯 ⊢ ℕ×ℕ ≤ ℕ.   (est_injection_de(F, ℕ×ℕ, ℕ) + S5, patron inf_egal_parties.)"""
    NN = _NN()
    P = E.produit(NN, NN)
    F = pairing_graphe()
    inj = conjonction_intro(conjonction_intro(conjonction_intro(
        pairing_graphe_fonctionnel(), pairing_graphe_domaine()),
        pairing_graphe_injectif()), pairing_graphe_image_incluse())
    assert inj.conclusion == est_injection_de(F, P, NN), \
        "NN_carre_inf_egal_NN : conjonction mal ordonnée"
    res = N.modus_ponens(inj, N.s5(est_injection_de(var("F"), P, NN), F, "F"))
    assert res.conclusion == inf_egal_card(P, NN)
    assert not res.hypotheses
    return res


# @livre Ch.III §6.3 Lem.2 | E III.48 L.4-16 | PDF p.151
def lemme_deux_NN():
    """🎯🎯 ⊢ Eq(ℕ×ℕ, ℕ).   (LEMME 2, E III.48 — « ℕ×ℕ est équipotent à ℕ ».)

    Cantor–Bernstein (∀-clos aux termes) sur ℕ×ℕ ≤ ℕ (ci-dessus) et ℕ ≤ ℕ×ℕ
    (direction A, NN_inf_egal_NN_carre, close)."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.cantor_bernstein.cloture._recollement import (
        cantor_bernstein)
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.denombrable.ensembles_denombrable_carre_iii6 import (
        NN_inf_egal_NN_carre)
    NN = _NN()
    P = E.produit(NN, NN)
    g_cb = N.generalisation("A", N.generalisation("B", cantor_bernstein("A", "B")))
    cb = instancie(instancie(g_cb, P), NN)               # (P≤ℕ ∧ ℕ≤P) ⇒ Eq(P, ℕ)
    res = N.modus_ponens(
        conjonction_intro(NN_carre_inf_egal_NN(), NN_inf_egal_NN_carre()), cb)
    assert res.conclusion == equipotent(P, NN), "lemme_deux_NN : forme inattendue"
    assert not res.hypotheses, "lemme_deux_NN : hypothèses résiduelles"
    return res


__all__ = ["pairing_graphe", "pairing_graphe_fonctionnel", "pairing_graphe_domaine",
           "pairing_graphe_injectif", "pairing_graphe_image_incluse",
           "NN_carre_inf_egal_NN", "lemme_deux_NN"]
