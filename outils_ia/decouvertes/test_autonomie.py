# -*- coding: utf-8 -*-
"""Le pipeline autonome — besoin, imprimeur, combleurs — protégé (ev.317-322).

Trois étages : l'imprimeur fait l'aller-retour exact sur les cibles réelles ;
l'organe de besoin ferme au noyau et nomme ses manques ; la chaîne complète
ferme une décomposition Goldbach MINIATURE sans script manuel (marker slow).
"""
import pytest

import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E


def test_imprimeur_aller_retour_exact():
    """7/7 sur les cibles des deux fournées de lemmes machine (ev.314)."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
        var, egal, et, impl, non, ou, existe, pourtout, appartient,
    )
    from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_recollement_somme.ensembles_somme_disjointe import (
        somme_cardinale_binaire,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
        est_cardinal, inf_egal_card,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (
        est_fini, successeur,
    )
    from outils_ia.arithmetique import lemmes_conjectures as L1
    from outils_ia.arithmetique import lemmes_conjectures_2 as L2
    from outils_ia.decouvertes.imprimeur import code_de, _registre_arithmetique
    _registre_arithmetique()
    ENV = {"var": var, "egal": egal, "et": et, "impl": impl, "non": non,
           "ou": ou, "existe": existe, "pourtout": pourtout,
           "appartient": appartient, "est_fini": est_fini,
           "est_cardinal": est_cardinal, "inf_egal_card": inf_egal_card,
           "successeur": successeur, "SC": somme_cardinale_binaire}
    for cible_fn in (L1.fini_somme_cardinal_cible, L1.fini_somme_successeur_cible,
                     L1.prop2_sous_fini_cible, L1.fini_descendant_sous_fini_cible,
                     L2.succ_fini_cardinal_cible,
                     L2.fini_somme_cardinal_successeur_cible,
                     L2.prop2_sous_somme_finie_cible):
        f = cible_fn()
        assert eval(code_de(f), ENV) == f          # noqa: S307 — aller-retour


@pytest.mark.slow
def test_besoin_ferme_et_nomme_ses_manques():
    """3 faces (ev.317) : fermeture 1 pas, 2 pas (noyau), manque NOMMÉ sinon."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_fini_successeur import (
        fini_implique_fini_successeur,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers_theoremes import (
        fini_implique_cardinal,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (
        est_fini, est_cardinal, successeur,
    )
    from outils_ia.arithmetique.numeraux import num, fini
    from outils_ia.decouvertes.besoin import besoins
    from conjecturer import _comme_impl

    impls = []
    for nom, th in (("fini_succ", fini_implique_fini_successeur("apb")),
                    ("fic", fini_implique_cardinal("apb"))):
        ab = _comme_impl(th.conclusion)
        impls.append((nom, th, ab[0], ab[1]))
    faits = {}
    for k in (2, 3, 4):
        t = fini(k)
        faits[t.conclusion] = ("Fini(N%d)" % k, t)

    th1, _ = besoins(est_fini(successeur(num(4))), impls, faits)
    assert th1 is not None and th1.est_clos                    # 1 pas
    th2, _ = besoins(est_cardinal(successeur(num(3))), impls, faits)
    assert th2 is not None and th2.est_clos                    # 2 pas
    th3, m3 = besoins(est_cardinal(successeur(successeur(successeur(num(4))))),
                      impls, faits, profondeur=2)
    assert th3 is None and m3                                  # manque NOMMÉ
    assert len(E.theorie_ensembles().axiomes) == 22


@pytest.mark.slow
def test_fermeture_autonome_miniature():
    """decomposition(N8) fermée par besoin→combleurs→assemblage (ev.321-322)."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
        var,
    )
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
        instancie,
    )
    from outils_ia.conjectures.goldbach_borne import decomposition
    from outils_ia.conjectures.goldbach_borne_n import goldbach_borne_n
    from outils_ia.arithmetique.machine_num import NUM
    from outils_ia.decouvertes.combleurs import fermer_par_besoin
    from conjecturer import _comme_impl

    borne = instancie(goldbach_borne_n(8), var("ncj"))
    ab = _comme_impl(borne.conclusion)
    th, prov = fermer_par_besoin(decomposition(NUM(8)),
                                 [("borne_8[n]", borne, ab[0], ab[1])],
                                 {}, borne=8)
    assert th is not None and th.est_clos
    assert th.conclusion == decomposition(NUM(8))
    assert len(prov) >= 2                                      # assemblage réel
    assert len(E.theorie_ensembles().axiomes) == 22


def test_organe_v2_recompose_les_conjoints():
    """ORGANE V2 (10 août, ev.358-359) : un antécédent conjonctif dont les
    morceaux sont fermables (faits + impl) doit être RECOMPOSÉ (∧-intro) et
    le but fermé — c'était le chaînon manquant diagnostiqué par PB14-15."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
        var, egal, et,
    )
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import (
        noyau_abrege as N,
    )
    from outils_ia.decouvertes.besoin import besoins

    x, y, z, w = var("xv2"), var("yv2"), var("zv2"), var("wv2")
    but = egal(y, y)
    A = et(egal(x, x), egal(z, z))
    # route : (x=x ∧ z=z) ⇒ y=y   (décharge vacante — S2, permise par le noyau)
    r1 = N.loi_deduction(A, N.reflexivite(y))
    # z=z fermable par une 2e impl depuis le fait w=w ; x=x est un FAIT
    r2 = N.loi_deduction(egal(w, w), N.reflexivite(z))
    impls = [("r1", r1, A, but), ("r2", r2, egal(w, w), egal(z, z))]
    faits = {egal(x, x): ("fait_x", N.reflexivite(x)),
             egal(w, w): ("fait_w", N.reflexivite(w))}
    th, manques = besoins(but, impls, faits, profondeur=3)
    assert th is not None and th.est_clos and th.conclusion == but
    assert manques == []
    assert len(E.theorie_ensembles().axiomes) == 22


def test_organe_v2_ne_nomme_que_les_recalcitrants():
    """Reporting v2 : si UN conjoint reste infermable, seuls les
    récalcitrants sont nommés — pas ceux qui ferment individuellement."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
        var, egal, et, existe,
    )
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import (
        noyau_abrege as N,
    )
    from outils_ia.decouvertes.besoin import besoins

    x, y, m = var("xv2b"), var("yv2b"), var("mv2b")
    #   but ∃ (non fermable par v9-réflexivité) : l'organe DOIT passer par r1
    but = existe("wv2b", egal(var("wv2b"), y))
    ex_y = N.modus_ponens(N.reflexivite(y),
                          N.s5(egal(var("wv2b"), y), y, "wv2b"))
    A = et(egal(x, x), egal(m, var("autre_v2b")))          # 2e conjoint : FAUX
    r1 = N.loi_deduction(A, ex_y)
    impls = [("r1", r1, A, but)]
    faits = {egal(x, x): ("fait_x", N.reflexivite(x))}
    th, manques = besoins(but, impls, faits, profondeur=3)
    assert th is None
    formules = [b["formule"] for b in manques]
    assert egal(m, var("autre_v2b")) in formules           # le récalcitrant
    assert egal(x, x) not in formules                      # PAS le fermable
    assert len(E.theorie_ensembles().axiomes) == 22


def test_organe_v4_instancie_les_faits_universels():
    """ORGANE V4 (10 août, ev.370) : un fait (∀x)φ du pool ferme le but
    φ[x:=t] par instanciation jugée noyau — l'hypothèse S{n} du pas de
    descente (PB23) était de cette forme et restait inerte."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
        var, egal, impl,
    )
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import (
        noyau_abrege as N,
    )
    from outils_ia.decouvertes.besoin import besoins

    x, a, b = var("xv4"), var("av4"), var("bv4")
    fait_univ = N.generalisation("xv4", N.reflexivite(x))  # (∀x)(x = x)
    but = egal(a, a)                                       # l'instance en a
    th, manques = besoins(but, [], {fait_univ.conclusion: ("univ", fait_univ)},
                          profondeur=2)
    assert th is not None and th.est_clos and th.conclusion == but
    assert manques == []
    assert len(E.theorie_ensembles().axiomes) == 22


def test_organe_v5_les_faits_universels_deviennent_des_routes():
    """ORGANE V5 (10 août, ev.372) : un fait (∀x)(P(x) ⇒ Q) sert de ROUTE —
    ré-ouvert puis traité par la boucle standard (σ, sous-but, mp)."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
        var, egal,
    )
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import (
        noyau_abrege as N,
    )
    from outils_ia.decouvertes.besoin import besoins

    x, b = var("xv5"), var("bv5")
    fait_univ = N.generalisation("xv5", N.loi_deduction(egal(x, x),
                                                        N.reflexivite(b)))
    #   (∀x)( x=x ⇒ b=b ) ; but = b=b ; sous-but x=x fourni en fait
    faits = {fait_univ.conclusion: ("univ_impl", fait_univ),
             egal(x, x): ("refl_x", N.reflexivite(x))}
    th, manques = besoins(egal(b, b), [], faits, profondeur=2)
    assert th is not None and th.est_clos and th.conclusion == egal(b, b)
    assert len(E.theorie_ensembles().axiomes) == 22


def test_organe_v6_proposeur_de_temoins():
    """ORGANE V6-ébauche (10 août, ev.374) : un PROPOSEUR suggère le témoin
    qu'aucune σ-unification ne trouve — le noyau juge l'instanciation.
    C'est l'organe créatif demandé par la machine (¬(n=n), ev.373)."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
        var, egal, existe,
    )
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import (
        noyau_abrege as N,
    )
    from outils_ia.decouvertes.besoin import besoins

    x, b, c = var("xv6"), var("bv6"), var("cv6")
    #   but ∃ (non fermable par v9-réflexivité) : seul le proposeur mène à c
    but = existe("wv6", egal(var("wv6"), b))
    ex_b = N.modus_ponens(N.reflexivite(b),
                          N.s5(egal(var("wv6"), b), b, "wv6"))
    #   (∀x)( x=c ⇒ but ) : seul x:=c rend l'antécédent prouvable
    fait_univ = N.generalisation("xv6", N.loi_deduction(egal(x, c), ex_b))
    faits = {fait_univ.conclusion: ("univ_c", fait_univ),
             egal(c, c): ("refl_c", N.reflexivite(c))}
    #   SANS proposeur : v5 ré-ouvre mais le sous-but x=c reste récalcitrant
    th0, _ = besoins(but, [], faits, profondeur=2)
    assert th0 is None
    #   AVEC proposeur suggérant le témoin c : fermé, jugé noyau
    prop = lambda _but, _faits: [(fait_univ.conclusion, c)]
    th1, manques = besoins(but, [], faits, profondeur=2, proposeurs=[prop])
    assert th1 is not None and th1.est_clos and th1.conclusion == but
    assert len(E.theorie_ensembles().axiomes) == 22


def test_organe_v7_existentiel_a_temoins_proposes():
    """ORGANE V7 (10 août, ev.375) : un but ∃x φ se ferme par témoin PROPOSÉ
    (récursion sur φ[x:=t] puis ré-introduction jugée noyau) — y compris les
    ∃ IMBRIQUÉS, la forme du cœur additif ∃p∃q de Goldbach."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
        var, egal, existe,
    )
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import (
        noyau_abrege as N,
    )
    from outils_ia.decouvertes.besoin import besoins

    c = var("cv7")
    but = existe("xv7", existe("yv7", egal(var("xv7"), var("yv7"))))
    faits = {egal(c, c): ("refl_c", N.reflexivite(c))}
    #   sans proposeur : rien
    th0, _ = besoins(but, [], faits, profondeur=3)
    assert th0 is None
    #   proposeur : témoin c pour chaque ∃ rencontré
    prop = lambda _but, _faits: [("∃", c)]
    th1, _ = besoins(but, [], faits, profondeur=3, proposeurs=[prop])
    assert th1 is not None and th1.est_clos and th1.conclusion == but
    assert len(E.theorie_ensembles().axiomes) == 22


def test_organes_v6v7v8_integration_goldbach():
    """INTÉGRATION (10 août, ev.375) : l'organe CRÉATIF ferme une
    décomposition de Goldbach de bout en bout — ∃p∃q par témoins PROPOSÉS
    (couple + complément, calcul Python), conjonction recomposée (v8),
    primalités et somme = faits certifiés du dépôt. Le noyau juge tout."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
        egal,
    )
    from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
        symetrie,
    )
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import (
        noyau_abrege as N,
    )
    from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_recollement_somme.ensembles_somme_disjointe import (
        somme_cardinale_binaire as SC,
    )
    from outils_ia.arithmetique.machine_num import NUM
    from outils_ia.arithmetique.calcul_num import somme_num
    from outils_ia.conjectures.primalite import est_premier_num
    from outils_ia.conjectures.goldbach_borne import decomposition, couple
    from outils_ia.decouvertes.besoin import besoins

    m = 16                                                   # 16 = 3 + 13
    a, b = couple(m)
    p1 = est_premier_num(a, d="d1", q="q1")
    p2 = est_premier_num(b, d="d2", q="q2")
    s = somme_num(a, b)                                      # N(a)+N(b) = N(m)
    s_inv = N.modus_ponens(s, symetrie(SC(NUM(a), NUM(b)), NUM(m)))
    faits = {p1.conclusion: ("premier_%d" % a, p1),
             p2.conclusion: ("premier_%d" % b, p2),
             s_inv.conclusion: ("somme", s_inv)}

    def _dec(t):
        for i in range(0, 2 * m + 1):
            if NUM(i) == t:
                return i
        return None

    def proposeur_goldbach(but, _faits):
        """Mécanique GÉNÉRALE : décode l'égalité-somme du but PAR ÉGALITÉ DE
        TERMES (SC est un τ-terme opaque), suggère couple puis complément."""
        from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var as _v
        if getattr(but, "tag", None) != "exists":
            return []
        f = but
        lieurs = []
        while getattr(f, "tag", None) == "exists":
            lieurs.append(f.lieur)
            f = f.sous[0]
        try:
            eq = f.sous[0].sous[1].sous[0]                   # C de et(et(A,B),C)
        except Exception:
            return []
        t_tot = _dec(eq.termes[0])
        if t_tot is None:
            return []
        if len(lieurs) == 2:                                 # 1er ∃ : couple
            if eq.termes[1] == SC(_v(lieurs[0]), _v(lieurs[1])):
                c = couple(t_tot)
                return [("∃", NUM(c[0]))] if c else []
            return []
        for a in range(2, t_tot):                            # 2e ∃ : complément
            if eq.termes[1] == SC(NUM(a), _v(lieurs[0])):
                return [("∃", NUM(t_tot - a))]
        return []

    but = decomposition(NUM(m))
    th, manques = besoins(but, [], faits, profondeur=4,
                          proposeurs=[proposeur_goldbach])
    assert th is not None and th.est_clos and th.conclusion == but
    assert len(E.theorie_ensembles().axiomes) == 22


def test_organe_v9_egalite_reflexive():
    """v9 (ev.381) : un but t=t ferme par réflexivité (Théorème 1, E I.39).

    Mesuré sur PB28 : la route JUMELLE (T=Q=k) traînait l'obligation
    « 2k = 2k » comme manque alors qu'elle est vraie par réflexivité."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
        var, egal,
    )
    from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_recollement_somme.ensembles_somme_disjointe import (
        somme_cardinale_binaire as SC,
    )
    from outils_ia.decouvertes.besoin import besoins

    vk = var("kv9")
    M = SC(vk, vk)
    th, manques = besoins(egal(M, M), [], {}, profondeur=1)
    assert th is not None and th.est_clos and th.conclusion == egal(M, M)
    assert manques == []
    # une égalité NON réflexive reste un manque (pas de fermeture sauvage)
    th2, _ = besoins(egal(M, vk), [], {}, profondeur=1)
    assert th2 is None
    assert len(E.theorie_ensembles().axiomes) == 22


def test_organe_v10_proposeur_par_appartenance():
    """v10 (ev.394) : un proposeur GÉNÉRIQUE — face à (∃x)φ(x), les témoins
    sont les t des faits « t ∈ A » du pool.

    Ne connaît ni le problème ni l'arithmétique ; le noyau juge. C'est le
    geste minimal du marcheur : les objets déjà nommés sont les candidats."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
        var, et, existe, appartient,
    )
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import (
        noyau_abrege as N,
    )
    from outils_ia.decouvertes.besoin import besoins

    def proposeur_appartenance(but, faits):
        if getattr(but, "tag", None) != "exists":
            return []
        vus, out = set(), []
        for ccl in faits:
            if getattr(ccl, "tag", None) != "in":
                continue
            t = ccl.termes[0]
            if t not in vus:
                vus.add(t)
                out.append(("∃", t))
        return out

    vA, vB, vc = var("Av10"), var("Bv10"), var("cv10")
    f1 = N.assume(appartient(vc, vA))
    f2 = N.assume(appartient(vc, vB))
    faits = {f1.conclusion: ("cA", f1), f2.conclusion: ("cB", f2)}
    but = existe("mv10", et(appartient(var("mv10"), vA),
                            appartient(var("mv10"), vB)))

    #   sans proposeur : le ∃ n'est pas attaquable
    th0, _ = besoins(but, [], faits, profondeur=3)
    assert th0 is None
    #   avec : fermé, jugé noyau, hypothèses = les deux appartenances
    th1, manques = besoins(but, [], faits, profondeur=3,
                           proposeurs=[proposeur_appartenance])
    assert th1 is not None and th1.conclusion == but
    assert th1.hypotheses == frozenset({f1.conclusion, f2.conclusion})
    assert manques == []
    assert len(E.theorie_ensembles().axiomes) == 22


def test_organe_v11_proposeur_par_schema():
    """v11 (ev.398) : proposeur générique par VARIABLES LIBRES — atteint les
    objets enfouis dans les prédicats DÉFINIS (est_fini = ¬…), là où v10
    (termes de tête) échoue. Pas suivant du marcheur."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
        var, egal, existe, libres_f,
    )
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import (
        noyau_abrege as N,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (
        est_fini,
    )
    from outils_ia.decouvertes.besoin import besoins

    def proposeur_schema(but, faits):
        if getattr(but, "tag", None) != "exists":
            return []
        vus, out = set(), []
        for ccl in faits:
            for nom in sorted(libres_f(ccl)):
                if nom not in vus:
                    vus.add(nom)
                    out.append(("∃", var(nom)))
        return out

    vc = var("cv11")
    f1 = N.assume(est_fini(vc))                     # tag "non" : c est ENFOUI
    faits = {f1.conclusion: ("Fini(c)", f1)}
    but = existe("wv11", egal(var("wv11"), vc))     # (∃w) w = c

    def proposeur_v10(but, faits):
        if getattr(but, "tag", None) != "exists":
            return []
        return [("∃", ccl.termes[0]) for ccl in faits
                if getattr(ccl, "tag", None) == "in"]

    th10, _ = besoins(but, [], faits, profondeur=3, proposeurs=[proposeur_v10])
    assert th10 is None                             # v10 ne trouve pas c
    th11, manques = besoins(but, [], faits, profondeur=3,
                            proposeurs=[proposeur_schema])
    assert th11 is not None and th11.conclusion == but
    assert manques == []
    assert len(E.theorie_ensembles().axiomes) == 22


def test_organe_v13_temoin_canonique_fabrique():
    """v13 (ev.401) : le proposeur FABRIQUE le témoin canonique τx(φ) depuis
    le but seul — il ne le choisit pas dans le pool. Licite par S5.

    Avec v14, l'effet observable est que le but existentiel est RAMENÉ aux
    propriétés du τ-terme : le manque n'est plus un ∃, c'est le geste de GG9
    devenu automatique."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
        var, et, existe, appartient, tau,
    )
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import (
        noyau_abrege as N,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (
        est_fini,
    )
    from outils_ia.decouvertes.besoin import besoins

    def proposeur_canonique(but, faits):
        if getattr(but, "tag", None) != "exists":
            return []
        return [("∃", tau(but.lieur, but.sous[0]))]

    vA = var("Av13t")
    matr = et(est_fini(var("yv13t")), appartient(var("yv13t"), vA))
    but = existe("yv13t", matr)
    T = tau("yv13t", matr)

    #   pool parlant du τ-TERME : v13 ferme, jugé noyau
    f1, f2 = N.assume(est_fini(T)), N.assume(appartient(T, vA))
    pool = {f1.conclusion: ("Fini(T)", f1), f2.conclusion: ("T∈A", f2)}
    th, manques = besoins(but, [], pool, profondeur=4,
                          proposeurs=[proposeur_canonique])
    assert th is not None and th.conclusion == but
    assert manques == []

    #   pool VIDE : v13 ne ferme pas, mais v14 fait remonter les obligations
    #   sur le témoin — le manque n'est PLUS un ∃.
    th0, m0 = besoins(but, [], {}, profondeur=4,
                      proposeurs=[proposeur_canonique])
    assert th0 is None and m0
    assert all(getattr(m["formule"], "tag", None) != "exists" for m in m0), \
        "v14 : le but ∃ devrait être ramené aux propriétés du τ-terme"
    assert len(E.theorie_ensembles().axiomes) == 22


def test_organe_v14_ne_jette_plus_les_manques_du_temoin():
    """v14 (ev.401) : une route-témoin qui ÉCHOUE ne perd plus les manques
    nommés par sa descente. Sans proposeur, rien ne change (garde-fou)."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
        var, egal, existe,
    )
    from outils_ia.decouvertes.besoin import besoins

    vb = var("bv14")
    but = existe("xv14", egal(var("xv14"), vb))

    #   sans proposeur : le ∃ reste le manque (comportement historique)
    th0, m0 = besoins(but, [], {}, profondeur=3)
    assert th0 is None
    assert m0 == [] or all(getattr(m["formule"], "tag", None) == "exists"
                           for m in m0)
    assert len(E.theorie_ensembles().axiomes) == 22



@pytest.mark.slow
def test_organe_v15_compounding_du_proposeur_appris():
    """v15 (ev.408) : la machine CAPITALISE ses témoins.

    Passe 1 — un proposeur calculateur ferme le but ; l'enregistreur retient
    les témoins employés. Passe 2 — le proposeur APPRIS seul (aucun calcul,
    aucun accès à l'arithmétique) referme le même but, instantanément.

    ⚠️ Le pool doit être COMPLET (la commutativité incluse) : sans elle, la
    recherche part en exploration longue — c'est ce qui avait fait expirer une
    première version de ce test (ev.409).
    ⚠️ Ne JAMAIS str()/repr() un τ-terme : le repr est récursif (MemoryError).
    """
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
        var,
    )
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import (
        noyau_abrege as N,
    )
    from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
        symetrie,
    )
    from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_recollement_somme.ensembles_somme_disjointe import (
        somme_cardinale_binaire as SC,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_somme.ensembles_arith_somme import (
        somme_cardinale_commutative,
    )
    from outils_ia.arithmetique.machine_num import NUM
    from outils_ia.arithmetique.calcul_num import somme_num
    from outils_ia.conjectures.primalite import est_premier_num
    from outils_ia.conjectures.goldbach_borne import decomposition
    from outils_ia.decouvertes.besoin import besoins

    m, p, q = 16, 3, 13
    faits = {}
    for x in (p, q):
        for d_, q_ in (("d1", "q1"), ("d2", "q2")):
            th = est_premier_num(x, d=d_, q=q_)
            faits[th.conclusion] = ("premier(%d)" % x, th)
    s = somme_num(p, q)
    faits[s.conclusion] = ("somme", s)
    sc = somme_cardinale_commutative(NUM(p), NUM(q))       # ← le fait décisif
    faits[sc.conclusion] = ("comm", sc)
    ssym = N.modus_ponens(s, symetrie(SC(NUM(p), NUM(q)), NUM(m)))
    faits[ssym.conclusion] = ("somme-sym", ssym)
    but = decomposition(NUM(m))

    registre = []

    def _calcul(but, faits):
        if getattr(but, "tag", None) != "exists":
            return []
        lieurs, f = [], but
        while getattr(f, "tag", None) == "exists":
            lieurs.append(f.lieur)
            f = f.sous[0]
        try:
            eq = f.sous[0].sous[1].sous[0]
        except Exception:
            return []
        if len(lieurs) == 2:
            if eq.termes[1] == SC(var(lieurs[0]), var(lieurs[1])):
                return [("∃", NUM(p))]
            return []
        for a in range(2, m):
            if eq.termes[1] == SC(NUM(a), var(lieurs[0])):
                return [("∃", NUM(m - a))]
        return []

    def _enregistreur(but, faits):
        sugg = _calcul(but, faits)
        for (_marq, t) in sugg:
            if t not in registre:
                registre.append(t)
        return sugg

    def _appris(but, faits):
        if getattr(but, "tag", None) != "exists":
            return []
        return [("∃", t) for t in registre]

    th1, _ = besoins(but, [], faits, profondeur=4, proposeurs=[_enregistreur])
    assert th1 is not None and th1.conclusion == but
    assert len(registre) == 2                    # les deux témoins retenus

    th2, manques = besoins(but, [], faits, profondeur=4, proposeurs=[_appris])
    assert th2 is not None and th2.conclusion == but
    assert manques == []
    assert len(E.theorie_ensembles().axiomes) == 22


def test_organe_v16_congruence_automatique():
    """v16 (ev.410) : la machine FABRIQUE le pas de congruence.

    Sur une opération ABSENTE du dépôt (a ⊕ b := (a+b)+1), elle doit fermer
    « a ⊕ b = b ⊕ a » à partir de la seule commutativité de « + » — et NE PAS
    fermer un énoncé faux."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
        var, egal,
    )
    from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_recollement_somme.ensembles_somme_disjointe import (
        somme_cardinale_binaire as SC,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_somme.ensembles_arith_somme import (
        somme_cardinale_commutative,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (
        successeur,
    )
    from outils_ia.decouvertes.besoin import besoins

    a, b = var("av16"), var("bv16")
    oplus = lambda x, y: successeur(SC(x, y))          # noqa: E731
    comm = somme_cardinale_commutative(a, b)
    faits = {comm.conclusion: ("comm", comm)}

    th, manques = besoins(egal(oplus(a, b), oplus(b, a)), [], faits,
                          profondeur=4)
    assert th is not None and th.est_clos
    assert th.conclusion == egal(oplus(a, b), oplus(b, a))
    assert manques == []
    #   garde-fou : un énoncé FAUX reste infermable
    th_faux, _ = besoins(egal(oplus(a, b), SC(a, b)), [], faits, profondeur=4)
    assert th_faux is None
    assert len(E.theorie_ensembles().axiomes) == 22


def test_organe_v17_chaine_de_reecritures():
    """v17 (ev.411) : plusieurs réécritures se COMPOSENT par transitivité.

    Deux commutations indépendantes sous un même terme — une seule congruence
    n'y suffit pas. Garde-fou : `a+b = a+c` doit rester ouvert."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
        var, egal,
    )
    from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_recollement_somme.ensembles_somme_disjointe import (
        somme_cardinale_binaire as SC,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_somme.ensembles_arith_somme import (
        somme_cardinale_commutative,
    )
    from outils_ia.decouvertes.besoin import besoins

    a, b, c, d = var("av17"), var("bv17"), var("cv17"), var("dv17")
    faits = {}
    for x, y in ((a, b), (c, d)):
        th = somme_cardinale_commutative(x, y)
        faits[th.conclusion] = ("comm", th)

    but = egal(SC(SC(a, b), SC(c, d)), SC(SC(b, a), SC(d, c)))
    th, manques = besoins(but, [], faits, profondeur=4)
    assert th is not None and th.est_clos and th.conclusion == but
    assert manques == []
    #   garde-fou
    th_faux, _ = besoins(egal(SC(a, b), SC(a, c)), [], faits, profondeur=4)
    assert th_faux is None
    assert len(E.theorie_ensembles().axiomes) == 22


def test_organe_v19_oracle_refute_avant_de_chercher():
    """v19 (12 août) : CALCULER avant de démontrer.

    Un but numériquement FAUX n'a aucune preuve : l'organe le dit tout de
    suite au lieu de dépenser son budget. Coût d'une consultation qui ne
    conclut pas : 1 µs (l'index des formules est bâti une fois).

    ⚠️ L'ASYMÉTRIE EST LE CŒUR DU TEST. v19 n'utilise QUE le verdict FAUX.
    « Aucun contre-exemple » ne ferme rien et ne doit rien fermer — Goldbach
    n'a aucun contre-exemple connu jusqu'à 4×10¹⁸ et reste ouverte. Le second
    cas ci-dessous verrouille précisément ça : un but VRAI mais non démontrable
    depuis le pool doit rester OUVERT, pas être fermé par l'oracle."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
        egal,
    )
    from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_recollement_somme.ensembles_somme_disjointe import (
        somme_cardinale_binaire as SC,
    )
    from outils_ia.arithmetique.numeraux import num
    from outils_ia.decouvertes.besoin import besoins

    #   FAUX : 2 + 2 = 5 — réfuté par le calcul, aucune recherche engagée
    th, manques = besoins(egal(SC(num(2), num(2)), num(5)), [], {}, profondeur=3)
    assert th is None
    assert manques and manques[0].get("refute") is True

    #   VRAI mais hors du pool : l'oracle NE DOIT PAS le fermer
    th2, manques2 = besoins(egal(SC(num(2), num(2)), num(4)), [], {},
                            profondeur=3)
    assert th2 is None, "l'oracle a FERMÉ un but — il ne démontre rien"
    assert not (manques2 and manques2[0].get("refute")), \
        "un but VRAI a été marqué réfuté"
    assert len(E.theorie_ensembles().axiomes) == 22


def test_organe_v18_associativite_d_une_operation_derivee():
    """v18 (ev.412) : les lois du pool sont INSTANCIÉES pour être appliquées.

    LE CAS QUI L'A FAIT NAÎTRE. On définit une opération neuve à partir de
    l'addition cardinale — `a ⊕ b := (a+b)+1` — et on demande son
    ASSOCIATIVITÉ. Le pool ne contient que deux lois **brutes**, sur `a+b` :
    associativité itérée et commutativité. Le but, lui, ne contient que des
    `(a+b)+1` : aucune loi ne s'applique littéralement, et le moteur restait
    muet. v18 matche le membre gauche de la loi contre les sous-termes
    rencontrés et fait instancier le théorème par le NOYAU.

    MESURE (12 août) : la chaîne minimale fait **5** pas, d'où la borne
    `max_pas=5` du moteur — avec 3, ce même but échouait. La recherche en
    PROFONDEUR, elle, ne le fermait à aucun budget (95 s à profondeur 7)."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
        var, egal,
    )
    from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_recollement_somme.ensembles_somme_disjointe import (
        somme_cardinale_binaire as SC,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (
        successeur,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_somme.ensembles_arith_somme import (
        somme_cardinale_commutative,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_somme.ensembles_somme_iteree import (
        somme_cardinale_associative_iteree,
    )
    from outils_ia.decouvertes.besoin import besoins

    a, b, c = var("av18"), var("bv18"), var("cv18")

    def oplus(x, y):
        return successeur(SC(x, y))

    #   deux lois BRUTES seulement — aucune instance pré-mâchée
    assoc = somme_cardinale_associative_iteree(a, b, c)
    comm = somme_cardinale_commutative(a, b)
    faits = {assoc.conclusion: ("assoc", assoc), comm.conclusion: ("comm", comm)}

    but = egal(oplus(oplus(a, b), c), oplus(a, oplus(b, c)))
    th, manques = besoins(but, [], faits, profondeur=4)
    assert th is not None and th.est_clos and not th.hypotheses
    assert th.conclusion == but
    assert manques == []
    #   garde-fou : un énoncé indérivable reste ouvert. Attention au choix —
    #   `(a⊕b)⊕c = (a⊕c)⊕b` serait un mauvais témoin : c'est VRAI (les deux
    #   valent a+b+c+2), donc le moteur a le droit de le fermer.
    th_faux, _ = besoins(egal(oplus(a, b), oplus(a, c)), [], faits,
                         profondeur=3)
    assert th_faux is None
    assert len(E.theorie_ensembles().axiomes) == 22
