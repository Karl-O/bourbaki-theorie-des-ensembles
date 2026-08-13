#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Tests du conjectureur (JALON 3) — le chaînage noyau produit un théorème CLOS correct.

Utilise de VRAIES implications closes (schémas S2/S3 du noyau) pour tester la transitivité et
la détection d'implication, sans dépendre du corpus. Frontière de confiance intacte.
"""
import sys
from pathlib import Path

_V9 = Path(__file__).resolve().parents[2]
if str(_V9) not in sys.path:
    sys.path.insert(0, str(_V9))
_ICI = Path(__file__).resolve().parent
if str(_ICI) not in sys.path:
    sys.path.insert(0, str(_ICI))

from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N   # noqa: E402
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (            # noqa: E402
    impl, ou, egal, appartient, var)
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import equiv, inclus        # noqa: E402
from conjecturer import (conjecturer, _comme_impl, _comme_egal, _comme_equiv,  # noqa: E402
                         _comme_inclus, _match, iterer, _cle_canon, fecondite, _corpus,
                         egalites_de, chainer_egalites, iterer_egalites,
                         equivalences_de, chainer_equivalences,
                         egal_vers_inclusions, pool_inclusions, chainer_inclusions)


def test_comme_impl_detecte_et_rejette():
    P, Q = appartient(var("a"), var("E")), appartient(var("b"), var("E"))
    assert _comme_impl(impl(P, Q)) == (P, Q)          # ¬P ∨ Q  →  (P, Q)
    assert _comme_impl(egal(var("a"), var("b"))) is None
    assert _comme_impl(ou(P, Q)) is None              # ∨ sans ¬ à gauche ≠ implication

    class _FauxAssemblage:                             # pas de `.tag` (couche primitive)
        pass
    assert _comme_impl(_FauxAssemblage()) is None      # robuste au corpus mixte


def test_transitivite_produit_un_theoreme_clos_nouveau():
    """S2: P⇒(P∨Q) et S3: (P∨Q)⇒(Q∨P) partagent (P∨Q) → conjecture P⇒(Q∨P), prouvée au noyau."""
    P, Q = appartient(var("a"), var("E")), appartient(var("b"), var("E"))
    T1, T2 = N.s2(P, Q), N.s3(P, Q)                   # ⊢P⇒(P∨Q) , ⊢(P∨Q)⇒(Q∨P)
    a1, b1 = _comme_impl(T1.conclusion)
    a2, b2 = _comme_impl(T2.conclusion)
    assert b1 == a2                                   # terme partagé (P∨Q)
    impls = [("s2", T1, a1, b1), ("s3", T2, a2, b2)]
    preuve_de = {T1.conclusion: ("s2", T1), T2.conclusion: ("s3", T2)}

    trouves = conjecturer(impls, preuve_de)
    cibles = [thm.conclusion for (_, _, _, thm) in trouves]
    assert impl(P, ou(Q, P)) in cibles               # le NOUVEAU théorème A⇒C
    for (_, _, _, thm) in trouves:
        assert thm.est_clos                          # certifié clos par le noyau
    assert any(mode == "transit." for (mode, _, _, _) in trouves)


def test_match_renommage_variables():
    """Matching 1er ordre : (r∈E ∨ s∈E) s'unifie à (a∈E ∨ b∈E) via σ={r:a, s:b} ; E fixe."""
    pat = ou(appartient(var("r"), var("E")), appartient(var("s"), var("E")))
    cib = ou(appartient(var("a"), var("E")), appartient(var("b"), var("E")))
    s = {}
    assert _match(pat, cib, s, {"r", "s"})        # E ∉ vlibres → doit coïncider structurellement
    assert s == {"r": var("a"), "s": var("b")}
    assert not _match(pat, cib, {}, set())        # sans variable libre → pas d'unification


def test_transitivite_relachee_unifie_puis_prouve():
    """Antécédents qui NE coïncident PAS exactement mais à σ près → chaînage quand même (transit.σ)."""
    P, Q = appartient(var("a"), var("E")), appartient(var("b"), var("E"))
    R, S = appartient(var("r"), var("E")), appartient(var("s"), var("E"))
    T1 = N.s2(P, Q)                               # ⊢ P ⇒ (P∨Q)
    T2 = N.s3(R, S)                               # ⊢ (R∨S) ⇒ (S∨R)   — antécédent ≠ (P∨Q) littéralement
    impls = [("s2", T1, *_comme_impl(T1.conclusion)),
             ("s3", T2, *_comme_impl(T2.conclusion))]
    trouves = conjecturer(impls, {T1.conclusion: ("s2", T1), T2.conclusion: ("s3", T2)})
    cibles = [thm.conclusion for (_, _, _, thm) in trouves]
    assert impl(P, ou(Q, P)) in cibles           # P ⇒ (Q∨P), obtenu APRÈS unification σ
    assert any(mode == "transit.σ" for (mode, _, _, _) in trouves)
    for (_, _, _, thm) in trouves:
        assert thm.est_clos                       # tout certifié clos par le noyau


def test_iterer_tour2_nouveau_vs_tour1():
    """Conjecture ITÉRÉE : les découvertes du tour 2 sont NOUVELLES vs le tour 1 (dédup α-canonique)."""
    P, Q = appartient(var("a"), var("E")), appartient(var("b"), var("E"))
    S = appartient(var("c"), var("E"))
    T1, T2, T3 = N.s2(P, Q), N.s3(P, Q), N.s2(ou(Q, P), S)
    impls = [("s2", T1, *_comme_impl(T1.conclusion)),
             ("s3", T2, *_comme_impl(T2.conclusion)),
             ("t3", T3, *_comme_impl(T3.conclusion))]
    preuve_de = {t.conclusion: (n, t) for n, t in (("s2", T1), ("s3", T2), ("t3", T3))}
    tous, par_tour = iterer(impls, preuve_de, rounds=2, garder=10)
    assert len(par_tour) >= 1
    k0 = {_cle_canon(thm.conclusion) for (_, _, _, thm) in par_tour[0]}
    if len(par_tour) > 1:
        k1 = {_cle_canon(thm.conclusion) for (_, _, _, thm) in par_tour[1]}
        assert k0.isdisjoint(k1)                  # tour 2 strictement nouveau vs tour 1
    for d in par_tour:
        for (_, _, _, thm) in d:
            assert thm.est_clos                   # tout certifié clos


def test_fecondite_compte_usage_des_sources():
    """La fécondité compte l'usage d'une source comme parent d'une découverte (générativité aval)."""
    P, Q = appartient(var("a"), var("E")), appartient(var("b"), var("E"))
    S = appartient(var("c"), var("E"))
    T1, T2, T3 = N.s2(P, Q), N.s3(P, Q), N.s2(ou(Q, P), S)
    impls = [("s2", T1, *_comme_impl(T1.conclusion)),
             ("s3", T2, *_comme_impl(T2.conclusion)),
             ("t3", T3, *_comme_impl(T3.conclusion))]
    preuve_de = {t.conclusion: (n, t) for n, t in (("s2", T1), ("s3", T2), ("t3", T3))}
    usage, info = fecondite(impls, preuve_de, rounds=2, garder=10)
    assert sum(usage.values()) >= 1                # ≥1 découverte a chaîné des sources
    assert all(v >= 1 for v in usage.values())     # une source comptée l'est au moins une fois


def test_comme_egal_detecte_et_rejette():
    """Détection d'égalité a=b (couche abrégée) ; rejette non-égalités et Assemblage (pas de .tag)."""
    a, b = var("a"), var("b")
    assert _comme_egal(egal(a, b)) == (a, b)
    assert _comme_egal(appartient(a, var("E"))) is None

    class _Fake:
        pass
    assert _comme_egal(_Fake()) is None


def test_chainer_egalites_debloque_algebre():
    """AMÉLIORATION : le chaînage de « = » (transitivité) découvre de VRAIES égalités certifiées,
    là où le moteur implications-only voyait 0 (ex. (A∪B)∪C=(B∪C)∪A par assoc ∘ commut)."""
    impls, preuve_de = _corpus(["bourbaki.i_description_mathematique_formelle", "bourbaki.ii_theorie_des_ensembles"])
    egs = egalites_de(preuve_de)
    assert egs, "aucune égalité dans le corpus ?"
    trouves = chainer_egalites(egs, preuve_de)
    assert len(trouves) >= 1                          # ≥1 nouvelle égalité (0 avant l'amélioration)
    for (mode, s1, s2, thm) in trouves:
        assert mode.startswith("egal")
        assert thm.est_clos                           # certifié clos par le noyau
        assert _comme_egal(thm.conclusion) is not None


def test_comme_equiv_detecte_et_rejette():
    """Détection A⇔B (= et(A⇒B, B⇒A)) ; rejette implication simple et conjonction non-inverse."""
    P, Q, R = (appartient(var(n), var("E")) for n in "abc")
    assert _comme_equiv(equiv(P, Q)) == (P, Q)
    assert _comme_equiv(impl(P, Q)) is None
    # et(A⇒B, C⇒A) : deux implications NON mutuellement inverses → pas une équivalence
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import et
    assert _comme_equiv(et(impl(P, Q), impl(R, P))) is None


def test_chainer_equivalences_et_iterer_egalites_sur_corpus():
    """AMÉLIORATION 2 + RELIE : le chaînage ⇔ trouve des caractérisations ; l'itération des égalités
    compose (tour 2 non vide, briques E<t>#k) — tout certifié clos au noyau."""
    _, preuve_de = _corpus(["bourbaki.i_description_mathematique_formelle", "bourbaki.ii_theorie_des_ensembles"])
    eqs = equivalences_de(preuve_de)
    assert eqs, "aucune équivalence détectée dans le corpus ?"
    trouves = chainer_equivalences(eqs, preuve_de)
    assert len(trouves) >= 1
    for (mode, _, _, thm) in trouves:
        assert mode.startswith("equiv") and thm.est_clos
        assert _comme_equiv(thm.conclusion) is not None
    tous, par_tour = iterer_egalites(preuve_de, rounds=2)
    assert len(par_tour) >= 2 and par_tour[1], "le compounding des égalités ne compose pas ?"
    for (_, _, _, thm) in tous:
        assert thm.est_clos


def test_comme_inclus_detecte_et_rejette():
    """Détection t⊂u (= ∀z(z∈t⇒z∈u)) avec son liant ; rejette implication et égalité."""
    A, B = var("A"), var("B")
    r = _comme_inclus(inclus(A, B))
    assert r is not None and r[0] == A and r[1] == B and r[2] == "z"
    assert _comme_inclus(egal(A, B)) is None
    assert _comme_inclus(impl(appartient(var("x"), A), appartient(var("x"), B))) is None


def test_pont_egalite_vers_inclusions_et_chainage():
    """PONT S6 : chaque égalité close du corpus donne 2 inclusions closes ; le chaînage ⊂
    (corpus + pont) produit de nouvelles inclusions certifiées."""
    _, preuve_de = _corpus(["bourbaki.i_description_mathematique_formelle", "bourbaki.ii_theorie_des_ensembles"])
    egs = egalites_de(preuve_de)
    assert egs
    d1, d2 = egal_vers_inclusions(egs[0][1])
    for d in (d1, d2):
        assert d.est_clos and _comme_inclus(d.conclusion) is not None
    incls, n_corpus, n_pont = pool_inclusions(preuve_de)
    assert n_pont >= 2 * (len(egs) - 2)              # presque toutes passent le pont
    trouves = chainer_inclusions(incls, preuve_de)
    assert len(trouves) >= 1
    for (mode, _, _, thm) in trouves:
        assert mode.startswith("incl") and thm.est_clos
        assert _comme_inclus(thm.conclusion) is not None


def test_existentiels_par_temoin():
    """RÉGIME 5 : ∃-intro par S5 — chaque découverte est close, de forme ∃, absente du corpus."""
    from conj_existe import chainer_existentiels
    _, preuve_de = _corpus(["bourbaki.i_description_mathematique_formelle", "bourbaki.ii_theorie_des_ensembles"])
    trouves = chainer_existentiels(preuve_de, min_occ=2, cap_par_thm=2)
    assert len(trouves) >= 1
    cles_corpus = {_cle_canon(c) for c in preuve_de}
    for (mode, _, _, thm) in trouves:
        assert mode == "∃-intro" and thm.est_clos
        assert thm.conclusion.tag == "exists"          # bien un existentiel
        assert _cle_canon(thm.conclusion) not in cles_corpus


def test_existentiels_structure_partagee():
    """RÉGIME 5, version PARTAGE (ev.278) : l'organe travaille en temps DAG.

    Trois protections : (a) un fait à sous-terme composite RÉPÉTÉ certifie un ∃
    (réflexivité du noyau sur un terme doublé — aucun accès au corpus) ; (b) la
    garde de budget SAUTE un fait trop gros et le RAPPORTE dans `sautes`, jamais
    en silence ; (c) sur un terme profondément PARTAGÉ (tour doublée ×24, dépliage
    ~2^24 nœuds, DAG ~50), l'organe répond vite — c'est le crash MemoryError
    d'avant le patch qui servirait de témoin d'échec."""
    from conj_existe import chainer_existentiels, _taille_dag
    from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import (
        ensembles_abrege as E,
    )
    u, v = var("u"), var("v")
    t_double = E.reunion(E.paire(u, u), E.paire(u, u))     # sous-terme paire(u,u) ×2
    fait = N.reflexivite(t_double)                          # ⊢ t = t   (clos, noyau)
    trouves = chainer_existentiels({fait.conclusion: ("refl", fait)},
                                   min_occ=2, cap_par_thm=3)
    assert len(trouves) >= 1
    for (mode, _, _, thm) in trouves:
        assert mode == "∃-intro" and thm.est_clos
        assert thm.conclusion.tag == "exists"

    # (b) la garde saute ET rapporte
    tour = v
    for _ in range(24):
        tour = E.paire(tour, tour)                          # dépliage ~2^24, DAG ~50
    gros = N.reflexivite(tour)
    assert _taille_dag(gros.conclusion) < 200               # le DAG, lui, est petit
    sautes = []
    petits = chainer_existentiels({gros.conclusion: ("tour", gros)},
                                  min_occ=2, cap_par_thm=1,
                                  budget_dag=10, sautes=sautes)
    assert petits == [] and sautes and sautes[0][0] == "tour", (
        "la garde doit sauter le fait ET le dire — jamais de troncature muette")

    # (c) et sans garde, le DAG partagé reste praticable (l'ancien organe explosait)
    vite = chainer_existentiels({gros.conclusion: ("tour", gros)},
                                min_occ=2, cap_par_thm=1)
    assert all(thm.est_clos for (_, _, _, thm) in vite)


def test_detachement_conjonctif_et_son_arret_aux_faits():
    """L'organe du capstone (ev.286) — et la leçon qui l'a fait naître.

    (a) Antécédent à DEUX conjoints (somme_binaire_entier dépouillée, instanciée
        à N2, N3) : les faits Fini(N2), Fini(N3) s'assemblent et détachent
        ⊢ Fini(N2+N3) — conclusion VÉRIFIÉE.
    (b) LE PIÈGE : est_fini est lui-même une conjonction ; le fait Fini(N2) doit
        être consommé ENTIER (arrêt-aux-faits-connus), jamais décomposé en
        est_cardinal + ¬succ.  On le prouve en vérifiant les provenances.
    (c) Fait manquant → (None, liste des manquants), jamais un échec muet."""
    from conj_existe import detachement_conjonctif
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
        instancie,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (
        est_fini,
    )
    from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_recollement_somme.ensembles_somme_disjointe import (
        somme_cardinale_binaire,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_1_somme_produit_entiers.ensembles_combinatoire_iii5 import (
        somme_binaire_entier,
    )
    from outils_ia.arithmetique.machine_num import NUM, fini_num

    gen = N.generalisation("acj2", N.generalisation("bcj2",
                                                    somme_binaire_entier("acj2", "bcj2")))
    inst = instancie(instancie(gen, NUM(2)), NUM(3))
    faits = {fini_num(2).conclusion: ("Fini(N2)", fini_num(2)),
             fini_num(3).conclusion: ("Fini(N3)", fini_num(3))}

    th, prov = detachement_conjonctif(inst, faits)
    assert th is not None, "détachement en échec : %s" % prov
    assert th.est_clos
    assert th.conclusion == est_fini(somme_cardinale_binaire(NUM(2), NUM(3)))
    assert prov == ["Fini(N2)", "Fini(N3)"], (
        "les faits Fini doivent être consommés ENTIERS — l'arrêt-aux-faits a cédé")

    rien, manquants = detachement_conjonctif(inst, {})
    assert rien is None and len(manquants) >= 2


def test_selectif_invente_la_parite():
    """👑 L'ORGANE SÉLECTIF INVENTE LA PARITÉ (v1, ev.278→282).

    L'abstraction TOTALE ne le peut pas : N6 contient N3 (les numéraux
    s'emboîtent).  En n'abstrayant que dans le membre DROIT de ⊢ N6 = N3+N3,
    la machine doit produire EXACTEMENT `parite.est_pair(N(6))` — la formule du
    module d'énoncé, pas une variante — certifiée par S5+MP, invariant 22."""
    from conj_existe import chainer_existentiels_selectif
    from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
        symetrie,
    )
    from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_recollement_somme.ensembles_somme_disjointe import (
        somme_cardinale_binaire,
    )
    from outils_ia.arithmetique.calcul_num import somme_num
    from outils_ia.arithmetique.machine_num import NUM
    from outils_ia.arithmetique.parite import K_PAIR, est_pair

    s33 = somme_cardinale_binaire(NUM(3), NUM(3))
    fait = N.modus_ponens(somme_num(3, 3), symetrie(s33, NUM(6)))   # ⊢ N6 = N3+N3
    trouves = chainer_existentiels_selectif(
        {fait.conclusion: ("N6=N3+N3", fait)}, cote="droite", lieur=K_PAIR)
    assert trouves, "l'organe sélectif n'a rien produit"
    conclusions = [thm.conclusion for (_, _, _, thm) in trouves]
    assert est_pair(NUM(6)) in conclusions, (
        "la parité de 6 n'est pas parmi les inventions — l'abstraction n'a pas "
        "visé N3 dans le membre droit")
    for (mode, _, _, thm) in trouves:
        assert mode.startswith("∃-sélectif") and thm.est_clos


def test_pas_de_conjecture_triviale():
    """A⇒A (S2 avec conséquent trivial) ne doit pas se re-conjecturer comme du neuf déjà connu."""
    P, Q = appartient(var("a"), var("E")), appartient(var("b"), var("E"))
    T1 = N.s2(P, Q)                                   # ⊢ P ⇒ (P∨Q)  (déjà connu)
    a1, b1 = _comme_impl(T1.conclusion)
    trouves = conjecturer([("s2", T1, a1, b1)], {T1.conclusion: ("s2", T1)})
    # rien de neuf : pas de 2ᵉ implication à chaîner, et P⇒(P∨Q) est déjà connu
    assert all(thm.conclusion != T1.conclusion for (_, _, _, thm) in trouves)


def test_gate_parametre_trois_faces_et_voile_de_cache():
    """Gate paramétré (7 août 2026) : source vraie OK, instance menteuse WRONG,
    et le prouveur-TRICHE qui rend le cache MEURT sous le voile — le contrôle
    discriminant : sans `_ns_gate`, la triche passerait et le gate ne testerait rien."""
    import inspect
    import textwrap
    from gen_paires_corruption import _statut_parametre
    from outils_ia.arithmetique import numeraux as NX

    insts = NX.fini_instances()
    for args, attendu in insts:                        # les instances disent vrai
        assert NX.fini(*args).conclusion == attendu
    src = textwrap.dedent(inspect.getsource(NX.fini))
    assert _statut_parametre(NX, "fini", src, insts) == "OK"
    menteuse = [(insts[0][0], insts[1][1])]            # énoncé de 3 pour l'argument 2
    assert _statut_parametre(NX, "fini", src, menteuse) == "WRONG"
    NX.fini(3)                                         # cache réel chaud, exprès
    triche = "def fini(k):\n    return _FINI[k]"
    assert _statut_parametre(NX, "fini", triche, insts) == "ERROR"


def test_cle_canon_partage_et_canonicite():
    """`_cle_canon` version PARTAGE (8 août 2026) : même sémantique α-canonique
    (renommage par 1re apparition dépliée), coût DAG. Trois faces : (a) α-variants
    → MÊME clé ; structurellement distincts → clés ≠ ; (b) un arbre PARTAGÉ et son
    égal non-partagé → même clé (le partage est invisible) ; (c) un empilement
    ou(t,t) de profondeur 40 (2^40 nœuds dépliés) se clef instantanément — avant,
    la sérialisation-chaîne explosait en mémoire (MemoryError mesuré, régime CY1)."""
    P = appartient(var("a"), var("E"))
    Q = appartient(var("b"), var("E"))
    # (a) canonicité
    assert _cle_canon(impl(P, Q)) == _cle_canon(
        impl(appartient(var("x"), var("F")), appartient(var("y"), var("F"))))
    assert _cle_canon(impl(P, P)) != _cle_canon(impl(P, Q))
    # (b) partage invisible : deux refs au MÊME objet vs deux objets égaux
    partage = ou(P, P)
    deplie = ou(appartient(var("a"), var("E")), appartient(var("a"), var("E")))
    assert _cle_canon(partage) == _cle_canon(deplie)
    # (c) le témoin d'explosion
    t = P
    for _ in range(40):
        t = ou(t, t)
    assert len(_cle_canon(t)) == 32                    # digest hex, calcul immédiat


def test_trace_au_fil_de_l_eau():
    """`trace` (8 août 2026) : un long run n'est plus une boîte noire — événements
    par tour, par implication-source, et par découverte certifiée, émis PENDANT le
    calcul. Le contrôle qui peut échouer : sans découverte possible, aucun événement
    « découverte » ; avec le régime s2/s3 qui en produit, il y en a."""
    P, Q = appartient(var("a"), var("E")), appartient(var("b"), var("E"))
    T1, T2 = N.s2(P, Q), N.s3(P, Q)
    a1, b1 = _comme_impl(T1.conclusion)
    a2, b2 = _comme_impl(T2.conclusion)
    impls = [("s2", T1, a1, b1), ("s3", T2, a2, b2)]
    connus = {T1.conclusion: ("s2", T1), T2.conclusion: ("s3", T2)}
    evts = []
    tous, par_tour = iterer(impls, connus, rounds=2, garder=5, trace=evts.append)
    types = {e["type"] for e in evts}
    assert {"tour", "conjecturer", "avancement", "fin_tour"} <= types
    n_dec = sum(1 for e in evts if e["type"] == "découverte")
    assert n_dec == len(tous)                       # un événement PAR découverte
    avancements = [e for e in evts if e["type"] == "avancement"]
    assert all(e["impl"] <= e["n"] for e in avancements)
