# -*- coding: utf-8 -*-
"""Test miroir de la FAMILLE IDENTITÉ CONCRÈTE (X)_{X∈𝔊} — §II.4.1, E II.22.

ANGLE MORT COMBLÉ (2026-07-26, dette 2/3).  `ensembles_famille_identite_ii4` n'avait
AUCUN test miroir alors qu'il consommait `membre_inter_ensemble`, passé au statut B
(énoncé renforcé) par la migration « ⋂ = sélection dans ⋃ ».  Le risque était donc
maximal exactement là où la couverture était nulle : « ça construit » n'est pas
« l'énoncé n'a pas bougé ».

CAHIER DES CHARGES.  Chaque conclusion est RECONSTRUITE À LA MAIN ci-dessous, à
partir des seules primitives de `ensembles_abrege` — jamais via les constructeurs
`enonce_*` du module testé, qui bougeraient AVEC lui et ne prouveraient rien.  Les
hypothèses sont assérées par égalité EXACTE de frozenset (pas par inclusion) et
doublées d'une GARDE ANTI-B explicite : aucun témoin d'indice — ni ¬(U=∅), ni
(∃i)(i∈U) — ne doit s'être glissé dans un énoncé qui n'en a pas besoin.

LOI N.1 (le cœur de ce fichier).  Le témoin d'indice est GRATUIT dès que la preuve
tient déjà un élément de l'intersection ; l'exiger par réflexe AFFAIBLIT l'énoncé.
Les deux résultats ⋂ du module tombent de part et d'autre de cette ligne, et les
deux tests dédiés le DÉMONTRENT au lieu de le postuler :
  · `membre_inter_parties` — le sens ⇐ CONCLUT z∈⋂U : témoin NON gratuit.  U≠∅ est
    load-bearing, et on l'établit en RÉFUTANT l'énoncé instancié à U=∅ (⊢ ¬énoncé,
    CLOS, sans PONT) : c'est le contre-exemple, pas une pétition de principe.
  · `inter_incluse_partie_parties` — on PART de z∈⋂U et l'antécédent c∈U EST le
    témoin : U≠∅ est GRATUITE.  Elle a donc été RETIRÉE (énoncé renforcé) ; le test
    verrouille son absence pour qu'elle ne repousse pas.
"""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, egal, et, non, impl, appartient, existe, pourtout, equiv, inclus)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    contraposition, equivalence_arriere, instancie)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_intersection_fondation.ensembles_inter_migration_ii4 import (
    indices_non_vides, inter_famille_vide_est_vide)
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_1_definitions_algebre.ensembles_famille_identite_ii4 import (
    IOTA, famille_identite_valeur, famille_identite_est_identite,
    membre_reunion_parties, membre_inter_parties, partie_incluse_reunion_parties,
    partie_incluse_reunion_parties_t, inter_incluse_partie_parties)

# ── Les énoncés, RECONSTRUITS À LA MAIN (aucun appel au module testé) ─────────
vU, vz, vc, vi, vX = var("U"), var("z"), var("c"), var("i"), var("X")

# G := graphe_terme(U, ι, ι) — la famille identité concrète, liant ι = « ifid ».
G = E.graphe_terme(vU, var("ifid"), "ifid")

# PONT(U) := (∀X)( X∈U ⇒ valeur_famille(G,X) = valeur(G,X) )   [hyp. honnête]
PONT = pourtout("X", impl(appartient(vX, vU),
                          egal(E.valeur_famille(G, vX), E.valeur(G, vX))))

NON_VIDE = non(egal(vU, E.VIDE))          # U ≠ ∅   (forme littérale du livre)
TEMOIN = indices_non_vides(vU)            # (∃i)(i∈U) — l'autre forme du témoin


def _garde_anti_B(r, attendues, nom):
    """Hypothèses EXACTES + aucun témoin d'indice clandestin (garde anti-statut-B)."""
    assert r.hypotheses == frozenset(attendues), "%s : hypothèses ≠ attendues" % nom
    assert TEMOIN not in r.hypotheses, "%s : témoin (∃i)(i∈U) clandestin" % nom
    if NON_VIDE not in attendues:
        assert NON_VIDE not in r.hypotheses, "%s : U≠∅ clandestine" % nom


# ── Les six résultats du module ──────────────────────────────────────────────
def test_famille_identite_valeur():
    """{X∈U} ⊢ G(X) = X — τ-léger : le terme-valeur est LA VARIABLE ι."""
    r = famille_identite_valeur()
    assert r.conclusion == egal(E.valeur(G, vX), vX)
    _garde_anti_B(r, [appartient(vX, vU)], "famille_identite_valeur")


def test_famille_identite_est_identite():
    """{PONT} ⊢ est_famille_identite(G,U), i.e. (∀X)(X∈U ⇒ valeur_famille(G,X)=X)."""
    r = famille_identite_est_identite()
    assert r.conclusion == pourtout("X", impl(appartient(vX, vU),
                                              egal(E.valeur_famille(G, vX), vX)))
    _garde_anti_B(r, [PONT], "famille_identite_est_identite")


def test_membre_reunion_parties():
    """{PONT} ⊢ (z ∈ ⋃U) ⇔ (∃i)(i∈U et z∈i).   Côté ⋃ : INTACT par la migration."""
    r = membre_reunion_parties()
    assert r.conclusion == equiv(appartient(vz, E.reunion_famille(G, vU)),
                                 existe("i", et(appartient(vi, vU), appartient(vz, vi))))
    _garde_anti_B(r, [PONT], "membre_reunion_parties")


def test_membre_inter_parties():
    """{PONT, U≠∅} ⊢ (z ∈ ⋂U) ⇔ (∀i)(i∈U ⇒ z∈i).   ÉNONCÉ INCHANGÉ par la migration.

    C'est LE résultat qui consommait `membre_inter_ensemble` (statut B).  Il ne le
    consomme plus : il passe par `caracterisation_inter_famille_indices_non_vide`.
    Ce qui compte est que l'énoncé, LUI, n'a pas bougé — mêmes deux hypothèses
    qu'avant migration, sous leur forme littérale ¬(U=∅) et non (∃i)(i∈U)."""
    r = membre_inter_parties()
    assert r.conclusion == equiv(appartient(vz, E.inter_famille(G, vU)),
                                 pourtout("i", impl(appartient(vi, vU),
                                                    appartient(vz, vi))))
    _garde_anti_B(r, [PONT, NON_VIDE], "membre_inter_parties")


def test_partie_incluse_reunion_parties():
    """{PONT} ⊢ (c∈U) ⇒ (c ⊂ ⋃U)  — et sa version TERME (motif _inst_gen)."""
    r = partie_incluse_reunion_parties()
    assert r.conclusion == impl(appartient(vc, vU), inclus(vc, E.reunion_famille(G, vU)))
    _garde_anti_B(r, [PONT], "partie_incluse_reunion_parties")

    vA = var("A")
    rt = partie_incluse_reunion_parties_t(vA)
    assert rt.conclusion == impl(appartient(vA, vU), inclus(vA, E.reunion_famille(G, vU)))
    _garde_anti_B(rt, [PONT], "partie_incluse_reunion_parties_t")


def test_inter_incluse_partie_parties():
    """{PONT} ⊢ (c∈U) ⇒ (⋂U ⊂ c).   ÉNONCÉ RENFORCÉ : U≠∅ est TOMBÉE (LOI N.1).

    L'avant-migration l'attachait par décoration C14 (`_attache_non_vide`), la
    première rédaction post-migration l'héritait de `membre_inter_parties`.  Les
    deux étaient gratuites : on part de z∈⋂U (élimination inconditionnelle) et
    c∈U fournit lui-même le témoin.  La conclusion est bit-à-bit celle d'avant."""
    r = inter_incluse_partie_parties()
    assert r.conclusion == impl(appartient(vc, vU), inclus(E.inter_famille(G, vU), vc))
    _garde_anti_B(r, [PONT], "inter_incluse_partie_parties")


# ── LOI N.1 : les deux côtés de la ligne, DÉMONTRÉS ──────────────────────────
def test_loi_n1_u_non_vide_est_load_bearing_pour_membre_inter():
    """CONTRE-EXEMPLE : à U=∅, l'énoncé de `membre_inter_parties` est RÉFUTABLE.

    ⊢ ¬( (z ∈ ⋂_{ι∈∅} G(ι)) ⇔ (∀i)(i∈∅ ⇒ z∈i) ), CLOS et SANS PONT.  Le membre
    droit se prouve ex falso ; le membre gauche est réfuté par
    `inter_famille_vide_est_vide` (⋂ sur un ensemble d'indices vide = ∅).  Donc
    U≠∅ n'est PAS une décoration ici : le sens ⇐ conclut z∈⋂U, le témoin
    d'indice n'est pas gratuit, et retirer l'hypothèse rendrait l'énoncé FAUX."""
    Gv = E.graphe_terme(E.VIDE, var("ifid"), "ifid")        # G sur U = ∅
    gauche = appartient(vz, E.inter_famille(Gv, E.VIDE))
    droit = pourtout("i", impl(appartient(vi, E.VIDE), appartient(vz, vi)))
    enonce_vide = equiv(gauche, droit)

    # (1) membre DROIT : prouvable ex falso, CLOS.
    nvide = instancie(N.axiome(E.theorie_ensembles(), E.AXIOME_VIDE), vi)
    thm_droit = N.generalisation("i", N.modus_ponens(
        nvide, N.s2(non(appartient(vi, E.VIDE)), appartient(vz, vi))))
    assert thm_droit.conclusion == droit and thm_droit.est_clos

    # (2) membre GAUCHE : RÉFUTABLE, CLOS.  « f » est un NOM dans la brique : on
    # ∀-clôt puis on instancie en Gv (liant traversé « z » non libre dans Gv).
    refute = instancie(instancie(
        N.generalisation("f", inter_famille_vide_est_vide("f", "z")), Gv), vz)
    assert refute.conclusion == non(gauche) and refute.est_clos

    # (3) l'équivalence entraînerait le membre gauche ⇒ elle est réfutable.
    h = N.assume(enonce_vide)
    imp = N.loi_deduction(enonce_vide,
                          N.modus_ponens(thm_droit, equivalence_arriere(h)))
    contra = N.modus_ponens(refute, contraposition(imp))
    assert contra.conclusion == non(enonce_vide)
    assert contra.hypotheses == frozenset() and contra.est_clos


def test_loi_n1_le_temoin_est_gratuit_pour_inter_incluse_partie():
    """VERROU : `inter_incluse_partie_parties` ne doit JAMAIS re-porter un témoin.

    Miroir exact du test précédent : ici la LOI N.1 s'applique (on part de z∈⋂U,
    et c∈U est le témoin), donc l'énoncé se tient sur la SEULE hypothèse PONT.
    Ce test échouera si quelqu'un « répare » le fichier en réintroduisant U≠∅ ou
    (∃i)(i∈U) — un affaiblissement gratuit est aussi malhonnête qu'un test qui ment."""
    r = inter_incluse_partie_parties()
    assert r.hypotheses == frozenset([PONT])
    assert NON_VIDE not in r.hypotheses
    assert TEMOIN not in r.hypotheses
    assert len(r.hypotheses) == 1

    # …et la conclusion est bien la MÊME que celle du résultat à 2 hypothèses
    # d'avant : c'est un RENFORCEMENT, pas un changement d'énoncé.
    assert r.conclusion == impl(appartient(vc, vU), inclus(E.inter_famille(G, vU), vc))


def test_theorie_ensembles_reste_a_22_axiomes():
    """INVARIANT DUR : rien n'est postulé — le PONT est une HYPOTHÈSE, pas un axiome."""
    famille_identite_est_identite()
    membre_reunion_parties()
    membre_inter_parties()
    inter_incluse_partie_parties()
    assert len(E.theorie_ensembles().axiomes) == 22
    assert PONT not in E.theorie_ensembles().axiomes
    assert IOTA == "ifid"
