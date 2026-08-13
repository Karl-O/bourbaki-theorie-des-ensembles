"""§II.4.1 — FAMILLE IDENTITÉ CONCRÈTE (X)_{X∈𝔊} : décharge de est_famille_identite.

Bourbaki (E II.22, §4.1) définit ⋃𝔊 — réunion d'un ensemble 𝔊 de parties — comme
la réunion de la FAMILLE IDENTITÉ (X)_{X∈𝔊} (idem ⋂𝔊, E II.22 L.49-53).  Le
fichier frère ensembles_reunion_ensemble_parties_ii4.py porte « f est la famille
identité sur U » en HYPOTHÈSE ABSTRAITE est_famille_identite(f, U).  ICI on la
CONSTRUIT et on la DÉCHARGE :

    G := graphe_terme(U, ι, ι)     (C54, E II.46 : le graphe de X ↦ X sur U ;
                                    terme-valeur = LA VARIABLE ι, liant ι=« ifid »)

modulo l'UNIQUE hypothèse honnête restante, le PONT NOTATIONNEL fam↔valeur :

    PONT(U) := (∀X)( X∈U  ⇒  valeur_famille(G, X) = valeur(G, X) )

(E II.4.1 : une famille EST une fonction et la notation X_ι DÉSIGNE sa valeur
f(ι)).  ⚠️ MUR STRUCTUREL documenté (tête de ensembles_factorielle_def2_rec.py,
précédent HW/HN, repris par ensembles_somme_indexee.py) : valeur_famille =
app("fam", ·) est un symbole LIBRE qu'AUCUN des 22 axiomes ne relie à valeur —
l'instance ci-dessus est IMPROUVABLE ET IRRÉFUTABLE en th.22.  PONT est la
lecture MINIMALE de cette notation sur la famille CONCRÈTE G (hypothèse, jamais
un axiome ; rien postulé).

Résultats certifiés (⋆ = hypothèses exactement {PONT(U)}) :
  · famille_identite_valeur          {X∈U} ⊢ G(X) = X    (graphe_terme_valeur,
        théorie dédiée C54 ; terme-valeur = la variable ι : τ-LÉGER)
  · famille_identite_est_identite  ⋆ ⊢ est_famille_identite(G, U)     (LA décharge)
  · membre_reunion_parties         ⋆ ⊢ (z ∈ ⋃U) ⇔ (∃i)(i∈U et z∈i)
  · membre_inter_parties             {PONT, U≠∅} ⊢ (z ∈ ⋂U) ⇔ (∀i)(i∈U ⇒ z∈i)
  · partie_incluse_reunion_parties ⋆ ⊢ (c∈U) ⇒ (c ⊂ ⋃U)   [+ version _t : TERME]
  · inter_incluse_partie_parties   ⋆ ⊢ (c∈U) ⇒ (⋂U ⊂ c)

U≠∅ SUR LE SEUL `membre_inter_parties` : hypothèse de FIDÉLITÉ (Déf. 2, E II.22 :
⋂ exige I≠∅), désormais RÉELLEMENT CONSOMMÉE.  L'ancien AXIOME_INTER_FAM était
l'équivalence inconditionnelle — et CONTRADICTOIRE (pour I=∅ l'intersection
contenait TOUT objet, cf. outils_ia/audit/preuve_incoherence_inter_vide.py) ;
U≠∅ n'y était qu'ATTACHÉE par affaiblissement C14 (décoration).  La SÉLECTION
DANS LA RÉUNION l'a remplacé : le membre droit est une CONJONCTION, l'équivalence
n'est plus gratuite et se récupère par `caracterisation_inter_famille_indices_
non_vide` (ii_4_intersection_fondation/ensembles_inter_migration_ii4) sous ¬(U=∅).
ÉNONCÉ INCHANGÉ, hypothèses comprises ; seule la preuve change.  Et U≠∅ y est
INDISPENSABLE : l'énoncé instancié à U=∅ est RÉFUTABLE (⊢ ¬énoncé, CLOS — le test
miroir l'exhibe), car le sens ⇐ CONCLUT z∈⋂U.

⚠️ AUDIT DETTE 2/3 (2026-07-26) — `inter_incluse_partie_parties` est RENFORCÉ :
son U≠∅ est TOMBÉ (LOI N.1 : le témoin d'indice est GRATUIT dès que la preuve
tient déjà un élément de l'intersection).  Ici on PART de z∈⋂U — l'élimination
`inter_donne_membres` est inconditionnelle — et l'antécédent c∈U EST le témoin.
U≠∅ n'a jamais rien porté : avant la migration simple décoration C14, après
héritée de l'équivalence complète dont seul le sens ⇒ servait.  Le résultat
repasse donc par le lemme frère `inter_incluse_partie`, réparé sur la seule
élimination et resté à la seule hypothèse `est_famille_identite`.  Le module ne
consomme plus `membre_inter_ensemble` (passé statut B) : le seul énoncé de ce
fichier qui porte encore U≠∅ le porte parce qu'il le DOIT.

Consommateurs : n°67 (E.R.27, plus petit/grand élément de 𝔉 pour ⊂),
n°95=133 (E III.30 Cor., pas d'ensemble de tous les cardinaux), n°140 (Zorn
Cor.2).  theorie_ensembles() == 22 (asserté en test).  Liant ι = « ifid »
EXOTIQUE (jamais traversé par les liants standard X/i/z/y des briques) ;
τ-liant de valeur = « y » (lettre simple, défaut du dépôt).
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, et, non, impl, appartient, existe, pourtout, equiv, inclus)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege import syllogisme
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, equivalence_avant, equivalence_arriere, instancie)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import (
    monotonie_pour_tout)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import composer_egalites
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_1_definitions_algebre.ensembles_reunion_ensemble_parties_ii4 import (
    est_famille_identite, membre_reunion_ensemble, partie_incluse_reunion,
    inter_incluse_partie)
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_intersection_fondation.ensembles_inter_migration_ii4 import (
    caracterisation_inter_famille_indices_non_vide)

IOTA = "ifid"          # liant du terme-valeur de G — EXOTIQUE (garde anti-collision)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# ── La famille identité concrète et son pont notationnel ─────────────────────
# @livre Ch.II §4.1 Def.- | E II.22 L.31-36 | PDF p.73  (⋃𝔊 = réunion de la famille (X)_{X∈𝔊} — ici la famille est CONSTRUITE par C54)
def famille_identite(u="U", iota=IOTA):
    """G := graphe_terme(U, ι, ι) — le graphe de X ↦ X sur U (famille identité, C54)."""
    return E.graphe_terme(_t(u), var(iota), iota)


# @livre Ch.II §4.1 Def.- | E II.22 L.26-30 | PDF p.73  (« famille de parties » = fonction ι↦X_ι : la notation X_ι désigne f(ι) — lecture portée en hypothèse)
def pont_fam_valeur(u="U", iota=IOTA):
    """PONT(U) := (∀X)(X∈U ⇒ valeur_famille(G,X) = valeur(G,X))   [hyp. honnête].

    Pont notationnel fam↔valeur sur la famille CONCRÈTE G (cf. docstring module :
    mur structurel, improuvable en th.22 — précédent HW/HN)."""
    G = famille_identite(u, iota)
    vX = var("X")
    return pourtout("X", impl(appartient(vX, _t(u)),
                              egal(E.valeur_famille(G, vX), E.valeur(G, vX))))


# ── {X∈U} ⊢ G(X) = X   (τ-léger : le terme-valeur est LA VARIABLE ι) ─────────
# @livre Ch.II §3.6 Crit.C54 | E II.46 L.1-14 | PDF p.97  (graphe de la fonction X↦X ; valeur en un point du domaine)
def famille_identite_valeur(u="U", c="X", iota=IOTA):
    """{c∈U} ⊢ G(c) = c.   (c = NOM — graphe_terme_valeur veut des NOMS.)

    Instance de graphe_terme_valeur (théorie dédiée C54, sanctionnée) sur le
    terme-valeur ι : T[c] = (c|ι)ι = c.  Cas encore plus simple que la famille
    Card-valuée (carte_cardinaux_valeur) : aucun τ dans le terme-valeur."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.cantor.ensembles_cantor import (
        graphe_terme_valeur)
    vu, vc = _t(u), var(c)
    res = graphe_terme_valeur(vu, var(iota), c, iota)
    assert res.conclusion == egal(E.valeur(famille_identite(u, iota), vc), vc), \
        "famille_identite_valeur : conclusion ≠ G(c)=c"
    assert res.hypotheses == frozenset({appartient(vc, vu)}), \
        "famille_identite_valeur : hypothèses ≠ {c∈U}"
    return res


# ── {PONT} ⊢ est_famille_identite(G, U)   (LA DÉCHARGE, P1) ──────────────────
# @livre Ch.II §4.1 Def.- | E II.22 L.31-36 | PDF p.73  (la famille (X)_{X∈𝔊} EST l'identité sur 𝔊)
def famille_identite_est_identite(u="U", iota=IOTA):
    """{PONT(U)} ⊢ est_famille_identite(G, U).

    Pour X∈U : fam(G,X) = G(X) (PONT instancié) puis G(X) = X (famille_identite_
    valeur) ; composition, C14, ∀-clôture sur X (X est LIÉ dans PONT, pas libre)."""
    vu = _t(u)
    G = famille_identite(u, iota)
    vX = var("X")
    hP = N.assume(pont_fam_valeur(u, iota))
    hX = N.assume(appartient(vX, vu))
    eq_pont = N.modus_ponens(hX, instancie(hP, vX))        # fam(G,X) = G(X)
    eq_val = famille_identite_valeur(u, "X", iota)          # {X∈U} ⊢ G(X) = X
    eq = composer_egalites(eq_pont, eq_val)                 # fam(G,X) = X
    res = N.generalisation("X", N.loi_deduction(appartient(vX, vu), eq))
    assert res.conclusion == est_famille_identite(G, vu), \
        "famille_identite_est_identite : conclusion ≠ est_famille_identite(G,U)"
    assert res.hypotheses == frozenset({pont_fam_valeur(u, iota)}), \
        "famille_identite_est_identite : hypothèses ≠ {PONT}"
    return res


# ── Transport : {est_famille_identite(f,U)} ⊢ C(f)  ⟼  {PONT} ⊢ C(G) ────────
def _decharge_identite(thm, u="U", iota=IOTA):
    """∀-clôture sur « f » (hypothèse abstraite d'abord déchargée par C14),
    instanciation en G, modus ponens avec famille_identite_est_identite.

    Gardes : les liants TRAVERSÉS par la substitution f:=G (X du pont, i des
    membership, z de ⊂) ne sont pas libres dans G — libres(G) = {U, ifid}."""
    H = est_famille_identite(var("f"), _t(u))
    assert thm.hypotheses == frozenset({H}), \
        "_decharge_identite : hypothèses ≠ {est_famille_identite(f,U)}"
    imp = N.loi_deduction(H, thm)                           # ⊢ H ⇒ C(f)   (clos)
    inst = instancie(N.generalisation("f", imp), famille_identite(u, iota))
    return N.modus_ponens(famille_identite_est_identite(u, iota), inst)


def _caracterisation_inter_sous_non_vide(u="U", z="z", iota=IOTA):
    """{U≠∅} ⊢ (z ∈ ⋂_{ι∈U} X_ι) ⇔ (∀i)((i∈U) ⇒ z ∈ X_i)   [X_i = fam(G,i)].

    L'ANCIEN AXIOME_INTER_FAM récupéré sur la famille CONCRÈTE G, par le pont de
    migration (CLOS) que l'on décharge de son antécédent ¬(U=∅) par C14 inverse.
    C'est ici, et ici seulement, que U≠∅ est consommée."""
    vu, vz = _t(u), var(z)
    hne = non(egal(vu, E.VIDE))
    pont = caracterisation_inter_famille_indices_non_vide(famille_identite(u, iota), vu, z)
    return instancie(N.modus_ponens(N.assume(hne), pont), vz)


def _identifie_corps(u="U", z="z", iota=IOTA):
    """({PONT} ⊢ (∀i inner_X) ⇒ (∀i inner_id), {PONT} ⊢ (∀i inner_id) ⇒ (∀i inner_X)).

    inner_X := (i∈U ⇒ z∈X_i)  et  inner_id := (i∈U ⇒ z∈i) ; le passage de l'un à
    l'autre est S6 (Leibniz) sur X_i = i, valable sous i∈U grâce à
    famille_identite_est_identite.  Liant « i » IMPOSÉ (celui des axiomes de famille)."""
    vu, vz, vi = _t(u), var(z), var("i")
    G = famille_identite(u, iota)
    inst = instancie(famille_identite_est_identite(u, iota), vi)   # (i∈U) ⇒ (X_i = i)
    s6 = N.s6(E.valeur_famille(G, vi), vi, "w", appartient(vz, var("w")))
    inner_X = impl(appartient(vi, vu), appartient(vz, E.valeur_famille(G, vi)))
    inner_id = impl(appartient(vi, vu), appartient(vz, vi))
    paire = []
    for src, dst, sens in ((inner_X, inner_id, equivalence_avant),
                           (inner_id, inner_X, equivalence_arriere)):
        h, hiU = N.assume(src), N.assume(appartient(vi, vu))
        leib = sens(N.modus_ponens(N.modus_ponens(hiU, inst), s6))
        cible = N.modus_ponens(N.modus_ponens(hiU, h), leib)
        paire.append(monotonie_pour_tout(
            N.loi_deduction(src, N.loi_deduction(appartient(vi, vu), cible)), "i"))
    return paire[0], paire[1]


# ── Membership de ⋃U et ⋂U, déchargés ────────────────────────────────────────
def enonce_membre_reunion_parties(u="U", z="z", iota=IOTA):
    vu, vz, vi = _t(u), var(z), var("i")
    return equiv(appartient(vz, E.reunion_famille(famille_identite(u, iota), vu)),
                 existe("i", et(appartient(vi, vu), appartient(vz, vi))))


# @livre Ch.II §4.1 Def.- | E II.22 L.31-36 | PDF p.73  (appartenance à ⋃𝔊, famille identité déchargée)
def membre_reunion_parties(u="U", z="z", iota=IOTA):
    """{PONT(U)} ⊢ (z ∈ ⋃U) ⇔ (∃i)(i∈U et z∈i).      ⋃U = ⋃_{ι∈U} G(ι)."""
    res = _decharge_identite(membre_reunion_ensemble("f", u, z), u, iota)
    assert res.conclusion == enonce_membre_reunion_parties(u, z, iota), \
        "membre_reunion_parties : conclusion ≠ énoncé attendu"
    assert res.hypotheses == frozenset({pont_fam_valeur(u, iota)}), \
        "membre_reunion_parties : hypothèses ≠ {PONT}"
    return res


def enonce_membre_inter_parties(u="U", z="z", iota=IOTA):
    vu, vz, vi = _t(u), var(z), var("i")
    return equiv(appartient(vz, E.inter_famille(famille_identite(u, iota), vu)),
                 pourtout("i", impl(appartient(vi, vu), appartient(vz, vi))))


# @livre Ch.II §4.1 Def.- | E II.22 L.49-53 | PDF p.73  (appartenance à ⋂𝔊 ; Déf. 2 exige I≠∅ — hypothèse de fidélité)
def membre_inter_parties(u="U", z="z", iota=IOTA):
    """{PONT(U), U≠∅} ⊢ (z ∈ ⋂U) ⇔ (∀i)(i∈U ⇒ z∈i).   (U≠∅ : fidélité Déf. 2.)

    ÉNONCÉ INCHANGÉ par la migration « ⋂ = sélection dans ⋃ » ; seule la preuve
    change.  Avant : équivalence gratuite (AXIOME_INTER_FAM inconditionnel — et
    FAUX pour U=∅) + U≠∅ attachée pour décor.  Maintenant : U≠∅ est CONSOMMÉE,
    via `_caracterisation_inter_sous_non_vide` (pont de migration), puis le corps
    est réécrit X_i ↦ i par `_identifie_corps` sous PONT."""
    star = _caracterisation_inter_sous_non_vide(u, z, iota)      # {U≠∅}
    fa_fwd, fa_bwd = _identifie_corps(u, z, iota)                # {PONT}
    res = conjonction_intro(syllogisme(equivalence_avant(star), fa_fwd),
                            syllogisme(fa_bwd, equivalence_arriere(star)))
    assert res.conclusion == enonce_membre_inter_parties(u, z, iota), \
        "membre_inter_parties : conclusion ≠ énoncé attendu"
    assert res.hypotheses == frozenset({pont_fam_valeur(u, iota),
                                        non(egal(_t(u), E.VIDE))}), \
        "membre_inter_parties : hypothèses ≠ {PONT, U≠∅}"
    return res


# ── Inclusions caractéristiques, déchargées ──────────────────────────────────
# @livre Ch.II §4.1 Prop.- | E II.22 L.31-36 | PDF p.73  (chaque élément de 𝔊 est inclus dans ⋃𝔊)
def partie_incluse_reunion_parties(u="U", c="c", iota=IOTA):
    """{PONT(U)} ⊢ (c∈U) ⇒ (c ⊂ ⋃U).      (c = NOM.)"""
    res = _decharge_identite(partie_incluse_reunion("f", u, c), u, iota)
    vu, vc = _t(u), var(c)
    assert res.conclusion == impl(appartient(vc, vu),
        inclus(vc, E.reunion_famille(famille_identite(u, iota), vu))), \
        "partie_incluse_reunion_parties : conclusion ≠ (c∈U)⇒(c⊂⋃U)"
    assert res.hypotheses == frozenset({pont_fam_valeur(u, iota)}), \
        "partie_incluse_reunion_parties : hypothèses ≠ {PONT}"
    return res


def partie_incluse_reunion_parties_t(tc, u="U", iota=IOTA):
    """{PONT(U)} ⊢ (C∈U) ⇒ (C ⊂ ⋃U)  pour un TERME C (motif _inst_gen).

    ∀-clôture sur le nom frais « cfid » (non libre dans PONT) puis instanciation ;
    garde : le liant traversé « z » (de ⊂) non libre dans C."""
    gen = N.generalisation("cfid", partie_incluse_reunion_parties(u, "cfid", iota))
    return instancie(gen, _t(tc))


# @livre Ch.II §4.1 Prop.- | E II.22 L.49-53 | PDF p.73  (⋂𝔊 est incluse dans chaque élément de 𝔊)
def inter_incluse_partie_parties(u="U", c="c", iota=IOTA):
    """{PONT(U)} ⊢ (c∈U) ⇒ (⋂U ⊂ c).      (c = NOM ; AUCUNE hypothèse U≠∅.)

    ÉNONCÉ RENFORCÉ (2026-07-26, audit dette 2/3) : l'hypothèse U≠∅ que portaient
    et l'avant-migration et la première rédaction post-migration est TOMBÉE.  Elle
    était GRATUITE des deux côtés, pour deux raisons indépendantes, et c'est la
    LOI N.1 (« le témoin d'indice est gratuit quand la preuve tient déjà un
    élément de l'intersection ») :
      · on PART de z∈⋂U — l'élimination `inter_donne_membres` est INCONDITIONNELLE ;
      · l'antécédent c∈U EST lui-même le témoin d'indice qui manquerait.
    Avant-migration : U≠∅ n'était qu'ATTACHÉE par affaiblissement C14 (décoration
    d'énoncé, ancien `_attache_non_vide`).  Après : elle était HÉRITÉE de
    `membre_inter_parties` parce que la preuve passait par l'équivalence complète —
    or seul le sens ⇒ est utilisé ici, et lui est gratuit.  On repasse donc par le
    lemme frère `inter_incluse_partie`, RÉPARÉ par la migration sur la seule
    élimination et resté à la seule hypothèse `est_famille_identite`.
    Ne pas confondre avec `membre_inter_parties` : là, le sens ⇐ CONCLUT z∈⋂U, le
    témoin n'est plus gratuit et U≠∅ est réellement load-bearing (l'énoncé y est
    RÉFUTABLE à U=∅, cf. le test miroir)."""
    res = _decharge_identite(inter_incluse_partie("f", u, c), u, iota)
    vu, vc = _t(u), var(c)
    assert res.conclusion == impl(appartient(vc, vu),
        inclus(E.inter_famille(famille_identite(u, iota), vu), vc)), \
        "inter_incluse_partie_parties : conclusion ≠ (c∈U)⇒(⋂U⊂c)"
    assert res.hypotheses == frozenset({pont_fam_valeur(u, iota)}), \
        "inter_incluse_partie_parties : hypothèses ≠ {PONT}"
    return res


__all__ = ["IOTA", "famille_identite", "pont_fam_valeur",
           "famille_identite_valeur", "famille_identite_est_identite",
           "enonce_membre_reunion_parties", "membre_reunion_parties",
           "enonce_membre_inter_parties", "membre_inter_parties",
           "partie_incluse_reunion_parties", "partie_incluse_reunion_parties_t",
           "inter_incluse_partie_parties"]
