"""Classer une hypothèse RÉSIDUELLE : déchargeable / réfutable / indépendante / inconnu.

Outil SUR le corpus (pas une notion du livre) : aucun marqueur `@livre`, aucun
`Theoreme` fabriqué, noyau et `subst` intouchés, `theorie_ensembles()` = 22.

LES QUATRE CLASSES (h = hypothèse résiduelle, T0 = la théorie des 22 axiomes)

  « déchargeable »  A_T0 ⊢ h   → le « mur » était FANTÔME : le théorème qui porte
                                 h se ferme par coupure.
  « réfutable »     A_T0 ⊢ ¬h  → TOUT théorème portant h est VACUEUX (certificat
                                 exigé : {h} ⊢ F et ⊢ ¬F).
  « indépendante »  ni l'un ni l'autre → il manque un AXIOME (ou un encodage) ;
                                 aucun effort de preuve n'y changera rien.
  « inconnu »       pas encore tranché.

⚠️ LE 4ᵉ CAS EST LE PLUS IMPORTANT : « inconnu » N'EST PAS « bloqué ». C'est la
classe à RE-MESURER après CHAQUE fix d'infrastructure. Dans ce dépôt, « bloqué »
s'est révélé FAUX NEUF fois au 2 août 2026 — six avant la semaine instrumentée
(ev. 1, 8, 9, 10, 36, 37 du journal ; « six » était le compte exact quand ce
docstring fut écrit), trois pendant (ev. 61, 64, 65). L'ÉNUMÉRATION fait foi,
pas le compte : la liste canonique vit dans verite/README.md §4. Le fix `subst`
du 24 juil. 2026 a percé d'un coup le mur « C62 récursion-fonction » et rendu
tractables des items catalogués « verrou-τ ». Un « inconnu » est une DETTE DE
MESURE, pas un verdict : on le re-passe à `classer` avec un prouveur plus fort ou
après réparation de l'encodage. Ne jamais l'archiver comme un mur.

────────────────────────────────────────────────────────────────────────────────
LE CRITÈRE SYNTAXIQUE D'INDÉPENDANCE, ET SON PIÈGE (MESURÉ)

`symboles_libres(h, T0)` rend les symboles de fonction de h qu'AUCUN des 22
axiomes ne mentionne. Non vide ⇒ argument de RÉINTERPRÉTATION disponible : rien
ne contraint ces symboles, on les réinterprète librement dans un modèle de T0.
C'est un INDICE d'indépendance — PAS une preuve :

    MESURE DU 26 juil. 2026 — symboles_libres( est_bien_ordonne(R_G≤, ℕ) )
                            = {'G_ordre_NN'}   (NON VIDE)
    et pourtant `bo_graphe_NN()` la DÉMONTRE, close, 0 hypothèse.

Le critère seul aurait donc produit un faux mur DE PLUS. D'où l'ordre imposé
dans `classer` : réfutation certifiée, puis PREUVE, puis seulement le critère
syntaxique. Sans prouveur injecté, « indépendante » ne repose QUE sur ce critère —
verdict à re-passer dès qu'un prouveur existe.

────────────────────────────────────────────────────────────────────────────────
LES SCHÉMAS DE RÉFUTATION SONT INSTANCIÉS, JAMAIS DEVINÉS

Un contre-théorème du dépôt est un SCHÉMA paramétré (ici en ses LIANTS). On lit les
paramètres RÉELS par décomposition structurelle de h, on RECONSTRUIT le schéma sur
ces paramètres et on exige `schema(params) == h` avant de produire le certificat ;
énumérer des noms devinés donnerait des faux négatifs silencieux. Le couple rendu
par `refutation_certifiee` est EXACTEMENT le certificat d'un `echec.Echec` de
classe E2 (vacuité), témoin ∅∈∅ compris. Le prouveur, lui, est INJECTÉ et jamais
câblé : l'outil reste utilisable sans lancer la moindre preuve.

⚠️ CE QUE `classer` NE MESURE PAS. D'un certificat rendu par le prouveur il vérifie
type, clôture et conclusion — PAS Ax(D). Un prouveur consommant une théorie DÉDIÉE
(motif massif : `Theorie(` apparaît 301× dans 57 fichiers) passerait pour
« déchargeable » à tort. Composer avec `verite.axiomes_consommes.invariant_reel`
sur le MÊME thunk : c'est une classe E4 (dette), pas un déchargement.
"""
from __future__ import annotations

import functools
import inspect
import itertools
import time

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Formule, Terme, non,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N

#: Les quatre valeurs de retour de `classer` — aucune autre.
CLASSES = ("dechargeable", "refutable", "independante", "inconnu")

#: Au-delà de ce nombre d'atomes distincts, le garde-fou de contingence
#: (2^k évaluations) est ABANDONNÉ : il rend « contingent » sans avoir mesuré.
MAX_ATOMES = 12


# ── Extraction ROBUSTE des symboles (parcours structurel, jamais de regex) ─────
def symboles(objet) -> frozenset[str]:
    """Les symboles de fonction (nœuds `app`) d'une `Formule` ou d'un `Terme`.

    Parcours itératif à mémo d'IDENTITÉ : les sous-arbres sont PARTAGÉS (subst est
    mémoïsée) et les termes cardinaux sont profondément imbriqués — un parcours
    naïf en arbre y explose. Rien n'est jamais rendu textuel (`repr` d'un terme
    cardinal = plusieurs 10^12 signes)."""
    if not isinstance(objet, (Formule, Terme)):
        raise TypeError("symboles : Formule ou Terme attendu, reçu " + type(objet).__name__)
    acc: set[str] = set()
    vus: set[int] = set()
    pile = [objet]
    while pile:
        o = pile.pop()
        if id(o) in vus:
            continue
        vus.add(id(o))
        if isinstance(o, Terme):
            if o.tag == "app":
                acc.add(o.nom)
            pile.extend(o.args)          # 'tau' : args = (Formule,) ; 'var' : ()
        elif isinstance(o, Formule):
            pile.extend(o.termes)
            pile.extend(o.sous)
        else:                             # ne peut arriver que sur un arbre corrompu
            raise TypeError("symboles : nœud inattendu " + type(o).__name__)
    return frozenset(acc)


@functools.lru_cache(maxsize=64)
def _symboles_axiomes(axiomes: frozenset) -> frozenset[str]:
    return frozenset().union(*(symboles(a) for a in axiomes)) if axiomes else frozenset()


def symboles_theorie(T0: N.Theorie) -> frozenset[str]:
    """Les symboles de fonction mentionnés par les axiomes EXPLICITES de T0."""
    return _symboles_axiomes(frozenset(T0.axiomes))


def symboles_libres(h: Formule, T0: N.Theorie) -> frozenset[str]:
    """Les symboles de h qu'AUCUN axiome de T0 ne mentionne.

    Non vide ⇒ un argument de réinterprétation est DISPONIBLE (indice
    d'indépendance), pas une preuve — cf. le contre-exemple mesuré en tête de
    module. Ne comptent que les symboles de FONCTION (`app`) : les axiomes étant
    clos, TOUTE variable libre de h serait « libre » et le critère se
    déclencherait sur presque tout."""
    return symboles(h) - symboles_theorie(T0)


# ── Garde-fou : h doit être CONTINGENTE au niveau propositionnel ──────────────
def _atomes(f: Formule, out: list) -> None:
    if f.tag in ("non", "ou"):
        for g in f.sous:
            _atomes(g, out)
    else:                                 # '=', 'in', 'exists' : opaques
        out.append(f)


def _evaluer(f: Formule, env: dict) -> bool:
    if f.tag == "non":
        return not _evaluer(f.sous[0], env)
    if f.tag == "ou":
        return _evaluer(f.sous[0], env) or _evaluer(f.sous[1], env)
    return env[f]


def contingente(h: Formule) -> bool:
    """h n'est ni une tautologie ni une contradiction PROPOSITIONNELLE.

    Abstraction : ¬ et ∨ sont interprétés, tout le reste est un atome opaque —
    sauf les atomes de la forme (T = T), forcés VRAIS (Théorème 1, réflexivité).
    Un h non contingent est prouvable (ou réfutable) SANS aucun axiome : lui
    attribuer « indépendante » serait faux. Au-delà de MAX_ATOMES atomes libres,
    on rend True SANS avoir mesuré (le garde-fou est alors inactif)."""
    ats: list = []
    try:
        _atomes(h, ats)
        fixe = {a: True for a in ats if a.tag == "=" and a.termes[0] == a.termes[1]}
        libres = [a for a in dict.fromkeys(ats) if a not in fixe]
        if len(libres) > MAX_ATOMES:
            return True
        vus = set()
        for bits in itertools.product((False, True), repeat=len(libres)):
            env = dict(fixe)
            env.update(zip(libres, bits))
            vus.add(_evaluer(h, env))
            if len(vus) == 2:
                return True
    except RecursionError:                # trop profond : garde-fou INACTIF (ne bloque pas)
        return True
    return False


# ── Schémas de réfutation CERTIFIÉS du dépôt (instanciés, jamais devinés) ──────
#
# ⚠️ 2026-07-26 — LE SCHÉMA « H-graphe » A ÉTÉ RETIRÉ, ET C'EST UN PROGRÈS.
# Il s'appuyait sur `hypothese_graphes_produit_vide_refutee` : { (∀F)(F∈∏(u,∅) ⇒
# est_un_graphe F) } ⊢ ∅∈∅ — un théorème du DÉFAUT de `AXIOME_PRODUIT_FAM`, dont le
# conjoint de tête « F ⊂ I × ⋃X_ι » (E II.32 Déf. 1) avait été perdu à la
# transcription. L'axiome RÉPARÉ rend cette hypothèse DÉMONTRABLE (`produit_graphe`) :
# garder sa réfutation rendrait la théorie incohérente. C'est le cas d'école du
# 4ᵉ verdict : un « réfutable » qui bascule en « déchargeable » après un fix
# d'encodage. Il est REMPLACÉ ici, et non simplement supprimé — sans quoi le
# registre serait vide et la machinerie de certification ne serait plus mesurée.
def _schema_h_univ(gx="X", gi="x"):
    """H-univ := (∃X)(∀x)(x ∈ X)  — l'existence d'un ENSEMBLE UNIVERSEL.

    Réfutée par Russell dans le dépôt (`pas_ensemble_universel`, E II.6 Rem. →
    E II.7). Paramétré par ses DEUX liants, car les α-variants sont des formules
    DISTINCTES dans ce noyau."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
        appartient, pourtout, existe, var)
    return existe(gx, pourtout(gi, appartient(var(gi), var(gx))))


def _appariement_h_univ(h: Formule):
    """(gx, gi) si h EST une instance de H-univ ; None sinon.

    L'arbre est (∃X)¬(∃x)¬(x∈X) : on lit gx (lieur du ∃ externe) et gi (lieur du
    ∃ interne du ∀) dans la STRUCTURE, on RECONSTRUIT le schéma sur eux, et c'est
    l'ÉGALITÉ qui tranche, pas la ressemblance — énumérer des noms devinés
    donnerait des faux négatifs silencieux."""
    try:
        gx = h.lieur                                          # (∃X)…
        gi = h.sous[0].sous[0].lieur                          # ∀x = ¬(∃x)¬…
        if _schema_h_univ(gx, gi) != h:
            return None
    except Exception:                     # forme étrangère au schéma
        return None
    return gx, gi


def _certificat_h_univ(gx, gi):
    """{ H-univ } ⊢ ∅∈∅.   (ex falso depuis ⊢ ¬H-univ, S2.)

    ⚠️ DETTE DÉCLARÉE (classe E4, cf. tête de module) : `pas_ensemble_universel`
    consomme, outre les 22 axiomes, l'instance de SÉLECTION S8 caractérisant
    R_b = {x∈b | x∉x} dans une THÉORIE DÉDIÉE (motif `theorie_diagonale_cantor`).
    La réfutation reste certifiée par le noyau, mais elle n'est pas « sur T0
    seule » : le composer avec `verite.axiomes_consommes.invariant_reel` pour
    mesurer cette dette. L'ancien schéma H-graphe, lui, tenait sur T0 seule."""
    from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ii_1_collectivisantes import (
        ensembles_pas_ensemble_universel as R)
    from outils_ia.verite.echec import temoin_absurdite
    neg = R.pas_ensemble_universel()                          # ⊢ ¬H-univ
    h = N.assume(_schema_h_univ(gx, gi))                      # { H } ⊢ H
    # ex falso : ¬H ⇒ (H ⇒ ∅∈∅)
    return N.modus_ponens(h, N.modus_ponens(
        neg, N.s2(non(h.conclusion), temoin_absurdite())))


#: (nom, appariement, certificat).  Un schéma s'ajoute ici, jamais dans `classer`.
SCHEMAS_REFUTATION = (("H-univ ((∃X)(∀x)(x∈X), Russell, E II.6-7)",
                       _appariement_h_univ, _certificat_h_univ),)


def _negation_close(f: Formule, T0: N.Theorie):
    """⊢ ¬f, close, sur les SEULS axiomes de T0 (témoin canonique ∅∈∅).

    Miroir de `echec.negation_temoin_close`, mais PARAMÉTRÉ par T0 ; refait à
    chaque appel par les primitives publiques du noyau.

    Le témoin est LU dans `echec.temoin_absurdite()` et non ré-écrit ici : les
    deux modules doivent parler du MÊME ∅∈∅, sans quoi le couple rendu par
    `refutation_certifiee` cesserait silencieusement d'être un certificat E2
    (`echec._v_E2` compare la conclusion à `echec.temoin_absurdite()`)."""
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
        instancie)
    from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import (
        ensembles_abrege as E)
    from outils_ia.verite.echec import temoin_absurdite
    if f != temoin_absurdite():
        return None
    return instancie(N.axiome(T0, E.AXIOME_VIDE), E.VIDE)


def refutation_certifiee(h: Formule, T0: N.Theorie):
    """(absurde, negation) si h est une instance d'un schéma de réfutation ; None sinon.

    `absurde` : {h} ⊢ F  (h EXACTEMENT, seule hypothèse) ; `negation` : ⊢ ¬F
    (close, sur les seuls axiomes de T0). Les deux sont RE-VÉRIFIÉS ici ; au
    moindre écart on rend None (jamais un certificat de confiance)."""
    for _nom, apparier, certifier in SCHEMAS_REFUTATION:
        params = apparier(h)
        if params is None:
            continue
        try:
            absurde = certifier(*params)
        except Exception:                 # collision de liants, terme exotique…
            continue
        if not isinstance(absurde, N.Theoreme) or absurde.hypotheses != frozenset({h}):
            continue
        negation = _negation_close(absurde.conclusion, T0)
        if negation is not None and negation.est_clos \
                and negation.conclusion == non(absurde.conclusion):
            return absurde, negation
    return None


# ── Le prouveur INJECTÉ : appelé `prouveur(cible, T0)`, résultat RE-VÉRIFIÉ ────
def prouve(prouveur, cible: Formule, T0: N.Theorie, reste=None):
    """Le `Theoreme` du noyau CLOS de conclusion `cible`, ou None.

    Ce qui rentre est traité comme non fiable : type, clôture et conclusion sont
    re-vérifiés. Une exception du prouveur vaut « pas de preuve ». `reste` n'est
    transmis que si le prouveur déclare un paramètre `timeout`."""
    kw = {}
    try:
        if reste is not None and "timeout" in inspect.signature(prouveur).parameters:
            kw["timeout"] = reste
    except (TypeError, ValueError):
        pass
    try:
        th = prouveur(cible, T0, **kw)
    except Exception:
        return None
    if not isinstance(th, N.Theoreme) or not th.est_clos or th.conclusion != cible:
        return None
    return th


def classer(h: Formule, T0: N.Theorie, prouveur=None, timeout=None) -> str:
    """L'une de CLASSES, exactement.

    Ordre IMPOSÉ (cf. le contre-exemple bo(≤,ℕ) en tête de module) :
      1. réfutation certifiée par schéma  (gratuite, décisive) ;
      2. A_T0 ⊢ h   par le prouveur injecté ;
      3. A_T0 ⊢ ¬h  par le prouveur injecté ;
      4. critère syntaxique de réinterprétation, sous garde-fou de contingence ;
      5. « inconnu » — à RE-MESURER, ce n'est pas un mur.
    `timeout` (secondes) borne le temps TOTAL passé en appels de prouveur ; il est
    transmis au prouveur s'il accepte un paramètre `timeout`."""
    if not isinstance(h, Formule):
        raise TypeError("classer : Formule attendue, reçu " + type(h).__name__)
    if not isinstance(T0, N.Theorie):
        raise TypeError("classer : Theorie attendue, reçu " + type(T0).__name__)

    if refutation_certifiee(h, T0) is not None:
        return "refutable"

    if prouveur is not None:
        debut = time.perf_counter()
        for cible, verdict in ((h, "dechargeable"), (non(h), "refutable")):
            reste = None if timeout is None else timeout - (time.perf_counter() - debut)
            if reste is not None and reste <= 0:
                return "inconnu"          # budget épuisé : PAS un verdict
            if prouve(prouveur, cible, T0, reste) is not None:
                return verdict

    if symboles_libres(h, T0) and contingente(h):
        return "independante"
    return "inconnu"


__all__ = ["CLASSES", "MAX_ATOMES", "SCHEMAS_REFUTATION", "symboles", "symboles_theorie",
           "symboles_libres", "contingente", "refutation_certifiee", "prouve", "classer"]
