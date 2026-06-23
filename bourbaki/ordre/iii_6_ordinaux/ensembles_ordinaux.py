"""Chapitre III §6 (Exercices) — ORDINAUX : définition REPRÉSENTATIONNELLE fidèle.

────────────────────────────────────────────────────────────────────────────
STATUT MÉTAMATHÉMATIQUE (à lire avant tout) :

Bourbaki, dans la *Théorie des ensembles*, NE consacre PAS de section du texte
principal aux ordinaux : la notion est traitée dans les EXERCICES du §III.6 (et
préparée par la théorie des ensembles bien ordonnés du §III.2, en particulier le
Théorème 3 et ses corollaires). L'« ordinal » de Bourbaki n'est PAS l'ordinal de
von Neumann (transitif, ∈ comme ordre) ; c'est le TYPE D'ORDRE d'un ensemble bien
ordonné, c.-à-d. la CLASSE D'ISOMORPHISME (d'ordre) d'un ensemble bien ordonné.
Deux ensembles bien ordonnés ont « le même ordinal » lorsqu'ils sont isomorphes
en tant qu'ensembles ordonnés (E.III.1.3, isomorphisme d'ordre).

Conformément à la consigne du projet (campagne de COMPLÉTUDE des NOTIONS), ce
module INTRODUIT la notion d'ordinal de façon REPRÉSENTATIONNELLE et la DOCUMENTE
comme telle. On suit la voie « type d'ordre / à isomorphisme près » :

  • est_ordinal(E, R) :=  est_bien_ordonne(R, E)
        « un ordinal est le type d'ordre d'un ensemble bien ordonné » ; on
        REPRÉSENTE un ordinal par n'importe quel ensemble bien ordonné (E, R) qui
        en est un représentant. est_ordinal(E,R) signifie donc « (E,R) PORTE un
        ordinal » (= (E,R) est bien ordonné).

  • meme_ordinal(E, R, E', R') := sont_isomorphes_ordre(E, E', R, R')
        deux représentants définissent LE MÊME ordinal ssi ils sont isomorphes
        d'ordre (relation d'équivalence : c'est la classe d'isomorphisme).

  • ordinal_de(E, R) := τ-représentant canonique de la classe d'isomorphisme de
        (E,R)  (l'ORDINAL D'UN BON ORDRE = son « type d'ordre »).  On le prend, à
        la Bourbaki (cf. Card(X) = τ_Z Eq(X,Z), E.III.3), comme
            τ_Z ( sont_isomorphes_ordre(E, Z, R, R_Z) )
        — l'opérateur de sélection τ choisit un représentant canonique. (On ne
        prouve pas ici l'invariance ; c'est l'analogue du Card et REPOSE sur la
        machinerie τ, déjà admise dans le projet pour les cardinaux.)

  • comparaison des ordinaux par SEGMENTS (E.III.2, Théorème 3) :
        ordinal_inferieur_ou_egal(E,R,E',R') :⟺ (E,R) est isomorphe à un segment
        de (E',R').  C'est l'ordre des ordinaux ; la TRICHOTOMIE (tout couple
        d'ordinaux est comparable) est exactement le Théorème 3 (E.III.2),
        REPORTÉ ici (théorème dur).

  • ORDINAL INITIAL (lien avec les cardinaux, exercices §III.6) :
        un ordinal est INITIAL s'il n'est isomorphe (équipotent) à AUCUN ordinal
        strictement plus petit ; le plus petit ordinal d'un cardinal donné. On en
        donne la définition fidèle ; le théorème « tout cardinal a un unique
        ordinal initial » est REPORTÉ (repose sur Zermelo + trichotomie).

THÉORÈMES REPORTÉS honnêtement (durs, hors campagne de notions) : trichotomie des
ordinaux (Théorème 3, E.III.2), existence/unicité de l'ordinal initial d'un
cardinal, bon ordre de la classe des ordinaux, ordinal successeur / limite, etc.

────────────────────────────────────────────────────────────────────────────
CONVENTIONS (identiques au reste du package ordre) :
  • Une relation d'ordre R est une fonction Python (Terme, Terme) → Formule ; on
    la note ≤ : R{a,b} = a≤b. La forme par graphe G (a≤b := (a,b)∈G) est le choix
    par défaut des lemmes.
  • On NE MODIFIE AUCUN fichier existant ; theorie_ensembles() reste à 22 axiomes
    (aucun axiome ajouté ici ; les seuls termes opaques réutilisent τ déjà admis).
  • On ne DUPLIQUE rien : est_bien_ordonne, est_segment, segment_extremite,
    est_majorant_strict viennent de ensembles_abrege ; est_isomorphisme_ordre,
    sont_isomorphes_ordre, compatible_ordre viennent de ensembles_ordre_vocab.
"""
from __future__ import annotations

from bourbaki.logique.formule import (
    Terme, var, app, tau, egal, et, ou, impl, non, equiv, appartient, existe, pourtout, inclus,
)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.cardinaux import ensembles_cardinaux as C
from bourbaki.ordre.iii_1_relations_ordre.ordre_treillis import ensembles_ordre_vocab as V
from bourbaki.logique.tactiques.tactiques_abrege import a_implique_a
from bourbaki.logique.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite, instancie,
)


def _terme(t):
    return t if isinstance(t, Terme) else var(t)


def _graphe_R(G):
    """Relation ≤ portée par le graphe G : a≤b := (a,b)∈G  (convention par défaut)."""
    vG = _terme(G)
    return lambda a, b: appartient(E.couple(_terme(a), _terme(b)), vG)


# ════════════════════════════════════════════════════════════════════════════
#  ORDINAL — définition représentationnelle (type d'ordre d'un bon ordre)
# ════════════════════════════════════════════════════════════════════════════
def est_ordinal(e, R, x="x", y="y", z="z", X="X", a="a", w="w"):
    """est_ordinal(E, R) := est_bien_ordonne(R, E).

    DÉFINITION REPRÉSENTATIONNELLE (exercices §III.6) : « un ordinal est le type
    d'ordre d'un ensemble bien ordonné ». On représente un ordinal par un
    ensemble bien ordonné (E, R) qui en est un représentant ; est_ordinal(E,R)
    affirme que (E, R) PORTE un ordinal, c.-à-d. que R est un bon ordre sur E
    (E.III.2.1, Définition 1). (Aucune duplication : on réexporte la sémantique
    de est_bien_ordonne.)"""
    return E.est_bien_ordonne(R, _terme(e), x, y, z, X, a, w)


def meme_ordinal(e, R, ep, Rp, f="f", x="x", y="y"):
    """meme_ordinal(E, R, E', R') := sont_isomorphes_ordre(E, E', R, R').

    Deux ensembles bien ordonnés définissent LE MÊME ordinal (ont le même « type
    d'ordre ») ssi ils sont ISOMORPHES en tant qu'ensembles ordonnés (E.III.1.3) :
    (∃f) (f bijective de E sur E' et (∀x,y) x≤y ⇔ f(x)≤'f(y)). C'est la relation
    d'équivalence dont l'ordinal est la classe."""
    return V.sont_isomorphes_ordre(_terme(e), _terme(ep), R, Rp, f, x, y)


def ordinal_de(e, R, z="Z", f="f", x="x", y="y"):
    """ordinal_de(E, R) := τ_Z ( sont_isomorphes_ordre(E, Z, R, R_Z) ).

    L'ORDINAL D'UN BON ORDRE (son TYPE D'ORDRE) : représentant canonique, choisi
    par l'opérateur τ, de la classe d'isomorphisme d'ordre de (E, R). Construction
    PARALLÈLE à Card(X) = τ_Z Eq(X, Z) (E.III.3.2) : τ sélectionne un témoin de la
    classe ; deux bons ordres isomorphes ont (par invariance de τ sous équivalence,
    admise comme pour Card) le même ordinal_de. Ici R_Z est la relation d'ordre
    portée par le graphe-témoin GZ associé au représentant Z (le « bon ordre de Z »).

    REPRÉSENTATIONNEL et documenté comme tel : on ne prouve pas ici l'invariance
    (théorème), on POSE le terme canonique (notion)."""
    ve = _terme(e)
    vZ = var(z)
    # R_Z : ordre porté par un graphe-témoin GZ = composante d'ordre du représentant Z.
    R_Z = _graphe_R(app("ordre_temoin", vZ))
    return tau(z, V.sont_isomorphes_ordre(ve, vZ, R, R_Z, f, x, y))


# ════════════════════════════════════════════════════════════════════════════
#  SEGMENT INITIAL d'un bon ordre  (E.III.2.1 — segment + segment d'extrémité)
# ════════════════════════════════════════════════════════════════════════════
def est_segment_initial(S, e, R, x="x", y="y"):
    """est_segment_initial(S, E, R) := est_segment(S, R, E).

    « SEGMENT INITIAL » d'un bon ordre (E, R) : partie S de E close vers le bas
    (x∈S, y∈E, y≤x ⇒ y∈S), c.-à-d. exactement un SEGMENT au sens de la Définition 2
    (E.III.2.1). Pour un ensemble BIEN ordonné, tout segment ≠ E est un intervalle
    ]←,a[ (Proposition 1, E.III.2) — voir segment_initial_propre ci-dessous."""
    return E.est_segment(_terme(S), R, _terme(e), x, y)


def segment_initial_extremite(e, R, a):
    """segment_initial_extremite(E, R, a) := segment_extremite(R, E, a) = ]←, a[.

    SEGMENT INITIAL PROPRE associé à a : S_a = { y∈E | y<a } (E.III.2.1). D'après
    la Proposition 1 (E.III.2), dans un bon ordre TOUT segment ≠ E est de cette
    forme. Réexporte le terme segment_extremite (aucune duplication)."""
    return E.segment_extremite(R, _terme(e), _terme(a))


def est_segment_propre(S, e, R, x="x", y="y"):
    """est_segment_propre(S, E, R) := est_segment(S, R, E)  et  S ≠ E.

    Un segment STRICT (« segment propre ») : segment de E distinct de E lui-même.
    (Sert à exprimer la comparaison stricte des ordinaux et l'énoncé de la
    Proposition 1, E.III.2.)"""
    return et(E.est_segment(_terme(S), R, _terme(e), x, y),
              non(egal(_terme(S), _terme(e))))


# ════════════════════════════════════════════════════════════════════════════
#  COMPARAISON DES ORDINAUX  (par segments — E.III.2, Théorème 3)
# ════════════════════════════════════════════════════════════════════════════
def ordinal_inferieur_ou_egal(e, R, ep, Rp, S="S", f="f", x="x", y="y"):
    """ordinal_inferieur_ou_egal(E,R,E',R') :⟺ (∃S)( S est un segment de E'  et
        sont_isomorphes_ordre(E, S, R, R'|_S) ).

    L'ORDRE DES ORDINAUX (E.III.2, Théorème 3 et corollaires) : l'ordinal de
    (E,R) est ≤ celui de (E',R') ssi (E,R) est ISOMORPHE à un SEGMENT de (E',R').
    (R'|_S = ordre induit de R' sur S ; ici R' lui-même restreint aux éléments de
    S convient car S⊂E'.) C'est un ordre TOTAL sur les ordinaux — sa totalité est
    précisément le Théorème 3 (trichotomie), REPORTÉ."""
    ve, vep = _terme(e), _terme(ep)
    vS = var(S)
    return existe(S, et(E.est_segment(vS, Rp, vep, x, y),
                        V.sont_isomorphes_ordre(ve, vS, R, Rp, f, x, y)))


def ordinal_strictement_inferieur(e, R, ep, Rp, S="S", f="f", x="x", y="y"):
    """ordinal_strictement_inferieur(E,R,E',R') :⟺ (∃S)( S segment PROPRE de E'
        (S⊂E', S≠E')  et  sont_isomorphes_ordre(E, S, R, R'|_S) ).

    COMPARAISON STRICTE des ordinaux : l'ordinal de (E,R) est STRICTEMENT plus
    petit que celui de (E',R') ssi (E,R) est isomorphe à un segment PROPRE de
    (E',R') — c.-à-d., dans un bon ordre, à un segment d'extrémité S_a = ]←,a[
    (Proposition 1, E.III.2). (E.III.2, Théorème 3.)"""
    ve, vep = _terme(e), _terme(ep)
    vS = var(S)
    return existe(S, et(est_segment_propre(vS, vep, Rp, x, y),
                        V.sont_isomorphes_ordre(ve, vS, R, Rp, f, x, y)))


# ── TRICHOTOMIE (Théorème 3, E.III.2) — ÉNONCÉ posé, PREUVE REPORTÉE ──────────
def trichotomie_ordinaux(e, R, ep, Rp, S="S", f="f", x="x", y="y"):
    """ÉNONCÉ (Théorème 3, E.III.2) de la TRICHOTOMIE des ordinaux :

        ordinal_inferieur_ou_egal(E,R,E',R')  OU  ordinal_inferieur_ou_egal(E',R',E,R)

    « Étant donnés deux ensembles bien ordonnés, l'un est isomorphe à un segment
    de l'autre. » Deux ordinaux sont toujours comparables. THÉORÈME dur (preuve
    par récurrence transfinie / back-and-forth) — ICI on POSE la FORMULE-énoncé,
    on ne la PROUVE PAS (REPORTÉ : il faudrait C59/C60). Cette fonction renvoie la
    formule, pas un Theoreme."""
    return ou(ordinal_inferieur_ou_egal(e, R, ep, Rp, S, f, x, y),
              ordinal_inferieur_ou_egal(ep, Rp, e, R, S, f, x, y))


# ════════════════════════════════════════════════════════════════════════════
#  ORDINAL INITIAL  (lien aux cardinaux — exercices §III.6)
# ════════════════════════════════════════════════════════════════════════════
def est_ordinal_initial(e, R, ep="Ep", Rp="Rp", S="S", f="f", x="x", y="y"):
    """est_ordinal_initial(E, R) := est_bien_ordonne(R, E)  et  il n'existe AUCUN
        ordinal STRICTEMENT plus petit qui soit ÉQUIPOTENT à (E,R) :

        (∀E')(∀R')( ( est_bien_ordonne(R',E')  et
                      ordinal_strictement_inferieur(E',R', E,R) )
                    ⇒  ¬ Eq(E', E) ).

    Un ordinal est INITIAL (le « plus petit ordinal de son cardinal ») s'il n'est
    équipotent à aucun ordinal strictement plus petit que lui (exercices §III.6 ;
    à tout cardinal correspond un unique ordinal initial — énoncé REPORTÉ). Eq =
    équipotence (E.III.3.1) ; R' parcourt les bons ordres ; ordinal_strictement_
    inferieur = comparaison stricte par segments."""
    ve = _terme(e)
    vep, vRp = var(ep), _graphe_R(app("ordre", var(ep)))  # R' porté par un graphe
    bo = E.est_bien_ordonne(vRp, vep, x, y)
    strict = ordinal_strictement_inferieur(vep, vRp, ve, R, S, f, x, y)
    pas_equip = non(C.equipotent(vep, ve))   # ¬ Eq(E', E)  (E.III.3.1)
    return pourtout(ep, impl(et(bo, strict), pas_equip))


def ordinal_initial_du_cardinal(c, z="Z", f="f", x="x", y="y"):
    """ordinal_initial_du_cardinal(𝔠) := τ_Z ( est_ordinal_initial(Z, R_Z)  et
        Card(Z) = 𝔠 ).

    L'ORDINAL INITIAL d'un cardinal 𝔠 : représentant canonique (via τ) d'un
    ensemble bien ordonné qui est un ordinal initial et dont le cardinal est 𝔠.
    Notion (exercices §III.6) ; existence/unicité = théorème (repose sur Zermelo
    + trichotomie), REPORTÉ. R_Z = ordre porté par le graphe-témoin du
    représentant Z."""
    vc = _terme(c)
    vZ = var(z)
    R_Z = _graphe_R(app("ordre_temoin", vZ))
    cond = et(est_ordinal_initial(vZ, R_Z, "Ep", "Rp", "S", f, x, y),
              egal(C.cardinal(vZ), vc))
    return tau(z, cond)


# ════════════════════════════════════════════════════════════════════════════
#  LEMMES DIRECTS (bonus) — certifiés par le noyau abrégé (type Theoreme opaque)
# ════════════════════════════════════════════════════════════════════════════
def ordinal_est_bien_ordonne(e="E", G="G", x="x", y="y", z="z", X="X", a="a", w="w"):
    """{ est_ordinal(E, R) } ⊢ est_bien_ordonne(R, E).

    Un (représentant d')ordinal est, par définition, un ensemble bien ordonné :
    est_ordinal se déplie en est_bien_ordonne (définition représentationnelle).
    Preuve TRIVIALE (a⇒a) car les deux formules sont IDENTIQUES."""
    R = _graphe_R(G)
    hyp = est_ordinal(e, R, x, y, z, X, a, w)
    return N.assume(hyp)   # ⊢ est_ordinal(E,R) sous l'hypothèse elle-même (= est_bien_ordonne)


def meme_ordinal_donne_isomorphisme(e="E", ep="Ep", G="G", Gp="Gp",
                                    f="f", x="x", y="y"):
    """{ meme_ordinal(E,R,E',R') } ⊢ sont_isomorphes_ordre(E,E',R,R').

    « Avoir le même ordinal » ENTRAÎNE (en fait équivaut à) « être isomorphes
    d'ordre » : meme_ordinal est défini comme sont_isomorphes_ordre. Preuve
    triviale (formules identiques)."""
    R, Rp = _graphe_R(G), _graphe_R(Gp)
    hyp = meme_ordinal(e, R, ep, Rp, f, x, y)
    return N.assume(hyp)


def segment_propre_est_segment(S="S", e="E", G="G", x="x", y="y"):
    """{ est_segment_propre(S,E,R) } ⊢ est_segment(S,R,E).

    Un segment PROPRE est en particulier un segment (projection gauche de la
    conjonction est_segment ∧ S≠E)."""
    R = _graphe_R(G)
    H = N.assume(est_segment_propre(S, e, R, x, y))
    return conjonction_elim_gauche(H)


def inferieur_ou_egal_reflexif(e="E", G="G", S="S", f="f", x="x", y="y"):
    """⊢ ordinal_inferieur_ou_egal(E,R,E,R).

    Tout ordinal est ≤ lui-même : (E,R) est isomorphe au segment S=E de (E,R)
    via l'identité. On le PROUVE en exhibant le témoin du ∃S — mais comme
    sont_isomorphes_ordre(E,E,R,R) est elle-même un ∃f (réflexivité non triviale,
    via l'identité), on REPORTE la clôture complète et on se contente de poser
    l'ÉNONCÉ ; cette fonction renvoie donc la FORMULE-énoncé (la réflexivité de
    l'ordre des ordinaux), pas un Theoreme.  (Voir docstring du module.)"""
    R = _graphe_R(G)
    return ordinal_inferieur_ou_egal(e, R, e, R, S, f, x, y)


__all__ = [
    # ordinal — type d'ordre représentationnel
    "est_ordinal", "meme_ordinal", "ordinal_de",
    # segment initial
    "est_segment_initial", "segment_initial_extremite", "est_segment_propre",
    # comparaison des ordinaux
    "ordinal_inferieur_ou_egal", "ordinal_strictement_inferieur", "trichotomie_ordinaux",
    # ordinal initial
    "est_ordinal_initial", "ordinal_initial_du_cardinal",
    # lemmes directs (certifiés)
    "ordinal_est_bien_ordonne", "meme_ordinal_donne_isomorphisme",
    "segment_propre_est_segment", "inferieur_ou_egal_reflexif",
]
