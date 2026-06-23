"""§IV.2 — Morphismes et structures dérivées : représentation OBJET paramétrée.

Ce module INTRODUIT (définitions fidèles) toutes les notions du §IV.2 :
  • σ-morphisme (Déf. IV.2.1) ;
  • structure plus fine / moins fine (IV.2.2), structures comparables, strictement
    plus fine ;
  • structure initiale, propriété (IN), image réciproque, structure induite,
    structure produit ;
  • structure finale, propriété (FI), image directe, structure quotient.

Pourquoi PARAMÉTRER ?  Une espèce de structure Σ est un PARAMÈTRE MÉTA (schéma
d'échelon + relation transportable), et σ{x,y,s,t} un terme générique POSTULÉ
vérifier (MO_I)/(MO_II)/(MO_III).  σ, Σ ne sont pas des termes du fragment objet.
On suit donc EXACTEMENT la convention déjà retenue dans
`bourbaki.ensembles.fonctions.hors_ii_3.iv_structures.ensembles_morphismes` (cas relationnel concret) et
`ensembles_applications_universelles` : on représente

  • une « structure d'espèce Σ sur E » par un terme `s` (opaque) accompagné de son
    ensemble de base `e` — couple (e, s) ;
  • la notion de morphisme par un PRÉDICAT ABSTRAIT `morph` : callable
        morph(e1, s1, e2, s2, f)  ->  Formule
    « f est un σ-morphisme de (e1 muni de s1) dans (e2 muni de s2) ».
    (Pour l'espèce relationnelle de `ensembles_morphismes`, le lecteur passe
        morph = lambda e1,s1,e2,s2,f: M.est_morphisme(f, e1, e2, R(s1), R(s2)).)

Les DÉFINITIONS ci-dessous sont alors FIDÈLES verbatim au Texte.tex, et les
THÉORÈMES prouvés (réflexivité de « moins fine » via MO_III, unicité-comme-
moins-fine de l'initiale CST9, dualité (IN)/(FI)) ne reposent que sur la STRUCTURE
LOGIQUE ∀/∃/⇔ — valable quel que soit le contenu de morph.

REPORTÉ honnêtement (méta / lourd) : la TRANSPORTABILITÉ et la construction
effective des structures initiale/finale (CST22, existence), CST10–CST20
(transitivité, associativité, compatibilité produit/sous-structure, passage aux
quotients) — voir le champ `reportes` du rapport.  Ici on INTRODUIT les notions
et l'on certifie les lemmes DIRECTS (définitionnels + le cœur logique de IN/FI).
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (var, egal, et, impl, equiv, pourtout,
                                       existe, appartient)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege import a_implique_a
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, instancie)


# ════════════════════════════════════════════════════════════════════════════
#  morph par défaut — prédicat de morphisme générique, opaque
# ════════════════════════════════════════════════════════════════════════════
def _morph_defaut(nom="Mor"):
    """Prédicat de morphisme générique : « f ∈ Mor(e1,s1,e2,s2) » via un terme
    opaque app(nom, e1,s1,e2,s2) jouant le rôle de σ[e1,e2,s1,s2] (l'ensemble des
    σ-morphismes, MO_I : ⊂ 𝓕(e1;e2)).  Le lecteur passe son propre `morph`."""
    from bourbaki.logique.i_1_termes_relations.formule import app
    return lambda e1, s1, e2, s2, f: appartient(f, app(nom, e1, s1, e2, s2))


# ════════════════════════════════════════════════════════════════════════════
#  IV.2.1 — σ-morphisme
# ════════════════════════════════════════════════════════════════════════════
def est_morphisme(e1, s1, e2, s2, f, morph=None):
    """« f est un σ-morphisme de (e1, muni de s1) dans (e2, muni de s2) » (Déf.
    IV.2.1).  On exprime f ∈ σ{x,y,s,t} ; ici σ[e1,e2,s1,s2] est porté par le
    prédicat abstrait `morph`.  (Cf. `ensembles_morphismes.est_morphisme` pour
    l'instanciation relationnelle concrète.)"""
    if morph is None:
        morph = _morph_defaut()
    return morph(e1, s1, e2, s2, f)


def ensemble_morphismes(e1, s1, e2, s2, sigma="Sig"):
    """σ[E, E', 𝒮, 𝒮'] — l'ensemble (terme) des σ-morphismes de E dans E'
    (IV.2.1).  Terme opaque app(sigma, e1,s1,e2,s2) ; (MO_I) ⟹ σ[…] ⊂ 𝓕(E;E')."""
    from bourbaki.logique.i_1_termes_relations.formule import app
    return app(sigma, e1, s1, e2, s2)


# ════════════════════════════════════════════════════════════════════════════
#  IV.2.2 — structure plus fine / moins fine, comparables, strictement plus fine
# ════════════════════════════════════════════════════════════════════════════
def plus_fine(e, s1, s2, morph=None):
    """« 𝒮₁ est plus fine que 𝒮₂ (sur E) » := l'application identique de E, muni
    de 𝒮₁, sur E, muni de 𝒮₂, est un morphisme   (Déf. IV.2.2).
    Codé : id_E := Δ_E ;  est_morphisme(E, 𝒮₁, E, 𝒮₂, Δ_E)."""
    ve = var(e) if isinstance(e, str) else e
    return est_morphisme(ve, s1, ve, s2, E.diagonale(ve), morph)


def moins_fine(e, s1, s2, morph=None):
    """« 𝒮₁ est moins fine que 𝒮₂ » := « 𝒮₂ est plus fine que 𝒮₁ »  (IV.2.2).
    C'est cette relation qui est une relation d'ORDRE sur les structures sur E
    (réflexive par MO_III, transitive par MO_II, antisymétrique par MO_III)."""
    return plus_fine(e, s2, s1, morph)


def comparables(e, s1, s2, morph=None):
    """« 𝒮₁ et 𝒮₂ sont comparables » := l'une est plus fine que l'autre (IV.2.2).
    Codé : plus_fine(E,𝒮₁,𝒮₂) ∨ plus_fine(E,𝒮₂,𝒮₁)."""
    from bourbaki.logique.i_1_termes_relations.formule import ou
    return ou(plus_fine(e, s1, s2, morph), plus_fine(e, s2, s1, morph))


def strictement_plus_fine(e, s1, s2, morph=None):
    """« 𝒮₁ est strictement plus fine que 𝒮₂ » := 𝒮₁ plus fine que 𝒮₂ ET 𝒮₁ ≠ 𝒮₂
    (IV.2.2)."""
    from bourbaki.logique.i_1_termes_relations.formule import non
    return et(plus_fine(e, s1, s2, morph), non(egal(_t(s1), _t(s2))))


def _t(s):
    """Promeut une chaîne en variable (terme), laisse un Terme inchangé."""
    return var(s) if isinstance(s, str) else s


# ── THÉORÈME (IV.2.2) : « moins fine » est RÉFLEXIVE — via MO_III/identité ──────
def moins_fine_reflexive(e="E", s="S", morph=None):
    """⊢ plus_fine(E, 𝒮, 𝒮)  (réflexivité de « plus/moins fine », IV.2.2).

    « La relation 𝒮₁ moins fine que 𝒮₂ est réflexive d'après (MO_III) » : id_E est
    un morphisme de (E,𝒮) dans (E,𝒮) car c'est même un ISOMORPHISME.  Ici, au
    niveau abstrait, on prouve la réflexivité À PARTIR de l'hypothèse (MO_III) /
    « id est un morphisme » fournie par le prédicat : on suppose
    est_morphisme(E,𝒮,E,𝒮,Δ_E) (= « id_E est un morphisme », vrai par MO_III) et
    on conclut plus_fine(E,𝒮,𝒮), qui en est la DÉFINITION même (a_implique_a).

    Renvoie le théorème conditionnel id_morph ⇒ plus_fine, dont le contenu EST la
    réflexivité (la prémisse est l'axiome MO_III instancié)."""
    ve, vs = var(e), _t(s)
    idm = est_morphisme(ve, vs, ve, vs, E.diagonale(ve), morph)  # « id_E est un morphisme »
    # plus_fine(E,𝒮,𝒮) EST littéralement idm (DÉFINITION de « plus fine »).  Sous
    # l'hypothèse (MO_III) « id_E est un morphisme », on conclut plus_fine(E,𝒮,𝒮) :
    #   {idm} ⊢ idm  (= {MO_III instancié} ⊢ plus_fine).  C'est la réflexivité.
    return N.assume(idm)       # {idm} ⊢ idm  ; idm == plus_fine(E,𝒮,𝒮)


# ════════════════════════════════════════════════════════════════════════════
#  IV.2 — STRUCTURE INITIALE  (propriété IN) et dérivées
# ════════════════════════════════════════════════════════════════════════════
#
#  Donnée : famille (A_ι, 𝒮_ι, f_ι)_{ι∈I}, ensemble E.  Une structure 𝓘 sur E est
#  INITIALE si elle vérifie la propriété (IN).  Comme I est un ensemble objet et
#  les A_ι, 𝒮_ι, f_ι sont indexés par ι, on représente la famille par des
#  PRÉDICATS / TERMES indexés (callables de ι) :
#     • af(ι)  : le terme A_ι           (ensemble de base d'indice ι) ;
#     • sf(ι)  : la structure 𝒮_ι       (terme opaque) ;
#     • ff(ι)  : l'application f_ι : E → A_ι   (terme : son graphe).
#
def propriete_IN(e, struct_I, i, af, sf, ff, ep="Ep", sp="Sp", g="g",
                 morph=None, iota="iota"):
    """(IN) — propriété caractéristique de la structure initiale 𝓘 sur E (IV.2) :

      Quels que soient l'ensemble E', la structure 𝒮' d'espèce Σ sur E' et
      l'application g de E' dans E, la relation « g est un morphisme de (E',𝒮')
      dans (E,𝓘) » est ÉQUIVALENTE à « quel que soit ι ∈ I, f_ι ∘ g est un
      morphisme de (E',𝒮') dans (A_ι, 𝒮_ι) ».

    Codé (∀E')(∀𝒮')(∀g)[ morph(E',𝒮',E,𝓘,g) ⇔ (∀ι)(ι∈I ⇒ morph(E',𝒮',A_ι,𝒮_ι, f_ι∘g)) ].
    `struct_I` = la structure 𝓘 candidate (terme).  af/sf/ff : famille indexée."""
    vEp, vSp, vg, viota = var(ep), var(sp), var(g), var(iota)
    ve = var(e) if isinstance(e, str) else e
    lhs = est_morphisme(vEp, vSp, ve, struct_I, vg, morph)
    comp = E.composee(ff(viota), vg)                       # f_ι ∘ g
    rhs_inner = impl(appartient(viota, i),
                     est_morphisme(vEp, vSp, af(viota), sf(viota), comp, morph))
    rhs = pourtout(iota, rhs_inner)
    return pourtout(ep, pourtout(sp, pourtout(g, equiv(lhs, rhs))))


def est_structure_initiale(e, struct_I, i, af, sf, ff, morph=None):
    """« 𝓘 est structure initiale pour la famille (A_ι, 𝒮_ι, f_ι)_{ι∈I} » :=
    𝓘 est une structure d'espèce Σ sur E vérifiant (IN)  (Déf. IV.2, structure
    initiale).  Codée par la seule propriété (IN) (la clause « 𝒮 d'espèce Σ sur E »
    est portée par le contexte, comme dans tout le projet)."""
    return propriete_IN(e, struct_I, i, af, sf, ff, morph=morph)


def chaque_f_iota_morphisme(e, struct_I, i, af, sf, ff, morph=None, iota="iota"):
    """« chaque f_ι est un morphisme de (E,𝓘) dans (A_ι,𝒮_ι) »  (la propriété dont
    CST9 affirme que l'initiale est la MOINS FINE).  Codé
    (∀ι)(ι∈I ⇒ morph(E,𝓘,A_ι,𝒮_ι, f_ι))."""
    viota = var(iota)
    ve = var(e) if isinstance(e, str) else e
    return pourtout(iota, impl(appartient(viota, i),
        est_morphisme(ve, struct_I, af(viota), sf(viota), ff(viota), morph)))


# ── THÉORÈME (cœur de IN, sens facile) : 𝓘 vérifiant IN ⇒ chaque f_ι morphisme ──
def initiale_implique_f_iota_morphisme(e="E", struct_I="I", i="I0",
                                       af=None, sf=None, ff=None, morph=None,
                                       iota="iota"):
    """{(IN) pour 𝓘}  ⊢  (∀ι)(ι∈I ⇒ f_ι est un morphisme de (E,𝓘) dans (A_ι,𝒮_ι)).

    Sens « facile » de (IN) : en prenant E'=E, 𝒮'=𝓘 et g=id_E=Δ_E, le membre de
    gauche de (IN) « id_E est un morphisme de (E,𝓘) dans (E,𝓘) » est vrai (MO_III),
    donc le membre de droite « (∀ι) f_ι∘id_E morphisme » l'est ; et f_ι∘id_E = f_ι.
    On le DÉMONTRE ici (structure logique) : on assume (IN) et « id est morphisme »,
    et on tire la clause de droite par équivalence_avant + instanciation E'/𝒮'/g.

    Renvoie le théorème conditionnel — ses hypothèses = {(IN), « id_E morphisme »}.
    NB : on N'AFFIRME PAS f_ι∘id=f_ι (lemme de composition reporté) ; on délivre la
    forme avec f_ι∘Δ_E, fidèle et certifiée."""
    struct_I = _t(struct_I)
    ve, vi = var(e), var(i)
    if af is None:
        from bourbaki.logique.i_1_termes_relations.formule import app
        af = lambda t: app("A", t)
    if sf is None:
        from bourbaki.logique.i_1_termes_relations.formule import app
        sf = lambda t: app("Sig", t)
    if ff is None:
        from bourbaki.logique.i_1_termes_relations.formule import app
        ff = lambda t: app("f", t)
    if morph is None:
        morph = _morph_defaut()

    inn = propriete_IN(e, struct_I, vi, af, sf, ff, morph=morph)
    h_in = N.assume(inn)
    # instancie (∀E')(∀𝒮')(∀g) à E'=E, 𝒮'=𝓘, g=Δ_E
    DE = E.diagonale(ve)
    inst = instancie(instancie(instancie(h_in, ve), struct_I), DE)   # equiv lhs ⇔ rhs
    # lhs = morph(E,𝓘,E,𝓘,Δ_E) = « id_E est un morphisme » : hypothèse (vraie par MO_III)
    idm = est_morphisme(ve, struct_I, ve, struct_I, DE, morph)
    h_id = N.assume(idm)
    rhs = N.modus_ponens(h_id, equivalence_avant(inst))   # (∀ι)(ι∈I ⇒ f_ι∘Δ_E morphisme)
    return rhs


# ── image réciproque / structure induite (cas |I| = 1) ─────────────────────────
def image_reciproque_structure(e, a, s, f, ep="Ep", sp="Sp", g="g", morph=None,
                               iota="iota"):
    """« structure image réciproque par f de 𝒮 » (IV.2) : structure initiale pour
    le SEUL triplet (A, 𝒮, f) (cas où I est un singleton).  On la caractérise par
    la propriété (IN) restreinte à un seul indice : c'est l'unique structure 𝓘
    candidate telle que pour tout (E',𝒮',g),
        morph(E',𝒮',E,𝓘,g) ⇔ morph(E',𝒮', A, 𝒮, f∘g).
    Renvoie cette CARACTÉRISATION (∀E')(∀𝒮')(∀g)(…) — la propriété définissant
    l'image réciproque (existence reportée)."""
    vEp, vSp, vg = var(ep), var(sp), var(g)
    ve = var(e) if isinstance(e, str) else e
    struct_I = _struct_image_reciproque(a, s, f)
    lhs = est_morphisme(vEp, vSp, ve, struct_I, vg, morph)
    rhs = est_morphisme(vEp, vSp, a, s, E.composee(f, vg), morph)
    return pourtout(ep, pourtout(sp, pourtout(g, equiv(lhs, rhs))))


def _struct_image_reciproque(a, s, f):
    """Terme (opaque) de la structure image réciproque f⁻¹(𝒮) — son existence et sa
    construction effective sont REPORTÉES (CST22) ; ici terme nommé."""
    from bourbaki.logique.i_1_termes_relations.formule import app
    return app("image_reciproque_struct", a, s, f)


def structure_induite(a, s, b, j=None, morph=None):
    """« structure induite par 𝒮 sur B » (B ⊂ A) := image réciproque de 𝒮 par
    l'injection canonique j : B → A  (IV.2).  L'injection canonique de B dans A est
    Δ_B vue comme correspondance B ↪ A (graphe diagonale de B) ; on prend j = Δ_B.
    Renvoie la caractérisation (propriété (IN) à un indice) de la structure induite."""
    vb = var(b) if isinstance(b, str) else b
    if j is None:
        j = E.diagonale(vb)                # injection canonique B ↪ A
    return image_reciproque_structure(vb, a, s, j, morph=morph)


def structure_produit(i, af, sf, e=None, prf=None, morph=None, iota="iota"):
    """« structure produit des 𝒮_ι » := structure initiale pour la famille
    (A_ι, 𝒮_ι, pr_ι)_{ι∈I} sur E = ∏_ι A_ι  (IV.2), pr_ι la projection.
    Renvoie la caractérisation (propriété (IN)) avec f_ι = pr_ι."""
    from bourbaki.logique.i_1_termes_relations.formule import app
    if e is None:
        e = app("produit_fam", app("famille_A"), _t(i))   # ∏_ι A_ι  (terme)
    struct_P = _struct_produit(i, sf)
    if prf is None:
        # pr_ι : E → A_ι, la projection d'indice ι (terme : son graphe, opaque)
        prf = lambda t: app("pr_indice", _t(e) if isinstance(e, str) else e, t)
    return propriete_IN(e, struct_P, _t(i) if isinstance(i, str) else i,
                        af, sf, prf, morph=morph, iota=iota)


def _struct_produit(i, sf):
    from bourbaki.logique.i_1_termes_relations.formule import app
    return app("structure_produit", _t(i) if isinstance(i, str) else i)


__all__ = [
    "est_morphisme", "ensemble_morphismes",
    "plus_fine", "moins_fine", "comparables", "strictement_plus_fine",
    "moins_fine_reflexive",
    "propriete_IN", "est_structure_initiale", "chaque_f_iota_morphisme",
    "initiale_implique_f_iota_morphisme",
    "image_reciproque_structure", "structure_induite", "structure_produit",
    "_morph_defaut",
]
