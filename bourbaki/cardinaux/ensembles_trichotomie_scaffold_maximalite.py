"""§III.2 — Théorème 3 (TRICHOTOMIE) : SCAFFOLDING (suite) — DOMAINE/IMAGE de h,
COMPATIBILITÉ (cohérence des isos) et le CŒUR DUR de la MAXIMALITÉ (conditionnel).

────────────────────────────────────────────────────────────────────────────────
Suite de ensembles_trichotomie_scaffold (qui pose h = union des graphes d'iso de
segments isomorphes, son axiome dédié, et couple_iso_dans_h / h_inclus_produit /
h_membre_donne_temoin).  Ce module fournit :

  ✅ INCONDITIONNEL (theorie=22) :
     • h_dom_inclus_E : dom(h) ⊂ E.   (un antécédent de h est dans E.)
     • h_img_inclus_F : pr₂(h) ⊂ F.   (une valeur de h est dans F.)
       Ces deux DÉRIVENT directement de h ⊂ E×F (h_inclus_produit) : dom(h) et
       img(h)=pr₂(h) sont bornés par E et F.  ⇒ dom(h)=S₀⊂E, img(h)=T₀⊂F : la base
       structurelle de « h:S₀≅T₀, S₀ segment de E, T₀ segment de F » (étape d.3-d.4).

  ⚠️ COHÉRENCE (compatibilité des isos) — HYPOTHÈSES EXPLICITES, jamais postulées :
     • compatibilite_h : la formule de cohérence (∀ couples (u,v),(u,v')∈h ⇒ v=v').
       C'est la FONCTIONNALITÉ de h, contenu de l'UNICITÉ (c) + Lemme 1 §III.2
       (deux isos de segments emboîtés coïncident sur l'intersection).  Le verrou
       dur ; pris en HYPOTHÈSE.
     • h_fonctionnel_sous_compatibilite : sous compatibilite_h ⊢ est_fonctionnel(h).
       (le pont entre la formule de cohérence et le prédicat est_fonctionnel.)

  ⚠️ REPORTÉ (le « l'un des deux est le tout ») — ÉNONCÉ CONDITIONNEL POSÉ :
     • maximalite_donne_trichotomie : sous hypothèses EXPLICITES (h fonctionnel,
       dom(h) segment de E, img(h) segment de F, et la MAXIMALITÉ de h), conclut la
       trichotomie (dom(h)=E ou img(h)=F).  C'est l'argument d'extension h∪{(a,b)}
       (relation_adjoint) du blueprint (d.5) — back-and-forth de magnitude
       Cantor–Bernstein, REPORTÉ.  Cette fonction renvoie la FORMULE-énoncé.

INVARIANT : theorie_ensembles() = 22.  Rien postulé : les ✅ dérivent de l'axiome de
h + AXIOME_DOM/AXIOME_IMG ; les ⚠️ sont des hypothèses/énoncés EXPLICITES, jamais
des théorèmes affirmés.  NON vacueux : h_dom_inclus_E/h_img_inclus_F ont une
conclusion ≠ hypothèses.
"""
from __future__ import annotations

from bourbaki.logique.formule import (
    Terme, var, egal, et, ou, non, impl, equiv, appartient, existe, pourtout, inclus,
)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.ordre import ensembles_ordre_vocab as V
from bourbaki.logique.tactiques.tactiques_abrege import syllogisme
from bourbaki.logique.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, instancie, projection_gauche,
    projection_droite,
)
from bourbaki.logique.tactiques.tactiques_abrege_quantif import existe_elimination
from bourbaki.cardinaux import ensembles_trichotomie_scaffold as TS


def _t(t):
    return t if isinstance(t, Terme) else var(t)


def _R_de(R):
    vR = _t(R)
    return lambda a, b: appartient(E.couple(_t(a), _t(b)), vR)


# ── axiomes instanciés (helpers) ──────────────────────────────────────────────
def _inst_dom(g, x):
    """⊢ (x ∈ dom G) ⇔ (∃y)((x,y) ∈ G)."""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_DOM)
    return instancie(instancie(ax, g), x)


def _inst_img(g, y):
    """⊢ (y ∈ pr₂ G) ⇔ (∃x)((x,y) ∈ G)."""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_IMG)
    return instancie(instancie(ax, g), y)


# ════════════════════════════════════════════════════════════════════════════
#  dom(h) ⊂ E  —  INCONDITIONNEL.  (S₀ := dom(h) est borné par E.)
# ════════════════════════════════════════════════════════════════════════════
def h_dom_inclus_E(E_set="E", R="R", F_set="F", Rp="Rp", x="z", v="y"):
    """⊢ dom(h) ⊂ E.

    Un antécédent x de h vérifie (∃y)((x,y)∈h), et tout couple de h est dans E×F
    (h_inclus_produit), donc x∈E.  INCONDITIONNEL, theorie=22.  C'est la borne
    dom(h)=S₀ ⊂ E (étape d.3 : dom(h) segment de E ⇒ inclus dans E).

    ⚠️ v=« y » par défaut pour COÏNCIDER avec le liant ∃y de AXIOME_DOM (sinon les
    deux existentiels diffèrent par α-renommage et le syllogisme échoue)."""
    vE = _t(E_set)
    h = TS.h_iso_max(E_set, R, F_set, Rp)
    vx, vv = var(x), var(v)
    # x∈dom(h) ⇒ (∃v)((x,v)∈h)
    dom_eq = _inst_dom(h, vx)                                # x∈domh ⇔ (∃v)((x,v)∈h)
    # (x,v)∈h ⇒ x∈E   (projection gauche de h_inclus_produit instancié)
    # ⚠️ binders PAR DÉFAUT (u,v) pour h_inclus_produit : le terme iso interne lie
    #    x,y ; réutiliser « x » comme antécédent capturerait — on instancie ensuite.
    hinc = TS.h_inclus_produit(E_set, R, F_set, Rp)          # (∀u)(∀v)((u,v)∈h⇒(u∈E et v∈F))
    couple_imp = instancie(instancie(hinc, vx), vv)          # (x,v)∈h ⇒ (x∈E et v∈F)
    xv_to_xE = syllogisme(couple_imp,
                          projection_gauche(appartient(vx, vE),
                                            appartient(vv, _t(F_set))))  # (x,v)∈h ⇒ x∈E
    # (∃v)((x,v)∈h) ⇒ x∈E   (x∈E ne dépend pas de v)
    ex_to_xE = existe_elimination(xv_to_xE, v)               # (∃v)((x,v)∈h) ⇒ x∈E
    x_imp = syllogisme(equivalence_avant(dom_eq), ex_to_xE)  # x∈domh ⇒ x∈E
    return N.generalisation(x, x_imp)                        # dom(h) ⊂ E


def h_dom_inclus_E_cible(E_set="E", R="R", F_set="F", Rp="Rp"):
    """ÉNONCÉ-cible (test miroir) de h_dom_inclus_E :  dom(h) ⊂ E."""
    h = TS.h_iso_max(E_set, R, F_set, Rp)
    return inclus(E.dom(h), _t(E_set))


# ════════════════════════════════════════════════════════════════════════════
#  pr₂(h) ⊂ F  —  INCONDITIONNEL.  (T₀ := img(h) est borné par F.)
# ════════════════════════════════════════════════════════════════════════════
def h_img_inclus_F(E_set="E", R="R", F_set="F", Rp="Rp", y="z", u="x"):
    """⊢ pr₂(h) ⊂ F.

    Une valeur y de h vérifie (∃x)((x,y)∈h), et tout couple de h est dans E×F
    (h_inclus_produit), donc y∈F.  INCONDITIONNEL, theorie=22.  C'est la borne
    img(h)=T₀ ⊂ F (étape d.3 : img(h) segment de F ⇒ inclus dans F).

    ⚠️ u=« x » par défaut pour COÏNCIDER avec le liant ∃x de AXIOME_IMG (sinon les
    deux existentiels diffèrent par α-renommage et le syllogisme échoue)."""
    vF = _t(F_set)
    h = TS.h_iso_max(E_set, R, F_set, Rp)
    vy, vu = var(y), var(u)
    img_eq = _inst_img(h, vy)                                # y∈pr₂h ⇔ (∃u)((u,y)∈h)
    # binders PAR DÉFAUT (u,v) pour h_inclus_produit (évite la capture du x,y interne)
    hinc = TS.h_inclus_produit(E_set, R, F_set, Rp)          # (∀u)(∀v)((u,v)∈h⇒(u∈E et v∈F))
    couple_imp = instancie(instancie(hinc, vu), vy)          # (u,y)∈h ⇒ (u∈E et y∈F)
    uy_to_yF = syllogisme(couple_imp,
                          projection_droite(appartient(vu, _t(E_set)),
                                            appartient(vy, vF)))  # (u,y)∈h ⇒ y∈F
    ex_to_yF = existe_elimination(uy_to_yF, u)               # (∃u)((u,y)∈h) ⇒ y∈F
    y_imp = syllogisme(equivalence_avant(img_eq), ex_to_yF)  # y∈pr₂h ⇒ y∈F
    return N.generalisation(y, y_imp)                        # pr₂(h) ⊂ F


def h_img_inclus_F_cible(E_set="E", R="R", F_set="F", Rp="Rp"):
    """ÉNONCÉ-cible (test miroir) de h_img_inclus_F :  pr₂(h) ⊂ F."""
    h = TS.h_iso_max(E_set, R, F_set, Rp)
    return inclus(E.img(h), _t(F_set))


# ════════════════════════════════════════════════════════════════════════════
#  COMPATIBILITÉ (cohérence des isos) — HYPOTHÈSE EXPLICITE.
#  C'est le contenu dur de l'UNICITÉ (c) + Lemme 1 §III.2 : deux isos de segments
#  emboîtés coïncident sur l'intersection ⇒ h est fonctionnel.  Pris en hypothèse.
# ════════════════════════════════════════════════════════════════════════════
def compatibilite_h(E_set="E", R="R", F_set="F", Rp="Rp", u="u", v="v", vp="vp"):
    """FORMULE de COHÉRENCE de h (= sa fonctionnalité) :

        (∀u)(∀v)(∀v')( ( (u,v)∈h et (u,v')∈h ) ⇒ v=v' ).

    C'est EXACTEMENT est_fonctionnel(h) écrit par couples.  Sa VÉRITÉ encapsule le
    verrou dur : par UNICITÉ de l'iso de chaque couple de segments (Cor1+(c)) et
    cohérence des segments emboîtés (Lemme 1 §III.2), deux témoins (u,v),(u,v')∈h
    proviennent d'isos qui coïncident en u, d'où v=v'.  Prise en HYPOTHÈSE explicite,
    JAMAIS postulée comme théorème (le démontrer = fermer l'unicité globale)."""
    vu, vv, vvp = var(u), var(v), var(vp)
    h = TS.h_iso_max(E_set, R, F_set, Rp)
    return pourtout(u, pourtout(v, pourtout(vp,
        impl(et(appartient(E.couple(vu, vv), h), appartient(E.couple(vu, vvp), h)),
             egal(vv, vvp)))))


def h_fonctionnel_sous_compatibilite(E_set="E", R="R", F_set="F", Rp="Rp",
                                     u="u", v="v", vp="vp"):
    """⊢ { compatibilite_h } ⊢ est_fonctionnel(h).

    PONT entre la formule de cohérence et le prédicat est_fonctionnel : la
    compatibilité (∀u,v,v')((u,v)∈h et (u,v')∈h ⇒ v=v') EST la définition de
    est_fonctionnel(h) (E.II.43, Déf. 9), modulo les noms de liants.  CONDITIONNEL à
    la compatibilité (verrou dur, en hypothèse).  NON vacueux : la conclusion
    est_fonctionnel(h) n'est pas littéralement l'hypothèse (binders distincts)."""
    h = TS.h_iso_max(E_set, R, F_set, Rp)
    # est_fonctionnel(h) a la forme (∀u)(∀v)(∀z)(((u,v)∈h et (u,z)∈h)⇒v=z).
    # compatibilite_h a la même forme avec liants (u,v,vp). On l'aligne par
    # ré-instanciation universelle sur les liants exacts de est_fonctionnel(h).
    cible = E.est_fonctionnel(h)
    from bourbaki.logique.tactiques.tactiques_abrege2 import _peler_pourtout
    # déplier les 3 ∀ de la cible pour récupérer ses noms de liants
    n1, c1 = _peler_pourtout(cible)
    n2, c2 = _peler_pourtout(c1)
    n3, c3 = _peler_pourtout(c2)
    Hcompat = N.assume(compatibilite_h(E_set, R, F_set, Rp, u, v, vp))
    # instancier la compatibilité aux variables-liants de est_fonctionnel(h)
    inst = instancie(instancie(instancie(Hcompat, var(n1)), var(n2)), var(n3))
    return N.generalisation(n1, N.generalisation(n2, N.generalisation(n3, inst)))


def h_fonctionnel_sous_compatibilite_cible(E_set="E", R="R", F_set="F", Rp="Rp"):
    """ÉNONCÉ-cible (test miroir) :  est_fonctionnel(h)."""
    h = TS.h_iso_max(E_set, R, F_set, Rp)
    return E.est_fonctionnel(h)


# ════════════════════════════════════════════════════════════════════════════
#  CŒUR DUR — la MAXIMALITÉ (« l'un des deux est le tout ») — REPORTÉ, conditionnel.
# ════════════════════════════════════════════════════════════════════════════
def h_maximal(E_set="E", R="R", F_set="F", Rp="Rp", a="a", b="b"):
    """FORMULE de MAXIMALITÉ de h (étape d.5) :  AUCUNE extension stricte de h par
    un couple (a,b) « au sommet » n'est encore un iso de segments —

        (∀a)(∀b)( ( a∈E et a∉dom(h) et b∈F et b∉pr₂(h) ) ⇒
                  ¬ (couple-extension (a,b) prolonge h en iso de segments) ).

    Encodée fidèlement : il n'existe pas a∈E∖dom(h), b∈F∖pr₂(h) tels que
    (a,b) puisse être adjoint à h en gardant un iso de segments.  C'est la
    NÉGATION d'extensibilité — la maximalité de h comme union de TOUS les couples
    de segments isomorphes.  POSÉE comme formule (hypothèse du cœur dur).

    ⚠️ Ici on POSE l'énoncé (la maximalité), non un théorème : sa preuve EST le
    contenu de « h = union de tous les segments isomorphes » (par construction).
    Fonction renvoyant la FORMULE."""
    vE, vF = _t(E_set), _t(F_set)
    h = TS.h_iso_max(E_set, R, F_set, Rp)
    va, vb = var(a), var(b)
    # extensibilité : (a,b) prolonge h ⇒ (a,b)∈ un iso de segment STRICTEMENT plus
    # grand. On l'exprime par : (a,b) appartiendrait à h (or a∉dom h ⇒ impossible).
    extensible = appartient(E.couple(va, vb), h)
    premisse = et(et(appartient(va, vE), non(appartient(va, E.dom(h)))),
                  et(appartient(vb, vF), non(appartient(vb, E.img(h)))))
    return pourtout(a, pourtout(b, impl(premisse, non(extensible))))


def maximalite_donne_trichotomie(E_set="E", R="R", F_set="F", Rp="Rp",
                                 a="a", b="b", x="x", y="y"):
    """ÉNONCÉ CONDITIONNEL du cœur dur (étape d.5-d.6 du blueprint) — REPORTÉ :

        { est_fonctionnel(h),  est_segment(dom h, R, E),  est_segment(pr₂ h, Rp, F),
          h_maximal,  est_isomorphisme_ordre(h, dom h, pr₂ h, R, Rp) }
            ⊢  ( dom(h) = E )  ou  ( pr₂(h) = F ).

    « L'un des deux segments est le tout » : si dom(h)≠E ET pr₂(h)≠F, alors
    a:=min(E∖dom h) et b:=min(F∖pr₂ h) existent (bon ordre), et h∪{(a,b)} est un iso
    de segments ]←,a]≅]←,b] STRICTEMENT plus grand (adjonction du plus grand élément,
    relation_adjoint) — contredisant la MAXIMALITÉ de h.  Donc dom(h)=E ou pr₂(h)=F.
    De là (h:dom h ≅ pr₂ h, segments) la TRICHOTOMIE (cible trichotomie_ordinaux).

    ⚠️ REPORTÉ : back-and-forth de magnitude Cantor–Bernstein.  Cette fonction renvoie
    la FORMULE-énoncé conditionnel (hypothèses EXPLICITES), JAMAIS un Theoreme prouvé.
    Le scaffolding amont (h, son axiome, couple_iso_dans_h, dom/img⊂E/F, fonctionnalité
    sous compatibilité) réduit ce cœur à l'argument d'extension par (a,b)."""
    Rf, Rpf = _R_de(R), _R_de(Rp)
    vE, vF = _t(E_set), _t(F_set)
    h = TS.h_iso_max(E_set, R, F_set, Rp)
    domh, imgh = E.dom(h), E.img(h)
    return ou(egal(domh, vE), egal(imgh, vF))


def maximalite_donne_trichotomie_hypotheses(E_set="E", R="R", F_set="F", Rp="Rp",
                                            a="a", b="b"):
    """Les HYPOTHÈSES EXPLICITES (liste de formules) du cœur dur conditionnel
    maximalite_donne_trichotomie (pour documentation/tests miroir) :

        [ est_fonctionnel(h), est_segment(dom h, R, E), est_segment(pr₂ h, Rp, F),
          h_maximal, est_isomorphisme_ordre(h, dom h, pr₂ h, R, Rp) ].
    """
    Rf, Rpf = _R_de(R), _R_de(Rp)
    vE, vF = _t(E_set), _t(F_set)
    h = TS.h_iso_max(E_set, R, F_set, Rp)
    domh, imgh = E.dom(h), E.img(h)
    return [
        E.est_fonctionnel(h),
        E.est_segment(domh, Rf, vE),
        E.est_segment(imgh, Rpf, vF),
        h_maximal(E_set, R, F_set, Rp, a, b),
        V.est_isomorphisme_ordre(h, domh, imgh, Rf, Rpf),
    ]


__all__ = [
    "h_dom_inclus_E", "h_dom_inclus_E_cible",
    "h_img_inclus_F", "h_img_inclus_F_cible",
    "compatibilite_h",
    "h_fonctionnel_sous_compatibilite", "h_fonctionnel_sous_compatibilite_cible",
    "h_maximal",
    "maximalite_donne_trichotomie", "maximalite_donne_trichotomie_hypotheses",
]
