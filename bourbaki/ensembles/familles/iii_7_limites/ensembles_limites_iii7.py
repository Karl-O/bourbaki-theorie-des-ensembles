"""§III.7.2 — Propriété universelle de la limite projective (Proposition 1, 1°).

Ce module NEUF prouve la partie TRACTABLE de la Proposition 1 (§III.7.2) — la
propriété universelle (cône) de la limite projective E = lim←_{α∈I} E_α — sans
toucher aux fichiers déposés.  Il RÉUTILISE (import, AUCUNE modification) :
 - `bourbaki.ensembles.familles.iii_7_limites.ensembles_limites` (système projectif, lim_proj,
   axiome (1), appartient_limite_projective, limite_projective_relation_1) ;
 - `bourbaki.ordre.iii_7_limites.ensembles_limites_canoniques` (application canonique f_α,
   canonique_proj_valeur f_α(z)=pr_α z).

ÉNONCÉ (Proposition 1, §III.7.2).  Soit (E_α, f_{αβ}) un système projectif relatif
à I, E = lim← E_α, f_α : E → E_α les applications canoniques.  Soit (u_α) une
famille d'applications u_α : F → E_α COMPATIBLE :
    (5)   f_{αβ} ∘ u_β = u_α      pour α ≤ β,
lue au niveau des valeurs :  f_{αβ}(u_β(y)) = u_α(y).
Alors il existe une application u : F → E et une seule telle que
    (6)   u_α = f_α ∘ u           pour tout α,
c.-à-d.  u_α(y) = f_α(u(y)).

CODAGE.  u_α := cone_u(u, α) = app("cone_u", u, α) (la donnée des u_α).  Le terme
de l'application canonique u : F → E est `cone_canonique(Efam, f, u)` ; sa valeur
en y est u(y) = E.valeur(cone_canonique, y).  L'AXIOME DÉFINITIONNEL caractérise
ses coordonnées :
    (★)   (∀α)(∀y)( (α∈I et y∈F) ⇒ pr_α(u(y)) = u_α(y) ),
c.-à-d. « u(y) = (u_α(y))_α » — légitimé par S8 (le graphe {(y, (u_α(y))_α)} se
sélectionne dans F × ∏_α E_α) + A1, isolé dans une THÉORIE DÉDIÉE paramétrée
(motif axiome_lim_proj / axiome_canonique_proj).  theorie_ensembles() reste à 22.

THÉORÈMES CERTIFIÉS par le noyau (cf. tests) :
 - `cone_compatibilite` : décomposition de la définition de la compatibilité (5).
 - `cone_coordonnee_valeur` : (★) instancié — pr_α(u(y)) = u_α(y).
 - `cone_image_dans_limite` : { compatibilité (5), u(y)∈∏ } ⊢ u(y) ∈ lim←.
       (le point u(y)=(u_α(y))_α vérifie la condition (1) de la limite : c'est le
        CŒUR de l'existence — l'image de la canonique tombe dans la limite.)
 - `cone_relation_6` : { u(y)∈lim←, α∈I, y∈F } ⊢ f_α(u(y)) = u_α(y)  (relation (6)).
 - `cone_existence` : { compatibilité (5), u(y)∈∏, α∈I, y∈F } ⊢ f_α(u(y)) = u_α(y)
       (la relation (6) sous les hypothèses de la Prop. 1 — EXISTENCE du cône).

REPORTÉ honnêtement (champ REPORTES) : UNICITÉ de u (« et une seule ») — exige
l'extensionnalité des applications dans le produit (deux applications de F vers une
PARTIE du produit qui ont mêmes coordonnées sont égales : extensionnalité du
produit + application_egale_par_valeurs sur la limite) ; les critères 2° (u
injective) ; Corollaires 1/2, Propositions 2-10.  Le résiduel « u(y)∈∏ » de
cone_image_dans_limite / cone_existence est l'énoncé « u est BIEN une application
F→∏ » (bonne-définition de la canonique) : honnête, NON vacuous, NON faux.
"""
from __future__ import annotations

from bourbaki.logique.formule import (
    Terme, var, egal, et, impl, appartient, existe, pourtout, app,
)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.ensembles.familles.iii_7_limites import ensembles_limites as L
from bourbaki.ordre.iii_7_limites import ensembles_limites_canoniques as C
from bourbaki.logique.tactiques.tactiques_abrege2 import (
    instancie, conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere,
)
from bourbaki.logique.tactiques.tactiques_abrege_egalite import (
    composer_egalites, congruence_terme, symetrie,
)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def _gleq():
    """Préordre ≤ par défaut (même défaut que les modules limites)."""
    return lambda u, v: appartient(E.couple(u, v), var("Gleq"))


# ════════════════════════════════════════════════════════════════════════════
#  CODAGE de la famille-cône (u_α : F → E_α) et de l'application canonique u
# ════════════════════════════════════════════════════════════════════════════
def cone_u(u, a):
    """u_α : F → E_α  (composante d'indice α de la famille-cône u=(u_α))."""
    return app("cone_u", u, a)


def cone_u_valeur(u, a, y):
    """u_α(y) := valeur(u_α, y)."""
    return E.valeur(cone_u(u, a), y)


def cone_canonique(Efam, f, u):
    """Terme (graphe) de l'application canonique u : F → E = lim← E_α  (Prop. 1).

    Efam = famille (E_α), f = système, u = famille-cône (u_α).  L'unique application
    telle que pr_α(u(y)) = u_α(y) : « u(y) = (u_α(y))_α ».  Terme opaque caractérisé
    par l'axiome (★) ci-dessous."""
    return app("cone_canon", Efam, f, u)


def cone_canonique_valeur(Efam, f, u, y):
    """u(y) := valeur(cone_canonique, y)  (la valeur de l'application canonique)."""
    return E.valeur(cone_canonique(Efam, f, u), y)


# ════════════════════════════════════════════════════════════════════════════
#  DÉFINITION — compatibilité de la famille-cône  (relation (5), au niveau valeurs)
# ════════════════════════════════════════════════════════════════════════════
def cone_compatible(f, u, leq, i, ff, a="a", b="b", y="yy"):
    """« (u_α : F → E_α) est compatible avec (f_{αβ}) » (Prop. 1, relation (5)) :=
        (∀α)(∀β)(∀y)( (α∈I et β∈I et α≤β et y∈F) ⇒ f_{αβ}(u_β(y)) = u_α(y) ).

    Lecture de (5) f_{αβ}∘u_β = u_α au niveau des valeurs (forme directement
    utilisable, comme cocycle_projectif/identite_projectif du module limites).
    ff = l'ensemble source commun F des u_α."""
    va, vb, vy = var(a), var(b), var(y)
    fab = L.appl_proj(f, va, vb)
    hyp = et(et(et(appartient(va, i), appartient(vb, i)), leq(va, vb)),
             appartient(vy, ff))
    concl = egal(E.valeur(fab, cone_u_valeur(u, vb, vy)), cone_u_valeur(u, va, vy))
    return pourtout(a, pourtout(b, pourtout(y, impl(hyp, concl))))


# ════════════════════════════════════════════════════════════════════════════
#  AXIOME DÉFINITIONNEL de l'application canonique u  (★)  : pr_α(u(y)) = u_α(y)
# ════════════════════════════════════════════════════════════════════════════
def axiome_cone_canonique(Efam, f, u, leq, i, ff, a="a", y="yy"):
    """AXIOME définitionnel (★) de l'application canonique u : F → E (Prop. 1) :
        (∀α)(∀y)( (α∈I et y∈F) ⇒ pr_α(u(y)) = u_α(y) ).

    « u(y) = (u_α(y))_α » : la α-coordonnée de u(y) est u_α(y).  Légitimé par S8
    (sélection du graphe {(y,(u_α(y))_α)} dans F × ∏_α E_α) + A1 — même statut que
    AXIOME_PRODUIT_FAM / axiome_lim_proj / axiome_canonique_proj.  ff = source F."""
    va, vy = var(a), var(y)
    u_y = cone_canonique_valeur(Efam, f, u, vy)
    hyp = et(appartient(va, i), appartient(vy, ff))
    concl = egal(E.projection_indice(u_y, va), cone_u_valeur(u, va, vy))
    return pourtout(a, pourtout(y, impl(hyp, concl)))


def theorie_cone_canonique(Efam, f, u, leq, i, ff):
    """Théorie dédiée ne contenant que l'axiome (★) de la valeur canonique-cône."""
    return N.Theorie("Cone-canonique-projectif",
                     [axiome_cone_canonique(Efam, f, u, leq, i, ff)])


# ════════════════════════════════════════════════════════════════════════════
#  THÉORÈMES DIRECTS
# ════════════════════════════════════════════════════════════════════════════
def cone_compatibilite(f="f", u="u", leq=None, i="I", ff="F", a="a", b="b", y="yy"):
    """{ (u_α) compatible } ⊢ (α,β∈I et α≤β et y∈F) ⇒ f_{αβ}(u_β(y)) = u_α(y).

    Lecture de la relation (5) en (α,β,y) fixés.  (Prop. 1, §III.7.2.)"""
    if leq is None:
        leq = _gleq()
    vf, vu, vi, vF = _t(f), _t(u), _t(i), _t(ff)
    va, vb, vy = var(a), var(b), var(y)
    H = N.assume(cone_compatible(vf, vu, leq, vi, vF, a, b, y))
    return instancie(instancie(instancie(H, va), vb), vy)


def cone_coordonnee_valeur(Efam="E", f="f", u="u", leq=None, i="I", ff="F",
                           a="a", y="yy"):
    """{ α∈I, y∈F } ⊢ pr_α(u(y)) = u_α(y).   (★) instancié — la α-coordonnée de u(y).

    Instance de l'axiome définitionnel (★) : la canonique u envoie y sur le point
    (u_α(y))_α du produit.  (Prop. 1, §III.7.2.)"""
    if leq is None:
        leq = _gleq()
    vE, vf, vu, vi, vF = _t(Efam), _t(f), _t(u), _t(i), _t(ff)
    va, vy = var(a), var(y)
    ax = N.axiome(theorie_cone_canonique(vE, vf, vu, leq, vi, vF),
                  axiome_cone_canonique(vE, vf, vu, leq, vi, vF))
    inst = instancie(instancie(ax, va), vy)            # (α∈I et y∈F) ⇒ pr_α(u(y))=u_α(y)
    Ha = N.assume(appartient(va, vi))
    Hy = N.assume(appartient(vy, vF))
    return N.modus_ponens(conjonction_intro(Ha, Hy), inst)   # pr_α(u(y)) = u_α(y)


def cone_condition_1(Efam="E", f="f", u="u", leq=None, i="I", ff="F",
                     a="a", b="b", y="yy"):
    """{ (u_α) compatible, α,β∈I, α≤β, y∈F } ⊢ pr_α(u(y)) = f_{αβ}(pr_β(u(y))).

    CŒUR de l'existence : le point u(y) = (u_α(y))_α vérifie la condition (1) de la
    limite projective.  Preuve :
        pr_α(u(y)) = u_α(y)                               [(★) en α]
                   = f_{αβ}(u_β(y))                        [compatibilité (5), symétrie]
                   = f_{αβ}(pr_β(u(y)))                    [(★) en β, congruence sous f_{αβ}].
    (Prop. 1, §III.7.2, condition (1).)"""
    if leq is None:
        leq = _gleq()
    vE, vf, vu, vi, vF = _t(Efam), _t(f), _t(u), _t(i), _t(ff)
    va, vb, vy = var(a), var(b), var(y)
    fab = L.appl_proj(vf, va, vb)
    pr_a = E.projection_indice(cone_canonique_valeur(vE, vf, vu, vy), va)
    pr_b = E.projection_indice(cone_canonique_valeur(vE, vf, vu, vy), vb)
    ua_y = cone_u_valeur(vu, va, vy)
    ub_y = cone_u_valeur(vu, vb, vy)
    # 1) pr_α(u(y)) = u_α(y)
    coord_a = cone_coordonnee_valeur(Efam, f, u, leq, i, ff, a, y)            # pr_α(u(y))=u_α(y)
    # 2) u_α(y) = f_{αβ}(u_β(y))   (compatibilité, symétrisée)
    comp_imp = cone_compatibilite(f, u, leq, i, ff, a, b, y)                  # prem ⇒ f_{αβ}(u_β(y))=u_α(y)
    prem = et(et(et(appartient(va, vi), appartient(vb, vi)), leq(va, vb)),
              appartient(vy, vF))
    Hprem = N.assume(prem)
    comp = N.modus_ponens(Hprem, comp_imp)                                    # f_{αβ}(u_β(y))=u_α(y)
    comp_sym = N.modus_ponens(comp, symetrie(E.valeur(fab, ub_y), ua_y))      # u_α(y)=f_{αβ}(u_β(y))
    # 3) f_{αβ}(u_β(y)) = f_{αβ}(pr_β(u(y)))   (congruence : u_β(y)=pr_β(u(y)))
    coord_b = cone_coordonnee_valeur(Efam, f, u, leq, i, ff, b, y)            # pr_β(u(y))=u_β(y)
    coord_b_sym = N.modus_ponens(coord_b, symetrie(pr_b, ub_y))              # u_β(y)=pr_β(u(y))
    cong = N.modus_ponens(coord_b_sym, congruence_terme(
        ub_y, pr_b, E.valeur(fab, var("w")), "w"))                           # f_{αβ}(u_β(y))=f_{αβ}(pr_β(u(y)))
    # chaîne : pr_α(u(y)) = u_α(y) = f_{αβ}(u_β(y)) = f_{αβ}(pr_β(u(y)))
    ch1 = composer_egalites(coord_a, comp_sym)                                # pr_α(u(y))=f_{αβ}(u_β(y))
    return composer_egalites(ch1, cong)                                       # pr_α(u(y))=f_{αβ}(pr_β(u(y)))


def cone_image_dans_limite(Efam="E", f="f", u="u", leq=None, i="I", ff="F",
                           y="yy", a="a", b="b"):
    """{ (u_α) compatible, u(y)∈∏_α E_α, y∈F } ⊢ u(y) ∈ lim←.

    L'image de l'application canonique u tombe dans la limite : u(y)=(u_α(y))_α est
    un point du produit qui vérifie la condition (1) (cf. cone_condition_1, en TOUT
    couple (α,β)).  On conclut par l'axiome (1) de la limite (caractérisation
    appartient_limite_projective).  (Prop. 1, §III.7.2 — bonne-définition de u.)

    Résiduel HONNÊTE « u(y)∈∏ » : c'est l'énoncé « u est bien une application F→∏ »
    (les coordonnées u_α(y)∈E_α se rassemblent en un graphe fonctionnel de domaine
    I) — bonne-définition de la canonique, non prouvée ici (NON vacuous, NON faux)."""
    if leq is None:
        leq = _gleq()
    vE, vf, vu, vi, vF = _t(Efam), _t(f), _t(u), _t(i), _t(ff)
    vy = var(y)
    va, vb = var(a), var(b)
    u_y = cone_canonique_valeur(vE, vf, vu, vy)
    # condition (1) en (α,β,y) : {compatible, prem4} ⊢ pr_α(u(y))=f_{αβ}(pr_β(u(y)))
    # avec prem4 = (α∈I et β∈I et α≤β) et y∈F.
    cc = cone_condition_1(Efam, f, u, leq, i, ff, a, b, y)   # {compatible, prem4, a∈I,b∈I,y∈F} ⊢ eq
    prem3 = et(et(appartient(va, vi), appartient(vb, vi)), leq(va, vb))
    prem4 = et(prem3, appartient(vy, vF))
    # cc garde prem4 ET a∈I,b∈I,y∈F (assumés par les sous-lemmes) : tout décharger en
    # implications, puis ré-alimenter depuis prem3 et y∈F.
    cc1 = N.loi_deduction(prem4, N.loi_deduction(appartient(va, vi),
              N.loi_deduction(appartient(vb, vi),
              N.loi_deduction(appartient(vy, vF), cc))))     # prem4 ⇒ (a∈I ⇒ (b∈I ⇒ (y∈F ⇒ eq)))
    Hy = N.assume(appartient(vy, vF))
    Hprem3 = N.assume(prem3)
    Ha = conjonction_elim_gauche(conjonction_elim_gauche(Hprem3))   # a∈I
    Hb = conjonction_elim_droite(conjonction_elim_gauche(Hprem3))   # b∈I
    Hprem4 = conjonction_intro(Hprem3, Hy)                          # prem4
    eq = N.modus_ponens(Hy, N.modus_ponens(Hb, N.modus_ponens(Ha,
             N.modus_ponens(Hprem4, cc1))))                # {compatible, prem3, y∈F} ⊢ eq
    imp_ab = N.loi_deduction(prem3, eq)                      # {compatible, y∈F} ⊢ prem3 ⇒ eq
    forall_ab = N.generalisation(a, N.generalisation(b, imp_ab))   # = _condition_1(f,leq,I,u(y))
    # appartenance au produit (résiduel HONNÊTE : u est bien F→∏)
    Hprod = N.assume(appartient(u_y, E.produit_famille(vE, vi)))
    both = conjonction_intro(Hprod, forall_ab)              # u(y)∈∏ et condition(1)
    # caractérisation : z∈lim ⇔ (z∈∏ et cond1), instanciée en z=u(y)
    car = L.appartient_limite_projective(Efam, f, leq, i, u_y)
    return N.modus_ponens(both, equivalence_arriere(car))   # u(y) ∈ lim←


def _canonique_proj_valeur_terme(Efam, f, leq, i, va, terme):
    """{ terme∈lim←, α∈I } ⊢ f_α(terme) = pr_α(terme).

    Variante de C.canonique_proj_valeur acceptant un TERME COMPLEXE en z (le helper
    déposé fait `var(z)`, qui corrompt si z est un terme).  On instancie ici
    l'axiome de la valeur canonique projective (C.axiome_canonique_proj) avec le
    terme tel quel — instanciation propre (subst_t), sans capture."""
    vE, vf, vi = _t(Efam), _t(f), _t(i)
    ax = N.axiome(C.theorie_canonique_proj(vE, vf, leq, vi),
                  C.axiome_canonique_proj(vE, vf, leq, vi))
    inst = instancie(instancie(ax, va), terme)          # (terme∈lim← et α∈I) ⇒ f_α(terme)=pr_α(terme)
    Hz = N.assume(appartient(terme, L.lim_proj(vE, vf)))
    Ha = N.assume(appartient(va, vi))
    return N.modus_ponens(conjonction_intro(Hz, Ha), inst)


def cone_relation_6(Efam="E", f="f", u="u", leq=None, i="I", ff="F", a="a", y="yy"):
    """{ u(y)∈lim←, α∈I, y∈F } ⊢ f_α(u(y)) = u_α(y).   (Prop. 1, relation (6).)

    La relation (6) u_α = f_α∘u lue au niveau des valeurs : sur la limite, la
    canonique f_α est pr_α (axiome de la valeur canonique projective), donc
        f_α(u(y)) = pr_α(u(y)) = u_α(y)   [(★) en α].
    (REQUIERT u(y)∈lim← — fourni soit en hypothèse, soit par cone_image_dans_limite.)"""
    if leq is None:
        leq = _gleq()
    vE, vf, vu, vi, vF = _t(Efam), _t(f), _t(u), _t(i), _t(ff)
    va, vy = var(a), var(y)
    u_y = cone_canonique_valeur(vE, vf, vu, vy)
    # f_α(u(y)) = pr_α(u(y))   (la canonique f_α est pr_α sur la limite)
    fa = _canonique_proj_valeur_terme(Efam, f, leq, i, va, u_y)    # {u(y)∈lim←, α∈I} ⊢ f_α(u(y))=pr_α(u(y))
    # pr_α(u(y)) = u_α(y)      [(★) en α]
    coord = cone_coordonnee_valeur(Efam, f, u, leq, i, ff, a, y)   # {α∈I, y∈F} ⊢ pr_α(u(y))=u_α(y)
    return composer_egalites(fa, coord)                       # f_α(u(y)) = u_α(y)


def cone_existence(Efam="E", f="f", u="u", leq=None, i="I", ff="F",
                   a="a", b="b", y="yy"):
    """{ (u_α) compatible, u(y)∈∏, α∈I, y∈F } ⊢ f_α(u(y)) = u_α(y).

    EXISTENCE de la limite projective d'un cône (Proposition 1, 1°) : l'application
    canonique u : F → E vérifie la relation (6) u_α = f_α∘u.  On assemble
    cone_image_dans_limite (u(y)∈lim←, via la compatibilité (5) + u(y)∈∏) puis
    cone_relation_6 (f_α(u(y))=u_α(y) sur la limite).

    Hypothèses résiduelles HONNÊTES :
      • compatibilité (5)        — l'hypothèse de la Proposition 1 ;
      • u(y)∈∏_α E_α             — bonne-définition de la canonique (u est F→∏) ;
      • α∈I, y∈F                 — domaines.
    Aucune n'est fausse ; aucune n'est vacuous (la conclusion f_α(u(y))=u_α(y) n'y
    figure pas).  UNICITÉ : REPORTÉE (extensionnalité du produit)."""
    if leq is None:
        leq = _gleq()
    vE, vf, vu, vi, vF = _t(Efam), _t(f), _t(u), _t(i), _t(ff)
    va, vy = var(a), var(y)
    u_y = cone_canonique_valeur(vE, vf, vu, vy)
    # u(y) ∈ lim←   (de la compatibilité + u(y)∈∏ + y∈F)
    in_lim = cone_image_dans_limite(Efam, f, u, leq, i, ff, y, a, b)
    # f_α(u(y)) = u_α(y)   (relation (6) ; requiert u(y)∈lim←, α∈I, y∈F)
    rel6 = cone_relation_6(Efam, f, u, leq, i, ff, a, y)
    # rel6 a l'hypothèse « u(y)∈lim← » ; on la COUPE par in_lim (modus tollendo sur
    # la déduction) : on remplace cette hypothèse par les hypothèses de in_lim.
    hyp_lim = appartient(u_y, L.lim_proj(vE, vf))
    rel6_imp = N.loi_deduction(hyp_lim, rel6)                 # u(y)∈lim← ⇒ f_α(u(y))=u_α(y)
    return N.modus_ponens(in_lim, rel6_imp)                   # f_α(u(y)) = u_α(y)


def cone_existence_forall(Efam="E", f="f", u="u", leq=None, i="I", ff="F",
                          a="a", b="b", y="yy"):
    """{ (u_α) compatible, u(y)∈∏, y∈F } ⊢ (∀α)( α∈I ⇒ f_α(u(y)) = u_α(y) ).

    Relation (6) sous sa forme « pour tout α » (u_α = f_α∘u pour tout α, Prop. 1).
    On décharge α∈I de cone_existence en implication puis on généralise sur α — α
    n'est libre dans aucune hypothèse résiduelle (compatibilité lie α ; u(y)∈∏ et
    y∈F ne mentionnent pas α libre).  (Prop. 1, §III.7.2, relation (6).)"""
    if leq is None:
        leq = _gleq()
    vi = _t(i)
    va = var(a)
    ex = cone_existence(Efam, f, u, leq, i, ff, a, b, y)      # {compat, u(y)∈∏, α∈I, y∈F} ⊢ eq6
    imp = N.loi_deduction(appartient(va, vi), ex)             # {compat, u(y)∈∏, y∈F} ⊢ α∈I ⇒ eq6
    return N.generalisation(a, imp)                           # (∀α)(α∈I ⇒ f_α(u(y))=u_α(y))


# Résultats DURS introduits mais NON prouvés — honnêteté.
REPORTES = [
    "Proposition 1, 1° UNICITÉ de u (« et une seule ») — extensionnalité du produit "
    "(application_egale_par_valeurs sur la limite) — REPORTÉ.",
    "Proposition 1, 2° (u injective ⇔ (∀y≠z)(∃α) u_α(y)≠u_α(z)) — REPORTÉ.",
    "Bonne-définition u(y)∈∏ (u est bien une application F→∏) — résiduel honnête de "
    "cone_image_dans_limite / cone_existence.",
    "Corollaires 1/2 (composition lim← u_α), Propositions 2-10 — REPORTÉS.",
]


__all__ = [
    "cone_u", "cone_u_valeur", "cone_canonique", "cone_canonique_valeur",
    "cone_compatible", "axiome_cone_canonique", "theorie_cone_canonique",
    "cone_compatibilite", "cone_coordonnee_valeur", "cone_condition_1",
    "cone_image_dans_limite", "cone_relation_6", "cone_existence",
    "cone_existence_forall",
    "REPORTES",
]
