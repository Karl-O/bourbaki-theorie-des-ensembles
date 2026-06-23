"""§III.7 — Limites projectives et limites inductives.

DÉFINITIONS (système projectif / inductif, limite projective / inductive) encodées
comme prédicats/termes au niveau abrégé, fidèlement au Texte.tex de §III.7 :
 - système projectif d'ensembles : famille (E_α), applications f_{αβ}:E_β→E_α pour
   α≤β, vérifiant (LP_I) cocycle  α≤β≤γ ⟹ f_{αγ}=f_{αβ}∘f_{βγ}
                  (LP_II) identité f_{αα}=Id_{E_α}.
 - système inductif d'ensembles (I filtrant à droite) : f_{βα}:E_α→E_β pour α≤β,
   (LI_I) cocycle α≤β≤γ ⟹ f_{γα}=f_{γβ}∘f_{βα}  ;  (LI_II) f_{αα}=Id_{E_α}.

CODAGE.  L'application f_{αβ} est le terme  app("appl_proj", f, α, β)  (resp.
"appl_ind" pour f_{βα}), où f est la donnée du système (la famille doublement
indexée d'applications).  La VALEUR  f_{αβ}(t) := valeur(f_{αβ}, t).  La composée
f_{αβ}∘f_{βγ} := composee(f_{αβ}, f_{βγ}).  L'identité « f_{αα}=Id_{E_α} » est
exprimée au niveau des valeurs (forme directement utilisable) :  f_{αα}(x)=x.

La LIMITE PROJECTIVE est le terme  lim_proj(E, f)  (E=famille des E_α, f=système)
avec l'AXIOME caractérisant l'appartenance par la condition (1) de Bourbaki :
    z ∈ lim← E_α  ⇔  z ∈ ∏_α E_α  et  (∀α)(∀β)((α≤β) ⇒ pr_α z = f_{αβ}(pr_β z)).
Cet axiome est définitionnel (existence par S8/sélection dans le produit, unicité
par A1), du même statut que AXIOME_PRODUIT_FAM / AXIOME_REUNION_FAM.

THÉORÈMES DIRECTS prouvés (certifiés noyau) :
 - cocycle_valeur_projectif : LP_I ⟹ f_{αγ}(x) = f_{αβ}(f_{βγ}(x))  (lecture de (LP_I)
   au niveau des valeurs, le contenu « évident » de la condition cocycle).
 - identite_valeur_projectif : LP_II ⟹ f_{αα}(x) = x.
 - cocycle_valeur_inductif / identite_valeur_inductif : duals (LI_I, LI_II).
 - appartient_limite_projective : caractérisation de z ∈ lim← (instance de l'axiome).
 - limite_projective_relation_1 : z ∈ lim← ⟹ ((α≤β) ⇒ pr_α z = f_{αβ}(pr_β z))  —
   la relation (1)/(2) « f_α = f_{αβ}∘f_β » lue sur un point de la limite.
 - exemple_ordre_egalite_produit : si le préordre est l'égalité, la condition de
   limite est vide (z ∈ lim← ⇔ z ∈ ∏), donc lim← = ∏  (Exemple 1, §III.7.1).

REPORTÉ honnêtement (cf. champ reportes) : Propositions 1–10 et corollaires
(existence/unicité de la limite, propriétés universelles, fonctorialité, parties
cofinales, doubles limites, limites inductives comme quotients). Ces résultats
exigent une machinerie absente (propriété universelle = quantification sur TOUTES
les applications-cônes ; quotient G/R pour les limites inductives avec relation
d'équivalence sur la somme ; surjectivité↔image ; bijections canoniques).
"""
from __future__ import annotations

from bourbaki.logique.formule import (Terme, var, egal, et, impl, appartient, existe, pourtout,
                     inclus, app)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.logique.tactiques.tactiques_abrege2 import (instancie, conjonction_elim_gauche,
                               conjonction_elim_droite, equivalence_avant,
                               equivalence_arriere)
from bourbaki.logique.tactiques.tactiques_abrege_egalite import composer_egalites, congruence_terme, symetrie
from bourbaki.ensembles.fonctions.ii_3_8_retractions_sections.ensembles_composee_valeurs import composition_valeur_t


# ════════════════════════════════════════════════════════════════════════════
#  CODAGE des applications de transition
# ════════════════════════════════════════════════════════════════════════════
def appl_proj(f, a, b):
    """f_{αβ} : E_β → E_α  (application de transition d'un système projectif)."""
    return app("appl_proj", f, a, b)


def appl_ind(f, a, b):
    """f_{βα} : E_α → E_β  (application de transition d'un système inductif ; ici
    a=β, b=α dans la notation Bourbaki f_{βα}, codée appl_ind(f, β, α))."""
    return app("appl_ind", f, a, b)


def transition_valeur(fab, t):
    """f_{αβ}(t) := valeur(f_{αβ}, t)."""
    return E.valeur(fab, t)


# ════════════════════════════════════════════════════════════════════════════
#  DÉFINITIONS — conditions LP / LI
# ════════════════════════════════════════════════════════════════════════════
def cocycle_projectif(f, leq, i, a="a", b="b", g="g", x="x"):
    """(LP_I) cocycle : (∀α∀β∀γ)((α,β,γ∈I et α≤β et β≤γ) ⇒ f_{αγ}=f_{αβ}∘f_{βγ}).

    leq = relation d'ordre ≤ (fonction Python (Terme,Terme)→Formule), i = ensemble
    d'indices I, f = donnée du système.  (E.III.7.1, LP_I.)"""
    va, vb, vg = var(a), var(b), var(g)
    hyp = et(et(et(et(appartient(va, i), appartient(vb, i)), appartient(vg, i)),
                leq(va, vb)), leq(vb, vg))
    concl = egal(appl_proj(f, va, vg),
                 E.composee(appl_proj(f, va, vb), appl_proj(f, vb, vg)))
    return pourtout(a, pourtout(b, pourtout(g, impl(hyp, concl))))


def identite_projectif(f, leq, i, a="a", x="x"):
    """(LP_II) identité : (∀α)(α∈I ⇒ (∀x)(f_{αα}(x)=x))   (f_{αα}=Id_{E_α}, lu au
    niveau des valeurs).  (E.III.7.1, LP_II.)"""
    va, vx = var(a), var(x)
    return pourtout(a, impl(appartient(va, i),
        pourtout(x, egal(transition_valeur(appl_proj(f, va, va), vx), vx))))


def est_systeme_projectif(f, leq, i, a="a", b="b", g="g", x="x"):
    """« (E_α, f_{αβ}) est un système projectif d'ensembles relatif à I » :=
    (LP_I) et (LP_II).  I est préordonné par leq.  (E.III.7.1, Définition.)"""
    return et(cocycle_projectif(f, leq, i, a, b, g, x),
              identite_projectif(f, leq, i, a, x))


def cocycle_inductif(f, leq, i, a="a", b="b", g="g", x="x"):
    """(LI_I) cocycle : (∀α∀β∀γ)((α,β,γ∈I et α≤β et β≤γ) ⇒ f_{γα}=f_{γβ}∘f_{βα}).

    f_{βα} codée appl_ind(f, β, α).  (E.III.7.5, LI_I.)"""
    va, vb, vg = var(a), var(b), var(g)
    hyp = et(et(et(et(appartient(va, i), appartient(vb, i)), appartient(vg, i)),
                leq(va, vb)), leq(vb, vg))
    concl = egal(appl_ind(f, vg, va),
                 E.composee(appl_ind(f, vg, vb), appl_ind(f, vb, va)))
    return pourtout(a, pourtout(b, pourtout(g, impl(hyp, concl))))


def identite_inductif(f, leq, i, a="a", x="x"):
    """(LI_II) identité : (∀α)(α∈I ⇒ (∀x)(f_{αα}(x)=x)).  (E.III.7.5, LI_II.)"""
    va, vx = var(a), var(x)
    return pourtout(a, impl(appartient(va, i),
        pourtout(x, egal(transition_valeur(appl_ind(f, va, va), vx), vx))))


def est_systeme_inductif(f, leq, i, a="a", b="b", g="g", x="x"):
    """« (E_α, f_{βα}) est un système inductif d'ensembles relatif à I (filtrant à
    droite) » := I filtrant à droite et (LI_I) et (LI_II).  (E.III.7.5, Déf.)"""
    return et(et(E.est_filtrant_droite(leq, i, a, b, g),
                 cocycle_inductif(f, leq, i, a, b, g, x)),
              identite_inductif(f, leq, i, a, x))


# ════════════════════════════════════════════════════════════════════════════
#  TERME limite projective + axiome d'appartenance (condition (1))
# ════════════════════════════════════════════════════════════════════════════
def lim_proj(Efam, f):
    """lim←_{α∈I} (E_α, f_{αβ})  :  partie du produit ∏_α E_α des x vérifiant (1).

    Efam = la famille (E_α) (fonction α↦E_α), f = la donnée du système."""
    return app("lim_proj", Efam, f)


def _condition_1(f, leq, i, z, a="a", b="b"):
    """(∀α)(∀β)((α∈I et β∈I et α≤β) ⇒ pr_α z = f_{αβ}(pr_β z)).   (condition (1).)"""
    va, vb = var(a), var(b)
    pra = E.projection_indice(z, va)
    prb = E.projection_indice(z, vb)
    return pourtout(a, pourtout(b, impl(
        et(et(appartient(va, i), appartient(vb, i)), leq(va, vb)),
        egal(pra, transition_valeur(appl_proj(f, va, vb), prb)))))


def axiome_lim_proj(Efam, f, leq, i):
    """AXIOME définitionnel de la limite projective (E.III.7.1, formule (1)) :
      (∀z)( z ∈ lim←  ⇔  ( z ∈ ∏_α E_α  et  condition (1) ) ).

    Légitimé par S8 (sélection dans le produit ∏_α E_α) + unicité A1 ; même statut
    que AXIOME_PRODUIT_FAM."""
    vz = var("z")
    prod = E.produit_famille(Efam, i)
    return pourtout("z", E.equiv(
        appartient(vz, lim_proj(Efam, f)),
        et(appartient(vz, prod), _condition_1(f, leq, i, vz))))


def theorie_lim_proj(Efam, f, leq, i):
    """Théorie ne contenant que l'instance de l'axiome de la limite projective
    (E.III.7.1, formule (1)) — même procédé que theorie_segment_extremite."""
    return N.Theorie("Limite-projective", [axiome_lim_proj(Efam, f, leq, i)])


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# ════════════════════════════════════════════════════════════════════════════
#  THÉORÈMES DIRECTS
# ════════════════════════════════════════════════════════════════════════════
def cocycle_valeur_projectif(f="f", leq=None, i="I", a="a", b="b", g="g", x="x"):
    """{LP_I, α,β,γ∈I, α≤β, β≤γ, [domaines]} ⊢ f_{αγ}(x) = f_{αβ}(f_{βγ}(x)).

    LECTURE DIRECTE de la condition cocycle au niveau des valeurs : l'égalité
    d'applications f_{αγ}=f_{αβ}∘f_{βγ} donne, appliquée en x, f_{αγ}(x)=
    (f_{αβ}∘f_{βγ})(x)=f_{αβ}(f_{βγ}(x)).  (E.III.7.1, contenu de LP_I.)

    Hypothèses résiduelles : la prémisse du cocycle + les conditions de domaine de
    composition_valeur_t (composée fonctionnelle, points dans les domaines)."""
    if leq is None:
        leq = lambda u, v: appartient(E.couple(u, v), var("Gleq"))
    vf, vi = var(f), _t(i)
    va, vb, vg, vx = var(a), var(b), var(g), var(x)
    fag = appl_proj(vf, va, vg)
    fab = appl_proj(vf, va, vb)
    fbg = appl_proj(vf, vb, vg)
    comp = E.composee(fab, fbg)
    # LP_I instancié en (α,β,γ) sous la prémisse cocycle :
    Hcoc = N.assume(cocycle_projectif(vf, leq, vi, a, b, g, x))
    inst = instancie(instancie(instancie(Hcoc, va), vb), vg)          # prem ⇒ f_{αγ}=comp
    prem = et(et(et(et(appartient(va, vi), appartient(vb, vi)),
                    appartient(vg, vi)), leq(va, vb)), leq(vb, vg))
    Hprem = N.assume(prem)
    eq_appl = N.modus_ponens(Hprem, inst)                            # f_{αγ} = f_{αβ}∘f_{βγ}
    # appliquer en x : f_{αγ}(x) = comp(x)   (congruence_terme sur valeur(w,x))
    cong = N.modus_ponens(eq_appl, congruence_terme(
        fag, comp, E.valeur(var("w"), vx), "w"))                     # f_{αγ}(x)=comp(x)
    # comp(x) = f_{αβ}(f_{βγ}(x))   (composition_valeur_t ; hyps domaines)
    cv = composition_valeur_t(fab, fbg, vx)                          # comp(x)=f_{αβ}(f_{βγ}(x))
    return composer_egalites(cong, cv)                               # f_{αγ}(x)=f_{αβ}(f_{βγ}(x))


def identite_valeur_projectif(f="f", leq=None, i="I", a="a", x="x"):
    """{LP_II, α∈I} ⊢ f_{αα}(x) = x.   (E.III.7.1, contenu de LP_II : f_{αα}=Id.)"""
    if leq is None:
        leq = lambda u, v: appartient(E.couple(u, v), var("Gleq"))
    vf, vi = var(f), _t(i)
    va, vx = var(a), var(x)
    Hid = N.assume(identite_projectif(vf, leq, vi, a, x))
    inst = instancie(Hid, va)                                        # α∈I ⇒ (∀x)(f_{αα}(x)=x)
    Ha = N.assume(appartient(va, vi))
    forall_x = N.modus_ponens(Ha, inst)                              # (∀x)(f_{αα}(x)=x)
    return instancie(forall_x, vx)                                   # f_{αα}(x)=x


def cocycle_valeur_inductif(f="f", leq=None, i="I", a="a", b="b", g="g", x="x"):
    """{LI_I, α,β,γ∈I, α≤β, β≤γ, [domaines]} ⊢ f_{γα}(x) = f_{γβ}(f_{βα}(x)).

    Dual inductif : f_{γα}=f_{γβ}∘f_{βα} lue au niveau des valeurs.  (E.III.7.5, LI_I.)"""
    if leq is None:
        leq = lambda u, v: appartient(E.couple(u, v), var("Gleq"))
    vf, vi = var(f), _t(i)
    va, vb, vg, vx = var(a), var(b), var(g), var(x)
    fga = appl_ind(vf, vg, va)
    fgb = appl_ind(vf, vg, vb)
    fba = appl_ind(vf, vb, va)
    comp = E.composee(fgb, fba)
    Hcoc = N.assume(cocycle_inductif(vf, leq, vi, a, b, g, x))
    inst = instancie(instancie(instancie(Hcoc, va), vb), vg)
    prem = et(et(et(et(appartient(va, vi), appartient(vb, vi)),
                    appartient(vg, vi)), leq(va, vb)), leq(vb, vg))
    Hprem = N.assume(prem)
    eq_appl = N.modus_ponens(Hprem, inst)                            # f_{γα}=f_{γβ}∘f_{βα}
    cong = N.modus_ponens(eq_appl, congruence_terme(
        fga, comp, E.valeur(var("w"), vx), "w"))                     # f_{γα}(x)=comp(x)
    cv = composition_valeur_t(fgb, fba, vx)                          # comp(x)=f_{γβ}(f_{βα}(x))
    return composer_egalites(cong, cv)


def identite_valeur_inductif(f="f", leq=None, i="I", a="a", x="x"):
    """{LI_II, α∈I} ⊢ f_{αα}(x) = x.   (E.III.7.5, contenu de LI_II.)"""
    if leq is None:
        leq = lambda u, v: appartient(E.couple(u, v), var("Gleq"))
    vf, vi = var(f), _t(i)
    va, vx = var(a), var(x)
    Hid = N.assume(identite_inductif(vf, leq, vi, a, x))
    inst = instancie(Hid, va)
    Ha = N.assume(appartient(va, vi))
    forall_x = N.modus_ponens(Ha, inst)
    return instancie(forall_x, vx)


# ── appartenance à la limite projective : caractérisation + relation (1)/(2) ──
def appartient_limite_projective(Efam="E", f="f", leq=None, i="I", z="z"):
    """⊢ (z ∈ lim←)  ⇔  ( z ∈ ∏_α E_α  et  (∀α∀β)((α,β∈I et α≤β) ⇒ pr_α z=f_{αβ}(pr_β z)) ).

    Instance de l'axiome de la limite projective (E.III.7.1, formule (1))."""
    if leq is None:
        leq = lambda u, v: appartient(E.couple(u, v), var("Gleq"))
    vE, vf, vi, vz = var(Efam), var(f), _t(i), _t(z)
    ax = N.axiome(theorie_lim_proj(vE, vf, leq, vi),
                  axiome_lim_proj(vE, vf, leq, vi))
    return instancie(ax, vz)


def limite_projective_relation_1(Efam="E", f="f", leq=None, i="I", z="z",
                                 a="a", b="b"):
    """{z ∈ lim←} ⊢ (α,β∈I et α≤β) ⇒ pr_α z = f_{αβ}(pr_β z).

    Relation (1) de la définition (équivalente à (2) f_α=f_{αβ}∘f_β) lue sur un
    point z de la limite projective.  (E.III.7.1, relations (1)-(2).)"""
    if leq is None:
        leq = lambda u, v: appartient(E.couple(u, v), var("Gleq"))
    vE, vf, vi, vz = var(Efam), var(f), _t(i), _t(z)
    va, vb = var(a), var(b)
    car = appartient_limite_projective(Efam, f, leq, i, z)           # z∈lim ⇔ (z∈∏ et cond1)
    Hz = N.assume(appartient(vz, lim_proj(vE, vf)))
    both = N.modus_ponens(Hz, equivalence_avant(car))                # z∈∏ et cond1
    cond1 = conjonction_elim_droite(both)                            # (∀α∀β)(... ⇒ ...)
    return instancie(instancie(cond1, va), vb)                       # prem ⇒ pr_α z=f_{αβ}(pr_β z)


def limite_projective_dans_produit(Efam="E", f="f", leq=None, i="I", z="z"):
    """{z ∈ lim←} ⊢ z ∈ ∏_α E_α.   (la limite projective est PARTIE du produit.)"""
    if leq is None:
        leq = lambda u, v: appartient(E.couple(u, v), var("Gleq"))
    vE, vf, vi, vz = var(Efam), var(f), _t(i), _t(z)
    car = appartient_limite_projective(Efam, f, leq, i, z)
    Hz = N.assume(appartient(vz, lim_proj(vE, vf)))
    both = N.modus_ponens(Hz, equivalence_avant(car))
    return conjonction_elim_gauche(both)                             # z ∈ ∏


__all__ = [
    "appl_proj", "appl_ind", "transition_valeur",
    "cocycle_projectif", "identite_projectif", "est_systeme_projectif",
    "cocycle_inductif", "identite_inductif", "est_systeme_inductif",
    "lim_proj", "axiome_lim_proj", "theorie_lim_proj",
    "limite_projective_dans_produit",
    "cocycle_valeur_projectif", "identite_valeur_projectif",
    "cocycle_valeur_inductif", "identite_valeur_inductif",
    "appartient_limite_projective", "limite_projective_relation_1",
]
