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

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (Terme, var, egal, et, impl, appartient, existe, pourtout,
                     inclus, app)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (instancie, conjonction_elim_gauche,
                               conjonction_elim_droite, equivalence_avant,
                               equivalence_arriere)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import composer_egalites, congruence_terme, symetrie
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_8_retractions_sections.ensembles_composee_valeurs import composition_valeur_t


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
# @livre Ch.III §7.1 Def.- | E III.52 L.1-12 | PDF p.155
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


# @livre Ch.III §7.1 Def.- | E III.52 L.1-12 | PDF p.155
def identite_projectif(f, leq, i, a="a", x="x"):
    """(LP_II) identité : (∀α)(α∈I ⇒ (∀x)(f_{αα}(x)=x))   (f_{αα}=Id_{E_α}, lu au
    niveau des valeurs).  (E.III.7.1, LP_II.)"""
    va, vx = var(a), var(x)
    return pourtout(a, impl(appartient(va, i),
        pourtout(x, egal(transition_valeur(appl_proj(f, va, va), vx), vx))))


# @livre Ch.III §7.1 Def.- | E III.52 L.1-12 | PDF p.155
# @livre Ch.R §6 Def.- | E.R.31 item 14 (système projectif d'ensembles relatif à I) | PDF p.334
def est_systeme_projectif(Efam, f, leq, i, a="a", b="b", g="g", x="x", z="zt"):
    """« (E_α, f_{αβ}) est un système projectif d'ensembles relatif à I » :=
    TYPAGE des transitions  et  (LP_I)  et  (LP_II).   (E.III.7.1, Définition.)

    ✅ ÉCART DE FIDÉLITÉ COMBLÉ le 5 août 2026 (cf. `docs/journal/ANOMALIES.md`).
    La définition n'encodait que les deux conditions NUMÉROTÉES et laissait
    tomber ce que Bourbaki pose en prose juste avant : « soit f_{αβ} **une
    application de E_β dans E_α** ».  Ce typage fait partie de la donnée du
    système — sans lui, « f_{αβ}(z) ∈ E_α » est indisponible, et toute preuve
    qui construit un point à partir des transitions est bloquée.

    ⚠️ La signature a donc gagné `Efam` EN TÊTE : on ne peut pas typer les
    transitions sans nommer la famille d'ensembles.  C'est précisément parce que
    l'ancienne signature ignorait `Efam` que la condition avait été omise — le
    manque était inscrit dans le TYPE de la fonction, pas seulement dans son
    corps.

    Les deux conditions numérotées restent disponibles séparément
    (`cocycle_projectif`, `identite_projectif`) pour les énoncés qui n'ont besoin
    que d'elles."""
    return et(et(cocycle_projectif(f, leq, i, a, b, g, x),
                 identite_projectif(f, leq, i, a, x)),
              transitions_typees(Efam, f, leq, i, a, b, z))


# @livre Ch.III §7.1 Def.- | E III.51 L.30-32 | PDF p.154  (le TYPAGE des transitions : « f_{αβ} une application de E_β dans E_α » — condition NON numérotée de la Définition, désormais CONJOINT de est_systeme_projectif ; exposée séparément pour les preuves qui n'ont besoin qu'elle)
def transitions_typees(Efam, f, leq, i, a="a", b="b", z="zt"):
    """« chaque f_{αβ} envoie E_β dans E_α » :=
        (∀α)(∀β)( (α∈I et β∈I et α≤β) ⇒ (∀z)( z ∈ E_β ⇒ f_{αβ}(z) ∈ E_α ) ).

    La condition que Bourbaki pose en prose juste avant (LP_I) et (LP_II).  Elle
    est depuis le 5 août 2026 un CONJOINT de `est_systeme_projectif` (l'écart de
    fidélité est comblé) ; elle reste exposée séparément parce que la plupart des
    preuves n'ont besoin QUE d'elle, et la porter seule est plus honnête que de
    supposer tout le système.

    Elle est indispensable dès qu'on veut placer dans lim← un point construit à
    partir des transitions : c'est elle qui donne « la coordonnée tombe bien dans
    E_α ».  Sans elle, l'inclusion réciproque de la surjectivité (Prop. 3
    §III.7.2) est hors d'atteinte."""
    va, vb, vz = var(a), var(b), var(z)
    Ea = E.valeur_famille(_t(Efam), va)
    Eb = E.valeur_famille(_t(Efam), vb)
    return pourtout(a, pourtout(b, impl(
        et(et(appartient(va, i), appartient(vb, i)), leq(va, vb)),
        pourtout(z, impl(appartient(vz, Eb),
                         appartient(transition_valeur(appl_proj(f, va, vb), vz),
                                    Ea))))))


# @livre Ch.III §7.1 Def.- | E III.51 L.30-32 | PDF p.154  (le typage COMPLET : « f_{αβ} est une APPLICATION de E_β dans E_α », c.-à-d. son graphe est dans (E_α)^(E_β) — fonctionnel, défini partout, à valeurs dans E_α)
def transitions_applications(Efam, f, leq, i, a="a", b="b"):
    """« chaque f_{αβ} est une APPLICATION de E_β dans E_α » :=
        (∀α)(∀β)( (α∈I et β∈I et α≤β) ⇒ f_{αβ} ∈ (E_α)^(E_β) ).

    ⚠️ PLUS FORT que `transitions_typees`, et c'est la forme FIDÈLE.  Découvert
    le 5 août 2026 en butant sur l'inclusion réciproque de la Prop. 3 : la
    machinerie du prolongement réclame, outre les valeurs dans E_α, que les
    transitions soient FONCTIONNELLES et DÉFINIES aux points utilisés — ce sont
    ces conditions de domaine (« (∃y)((t,y) ∈ f_{αβ}) ») qui restaient
    indémontrables.  Or « application de E_β dans E_α » dit les trois d'un coup.
    `transitions_typees` n'en capturait qu'UNE : le premier comblement de
    l'écart de fidélité (4-5 août) était donc PARTIEL.

    ENCODAGE : l'EXPOSANT (E_α)^(E_β) — l'ensemble des GRAPHES fonctionnels de
    domaine E_β — et non 𝓕(E_β;E_α), qui est l'ensemble des TRIPLETS.  Les
    transitions du dépôt sont manipulées comme des graphes (`valeur(f_{αβ}, t)`
    sans `graphe_de`), donc c'est l'exposant qui s'apparie.  Se tromper des deux
    donne un terme qui ne se raccorde à rien.

    Les trois conséquences se lisent par `axiome_exposant` : inclusion dans
    E_β×E_α, fonctionnalité, domaine = E_β."""
    va, vb = var(a), var(b)
    Ea = E.valeur_famille(_t(Efam), va)
    Eb = E.valeur_famille(_t(Efam), vb)
    return pourtout(a, pourtout(b, impl(
        et(et(appartient(va, i), appartient(vb, i)), leq(va, vb)),
        appartient(appl_proj(f, va, vb), E.exposant(Eb, Ea)))))


# @livre Ch.III §7.1 Def.- | E III.51 L.30-32 | PDF p.154  (ce que le typage complet DONNE : les transitions sont fonctionnelles et définies sur tout E_β)
def transitions_fonctionnelles_et_totales(Efam="E", f="f", leq=None, i="I",
                                          a="a", b="b"):
    """{ transitions applications,  (α∈I et β∈I et α≤β) }
        ⊢ ( est_fonctionnel(f_{αβ}),  dom f_{αβ} = E_β ).

    Les deux conséquences que `transitions_typees` ne donnait PAS et qui
    bloquaient l'inclusion réciproque de la Prop. 3 : la machinerie du
    prolongement réclame que les transitions soient fonctionnelles et définies
    aux points utilisés (conditions « (∃y)((t,y) ∈ f_{αβ}) », mesurées).

    Lecture directe de `axiome_exposant` : G ∈ F^E ⇔ ((G⊂E×F et G fonctionnel)
    et dom G = E).  Rend le couple (fonctionnalité, domaine)."""
    if leq is None:
        leq = lambda u, v: appartient(E.couple(u, v), var("Gleq"))
    vE, vi = _t(Efam), _t(i)
    va, vb = var(a), var(b)
    Ea, Eb = E.valeur_famille(vE, va), E.valeur_famille(vE, vb)
    fab = appl_proj(_t(f), va, vb)
    h_prem = N.assume(et(et(appartient(va, vi), appartient(vb, vi)), leq(va, vb)))
    h_app = N.modus_ponens(h_prem, instancie(instancie(
        N.assume(transitions_applications(vE, _t(f), leq, vi, a, b)), va), vb))
    corps = N.modus_ponens(h_app, equivalence_avant(instancie(
        N.axiome(E.theorie_exposant(Eb, Ea), E.axiome_exposant(Eb, Ea)), fab)))
    func = conjonction_elim_droite(conjonction_elim_gauche(corps))
    dom = conjonction_elim_droite(corps)
    assert func.conclusion == E.est_fonctionnel(fab), \
        "transitions_fonctionnelles_et_totales : ≠ est_fonctionnel(f_{αβ})"
    assert dom.conclusion == egal(E.dom(fab), Eb), \
        "transitions_fonctionnelles_et_totales : ≠ (dom f_{αβ} = E_β)"
    return func, dom


# @livre Ch.III §7.1 Def.- | E III.51 L.30-32 | PDF p.154  (👑 la conséquence OPÉRATOIRE du typage complet : une transition est DÉFINIE en tout point de E_β — c'est la condition qui bloquait l'inclusion réciproque de la Prop. 3)
def transition_definie_en(t, Efam="E", f="f", leq=None, i="I", a="a", b="b",
                          y="y"):
    """{ transitions applications,  (α∈I et β∈I et α≤β),  t ∈ E_β }
        ⊢ (∃y)((t, f_{αβ}(t)-candidat) ∈ f_{αβ})   c.-à-d. « f_{αβ} est définie en t ».

    C'est LA brique que le typage partiel ne pouvait pas fournir.  Les preuves
    du prolongement cofinal (Prop. 3) réclament, à chaque évaluation d'une
    transition, la garantie que le point est bien dans son domaine — sans quoi
    `valeur(f_{αβ}, t)` est un τ vide et les briques de valeur ne s'appliquent
    pas.  Mesuré : 6 hypothèses résiduelles de cette forme.

    Route (celle de `hyp_applicative_de_application`, E.R.9) : `dom f_{αβ} = E_β`
    vient de `transitions_fonctionnelles_et_totales` ; S6 transporte
    « t ∈ E_β » en « t ∈ dom f_{αβ} » ; AXIOME_DOM le convertit en l'existentielle.

    ⚠️ Le liant de l'existentielle est celui d'AXIOME_DOM — le paramètre `y` est
    documentaire, il ne le renomme pas : deux α-variants sont DISTINCTS pour le
    noyau, donc la cible doit être produite par l'axiome lui-même."""
    if leq is None:
        leq = lambda u, v: appartient(E.couple(u, v), var("Gleq"))
    vE, vt = _t(Efam), _t(t)
    vb = var(b)
    Eb = E.valeur_famille(vE, vb)
    fab = appl_proj(_t(f), var(a), vb)
    _, h_dom = transitions_fonctionnelles_et_totales(vE, _t(f), leq, _t(i), a, b)
    s6 = N.s6(E.dom(fab), Eb, "w", appartient(vt, var("w")))
    t_dans_dom = N.modus_ponens(
        N.assume(appartient(vt, Eb)),
        equivalence_arriere(N.modus_ponens(h_dom, s6)))
    membre = instancie(instancie(
        N.axiome(E.theorie_ensembles(), E.AXIOME_DOM), fab), vt)
    res = N.modus_ponens(t_dans_dom, equivalence_avant(membre))
    assert res.conclusion.tag == "exists", \
        "transition_definie_en : la conclusion n'est pas une existentielle"
    assert appartient(vt, Eb) in res.hypotheses, \
        "transition_definie_en : l'hypothèse « t ∈ E_β » a disparu"
    assert len(res.hypotheses) == 3, \
        f"transition_definie_en : hyps ≠ 3 ({len(res.hypotheses)})"
    return res


# @livre Ch.III §7.1 Def.- | E III.51 L.30-32 | PDF p.154  (l'autre moitié du typage, à VALEURS : f_{αβ}(t) ∈ E_α — c'est elle qui place les valeurs de transition dans les fibres)
def transition_valeur_dans_E(t, Efam="E", f="f", leq=None, i="I", a="a", b="b",
                             z="zt"):
    """{ transitions typées,  (α∈I et β∈I et α≤β),  t ∈ E_β }
        ⊢ f_{αβ}(t) ∈ E_α.                                            [3 hyps].

    Le PENDANT de `transition_definie_en`, et les deux ensemble disent
    « f_{αβ} est une application de E_β dans E_α » : celui-ci en tire les
    VALEURS (`transitions_typees`), celui-là le DOMAINE (`transitions_applications`).

    👑 Ce n'est pas une redite : mesuré sur les hypothèses résiduelles de
    l'inclusion réciproque de la Prop. 3, les deux moitiés sont **chacune
    porteuse, à des endroits différents** — 6 hypothèses réclamaient le domaine,
    3 réclament les valeurs.  C'est la confirmation la plus nette que le typage
    partiel du 4-5 août ne pouvait pas suffire : il ne couvrait qu'un des deux
    besoins, et l'autre était invisible tant que le premier bloquait."""
    if leq is None:
        leq = lambda u, v: appartient(E.couple(u, v), var("Gleq"))
    vE, vi, vt = _t(Efam), _t(i), _t(t)
    va, vb = var(a), var(b)
    Ea, Eb = E.valeur_famille(vE, va), E.valeur_famille(vE, vb)
    h_prem = N.assume(et(et(appartient(va, vi), appartient(vb, vi)), leq(va, vb)))
    corps = N.modus_ponens(h_prem, instancie(instancie(
        N.assume(transitions_typees(vE, _t(f), leq, vi, a, b, z)), va), vb))
    res = N.modus_ponens(N.assume(appartient(vt, Eb)), instancie(corps, vt))
    assert res.conclusion == appartient(
        transition_valeur(appl_proj(_t(f), va, vb), vt), Ea), \
        "transition_valeur_dans_E : ≠ (f_{αβ}(t) ∈ E_α)"
    assert len(res.hypotheses) == 3, \
        f"transition_valeur_dans_E : hyps ≠ 3 ({len(res.hypotheses)})"
    return res


# @livre Ch.III §7.5 Def.- | E III.61 L.3-4 | PDF p.164
def cocycle_inductif(f, leq, i, a="a", b="b", g="g", x="x"):
    """(LI_I) cocycle : (∀α∀β∀γ)((α,β,γ∈I et α≤β et β≤γ) ⇒ f_{γα}=f_{γβ}∘f_{βα}).

    f_{βα} codée appl_ind(f, β, α).  (E.III.7.5, LI_I.)"""
    va, vb, vg = var(a), var(b), var(g)
    hyp = et(et(et(et(appartient(va, i), appartient(vb, i)), appartient(vg, i)),
                leq(va, vb)), leq(vb, vg))
    concl = egal(appl_ind(f, vg, va),
                 E.composee(appl_ind(f, vg, vb), appl_ind(f, vb, va)))
    return pourtout(a, pourtout(b, pourtout(g, impl(hyp, concl))))


# @livre Ch.III §7.5 Def.- | E III.61 L.3-4 | PDF p.164
def identite_inductif(f, leq, i, a="a", x="x"):
    """(LI_II) identité : (∀α)(α∈I ⇒ (∀x)(f_{αα}(x)=x)).  (E.III.7.5, LI_II.)"""
    va, vx = var(a), var(x)
    return pourtout(a, impl(appartient(va, i),
        pourtout(x, egal(transition_valeur(appl_ind(f, va, va), vx), vx))))


# @livre Ch.III §7.5 Def.- | E III.60 L.33-35 | PDF p.163
#   (début de la définition, sous l'intitulé « 5. Limites inductives » : « I ensemble
#    préordonné filtrant à droite, (E_α) famille d'ensembles » — suite E III.61)
# @livre Ch.III §7.5 Def.- | E III.61 L.1-31 | PDF p.164
# @livre Ch.R §6 Def.- | E.R.30 item 13 (système inductif d'ensembles relatif à I) | PDF p.333
def est_systeme_inductif(f, leq, i, a="a", b="b", g="g", x="x"):
    """« (E_α, f_{βα}) est un système inductif d'ensembles relatif à I (filtrant à
    droite) » := I filtrant à droite et (LI_I) et (LI_II).  (E.III.7.5, Déf.)"""
    return et(et(E.est_filtrant_droite(leq, i, a, b, g),
                 cocycle_inductif(f, leq, i, a, b, g, x)),
              identite_inductif(f, leq, i, a, x))


# ════════════════════════════════════════════════════════════════════════════
#  TERME limite projective + axiome d'appartenance (condition (1))
# ════════════════════════════════════════════════════════════════════════════
# @livre Ch.III §7.1 Def.- | E III.52 L.1-7 | PDF p.155
# @livre Ch.R §6 Def.- | E.R.31 item 14 (limite projective E = lim<- Ea, partie du produit) | PDF p.334
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


# @livre Ch.III §7.1 Def.- | E III.52 L.4-4 | PDF p.155
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
# @livre Ch.III §7.1 Def.- | E III.52 L.4-4 | PDF p.155
def appartient_limite_projective(Efam="E", f="f", leq=None, i="I", z="z"):
    """⊢ (z ∈ lim←)  ⇔  ( z ∈ ∏_α E_α  et  (∀α∀β)((α,β∈I et α≤β) ⇒ pr_α z=f_{αβ}(pr_β z)) ).

    Instance de l'axiome de la limite projective (E.III.7.1, formule (1)).

    ⚠️ TERM-SAFE depuis le 5 août 2026 : `Efam` et `f` passent par `_t` et non
    plus par `var`.  Avec `var`, un Efam déjà TERME devenait `var(Terme)` —
    doublement enveloppé — et l'énoncé produit ne s'appariait plus avec celui
    des autres briques.  Neutre pour les appels par NOM (tous les appels du
    dépôt) ; c'est ce qui permet de viser la limite d'un système CONSTRUIT,
    comme le système restreint de la Prop. 3."""
    if leq is None:
        leq = lambda u, v: appartient(E.couple(u, v), var("Gleq"))
    vE, vf, vi, vz = _t(Efam), _t(f), _t(i), _t(z)
    ax = N.axiome(theorie_lim_proj(vE, vf, leq, vi),
                  axiome_lim_proj(vE, vf, leq, vi))
    return instancie(ax, vz)


# @livre Ch.III §7.1 Def.- | E III.52 L.4-11 | PDF p.155
def limite_projective_relation_1(Efam="E", f="f", leq=None, i="I", z="z",
                                 a="a", b="b"):
    """{z ∈ lim←} ⊢ (α,β∈I et α≤β) ⇒ pr_α z = f_{αβ}(pr_β z).

    Relation (1) de la définition (équivalente à (2) f_α=f_{αβ}∘f_β) lue sur un
    point z de la limite projective.  (E.III.7.1, relations (1)-(2).)

    ⚠️ TERM-SAFE depuis le 5 août 2026 — même correction que
    `appartient_limite_projective` : `_t` au lieu de `var`."""
    if leq is None:
        leq = lambda u, v: appartient(E.couple(u, v), var("Gleq"))
    vE, vf, vi, vz = _t(Efam), _t(f), _t(i), _t(z)
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
    "transitions_typees", "transitions_applications",
    "transitions_fonctionnelles_et_totales",
    "cocycle_inductif", "identite_inductif", "est_systeme_inductif",
    "lim_proj", "axiome_lim_proj", "theorie_lim_proj",
    "limite_projective_dans_produit",
    "cocycle_valeur_projectif", "identite_valeur_projectif",
    "cocycle_valeur_inductif", "identite_valeur_inductif",
    "appartient_limite_projective", "limite_projective_relation_1",
]
