"""§III.7 — Limites projectives / inductives : notions COMPLÉMENTAIRES.

Ce module INTRODUIT (définitions fidèles, prédicats/termes au niveau abrégé) les
notions de §III.7 qui n'étaient PAS encore couvertes par
`bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites.ensembles_limites` (lequel pose déjà : système
projectif/inductif (LP_I/LP_II/LI_I/LI_II), terme `lim_proj` + son axiome (1),
cocycle/identité au niveau des valeurs, appartenance à lim←).  Il RÉUTILISE ce
module (import, AUCUNE modification) et en suit les conventions :

  • le préordre ≤ sur I est donné par une fonction Python `leq : (Terme,Terme)→Formule` ;
  • f_{αβ} (projectif) = `appl_proj(f,α,β)` ;  f_{βα} (inductif) = `appl_ind(f,β,α)` ;
  • f_{αβ}(t) = E.valeur(f_{αβ}, t) ;  composée = E.composee(·,·) ;
  • lim← E_α = `lim_proj(Efam, f)`.

NOTIONS INTRODUITES ICI (toutes §III.7) :

  PROJECTIF
   • application_canonique_proj  f_α : E → E_α  (restriction à E de pr_α), via son
     graphe `f_canon_proj(Efam,f,α)` + AXIOME définitionnel de sa valeur
     f_α(z)=pr_α z  (formule (2)).
   • est_systeme_projectif_applications  (u_α : E_α→F_α, u_α∘f_{αβ}=g_{αβ}∘u_β)  et
     le terme `lim_proj_applications`  u = lim← u_α  (Cor.1, §III.7.2).
   • est_systeme_projectif_parties  (M_α⊂E_α, f_{αβ}⟨M_β⟩⊂M_α)  (§III.7.1).
   • restriction d'un système projectif à une partie J + application canonique g
     (formules (3) et (4)).

  INDUCTIF (le grand manque : la limite inductive comme QUOTIENT)
   • relation_coherence_inductive  R{x,y} sur la somme G=∑E_α  (§III.7.5) :
        « (∃γ)( γ≥λ(x) et γ≥λ(y) et f_{γ,λ(x)}(x) = f_{γ,λ(y)}(y) ) » ;
   • terme `lim_ind(Efam,f,leq,i)` = G/R  (quotient de la somme par R) ;
   • est_systeme_inductif_applications + terme `lim_ind_applications` (Cor.1, §III.7.6) ;
   • est_systeme_inductif_parties (M_α⊂E_α, f_{βα}⟨M_α⟩⊂M_β)  (§III.7.6) ;
   • application_canonique_ind  f_α : E_α → E  (restriction à E_α de la canonique
     f : G→G/R), via son graphe `f_canon_ind` + AXIOME de sa valeur f_α(x)=Cl_R(x).

AXIOMES de membership employés : tous DÉFINITIONNELS (S8 sélection + A1 unicité),
isolés dans des THÉORIES DÉDIÉES paramétrées (motif theorie_segment_extremite /
axiome_lim_proj).  theorie_ensembles() reste à 22 axiomes (rien n'y est ajouté).

THÉORÈMES DIRECTS prouvés (certifiés noyau) : caractérisation des valeurs
canoniques (instances d'axiome), relation (2) f_α=f_{αβ}∘f_β lue au niveau des
valeurs, relation (22) f_β∘f_{βα}=f_α (inductif) lue au niveau des valeurs,
décompositions des définitions conjonctives.

REPORTÉ honnêtement : Propositions 1–10 et corollaires (existence/unicité par
propriété universelle, fonctorialité lim←/lim→, parties cofinales bijectives,
doubles limites, R d'équivalence, b) de Th.1) — machinerie absente (cônes
universels, quotient effectif, surjectivité↔image).  On INTRODUIT les notions ;
les théorèmes durs sont nommés mais non prouvés.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, et, impl, appartient, existe, pourtout, inclus, app,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites import ensembles_limites as L
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    instancie, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere,
)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
    composer_egalites, symetrie,
)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def _gleq():
    """Préordre ≤ par défaut, lu sur un graphe Gleq (même défaut que le module limites)."""
    return lambda u, v: appartient(E.couple(u, v), var("Gleq"))


# Graphe (Terme) du préordre par défaut, support du `leq` ci-dessus : ≤ = Gleq.
# IMPORTANT : un préordre s'utilise comme FONCTION `leq:(T,T)→Formule` DANS les
# formules, mais NE PEUT PAS figurer comme argument d'un terme `app(...)` (un terme
# ne contient que des Termes).  Quand un TERME doit mémoriser le préordre (graphe
# de cohérence, limite inductive), on lui passe ce GRAPHE `gleq` (un Terme).
_GRAPHE_LEQ_DEFAUT = var("Gleq")


# ════════════════════════════════════════════════════════════════════════════
#  PROJECTIF — application canonique f_α : E → E_α  (E.III.7.1, formules (2))
# ════════════════════════════════════════════════════════════════════════════
# @livre Ch.III §7.1 Def.- | E III.52 L.13-15 | PDF p.155
# @livre Ch.R §6 Def.- | E.R.31 item 14 (application canonique fa : E -> Ea) | PDF p.334
def f_canon_proj(Efam, f, a):
    """Graphe de l'application canonique f_α : E → E_α  (E = lim← E_α).

    « f_α est la restriction à E de la projection pr_α »  (E.III.7.1).  Codé comme
    la restriction du graphe de pr_α (codé `app("pr_indice", α)`) à la limite E."""
    return E.restriction(app("pr_indice", a), L.lim_proj(Efam, f))


def application_canonique_proj_valeur(Efam, f, a, z):
    """Terme f_α(z) := valeur(f_canon_proj, z)  (valeur de la canonique en z∈E)."""
    return E.valeur(f_canon_proj(Efam, f, a), z)


def axiome_canonique_proj(Efam, f, leq, i, a="a", z="z"):
    """AXIOME définitionnel (E.III.7.1, (2)) : pour z∈E=lim← et α∈I,
        f_α(z) = pr_α z.

    « f_α est la restriction à E de pr_α » : sur la limite, la canonique COÏNCIDE
    avec la coordonnée d'indice α.  S8 (graphe restreint) + A1, comme AXIOME_RESTRICTION."""
    va, vz = var(a), var(z)
    hyp = et(appartient(vz, L.lim_proj(Efam, f)), appartient(va, i))
    concl = egal(application_canonique_proj_valeur(Efam, f, va, vz),
                 E.projection_indice(vz, va))
    return pourtout(a, pourtout(z, impl(hyp, concl)))


def theorie_canonique_proj(Efam, f, leq, i):
    """Théorie dédiée ne contenant que l'axiome de la valeur canonique projective."""
    return N.Theorie("Canonique-projective", [axiome_canonique_proj(Efam, f, leq, i)])


def canonique_proj_valeur(Efam="E", f="f", leq=None, i="I", a="a", z="z"):
    """{z∈lim←, α∈I} ⊢ f_α(z) = pr_α z.   (E.III.7.1, formule (2), lue ponctuellement.)

    Instance de l'axiome de la valeur canonique : sur la limite, la canonique f_α
    n'est autre que la projection pr_α."""
    if leq is None:
        leq = _gleq()
    vE, vf, vi = _t(Efam), _t(f), _t(i)
    va, vz = var(a), var(z)
    ax = N.axiome(theorie_canonique_proj(vE, vf, leq, vi),
                  axiome_canonique_proj(vE, vf, leq, vi))
    inst = instancie(instancie(ax, va), vz)               # hyp ⇒ f_α(z)=pr_α z
    Hz = N.assume(appartient(vz, L.lim_proj(vE, vf)))
    Ha = N.assume(appartient(va, vi))
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import conjonction_intro
    return N.modus_ponens(conjonction_intro(Hz, Ha), inst)   # f_α(z)=pr_α z


# @livre Ch.III §7.1 Prop.- | E III.52 L.16-18 | PDF p.155
def relation_2_projective(Efam="E", f="f", leq=None, i="I", a="a", b="b", z="z"):
    """{z∈lim←, α,β∈I, α≤β} ⊢ f_α(z) = f_{αβ}(f_β(z)).   (E.III.7.1, formule (2).)

    Relation (2) f_α=f_{αβ}∘f_β lue sur un point z de la limite : c'est la relation
    (1) (pr_α z=f_{αβ}(pr_β z)) habillée par f_α=pr_α et f_β=pr_β sur la limite."""
    if leq is None:
        leq = _gleq()
    vE, vf, vi = _t(Efam), _t(f), _t(i)
    va, vb, vz = var(a), var(b), var(z)
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import conjonction_intro
    # (1) sur la limite : pr_α z = f_{αβ}(pr_β z)
    rel1_imp = L.limite_projective_relation_1(Efam, f, leq, i, z, a, b)   # prem ⇒ pr_α z=f_{αβ}(pr_β z)
    prem = et(et(appartient(va, vi), appartient(vb, vi)), leq(va, vb))
    Hprem = N.assume(prem)
    eq1 = N.modus_ponens(Hprem, rel1_imp)                 # pr_α z = f_{αβ}(pr_β z)
    # f_α(z) = pr_α z   et   f_β(z) = pr_β z
    fa = canonique_proj_valeur(Efam, f, leq, i, a, z)     # f_α(z)=pr_α z
    fb = canonique_proj_valeur(Efam, f, leq, i, b, z)     # f_β(z)=pr_β z
    # f_α(z) = pr_α z = f_{αβ}(pr_β z)
    chaine = composer_egalites(fa, eq1)                   # f_α(z) = f_{αβ}(pr_β z)
    # remplacer pr_β z par f_β(z) :  f_{αβ}(pr_β z) = f_{αβ}(f_β(z)), via congruence
    from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import congruence_terme
    fab = L.appl_proj(vf, va, vb)
    # f_α(z) = f_{αβ}(pr_β z) ; et f_{αβ}(pr_β z) = f_{αβ}(f_β(z)) par symétrie de fb
    fb_sym = N.modus_ponens(fb, symetrie(application_canonique_proj_valeur(vE, vf, vb, vz),
                                         E.projection_indice(vz, vb)))   # pr_β z = f_β(z)
    cong2 = N.modus_ponens(fb_sym, congruence_terme(
        E.projection_indice(vz, vb),
        application_canonique_proj_valeur(vE, vf, vb, vz),
        E.valeur(fab, var("w")), "w"))                    # f_{αβ}(pr_β z) = f_{αβ}(f_β(z))
    return composer_egalites(chaine, cong2)               # f_α(z) = f_{αβ}(f_β(z))


# ════════════════════════════════════════════════════════════════════════════
#  PROJECTIF — système projectif d'APPLICATIONS + limite lim← u_α
#  (E.III.7.2, Cor.1 ; Déf. « système projectif d'applications »)
# ════════════════════════════════════════════════════════════════════════════
# @livre Ch.III §7.2 Def.- | E III.54 L.1-3 | PDF p.157
# @livre Ch.R §6 Def.- | E.R.31 item 14 (système projectif d'applications (ua)) | PDF p.334
def est_systeme_projectif_applications(u, f, g, leq, i, a="a", b="b"):
    """« (u_α) est un système projectif d'applications de (E_α,f_{αβ}) dans
    (F_α,g_{αβ}) » := (∀α∀β)((α,β∈I et α≤β) ⇒ u_α∘f_{αβ} = g_{αβ}∘u_β).

    u = donnée des u_α (u_α := app("u_indice",u,α)), f = système source, g = système
    but.  Diagramme commutatif u_α∘f_{αβ}=g_{αβ}∘u_β du Cor.1.  (E.III.7.2, Déf.)"""
    va, vb = var(a), var(b)
    ua = app("u_indice", u, va)
    ub = app("u_indice", u, vb)
    fab = L.appl_proj(f, va, vb)
    gab = L.appl_proj(g, va, vb)
    hyp = et(et(appartient(va, i), appartient(vb, i)), leq(va, vb))
    concl = egal(E.composee(ua, fab), E.composee(gab, ub))
    return pourtout(a, pourtout(b, impl(hyp, concl)))


def u_indice(u, a):
    """u_α : E_α → F_α  (composante d'indice α d'un système projectif d'applications)."""
    return app("u_indice", u, a)


# @livre Ch.III §7.2 Def.- | E III.54 L.3-5 | PDF p.157
# @livre Ch.III §7.2 Rem.2 | E III.56 L.1-4 | PDF p.159
#   (prose, fin de la Remarque 2 commencée E III.55 : quand F s'identifie à lim← F_α,
#    u définie par (6) s'identifie à la limite projective du système (u_α) — « abus
#    de langage u = lim← u_α » ; rien à formaliser de plus)
# @livre Ch.R §6 Def.- | E.R.31 item 14 (limite projective u = lim<- ua) | PDF p.334
def lim_proj_applications(EfamE, fE, EfamF, fF, u):
    """u = lim← u_α : E → F  (limite projective de la famille (u_α), Cor.1 §III.7.2).

    L'unique application u : E=lim←E_α → F=lim←F_α telle que g_α∘u = u_α∘f_α pour
    tout α.  Terme opaque (son existence/unicité = Cor.1, REPORTÉ)."""
    return app("lim_proj_appl", EfamE, fE, EfamF, fF, u)


# ════════════════════════════════════════════════════════════════════════════
#  PROJECTIF — système projectif de PARTIES  (E.III.7.1, formule (8))
# ════════════════════════════════════════════════════════════════════════════
# @livre Ch.III §7.2 Def.- | E III.54 L.20-23 | PDF p.157
def est_systeme_projectif_parties(M, f, leq, i, a="a", b="b"):
    """« (M_α) est un système projectif de parties des E_α » :=
    (∀α∀β)((α,β∈I et α≤β) ⇒ f_{αβ}⟨M_β⟩ ⊂ M_α).

    M = la famille des parties (M_α := M_indice(M,α) = sa valeur en α).  Condition
    de Bourbaki
    « f_{αβ}(M_β) ⊂ M_α » (E.III.7.1) ; on N'EXIGE PAS ici M_α⊂E_α (énoncé par le
    contexte) — la condition caractéristique est l'inclusion des images."""
    va, vb = var(a), var(b)
    Ma, Mb = M_indice(M, va), M_indice(M, vb)
    fab = L.appl_proj(f, va, vb)
    hyp = et(et(appartient(va, i), appartient(vb, i)), leq(va, vb))
    concl = inclus(E.image(fab, Mb), Ma)
    return pourtout(a, pourtout(b, impl(hyp, concl)))


# @livre Ch.III §7.2 Def.- | E III.54 L.20-23 | PDF p.157  (M_α, composante d'une famille de parties — une famille EST une fonction, donc sa composante EST sa valeur)
def M_indice(M, a):
    """M_α : partie de E_α  (composante d'un système projectif/inductif de parties).

    ✅ TRANSPARENT depuis le 5 août 2026.  C'était `app("M_indice", M, α)` — un
    accesseur OPAQUE, sans aucun axiome : rien n'était donc démontrable sur les
    M_α, et la 2ᵉ assertion de la Prop. 2 (« u⁻¹(x') = lim← M_α ») était hors
    d'atteinte par construction, pas par difficulté.

    Or Bourbaki écrit simplement « une famille (M_α)_{α∈I} de parties », et une
    famille EST une fonction (E.II.4.1) : sa composante EST sa valeur.  D'où
    `valeur_famille`, exactement comme pour les E_α.  Une famille de parties
    CONSTRUITE (un `graphe_terme`) a désormais des composantes calculables.

    Même diagnostic et même remède que `restriction_systeme_indices` (cf.
    `prop3_surj/ensembles_restriction_systeme`)."""
    return E.valeur_famille(_t(M), _t(a))


# @livre Ch.III §7.2 Def.- | E III.54 L.24-26 | PDF p.157
def lim_proj_parties(M, f):
    """lim← M_α  (limite projective du système de parties (M_α,g_{αβ})).

    Formule (8) : lim← M_α = (lim← E_α) ∩ ∏_α M_α  — l'identité (8) est REPORTÉE ;
    on introduit ici le terme.  Codé comme la limite projective du système (M_α)."""
    return L.lim_proj(M, f)


# ════════════════════════════════════════════════════════════════════════════
#  PROJECTIF — restriction à une partie J + application canonique g
#  (E.III.7.1, formules (3) et (4))
# ════════════════════════════════════════════════════════════════════════════
# @livre Ch.III §7.2 Rem.3 | E III.56 L.5-20 | PDF p.159
#   (prose, Remarque 3 : pour J partie FINIE de I, F_J = limite du système restreint
#    à J ; (F_J, g_JK) système projectif sur l'ordonné filtrant F(I) des parties
#    finies, et bijection canonique h : E → lim← F_J — exemple non formalisé ; la
#    notion support « restriction de l'ensemble d'indices » est le terme ci-dessous)
def restriction_systeme_indices(Efam, f, J):
    """Système projectif (E_α)_{α∈J} obtenu par restriction de l'ensemble d'indices
    à une partie J ⊂ I.  Même donnée f, indices restreints à J.  (E.III.7.1.)"""
    return app("restr_indices", Efam, f, J)


# @livre Ch.III §7.2 Def.- | E III.52 L.27-32 | PDF p.155
def application_canonique_g(Efam, f, J):
    """g : E → E'  (E=lim←_I, E'=lim←_J), application CANONIQUE de la restriction à J.

    Formule (3) : g(x) = (f_α(x))_{α∈J}.  Terme du graphe de g."""
    return app("g_restr_J", Efam, f, J)


def axiome_canonique_g(Efam, f, leq, i, J, x="x", a="a"):
    """AXIOME définitionnel (E.III.7.1, (3)) : pour x∈E=lim←_I et α∈J,
        pr_α(g(x)) = f_α(x).

    « g(x) = (f_α(x))_{α∈J} » : la α-coordonnée de g(x) est f_α(x).  S8 + A1."""
    va, vx = var(a), var(x)
    g = application_canonique_g(Efam, f, J)
    hyp = et(appartient(vx, L.lim_proj(Efam, f)), appartient(va, J))
    concl = egal(E.projection_indice(E.valeur(g, vx), va),
                 application_canonique_proj_valeur(Efam, f, va, vx))
    return pourtout(a, pourtout(x, impl(hyp, concl)))


def theorie_canonique_g(Efam, f, leq, i, J):
    """Théorie dédiée pour l'axiome de l'application canonique g de restriction à J."""
    return N.Theorie("Canonique-restriction-J", [axiome_canonique_g(Efam, f, leq, i, J)])


# ════════════════════════════════════════════════════════════════════════════
#  INDUCTIF — relation de cohérence R + limite inductive E = G/R
#  (E.III.7.5 : G = somme ∑E_α, R d'équivalence, E = G/R)
# ════════════════════════════════════════════════════════════════════════════
def lambda_indice(x):
    """λ(x) := l'unique α tel que x∈E_α  (E_α identifiés à des parties de G=∑E_α).

    Terme opaque λ(x) (la « projection d'indice » de la somme) — caractérisé par
    le codage de la somme disjointe (x = (x₀, α) ⟹ λ(x)=α) ; laissé opaque ici."""
    return app("lambda_ind", x)


# @livre Ch.III §7.5 Def.- | E III.61 L.9-15 | PDF p.164
# @livre Ch.R §6 Def.- | E.R.30 item 13 (relation d'équivalence de recollement sur la somme) | PDF p.333
def relation_coherence_inductive(f, leq, i, x, y, g="g"):
    """R{x,y} := (∃γ)( γ∈I et γ≥λ(x) et γ≥λ(y) et f_{γ,λ(x)}(x) = f_{γ,λ(y)}(y) ).

    Relation de cohérence sur la somme G=∑E_α (E.III.7.5) : x et y deviennent égaux
    après transport par un même indice γ assez grand.  C'est cette R (équivalence —
    REPORTÉ) qui définit la limite inductive E=G/R.

    f_{γ,λ(x)} = appl_ind(f, γ, λ(x))  (transition E_{λ(x)}→E_γ)."""
    vg = var(g)
    lx, ly = lambda_indice(x), lambda_indice(y)
    f_gx = L.appl_ind(f, vg, lx)
    f_gy = L.appl_ind(f, vg, ly)
    corps = et(et(et(appartient(vg, i), leq(lx, vg)), leq(ly, vg)),
               egal(E.valeur(f_gx, x), E.valeur(f_gy, y)))
    return existe(g, corps)


def coherence_rel(f, leq, i, g="g"):
    """Renvoie R{·,·} (fonction (Terme,Terme)→Formule) pour usage comme relation
    (quotient, classes).  R{x,y} = relation_coherence_inductive(f,leq,i,x,y)."""
    return lambda x, y: relation_coherence_inductive(f, leq, i, x, y, g)


def graphe_coherence(f, i, gleq=None):
    """Graphe de la relation de cohérence R sur G=∑E_α  (terme du graphe ⊂ G×G).

    G_R := { (x,y) | R{x,y} }.  Terme opaque (existence par S8 dans G×G).  Le
    préordre est mémorisé par son GRAPHE `gleq` (Terme) — voir _GRAPHE_LEQ_DEFAUT."""
    if gleq is None:
        gleq = _GRAPHE_LEQ_DEFAUT
    return app("graphe_coherence", f, i, gleq)


# @livre Ch.III §7.5 Def.- | E III.61 L.23-27 | PDF p.164
# @livre Ch.R §6 Def.- | E.R.30 item 13 (limite inductive E = lim-> Ea = somme/R) | PDF p.333
def lim_ind(Efam, f, i, gleq=None):
    """E = lim→_{α∈I} (E_α, f_{βα}) := G/R  (limite inductive, E.III.7.5).

    G = ∑_α E_α (somme de la famille), R = relation de cohérence ; la limite est le
    QUOTIENT de la somme par R.  Codé E.quotient(graphe_coherence, somme_famille)
    — fidèle à « E = G/R ».  Le préordre est mémorisé par son graphe `gleq` (Terme)."""
    if gleq is None:
        gleq = _GRAPHE_LEQ_DEFAUT
    G = E.somme_famille(Efam, i)
    GR = graphe_coherence(f, i, gleq)
    return E.quotient(GR, G)


# @livre Ch.III §7.5 Ex.2 | E III.62 L.1-7 | PDF p.165
#   (prose en petit texte, fin de l'Exemple 2 commencé E III.61 : identification de F
#    à lim→ E_α via G = somme de la famille, bijections h_α : F → G_α, relation R
#    correspondant à la partition (P_y), bijection réciproque — rien à formaliser de
#    plus que la somme G ci-dessous)
def somme_systeme_inductif(Efam, i):
    """G = ∑_{α∈I} E_α  (somme de la famille sous-jacente au système inductif)."""
    return E.somme_famille(Efam, i)


# ── INDUCTIF — application canonique f_α : E_α → E  (E.III.7.5, formule (22)) ──
# @livre Ch.III §7.5 Def.- | E III.61 L.31-34 | PDF p.164
# @livre Ch.R §6 Def.- | E.R.30 item 13 (application canonique fa : Ea -> E) | PDF p.333
def f_canon_ind(Efam, f, i, gleq=None):
    """Graphe de l'application canonique f_α : E_α → E  (E = lim→ E_α = G/R).

    « f_α est la restriction à E_α de l'application canonique f : G → G/R ».  Codé
    comme la restriction de l'application canonique du quotient à la partie E_α.
    Le préordre est mémorisé par son graphe `gleq` (Terme).  ATTENTION : ce graphe
    NE dépend PAS de α (la canonique du quotient est unique) ; α intervient via la
    restriction à E_α, prise dans `application_canonique_ind_valeur`."""
    if gleq is None:
        gleq = _GRAPHE_LEQ_DEFAUT
    G = E.somme_famille(Efam, i)
    GR = graphe_coherence(f, i, gleq)
    return E.application_canonique(GR, G)                 # f : G → G/R, x ↦ Cl_R(x)


def application_canonique_ind_valeur(Efam, f, i, a, x, gleq=None):
    """Terme f_α(x) := Cl_R(x) = valeur(canonique du quotient, x) — pour x∈E_α⊂G.

    f_α est la restriction à E_α de la canonique p:G→G/R ; sa valeur en x∈E_α est
    donc p(x)=Cl_R(x).  (E.III.7.5.)"""
    if gleq is None:
        gleq = _GRAPHE_LEQ_DEFAUT
    return E.valeur(f_canon_ind(Efam, f, i, gleq), x)


def axiome_canonique_ind(Efam, f, i, gleq=None, a="a", x="x"):
    """AXIOME définitionnel (E.III.7.5) : pour α∈I et x∈E_α,
        f_α(x) = Cl_R(x)   (classe de cohérence de x).

    « f_α est la restriction à E_α de la canonique f : G→G/R, x↦Cl_R(x) ».  S8 + A1
    (même statut que AXIOME_RESTRICTION composé avec l'application canonique p)."""
    if gleq is None:
        gleq = _GRAPHE_LEQ_DEFAUT
    va, vx = var(a), var(x)
    GR = graphe_coherence(f, i, gleq)
    hyp = et(appartient(va, i),
             appartient(vx, E.valeur_famille(Efam, va)))
    concl = egal(application_canonique_ind_valeur(Efam, f, i, va, vx, gleq),
                 E.classe(GR, vx))
    return pourtout(a, pourtout(x, impl(hyp, concl)))


def theorie_canonique_ind(Efam, f, i, gleq=None):
    """Théorie dédiée pour l'axiome de la valeur canonique inductive."""
    if gleq is None:
        gleq = _GRAPHE_LEQ_DEFAUT
    return N.Theorie("Canonique-inductive", [axiome_canonique_ind(Efam, f, i, gleq)])


def canonique_ind_valeur(Efam="E", f="f", i="I", gleq=None, a="a", x="x"):
    """{α∈I, x∈E_α} ⊢ f_α(x) = Cl_R(x).   (E.III.7.5, application canonique inductive.)"""
    if gleq is None:
        gleq = _GRAPHE_LEQ_DEFAUT
    vE, vf, vi = _t(Efam), _t(f), _t(i)
    va, vx = var(a), var(x)
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import conjonction_intro
    ax = N.axiome(theorie_canonique_ind(vE, vf, vi, gleq),
                  axiome_canonique_ind(vE, vf, vi, gleq))
    inst = instancie(instancie(ax, va), vx)
    Ha = N.assume(appartient(va, vi))
    Hx = N.assume(appartient(vx, E.valeur_famille(vE, va)))
    return N.modus_ponens(conjonction_intro(Ha, Hx), inst)   # f_α(x)=Cl_R(x)


# ════════════════════════════════════════════════════════════════════════════
#  INDUCTIF — système inductif d'APPLICATIONS + limite lim→ u_α
#  (E.III.7.6, Cor.1)
# ════════════════════════════════════════════════════════════════════════════
# @livre Ch.III §7.6 Def.- | E III.63 L.29-31 | PDF p.166
# @livre Ch.R §6 Def.- | E.R.30 item 13 (système inductif d'applications (ua)) | PDF p.333
def est_systeme_inductif_applications(u, f, g, leq, i, a="a", b="b"):
    """« (u_α) est un système inductif d'applications de (E_α,f_{βα}) dans
    (F_α,g_{βα}) » := (∀α∀β)((α,β∈I et α≤β) ⇒ u_β∘f_{βα} = g_{βα}∘u_α).

    Diagramme commutatif u_β∘f_{βα}=g_{βα}∘u_α du Cor.1.  (E.III.7.6, Déf.)"""
    va, vb = var(a), var(b)
    ua = app("u_indice", u, va)
    ub = app("u_indice", u, vb)
    fba = L.appl_ind(f, vb, va)
    gba = L.appl_ind(g, vb, va)
    hyp = et(et(appartient(va, i), appartient(vb, i)), leq(va, vb))
    concl = egal(E.composee(ub, fba), E.composee(gba, ua))
    return pourtout(a, pourtout(b, impl(hyp, concl)))


# @livre Ch.III §7.6 Def.- | E III.63 L.31-33 | PDF p.166
# @livre Ch.III §7.6 Rem.2 | E III.65 L.22-29 | PDF p.168
#   (prose, Remarque 2 : quand E'_α = E' et i_βα = Id, E' s'identifie à lim→ E_α et u
#    définie par (24) s'identifie à la limite inductive du système (u_α) — « abus de
#    langage u = lim→ u_α » ; rien à formaliser de plus)
# @livre Ch.R §6 Def.- | E.R.30 item 13 (limite inductive u = lim-> ua) | PDF p.333
def lim_ind_applications(EfamE, fE, EfamF, fF, u, i, gleq=None):
    """u = lim→ u_α : E → F  (limite inductive de la famille (u_α), Cor.1 §III.7.6).

    L'unique application u : E=lim→E_α → F=lim→F_α telle que u∘f_α = g_α∘u_α pour
    tout α.  Terme opaque (existence/unicité = Cor.1, REPORTÉ).  Préordre mémorisé
    par son graphe `gleq` (Terme)."""
    if gleq is None:
        gleq = _GRAPHE_LEQ_DEFAUT
    return app("lim_ind_appl", EfamE, fE, EfamF, fF, u, i, gleq)


# ════════════════════════════════════════════════════════════════════════════
#  INDUCTIF — système inductif de PARTIES  (E.III.7.6, Cor. de la Prop. 7)
# ════════════════════════════════════════════════════════════════════════════
# @livre Ch.III §7.6 Def.- | E III.64 L.24-26 | PDF p.167
def est_systeme_inductif_parties(M, f, leq, i, a="a", b="b"):
    """« (M_α) est un système inductif de parties des E_α » :=
    (∀α∀β)((α,β∈I et α≤β) ⇒ f_{βα}⟨M_α⟩ ⊂ M_β).

    Condition de Bourbaki « f_{βα}(M_α) ⊂ M_β »  (E.III.7.6, Cor. de la Prop.7)."""
    va, vb = var(a), var(b)
    Ma, Mb = M_indice(M, va), M_indice(M, vb)
    fba = L.appl_ind(f, vb, va)
    hyp = et(et(appartient(va, i), appartient(vb, i)), leq(va, vb))
    concl = inclus(E.image(fba, Ma), Mb)
    return pourtout(a, pourtout(b, impl(hyp, concl)))


def lim_ind_parties(M, f, i, gleq=None):
    """lim→ M_α  (limite inductive du système de parties (M_α,ḡ_{βα})).

    Identifiée à une partie de E par l'injection lim→ j_α  (E.III.7.6, Cor.) —
    identification REPORTÉE ; on introduit le terme."""
    if gleq is None:
        gleq = _GRAPHE_LEQ_DEFAUT
    return lim_ind(M, f, i, gleq)


# ════════════════════════════════════════════════════════════════════════════
#  THÉORÈMES DIRECTS — décompositions des définitions conjonctives
# ════════════════════════════════════════════════════════════════════════════
def systeme_projectif_applications_commute(u="u", f="f", g="g", leq=None, i="I",
                                           a="a", b="b"):
    """{ (u_α) sys. proj. d'appl. } ⊢ (α,β∈I et α≤β) ⇒ u_α∘f_{αβ}=g_{αβ}∘u_β.

    Lecture de la définition (diagramme commutatif) en un couple (α,β) fixé."""
    if leq is None:
        leq = _gleq()
    vu, vf, vg, vi = _t(u), _t(f), _t(g), _t(i)
    va, vb = var(a), var(b)
    H = N.assume(est_systeme_projectif_applications(vu, vf, vg, leq, vi, a, b))
    return instancie(instancie(H, va), vb)


def systeme_inductif_applications_commute(u="u", f="f", g="g", leq=None, i="I",
                                          a="a", b="b"):
    """{ (u_α) sys. ind. d'appl. } ⊢ (α,β∈I et α≤β) ⇒ u_β∘f_{βα}=g_{βα}∘u_α."""
    if leq is None:
        leq = _gleq()
    vu, vf, vg, vi = _t(u), _t(f), _t(g), _t(i)
    va, vb = var(a), var(b)
    H = N.assume(est_systeme_inductif_applications(vu, vf, vg, leq, vi, a, b))
    return instancie(instancie(H, va), vb)


def systeme_projectif_parties_inclusion(M="M", f="f", leq=None, i="I", a="a", b="b"):
    """{ (M_α) sys. proj. de parties } ⊢ (α,β∈I et α≤β) ⇒ f_{αβ}⟨M_β⟩ ⊂ M_α."""
    if leq is None:
        leq = _gleq()
    vM, vf, vi = _t(M), _t(f), _t(i)
    va, vb = var(a), var(b)
    H = N.assume(est_systeme_projectif_parties(vM, vf, leq, vi, a, b))
    return instancie(instancie(H, va), vb)


def systeme_inductif_parties_inclusion(M="M", f="f", leq=None, i="I", a="a", b="b"):
    """{ (M_α) sys. ind. de parties } ⊢ (α,β∈I et α≤β) ⇒ f_{βα}⟨M_α⟩ ⊂ M_β."""
    if leq is None:
        leq = _gleq()
    vM, vf, vi = _t(M), _t(f), _t(i)
    va, vb = var(a), var(b)
    H = N.assume(est_systeme_inductif_parties(vM, vf, leq, vi, a, b))
    return instancie(instancie(H, va), vb)


# Liste des résultats durs INTRODUITS mais NON prouvés (honnêteté).
REPORTES = [
    "Proposition 1 (propriété universelle de lim←) — cônes universels absents.",
    "Corollaire 1/2 Prop.1 (existence/composition de lim← u_α) — REPORTÉ.",
    "Proposition 2 + Cor. (u^{-1}(x')=lim← des u_α^{-1}, injective/bijective) — REPORTÉ.",
    "Proposition 3 (partie cofinale : g bijective) — REPORTÉ.",
    "Proposition 4 + Cor. (doubles limites projectives) — REPORTÉ.",
    "Proposition 5, Théorème 1 (surjectivité, b) non-vacuité) — REPORTÉ.",
    "Lemme 1, Proposition 6 (propriété universelle de lim→) — REPORTÉ.",
    "Proposition 7 + Cor. (lim→ injective/surjective, parties) — REPORTÉ.",
    "Proposition 8/9/10 + Cor. (cofinal, doubles, produit lim→) — REPORTÉ.",
    "R relation d'équivalence sur G (réflexive/sym./trans. — filtrant requis) — REPORTÉ.",
]


__all__ = [
    # projectif : application canonique
    "f_canon_proj", "application_canonique_proj_valeur",
    "axiome_canonique_proj", "theorie_canonique_proj",
    "canonique_proj_valeur", "relation_2_projective",
    # projectif : systèmes d'applications / parties / restriction
    "est_systeme_projectif_applications", "u_indice", "lim_proj_applications",
    "est_systeme_projectif_parties", "M_indice", "lim_proj_parties",
    "restriction_systeme_indices", "application_canonique_g",
    "axiome_canonique_g", "theorie_canonique_g",
    # inductif : relation de cohérence + limite = quotient
    "lambda_indice", "relation_coherence_inductive", "coherence_rel",
    "graphe_coherence", "lim_ind", "somme_systeme_inductif",
    # inductif : application canonique
    "f_canon_ind", "application_canonique_ind_valeur",
    "axiome_canonique_ind", "theorie_canonique_ind", "canonique_ind_valeur",
    # inductif : systèmes d'applications / parties
    "est_systeme_inductif_applications", "lim_ind_applications",
    "est_systeme_inductif_parties", "lim_ind_parties",
    # théorèmes directs (décompositions)
    "systeme_projectif_applications_commute", "systeme_inductif_applications_commute",
    "systeme_projectif_parties_inclusion", "systeme_inductif_parties_inclusion",
    "REPORTES",
]
