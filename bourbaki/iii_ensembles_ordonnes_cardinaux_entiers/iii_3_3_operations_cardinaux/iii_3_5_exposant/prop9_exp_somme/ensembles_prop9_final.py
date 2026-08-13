"""§III.3.5 — PROPOSITION 9 (forme exponentielle), ASSEMBLAGE FINAL de la BIJECTION
Φ : 𝓕(B⊔C; A) → 𝓕(B;A) × 𝓕(C;A),   f ↦ (f|B , f|C)   [a^(b+c) = a^b · a^c].

ÉNONCÉ visé (forme cardinale binaire du projet) :

        ⊢ Card(𝓕(B⊔C; A)) = Card(𝓕(B;A) × 𝓕(C;A))

(= `cible_prop9_exp_somme`).  Ce module ASSEMBLE la bijection Φ comme un GRAPHE
W (exactement le schéma graphe-terme de la Proposition 12, `chi_bijection`), et
ferme tout ce qui est atteignable sans le pont membership×valeur reporté :

  Φ(f) := ( (f|B, B), A ),  ( (f|C, C), A )         (couple de DEUX applications)
  W    := graphe_terme( 𝓕(B⊔C;A) , Φ(f) , « f » )   (graphe de Φ)

où f|B = restriction_gauche(f, B) et f|C = restriction_droite(f, C) sont les
graphes des restrictions u↦f((u,0)), v↦f((v,1)) déjà certifiés (round 25/26,
`ensembles_prop9_exp_somme`).  Φ(f) est donc le COUPLE des deux applications-triples
((f|B,B),A) ∈ 𝓕(B;A) et ((f|C,C),A) ∈ 𝓕(C;A), exactement l'image de Φ.

═══════════════════════════════════════════════════════════════════════════════
ÉTAT (SALVAGE, paliers sûrs livrés au fur et à mesure) :

PALIER W (CLOS) — LE GRAPHE DE Φ ET SES CONJOINTS STRUCTURELS :
  • phi_valeur(f,A,B,C)          : Φ(f) = ((f|B,B),A),((f|C,C),A)  (terme) ;
  • W(A,B,C)                     : W = graphe_terme(𝓕(B⊔C;A), Φ(f), « f »)  (terme) ;
  • W_fonctionnel               ⊢ est_fonctionnel(W)        [C54, automatique] ;
  • W_domaine                   ⊢ dom W = 𝓕(B⊔C;A)          [C54, automatique] ;
  • W_valeur                    {f∈𝓕(B⊔C;A)} ⊢ W(f) = Φ(f) [C54].

PALIER INJ½ (CLOS) — INJECTIVITÉ, demi-extraction (le contenu vraiment dérivable) :
  • W_injective_restrictions_coincident
        {f₁,f₂∈𝓕(B⊔C;A), W(f₁)=W(f₂)} ⊢ (f₁|B = f₂|B  et  f₁|C = f₂|C).
    Deux fonctions de même image par Φ ont les MÊMES restrictions (graphes des
    restrictions gauche/droite égaux), par décomposition de couples (Bourbaki
    E.II.30) ; c'est le cœur de l'injectivité de Φ.

PALIER FIN (CLOS, CONDITIONNEL) — DERNIER MILE Φ bijection ⟹ égalité-cible :
  • card_eq_si_bijection
        {est_bijection_de(W, 𝓕(B⊔C;A), 𝓕(B;A)×𝓕(C;A))}
        ⊢ Card(𝓕(B⊔C;A)) = Card(𝓕(B;A) × 𝓕(C;A))   (= cible_prop9_exp_somme).
    Dès que W est une bijection, le témoin de Eq + Proposition 1 (sens direct,
    `_prop1_direct_t`) donnent l'égalité.  Il ne reste qu'à fermer les deux
    conjoints DURS de est_bijection_de(W,…) ci-dessous.

CŒUR REPORTÉ (les deux conjoints DURS de la bijection) : voir
`bijection_phi_conjoints_durs_REPORTE` — bien-définition (Φ(f) ∈ produit),
injectivité COMPLÈTE (f₁=f₂ depuis restrictions égales) et surjectivité
(recollement réindexé), tous trois bloqués sur le MÊME pont membership×valeur le
long des injections ι_B,ι_C (transporter « f((u,0))∈A » et identifier
recollement|B = g) — exactement le verrou hérité de R24/R25/R26.
═══════════════════════════════════════════════════════════════════════════════
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import Terme, var, egal, et
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    instancie)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
    symetrie, composer_egalites)
from bourbaki.ii_theorie_des_ensembles.ii_2_couples.ii_2_1_definition_couples.ensembles_couples import (
    couple_egal_implique_composantes)
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_6_fonction_terme.ensembles_fonction_terme import (
    graphe_terme_fonctionnel)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.cantor.ensembles_cantor import (
    graphe_terme_domaine, graphe_terme_valeur)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    cardinal, equipotent, est_bijection_de)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_produit.ensembles_arith_cardinale import _prop1_direct_t
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_recollement_somme.ensembles_somme_disjointe import somme_disjointe
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_5_exposant.prop9_exp_somme.ensembles_prop9_exp_somme import (
    cible_prop9_exp_somme, restriction_gauche, restriction_droite)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# Le point courant du graphe W = « f » (l'application à restreindre).  Il doit
# éviter les liants INTERNES de la machinerie graphe-terme (x, y) et ceux des
# restrictions (e = point du graphe-terme interne des restrictions, c = liant τ
# de la valeur f((·,0))).  « f » est libre de toute collision.
_POINT = "f"


# ═══════════════════════════════════════════════════════════════════════════════
# PALIER W — Φ(f), le graphe W de Φ, et ses conjoints STRUCTURELS (C54)
# ═══════════════════════════════════════════════════════════════════════════════
def phi_valeur(f, a="A", b="B", c="C"):
    """Φ(f) := ( ((f|B, B), A) , ((f|C, C), A) )   (terme) — l'image de f par Φ.

    Le COUPLE des deux applications-triples : la restriction gauche ((f|B,B),A) ∈
    𝓕(B;A) et la restriction droite ((f|C,C),A) ∈ 𝓕(C;A).  C'est exactement
    Φ(f) = (f|B, f|C) au codage application-triple du projet."""
    vf, va, vb, vc = _t(f), _t(a), _t(b), _t(c)
    triple_g = E.couple(E.couple(restriction_gauche(vf, vb), vb), va)   # ((f|B,B),A)
    triple_d = E.couple(E.couple(restriction_droite(vf, vc), vc), va)   # ((f|C,C),A)
    return E.couple(triple_g, triple_d)


def domaine_phi(a="A", b="B", c="C"):
    """𝓕(B⊔C; A)   (domaine de Φ, source de la bijection)."""
    va, vb, vc = _t(a), _t(b), _t(c)
    return E.applications(somme_disjointe(vb, vc), va)


def codomaine_phi(a="A", b="B", c="C"):
    """𝓕(B;A) × 𝓕(C;A)   (codomaine de Φ, but de la bijection)."""
    va, vb, vc = _t(a), _t(b), _t(c)
    return E.produit(E.applications(vb, va), E.applications(vc, va))


def W(a="A", b="B", c="C"):
    """W := graphe_terme( 𝓕(B⊔C;A) , Φ(f) , « f » )   (le GRAPHE de Φ, terme).

    Schéma graphe-terme identique à la Proposition 12 (`chi_bijection._W`) : le
    graphe de l'application f ↦ Φ(f) sur tout 𝓕(B⊔C;A).  Point courant « f »."""
    va, vb, vc = _t(a), _t(b), _t(c)
    return E.graphe_terme(domaine_phi(va, vb, vc), phi_valeur(var(_POINT), va, vb, vc), _POINT)


# ── CONJOINT 1 — W fonctionnel  (automatique, C54) ────────────────────────────
def W_fonctionnel(a="A", b="B", c="C"):
    """⊢ est_fonctionnel(W).   (Φ associe à chaque f UNE image Φ(f) ; cas C54.)"""
    va, vb, vc = _t(a), _t(b), _t(c)
    return graphe_terme_fonctionnel(domaine_phi(va, vb, vc),
                                    phi_valeur(var(_POINT), va, vb, vc), _POINT, "y")


# ── CONJOINT 2 — dom W = 𝓕(B⊔C;A)  (automatique, C54) ─────────────────────────
def W_domaine(a="A", b="B", c="C"):
    """⊢ dom(W) = 𝓕(B⊔C; A).   (Φ est définie sur TOUT l'espace 𝓕(B⊔C;A).)"""
    va, vb, vc = _t(a), _t(b), _t(c)
    return graphe_terme_domaine(domaine_phi(va, vb, vc),
                                phi_valeur(var(_POINT), va, vb, vc), _POINT, "y", "z")


def W_valeur(f="g", a="A", b="B", c="C"):
    """{f ∈ 𝓕(B⊔C; A)} ⊢ W(f) = Φ(f).   (la valeur de Φ en f.)

    ⚠ le point d'évaluation f doit être un NOM (string) ≠ liant « f » de W et
    ≠ liants internes {x,y} de la machinerie graphe-terme (sinon capture).  Le
    DÉFAUT est « g » (≠ f, x, y, et ≠ e,c des restrictions)."""
    if not isinstance(f, str):
        raise ValueError("W_valeur : le point d'évaluation doit être un NOM (string)")
    va, vb, vc = _t(a), _t(b), _t(c)
    return graphe_terme_valeur(domaine_phi(va, vb, vc),
                               phi_valeur(var(_POINT), va, vb, vc), f, _POINT, "y")


# ═══════════════════════════════════════════════════════════════════════════════
# PALIER INJ½ — injectivité de Φ, demi-extraction : mêmes restrictions.
# ═══════════════════════════════════════════════════════════════════════════════
def W_injective_restrictions_coincident(a="A", b="B", c="C", f1="f1", f2="f2"):
    """{f₁∈𝓕(B⊔C;A), f₂∈𝓕(B⊔C;A), W(f₁)=W(f₂)}
        ⊢ ( (f₁|B = f₂|B)  et  (f₁|C = f₂|C) ).

    CŒUR DE L'INJECTIVITÉ de Φ.  W(fᵢ)=Φ(fᵢ)=(((fᵢ|B,B),A),((fᵢ|C,C),A))
    (W_valeur) ; de W(f₁)=W(f₂) on tire Φ(f₁)=Φ(f₂), puis par décomposition de
    couples (couple_egal_implique_composantes, E.II.30, appliqué trois fois à
    chaque côté : couple externe, triple, paire interne) on extrait f₁|B=f₂|B et
    f₁|C=f₂|C — les deux restrictions COÏNCIDENT.

    (Le dernier pas f₁=f₂ exige l'extensionnalité fonctionnelle sur B⊔C, qui
    reconstruit f à partir de ses restrictions ; bloqué sur le pont reporté.)"""
    if not (isinstance(f1, str) and isinstance(f2, str)):
        raise ValueError("W_injective… : f1, f2 doivent être des NOMS (strings)")
    va, vb, vc = _t(a), _t(b), _t(c)
    vf1, vf2 = var(f1), var(f2)
    Wt = W(va, vb, vc)
    dom = domaine_phi(va, vb, vc)
    phi1, phi2 = phi_valeur(vf1, va, vb, vc), phi_valeur(vf2, va, vb, vc)

    # W(f₁)=Φ(f₁) et W(f₂)=Φ(f₂)   (W_valeur déchargée par fᵢ∈dom)
    h1 = N.assume(E.appartient(vf1, dom))
    h2 = N.assume(E.appartient(vf2, dom))
    Wf1 = N.modus_ponens(h1, N.loi_deduction(E.appartient(vf1, dom),
                                             W_valeur(f1, va, vb, vc)))   # W(f₁)=Φ(f₁)
    Wf2 = N.modus_ponens(h2, N.loi_deduction(E.appartient(vf2, dom),
                                             W_valeur(f2, va, vb, vc)))   # W(f₂)=Φ(f₂)
    # Φ(f₁) = W(f₁) = W(f₂) = Φ(f₂)
    heq = N.assume(egal(E.valeur(Wt, vf1), E.valeur(Wt, vf2)))             # W(f₁)=W(f₂)
    phi1_eq_phi2 = composer_egalites(composer_egalites(
        N.modus_ponens(Wf1, symetrie(E.valeur(Wt, vf1), phi1)), heq), Wf2)  # Φ(f₁)=Φ(f₂)

    # décomposition du couple EXTERNE : (TG₁,TD₁)=(TG₂,TD₂) ⇒ (TG₁=TG₂ et TD₁=TD₂)
    TG1 = E.couple(E.couple(restriction_gauche(vf1, vb), vb), va)          # ((f₁|B,B),A)
    TD1 = E.couple(E.couple(restriction_droite(vf1, vc), vc), va)          # ((f₁|C,C),A)
    TG2 = E.couple(E.couple(restriction_gauche(vf2, vb), vb), va)
    TD2 = E.couple(E.couple(restriction_droite(vf2, vc), vc), va)
    comp_ext = N.modus_ponens(phi1_eq_phi2,
                              couple_egal_implique_composantes(TG1, TD1, TG2, TD2))
    TG_eq = conjonction_elim_gauche(comp_ext)        # ((f₁|B,B),A)=((f₂|B,B),A)
    TD_eq = conjonction_elim_droite(comp_ext)        # ((f₁|C,C),A)=((f₂|C,C),A)

    rg_eq = _strip_triple(TG_eq, restriction_gauche(vf1, vb), vb, va,
                          restriction_gauche(vf2, vb))   # f₁|B = f₂|B
    rd_eq = _strip_triple(TD_eq, restriction_droite(vf1, vc), vc, va,
                          restriction_droite(vf2, vc))   # f₁|C = f₂|C
    return conjonction_intro(rg_eq, rd_eq)


def _strip_triple(triple_eq, g1, mid1, top, g2):
    """De ⊢ ((g₁,mid),top) = ((g₂,mid),top), tire ⊢ g₁ = g₂.

    Deux décompositions de couples : ((g,mid),top) → (g,mid) → g.  (mid et top
    sont communs aux deux côtés ; seul g varie.)"""
    inner1 = E.couple(g1, mid1)          # (g₁,mid)
    inner2 = E.couple(g2, mid1)          # (g₂,mid)
    # ((g₁,mid),top)=((g₂,mid),top) ⇒ (g₁,mid)=(g₂,mid)
    comp1 = N.modus_ponens(triple_eq,
                           couple_egal_implique_composantes(inner1, top, inner2, top))
    inner_eq = conjonction_elim_gauche(comp1)        # (g₁,mid)=(g₂,mid)
    # (g₁,mid)=(g₂,mid) ⇒ g₁=g₂
    comp2 = N.modus_ponens(inner_eq,
                           couple_egal_implique_composantes(g1, mid1, g2, mid1))
    return conjonction_elim_gauche(comp2)            # g₁=g₂


# ═══════════════════════════════════════════════════════════════════════════════
# PALIER FIN — Φ bijection ⟹ égalité-cible (le DERNIER MILE, CONDITIONNEL)
# ═══════════════════════════════════════════════════════════════════════════════
def equipotent_si_bijection(a="A", b="B", c="C"):
    """{est_bijection_de(W, 𝓕(B⊔C;A), 𝓕(B;A)×𝓕(C;A))} ⊢ Eq(𝓕(B⊔C;A), 𝓕(B;A)×𝓕(C;A)).

    Dès que W (le graphe de Φ) est une bijection 𝓕(B⊔C;A) → 𝓕(B;A)×𝓕(C;A),
    l'équipotence Eq(·,·) = (∃F)(bijection_de(F,·,·)) est attestée par le témoin
    F := W (S5)."""
    va, vb, vc = _t(a), _t(b), _t(c)
    Wt = W(va, vb, vc)
    dom = domaine_phi(va, vb, vc)
    cod = codomaine_phi(va, vb, vc)
    bij = N.assume(est_bijection_de(Wt, dom, cod))
    corps = est_bijection_de(var("F"), dom, cod)     # corps de Eq avec liant F
    return N.modus_ponens(bij, N.s5(corps, Wt, "F"))  # (∃F)bijection_de(F,dom,cod) = Eq(dom,cod)


# (dernier mile conditionnel du Cor.1 : Phi bijection => a^(b+c) = a^b·a^c.)
# @livre Ch.III §3.5 Demo.- | E III.28 L.31-33 | PDF p.131
def card_eq_si_bijection(a="A", b="B", c="C"):
    """{est_bijection_de(W, 𝓕(B⊔C;A), 𝓕(B;A)×𝓕(C;A))}
        ⊢ Card(𝓕(B⊔C;A)) = Card(𝓕(B;A) × 𝓕(C;A)).        (= cible_prop9_exp_somme.)

    LE DERNIER MILE de la Proposition 9, CONDITIONNEL à la bijectivité de W.
    Eq(𝓕(B⊔C;A), 𝓕(B;A)×𝓕(C;A)) (equipotent_si_bijection) ⇒ égalité des cardinaux
    (Proposition 1, sens direct, `_prop1_direct_t`).  La conclusion est
    LITTÉRALEMENT `cible_prop9_exp_somme(A,B,C)` (a^(b+c) = a^b · a^c).

    Il ne reste, pour CLORE inconditionnellement la Proposition 9, qu'à fournir
    est_bijection_de(W,…) — c.-à-d. les deux conjoints DURS reportés
    (`bijection_phi_conjoints_durs_REPORTE`)."""
    va, vb, vc = _t(a), _t(b), _t(c)
    dom = domaine_phi(va, vb, vc)
    cod = codomaine_phi(va, vb, vc)
    eq = equipotent_si_bijection(va, vb, vc)         # {bij W} ⊢ Eq(dom, cod)
    prop1 = _prop1_direct_t(dom, cod)                # Eq(dom,cod) ⇒ Card dom = Card cod
    return N.modus_ponens(eq, prop1)                 # {bij W} ⊢ Card(dom)=Card(cod)


# ═══════════════════════════════════════════════════════════════════════════════
# CŒUR REPORTÉ — les deux conjoints DURS de est_bijection_de(W, …)
# ═══════════════════════════════════════════════════════════════════════════════
def bijection_phi_conjoints_durs_REPORTE():
    """REPORTÉ (non clos) — les deux conjoints DURS de est_bijection_de(W, …).

    Ce module ferme : le GRAPHE W de Φ + ses conjoints structurels (W fonctionnel,
    dom W = 𝓕(B⊔C;A), W(f)=Φ(f)), la demi-injectivité (mêmes restrictions), et le
    DERNIER MILE conditionnel (W bijection ⟹ égalité-cible, card_eq_si_bijection).

    Restent REPORTÉS (verrou identique R24/R25/R26 — pont membership×valeur le long
    des injections ι_B:u↦(u,0), ι_C:v↦(v,1)) :
      (i)   BIEN-DÉFINITION  Φ(f) ∈ 𝓕(B;A)×𝓕(C;A)  pour f∈𝓕(B⊔C;A) : il faut
            ((f|B,B),A) ∈ 𝓕(B;A), c.-à-d. f|B ∈ A^B, donc la valeur f((u,0))∈A
            pour u∈B — transport de « f∈𝓕(B⊔C;A) ⇒ f((u,0))∈A car (u,0)∈B⊔C » à
            travers ι_B ;  (entre dans image(W,·) ⊂ 𝓕(B;A)×𝓕(C;A)) ;
      (ii)  INJECTIVITÉ COMPLÈTE : de f₁|B=f₂|B et f₁|C=f₂|C
            (W_injective_restrictions_coincident, CLOS) à f₁=f₂, par
            EXTENSIONNALITÉ fonctionnelle (graphe_egal_par_valeurs) sur B⊔C — tout
            antécédent est une copie (u,0) ou (v,1), et la valeur coïncide via la
            restriction correspondante (cas-analyse sur la somme disjointe) ;
      (iii) SURJECTIVITÉ  image(W,𝓕(B⊔C;A)) ⊃ 𝓕(B;A)×𝓕(C;A) : depuis (g,h)
            arbitraire, le recollement réindexé ψ(g,h) (recollement_fonctionnel,
            CLOS dans ensembles_prop9_exp_somme) vérifie Φ(ψ(g,h))=(g,h) — même
            verrou d'extensionnalité fonctionnelle réindexée que (ii).

    Une fois ces conjoints fermés, est_bijection_de(W,…) alimente
    `card_eq_si_bijection` et CLÔT inconditionnellement la Proposition 9."""
    raise NotImplementedError(
        "Conjoints DURS de est_bijection_de(W,…) reportés : bien-définition Φ(f)∈"
        "produit (i), injectivité complète f₁=f₂ depuis restrictions égales (ii), "
        "surjectivité via recollement réindexé (iii) — tous bloqués sur le pont "
        "membership×valeur le long des injections ι_B,ι_C.  Ce module livre le "
        "graphe W de Φ, W fonctionnel + dom W = 𝓕(B⊔C;A) + W(f)=Φ(f), la "
        "demi-injectivité (mêmes restrictions) et le dernier mile conditionnel "
        "card_eq_si_bijection.")


__all__ = [
    "phi_valeur", "domaine_phi", "codomaine_phi", "W",
    "W_fonctionnel", "W_domaine", "W_valeur",
    "W_injective_restrictions_coincident",
    "equipotent_si_bijection", "card_eq_si_bijection",
    "bijection_phi_conjoints_durs_REPORTE",
]
