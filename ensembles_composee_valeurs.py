"""§II.3.8 Théorème 1 / identités de composition au niveau des VALEURS.

S'appuie sur le verrou « valeur d'une composée » composition_valeur :
    ⊢ (g∘f)(x) = g(f(x))   sous {F,G fonctionnels, x∈dom F, f(x)∈dom G}.

On en déduit ici les identités de composition au niveau des valeurs qui étaient
reportées au round 1 :

  • `composition_valeur_t` : version « TERMES » de composition_valeur — accepte des
        termes composés (p.ex. H∘G) comme facteurs. Conclusion ⊢ (tG∘tF)(x)=tG(tF(x))
        avec, en hypothèses, « tG∘tF fonctionnel » et l'existence des correspondants
        (les conditions C46) — sans recourir à la Proposition 6 (qui n'est énoncée
        que pour des graphes-fonctions « lettres »).

  • `associativite_valeur` : ⊢ ((h∘g)∘f)(x) = (h∘(g∘f))(x)
        (les deux membres valent h(g(f(x)))) — contenu « valeurs » de
        l'associativité de la composition (préalable au Théorème 1 a/b).

Les compositions r∘r' / s∘s' du Théorème 1 a-f, et Prop. 9, restent reportées
(cf. rapport) : elles exigent en plus le pont surjectivité↔image.
"""
from __future__ import annotations

from formule import Terme, var, egal, existe, appartient
import noyau_abrege as N
import ensembles_abrege as E
from tactiques_abrege2 import instancie, equivalence_avant
from tactiques_abrege_egalite import composer_egalites, congruence_terme, symetrie
from ensembles_fonctions import valeur_dans_graphe, valeur_caracterisation
from ensembles_fonctions_composee import composee_intro


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def _symetrie_thm(thm_eq):
    """De Γ⊢(T=U) déduire Γ⊢(U=T)."""
    t, u = thm_eq.conclusion.termes
    return N.modus_ponens(thm_eq, symetrie(t, u))


def composition_valeur_t(tG, tF, tx):
    """⊢ (tG∘tF)(x) = tG(tF(x))   (version TERMES de composition_valeur).

    tG, tF, tx : termes (ou noms). Hypothèses laissées dans le séquent :
      tF fonctionnel-au-point (∃y)(x,y)∈tF, (∃y)(f(x),y)∈tG, et tG∘tF fonctionnel.
    On n'invoque PAS la Proposition 6 (réservée aux fonctions-lettres) : la
    fonctionnalité de la composée reste une hypothèse explicite."""
    vG, vF, vx, vy = _t(tG), _t(tF), _t(tx), var("y")
    comp = E.composee(vG, vF)
    fx = E.valeur(vF, vx)
    gfx = E.valeur(vG, fx)                              # g(f(x))
    gof = E.valeur(comp, vx)                            # (g∘f)(x)
    in_comp = composee_intro(vG, vF, vx, gfx, fx,       # (x, g(f(x))) ∈ G∘F  [hyps domaines]
                             valeur_dans_graphe(vF, vx), valeur_dans_graphe(vG, fx))
    vc = valeur_caracterisation(comp, vx)              # ((x,y)∈comp ⇔ y=(g∘f)(x)) [hyps comp func/dom]
    vc_gfx = instancie(N.generalisation("y", vc), gfx)
    eq = N.modus_ponens(in_comp, equivalence_avant(vc_gfx))   # g(f(x)) = (g∘f)(x)
    # cut de l'hypothèse de domaine « (∃y)(x,y)∈comp » (dérivée de in_comp)
    comp_dom = N.modus_ponens(in_comp, N.s5(appartient(E.couple(vx, vy), comp), gfx, "y"))
    eq1 = N.modus_ponens(comp_dom, N.loi_deduction(
        existe("y", appartient(E.couple(vx, vy), comp)), eq))
    return N.modus_ponens(eq1, symetrie(gfx, gof))      # (g∘f)(x) = g(f(x))


def composee_associee_droite_valeur(h="H", g="G", f="F", x="x"):
    """⊢ (h∘(g∘f))(x) = h(g(f(x))).   (réduction « à droite » au niveau des valeurs.)

    Point x simple (sans nesting) : composition_valeur_t deux fois + congruence
    sous h(·). Sert de demi-associativité ; l'identité complète
    ((h∘g)∘f)(x)=(h∘(g∘f))(x) est REPORTÉE (cf. rapport) car le membre gauche
    exige composition_valeur en un point qui est lui-même une valeur τy(...),
    ce qui déclenche la capture du liant « y » dans valeur_caracterisation."""
    vH, vG, vF, vx = var(h), var(g), var(f), var(x)
    GF = E.composee(vG, vF)
    fx = E.valeur(vF, vx)
    Gfx = E.valeur(vG, fx)                               # g(f(x))
    R1 = composition_valeur_t(vH, GF, vx)               # (h∘(g∘f))(x) = h((g∘f)(x))
    R2 = composition_valeur_t(vG, vF, vx)               # (g∘f)(x) = g(f(x))
    cong = N.modus_ponens(R2, congruence_terme(         # h((g∘f)(x)) = h(g(f(x)))
        E.valeur(GF, vx), Gfx, E.valeur(vH, var("w")), "w"))
    return composer_egalites(R1, cong)                  # (h∘(g∘f))(x) = h(g(f(x)))


def retraction_compose_valeur(r="R", f="F", a="A", x="x"):
    """{est_retraction(R,F,A), F func, R func, x∈domF, f(x)∈domR} ⊢ (x∈A) ⇒ ((r∘f)(x) = x).

    Relie la définition matricielle r∘f = Id_A (E.II.48, Déf. 11 : (∀x∈A) r(f(x))=x)
    au niveau « composée » : (r∘f)(x) = r(f(x)) (composition_valeur) puis r(f(x))=x
    (instance de est_retraction). Donc (r∘f)(x)=x sur A — l'identité d'application
    Id_A lue sur les valeurs."""
    vR, vF, vA, vx = var(r), var(f), var(a), var(x)
    comp = E.composee(vR, vF)
    fx = E.valeur(vF, vx)
    rfx = E.valeur(vR, fx)                               # r(f(x))
    rof = E.valeur(comp, vx)                             # (r∘f)(x)
    # (r∘f)(x) = r(f(x))   (composition_valeur ; hyps fonctionnels/domaines)
    cv = composition_valeur_t(vR, vF, vx)               # (r∘f)(x) = r(f(x))
    # r(f(x)) = x   à partir de est_retraction(R,F,A) sous x∈A
    hret = N.assume(E.est_retraction(vR, vF, vA))       # (∀x)(x∈A ⇒ r(f(x))=x)
    inst = instancie(hret, vx)                          # x∈A ⇒ r(f(x))=x
    hxa = N.assume(appartient(vx, vA))
    eq_rfx_x = N.modus_ponens(hxa, inst)                # {ret, x∈A} ⊢ r(f(x))=x
    chained = composer_egalites(cv, eq_rfx_x)           # (r∘f)(x) = x
    return N.loi_deduction(appartient(vx, vA), chained)  # (x∈A) ⇒ (r∘f)(x)=x


__all__ = ["composition_valeur_t", "composee_associee_droite_valeur",
           "retraction_compose_valeur"]
