"""§II.3 — Notions fondamentales « correspondance / fonction / application / Id »
(INTRODUCTION fidèle des prédicats encore manquants).

AUDIT (cf. fichier de mission) : presque toutes les notions fondamentales de
Bourbaki chap. I–II.3.4 sont DÉJÀ présentes (logique : ∀/∃/τ/=/¬/∨/⇒/⇔/Coll dans
`logique/formule.py` + `noyau_abrege.py` ; ensembles : ∈, ⊂, ∅, paire, singleton,
couple, produit ×, parties P, réunion/intersection/différence, correspondance via
graphe (dom, img, image, réciproque, composée), graphe fonctionnel `est_fonctionnel`,
valeur f(x), injection/surjection/bijection, Id via Δ_X, restriction…).

Ce module N'AJOUTE AUCUN axiome et ne touche à AUCUN fichier existant ; il INTRODUIT
seulement, sous forme de PRÉDICATS / TERMES réutilisables, les quatre énoncés de
Bourbaki qui n'étaient présents qu'IMPLICITEMENT (à l'intérieur de
`axiome_exposant` / `axiome_applications` / `diagonale`) :

  • est_une_correspondance(Γ, A, B)  (E.II.3.1, Déf. 1) : Γ = (G, A, B) avec G⊂A×B.
  • est_un_graphe_fonctionnel(G)      (E.II.3.4, Déf. 9) : synonyme exposé de
        `est_fonctionnel` (au plus une valeur par antécédent).
  • est_une_fonction(F)               (E.II.3.4, Déf. 9) : F est un graphe fonctionnel
        (« on dit que F est une fonction si F est un graphe fonctionnel »).
  • est_application(F, A, B)          (E.II.3.4 + E.II.5.2) : F (vu comme graphe) est
        un graphe fonctionnel, de domaine exactement A, et inclus dans A×B
        (l'image tombe dans B) — la « application de A dans B ».
  • application_identique(A)          (E.II.3.4, identité Id_A : x ↦ x sur A) : la
        fonction-terme x↦x (mécanisme C54 `fonction_terme`), dont le graphe est la
        diagonale Δ_A (E.III.3.1, déjà présent).

theorie_ensembles() RESTE à 22 axiomes (rien n'est écrit dedans).
"""
from __future__ import annotations

from bourbaki.logique.formule import Terme, var, egal, et, impl, appartient, pourtout
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E


def _t(v):
    """Coercion nom→terme : accepte un Terme ou un nom de variable."""
    return v if isinstance(v, Terme) else var(v)


# ── §II.3.1, Déf. 1 — Correspondance Γ = (G, A, B) ────────────────────────────
def est_une_correspondance(g, a, b):
    """« (G, A, B) est une correspondance de A dans B » := G ⊂ A×B   (E.II.3.1, Déf. 1).

    Une correspondance est le triple (graphe, ensemble de départ, ensemble d'arrivée)
    où le graphe G est une partie du produit A×B (Bourbaki, E.II.3.1).  On expose ici
    la condition portant sur le graphe ; le triple lui-même est (G, A, B) (couple
    itéré, cf. `correspondance` ci-dessous)."""
    return E.inclus(_t(g), E.produit(_t(a), _t(b)))


def correspondance(g, a, b):
    """Γ := (G, A, B) = ((G, A), B)  (le triple « correspondance », E.II.3.1)."""
    return E.couple(E.couple(_t(g), _t(a)), _t(b))


# ── §II.3.4, Déf. 9 — Graphe fonctionnel / fonction ───────────────────────────
def est_un_graphe_fonctionnel(g):
    """« G est un graphe fonctionnel » := (∀u)(∀v)(∀z)(((u,v)∈G et (u,z)∈G) ⇒ v=z)
    (E.II.3.4, Déf. 9 ; au plus une valeur par antécédent).

    Synonyme EXPOSÉ de `est_fonctionnel` (déjà présent) ; introduit sous le nom de
    Bourbaki pour la lisibilité des énoncés « G graphe fonctionnel »."""
    return E.est_fonctionnel(_t(g))


def est_une_fonction(f):
    """« F est une fonction » := F est un graphe fonctionnel   (E.II.3.4, Déf. 9).

    Bourbaki : « on dit que F est une fonction si F est un graphe fonctionnel ».
    Une fonction est donc identifiée à son graphe fonctionnel (sans donnée de but)."""
    return est_un_graphe_fonctionnel(_t(f))


# ── §II.3.4 + §II.5.2 — Application de A dans B ───────────────────────────────
def est_application(f, a, b):
    """« F est (le graphe d')une application de A dans B » :=
        F graphe fonctionnel  ET  dom F = A  ET  F ⊂ A×B          (E.II.3.4 / E.II.5.2).

    L'application est totale (domaine exactement A) et son image tombe dans B
    (F ⊂ A×B).  C'est la condition « G ∈ F^E » dépliée (cf. axiome_exposant : G⊂E×F,
    G fonctionnel, dom G = E) exposée ici comme prédicat réutilisable sur le graphe.
    L'objet « application » (triple) est `correspondance(F, A, B)`."""
    vF, vA, vB = _t(f), _t(a), _t(b)
    return et(et(est_un_graphe_fonctionnel(vF), egal(E.dom(vF), vA)),
              E.inclus(vF, E.produit(vA, vB)))


# ── §II.3.4 — Application identique Id_A : x ↦ x ──────────────────────────────
def graphe_identite(a, x="x"):
    """Graphe de Id_A := {(x, x) | x∈A}  (= la diagonale Δ_A, E.III.3.1).

    Construit comme graphe-terme de la fonction constante-en-soi x↦x (mécanisme
    C54 `graphe_terme`) ; sa caractérisation d'appartenance découle de
    `axiome_graphe_terme` (théorie dédiée existante).  Égal en extension à Δ_A."""
    return E.graphe_terme(_t(a), var(x), x)


def application_identique(a, x="x"):
    """Id_A := (x ↦ x sur A)  =  (graphe Δ_A, A, A)   (application identique, E.II.3.4).

    La fonction-terme x↦x de source A et but A (mécanisme C54 `fonction_terme`) :
    le triple ({(x,x)|x∈A}, A, A).  Son graphe est la diagonale Δ_A (E.III.3.1).
    Pour x∈A, Id_A(x) = x (caractérisé par axiome_graphe_terme, théorie dédiée)."""
    return E.fonction_terme(_t(a), var(x), _t(a), x)


# ── Lemme direct (introduction « par construction ») ──────────────────────────
def application_identique_est_application(a="A", x="x"):
    """⊢ graphe-Id_A ⊂ A×A.   (le graphe de l'identité est inclus dans A×A.)

    Lemme DIRECT : tout w∈graphe(Id_A) est un couple (x,x) avec x∈A, donc ∈ A×A.
    Via `axiome_graphe_terme` (théorie dédiée) + `AXIOME_PRODUIT`.  On ne prouve PAS
    ici « Id_A est une application » au complet (fonctionnalité + dom exact) — gros
    lemme reporté ; seule l'inclusion du graphe dans A×A est établie."""
    from bourbaki.logique.formule import existe
    from bourbaki.logique.tactiques.tactiques_abrege2 import (
        instancie, equivalence_avant, equivalence_arriere, conjonction_intro,
        conjonction_elim_gauche, conjonction_elim_droite)
    from bourbaki.logique.tactiques.tactiques_abrege import syllogisme
    from bourbaki.logique.tactiques.tactiques_abrege_quantif import existe_elimination
    from bourbaki.logique.tactiques.tactiques_abrege_egalite import symetrie

    vA = _t(a)
    vw, vx, vy = var("w"), var(x), var("y")
    vp, vq = var("p"), var("q")

    # corps du produit, paramétré par les deux positions (même imbrication que
    # AXIOME_PRODUIT : ((w=(p,q) et p∈A) et q∈A)).
    def prod_corps(t1, t2):
        return et(et(egal(vw, E.couple(t1, t2)), appartient(t1, vA)),
                  appartient(t2, vA))
    corps_q = existe("q", prod_corps(vx, vq))          # (∃q)((w=(x,q) et x∈A) et q∈A)
    corps_pq = existe("p", existe("q", prod_corps(vp, vq)))   # (∃p)(∃q)(...)

    # axiome C54 : (∀w)(w∈G ⇔ (∃x)(∃y)(w=(x,y) et x∈A et y=x))
    th = E.theorie_graphe_terme(vA, vx, x)
    ax = N.axiome(th, E.axiome_graphe_terme(vA, vx, x))      # (∀w)(...)
    inst = instancie(ax, vw)                                 # w∈G ⇔ (∃x)(∃y)(...C54...)

    # AXIOME_PRODUIT instancié à A,A,w : w∈A×A ⇔ (∃p)(∃q)((w=(p,q) et p∈A) et q∈A)
    axp = N.axiome(E.theorie_ensembles(), E.AXIOME_PRODUIT)
    instp = instancie(instancie(instancie(axp, vA), vA), vw)  # w∈A×A ⇔ corps_pq

    # corps C54 (témoins x,y) : (w=(x,y) et x∈A) et y=x   ⊢   w∈A×A
    corps = et(et(egal(vw, E.couple(vx, vy)), appartient(vx, vA)), egal(vy, vx))
    hc = N.assume(corps)
    w_xy = conjonction_elim_gauche(conjonction_elim_gauche(hc))   # w=(x,y)
    x_in = conjonction_elim_droite(conjonction_elim_gauche(hc))   # x∈A
    y_eq_x = conjonction_elim_droite(hc)                          # y=x
    # y∈A : de x=y et x∈A par Leibniz (s6) sur w2 ↦ w2∈A
    x_eq_y = N.modus_ponens(y_eq_x, symetrie(vy, vx))            # x=y
    y_in = N.modus_ponens(x_in, equivalence_avant(
        N.modus_ponens(x_eq_y, N.s6(vx, vy, "w2", appartient(var("w2"), vA)))))  # y∈A

    built = conjonction_intro(conjonction_intro(w_xy, x_in), y_in)   # = prod_corps(x,y)
    # ∃-intro q puis p (S5 : (t|v)R ⇒ (∃v)R).
    #   s5(prod_corps(x,q), vy, "q") : (vy|q)prod_corps(x,q) = prod_corps(x,y) ⇒ corps_q
    ex_q = N.modus_ponens(built, N.s5(prod_corps(vx, vq), vy, "q"))   # ⊢ corps_q
    #   s5(corps_q-as-body-of-p, vx, "p") : corps_q = (vx|p)(∃q)prod_corps(p,q) ⇒ corps_pq
    ex_pq = N.modus_ponens(ex_q, N.s5(existe("q", prod_corps(vp, vq)), vx, "p"))  # ⊢ corps_pq
    to_prod = N.modus_ponens(ex_pq, equivalence_arriere(instp))      # ⊢ w∈A×A
    membre_imp = existe_elimination(
        existe_elimination(N.loi_deduction(corps, to_prod), "y"), "x")  # (∃x)(∃y)corps ⇒ w∈A×A
    w_in_prod = syllogisme(equivalence_avant(inst), membre_imp)      # w∈G ⇒ w∈A×A
    return N.generalisation("w", w_in_prod)                          # ⊢ G ⊂ A×A


__all__ = [
    "est_une_correspondance", "correspondance",
    "est_un_graphe_fonctionnel", "est_une_fonction",
    "est_application",
    "graphe_identite", "application_identique",
    "application_identique_est_application",
]
