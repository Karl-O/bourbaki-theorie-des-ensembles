"""§II.5.3 — Injectivité de l'application diagonale  x ↦ x̃  (E.II.5.3).

L'application diagonale  diag : E → E^I,  x ↦ x̃  (x̃ = graphe de la fonction
constante ι↦x) est une INJECTION (Bourbaki, E.II.5.3).  Ce module CERTIFIE par le
noyau LCF l'injectivité, sous une hypothèse d'indice-témoin honnête  α∈I  (qui
écarte le cas dégénéré I=∅ où tous les x̃ valent ∅ et où l'injectivité est fausse
dès que E a deux éléments) :

    ⊢ ( α∈I  et  x∈E  et  y∈E  et  x̃ = ỹ )  ⇒  x = y .

STRATÉGIE (purement set/fonction-théorique, AUCUN calcul cardinal au runtime —
seul `graphe_terme_valeur` est importé du module Cantor, à coût d'import) :

  1.  x̃ = famille_constante(I, x) = graphe_terme(I, x, ι).  La valeur-terme est la
      CONSTANTE x (le liant ι n'y figure pas) ; donc, par `graphe_terme_valeur`
      (le pivot : {u∈A} ⊢ F(u) = (u|z)T), évalué en u=α avec T=x indépendant de ι :
                          {α∈I} ⊢ x̃(α) = x .
      De même  {α∈I} ⊢ ỹ(α) = y .

  2.  De l'hypothèse x̃ = ỹ, par Leibniz (congruence des termes, C44/S6) appliquée
      au terme « valeur(·, α) » (variable-trou w) :
                          (x̃ = ỹ) ⇒ ( x̃(α) = ỹ(α) ).

  3.  Composition d'égalités :   x = x̃(α) = ỹ(α) = y ,  d'où  x = y .

  4.  `loi_deduction` décharge la conjonction des quatre hypothèses → l'implication
      CLOSE (0 hypothèse non déchargée).

NOTE SUR LES NOMS DE LIANTS (capture de τ).  `valeur(F, u)` s'écrit τy((u,y)∈F)
(liant interne « y », fixé dans tout le projet et apparié par valeur_caracterisation
/C46).  La SECONDE variable générique du théorème est donc nommée « yy » (et non
« y ») afin que sa valeur-constante n'entre pas en collision avec ce liant « y » de
τ/valeur — c'est un simple choix de variable liée (l'énoncé reste « pour tous deux
éléments »), exactement le motif de binders frais des modules clos voisins.  Les
hypothèses x∈E, y∈E sont des hypothèses de TYPAGE de l'énoncé fidèle ; elles sont
portées par l'implication (déchargées par affaiblissement), la preuve n'en a pas
besoin (l'argument vaut pour x, y quelconques dès que α∈I).

GARDE-FOUS : primitives N.* uniquement (aucun Theoreme fabriqué) ; aucun axiome
neuf (theorie_ensembles reste à 22) ; conclusion close, == `cible_diagonale_injective`.
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (Terme, var, egal, et, impl, appartient)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (conjonction_elim_gauche,
                               conjonction_elim_droite)
from bourbaki.logique.i_4_egalitaires.tactiques_abrege_egalite import (symetrie, composer_egalites,
                                      congruence_terme)
from bourbaki.ensembles.familles.ii_5_produit_famille.ii_5_1_extension_canonique.ensembles_extension_canonique import famille_constante
from bourbaki.cardinaux.iii_3_equipotence_cardinaux.cantor.ensembles_cantor import graphe_terme_valeur


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def cible_diagonale_injective(e="E", i="I", x="x", y="yy", alpha="alpha", iota="iota"):
    """Énoncé visé : ( α∈I et x∈E et y∈E et x̃ = ỹ ) ⇒ x = y.   (§II.5.3, injectivité.)

    Hypothèse conjonctive  ((α∈I et x∈E) et y∈E) et x̃=ỹ  (associée à gauche, motif
    `conjonction_*`) ; x̃ = famille_constante(I, x, ι), ỹ = famille_constante(I, y, ι).
    « y » par défaut « yy » (≠ liant « y » de valeur/τ, cf. docstring du module)."""
    vE, vI = _t(e), _t(i)
    vx, vy, valpha = _t(x), _t(y), _t(alpha)
    xt = famille_constante(vI, vx, iota)                       # x̃
    yt = famille_constante(vI, vy, iota)                       # ỹ
    hyp = et(et(et(appartient(valpha, vI), appartient(vx, vE)),
                appartient(vy, vE)),
             egal(xt, yt))
    return impl(hyp, egal(vx, vy))


# @livre Ch.II §5.3 Def.- | E II.33 L.20-22 | PDF p.84
def diagonale_injective(e="E", i="I", x="x", y="yy", alpha="alpha", iota="iota"):
    """⊢ ( α∈I et x∈E et y∈E et x̃ = ỹ ) ⇒ x = y.   (§II.5.3 : x↦x̃ est une injection.)

    Injectivité de l'application diagonale, sous l'hypothèse d'indice-témoin α∈I.
    Cf. docstring du module pour la stratégie (valeurs x̃(α)=x, ỹ(α)=y via le pivot
    `graphe_terme_valeur`, Leibniz sur valeur(·,α), composition d'égalités)."""
    vE, vI = _t(e), _t(i)
    vx, vy, valpha = _t(x), _t(y), _t(alpha)
    xt = famille_constante(vI, vx, iota)                       # x̃ = graphe_terme(I, x, ι)
    yt = famille_constante(vI, vy, iota)                       # ỹ = graphe_terme(I, y, ι)

    # ── hypothèse conjonctive et extraction des conjoints utiles ──────────────
    H = et(et(et(appartient(valpha, vI), appartient(vx, vE)),
              appartient(vy, vE)),
           egal(xt, yt))
    hH = N.assume(H)
    h_eq = conjonction_elim_droite(hH)                         # x̃ = ỹ
    h_alpha = conjonction_elim_gauche(conjonction_elim_gauche(
        conjonction_elim_gauche(hH)))                          # α∈I

    # ── 1.  x̃(α) = x  et  ỹ(α) = y   (pivot graphe_terme_valeur, sous α∈I) ─────
    # graphe_terme_valeur(A, T, u, x, y) : {u∈A} ⊢ F(u) = (u|x)T, F=graphe_terme(A,T,x).
    # Ici A=I, T=x (resp. y) constante (indépendante de ι), u=α : (α|ι)x = x.
    val_x = graphe_terme_valeur(vI, vx, alpha, iota, "y")      # {α∈I} ⊢ x̃(α) = x
    val_y = graphe_terme_valeur(vI, vy, alpha, iota, "y")      # {α∈I} ⊢ ỹ(α) = y
    # décharger l'hypothèse α∈I de chacune par modus ponens avec h_alpha
    val_x = N.modus_ponens(h_alpha, N.loi_deduction(appartient(valpha, vI), val_x))
    val_y = N.modus_ponens(h_alpha, N.loi_deduction(appartient(valpha, vI), val_y))

    # ── 2.  Leibniz : (x̃ = ỹ) ⇒ ( x̃(α) = ỹ(α) )  via valeur(·, α), trou « w » ─
    V = E.valeur(var("w"), valpha)                             # valeur(w, α) (trou w)
    cong = congruence_terme(xt, yt, V, "w")                    # (x̃=ỹ) ⇒ (x̃(α)=ỹ(α))
    val_eq = N.modus_ponens(h_eq, cong)                        # x̃(α) = ỹ(α)   [hyp H]

    # ── 3.  composer : x = x̃(α) = ỹ(α) = y ─────────────────────────────────────
    x_xta = N.modus_ponens(val_x, symetrie(val_x.conclusion.termes[0],
                                           val_x.conclusion.termes[1]))   # x = x̃(α)
    chain = composer_egalites(composer_egalites(x_xta, val_eq), val_y)    # x = y   [hyp H]

    # ── 4.  décharger la conjonction des quatre hypothèses → implication close ─
    return N.loi_deduction(H, chain)


__all__ = ["cible_diagonale_injective", "diagonale_injective"]
