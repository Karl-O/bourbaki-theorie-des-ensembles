"""§II.5.3 — La diagonale vit dans le produit E^I  (E.II.5.3).

Pour x∈E, x̃ := graphe de la fonction constante ι↦x (ι∈I) est le graphe d'une
APPLICATION de I dans E ; il appartient donc à E^I = exposant(I,E) (l'ensemble des
graphes fonctionnels de I dans E, E.II.5.2).  Par conséquent la DIAGONALE
Δ = { x̃ | x∈E } = graphe(diag)⟨E⟩ est une PARTIE de E^I.  Ce module CERTIFIE par le
noyau LCF ces deux faits, par une preuve PUREMENT ensembliste (graphes fonctionnels)
— aucun calcul cardinal :

  (a)  `diagonale_terme_dans_exposant`   ⊢ (x∈E) ⇒ ( x̃ ∈ E^I ) ;
  (b)  `diagonale_incluse_exposant`      ⊢ Δ ⊂ E^I .

CARACTÉRISATION DE E^I (E.II.5.2, théorie DÉDIÉE `theorie_exposant`, HORS des 22
axiomes) :  `axiome_exposant(I,E)` donne, pour tout graphe G,
        G ∈ E^I  ⇔  ( ( G ⊂ I×E  et  G fonctionnel )  et  dom G = I ) .

STRATÉGIE (a) — instancier cet axiome en x̃ = graphe_terme(I,x,ι) et fermer les
trois conjoints :
  (i)   x̃ fonctionnel   : `graphe_terme_fonctionnel` (cœur du Critère C54) ;
  (ii)  dom x̃ = I        : `graphe_terme_domaine` (première projection) ;
  (iii) x̃ ⊂ I×E          : tout z∈x̃ est un couple (ι,y) avec ι∈I et y=x ; sous
        l'hypothèse x∈E, y=x∈E (Leibniz), donc (ι,y)∈I×E (`couple_dans_produit`),
        d'où z∈I×E (Leibniz, z=(ι,y)) — les témoins ι,y sont déchargés
        (existe_elimination) car la conclusion z∈I×E ne les mentionne pas.
La conjonction des trois et le sens ⇐ de l'axiome donnent x̃∈E^I ; `loi_deduction`
décharge l'unique hypothèse x∈E → l'implication CLOSE.

STRATÉGIE (b) — Δ = graphe(diag)⟨E⟩ ; z∈Δ ⇔ (∃x)(x∈E et (x,z)∈graphe(diag))
(`membre_diagonale`, AXIOME_IMAGE).  Sous le témoin x : (x,z)∈graphe(diag) ⇔
(x∈E et z=x̃) (`membre_graphe_terme` sur le graphe-terme x↦x̃, valeur-terme T[x]=x̃) ;
on en tire x∈E et z=x̃.  Sous x∈E, (a) donne x̃∈E^I ; z=x̃ réécrit en z∈E^I (Leibniz).
existe_elimination décharge x (z∈E^I ne le mentionne pas) ; `generalisation`/def de ⊂
ferment Δ ⊂ E^I.

GARDE-FOUS : primitives N.* uniquement (aucun Theoreme fabriqué) ; la caractérisation
de E^I vit dans la théorie SÉPARÉE `theorie_exposant` (motif theorie_graphe_terme),
donc theorie_ensembles RESTE à 22 axiomes ; conclusions == cibles, hypothèses =
antécédents honnêtes (jamais la conclusion en hypothèse).

LIANTS FRAIS (anti-capture de τ) : le graphe-terme lie son domaine en « ι » (resp.
« x » pour graphe(diag)) ; la valeur τy de `valeur` lie « y » ; on choisit donc les
binders du corps (« y », « yb ») distincts des coordonnées-paramètres.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (Terme, var, egal, et, impl,
                                       appartient, existe, inclus)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    instancie, equivalence_avant, equivalence_arriere, conjonction_intro,
    conjonction_elim_gauche, conjonction_elim_droite)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import symetrie
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import existe_elimination
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_6_fonction_terme.ensembles_fonction_terme import (
    membre_graphe_terme, graphe_terme_fonctionnel)
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_6_fonction_terme.ensembles_projections_terme import (
    graphe_terme_domaine)
from bourbaki.ii_theorie_des_ensembles.ii_2_couples.ii_2_2_produit_deux_ensembles.ensembles_produit import (
    couple_dans_produit_ssi)
from bourbaki.ii_theorie_des_ensembles.ii_5_produit_famille.ii_5_1_extension_canonique.ensembles_extension_canonique import (
    famille_constante, graphe_application_diagonale, diagonale_produit, membre_diagonale)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# ════════════════════════════════════════════════════════════════════════════
# (a)  x̃ ∈ E^I   (le graphe constant ι↦x est un graphe fonctionnel de I dans E)
# ════════════════════════════════════════════════════════════════════════════
def cible_diagonale_terme_dans_exposant(e="E", i="I", x="x", iota="iota"):
    """Énoncé visé : (x ∈ E) ⇒ ( x̃ ∈ E^I ).   (§II.5.3 : x̃ = ι↦x est dans E^I.)

    x̃ = famille_constante(I, x, ι) = graphe_terme(I, x, ι) ; E^I = exposant(I, E)."""
    vE, vI, vx = _t(e), _t(i), _t(x)
    xt = famille_constante(vI, vx, iota)                       # x̃
    return impl(appartient(vx, vE), appartient(xt, E.exposant(vI, vE)))


def _inclus_terme_dans_produit(vI, vE, vx, iota):
    """{x ∈ E} ⊢ x̃ ⊂ I×E,   x̃ = graphe_terme(I, x, ι).

    z∈x̃ ⇔ (∃ι)(∃y)(z=(ι,y) et ι∈I et y=x)  (axiome_graphe_terme) ; sous ce corps,
    y=x∈E (Leibniz) et ι∈I donnent (ι,y)∈I×E (`couple_dans_produit`), réécrit en
    z∈I×E par z=(ι,y) (Leibniz).  Témoins ι,y déchargés (conclusion sans ι,y)."""
    vz, vy = var("z"), var("y")
    xt = famille_constante(vI, vx, iota)                       # x̃ = graphe_terme(I,x,ι)
    prod = E.produit(vI, vE)                                   # I×E
    # z∈x̃ ⇔ (∃ι)(∃y)(z=(ι,y) et ι∈I et y=x)  (axiome_graphe_terme instancié en z)
    th = E.theorie_graphe_terme(vI, vx, iota)
    ax = N.axiome(th, E.axiome_graphe_terme(vI, vx, iota))
    car = instancie(ax, vz)
    viota = var(iota)
    body = et(et(egal(vz, E.couple(viota, vy)), appartient(viota, vI)),
              egal(vy, vx))                                    # z=(ι,y) et ι∈I et y=x
    hb = N.assume(body)
    z_eq = conjonction_elim_gauche(conjonction_elim_gauche(hb))   # z=(ι,y)
    iota_in = conjonction_elim_droite(conjonction_elim_gauche(hb))  # ι∈I
    y_eq_x = conjonction_elim_droite(hb)                          # y=x
    # y∈E : de x∈E et y=x (Leibniz S6 sur w∈E)
    h_x = N.assume(appartient(vx, vE))                           # x∈E
    y_in_E = N.modus_ponens(h_x, equivalence_arriere(N.modus_ponens(
        y_eq_x, N.s6(vy, vx, "w", appartient(var("w"), vE)))))   # y∈E
    # (ι,y)∈I×E  via couple_dans_produit_ssi : ((ι,y)∈I×E) ⇔ (ι∈I et y∈E) ; sens ⇐
    cple = equivalence_arriere(couple_dans_produit_ssi(viota, vy, vI, vE))  # (ι∈I et y∈E) ⇒ (ι,y)∈I×E
    iy_in_prod = N.modus_ponens(conjonction_intro(iota_in, y_in_E), cple)  # (ι,y)∈I×E
    # z∈I×E : réécrire (ι,y) → z via z=(ι,y) (Leibniz S6, sens (ι,y)↦z)
    cple_eq_z = N.modus_ponens(z_eq, symetrie(vz, E.couple(viota, vy)))   # (ι,y)=z
    z_in_prod = N.modus_ponens(iy_in_prod, equivalence_avant(N.modus_ponens(
        cple_eq_z, N.s6(E.couple(viota, vy), vz, "w", appartient(var("w"), prod)))))  # z∈I×E
    # décharger le corps, éliminer les témoins y puis ι (z∈I×E sans ι,y)
    ex_imp = existe_elimination(existe_elimination(
        N.loi_deduction(body, z_in_prod), "y"), iota)          # (∃ι)(∃y)body ⇒ z∈I×E
    h_z = N.assume(appartient(vz, xt))                          # z∈x̃
    ex = N.modus_ponens(h_z, equivalence_avant(car))           # (∃ι)(∃y)body
    z_in_prod2 = N.modus_ponens(ex, ex_imp)                    # z∈I×E   [hyp x∈E]
    imp = N.loi_deduction(appartient(vz, xt), z_in_prod2)      # z∈x̃ ⇒ z∈I×E
    return N.generalisation("z", imp)                          # x̃ ⊂ I×E   [hyp x∈E]


# @livre Ch.II §5.3 Def.- | E II.33 L.18-22 | PDF p.84
def diagonale_terme_dans_exposant(e="E", i="I", x="x", iota="iota"):
    """⊢ (x ∈ E) ⇒ ( x̃ ∈ E^I ).   (§II.5.3 : le graphe constant ι↦x est dans E^I.)

    Cf. docstring du module pour la stratégie : axiome_exposant(I,E) instancié en x̃,
    les trois conjoints (fonctionnel, dom=I, ⊂I×E) fermés, puis le sens ⇐ ; l'unique
    hypothèse x∈E est déchargée par loi_deduction."""
    vE, vI, vx = _t(e), _t(i), _t(x)
    xt = famille_constante(vI, vx, iota)                       # x̃ = graphe_terme(I,x,ι)

    # axiome_exposant(I,E) en x̃ : x̃∈E^I ⇔ ((x̃⊂I×E et x̃ fonct) et dom x̃=I)
    ax_exp = N.axiome(E.theorie_exposant(vI, vE), E.axiome_exposant(vI, vE))
    car = instancie(ax_exp, xt)

    # (i) x̃ fonctionnel   (graphe_terme_fonctionnel, sans hypothèse)
    func = graphe_terme_fonctionnel(vI, vx, iota, "y")         # est_fonctionnel(x̃)
    # (ii) dom x̃ = I       (graphe_terme_domaine, sans hypothèse)
    domeq = graphe_terme_domaine(vI, vx, iota, "y", "z")       # dom(x̃) = I
    # (iii) x̃ ⊂ I×E        (sous x∈E)
    incl = _inclus_terme_dans_produit(vI, vE, vx, iota)        # x̃⊂I×E   [hyp x∈E]

    # conjonction ((x̃⊂I×E et x̃ fonct) et dom x̃=I) puis sens ⇐ de l'axiome
    corps = conjonction_intro(conjonction_intro(incl, func), domeq)
    xt_in_exp = N.modus_ponens(corps, equivalence_arriere(car))   # x̃∈E^I   [hyp x∈E]
    return N.loi_deduction(appartient(vx, vE), xt_in_exp)        # (x∈E) ⇒ x̃∈E^I


# ════════════════════════════════════════════════════════════════════════════
# (b)  Δ ⊂ E^I   (la diagonale est une partie du produit E^I)
# ════════════════════════════════════════════════════════════════════════════
def cible_diagonale_incluse_exposant(e="E", i="I", x="xa", iota="iota"):
    """Énoncé visé : Δ ⊂ E^I.   (§II.5.3 : la diagonale est une partie du produit.)

    Δ = diagonale_produit(E, I, xa, ι) = graphe(diag)⟨E⟩ = {x̃ | x∈E} ; E^I = exposant(I,E)."""
    vE, vI = _t(e), _t(i)
    Delta = diagonale_produit(vE, vI, x, iota)                 # Δ
    return inclus(Delta, E.exposant(vI, vE))


# @livre Ch.II §5.3 Def.- | E II.33 L.18-22 | PDF p.84
def diagonale_incluse_exposant(e="E", i="I", x="xa", iota="iota"):
    """⊢ Δ ⊂ E^I.   (§II.5.3 : la diagonale est une partie du produit E^I.)

    Δ = {x̃ | x∈E} ; chaque x̃ est dans E^I par `diagonale_terme_dans_exposant` (a).
    Cf. docstring du module pour la stratégie (membre_diagonale + membre_graphe_terme
    donnent x∈E et z=x̃ sous le témoin x ; (a) puis Leibniz donnent z∈E^I)."""
    vE, vI = _t(e), _t(i)
    vz = var("z")
    Delta = diagonale_produit(vE, vI, x, iota)                 # Δ = graphe(diag)⟨E⟩
    GD = graphe_application_diagonale(vE, vI, x, iota)         # graphe(diag) = graphe_terme(E, x↦x̃, xa)
    T = famille_constante(vI, var(x), iota)                    # valeur-terme x↦x̃  (lié par xa)

    # z∈Δ ⇔ (∃x)(x∈E et (x,z)∈graphe(diag))   (membre_diagonale, AXIOME_IMAGE ; le
    # liant existentiel de l'image est « x », ≠ « xa » liant du graphe-terme).
    # membre_diagonale enveloppe ses arguments par var() : on lui passe les NOMS
    # (e, i) — pas vE, vI — pour produire des var simples (sinon var(Terme) imbrique).
    mem_diag = membre_diagonale(e, i, x, iota)
    vw = var("x")                                              # témoin existentiel de l'image
    body = et(appartient(vw, vE), appartient(E.couple(vw, vz), GD))  # x∈E et (x,z)∈graphe(diag)
    hb = N.assume(body)
    w_in_E = conjonction_elim_gauche(hb)                       # x∈E
    cpl_in_GD = conjonction_elim_droite(hb)                    # (x,z)∈graphe(diag)

    # (x,z)∈graphe(diag) ⇔ (x∈E et z=x̃)   (membre_graphe_terme ; T[x] = x̃, le liant
    # de domaine « xa » du graphe-terme, corps interne « yb » ≠ z,x)
    mem_gt = membre_graphe_terme(vE, T, "x", "z", x, "yb")
    cond = N.modus_ponens(cpl_in_GD, equivalence_avant(mem_gt))   # x∈E et z=x̃
    z_eq_xt = conjonction_elim_droite(cond)                   # z = x̃   (x̃ = T[x])
    xt = famille_constante(vI, vw, iota)                       # x̃ = graphe_terme(I, x, ι) = T[x]

    # (a) en x : (x∈E) ⇒ x̃∈E^I ; modus_ponens avec x∈E
    a_imp = diagonale_terme_dans_exposant(vE, vI, vw, iota)    # (x∈E) ⇒ x̃∈E^I
    xt_in_exp = N.modus_ponens(w_in_E, a_imp)                 # x̃∈E^I
    # z∈E^I : réécrire x̃ → z via z=x̃ (Leibniz S6, sens x̃↦z)
    xt_eq_z = N.modus_ponens(z_eq_xt, symetrie(vz, xt))       # x̃=z
    z_in_exp = N.modus_ponens(xt_in_exp, equivalence_avant(N.modus_ponens(
        xt_eq_z, N.s6(xt, vz, "w", appartient(var("w"), E.exposant(vI, vE))))))  # z∈E^I

    # décharger le corps, éliminer le témoin x (z∈E^I sans x), puis fermer Δ⊂E^I
    ex_imp = existe_elimination(N.loi_deduction(body, z_in_exp), "x")   # (∃x)body ⇒ z∈E^I
    h_z = N.assume(appartient(vz, Delta))                     # z∈Δ
    ex = N.modus_ponens(h_z, equivalence_avant(mem_diag))     # (∃x)(x∈E et (x,z)∈graphe(diag))
    z_in_exp2 = N.modus_ponens(ex, ex_imp)                    # z∈E^I
    imp = N.loi_deduction(appartient(vz, Delta), z_in_exp2)   # z∈Δ ⇒ z∈E^I
    return N.generalisation("z", imp)                         # Δ ⊂ E^I


__all__ = [
    "cible_diagonale_terme_dans_exposant", "diagonale_terme_dans_exposant",
    "cible_diagonale_incluse_exposant", "diagonale_incluse_exposant",
]
