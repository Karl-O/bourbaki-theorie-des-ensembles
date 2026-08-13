"""§III.3.2 — Borne « 1 ≤ x pour tout cardinal x ≠ 0 » de l'ordre ≤ des cardinaux.

Énoncé VERBATIM (E.III.3.2, « Relation d'ordre ≤ entre cardinaux ») :
    « On a 0 ≤ x pour tout cardinal x, et 1 ≤ x pour tout cardinal x ≠ 0. »

La borne « 0 ≤ x » est certifiée dans ensembles_cardinaux_bornes.zero_inf_egal.
On certifie ici la SECONDE borne, INDÉPENDANTE de Cantor–Bernstein (réservé à
l'antisymétrie) :

  `un_inf_egal`  ⊢ ¬(X = ∅) ⇒ ({∅} ≤ X)      (= « 1 ≤ x » pour x = Card X ≠ 0,
  car 1 = Card{∅} et 0 = Card∅).

  Stratégie de Bourbaki rendue rigoureuse : si X ≠ ∅, il existe un élément e ∈ X
  (e := τ_w(w∈X), témoin canonique fourni par non_vide_ssi_element + existe_temoin) ;
  l'application CONSTANTE  {∅} → X,  ∅ ↦ e  est une injection de {∅} dans X.  Son
  graphe est le GRAPHE DE TERME (clos, AUCUN axiome nouveau)

        G := graphe_terme({∅}, e, "d0") = { (d, e) | d ∈ {∅} } = { (∅, e) }.

  Le terme défini T(d0) = e est CONSTANT (il ne dépend pas de la variable liée d0) :
  G est donc le graphe à un seul couple (∅, e).  On certifie est_injection_de(G,{∅},X)
  par ses quatre conjoints :
    • G fonctionnel        (graphe_terme_fonctionnel — un graphe de terme l'est) ;
    • dom G = {∅}          (graphe_terme_domaine) ;
    • G injective sur {∅}  (TRIVIAL : {∅} n'a qu'un élément — tout u∈{∅} vaut ∅, donc
                            deux éléments de {∅} sont égaux ; l'égalité des valeurs
                            n'est même pas utilisée) ;
    • image(G,{∅}) ⊂ X     (image = {e} ; le seul élément e est dans X par e∈X — ici
                            on UTILISE l'hypothèse X≠∅, sous forme e∈X) ;
  puis S5 (témoin G) donne (∃F)est_injection_de(F,{∅},X) = inf_egal_card({∅},X) =
  « {∅} ≤ X ».  On décharge enfin l'hypothèse e∈X par « ¬(X=∅) ⇒ e∈X ».

  `cardinal_un_inf_egal`  ⊢ ¬(X = ∅) ⇒ (1 ≤ Card X)   (1 = Card{∅}).

NB liant : le témoin emploie le binder « w » (≠ « z » qui sert de variable de
l'inclusion ⊂ et de l'extension A1) pour qu'aucune τ-capture ne survienne quand on
forme image(G,{∅}) ⊂ X ; le terme défini emploie « d0 » (≠ « x »/« y » des axiomes
DOM/IMAGE), si bien que G ne contient aucun « x »/« y » libre et que les instances
des axiomes conservent leurs liants structurels (appariement MP direct).
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (Terme, var, tau, egal, et, non, impl, appartient,
                                       existe, inclus, subst_t)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege import syllogisme
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (conjonction_intro,
                               conjonction_elim_gauche, conjonction_elim_droite,
                               equivalence_avant, equivalence_arriere,
                               equivalence_transitivite, instancie)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import symetrie, composer_egalites
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import (existe_elimination, alpha_existe)
from bourbaki.ii_theorie_des_ensembles.ii_2_couples.ii_2_1_definition_couples.ensembles_couples import singleton_membre
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_vide import non_vide_ssi_element
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_6_fonction_terme.ensembles_fonction_terme import (graphe_terme_fonctionnel,
                               membre_graphe_terme)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.cantor.ensembles_cantor import graphe_terme_domaine
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import est_injection_de, inf_egal_card, cardinal


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# ═══════════════════════════════════════════════════════════════════════════════
# Le marqueur 1 = {∅}, le témoin e = τ_w(w∈X), et le graphe constant G = {(∅,e)}
# ═══════════════════════════════════════════════════════════════════════════════
UN = E.singleton(E.VIDE)          # 1 = Card({∅}) = {∅}
_CV = "d0"                        # variable C54 (le terme défini ne dépend PAS d'elle)
_WB = "w"                         # binder du témoin (≠ « z » de l'inclusion / A1)


def _temoin(x):
    """e := τ_w(w ∈ X)   (élément canonique de X lorsque X ≠ ∅ ; binder « w »)."""
    return tau(_WB, appartient(var(_WB), _t(x)))


def _G(x):
    """G := graphe_terme({∅}, e, "d0") = { (∅, e) }   (graphe de l'application ∅↦e)."""
    return E.graphe_terme(UN, _temoin(x), _CV)


# ── e ∈ X  à partir de  ¬(X = ∅) ──────────────────────────────────────────────
def temoin_dans(x="X"):
    """⊢ ¬(X = ∅) ⇒ (e ∈ X),   e = τ_w(w∈X).   (X non vide a un élément ; clos.)

    non_vide_ssi_element donne ¬(X=∅) ⇒ (∃z)(z∈X) ; on renomme-α (∃z)→(∃w) puis
    existe_temoin (∃w)(w∈X) ⇒ (τ_w(w∈X)|w)(w∈X) = e∈X extrait le témoin canonique."""
    vX = _t(x)
    ex_z = equivalence_avant(non_vide_ssi_element(vX))         # ¬(X=∅) ⇒ (∃z)(z∈X)
    ren = alpha_existe("z", _WB, appartient(var("z"), vX))     # (∃z)(z∈X) ⇔ (∃w)(w∈X)
    ex_w = syllogisme(ex_z, equivalence_avant(ren))            # ¬(X=∅) ⇒ (∃w)(w∈X)
    et_w = N.existe_temoin(appartient(var(_WB), vX), _WB)      # (∃w)(w∈X) ⇒ e∈X
    return syllogisme(ex_w, et_w)                              # ¬(X=∅) ⇒ e∈X


# ── PALIER 1 : G fonctionnel  (clos) ──────────────────────────────────────────
def un_fonctionnel(x="X"):
    """⊢ est_fonctionnel(G),  G = graphe_terme({∅}, e).   (un graphe de terme l'est ; clos.)"""
    return graphe_terme_fonctionnel(UN, _temoin(x), _CV, "y")


# ── PALIER 2 : dom G = {∅}  (clos) ────────────────────────────────────────────
def un_domaine(x="X"):
    """⊢ dom(G) = {∅}.   (le graphe constant est défini sur tout {∅} ; clos.)"""
    return graphe_terme_domaine(UN, _temoin(x), _CV, "y", "z")


# ── PALIER 3 : injective_dans(G, {∅})  (clos, trivial — {∅} singleton) ─────────
def un_injective(x="X"):
    """⊢ injective_dans(G, {∅}).   (TRIVIAL : {∅} n'a qu'un élément ; clos.)

    Forme : (∀u)(∀u')(((u∈{∅} et u'∈{∅}) et G(u)=G(u')) ⇒ u=u').  Tout u∈{∅} vaut ∅
    (singleton_membre), de même u'=∅, donc u=∅=u' — l'égalité des valeurs n'est pas
    même utilisée.  Liants u, up (forme défaut de injective_dans)."""
    G = _G(x)
    vu, vup = var("u"), var("up")
    ante = et(et(appartient(vu, UN), appartient(vup, UN)),
              egal(E.valeur(G, vu), E.valeur(G, vup)))
    h = N.assume(ante)
    u_in = conjonction_elim_gauche(conjonction_elim_gauche(h))    # u∈{∅}
    up_in = conjonction_elim_droite(conjonction_elim_gauche(h))   # u'∈{∅}
    u_eq0 = N.modus_ponens(u_in, equivalence_avant(singleton_membre(vu, E.VIDE)))    # u=∅
    up_eq0 = N.modus_ponens(up_in, equivalence_avant(singleton_membre(vup, E.VIDE))) # u'=∅
    u_eq_up = composer_egalites(u_eq0, N.modus_ponens(up_eq0, symetrie(vup, E.VIDE)))  # u=∅=u'
    inner = N.loi_deduction(ante, u_eq_up)
    return N.generalisation("u", N.generalisation("up", inner))   # injective_dans(G, {∅})


# ── PALIER 4 : image(G, {∅}) ⊂ X  (sous e∈X) ─────────────────────────────────
def un_image_inclus(x="X"):
    """⊢_{e∈X}  image(G, {∅}) ⊂ X,   G = graphe_terme({∅}, e).

    z∈G⟨{∅}⟩ ⇔ (∃t)(t∈{∅} et (t,z)∈G) [AXIOME_IMAGE, témoin renommé « t »].  Sous le
    corps, (t,z)∈G donne z=T[t]=e (membre_graphe_terme ; T constant) ; e∈X et z=e
    (Leibniz) donnent z∈X.  ∃-élim → G⟨{∅}⟩ ⊂ X.  Liant z (= celui de l'inclusion),
    distinct du binder « w » du témoin e, d'où aucune capture."""
    vX = _t(x)
    G = _G(x)
    T = _temoin(x)                                    # e
    vz, vt = var("z"), var("t")
    he = N.assume(appartient(T, vX))                  # e∈X  [hyp]
    ax_img = N.axiome(E.theorie_ensembles(), E.AXIOME_IMAGE)
    img_car0 = instancie(instancie(instancie(ax_img, G), UN), vz)   # z∈G⟨{∅}⟩ ⇔ (∃x)(x∈{∅} et (x,z)∈G)
    inner_x = et(appartient(var("x"), UN), appartient(E.couple(var("x"), vz), G))
    ren = alpha_existe("x", "t", inner_x)
    img_car = equivalence_transitivite(img_car0, ren)              # … ⇔ (∃t)(t∈{∅} et (t,z)∈G)
    mem = membre_graphe_terme(UN, T, "t", "z", _CV, "yb")          # ((t,z)∈G) ⇔ (t∈{∅} et z=e)
    Tt = subst_t(vt, _CV, T)                                       # = e (T constant)
    body = et(appartient(vt, UN), appartient(E.couple(vt, vz), G))
    hb = N.assume(body)
    cpl_in = conjonction_elim_droite(hb)                           # (t,z)∈G
    z_eq_e = conjonction_elim_droite(N.modus_ponens(cpl_in, equivalence_avant(mem)))  # z=e
    z_in = N.modus_ponens(he, equivalence_arriere(N.modus_ponens(
        z_eq_e, N.s6(vz, Tt, "w2", appartient(var("w2"), vX)))))   # z∈X
    fwd_inner = existe_elimination(N.loi_deduction(body, z_in), "t")  # (∃t)body ⇒ z∈X
    fwd = syllogisme(equivalence_avant(img_car), fwd_inner)        # z∈G⟨{∅}⟩ ⇒ z∈X
    return N.generalisation("z", fwd)                             # image(G,{∅}) ⊂ X


# ═══════════════════════════════════════════════════════════════════════════════
# 1 ≤ x   pour x ≠ 0   (l'application constante {∅}→X, ∅↦e, injecte {∅} dans X)
# ═══════════════════════════════════════════════════════════════════════════════
# @livre Ch.III §3.2 Rem.- | E III.25 L.7-9 | PDF p.128
#   (petit texte : « Il est clair que l'on a 0 ≤ x pour tout cardinal x, et 1 ≤ x
#    pour tout cardinal x ≠ 0. » — seconde borne, 1 ≤ x pour x ≠ 0, certifiée ici.)
def un_inf_egal(x="X"):
    """⊢ ¬(X = ∅) ⇒ ({∅} ≤ X).   (« 1 ≤ x » pour x ≠ 0, E.III.3.2 ; 1 = Card{∅}.)

    Témoin = G = graphe_terme({∅}, e), e = τ_w(w∈X).  est_injection_de(G,{∅},X) tient
    par ses quatre conjoints — fonctionnel, dom={∅}, injectif (trivial), image⊂X (sous
    e∈X) ; S5 témoin G donne {∅}≤X.  L'hypothèse e∈X est ensuite déchargée par
    temoin_dans (« ¬(X=∅) ⇒ e∈X »), d'où la conclusion conditionnelle « ¬(X=∅) ⇒ … »."""
    vX = _t(x)
    G = _G(x)
    func = un_fonctionnel(x)                          # G fonctionnel
    domeq = un_domaine(x)                             # dom G = {∅}
    inj = un_injective(x)                             # injective_dans(G, {∅})
    img = un_image_inclus(x)                          # image(G,{∅}) ⊂ X   [hyp e∈X]
    injection = conjonction_intro(conjonction_intro(conjonction_intro(
        func, domeq), inj), img)                      # est_injection_de(G,{∅},X)  [hyp e∈X]
    le = N.modus_ponens(injection,
        N.s5(est_injection_de(var("F"), UN, vX), G, "F"))   # {∅} ≤ X   [hyp e∈X]
    # décharger e∈X via temoin_dans : ¬(X=∅) ⇒ e∈X, puis chaîner (syllogisme)
    e_inX = appartient(_temoin(x), vX)
    e_imp_le = N.loi_deduction(e_inX, le)             # e∈X ⇒ {∅}≤X
    return syllogisme(temoin_dans(x), e_imp_le)       # ¬(X=∅) ⇒ {∅}≤X


def cardinal_un_inf_egal(x="X"):
    """⊢ ¬(X = ∅) ⇒ (1 ≤ Card X).   (= « 1 ≤ x » pour x = Card X ≠ 0 ; E.III.3.2.)

    1 = Card{∅} = {∅} (le cardinal du singleton).  On généralise « ¬(X=∅)⇒{∅}≤X » en
    (∀X)(…) puis on INSTANCIE au TERME Card X : ¬(Card X=∅) ⇒ {∅}≤Card X.  Comme on
    cherche la forme « x≠0 ⇒ 1≤x » avec x=Card X, et que {∅}≤Card X EST 1≤Card X, la
    conclusion est exactement 1 ≤ Card X sous l'hypothèse Card X ≠ ∅ = 0."""
    vX = _t(x)
    cardX = cardinal(vX)
    gen = N.generalisation("X", un_inf_egal("X"))     # (∀X)(¬(X=∅) ⇒ {∅}≤X)
    return instancie(gen, cardX)                      # ¬(Card X=∅) ⇒ {∅}≤Card X = 1≤Card X


__all__ = ["UN", "temoin_dans", "un_fonctionnel", "un_domaine", "un_injective",
           "un_image_inclus", "un_inf_egal", "cardinal_un_inf_egal"]
