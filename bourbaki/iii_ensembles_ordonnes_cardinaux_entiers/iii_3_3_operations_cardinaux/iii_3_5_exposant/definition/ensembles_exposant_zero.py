"""§III.3.5 — ZÉRO-EXPOSANT  0^a = 0  pour  a ≠ 0  (E.III.3.5, Proposition 11, cas
indépendant de a^0=1).

VOIE FIDÈLE (rien postulé — on DÉRIVE depuis les axiomes de DÉFINITION de membership
de F^E et 𝓕(E;F), exactement comme ensembles_exposant_cardinal.py pour a^0=1) :

    0^a := exposant_cardinal_binaire(0, a) = Card(𝓕(a; 0)) = Card(𝓕(A; ∅))   (0=∅).

On montre que, lorsque A ≠ ∅, l'ensemble 𝓕(A; ∅) des applications de A dans ∅ est
VIDE (aucun graphe fonctionnel de domaine A non vide ne se plonge dans A×∅=∅), d'où
Card(𝓕(A; ∅)) = Card(∅) = 0.

Paliers (tous DÉRIVÉS, aucun théorème postulé) :

  (a) produit_vide_droit(A)        ⊢ A×∅ = ∅              (le produit de but vide est vide) ;
  (b) exposant_vide_but_est_vide(A) ⊢ G ∈ ∅^A ⇒ G = ∅     (G⊂A×∅=∅ ⇒ G⊂∅ ⇒ G=∅) ;
  (c) dom_vide_egale_vide          (importé) ⊢ dom(∅) = ∅ ;
  (d) exposant_vide_but_force_dom_vide(A) ⊢ G ∈ ∅^A ⇒ dom G = ∅
          (dom G = A par AXIOME_EXPOSANT, et G=∅ ⇒ dom G=∅ ; on en tire A=∅ aussi) ;
  (e) exposant_vide_but_vide(A)    ⊢ ¬(A=∅) ⇒ ¬(G ∈ ∅^A)  (∅^A est vide si A≠∅) ;
  (f) applications_but_vide_est_vide(A) ⊢ ¬(A=∅) ⇒ 𝓕(A;∅) = ∅  (aucun graphe G ⇒ aucune appl.) ;
  (g) exposant_zero_base_egale_zero(A)  ⊢ ¬(A=∅) ⇒ Card(𝓕(A;∅)) = Card(∅)   (= 0^a = 0) ;
  (h) exposant_cardinal_zero_base(A)    idem sur l'OPÉRATEUR exposant_cardinal_binaire.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (Terme, var, egal, et, non, ou, impl, appartient,
                     existe, pourtout, inclus, subst_t, subst_f)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege import a_implique_a, syllogisme
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (conjonction_intro, conjonction_elim_gauche,
                               conjonction_elim_droite, equivalence_avant,
                               equivalence_arriere, equivalence_transitivite,
                               instancie, projection_gauche, projection_droite)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (symetrie, composer_egalites,
                               congruence_terme)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import existe_elimination, alpha_existe
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_theoremes import egalite_par_extension, vide_sans_element
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import cardinal

# réutilisation des paliers vide déjà clos dans le module a^0=1
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_5_exposant.definition.ensembles_exposant_cardinal import (
    _ex_falso, _n_in_vide, vide_inclus, dom_vide_egale_vide,
    inclus_vide_implique_egal_vide, exposant_cardinal_binaire)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# ═══════════════════════════════════════════════════════════════════════════════
# (a)  A × ∅ = ∅   (le produit cartésien de BUT vide est vide)  — dual de produit_vide_gauche
# ═══════════════════════════════════════════════════════════════════════════════
def produit_vide_droit(a="A"):
    """⊢ A×∅ = ∅.   (le produit cartésien de but vide est vide.)

    z∈A×∅ ⇔ (∃p)(∃q)(z=(p,q) et p∈A et q∈∅) [AXIOME_PRODUIT].  ⇒ : q∈∅ impossible
    → ex falso ; double ∃-élim.  ⇐ : z∈∅ impossible.  Par extension (A1)."""
    vA = _t(a)
    vz, vp, vq = var("z"), var("p"), var("q")
    ax_prod = N.axiome(E.theorie_ensembles(), E.AXIOME_PRODUIT)
    prod_car = instancie(instancie(instancie(ax_prod, vA), E.VIDE), vz)  # z∈A×∅ ⇔ (∃p)(∃q)body
    # body = (z=(p,q) et p∈A) et q∈∅
    body = et(et(egal(vz, E.couple(vp, vq)), appartient(vp, vA)), appartient(vq, E.VIDE))
    hb = N.assume(body)
    q_in_vide = conjonction_elim_droite(hb)                            # q∈∅
    n_q = vide_sans_element("q")
    z_in_vide = _ex_falso(q_in_vide, n_q, appartient(vz, E.VIDE))      # z∈∅
    fwd_q = existe_elimination(N.loi_deduction(body, z_in_vide), "q")  # (∃q)body ⇒ z∈∅
    fwd_pq = existe_elimination(fwd_q, "p")                            # (∃p)(∃q)body ⇒ z∈∅
    fwd = syllogisme(equivalence_avant(prod_car), fwd_pq)             # z∈A×∅ ⇒ z∈∅
    # ⇐ : z∈∅ ⇒ z∈A×∅  par ex falso
    hz = N.assume(appartient(vz, E.VIDE))
    bwd = N.loi_deduction(appartient(vz, E.VIDE),
        _ex_falso(hz, vide_sans_element("z"), appartient(vz, E.produit(vA, E.VIDE))))
    equiv_z = conjonction_intro(fwd, bwd)              # z∈A×∅ ⇔ z∈∅
    char = N.generalisation("z", equiv_z)
    self_vide = N.generalisation("z", conjonction_intro(
        a_implique_a(appartient(vz, E.VIDE)), a_implique_a(appartient(vz, E.VIDE))))
    return egalite_par_extension(char, self_vide, E.produit(vA, E.VIDE), E.VIDE, "z")


# ═══════════════════════════════════════════════════════════════════════════════
# (b)  G ∈ ∅^A ⇒ G = ∅   (un graphe inclus dans A×∅=∅ est vide)
# ═══════════════════════════════════════════════════════════════════════════════
def exposant_vide_but_est_vide(a="A", g="G"):
    """⊢ (G ∈ ∅^A) ⇒ (G = ∅).   (tout graphe de ∅^A est vide : G⊂A×∅=∅ ⇒ G⊂∅ ⇒ G=∅.)

    AXIOME_EXPOSANT(A,∅) : G∈∅^A ⇔ (G⊂A×∅ et G fonctionnel et dom G=A).  Le 1ᵉʳ
    conjoint G⊂A×∅, avec A×∅=∅ (produit_vide_droit, Leibniz), donne G⊂∅ ; tout
    sous-ensemble du vide est vide (inclus_vide_implique_egal_vide)."""
    vA, vG = _t(a), _t(g)
    ax = N.axiome(E.theorie_exposant(vA, E.VIDE), E.axiome_exposant(vA, E.VIDE))
    car = instancie(ax, vG)                             # G∈∅^A ⇔ (G⊂A×∅ et G fonct et domG=A)
    h = N.assume(appartient(vG, E.exposant(vA, E.VIDE)))   # G∈∅^A
    corps = N.modus_ponens(h, equivalence_avant(car))   # (G⊂A×∅ et G fonct) et domG=A
    g_sub_prod = conjonction_elim_gauche(conjonction_elim_gauche(corps))   # G⊂A×∅
    # A×∅=∅ → G⊂∅  (Leibniz S6 sur le 2ᵉ argument de ⊂)
    pv = produit_vide_droit(vA)                         # A×∅=∅
    leib = N.s6(E.produit(vA, E.VIDE), E.VIDE, "w", inclus(vG, var("w")))   # (A×∅=∅)⇒(G⊂A×∅ ⇔ G⊂∅)
    g_sub_vide = N.modus_ponens(g_sub_prod,
                    equivalence_avant(N.modus_ponens(pv, leib)))   # G⊂∅
    g_eq_vide = N.modus_ponens(g_sub_vide, inclus_vide_implique_egal_vide(vG))   # G=∅
    return N.loi_deduction(appartient(vG, E.exposant(vA, E.VIDE)), g_eq_vide)


# ═══════════════════════════════════════════════════════════════════════════════
# (d)  G ∈ ∅^A ⇒ A = ∅   (le domaine de G est A par déf, et G=∅ ⇒ dom G=∅, d'où A=∅)
# ═══════════════════════════════════════════════════════════════════════════════
def exposant_vide_but_force_base_vide(a="A", g="G"):
    """⊢ (G ∈ ∅^A) ⇒ (A = ∅).   (l'existence d'un graphe de ∅^A force A vide.)

    AXIOME_EXPOSANT donne dom G = A (3ᵉ conjoint).  Or G = ∅ (exposant_vide_but_est_vide),
    donc dom G = dom ∅ = ∅ (congruence + dom_vide_egale_vide).  Par transitivité de =,
    A = dom G = ∅, donc A = ∅."""
    vA, vG = _t(a), _t(g)
    ax = N.axiome(E.theorie_exposant(vA, E.VIDE), E.axiome_exposant(vA, E.VIDE))
    car = instancie(ax, vG)                             # G∈∅^A ⇔ (G⊂A×∅ et G fonct et domG=A)
    h = N.assume(appartient(vG, E.exposant(vA, E.VIDE)))   # G∈∅^A
    corps = N.modus_ponens(h, equivalence_avant(car))   # (G⊂A×∅ et G fonct) et domG=A
    dom_g_eq_A = conjonction_elim_droite(corps)         # dom G = A
    A_eq_dom_g = N.modus_ponens(dom_g_eq_A,             # A = dom G  (symétrie de =)
                    symetrie(E.dom(vG), vA))
    # G=∅ → dom G = dom ∅  (congruence sur le trou w dans dom(w))
    g_eq_vide = N.modus_ponens(h, exposant_vide_but_est_vide(vA, vG))   # G=∅
    dom_cong = N.modus_ponens(g_eq_vide, congruence_terme(vG, E.VIDE, E.dom(var("w"))))  # dom G=dom ∅
    dom_g_eq_vide = composer_egalites(dom_cong, dom_vide_egale_vide())  # dom G = ∅
    A_eq_vide = composer_egalites(A_eq_dom_g, dom_g_eq_vide)            # A = ∅
    return N.loi_deduction(appartient(vG, E.exposant(vA, E.VIDE)), A_eq_vide)


# ═══════════════════════════════════════════════════════════════════════════════
# (e)  ¬(A=∅) ⇒ ¬(G ∈ ∅^A)   (∅^A est VIDE quand A≠∅)
# ═══════════════════════════════════════════════════════════════════════════════
def exposant_vide_but_vide(a="A", g="G"):
    """⊢ ¬(A = ∅) ⇒ ¬(G ∈ ∅^A).   (si A≠∅, aucun graphe n'appartient à ∅^A.)

    Contraposée de exposant_vide_but_force_base_vide (G∈∅^A ⇒ A=∅) : si A≠∅, alors
    ¬(G∈∅^A)."""
    vA, vG = _t(a), _t(g)
    impl_force = exposant_vide_but_force_base_vide(vA, vG)   # G∈∅^A ⇒ A=∅
    # contraposition : (P⇒Q) ⊢ (¬Q ⇒ ¬P)
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import contraposition
    return contraposition(impl_force)                       # ¬(A=∅) ⇒ ¬(G∈∅^A)


# ═══════════════════════════════════════════════════════════════════════════════
# (f)  ¬(A=∅) ⇒ 𝓕(A;∅) = ∅   (aucune application A→∅ quand A≠∅)
# ═══════════════════════════════════════════════════════════════════════════════
def applications_but_vide_est_vide(a="A"):
    """⊢ ¬(A = ∅) ⇒ 𝓕(A; ∅) = ∅.   (l'ensemble des applications de A dans ∅ est vide.)

    AXIOME_APPLICATIONS(A,∅) : z∈𝓕(A;∅) ⇔ (∃G)(z=((G,A),∅) et G∈∅^A).
      ⇒ : sous ¬(A=∅), le corps existentiel est impossible (G∈∅^A est faux,
          exposant_vide_but_vide), donc (∃G)body est faux, donc z∈𝓕(A;∅) ⇒ z∈∅
          (ex falso) ; ∃-élim.
      ⇐ : z∈∅ ⇒ z∈𝓕(A;∅) vacuement.
    Par extension (A1).  Hypothèse ¬(A=∅) tirée tout du long, déchargée à la fin."""
    vA = _t(a)
    vz, vG = var("z"), var("G")
    hA = N.assume(non(egal(vA, E.VIDE)))                # ¬(A=∅)  (hyp courante)
    ax = N.axiome(E.theorie_applications(vA, E.VIDE), E.axiome_applications(vA, E.VIDE))
    app_car = instancie(ax, vz)                         # z∈𝓕(A;∅) ⇔ (∃G)(z=((G,A),∅) et G∈∅^A)
    triple = E.couple(E.couple(vG, vA), E.VIDE)         # ((G,A),∅)
    body = et(egal(vz, triple), appartient(vG, E.exposant(vA, E.VIDE)))
    # ── ⇒ : sous le corps body, G∈∅^A est faux (car A≠∅) → ex falso z∈∅ ──────────
    hb = N.assume(body)
    G_in = conjonction_elim_droite(hb)                  # G∈∅^A
    n_G_in = N.modus_ponens(hA, exposant_vide_but_vide(vA, vG))   # ¬(G∈∅^A)
    z_in_vide = _ex_falso(G_in, n_G_in, appartient(vz, E.VIDE))   # z∈∅  [sous body]
    fwd_inner = existe_elimination(N.loi_deduction(body, z_in_vide), "G")   # (∃G)body ⇒ z∈∅
    fwd = syllogisme(equivalence_avant(app_car), fwd_inner)       # z∈𝓕(A;∅) ⇒ z∈∅
    # ── ⇐ : z∈∅ ⇒ z∈𝓕(A;∅)  par ex falso ─────────────────────────────────────
    hz = N.assume(appartient(vz, E.VIDE))
    bwd = N.loi_deduction(appartient(vz, E.VIDE),
        _ex_falso(hz, vide_sans_element("z"), appartient(vz, E.applications(vA, E.VIDE))))
    equiv_z = conjonction_intro(fwd, bwd)               # z∈𝓕(A;∅) ⇔ z∈∅
    char = N.generalisation("z", equiv_z)
    self_vide = N.generalisation("z", conjonction_intro(
        a_implique_a(appartient(vz, E.VIDE)), a_implique_a(appartient(vz, E.VIDE))))
    eq = egalite_par_extension(char, self_vide, E.applications(vA, E.VIDE), E.VIDE, "z")  # 𝓕(A;∅)=∅  [sous ¬(A=∅)]
    return N.loi_deduction(non(egal(vA, E.VIDE)), eq)   # ¬(A=∅) ⇒ 𝓕(A;∅)=∅


# ═══════════════════════════════════════════════════════════════════════════════
# (g)  ¬(A=∅) ⇒ Card(𝓕(A;∅)) = Card(∅)   (= 0^a = 0, PROPOSITION 11, CLOS)
# ═══════════════════════════════════════════════════════════════════════════════
def exposant_zero_base_egale_zero(a="A"):
    """⊢ ¬(A = ∅) ⇒ Card(𝓕(A; ∅)) = Card(∅).   (= 0^a = 0 pour a≠0 ; PROPOSITION 11.)

    𝓕(A;∅)=∅ sous ¬(A=∅) (applications_but_vide_est_vide).  Congruence du cardinal
    (congruence_terme sur le trou w dans Card(w)) : (𝓕(A;∅)=∅) ⇒ Card(𝓕(A;∅))=Card(∅).
    MP, puis déchargement de l'hypothèse ¬(A=∅)."""
    vA = _t(a)
    AF = E.applications(vA, E.VIDE)                     # 𝓕(A;∅)  (support de 0^a)
    eq_sets = N.modus_ponens(N.assume(non(egal(vA, E.VIDE))),
                             applications_but_vide_est_vide(vA))   # 𝓕(A;∅)=∅  [sous ¬(A=∅)]
    cong = congruence_terme(AF, E.VIDE, cardinal(var("w")))       # (𝓕(A;∅)=∅) ⇒ Card(𝓕(A;∅))=Card(∅)
    card_eq = N.modus_ponens(eq_sets, cong)            # Card(𝓕(A;∅))=Card(∅)  [sous ¬(A=∅)]
    return N.loi_deduction(non(egal(vA, E.VIDE)), card_eq)   # ¬(A=∅) ⇒ Card(𝓕(A;∅))=Card(∅)


# @livre Ch.III §3.5 Prop.11 | E III.29 L.10-11 | PDF p.132
# (démo du livre pour 0^a=0 : « il n'existe aucune application d'un ensemble non
#  vide dans ∅ ».)
# @livre Ch.III §3.5 Demo.11 | E III.29 L.16-17 | PDF p.132
def exposant_cardinal_zero_base(a="A"):
    """⊢ ¬(A = ∅) ⇒ exposant_cardinal_binaire(∅, A) = Card(∅).   (0^a = 0 sur l'OPÉRATEUR.)

    Par définition exposant_cardinal_binaire(∅, A) = Card(𝓕(A; ∅)) (0 = ∅, la base).
    La conclusion est donc LITTÉRALEMENT exposant_zero_base_egale_zero(A)."""
    return exposant_zero_base_egale_zero(_t(a))


__all__ = ["produit_vide_droit",
           "exposant_vide_but_est_vide", "exposant_vide_but_force_base_vide",
           "exposant_vide_but_vide", "applications_but_vide_est_vide",
           "exposant_zero_base_egale_zero", "exposant_cardinal_zero_base"]
