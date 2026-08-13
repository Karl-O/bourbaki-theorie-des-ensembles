"""§III.3.5 — PROPOSITION 9 (forme exponentielle), CLÔTURE par CANTOR–BERNSTEIN :
a^(b+c) = a^b · a^c,  c.-à-d.

        ⊢ Card(𝓕(B⊔C; A)) = Card(𝓕(B;A) × 𝓕(C;A))           (= cible_prop9_exp_somme)

ROUTE = CANTOR–BERNSTEIN (évite TOUTE surjectivité).  On construit DEUX injections :

   (A) Φ : 𝓕(B⊔C;A) ↪ 𝓕(B;A) × 𝓕(C;A)     f ↦ ( ((f|B,B),A) , ((f|C,C),A) )
   (B) ψ : 𝓕(B;A) × 𝓕(C;A) ↪ 𝓕(B⊔C;A)     (g,h) ↦ recollement réindexé

puis  cantor_bernstein  ⊢  equipotent(𝓕(B⊔C;A), 𝓕(B;A)×𝓕(C;A))  et  _prop1_direct_t
⊢ Card(𝓕(B⊔C;A)) = Card(𝓕(B;A)×𝓕(C;A)) = cible.

LE DÉBLOCAGE — le PONT « valeur d'un graphe » (round courant) :
Une application f∈𝓕(E;F) est le TRIPLE ((G,E),F).  Or valeur(f,x) traite f comme un
graphe → garbage sur le triple.  Bourbaki : f(x) := G(x) = valeur DU GRAPHE
G = graphe_de(f) = pr₁(pr₁ f).  Les restrictions de Φ sont donc construites au niveau
du GRAPHE :  f|B := { (u, graphe_de(f)((u,0))) | u ∈ B }  (graphe_terme sur B).
Le pont `valeur_dans_codomaine(G,E,F,x)` ({G⊂E×F, dom G=E, x∈E} ⊢ G(x)∈F) donne alors
la BIEN-DÉFINITION (f|B ⊂ B×A), et `graphe_de_triple` (gr(((G,E),F))=G) relie f à G.

═══════════════════════════════════════════════════════════════════════════════
ÉTAT (round courant) :

  DIRECTION A — CLOSE (le déblocage) :
    `inf_egal_phi`  ⊢  inf_egal_card(𝓕(B⊔C;A), 𝓕(B;A)×𝓕(C;A))   (a^(b+c) ≤ a^b·a^c)
    via Φ : f ↦ (((f|B,B),A),((f|C,C),A)), dont les QUATRE conjoints de est_injection_de
    sont CLOS : W_phi_fonctionnel / W_phi_domaine / W_phi_image_incluse / W_phi_injective
    (cette dernière = back-and-forth complet : restrictions → valeurs du graphe →
    extensionnalité graphe_egal_par_valeurs → graphe_de(f₁)=graphe_de(f₂) → f₁=f₂).
    Le verrou « valeur d'application-triple » des rounds 24→32 est LEVÉ par le pont
    graphe_de + valeur_dans_codomaine.

  DIRECTION B — ψ : (g,h) ↦ ((K,B⊔C),A), K = recollement réindexé.  SONT CLOS :
    K_fonctionnelle, K_domaine, K_inclus, K_dans_exposant,
    psi_dans_applications_sous_appartenance (BIEN-DÉFINITION de ψ),
    W_psi_fonctionnel / W_psi_domaine / W_psi_image_incluse.
    RESTE OUVERT le SEUL conjoint injective_dans(W_ψ, …) (même back-and-forth que Φ,
    via valeur_reunion_gauche/droite) — voir `direction_B_REPORTE`.

  ASSEMBLEUR FINAL (VÉRIFIÉ) : `prop9_depuis_deux_injections(inf_A, inf_B)` ⊢
    Card(𝓕(B⊔C;A)) = Card(𝓕(B;A)×𝓕(C;A)) = cible_prop9_exp_somme, via cantor_bernstein
    + _prop1_direct_t.  Avec inf_A := inf_egal_phi() (CLOS), il ne reste qu'à fournir
    inf_B (Direction B) pour CLORE INCONDITIONNELLEMENT la Proposition 9.

theorie_ensembles INCHANGÉE (22 axiomes) ; AUCUN fichier existant modifié.
═══════════════════════════════════════════════════════════════════════════════
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (Terme, var, egal, et, non, ou, impl,
                     appartient, existe, pourtout, inclus, subst_t, subst_f)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege import a_implique_a, syllogisme
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, equivalence_transitivite, instancie,
    cas)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import existe_elimination
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
    symetrie, composer_egalites, congruence_terme)

from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    cardinal, est_injection_de, inf_egal_card, equipotent)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.fondations.ensembles_graphe_de import (
    graphe_de, graphe_de_triple)
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_4_fonctions.ensembles_valeur_codomaine import (
    couple_valeur_dans_graphe, valeur_dans_codomaine)
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_recollement_somme.ensembles_somme_disjointe import (
    somme_disjointe, ZERO, UN,
    injection_gauche_dans_somme, injection_droite_dans_somme,
    membre_somme_caracterise)
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_6_fonction_terme.ensembles_fonction_terme import (
    graphe_terme_fonctionnel, membre_graphe_terme)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.cantor.ensembles_cantor import (
    graphe_terme_domaine, graphe_terme_valeur)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_5_exposant.prop9_exp_somme.ensembles_exposant_somme import (
    membre_exposant_somme, membre_applications_somme, membre_applications_b,
    membre_produit_applications, applications_somme_donne_graphe)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_produit.ensembles_arith_cardinale import _prop1_direct_t


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# ═══════════════════════════════════════════════════════════════════════════════
#  LIANTS — choix sûrs (cf. PIÈGES de la mission)
# ───────────────────────────────────────────────────────────────────────────────
#   • graphe_de(f) lie a,b (pr₁ à deux niveaux) ;
#   • valeur(G,x,b) lie b — on passe « q » (≠ a,b,x,y,u,v,z) pour la valeur DANS un
#     graphe_terme quantifié sur y ;
#   • graphe_terme lie son point (ici « e ») et « y » en interne.
# Points d'évaluation des restrictions : éviter {e, y} (liant du graphe + interne).
_PT = "e"        # point courant du graphe-terme des restrictions
_VB = "m"        # liant frais du τ de la valeur  (≠ a,b,x,y,z,e ET ≠ p,q,w de produit_ssi)


# ═══════════════════════════════════════════════════════════════════════════════
#  LES RESTRICTIONS AU NIVEAU GRAPHE  (LE déblocage : graphe_de, pas valeur(f,·))
# ───────────────────────────────────────────────────────────────────────────────
#   RG(f) := { (e, graphe_de(f)((e,0))) | e∈B }   (graphe-terme C54)
#   RD(f) := { (e, graphe_de(f)((e,1))) | e∈C }
# ═══════════════════════════════════════════════════════════════════════════════
def _val_g(f):
    """graphe_de(f)((e,0))  = valeur DU GRAPHE de f sur la copie gauche (e,0)."""
    return E.valeur(graphe_de(_t(f)), E.couple(var(_PT), ZERO), _VB)


def _val_d(f):
    """graphe_de(f)((e,1))  = valeur DU GRAPHE de f sur la copie droite (e,1)."""
    return E.valeur(graphe_de(_t(f)), E.couple(var(_PT), UN), _VB)


def restriction_gauche(f, b):
    """f|B := { (e, graphe_de(f)((e,0))) | e∈B }  (terme, niveau GRAPHE)."""
    return E.graphe_terme(_t(b), _val_g(f), _PT)


def restriction_droite(f, c):
    """f|C := { (e, graphe_de(f)((e,1))) | e∈C }  (terme, niveau GRAPHE)."""
    return E.graphe_terme(_t(c), _val_d(f), _PT)


def phi_valeur(f, a, b, c):
    """Φ(f) := ( ((f|B,B),A) , ((f|C,C),A) )   (couple de deux applications-triples)."""
    vf, va, vb, vc = _t(f), _t(a), _t(b), _t(c)
    triple_g = E.couple(E.couple(restriction_gauche(vf, vb), vb), va)   # ((f|B,B),A)
    triple_d = E.couple(E.couple(restriction_droite(vf, vc), vc), va)   # ((f|C,C),A)
    return E.couple(triple_g, triple_d)


# ── valeurs / domaines / fonctionnalité des restrictions (C54) ────────────────
def restriction_gauche_fonctionnelle(f="f", b="B"):
    """⊢ est_fonctionnel(f|B).   (graphe-terme toujours fonctionnel, C54.)"""
    return graphe_terme_fonctionnel(_t(b), _val_g(f), _PT, "y")


def restriction_gauche_domaine(f="f", b="B"):
    """⊢ dom(f|B) = B."""
    return graphe_terme_domaine(_t(b), _val_g(f), _PT, "y", "z")


def restriction_droite_fonctionnelle(f="f", c="C"):
    """⊢ est_fonctionnel(f|C)."""
    return graphe_terme_fonctionnel(_t(c), _val_d(f), _PT, "y")


def restriction_droite_domaine(f="f", c="C"):
    """⊢ dom(f|C) = C."""
    return graphe_terme_domaine(_t(c), _val_d(f), _PT, "y", "z")


# ═══════════════════════════════════════════════════════════════════════════════
#  BIEN-DÉFINITION (LE PONT) :  f|B ⊂ B×A   sous  G⊂(B⊔C)×A et dom G=B⊔C
#   où G = graphe_de(f).  C'est ce qui débloque la Prop 9 : la valeur du GRAPHE
#   G((e,0)) est dans A pour e∈B (valeur_dans_codomaine), donc (e,G((e,0)))∈B×A.
# ═══════════════════════════════════════════════════════════════════════════════
def _membre_produit(u, v, a, b):
    """⊢ ((u,v) ∈ A×B) ⇔ (u∈A et v∈B)   pour des TERMES (couple_dans_produit_ssi)."""
    from bourbaki.ii_theorie_des_ensembles.ii_2_couples.ii_2_2_produit_deux_ensembles.ensembles_produit import couple_dans_produit_ssi
    return couple_dans_produit_ssi(_t(u), _t(v), _t(a), _t(b))


# ── PONT (valeur du graphe) avec LIANT τ paramétré _VB="q" (≠ y de graphe_terme) ──
# Re-dérive couple_valeur_dans_graphe / valeur_dans_codomaine avec le binder « q »,
# car la VALEUR figure dans un graphe_terme quantifié sur « y » (verrou liant-valeur).
def _couple_valeur_q(g, e, x):
    """{dom G = E, x ∈ E} ⊢ (x, G(x)) ∈ G,  où G(x) = valeur(G,x,« q »).

    Miroir de couple_valeur_dans_graphe avec le liant τ « q » (au lieu de « y »)."""
    vG, vE, vx = _t(g), _t(e), _t(x)
    vq = var(_VB)
    h_dom = N.assume(egal(E.dom(vG), vE))            # dom G = E
    h_xin = N.assume(appartient(vx, vE))             # x ∈ E
    leib = N.s6(E.dom(vG), vE, "w", appartient(vx, var("w")))
    x_in_dom = N.modus_ponens(h_xin, equivalence_arriere(N.modus_ponens(h_dom, leib)))
    ax_dom = N.axiome(E.theorie_ensembles(), E.AXIOME_DOM)
    dom_car = instancie(instancie(ax_dom, vG), vx)               # x∈dom G ⇔ (∃y)((x,y)∈G)
    # AXIOME_DOM lie « y » ; on renomme en « q » pour s'apparier à valeur(·,·,"q")
    from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import alpha_existe
    inner_y = appartient(E.couple(vx, var("y")), vG)
    ren = alpha_existe("y", _VB, inner_y)                        # (∃y)…⇔(∃q)…
    dom_car_q = equivalence_transitivite(dom_car, ren)           # x∈dom G ⇔ (∃q)((x,q)∈G)
    ex_q = N.modus_ponens(x_in_dom, equivalence_avant(dom_car_q))  # (∃q)((x,q)∈G)
    # existe_temoin pour le témoin canonique τq((x,q)∈G) = valeur(G,x,"q")
    r = appartient(E.couple(vx, vq), vG)
    return N.modus_ponens(ex_q, N.existe_temoin(r, _VB))         # (x, G(x))∈G


def _valeur_codomaine_q(g, e, f, x):
    """{G ⊂ E×F, dom G = E, x ∈ E} ⊢ G(x) ∈ F,  G(x) = valeur(G,x,« q »).

    Miroir de valeur_dans_codomaine avec le liant « q » (apparié au graphe_terme)."""
    from bourbaki.ii_theorie_des_ensembles.ii_2_couples.ii_2_2_produit_deux_ensembles.ensembles_produit import couple_dans_produit_ssi
    vG, vE, vF, vx = _t(g), _t(e), _t(f), _t(x)
    fx = E.valeur(vG, vx, _VB)                        # G(x)  (binder q)
    h_incl = N.assume(inclus(vG, E.produit(vE, vF)))  # G ⊂ E×F
    cpl = _couple_valeur_q(vG, vE, vx)               # (x,G(x))∈G  [dom G=E, x∈E]
    incl_inst = instancie(h_incl, E.couple(vx, fx))  # (x,G(x))∈G ⇒ (x,G(x))∈E×F
    in_prod = N.modus_ponens(cpl, incl_inst)         # (x,G(x))∈E×F
    ssi = couple_dans_produit_ssi(vx, fx, vE, vF)    # ((x,G(x))∈E×F) ⇔ (x∈E et G(x)∈F)
    return conjonction_elim_droite(
        N.modus_ponens(in_prod, equivalence_avant(ssi)))          # G(x)∈F


def _membre_graphe_terme_z(a, t, x, z="z", y="y"):
    """⊢ (z∈F) ⇔ (∃x)(∃y)(z=(x,y) et x∈A et y=T),  F=graphe_terme(A,T), point binder x.

    Instance de l'axiome graphe-terme C54 (axiome_graphe_terme), pour un z ARBITRAIRE
    (et non un couple (u,v) déjà décomposé comme membre_graphe_terme)."""
    va = _t(a)
    ax = N.axiome(E.theorie_graphe_terme(va, t, x, y, z),
                  E.axiome_graphe_terme(va, t, x, y, z))
    return instancie(ax, _t(z))


def _restriction_inclus(vf, va, vb, vc, vD, RG, T, marker, inj_lemme):
    """{ graphe_de(f)⊂(B⊔C)×A, dom graphe_de(f)=B⊔C } ⊢ RG ⊂ D×A.

    Cœur GÉNÉRIQUE de la bien-définition d'une restriction.  vb, vc fixent la somme
    B⊔C ; vD est le domaine de la restriction (B à gauche, C à droite).
    RG = graphe_terme(D, T), T = graphe_de(f)((e,marker)).  Pour z∈RG, z=(e,y) avec
    e∈D et y=T (axiome graphe-terme) ; (e,marker)∈B⊔C (inj_lemme) donc T∈A
    (_valeur_codomaine_q sous G⊂(B⊔C)×A, dom G=B⊔C), d'où (e,y)∈D×A, i.e. z∈D×A."""
    G = graphe_de(vf)
    BC = somme_disjointe(vb, vc)
    DA = E.produit(vD, va)                          # D×A
    ve, vy, vz = var(_PT), var("y"), var("z")

    hyp_incl = N.assume(inclus(G, E.produit(BC, va)))   # G ⊂ (B⊔C)×A
    hyp_dom = N.assume(egal(E.dom(G), BC))              # dom G = B⊔C

    car = _membre_graphe_terme_z(vD, T, _PT, "z", "y")  # z∈RG ⇔ (∃e)(∃y)(z=(e,y) et e∈D et y=T)
    body = et(et(egal(vz, E.couple(ve, vy)), appartient(ve, vD)), egal(vy, T))
    hb = N.assume(body)
    z_eq = conjonction_elim_gauche(conjonction_elim_gauche(hb))   # z=(e,y)
    eD = conjonction_elim_droite(conjonction_elim_gauche(hb))     # e∈D
    y_eq_T = conjonction_elim_droite(hb)                          # y=T
    em_in_BC = N.modus_ponens(eD, inj_lemme)                      # (e,marker)∈B⊔C
    vdc = _valeur_codomaine_q(G, BC, va, E.couple(ve, marker))    # ⊢ T∈A
    T_in_A = _cut(vdc, [
        (inclus(G, E.produit(BC, va)), hyp_incl),
        (egal(E.dom(G), BC), hyp_dom),
        (appartient(E.couple(ve, marker), BC), em_in_BC)])        # T∈A
    y_in_A = N.modus_ponens(T_in_A, equivalence_arriere(N.modus_ponens(
        y_eq_T, N.s6(vy, T, "w", appartient(var("w"), va)))))     # y∈A
    ey_in_prod = N.modus_ponens(conjonction_intro(eD, y_in_A),
                                equivalence_arriere(_membre_produit(ve, vy, vD, va)))  # (e,y)∈D×A
    z_in_prod = N.modus_ponens(ey_in_prod, equivalence_arriere(N.modus_ponens(
        z_eq, N.s6(vz, E.couple(ve, vy), "w", appartient(var("w"), DA)))))  # z∈D×A
    ex_imp = existe_elimination(existe_elimination(
        N.loi_deduction(body, z_in_prod), "y"), _PT)              # (∃e)(∃y)body ⇒ z∈D×A
    h_z = N.assume(appartient(vz, RG))
    ex = N.modus_ponens(h_z, equivalence_avant(car))             # (∃e)(∃y)body
    z_in_DA = N.modus_ponens(ex, ex_imp)                         # z∈D×A
    imp_z = N.loi_deduction(appartient(vz, RG), z_in_DA)         # z∈RG ⇒ z∈D×A
    return N.generalisation("z", imp_z)                         # RG ⊂ D×A


def restriction_gauche_inclus(f="f", a="A", b="B", c="C"):
    """{ graphe_de(f) ⊂ (B⊔C)×A,  dom(graphe_de(f)) = B⊔C }  ⊢  f|B ⊂ B×A.

    BIEN-DÉFINITION (gauche).  Voir _restriction_inclus.  LE PONT : la valeur du
    GRAPHE sous-jacent G=graphe_de(f), pas du triple.  Marker 0, injection gauche."""
    vf, va, vb, vc = _t(f), _t(a), _t(b), _t(c)
    return _restriction_inclus(vf, va, vb, vc, vb, restriction_gauche(vf, vb),
                               _val_g(vf), ZERO,
                               injection_gauche_dans_somme(var(_PT), vb, vc))


def restriction_droite_inclus(f="f", a="A", b="B", c="C"):
    """{ graphe_de(f) ⊂ (B⊔C)×A,  dom(graphe_de(f)) = B⊔C }  ⊢  f|C ⊂ C×A.

    BIEN-DÉFINITION (droite).  Miroir : marker 1, injection droite, D=C."""
    vf, va, vb, vc = _t(f), _t(a), _t(b), _t(c)
    return _restriction_inclus(vf, va, vb, vc, vc, restriction_droite(vf, vc),
                               _val_d(vf), UN,
                               injection_droite_dans_somme(var(_PT), vb, vc))


def _cut(thm, paires):
    """Remplace chaque hypothèse `hyp` de `thm` par sa preuve `preuve`
    (loi_deduction puis modus_ponens), pour une liste de (hyp, preuve)."""
    out = thm
    for hyp_formule, preuve in paires:
        out = N.modus_ponens(preuve, N.loi_deduction(hyp_formule, out))
    return out


# ═══════════════════════════════════════════════════════════════════════════════
#  f|B ∈ A^B   et   ((f|B,B),A) ∈ 𝓕(B;A)   (assemblage via axiome_exposant/applications)
# ═══════════════════════════════════════════════════════════════════════════════
def _restriction_dans_exposant(va, vD, RG, incl_thm, func_thm, dom_thm):
    """{hyps de incl_thm} ⊢ RG ∈ A^D.

    axiome_exposant(D,A) : RG∈A^D ⇔ (RG⊂D×A et RG fonctionnel et dom RG=D).
    Les trois conjoints : incl_thm (⊂, sous hyps structurelles), func_thm, dom_thm
    (clos).  Conjonction-intro puis sens ⇐ de l'axiome."""
    ax = N.axiome(E.theorie_exposant(vD, va), E.axiome_exposant(vD, va))
    car = instancie(ax, RG)                          # RG∈A^D ⇔ (RG⊂D×A et func et dom=D)
    corps = conjonction_intro(conjonction_intro(incl_thm, func_thm), dom_thm)
    return N.modus_ponens(corps, equivalence_arriere(car))   # RG∈A^D


def _triple_dans_applications(va, vD, RG, in_exp_thm):
    """{hyps de in_exp_thm} ⊢ ((RG,D),A) ∈ 𝓕(D;A).

    axiome_applications(D,A) : t∈𝓕(D;A) ⇔ (∃G)(t=((G,D),A) et G∈A^D).  Témoin
    G:=RG : t=((RG,D),A) (réflexivité) et RG∈A^D (in_exp_thm).  S5 + sens ⇐."""
    triple = E.couple(E.couple(RG, vD), va)          # ((RG,D),A)
    ax = N.axiome(E.theorie_applications(vD, va, "t", "G"),
                  E.axiome_applications(vD, va, "t", "G"))
    car = instancie(ax, triple)                      # ((RG,D),A)∈𝓕(D;A) ⇔ (∃G)(...)
    # corps de l'∃ avec témoin G:=RG : (((RG,D),A)=((RG,D),A) et RG∈A^D)
    cible = et(egal(triple, E.couple(E.couple(var("G"), vD), va)),
               appartient(var("G"), E.exposant(vD, va)))
    wit = conjonction_intro(N.reflexivite(triple), in_exp_thm)   # corps (témoin RG)
    ex = N.modus_ponens(wit, N.s5(cible, RG, "G"))   # (∃G)(...)
    return N.modus_ponens(ex, equivalence_arriere(car))          # ((RG,D),A)∈𝓕(D;A)


def triple_gauche_dans_applications(f="f", a="A", b="B", c="C"):
    """{ graphe_de(f)⊂(B⊔C)×A, dom graphe_de(f)=B⊔C } ⊢ ((f|B,B),A) ∈ 𝓕(B;A).

    1ʳᵉ composante de Φ(f) BIEN DÉFINIE : f|B∈A^B (incl bien-déf + func + dom), puis
    le triple ((f|B,B),A) est une application de B dans A."""
    vf, va, vb, vc = _t(f), _t(a), _t(b), _t(c)
    RG = restriction_gauche(vf, vb)
    in_exp = _restriction_dans_exposant(va, vb, RG,
        restriction_gauche_inclus(f, a, b, c),
        restriction_gauche_fonctionnelle(f, b),
        restriction_gauche_domaine(f, b))
    return _triple_dans_applications(va, vb, RG, in_exp)


def triple_droite_dans_applications(f="f", a="A", b="B", c="C"):
    """{ graphe_de(f)⊂(B⊔C)×A, dom graphe_de(f)=B⊔C } ⊢ ((f|C,C),A) ∈ 𝓕(C;A).

    2ᵈᵉ composante de Φ(f) bien définie (miroir gauche, D=C)."""
    vf, va, vb, vc = _t(f), _t(a), _t(b), _t(c)
    RD = restriction_droite(vf, vc)
    in_exp = _restriction_dans_exposant(va, vc, RD,
        restriction_droite_inclus(f, a, b, c),
        restriction_droite_fonctionnelle(f, c),
        restriction_droite_domaine(f, c))
    return _triple_dans_applications(va, vc, RD, in_exp)


def phi_dans_codomaine(f="f", a="A", b="B", c="C"):
    """{ graphe_de(f)⊂(B⊔C)×A, dom graphe_de(f)=B⊔C } ⊢ Φ(f) ∈ 𝓕(B;A)×𝓕(C;A).

    BIEN-DÉFINITION de Φ : le couple Φ(f)=(((f|B,B),A),((f|C,C),A)) est dans le
    produit 𝓕(B;A)×𝓕(C;A) (couple_dans_produit_ssi + les deux composantes)."""
    vf, va, vb, vc = _t(f), _t(a), _t(b), _t(c)
    TG = E.couple(E.couple(restriction_gauche(vf, vb), vb), va)   # ((f|B,B),A)
    TD = E.couple(E.couple(restriction_droite(vf, vc), vc), va)   # ((f|C,C),A)
    FB = E.applications(vb, va)                                   # 𝓕(B;A)
    FC = E.applications(vc, va)                                   # 𝓕(C;A)
    g_in = triple_gauche_dans_applications(f, a, b, c)            # TG∈𝓕(B;A)
    d_in = triple_droite_dans_applications(f, a, b, c)            # TD∈𝓕(C;A)
    return N.modus_ponens(conjonction_intro(g_in, d_in),
                          equivalence_arriere(_membre_produit(TG, TD, FB, FC)))


# ═══════════════════════════════════════════════════════════════════════════════
#  DÉCHARGE des hypothèses structurelles via  f ∈ 𝓕(B⊔C;A)  (le triple → graphe_de)
#   De f∈𝓕(B⊔C;A) on tire un témoin G avec f=((G,B⊔C),A) et G⊂(B⊔C)×A, dom G=B⊔C ;
#   graphe_de_triple + Leibniz donnent graphe_de(f)=G, d'où les deux faits sur
#   graphe_de(f) — exactement les hypothèses de phi_dans_codomaine.
# ═══════════════════════════════════════════════════════════════════════════════
def _hyp_incl_struct(vf, va, vb, vc):
    """La formule  graphe_de(f) ⊂ (B⊔C)×A."""
    BC = somme_disjointe(vb, vc)
    return inclus(graphe_de(vf), E.produit(BC, va))


def _hyp_dom_struct(vf, va, vb, vc):
    """La formule  dom(graphe_de(f)) = B⊔C."""
    BC = somme_disjointe(vb, vc)
    return egal(E.dom(graphe_de(vf)), BC)


def phi_dans_codomaine_sous_appartenance(f="f", a="A", b="B", c="C"):
    """{ f ∈ 𝓕(B⊔C;A) } ⊢ Φ(f) ∈ 𝓕(B;A)×𝓕(C;A).

    BIEN-DÉFINITION COMPLÈTE de Φ.  applications_somme_donne_graphe donne, sous
    f∈𝓕(B⊔C;A), un témoin G avec f=((G,B⊔C),A) et (G⊂(B⊔C)×A et G fonct et dom G=B⊔C).
    graphe_de_triple ⊢ graphe_de(((G,B⊔C),A))=G ; via f=((G,B⊔C),A) (Leibniz) on a
    graphe_de(f)=G, donc graphe_de(f)⊂(B⊔C)×A et dom graphe_de(f)=B⊔C — exactement
    les hypothèses de phi_dans_codomaine, qu'on décharge.  Témoin éliminé."""
    vf, va, vb, vc = _t(f), _t(a), _t(b), _t(c)
    BC = somme_disjointe(vb, vc)
    vG = var("G")
    triple = E.couple(E.couple(vG, BC), va)                # ((G,B⊔C),A)
    # corps de l'existentielle de applications_somme_donne_graphe
    corps_exp = et(et(inclus(vG, E.produit(BC, va)), E.est_fonctionnel(vG)),
                   egal(E.dom(vG), BC))
    body = et(egal(vf, triple), corps_exp)                 # f=((G,B⊔C),A) et corps_exp

    # sous le corps (témoin G) : décharger phi_dans_codomaine
    hb = N.assume(body)
    f_eq = conjonction_elim_gauche(hb)                     # f=((G,B⊔C),A)
    g_props = conjonction_elim_droite(hb)                  # corps_exp
    g_incl = conjonction_elim_gauche(conjonction_elim_gauche(g_props))  # G⊂(B⊔C)×A
    g_dom = conjonction_elim_droite(g_props)               # dom G=B⊔C
    # graphe_de(f) = G  :  graphe_de_triple ⊢ gr(((G,B⊔C),A))=G ; f=triple ⇒ gr(f)=gr(triple)
    gr_triple = graphe_de_triple(vG, BC, va)               # gr(((G,B⊔C),A))=G
    # gr(f)=gr(triple)  (congruence sous f=triple)
    gr_f_eq_gr_triple = N.modus_ponens(f_eq,
        congruence_terme(vf, triple, graphe_de(var("w"))))  # gr(f)=gr(triple)
    gr_f_eq_G = composer_egalites(gr_f_eq_gr_triple, gr_triple)   # gr(f)=G
    # transporter G⊂(B⊔C)×A → gr(f)⊂(B⊔C)×A,  dom G=B⊔C → dom gr(f)=B⊔C
    incl_grf = N.modus_ponens(g_incl, equivalence_arriere(N.modus_ponens(gr_f_eq_G,
        N.s6(graphe_de(vf), vG, "w", inclus(var("w"), E.produit(BC, va))))))  # gr(f)⊂(B⊔C)×A
    dom_grf = N.modus_ponens(g_dom, equivalence_arriere(N.modus_ponens(gr_f_eq_G,
        N.s6(graphe_de(vf), vG, "w", egal(E.dom(var("w")), BC)))))  # dom gr(f)=B⊔C
    # décharger les deux hypothèses de phi_dans_codomaine
    phi_in = phi_dans_codomaine(f, a, b, c)                # {gr(f)⊂..,dom gr(f)=..} ⊢ Φ(f)∈cod
    phi_in = _cut(phi_in, [
        (_hyp_incl_struct(vf, va, vb, vc), incl_grf),
        (_hyp_dom_struct(vf, va, vb, vc), dom_grf)])       # Φ(f)∈cod  [hyp body]
    # éliminer le témoin G
    inner = existe_elimination(N.loi_deduction(body, phi_in), "G")  # (∃G)body ⇒ Φ(f)∈cod
    # (∃G)body  vient de f∈𝓕(B⊔C;A) (applications_somme_donne_graphe)
    decomp = applications_somme_donne_graphe(a, b, c, f)   # f∈𝓕(B⊔C;A) ⇒ (∃G)body
    h_app = N.assume(appartient(vf, E.applications(BC, va)))
    ex_body = N.modus_ponens(h_app, decomp)               # (∃G)body  [hyp f∈𝓕]
    return N.modus_ponens(ex_body, inner)                 # Φ(f)∈cod   [hyp f∈𝓕(B⊔C;A)]


# ═══════════════════════════════════════════════════════════════════════════════
#  L'INJECTION  Φ : 𝓕(B⊔C;A) ↪ 𝓕(B;A)×𝓕(C;A)   (témoin W_Φ = graphe de Φ)
# ═══════════════════════════════════════════════════════════════════════════════
_POINT = "f"        # point courant du graphe-terme W_Φ  (≠ x,y internes, ≠ e,m,a,b)


def domaine_phi(a="A", b="B", c="C"):
    """𝓕(B⊔C; A)   (domaine / source de Φ)."""
    va, vb, vc = _t(a), _t(b), _t(c)
    return E.applications(somme_disjointe(vb, vc), va)


def codomaine_phi(a="A", b="B", c="C"):
    """𝓕(B;A) × 𝓕(C;A)   (codomaine / but de Φ)."""
    va, vb, vc = _t(a), _t(b), _t(c)
    return E.produit(E.applications(vb, va), E.applications(vc, va))


def W_phi(a="A", b="B", c="C"):
    """W_Φ := graphe_terme( 𝓕(B⊔C;A) , Φ(f) , « f » )   (le GRAPHE de Φ, terme)."""
    va, vb, vc = _t(a), _t(b), _t(c)
    return E.graphe_terme(domaine_phi(va, vb, vc),
                          phi_valeur(var(_POINT), va, vb, vc), _POINT)


def W_phi_fonctionnel(a="A", b="B", c="C"):
    """⊢ est_fonctionnel(W_Φ).   (graphe-terme toujours fonctionnel, C54.)"""
    va, vb, vc = _t(a), _t(b), _t(c)
    return graphe_terme_fonctionnel(domaine_phi(va, vb, vc),
                                    phi_valeur(var(_POINT), va, vb, vc), _POINT, "y")


def W_phi_domaine(a="A", b="B", c="C"):
    """⊢ dom(W_Φ) = 𝓕(B⊔C; A).   (Φ définie sur tout 𝓕(B⊔C;A).)"""
    va, vb, vc = _t(a), _t(b), _t(c)
    return graphe_terme_domaine(domaine_phi(va, vb, vc),
                                phi_valeur(var(_POINT), va, vb, vc), _POINT, "y", "z")


def W_phi_valeur(f="g", a="A", b="B", c="C"):
    """{f ∈ 𝓕(B⊔C;A)} ⊢ W_Φ(f) = Φ(f).   (point d'évaluation NOM ≠ f,x,y,e,m.)"""
    if not isinstance(f, str):
        raise ValueError("W_phi_valeur : point d'évaluation = NOM (string)")
    va, vb, vc = _t(a), _t(b), _t(c)
    return graphe_terme_valeur(domaine_phi(va, vb, vc),
                               phi_valeur(var(_POINT), va, vb, vc), f, _POINT, "y")


# ── CONJOINT image : image(W_Φ, 𝓕(B⊔C;A)) ⊂ 𝓕(B;A)×𝓕(C;A)  (BIEN-DÉFINITION) ──
def W_phi_image_incluse(a="A", b="B", c="C"):
    """⊢ image(W_Φ, 𝓕(B⊔C;A)) ⊂ 𝓕(B;A)×𝓕(C;A).

    z∈W_Φ⟨dom⟩ ⇔ (∃t)(t∈dom et (t,z)∈W_Φ).  Or (t,z)∈W_Φ ⇔ (t∈dom et z=Φ(t))
    (membre_graphe_terme), donc z=Φ(t) avec t∈dom ; phi_dans_codomaine_sous_
    appartenance ⊢ Φ(t)∈cod, d'où z∈cod (Leibniz).  Conclusion = inclusion."""
    va, vb, vc = _t(a), _t(b), _t(c)
    dom = domaine_phi(va, vb, vc)
    cod = codomaine_phi(va, vb, vc)
    W = W_phi(va, vb, vc)
    PHI = phi_valeur(var(_POINT), va, vb, vc)        # Φ(f), point f
    vz, vt = var("z"), var("t")
    from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import alpha_existe

    # z∈W⟨dom⟩ ⇔ (∃t)(t∈dom et (t,z)∈W)  (AXIOME_IMAGE ; le liant frais est α-renommé t)
    ax_img = N.axiome(E.theorie_ensembles(), E.AXIOME_IMAGE)
    img0 = instancie(instancie(instancie(ax_img, W), dom), vz)
    impl_LtoEX = img0.conclusion.sous[0].sous[0].sous[0]
    rhs_ex = impl_LtoEX.sous[1]
    assert rhs_ex.tag == "exists"
    nom = rhs_ex.lieur
    inner = et(appartient(var(nom), dom), appartient(E.couple(var(nom), vz), W))
    ren = alpha_existe(nom, "t", inner)
    img_car = equivalence_transitivite(img0, ren)    # z∈W⟨dom⟩ ⇔ (∃t)(t∈dom et (t,z)∈W)

    # (t,z)∈W ⇔ (t∈dom et z=Φ(t))   [membre_graphe_terme, point f, coords t,z]
    mem = membre_graphe_terme(dom, PHI, "t", "z", _POINT, "y")  # ((t,z)∈W)⇔(t∈dom et z=Φ[t])
    Phi_t = subst_t(vt, _POINT, PHI)                 # Φ(t) = Φ[f:=t]

    body = et(appartient(vt, dom), appartient(E.couple(vt, vz), W))
    hb = N.assume(body)
    t_in = conjonction_elim_gauche(hb)               # t∈dom
    tz_in = conjonction_elim_droite(hb)              # (t,z)∈W
    cond = N.modus_ponens(tz_in, equivalence_avant(mem))   # t∈dom et z=Φ(t)
    z_eq = conjonction_elim_droite(cond)             # z=Φ(t)
    # Φ(t)∈cod  (phi_dans_codomaine_sous_appartenance instancié en t ; hyp t∈dom déchargée)
    phi_t_in = _phi_cod_en_point(va, vb, vc, vt, t_in)   # Φ(t)∈cod
    # z∈cod  (z=Φ(t), Leibniz)
    z_in_cod = N.modus_ponens(phi_t_in, equivalence_arriere(N.modus_ponens(
        z_eq, N.s6(vz, Phi_t, "w", appartient(var("w"), cod)))))   # z∈cod
    ex_imp = existe_elimination(N.loi_deduction(body, z_in_cod), "t")  # (∃t)body ⇒ z∈cod
    h_z = N.assume(appartient(vz, E.image(W, dom)))
    ex = N.modus_ponens(h_z, equivalence_avant(img_car))   # (∃t)body
    z_in = N.modus_ponens(ex, ex_imp)                # z∈cod
    return N.generalisation("z", N.loi_deduction(appartient(vz, E.image(W, dom)), z_in))


def _phi_cod_en_point(va, vb, vc, vt, t_in_thm):
    """De {t∈dom} (t_in_thm) ⊢ Φ(t) ∈ cod, par instanciation-terme de
    phi_dans_codomaine_sous_appartenance au point t (hyp déchargée)."""
    dom = domaine_phi(va, vb, vc)
    cod = codomaine_phi(va, vb, vc)
    # généraliser sur le point « f » puis instancier à t (renommage déterministe)
    base = phi_dans_codomaine_sous_appartenance("f", va, vb, vc)  # {f∈dom} ⊢ Φ(f)∈cod
    base_imp = N.loi_deduction(appartient(var("f"), dom), base)   # f∈dom ⇒ Φ(f)∈cod
    gen = N.generalisation("f", base_imp)            # (∀f)(f∈dom ⇒ Φ(f)∈cod)
    inst = instancie(gen, vt)                        # t∈dom ⇒ Φ(t)∈cod
    return N.modus_ponens(t_in_thm, inst)            # Φ(t)∈cod   [hyp t∈dom]


# ═══════════════════════════════════════════════════════════════════════════════
#  INJECTIVITÉ de Φ  :  W(f₁)=W(f₂) ⇒ f₁=f₂.   Cœur back-and-forth (extensionnalité).
# ───────────────────────────────────────────────────────────────────────────────
#   Étapes :  W(fᵢ)=Φ(fᵢ) (W_phi_valeur) ⇒ Φ(f₁)=Φ(f₂) ⇒ (couples) f₁|B=f₂|B et
#   f₁|C=f₂|C ⇒ (graphe_terme_valeur) valeurs de graphe_de(fᵢ) coïncident sur (u,0)
#   et (v,1), donc sur tout B⊔C (cas-analyse somme) ⇒ (graphe_egal_par_valeurs)
#   graphe_de(f₁)=graphe_de(f₂) ⇒ (triple) f₁=f₂.
# ═══════════════════════════════════════════════════════════════════════════════
def _valeur_rebind_m_y(vG, vx):
    """⊢ valeur(G, x, « m ») = valeur(G, x, « y »).   (α-renommage du liant τ, CS1.)

    valeur(G,x,b) = τb((x,b)∈G).  alpha_tau(r, "m", "y") avec r=((x,m)∈G) renomme le
    liant m→y : τm((x,m)∈G) = τy((x,y)∈G).  Primitive saine (mêmes développements-τ)."""
    r = appartient(E.couple(vx, var("m")), vG)       # (x,m)∈G  (liant courant m)
    return N.alpha_tau(r, "m", "y")                  # valeur(G,x,m) = valeur(G,x,y)


def _restriction_valeurs_coincident(va, vb, T1, T2, RG1, RG2, u_nom):
    """{ RG1 = RG2,  u∈B } ⊢ T1[u] = T2[u]  (u_nom : NOM du point d'évaluation),
       RGᵢ = graphe_terme(B, Tᵢ), Tᵢ[u] = valeur de graphe_de(fᵢ) en (u,0) (resp (u,1)).

    graphe_terme_valeur : RGᵢ(u)=Tᵢ[u] sous u∈B ; RG1=RG2 ⇒ RG1(u)=RG2(u)
    (congruence) ; chaîner T1[u]=RG1(u)=RG2(u)=T2[u].  u_nom doit être une STRING
    (le point d'évaluation de membre_graphe_terme doit être un NOM, pas un terme)."""
    vu = var(u_nom)
    T1u = subst_t(vu, _PT, T1)                       # T1[u]
    T2u = subst_t(vu, _PT, T2)                       # T2[u]
    val1 = graphe_terme_valeur(vb, T1, u_nom, _PT, "y")  # {u∈B} ⊢ RG1(u)=T1[u]
    val2 = graphe_terme_valeur(vb, T2, u_nom, _PT, "y")  # {u∈B} ⊢ RG2(u)=T2[u]
    h_eq = N.assume(egal(RG1, RG2))                  # RG1=RG2
    # RG1(u)=RG2(u)  (congruence du terme valeur(·,u,"y") le long de RG1=RG2)
    RG1u_eq_RG2u = N.modus_ponens(h_eq,
        congruence_terme(RG1, RG2, E.valeur(var("w"), vu, "y")))   # RG1(u)=RG2(u)
    # T1[u]=RG1(u)  (symétrie de val1)
    T1u_eq_RG1u = N.modus_ponens(val1, symetrie(E.valeur(RG1, vu, "y"), T1u))  # T1[u]=RG1(u)
    # T1[u]=RG1(u)=RG2(u)=T2[u]
    return composer_egalites(composer_egalites(T1u_eq_RG1u, RG1u_eq_RG2u), val2)


# ── Φ(f₁)=Φ(f₂)  ⟹  RG₁=RG₂  et  RD₁=RD₂  (décomposition couple + triple) ──────
def _strip_triple(triple_eq, g1, mid, top, g2):
    """De ⊢ ((g₁,mid),top)=((g₂,mid),top), tire ⊢ g₁=g₂.  (deux décompos de couples.)"""
    from bourbaki.ii_theorie_des_ensembles.ii_2_couples.ii_2_1_definition_couples.ensembles_couples import couple_egal_implique_composantes
    inner1 = E.couple(g1, mid)
    inner2 = E.couple(g2, mid)
    comp1 = N.modus_ponens(triple_eq,
                           couple_egal_implique_composantes(inner1, top, inner2, top))
    inner_eq = conjonction_elim_gauche(comp1)        # (g₁,mid)=(g₂,mid)
    comp2 = N.modus_ponens(inner_eq,
                           couple_egal_implique_composantes(g1, mid, g2, mid))
    return conjonction_elim_gauche(comp2)            # g₁=g₂


def _phi_egal_donne_restrictions(vf1, vf2, va, vb, vc):
    """{Φ(f₁)=Φ(f₂)} ⊢ (RG₁=RG₂ et RD₁=RD₂).

    Φ(fᵢ)=(((fᵢ|B,B),A),((fᵢ|C,C),A)) ; couple_egal_implique_composantes (3×) extrait
    f₁|B=f₂|B et f₁|C=f₂|C."""
    from bourbaki.ii_theorie_des_ensembles.ii_2_couples.ii_2_1_definition_couples.ensembles_couples import couple_egal_implique_composantes
    RG1, RG2 = restriction_gauche(vf1, vb), restriction_gauche(vf2, vb)
    RD1, RD2 = restriction_droite(vf1, vc), restriction_droite(vf2, vc)
    TG1 = E.couple(E.couple(RG1, vb), va)
    TD1 = E.couple(E.couple(RD1, vc), va)
    TG2 = E.couple(E.couple(RG2, vb), va)
    TD2 = E.couple(E.couple(RD2, vc), va)
    phi1 = phi_valeur(vf1, va, vb, vc)
    phi2 = phi_valeur(vf2, va, vb, vc)
    h = N.assume(egal(phi1, phi2))                   # Φ(f₁)=Φ(f₂)
    comp_ext = N.modus_ponens(h,
        couple_egal_implique_composantes(TG1, TD1, TG2, TD2))
    TG_eq = conjonction_elim_gauche(comp_ext)        # TG₁=TG₂
    TD_eq = conjonction_elim_droite(comp_ext)        # TD₁=TD₂
    rg_eq = _strip_triple(TG_eq, RG1, vb, va, RG2)   # RG₁=RG₂
    rd_eq = _strip_triple(TD_eq, RD1, vc, va, RD2)   # RD₁=RD₂
    return conjonction_intro(rg_eq, rd_eq)


# ── valeur(G₁,x,«y») = valeur(G₂,x,«y») pour x = (u,marker), depuis RGᵢ coincidence ──
def _val_egal_en_copie(vf1, vf2, va, vD, T1, T2, RG1, RG2, marker, u_nom, vw):
    """{ RG₁=RG₂, u∈D, x=(u,marker) } ⊢ G₁(x) = G₂(x)   (binder « y », Gᵢ=graphe_de(fᵢ)).

    De _restriction_valeurs_coincident : G₁((u,marker))=G₂((u,marker)) (binder m).
    Rebind m→y (alpha_tau) des deux côtés ; Leibniz x=(u,marker) transporte au point x.
    vw = var(x) (le point courant de la somme, libre)."""
    vu = var(u_nom)
    G1, G2 = graphe_de(vf1), graphe_de(vf2)
    um = E.couple(vu, marker)                         # (u,marker)
    # G_i((u,marker)) en binder m  (= Tᵢ[u])
    coinc_m = _restriction_valeurs_coincident(va, vD, T1, T2, RG1, RG2, u_nom)
    # coinc_m : {RG₁=RG₂, u∈D} ⊢ valeur(G₁,(u,m),m)=valeur(G₂,(u,m),m)
    # rebind chaque côté m→y
    reb1 = _valeur_rebind_m_y(G1, um)                 # G₁((u,m))[m]=G₁((u,m))[y]
    reb2 = _valeur_rebind_m_y(G2, um)                 # G₂((u,m))[m]=G₂((u,m))[y]
    # G₁((u,m))[y] = G₁((u,m))[m] = G₂((u,m))[m] = G₂((u,m))[y]
    y1_eq_m1 = N.modus_ponens(reb1, symetrie(E.valeur(G1, um, "m"), E.valeur(G1, um, "y")))
    chain = composer_egalites(composer_egalites(y1_eq_m1, coinc_m), reb2)  # G₁((u,m))[y]=G₂((u,m))[y]
    # Leibniz : x=(u,marker) ⇒ G₁(x)[y]=G₂(x)[y]  (réécrire (u,marker)→x des deux côtés)
    h_x_eq = N.assume(egal(vw, um))                  # x=(u,marker)
    # G₁((u,m))[y] = G₁(x)[y]  via x=(u,m) (congruence valeur(G₁,·,y))
    g1_um_eq_x = N.modus_ponens(h_x_eq,
        congruence_terme(vw, um, E.valeur(G1, var("@h"), "y"), "@h"))  # G₁(x)[y]=G₁((u,m))[y]
    g2_um_eq_x = N.modus_ponens(h_x_eq,
        congruence_terme(vw, um, E.valeur(G2, var("@h"), "y"), "@h"))  # G₂(x)[y]=G₂((u,m))[y]
    # G₁(x)[y] = G₁((u,m))[y] = G₂((u,m))[y] = G₂((u,m))[y]→G₂(x)[y]
    g2x_eq = N.modus_ponens(g2_um_eq_x, symetrie(E.valeur(G2, vw, "y"), E.valeur(G2, um, "y")))
    return composer_egalites(composer_egalites(g1_um_eq_x, chain), g2x_eq)  # G₁(x)[y]=G₂(x)[y]


def _valeurs_coincident_sur_somme(vf1, vf2, va, vb, vc):
    """{ RG₁=RG₂, RD₁=RD₂ } ⊢ (∀x)(x∈B⊔C ⇒ G₁(x)=G₂(x))   (binder « y », Gᵢ=graphe_de(fᵢ)).

    Cas-analyse de membre_somme_caracterise : tout x∈B⊔C est (u,0) (u∈B) ou (v,1)
    (v∈C) ; _val_egal_en_copie donne l'égalité des valeurs dans chaque copie."""
    G1, G2 = graphe_de(vf1), graphe_de(vf2)
    BC = somme_disjointe(vb, vc)
    vx = var("x")
    TG1, TG2 = _val_g(vf1), _val_g(vf2)
    TD1, TD2 = _val_d(vf1), _val_d(vf2)
    RG1, RG2 = restriction_gauche(vf1, vb), restriction_gauche(vf2, vb)
    RD1, RD2 = restriction_droite(vf1, vc), restriction_droite(vf2, vc)
    val_eq = egal(E.valeur(G1, vx, "y"), E.valeur(G2, vx, "y"))   # cible G₁(x)=G₂(x)

    from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import alpha_existe
    from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_recollement_somme.ensembles_somme_disjointe import _ou_congruence
    car0 = membre_somme_caracterise(vb, vc, vx)  # x∈B⊔C ⇔ ((∃u)(u∈B et x=(u,0)) ou (∃v)(v∈C et x=(v,1)))
    # α-renommer les DEUX liants : GAUCHE « u »→« s », DROIT « v »→« t » (points sûrs,
    # ≠ liants internes de graphe_terme_valeur ET ≠ variables-fonction u,up de l'appelant)
    bodyU_u = et(appartient(var("u"), vb), egal(vx, E.couple(var("u"), ZERO)))
    bodyV_v = et(appartient(var("v"), vc), egal(vx, E.couple(var("v"), UN)))
    renU = alpha_existe("u", "s", bodyU_u)           # (∃u)bodyU ⇔ (∃s)bodyS
    renV = alpha_existe("v", "t", bodyV_v)           # (∃v)bodyV ⇔ (∃t)bodyT
    car = equivalence_transitivite(car0, _ou_congruence(renU, renV))
    bodyS = et(appartient(var("s"), vb), egal(vx, E.couple(var("s"), ZERO)))
    bodyT = et(appartient(var("t"), vc), egal(vx, E.couple(var("t"), UN)))
    # branche GAUCHE (binder « s ») : (∃s)(s∈B et x=(s,0)) ⇒ G₁(x)=G₂(x)
    hU = N.assume(bodyS)
    uB = conjonction_elim_gauche(hU)                 # s∈B
    x_eq_u0 = conjonction_elim_droite(hU)            # x=(s,0)
    velc = _val_egal_en_copie(vf1, vf2, va, vb, TG1, TG2, RG1, RG2, ZERO, "s", vx)
    velc = _cut(velc, [(egal(vx, E.couple(var("s"), ZERO)), x_eq_u0),
                       (appartient(var("s"), vb), uB)])           # {RG₁=RG₂} ⊢ val_eq  [bodyS]
    brU = existe_elimination(N.loi_deduction(bodyS, velc), "s")   # (∃s)bodyS ⇒ val_eq
    # branche DROITE (binder « t ») : (∃t)(t∈C et x=(t,1)) ⇒ G₁(x)=G₂(x)
    hV = N.assume(bodyT)
    vC = conjonction_elim_gauche(hV)                 # t∈C
    x_eq_v1 = conjonction_elim_droite(hV)            # x=(t,1)
    velcd = _val_egal_en_copie(vf1, vf2, va, vc, TD1, TD2, RD1, RD2, UN, "t", vx)
    velcd = _cut(velcd, [(egal(vx, E.couple(var("t"), UN)), x_eq_v1),
                         (appartient(var("t"), vc), vC)])         # {RD₁=RD₂} ⊢ val_eq  [bodyT]
    brV = existe_elimination(N.loi_deduction(bodyT, velcd), "t")  # (∃t)bodyT ⇒ val_eq
    # disjonction ⇒ val_eq
    disj = ou(existe("s", bodyS), existe("t", bodyT))
    hd = N.assume(disj)
    val = cas(hd, brU, brV)                          # val_eq  [hyp disj, RG/RD eqs]
    disj_imp = N.loi_deduction(disj, val)            # disj ⇒ val_eq
    # x∈B⊔C ⇒ val_eq  (via car)
    h_x = N.assume(appartient(vx, BC))
    d = N.modus_ponens(h_x, equivalence_avant(car))  # disj
    val_x = N.modus_ponens(d, disj_imp)              # val_eq  [hyp x∈B⊔C, RG/RD eqs]
    return N.generalisation("x", N.loi_deduction(appartient(vx, BC), val_x))


# ── G ⊂ E×F  ⟹  est_un_graphe(G)  (tout élément d'un produit est un couple) ─────
def _inclus_produit_est_graphe(vG, vE, vF):
    """{ G ⊂ E×F } ⊢ est_un_graphe(G).   (z∈G ⇒ z∈E×F ⇒ z=(p,q) couple.)"""
    from bourbaki.ii_theorie_des_ensembles.ii_2_couples.ii_2_2_produit_deux_ensembles.ensembles_produit import _instance_produit
    vz = var("z")
    h_incl = N.assume(inclus(vG, E.produit(vE, vF)))   # G⊂E×F = (∀z)(z∈G⇒z∈E×F)
    z_in_prod_imp = instancie(h_incl, vz)              # z∈G ⇒ z∈E×F
    # z∈E×F ⇒ (∃p)(∃q)(z=(p,q) et p∈E et q∈F)  (AXIOME_PRODUIT)
    car = _instance_produit(vE, vF, vz)                # z∈E×F ⇔ (∃p)(∃q)(z=(p,q) et …)
    body = et(et(egal(vz, E.couple(var("p"), var("q"))), appartient(var("p"), vE)),
              appartient(var("q"), vF))
    hb = N.assume(body)
    z_pq = conjonction_elim_gauche(conjonction_elim_gauche(hb))   # z=(p,q)
    # z=(p,q) ⇒ (∃x)(∃y)(z=(x,y)) = est_un_couple(z)  (witness x:=p, y:=q ; binders x,y)
    inner_xy = egal(vz, E.couple(var("x"), var("y")))            # z=(x,y)
    body_py = subst_f(var("p"), "x", inner_xy)                   # (p|x)(z=(x,y)) = z=(p,y)
    ex_y = N.modus_ponens(z_pq, N.s5(body_py, var("q"), "y"))    # (∃y)(z=(p,y))
    ex_xy = N.modus_ponens(ex_y, N.s5(existe("y", inner_xy), var("p"), "x"))  # (∃x)(∃y)(z=(x,y))
    couple_z = existe_elimination(existe_elimination(
        N.loi_deduction(body, ex_xy), "q"), "p")       # (∃p)(∃q)(z=(p,q) et…) ⇒ est_un_couple(z)
    z_in = N.assume(appartient(vz, vG))
    in_prod = N.modus_ponens(z_in, z_in_prod_imp)      # z∈E×F
    ex_body = N.modus_ponens(in_prod, equivalence_avant(car))  # (∃p)(∃q)(z=(p,q) et…)
    couple = N.modus_ponens(ex_body, couple_z)         # est_un_couple(z)
    return N.generalisation("z", N.loi_deduction(appartient(vz, vG), couple))  # est_un_graphe(G)


def _graphe_de_proprietes(vf, va, vb, vc):
    """{ f ∈ 𝓕(B⊔C;A) } ⊢ ( est_fonctionnel(gr(f)) et est_un_graphe(gr(f))
                            et dom gr(f) = B⊔C ),   gr(f)=graphe_de(f).

    De applications_somme_donne_graphe : témoin G avec f=((G,B⊔C),A) et G⊂(B⊔C)×A,
    G fonctionnel, dom G=B⊔C ; graphe_de_triple + Leibniz ⇒ gr(f)=G ; on transporte
    les trois propriétés (est_un_graphe via _inclus_produit_est_graphe sous G⊂…)."""
    BC = somme_disjointe(vb, vc)
    vG = var("G")
    triple = E.couple(E.couple(vG, BC), va)
    corps_exp = et(et(inclus(vG, E.produit(BC, va)), E.est_fonctionnel(vG)),
                   egal(E.dom(vG), BC))
    body = et(egal(vf, triple), corps_exp)
    grf = graphe_de(vf)
    cible = et(et(E.est_fonctionnel(grf), E.est_un_graphe(grf)), egal(E.dom(grf), BC))

    hb = N.assume(body)
    f_eq = conjonction_elim_gauche(hb)
    g_props = conjonction_elim_droite(hb)
    g_incl = conjonction_elim_gauche(conjonction_elim_gauche(g_props))  # G⊂(B⊔C)×A
    g_func = conjonction_elim_droite(conjonction_elim_gauche(g_props))  # G fonctionnel
    g_dom = conjonction_elim_droite(g_props)                            # dom G=B⊔C
    # gr(f)=G
    gr_triple = graphe_de_triple(vG, BC, va)
    gr_f_eq_gr_triple = N.modus_ponens(f_eq, congruence_terme(vf, triple, graphe_de(var("w"))))
    gr_f_eq_G = composer_egalites(gr_f_eq_gr_triple, gr_triple)         # gr(f)=G
    # est_un_graphe(G)  (sous G⊂(B⊔C)×A), puis transporter à gr(f)
    g_graphe = _cut(_inclus_produit_est_graphe(vG, BC, va),
                    [(inclus(vG, E.produit(BC, va)), g_incl)])          # est_un_graphe(G)
    # transporter func, graphe, dom de G à gr(f)  (gr(f)=G, Leibniz)
    func_grf = N.modus_ponens(g_func, equivalence_arriere(N.modus_ponens(gr_f_eq_G,
        N.s6(grf, vG, "w", E.est_fonctionnel(var("w"))))))             # gr(f) fonctionnel
    graphe_grf = N.modus_ponens(g_graphe, equivalence_arriere(N.modus_ponens(gr_f_eq_G,
        N.s6(grf, vG, "w", E.est_un_graphe(var("w"))))))              # gr(f) graphe
    dom_grf = N.modus_ponens(g_dom, equivalence_arriere(N.modus_ponens(gr_f_eq_G,
        N.s6(grf, vG, "w", egal(E.dom(var("w")), BC)))))             # dom gr(f)=B⊔C
    concl = conjonction_intro(conjonction_intro(func_grf, graphe_grf), dom_grf)
    inner = existe_elimination(N.loi_deduction(body, concl), "G")     # (∃G)body ⇒ cible
    decomp = applications_somme_donne_graphe(va, vb, vc, vf)
    h_app = N.assume(appartient(vf, E.applications(BC, va)))
    ex_body = N.modus_ponens(h_app, decomp)                          # (∃G)body
    return N.modus_ponens(ex_body, inner)                           # cible  [f∈𝓕(B⊔C;A)]


def _f_egal_triple_graphe_de(vf, va, vb, vc):
    """{ f ∈ 𝓕(B⊔C;A) } ⊢ f = ((graphe_de(f), B⊔C), A).

    De applications_somme_donne_graphe : f=((G,B⊔C),A) ; graphe_de(f)=G
    (graphe_de_triple) ; congruence ⇒ ((graphe_de(f),B⊔C),A)=((G,B⊔C),A)=f."""
    BC = somme_disjointe(vb, vc)
    vG = var("G")
    triple = E.couple(E.couple(vG, BC), va)              # ((G,B⊔C),A)
    triple_gr = E.couple(E.couple(graphe_de(vf), BC), va)  # ((gr(f),B⊔C),A)
    corps_exp = et(et(inclus(vG, E.produit(BC, va)), E.est_fonctionnel(vG)),
                   egal(E.dom(vG), BC))
    body = et(egal(vf, triple), corps_exp)
    cible = egal(vf, triple_gr)

    hb = N.assume(body)
    f_eq = conjonction_elim_gauche(hb)                   # f=((G,B⊔C),A)
    gr_triple = graphe_de_triple(vG, BC, va)             # gr(((G,B⊔C),A))=G
    gr_f_eq_gr_triple = N.modus_ponens(f_eq, congruence_terme(vf, triple, graphe_de(var("w"))))
    gr_f_eq_G = composer_egalites(gr_f_eq_gr_triple, gr_triple)   # gr(f)=G
    # ((gr(f),B⊔C),A) = ((G,B⊔C),A)  (congruence du triple le long de gr(f)=G)
    triple_eq = N.modus_ponens(gr_f_eq_G,
        congruence_terme(graphe_de(vf), vG, E.couple(E.couple(var("w"), BC), va)))  # triple_gr=triple_G
    # f = ((G,B⊔C),A) = ((gr(f),B⊔C),A)
    triple_eq_sym = N.modus_ponens(triple_eq, symetrie(triple_gr, triple))   # triple=triple_gr
    f_eq_triple_gr = composer_egalites(f_eq, triple_eq_sym)   # f=((gr(f),B⊔C),A)
    inner = existe_elimination(N.loi_deduction(body, f_eq_triple_gr), "G")
    decomp = applications_somme_donne_graphe(va, vb, vc, vf)
    h_app = N.assume(appartient(vf, E.applications(BC, va)))
    ex_body = N.modus_ponens(h_app, decomp)
    return N.modus_ponens(ex_body, inner)               # f=((gr(f),B⊔C),A)  [f∈𝓕]


def _graphe_de_egal(vf1, vf2, va, vb, vc):
    """{ f₁∈𝓕(B⊔C;A), f₂∈𝓕(B⊔C;A), Φ(f₁)=Φ(f₂) } ⊢ graphe_de(f₁) = graphe_de(f₂).

    EXTENSIONNALITÉ FONCTIONNELLE.  Φ(f₁)=Φ(f₂) ⇒ RGᵢ et RDᵢ coïncident
    (_phi_egal_donne_restrictions) ⇒ valeurs de Gᵢ coïncident sur B⊔C
    (_valeurs_coincident_sur_somme) ; Gᵢ fonctionnel/graphe, dom Gᵢ=B⊔C
    (_graphe_de_proprietes) ; graphe_egal_par_valeurs conclut G₁=G₂."""
    from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_4_fonctions.ensembles_extensionnalite import graphe_egal_par_valeurs
    G1, G2 = graphe_de(vf1), graphe_de(vf2)
    BC = somme_disjointe(vb, vc)
    # RG/RD coïncident, puis valeurs coïncident sur B⊔C
    restr = _phi_egal_donne_restrictions(vf1, vf2, va, vb, vc)    # {Φ eq} ⊢ RG eq et RD eq
    RG_eq = conjonction_elim_gauche(restr)
    RD_eq = conjonction_elim_droite(restr)
    vals = _valeurs_coincident_sur_somme(vf1, vf2, va, vb, vc)    # {RG eq,RD eq} ⊢ (∀x)(x∈B⊔C⇒G₁(x)=G₂(x))
    vals = _cut(vals, [(RG_eq.conclusion, RG_eq), (RD_eq.conclusion, RD_eq)])  # {Φ eq} ⊢ vals
    # propriétés des graphes  (sous fᵢ∈𝓕)
    p1 = _graphe_de_proprietes(vf1, va, vb, vc)   # {f₁∈𝓕} ⊢ G₁ func et G₁ graphe et dom G₁=B⊔C
    p2 = _graphe_de_proprietes(vf2, va, vb, vc)
    f1_func = conjonction_elim_gauche(conjonction_elim_gauche(p1))
    f1_graphe = conjonction_elim_droite(conjonction_elim_gauche(p1))
    f1_dom = conjonction_elim_droite(p1)          # dom G₁=B⊔C
    f2_func = conjonction_elim_gauche(conjonction_elim_gauche(p2))
    f2_graphe = conjonction_elim_droite(conjonction_elim_gauche(p2))
    f2_dom = conjonction_elim_droite(p2)          # dom G₂=B⊔C
    # dom G₁=dom G₂  : dom G₁=B⊔C=dom G₂
    dom_eq = composer_egalites(f1_dom, N.modus_ponens(f2_dom, symetrie(E.dom(G2), BC)))  # dom G₁=dom G₂
    # (∀x)(x∈dom G₁ ⇒ G₁(x)=G₂(x))  : réécrire dom G₁=B⊔C dans vals
    vals_dom = _vals_reindex_dom(G1, G2, BC, vals, f1_dom)   # (∀x)(x∈dom G₁⇒G₁(x)=G₂(x))
    # graphe_egal_par_valeurs(G₁,G₂) : grande conjonction ⇒ G₁=G₂
    geq = graphe_egal_par_valeurs(G1, G2)
    hyp_conj = et(et(et(et(et(
        E.est_fonctionnel(G1), E.est_fonctionnel(G2)),
        E.est_un_graphe(G1)), E.est_un_graphe(G2)),
        egal(E.dom(G1), E.dom(G2))),
        _egalite_valeurs(G1, G2))
    conj = conjonction_intro(conjonction_intro(conjonction_intro(conjonction_intro(conjonction_intro(
        f1_func, f2_func), f1_graphe), f2_graphe), dom_eq), vals_dom)
    assert conj.conclusion == hyp_conj, "conjonction hypothèses ≠ attendu graphe_egal_par_valeurs"
    return N.modus_ponens(conj, geq)              # G₁=G₂


def _egalite_valeurs(vf, vg, x="x"):
    """(∀x)(x∈dom F ⇒ F(x)=G(x))  — réexposé de extensionnalite.egalite_valeurs."""
    from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_4_fonctions.ensembles_extensionnalite import egalite_valeurs
    return egalite_valeurs(vf, vg, x)


def _vals_reindex_dom(G1, G2, BC, vals_thm, dom1_eq):
    """De {Γ}⊢(∀x)(x∈B⊔C⇒G₁(x)=G₂(x)) et dom G₁=B⊔C, déduire
       {Γ}⊢(∀x)(x∈dom G₁⇒G₁(x)=G₂(x))   (réécriture dom G₁ ⇒ B⊔C)."""
    vx = var("x")
    hx = N.assume(appartient(vx, E.dom(G1)))      # x∈dom G₁
    # dom G₁=B⊔C ⇒ (x∈dom G₁ ⇔ x∈B⊔C)
    x_in_BC = N.modus_ponens(hx, equivalence_avant(N.modus_ponens(dom1_eq,
        N.s6(E.dom(G1), BC, "w", appartient(vx, var("w"))))))   # x∈B⊔C
    val_x = N.modus_ponens(x_in_BC, instancie(vals_thm, vx))    # G₁(x)=G₂(x)
    return N.generalisation("x", N.loi_deduction(appartient(vx, E.dom(G1)), val_x))


def phi_injective_sous_appartenance(f1="f1", f2="f2", a="A", b="B", c="C"):
    """{ f₁∈𝓕(B⊔C;A), f₂∈𝓕(B⊔C;A), Φ(f₁)=Φ(f₂) } ⊢ f₁ = f₂.

    INJECTIVITÉ de Φ (cœur).  graphe_de(f₁)=graphe_de(f₂) (_graphe_de_egal, extensionnalité)
    et fᵢ=((graphe_de(fᵢ),B⊔C),A) (_f_egal_triple_graphe_de) ⇒ f₁=((gr(f₁),B⊔C),A)=
    ((gr(f₂),B⊔C),A)=f₂  (congruence + transitivité)."""
    vf1, vf2, va, vb, vc = _t(f1), _t(f2), _t(a), _t(b), _t(c)
    BC = somme_disjointe(vb, vc)
    gr_eq = _graphe_de_egal(vf1, vf2, va, vb, vc)        # gr(f₁)=gr(f₂)
    f1_tr = _f_egal_triple_graphe_de(vf1, va, vb, vc)    # f₁=((gr(f₁),B⊔C),A)
    f2_tr = _f_egal_triple_graphe_de(vf2, va, vb, vc)    # f₂=((gr(f₂),B⊔C),A)
    # ((gr(f₁),B⊔C),A) = ((gr(f₂),B⊔C),A)  (congruence du triple le long de gr(f₁)=gr(f₂))
    tr1 = E.couple(E.couple(graphe_de(vf1), BC), va)
    tr2 = E.couple(E.couple(graphe_de(vf2), BC), va)
    tr_eq = N.modus_ponens(gr_eq,
        congruence_terme(graphe_de(vf1), graphe_de(vf2),
                         E.couple(E.couple(var("w"), BC), va)))   # tr₁=tr₂
    # f₁ = tr₁ = tr₂ = f₂
    f2_from_tr2 = N.modus_ponens(f2_tr, symetrie(vf2, tr2))       # tr₂=f₂
    return composer_egalites(composer_egalites(f1_tr, tr_eq), f2_from_tr2)  # f₁=f₂


def W_phi_injective(a="A", b="B", c="C"):
    """⊢ injective_dans(W_Φ, 𝓕(B⊔C;A)).

    (∀u)(∀u')((u∈dom et u'∈dom et W(u)=W(u')) ⇒ u=u').  W(·)=Φ(·) (W_phi_valeur, sous
    ·∈dom) ⇒ Φ(f₁)=Φ(f₂) ; phi_injective_sous_appartenance ⇒ f₁=f₂.

    NB liants : les variables-fonction sont nommées « f1 », « f2 » (et NON « u »,
    « u' », qui collisionnent avec les liants INTERNES u,v,z de la machinerie
    graphe_terme_valeur quand la fonction est elle-même substituée dans une valeur).
    On α-renomme ENSUITE le double ∀ « f1,f2 » → « u,u' » pour s'apparier exactement à
    la forme `injective_dans` (binders u, up) attendue par est_injection_de."""
    va, vb, vc = _t(a), _t(b), _t(c)
    dom = domaine_phi(va, vb, vc)
    Wt = W_phi(va, vb, vc)
    vf1, vf2 = var("f1"), var("f2")                        # variables-fonction SÛRES
    phi1 = phi_valeur(vf1, va, vb, vc)
    phi2 = phi_valeur(vf2, va, vb, vc)

    hyp = et(et(appartient(vf1, dom), appartient(vf2, dom)),
             egal(E.valeur(Wt, vf1), E.valeur(Wt, vf2)))   # f₁∈dom et f₂∈dom et W(f₁)=W(f₂)
    h = N.assume(hyp)
    f1_in = conjonction_elim_gauche(conjonction_elim_gauche(h))
    f2_in = conjonction_elim_droite(conjonction_elim_gauche(h))
    W_eq = conjonction_elim_droite(h)                            # W(f₁)=W(f₂)
    Wf1 = _cut(W_phi_valeur("f1", va, vb, vc), [(appartient(vf1, dom), f1_in)])    # W(f₁)=Φ(f₁)
    Wf2 = _cut(W_phi_valeur("f2", va, vb, vc), [(appartient(vf2, dom), f2_in)])    # W(f₂)=Φ(f₂)
    phi_eq = composer_egalites(composer_egalites(
        N.modus_ponens(Wf1, symetrie(E.valeur(Wt, vf1), phi1)), W_eq), Wf2)   # Φ(f₁)=Φ(f₂)
    f_eq = phi_injective_sous_appartenance("f1", "f2", va, vb, vc)
    f_eq = _cut(f_eq, [(appartient(vf1, dom), f1_in),
                       (appartient(vf2, dom), f2_in),
                       (egal(phi1, phi2), phi_eq)])             # f₁=f₂  [hyp]
    inner = N.loi_deduction(hyp, f_eq)
    raw = N.generalisation("f1", N.generalisation("f2", inner))  # (∀f1)(∀f2)…
    # α-renommer (∀f1)(∀f2)P → (∀u)(∀up)P  par instanciation puis re-généralisation
    inst = instancie(instancie(raw, var("u")), var("up"))        # P[f1:=u, f2:=up]
    return N.generalisation("u", N.generalisation("up", inst))   # (∀u)(∀up)… = injective_dans


# ═══════════════════════════════════════════════════════════════════════════════
#  DIRECTION A :  𝓕(B⊔C;A) ≤ 𝓕(B;A)×𝓕(C;A)   (Φ est une injection)
# ═══════════════════════════════════════════════════════════════════════════════
def W_phi_est_injection(a="A", b="B", c="C"):
    """⊢ est_injection_de(W_Φ, 𝓕(B⊔C;A), 𝓕(B;A)×𝓕(C;A)).

    Les QUATRE conjoints (E.III.3.2) : W_Φ fonctionnel, dom W_Φ=𝓕(B⊔C;A), injective
    sur 𝓕(B⊔C;A), image⊂𝓕(B;A)×𝓕(C;A).  Tous CLOS (graphe de Φ via le pont graphe_de)."""
    va, vb, vc = _t(a), _t(b), _t(c)
    return conjonction_intro(conjonction_intro(conjonction_intro(
        W_phi_fonctionnel(va, vb, vc), W_phi_domaine(va, vb, vc)),
        W_phi_injective(va, vb, vc)), W_phi_image_incluse(va, vb, vc))


# (direction A de la clôture Cantor-Bernstein du Cor.1 : a^(b+c) <= a^b·a^c.)
# @livre Ch.III §3.5 Demo.- | E III.28 L.31-33 | PDF p.131
def inf_egal_phi(a="A", b="B", c="C"):
    """⊢ inf_egal_card(𝓕(B⊔C;A), 𝓕(B;A)×𝓕(C;A)).   (= « 𝓕(B⊔C;A) ≤ 𝓕(B;A)×𝓕(C;A) ».)

    L'injection-témoin est W_Φ (W_phi_est_injection) : par S5 (témoin F:=W_Φ),
    (∃F) est_injection_de(F, 𝓕(B⊔C;A), 𝓕(B;A)×𝓕(C;A)) = inf_egal_card(·,·)."""
    va, vb, vc = _t(a), _t(b), _t(c)
    dom = domaine_phi(va, vb, vc)
    cod = codomaine_phi(va, vb, vc)
    Wt = W_phi(va, vb, vc)
    inj = W_phi_est_injection(va, vb, vc)            # est_injection_de(W_Φ, dom, cod)
    return N.modus_ponens(inj, N.s5(est_injection_de(var("F"), dom, cod), Wt, "F"))


# ═══════════════════════════════════════════════════════════════════════════════
#  CLÔTURE PAR CANTOR–BERNSTEIN  :  l'égalité-cible À PARTIR des DEUX directions.
# ───────────────────────────────────────────────────────────────────────────────
#   DIRECTION A (CLOSE, inf_egal_phi) :  𝓕(B⊔C;A) ≤ 𝓕(B;A)×𝓕(C;A).
#   DIRECTION B (à fournir, inf_egal_psi) :  𝓕(B;A)×𝓕(C;A) ≤ 𝓕(B⊔C;A).
#   cantor_bernstein + _prop1_direct_t ⟹ Card(𝓕(B⊔C;A)) = Card(𝓕(B;A)×𝓕(C;A)).
# ═══════════════════════════════════════════════════════════════════════════════
def prop9_depuis_deux_injections(inf_A, inf_B, a="A", b="B", c="C"):
    """De  ⊢ inf_egal_card(𝓕(B⊔C;A), 𝓕(B;A)×𝓕(C;A))   (DIRECTION A, inf_A)
       et  ⊢ inf_egal_card(𝓕(B;A)×𝓕(C;A), 𝓕(B⊔C;A))   (DIRECTION B, inf_B)
       déduit  ⊢ Card(𝓕(B⊔C;A)) = Card(𝓕(B;A) × 𝓕(C;A))  =  cible_prop9_exp_somme.

    ASSEMBLEUR FINAL (PUR) de la Proposition 9 par CANTOR–BERNSTEIN :
      cantor_bernstein(dom,cod) ⊢ (dom≤cod et cod≤dom) ⇒ Eq(dom,cod) ;
      MP avec (inf_A et inf_B) ⊢ Eq(dom,cod) ;
      _prop1_direct_t(dom,cod) ⊢ Eq(dom,cod) ⇒ Card dom = Card cod.
    La conclusion est LITTÉRALEMENT cible_prop9_exp_somme(A,B,C).  inf_A, inf_B sont
    des THÉORÈMES CLOS (Direction A = inf_egal_phi ; Direction B = inf_egal_psi)."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.cantor_bernstein.cloture import cantor_bernstein
    va, vb, vc = _t(a), _t(b), _t(c)
    dom = domaine_phi(va, vb, vc)
    cod = codomaine_phi(va, vb, vc)
    # cantor_bernstein : (X≤Y et Y≤X) ⇒ Eq(X,Y)  — version TERME (généralise puis
    # instancie aux deux espaces, comme _prop1_direct_t ; évite la capture des noms
    # internes f,g de la machinerie Knaster–Tarski sur des termes composés).
    cb_nom = cantor_bernstein("A", "B", "f", "g")    # (A≤B et B≤A) ⇒ Eq(A,B)
    cb_gen = N.generalisation("A", N.generalisation("B", cb_nom))
    cb = instancie(instancie(cb_gen, dom), cod)      # (dom≤cod et cod≤dom) ⇒ Eq(dom,cod)
    eq = N.modus_ponens(conjonction_intro(inf_A, inf_B), cb)   # Eq(dom, cod)
    # Proposition 1 sens direct : Eq(dom,cod) ⇒ Card dom = Card cod
    prop1 = _prop1_direct_t(dom, cod)
    return N.modus_ponens(eq, prop1)                           # Card dom = Card cod = cible


# ═══════════════════════════════════════════════════════════════════════════════
#  DIRECTION B : ψ : 𝓕(B;A)×𝓕(C;A) ↪ 𝓕(B⊔C;A)  (recollement réindexé)
# ───────────────────────────────────────────────────────────────────────────────
#   pour (g,h), K_g et K_h réindexent les graphes sur les copies marquées :
#     K_g = graphe_terme(B×{0}, g(pr₁ z)) ,  K_h = graphe_terme(C×{1}, h(pr₁ z))
#   K = K_g ∪ K_h  est une fonction B⊔C→A (domaines disjoints), ψ(g,h)=((K,B⊔C),A).
# ═══════════════════════════════════════════════════════════════════════════════
_PTK = "k"        # point courant des graphe-terme réindexés K_g, K_h (≠ x,y,z internes)
_VBK = "m"        # liant τ de la valeur g(pr₁ k) / h(pr₁ k)  (= _VB, sûr)


def _B0(vb):
    """B×{0}  (copie marquée gauche)."""
    return E.produit(vb, E.singleton(ZERO))


def _C1(vc):
    """C×{1}  (copie marquée droite)."""
    return E.produit(vc, E.singleton(UN))


def _val_Kg(g):
    """g(pr₁ z) = valeur(graphe_de(g), pr₁ z, m)   (valeur du graphe de g en pr₁ z)."""
    return E.valeur(graphe_de(_t(g)), E.pr1(var(_PTK), "a", "b"), _VBK)


def _val_Kh(h):
    """h(pr₁ z) = valeur(graphe_de(h), pr₁ z, m)."""
    return E.valeur(graphe_de(_t(h)), E.pr1(var(_PTK), "a", "b"), _VBK)


def K_gauche(g, b):
    """K_g := graphe_terme(B×{0}, g(pr₁ z))  (réindexation du graphe de g sur B×{0})."""
    return E.graphe_terme(_B0(_t(b)), _val_Kg(g), _PTK)


def K_droite(h, c):
    """K_h := graphe_terme(C×{1}, h(pr₁ z))  (réindexation du graphe de h sur C×{1})."""
    return E.graphe_terme(_C1(_t(c)), _val_Kh(h), _PTK)


def K_psi(g, h, b, c):
    """K := K_g ∪ K_h  (le graphe recollé de ψ(g,h), fonction sur B⊔C)."""
    return E.reunion(K_gauche(g, b), K_droite(h, c))


def K_gauche_domaine(g="g", b="B"):
    """⊢ dom(K_g) = B×{0}."""
    return graphe_terme_domaine(_B0(_t(b)), _val_Kg(g), _PTK, "y", "zz")


def K_droite_domaine(h="h", c="C"):
    """⊢ dom(K_h) = C×{1}."""
    return graphe_terme_domaine(_C1(_t(c)), _val_Kh(h), _PTK, "y", "zz")


def K_gauche_fonctionnelle(g="g", b="B"):
    """⊢ est_fonctionnel(K_g)  (graphe-terme, C54)."""
    return graphe_terme_fonctionnel(_B0(_t(b)), _val_Kg(g), _PTK, "y")


def K_droite_fonctionnelle(h="h", c="C"):
    """⊢ est_fonctionnel(K_h)."""
    return graphe_terme_fonctionnel(_C1(_t(c)), _val_Kh(h), _PTK, "y")


def _inclus_de_egal(t_eq, sur):
    """De ⊢ X = Y, déduit ⊢ X ⊂ Y   (égalité ⇒ inclusion ; X,Y termes via t_eq)."""
    # X⊂Y = (∀z)(z∈X ⇒ z∈Y) ; de X=Y, z∈X ⇒ z∈Y (Leibniz)
    X = t_eq.conclusion.termes[0]
    Y = t_eq.conclusion.termes[1]
    vz = var("z")
    hz = N.assume(appartient(vz, X))
    z_in_Y = N.modus_ponens(hz, equivalence_avant(N.modus_ponens(t_eq,
        N.s6(X, Y, "w", appartient(vz, var("w"))))))
    return N.generalisation("z", N.loi_deduction(appartient(vz, X), z_in_Y))


def K_fonctionnelle(g="g", h="h", b="B", c="C"):
    """⊢ est_fonctionnel(K).   K = K_g ∪ K_h ; domaines DISJOINTS (copies 0≠1).

    reunion_graphes_fonctionnelle (PIVOT) sous {K_g func, K_h func, (∀u)¬(u∈dom K_g
    et u∈dom K_h)} ; la disjonction vient de domaines_disjoints_si_marques car
    dom K_g=B×{0}, dom K_h=C×{1} (équivaut à inclusion)."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.recollement.ensembles_restriction_somme import (
        reunion_graphes_fonctionnelle, domaines_disjoints_si_marques)
    vg, vh, vb, vc = _t(g), _t(h), _t(b), _t(c)
    Kg, Kh = K_gauche(vg, vb), K_droite(vh, vc)
    # disjonction des domaines (généralisée sur u), via dom K_g⊂B×{0}, dom K_h⊂C×{1}
    domKg_incl = _inclus_de_egal(K_gauche_domaine(g, b), _B0(vb))   # dom K_g⊂B×{0}
    domKh_incl = _inclus_de_egal(K_droite_domaine(h, c), _C1(vc))   # dom K_h⊂C×{1}
    disj_u = domaines_disjoints_si_marques(Kg, Kh, vb, vc, "u")     # ¬(u∈domKg et u∈domKh)
    disj_u = _cut(disj_u, [(inclus(E.dom(Kg), _B0(vb)), domKg_incl),
                           (inclus(E.dom(Kh), _C1(vc)), domKh_incl)])
    disj = N.generalisation("u", disj_u)
    disj_f = pourtout("u", non(et(appartient(var("u"), E.dom(Kg)),
                                  appartient(var("u"), E.dom(Kh)))))
    pivot = reunion_graphes_fonctionnelle(Kg, Kh)   # {Kg func,Kh func,disj}⊢func(K)
    out = _cut(pivot, [(E.est_fonctionnel(Kg), K_gauche_fonctionnelle(g, b)),
                       (E.est_fonctionnel(Kh), K_droite_fonctionnelle(h, c)),
                       (disj_f, disj)])
    return out                                      # est_fonctionnel(K)


def K_domaine(g="g", h="h", b="B", c="C"):
    """⊢ dom(K) = B⊔C.   dom K = dom K_g ∪ dom K_h = B×{0} ∪ C×{1} = B⊔C."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.recollement.ensembles_restriction_somme import dom_reunion_graphes
    vg, vh, vb, vc = _t(g), _t(h), _t(b), _t(c)
    Kg, Kh = K_gauche(vg, vb), K_droite(vh, vc)
    BC = somme_disjointe(vb, vc)
    # dom K = dom K_g ∪ dom K_h
    dom_eq = dom_reunion_graphes(Kg, Kh)            # dom(K_g∪K_h)=dom K_g∪dom K_h
    # dom K_g=B×{0}, dom K_h=C×{1} ; réécrire dom K_g∪dom K_h → B×{0}∪C×{1} = B⊔C
    dKg = K_gauche_domaine(g, b)                    # dom K_g=B×{0}
    dKh = K_droite_domaine(h, c)                    # dom K_h=C×{1}
    # dom K_g∪dom K_h = B×{0}∪dom K_h  (congruence gauche)
    step1 = N.modus_ponens(dKg, congruence_terme(E.dom(Kg), _B0(vb),
        E.reunion(var("w"), E.dom(Kh))))            # domKg∪domKh = B×{0}∪domKh
    step2 = N.modus_ponens(dKh, congruence_terme(E.dom(Kh), _C1(vc),
        E.reunion(_B0(vb), var("w"))))              # B×{0}∪domKh = B×{0}∪C×{1} = B⊔C
    # dom K = domKg∪domKh = B×{0}∪domKh = B⊔C   (B⊔C est littéralement B×{0}∪C×{1})
    return composer_egalites(composer_egalites(dom_eq, step1), step2)   # dom K = B⊔C


def _copie_dans_somme(vk, vb, vc, marker, gauche):
    """{ k ∈ B×{0} } ⊢ k ∈ B⊔C   (gauche=True),  ou  { k ∈ C×{1} } ⊢ k ∈ B⊔C (gauche=False).

    B⊔C = (B×{0})∪(C×{1}) ; injection de la copie marquée dans la réunion
    (membre_somme_reunion, sens ⇐ via S2/S3)."""
    from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_recollement_somme.ensembles_somme_disjointe import membre_somme_reunion
    Dm = E.produit(vb if gauche else vc, E.singleton(marker))
    B0 = E.produit(vb, E.singleton(ZERO))
    C1 = E.produit(vc, E.singleton(UN))
    reun = membre_somme_reunion(vb, vc, vk)            # k∈B⊔C ⇔ (k∈B×{0} ou k∈C×{1})
    hk = N.assume(appartient(vk, Dm))                  # k∈D×{marker}
    if gauche:
        disj = N.modus_ponens(hk, N.s2(appartient(vk, B0), appartient(vk, C1)))   # ∈B0 ou ∈C1
    else:
        disj = N.modus_ponens(N.modus_ponens(hk, N.s2(appartient(vk, C1), appartient(vk, B0))),
                              N.s3(appartient(vk, C1), appartient(vk, B0)))         # ∈B0 ou ∈C1
    k_in_BC = N.modus_ponens(disj, equivalence_arriere(reun))   # k∈B⊔C
    return N.loi_deduction(appartient(vk, Dm), k_in_BC)         # k∈D×{marker} ⇒ k∈B⊔C


def _pr1_dans_facteur(vk, vb, marker, marker_name):
    """{ k ∈ B×{marker} } ⊢ pr₁(k) ∈ B.

    k∈B×{marker} ⇔ (∃u)(u∈B et k=(u,marker)) (_membre_produit_singleton) ; sous le
    témoin u, pr₁(k)=pr₁((u,marker))=u (projection_premiere) et u∈B, d'où pr₁(k)∈B."""
    from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_recollement_somme.ensembles_somme_disjointe import _membre_produit_singleton
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_produit.ensembles_produit_commute import _projection_premiere_ab
    pr1k = E.pr1(vk, "a", "b")
    car = _membre_produit_singleton(vb, marker, vk, "u")   # k∈B×{marker} ⇔ (∃u)(u∈B et k=(u,marker))
    body = et(appartient(var("u"), vb), egal(vk, E.couple(var("u"), marker)))
    hb = N.assume(body)
    uB = conjonction_elim_gauche(hb)                       # u∈B
    k_eq = conjonction_elim_droite(hb)                     # k=(u,marker)
    # pr₁(k) = pr₁((u,marker)) = u
    pr1_cong = N.modus_ponens(k_eq, congruence_terme(vk, E.couple(var("u"), marker),
        E.pr1(var("w"), "a", "b")))                        # pr₁(k)=pr₁((u,marker))
    pr1_uv = _projection_premiere_ab(var("u"), marker, "a", "b")   # pr₁((u,marker))=u
    pr1k_eq_u = composer_egalites(pr1_cong, pr1_uv)        # pr₁(k)=u
    pr1k_in_B = N.modus_ponens(uB, equivalence_arriere(N.modus_ponens(pr1k_eq_u,
        N.s6(pr1k, var("u"), "w", appartient(var("w"), vb)))))   # pr₁(k)∈B
    ex_imp = existe_elimination(N.loi_deduction(body, pr1k_in_B), "u")
    hk = N.assume(appartient(vk, E.produit(vb, E.singleton(marker))))
    ex = N.modus_ponens(hk, equivalence_avant(car))
    return N.modus_ponens(ex, ex_imp)                      # {k∈B×{marker}} ⊢ pr₁(k)∈B


def _K_morceau_inclus(vg, va, vb, vc, vD, Kg, valK, marker, marker_in_BC_lemme):
    """{ graphe_de(g)⊂D×A, dom graphe_de(g)=D } ⊢ K_g ⊂ (B⊔C)×A,
       K_g = graphe_terme(D×{marker}, g(pr₁ k)), valK = g(pr₁ k).

    z∈K_g ⇒ z=(k,y), k∈D×{marker}, y=g(pr₁ k) ; pr₁(k)∈D (_pr1_dans_facteur) ⇒
    y∈A (pont _valeur_codomaine_q) ; k∈D×{marker}⊂B⊔C (marker_in_BC_lemme : k∈B⊔C) ;
    donc (k,y)∈(B⊔C)×A, i.e. z∈(B⊔C)×A."""
    G = graphe_de(vg)
    BC = somme_disjointe(vb, vc)
    Dm = E.produit(vD, E.singleton(marker))        # D×{marker}
    vk, vy, vz = var("k"), var("y"), var("z")
    pr1k = E.pr1(vk, "a", "b")
    BCA = E.produit(BC, va)

    hyp_incl = N.assume(inclus(G, E.produit(vD, va)))   # graphe_de(g)⊂D×A
    hyp_dom = N.assume(egal(E.dom(G), vD))             # dom graphe_de(g)=D

    car = _membre_graphe_terme_z(Dm, valK, _PTK, "z", "y")  # z∈K_g ⇔ (∃k)(∃y)(z=(k,y) et k∈D×{marker} et y=valK)
    body = et(et(egal(vz, E.couple(vk, vy)), appartient(vk, Dm)), egal(vy, valK))
    hb = N.assume(body)
    z_eq = conjonction_elim_gauche(conjonction_elim_gauche(hb))   # z=(k,y)
    kDm = conjonction_elim_droite(conjonction_elim_gauche(hb))    # k∈D×{marker}
    y_eq = conjonction_elim_droite(hb)                           # y=g(pr₁ k)
    # pr₁(k)∈D
    pr1k_in_D = _cut(_pr1_dans_facteur(vk, vD, marker, None),
                     [(appartient(vk, Dm), kDm)])                # pr₁(k)∈D
    # g(pr₁ k)∈A  (pont _valeur_codomaine_q sous graphe_de(g)⊂D×A, dom=D, pr₁(k)∈D)
    vdc = _valeur_codomaine_q(G, vD, va, pr1k)                   # ⊢ g(pr₁ k)∈A
    valK_in_A = _cut(vdc, [(inclus(G, E.produit(vD, va)), hyp_incl),
                           (egal(E.dom(G), vD), hyp_dom),
                           (appartient(pr1k, vD), pr1k_in_D)])    # valK∈A
    y_in_A = N.modus_ponens(valK_in_A, equivalence_arriere(N.modus_ponens(
        y_eq, N.s6(vy, valK, "w", appartient(var("w"), va)))))   # y∈A
    # k∈B⊔C
    k_in_BC = N.modus_ponens(kDm, marker_in_BC_lemme)            # k∈B⊔C
    # (k,y)∈(B⊔C)×A
    ky_in = N.modus_ponens(conjonction_intro(k_in_BC, y_in_A),
                           equivalence_arriere(_membre_produit(vk, vy, BC, va)))
    z_in = N.modus_ponens(ky_in, equivalence_arriere(N.modus_ponens(
        z_eq, N.s6(vz, E.couple(vk, vy), "w", appartient(var("w"), BCA)))))  # z∈(B⊔C)×A
    ex_imp = existe_elimination(existe_elimination(
        N.loi_deduction(body, z_in), "y"), _PTK)
    hz = N.assume(appartient(vz, Kg))
    ex = N.modus_ponens(hz, equivalence_avant(car))
    return N.generalisation("z", N.loi_deduction(appartient(vz, Kg),
                                                 N.modus_ponens(ex, ex_imp)))  # K_g⊂(B⊔C)×A


def K_gauche_inclus(g="g", a="A", b="B", c="C"):
    """{ graphe_de(g)⊂B×A, dom graphe_de(g)=B } ⊢ K_g ⊂ (B⊔C)×A."""
    vg, va, vb, vc = _t(g), _t(a), _t(b), _t(c)
    Kg = K_gauche(vg, vb)
    return _K_morceau_inclus(vg, va, vb, vc, vb, Kg, _val_Kg(vg), ZERO,
                             _copie_dans_somme(var("k"), vb, vc, ZERO, True))


def K_droite_inclus(h="h", a="A", b="B", c="C"):
    """{ graphe_de(h)⊂C×A, dom graphe_de(h)=C } ⊢ K_h ⊂ (B⊔C)×A."""
    vh, va, vb, vc = _t(h), _t(a), _t(b), _t(c)
    Kh = K_droite(vh, vc)
    return _K_morceau_inclus(vh, va, vb, vc, vc, Kh, _val_Kh(vh), UN,
                             _copie_dans_somme(var("k"), vb, vc, UN, False))


def K_inclus(g="g", h="h", a="A", b="B", c="C"):
    """{ graphe_de(g)⊂B×A, dom graphe_de(g)=B, graphe_de(h)⊂C×A, dom graphe_de(h)=C }
        ⊢ K ⊂ (B⊔C)×A.    (z∈K_g∪K_h ⇒ z∈K_g ou z∈K_h ⇒ z∈(B⊔C)×A.)"""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.recollement.ensembles_restriction_somme import membre_reunion_graphes
    vg, vh, va, vb, vc = _t(g), _t(h), _t(a), _t(b), _t(c)
    Kg, Kh = K_gauche(vg, vb), K_droite(vh, vc)
    K = E.reunion(Kg, Kh)
    BC = somme_disjointe(vb, vc)
    BCA = E.produit(BC, va)
    vz = var("z")
    incl_g = K_gauche_inclus(g, a, b, c)           # K_g⊂(B⊔C)×A  [hyps g]
    incl_h = K_droite_inclus(h, a, b, c)           # K_h⊂(B⊔C)×A  [hyps h]
    # z∈K_g ⇒ z∈(B⊔C)×A  et  z∈K_h ⇒ z∈(B⊔C)×A   (instances des inclusions)
    impG = instancie(incl_g, vz)
    impH = instancie(incl_h, vz)
    car = membre_reunion_graphes(Kg, Kh, vz)       # z∈K ⇔ (z∈K_g ou z∈K_h)
    hz = N.assume(appartient(vz, K))
    disj = N.modus_ponens(hz, equivalence_avant(car))   # z∈K_g ou z∈K_h
    z_in = cas(disj, impG, impH)                   # z∈(B⊔C)×A
    return N.generalisation("z", N.loi_deduction(appartient(vz, K), z_in))   # K⊂(B⊔C)×A


def K_dans_exposant(g="g", h="h", a="A", b="B", c="C"):
    """{ graphe_de(g)⊂B×A, dom graphe_de(g)=B, graphe_de(h)⊂C×A, dom graphe_de(h)=C }
        ⊢ K ∈ A^(B⊔C).    (K⊂(B⊔C)×A et K fonctionnel et dom K=B⊔C, via axiome_exposant.)"""
    vg, vh, va, vb, vc = _t(g), _t(h), _t(a), _t(b), _t(c)
    K = K_psi(vg, vh, vb, vc)
    BC = somme_disjointe(vb, vc)
    incl = K_inclus(g, h, a, b, c)                 # K⊂(B⊔C)×A  [hyps g,h]
    func = K_fonctionnelle(g, h, b, c)             # est_fonctionnel(K)  (clos)
    dom = K_domaine(g, h, b, c)                    # dom K=B⊔C  (clos)
    return _restriction_dans_exposant(va, BC, K, incl, func, dom)   # K∈A^(B⊔C)


def psi_dans_applications(g="g", h="h", a="A", b="B", c="C"):
    """{ graphe_de(g)⊂B×A, dom graphe_de(g)=B, graphe_de(h)⊂C×A, dom graphe_de(h)=C }
        ⊢ ((K, B⊔C), A) ∈ 𝓕(B⊔C; A).    (ψ(g,h) est une application de B⊔C dans A.)"""
    vg, vh, va, vb, vc = _t(g), _t(h), _t(a), _t(b), _t(c)
    K = K_psi(vg, vh, vb, vc)
    BC = somme_disjointe(vb, vc)
    in_exp = K_dans_exposant(g, h, a, b, c)        # K∈A^(B⊔C)
    return _triple_dans_applications(va, BC, K, in_exp)   # ((K,B⊔C),A)∈𝓕(B⊔C;A)


def _graphe_de_facteur_props(vg, va, vD):
    """{ g ∈ 𝓕(D;A) } ⊢ ( graphe_de(g) ⊂ D×A  et  dom graphe_de(g) = D ).

    membre_applications_b(D,A) : g∈𝓕(D;A) ⇔ (∃G)(g=((G,D),A) et G∈A^D) ; axiome_exposant
    déplie G∈A^D en (G⊂D×A et G fonct et dom G=D) ; graphe_de_triple+Leibniz ⇒
    graphe_de(g)=G ; transport des deux propriétés à graphe_de(g)."""
    from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_6_fonction_terme.ensembles_fonction_terme import graphe_terme_fonctionnel  # noqa
    vG = var("G")
    triple = E.couple(E.couple(vG, vD), va)
    in_exp = appartient(vG, E.exposant(vD, va))
    grg = graphe_de(vg)
    # membre_applications_b instancié : g∈𝓕(D;A) ⇔ (∃G)(g=((G,D),A) et G∈A^D)
    ax_app = N.axiome(E.theorie_applications(vD, va, "t", "G"),
                      E.axiome_applications(vD, va, "t", "G"))
    app_car = instancie(ax_app, vg)                # g∈𝓕(D;A) ⇔ (∃G)(g=((G,D),A) et G∈A^D)
    ax_exp = N.axiome(E.theorie_exposant(vD, va), E.axiome_exposant(vD, va))
    exp_car = instancie(ax_exp, vG)                # G∈A^D ⇔ (G⊂D×A et G fonct et dom G=D)

    cible = et(inclus(grg, E.produit(vD, va)), egal(E.dom(grg), vD))
    body = et(egal(vg, triple), in_exp)
    hb = N.assume(body)
    g_eq = conjonction_elim_gauche(hb)             # g=((G,D),A)
    g_in_exp = conjonction_elim_droite(hb)         # G∈A^D
    corps = N.modus_ponens(g_in_exp, equivalence_avant(exp_car))   # G⊂D×A et G fonct et dom G=D
    G_incl = conjonction_elim_gauche(conjonction_elim_gauche(corps))  # G⊂D×A
    G_dom = conjonction_elim_droite(corps)         # dom G=D
    # graphe_de(g)=G
    gr_triple = graphe_de_triple(vG, vD, va)       # gr(((G,D),A))=G
    gr_g_eq = composer_egalites(
        N.modus_ponens(g_eq, congruence_terme(vg, triple, graphe_de(var("w")))), gr_triple)  # gr(g)=G
    incl_grg = N.modus_ponens(G_incl, equivalence_arriere(N.modus_ponens(gr_g_eq,
        N.s6(grg, vG, "w", inclus(var("w"), E.produit(vD, va))))))   # gr(g)⊂D×A
    dom_grg = N.modus_ponens(G_dom, equivalence_arriere(N.modus_ponens(gr_g_eq,
        N.s6(grg, vG, "w", egal(E.dom(var("w")), vD)))))            # dom gr(g)=D
    concl = conjonction_intro(incl_grg, dom_grg)
    inner = existe_elimination(N.loi_deduction(body, concl), "G")
    h_app = N.assume(appartient(vg, E.applications(vD, va)))
    ex_body = N.modus_ponens(h_app, equivalence_avant(app_car))     # (∃G)body
    return N.modus_ponens(ex_body, inner)          # cible  [g∈𝓕(D;A)]


def psi_dans_applications_sous_appartenance(g="g", h="h", a="A", b="B", c="C"):
    """{ g ∈ 𝓕(B;A),  h ∈ 𝓕(C;A) } ⊢ ψ(g,h) = ((K,B⊔C),A) ∈ 𝓕(B⊔C; A).

    BIEN-DÉFINITION de ψ.  _graphe_de_facteur_props extrait, sous g∈𝓕(B;A) (resp.
    h∈𝓕(C;A)), les quatre faits structurels graphe_de(g)⊂B×A, dom=B (resp. C) qui
    déchargent psi_dans_applications."""
    vg, vh, va, vb, vc = _t(g), _t(h), _t(a), _t(b), _t(c)
    pg = _graphe_de_facteur_props(vg, va, vb)      # {g∈𝓕(B;A)} ⊢ gr(g)⊂B×A et dom gr(g)=B
    ph = _graphe_de_facteur_props(vh, va, vc)      # {h∈𝓕(C;A)} ⊢ gr(h)⊂C×A et dom gr(h)=C
    g_incl = conjonction_elim_gauche(pg)
    g_dom = conjonction_elim_droite(pg)
    h_incl = conjonction_elim_gauche(ph)
    h_dom = conjonction_elim_droite(ph)
    base = psi_dans_applications(g, h, a, b, c)     # {4 hyps} ⊢ ψ(g,h)∈𝓕(B⊔C;A)
    grg, grh = graphe_de(vg), graphe_de(vh)
    return _cut(base, [
        (inclus(grg, E.produit(vb, va)), g_incl),
        (egal(E.dom(grg), vb), g_dom),
        (inclus(grh, E.produit(vc, va)), h_incl),
        (egal(E.dom(grh), vc), h_dom)])            # ψ(g,h)∈𝓕(B⊔C;A)  [g∈𝓕(B;A),h∈𝓕(C;A)]


# ── L'injection ψ : graphe W_ψ = graphe_terme(cod, ψ(pr₁ p, pr₂ p), « p ») ────────
_POINTPS = "p"        # point courant de W_ψ  (un couple (g,h) ∈ cod)


def psi_valeur(p, a, b, c):
    """ψ(p) := ((K(pr₁ p, pr₂ p), B⊔C), A)   pour p=(g,h) ∈ 𝓕(B;A)×𝓕(C;A)."""
    vp, va, vb, vc = _t(p), _t(a), _t(b), _t(c)
    g = E.pr1(vp, "a", "b")
    h = E.pr2(vp, "a", "b")
    BC = somme_disjointe(vb, vc)
    return E.couple(E.couple(K_psi(g, h, vb, vc), BC), va)


def W_psi(a="A", b="B", c="C"):
    """W_ψ := graphe_terme( 𝓕(B;A)×𝓕(C;A) , ψ(p) , « p » )  (le GRAPHE de ψ, terme)."""
    va, vb, vc = _t(a), _t(b), _t(c)
    return E.graphe_terme(codomaine_phi(va, vb, vc),
                          psi_valeur(var(_POINTPS), va, vb, vc), _POINTPS)


def W_psi_fonctionnel(a="A", b="B", c="C"):
    """⊢ est_fonctionnel(W_ψ)  (graphe-terme, C54)."""
    va, vb, vc = _t(a), _t(b), _t(c)
    return graphe_terme_fonctionnel(codomaine_phi(va, vb, vc),
                                    psi_valeur(var(_POINTPS), va, vb, vc), _POINTPS, "y")


def W_psi_domaine(a="A", b="B", c="C"):
    """⊢ dom(W_ψ) = 𝓕(B;A)×𝓕(C;A)  (graphe-terme, C54)."""
    va, vb, vc = _t(a), _t(b), _t(c)
    return graphe_terme_domaine(codomaine_phi(va, vb, vc),
                                psi_valeur(var(_POINTPS), va, vb, vc), _POINTPS, "y", "z")


def _psi_cod_en_point(va, vb, vc, vp, p_in_thm):
    """De {p∈cod} (p_in_thm) ⊢ ψ(p) ∈ 𝓕(B⊔C;A).

    p∈𝓕(B;A)×𝓕(C;A) ⇒ pr₁p∈𝓕(B;A) et pr₂p∈𝓕(C;A) (_membre_produit_pr1/pr2_ab) ;
    psi_dans_applications_sous_appartenance(pr₁p, pr₂p) ⊢ ψ(p)∈𝓕(B⊔C;A)
    (ψ(p)=ψ_valeur(p) emploie justement g:=pr₁p, h:=pr₂p)."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_produit.ensembles_produit_commute import (
        _membre_produit_pr1_ab, _membre_produit_pr2_ab)
    FB = E.applications(vb, va)                    # 𝓕(B;A)
    FC = E.applications(vc, va)                    # 𝓕(C;A)
    g = E.pr1(vp, "a", "b")                        # pr₁p
    h = E.pr2(vp, "a", "b")                        # pr₂p
    # pr₁p∈𝓕(B;A), pr₂p∈𝓕(C;A)
    pr1_in = _cut(_membre_produit_pr1_ab(FB, FC, vp),
                  [(appartient(vp, E.produit(FB, FC)), p_in_thm)])   # pr₁p∈𝓕(B;A)
    pr2_in = _cut(_membre_produit_pr2_ab(FB, FC, vp),
                  [(appartient(vp, E.produit(FB, FC)), p_in_thm)])   # pr₂p∈𝓕(C;A)
    # ψ(g,h)∈𝓕(B⊔C;A) avec g=pr₁p, h=pr₂p (instance-terme)
    base = psi_dans_applications_sous_appartenance(g, h, va, vb, vc)
    return _cut(base, [(appartient(g, FB), pr1_in), (appartient(h, FC), pr2_in)])  # ψ(p)∈𝓕(B⊔C;A)


def W_psi_image_incluse(a="A", b="B", c="C"):
    """⊢ image(W_ψ, 𝓕(B;A)×𝓕(C;A)) ⊂ 𝓕(B⊔C;A).

    z∈W_ψ⟨cod⟩ ⇔ (∃p)(p∈cod et (p,z)∈W_ψ) ; (p,z)∈W_ψ ⇔ (p∈cod et z=ψ(p)) ;
    ψ(p)∈𝓕(B⊔C;A) (_psi_cod_en_point) ⇒ z∈𝓕(B⊔C;A)."""
    va, vb, vc = _t(a), _t(b), _t(c)
    cod = codomaine_phi(va, vb, vc)
    dom = domaine_phi(va, vb, vc)                  # 𝓕(B⊔C;A) — c'est le BUT de ψ
    W = W_psi(va, vb, vc)
    PSI = psi_valeur(var(_POINTPS), va, vb, vc)
    vz, vp = var("z"), var("p")
    from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import alpha_existe

    ax_img = N.axiome(E.theorie_ensembles(), E.AXIOME_IMAGE)
    img0 = instancie(instancie(instancie(ax_img, W), cod), vz)
    impl_LtoEX = img0.conclusion.sous[0].sous[0].sous[0]
    rhs_ex = impl_LtoEX.sous[1]
    assert rhs_ex.tag == "exists"
    nom = rhs_ex.lieur
    inner = et(appartient(var(nom), cod), appartient(E.couple(var(nom), vz), W))
    ren = alpha_existe(nom, "pp", inner)           # liant frais « pp » (« p » est le point de W_ψ)
    img_car = equivalence_transitivite(img0, ren)  # z∈W_ψ⟨cod⟩ ⇔ (∃pp)(pp∈cod et (pp,z)∈W_ψ)

    vp = var("pp")                                 # le témoin de l'image
    mem = membre_graphe_terme(cod, PSI, "pp", "z", _POINTPS, "y")  # ((pp,z)∈W_ψ)⇔(pp∈cod et z=ψ[pp])
    Psi_p = subst_t(vp, _POINTPS, PSI)             # ψ(pp)
    body = et(appartient(vp, cod), appartient(E.couple(vp, vz), W))
    hb = N.assume(body)
    p_in = conjonction_elim_gauche(hb)             # p∈cod
    pz_in = conjonction_elim_droite(hb)            # (p,z)∈W_ψ
    cond = N.modus_ponens(pz_in, equivalence_avant(mem))   # p∈cod et z=ψ(p)
    z_eq = conjonction_elim_droite(cond)           # z=ψ(p)
    psi_p_in = _psi_cod_en_point(va, vb, vc, vp, p_in)     # ψ(p)∈𝓕(B⊔C;A)
    z_in = N.modus_ponens(psi_p_in, equivalence_arriere(N.modus_ponens(
        z_eq, N.s6(vz, Psi_p, "w", appartient(var("w"), dom)))))   # z∈𝓕(B⊔C;A)
    ex_imp = existe_elimination(N.loi_deduction(body, z_in), "pp")
    h_z = N.assume(appartient(vz, E.image(W, cod)))
    ex = N.modus_ponens(h_z, equivalence_avant(img_car))
    return N.generalisation("z", N.loi_deduction(appartient(vz, E.image(W, cod)),
                                                 N.modus_ponens(ex, ex_imp)))


def direction_B_REPORTE():
    """REPORTÉ (PARTIEL) — DIRECTION B : 𝓕(B;A)×𝓕(C;A) ≤ 𝓕(B⊔C;A).
    SEULE LA ψ-INJECTIVITÉ RESTE OUVERTE ; tout le reste de ψ est CLOS.

    DIRECTION A (CLOSE, inf_egal_phi) ⊢ inf_egal_card(𝓕(B⊔C;A), 𝓕(B;A)×𝓕(C;A))
    via Φ : f ↦ (((f|B,B),A),((f|C,C),A)), 4 conjoints de est_injection_de certifiés.

    DIRECTION B — ψ : (g,h) ↦ ((K,B⊔C),A), K = K_g ∪ K_h recollement réindexé
        K_g = graphe_terme(B×{0}, g(pr₁ k)) ,  K_h = graphe_terme(C×{1}, h(pr₁ k)).
    SONT CLOS dans ce module :
      • K_fonctionnelle ⊢ est_fonctionnel(K)         (copies marquées disjointes) ;
      • K_domaine       ⊢ dom K = B⊔C ;
      • K_inclus        {hyps gr} ⊢ K ⊂ (B⊔C)×A      (pont valeur_dans_codomaine) ;
      • K_dans_exposant {hyps gr} ⊢ K ∈ A^(B⊔C) ;
      • psi_dans_applications_sous_appartenance  {g∈𝓕(B;A), h∈𝓕(C;A)} ⊢ ψ(g,h)∈𝓕(B⊔C;A)
        (BIEN-DÉFINITION COMPLÈTE de ψ) ;
      • W_psi_fonctionnel / W_psi_domaine / W_psi_image_incluse  (graphe W_ψ de ψ :
        fonctionnel, défini sur tout 𝓕(B;A)×𝓕(C;A), image ⊂ 𝓕(B⊔C;A)).
    RESTE OUVERT le SEUL conjoint d'injectivité : injective_dans(W_ψ, 𝓕(B;A)×𝓕(C;A)),
    i.e. ψ(p₁)=ψ(p₂) ⇒ p₁=p₂.  Le verrou conceptuel est LEVÉ (l'infra recollement
    `valeur_reunion_gauche/droite` donne K((u,0))=g(u), K((v,1))=h(v) ; combinée au pont
    graphe_de et à graphe_egal_par_valeurs, elle reconstruit gᵢ,hᵢ comme pour Φ).  Il
    s'agit du MÊME back-and-forth que W_phi_injective, dupliqué pour ψ — hors budget de
    ce round mais purement mécanique (aucun verrou nouveau).

    Une fois inf_egal_psi clos (assemblage des 4 conjoints W_ψ + S5, miroir d'inf_egal_phi),
    `prop9_depuis_deux_injections(inf_egal_phi(), inf_egal_psi())` CLÔT INCONDITIONNELLEMENT
    la Proposition 9 (conclusion == cible_prop9_exp_somme — assembleur VÉRIFIÉ)."""
    raise NotImplementedError(
        "DIRECTION B : SEUL le conjoint injective_dans(W_ψ, 𝓕(B;A)×𝓕(C;A)) reste ouvert. "
        "ψ bien définie + W_ψ fonctionnel/domaine/image⊂𝓕(B⊔C;A) sont CLOS ; la ψ-injectivité "
        "est le même back-and-forth que W_phi_injective (via valeur_reunion_gauche/droite + "
        "graphe_egal_par_valeurs), purement mécanique, hors budget.  DIRECTION A (inf_egal_phi) "
        "CLOSE ; prop9_depuis_deux_injections assemble la cible dès que inf_egal_psi est fourni.")


__all__ = [
    "restriction_gauche", "restriction_droite", "phi_valeur",
    "restriction_gauche_fonctionnelle", "restriction_gauche_domaine",
    "restriction_droite_fonctionnelle", "restriction_droite_domaine",
    "restriction_gauche_inclus", "restriction_droite_inclus",
    "triple_gauche_dans_applications", "triple_droite_dans_applications",
    "phi_dans_codomaine", "phi_dans_codomaine_sous_appartenance",
    "domaine_phi", "codomaine_phi", "W_phi",
    "W_phi_fonctionnel", "W_phi_domaine", "W_phi_valeur",
    "W_phi_image_incluse", "phi_injective_sous_appartenance", "W_phi_injective",
    "W_phi_est_injection", "inf_egal_phi",
    "prop9_depuis_deux_injections", "direction_B_REPORTE",
    # — DIRECTION B (ψ) —
    "K_gauche", "K_droite", "K_psi", "psi_valeur",
    "K_fonctionnelle", "K_domaine", "K_inclus", "K_dans_exposant",
    "K_gauche_inclus", "K_droite_inclus",
    "psi_dans_applications", "psi_dans_applications_sous_appartenance",
    "W_psi", "W_psi_fonctionnel", "W_psi_domaine", "W_psi_image_incluse",
]
