"""§III.3.5 — PROPOSITION 10 (currying), DIRECTION B : l'injection UNCURRY.

        ⊢ inf_egal_card( 𝓕(C; 𝓕(B;A)) ,  𝓕(B×C; A) )                (= (a^b)^c ≤ a^(b·c))

On construit l'UNCURRY  U : 𝓕(C; 𝓕(B;A)) ↪ 𝓕(B×C; A)  qui à g associe
l'application  (b,c) ↦ g(c)(b)  — DEUX évaluations « au sens de Bourbaki » :
g(c) = valeur(graphe_de(g), c) ∈ 𝓕(B;A), puis g(c)(b) = valeur(graphe_de(g(c)), b) ∈ A.

Au niveau VALEUR (k = couple (b,c) ∈ B×C, b=pr₁ k, c=pr₂ k) :
  val2(g,k) := valeur(graphe_de( valeur(graphe_de(g), pr₂ k, « m ») ), pr₁ k, « m »).
TERMES FIDÈLES AU PONT (comme prop10_close : f(x)=G(x)=valeur(graphe_de(f),x), PAS
valeur(f,x) sur le triple) :
  uncurry_graphe(g) := graphe_terme( B×C , val2(g,k) , « k » )   = { ((b,c), g(c)(b)) }
  uncurry_appli(g)  := ( ( uncurry_graphe(g) , B×C ) , A )        (la fonction EMBALLÉE)
  W_U := graphe_terme( 𝓕(C;𝓕(B;A)) , uncurry_appli(g) , « g » )  (le graphe de U)

est_injection_de(W_U, 𝓕(C;𝓕(B;A)), 𝓕(B×C;A)) — QUATRE conjoints (E.III.3.2) :
  • W_U_fonctionnel / W_U_domaine                              (C54, triviaux) ;
  • W_U_image_incluse  : image(W_U,dom) ⊂ 𝓕(B×C;A)   (BIEN-DÉFINITION) — LE CŒUR :
      uncurry_appli(g)∈𝓕(B×C;A) car uncurry_graphe(g)⊂(B×C)×A, chaque val2(g,k)∈A par
      valeur_application_dans_but appliqué DEUX FOIS (g(c)∈𝓕(B;A) le long de c∈C ;
      g(c)(b)∈A le long de b∈B) ; (b,c)∈B×C via pr₁/pr₂ ;
  • W_U_injective      : U(g₁)=U(g₂) ⟹ val2 coïncident sur B×C ⟹ g₁(c)(b)=g₂(c)(b)
      ∀b,c ⟹ g₁(c)=g₂(c) ∀c (application_egale_par_valeurs niv.0) ⟹ g₁=g₂ (niv.1).

Puis  S5 (témoin W_U) ⟹ inf_egal_uncurry() ⊢ inf_egal_card(𝓕(C;𝓕(B;A)), 𝓕(B×C;A)).

GABARIT : ensembles_prop9_close (Φ : W_phi_*, back-and-forth) et ensembles_prop10_close
(représentation fidèle au pont, niveaux imbriqués).  theorie_ensembles INCHANGÉE
(22 axiomes) ; aucun fichier existant modifié ; rien postulé.
"""
from __future__ import annotations

from bourbaki.logique.formule import (Terme, var, egal, et, impl, non, ou,
                     appartient, existe, pourtout, inclus, subst_t, subst_f)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.logique.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, equivalence_transitivite, instancie)
from bourbaki.logique.tactiques.tactiques_abrege_quantif import existe_elimination
from bourbaki.logique.tactiques.tactiques_abrege_egalite import (
    symetrie, composer_egalites, congruence_terme)

from bourbaki.cardinaux.ensembles_cardinaux import est_injection_de, inf_egal_card
from bourbaki.cardinaux.arithmetique.ensembles_graphe_de import graphe_de
from bourbaki.ensembles.fonctions.ii_3_6_fonction_terme.ensembles_fonction_terme import (
    graphe_terme_fonctionnel, membre_graphe_terme)
from bourbaki.cardinaux.ensembles_cantor import (
    graphe_terme_domaine, graphe_terme_valeur)
from bourbaki.ensembles.familles.ensembles_produit import couple_dans_produit_ssi
from bourbaki.ensembles.fonctions.hors_ii_3.ii_5_produit_famille.ensembles_application_valeur import (
    valeur_application_dans_but, application_egale_par_valeurs,
    egalite_valeurs_application)
from bourbaki.cardinaux.arithmetique.ensembles_produit_commute import (
    _projection_premiere_ab, _projection_seconde_ab,
    _membre_produit_pr1_ab, _membre_produit_pr2_ab)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# ═══════════════════════════════════════════════════════════════════════════════
#  LIANTS — choix sûrs (cf. PIÈGES de la mission)
# ───────────────────────────────────────────────────────────────────────────────
#   • « k »  : point courant du graphe-terme uncurry_graphe (le couple (b,c)) ;
#   • « g »  : point courant du graphe-terme W_U (la fonction g) ;
#   • « m »  : liant τ des DEUX valeur(·,·)  (= exotique, ≠ y,z de la machinerie
#              graphe-terme) ; recollé à « y » du PONT par α-renommage (CS1) ;
#   • « a »,« b » : liants des projections pr₁ k, pr₂ k (τ-scopes disjoints).
#   • « r »  : 2ᵉ coordonnée dans la décomposition C54 (z' = (k,r)) ;
#   • « z »  : trou « w » de l'axiome C54.
_PTK = "k"          # point courant de uncurry_graphe (couple (b,c))
_POINT = "g"        # point courant de W_U (la fonction)
_VAL = "m"          # liant τ des valeurs (exotique, recollé à « y »)
_DEC = "r"          # 2ᵉ coord de la décomposition C54


# ═══════════════════════════════════════════════════════════════════════════════
#  TERMES FIDÈLES AU PONT  :  val2(g,k) = g(pr₂ k)(pr₁ k)
# ═══════════════════════════════════════════════════════════════════════════════
def _gc(g, k):
    """g(c) = valeur(graphe_de(g), pr₂ k, « m »)   (l'application B→A « tranche en c »)."""
    return E.valeur(graphe_de(_t(g)), E.pr2(_t(k), "a", "b"), _VAL)


def _val2(g, k):
    """val2(g,k) = g(c)(b) = valeur(graphe_de( g(c) ), pr₁ k, « m »)   (= g(pr₂ k)(pr₁ k))."""
    return E.valeur(graphe_de(_gc(g, k)), E.pr1(_t(k), "a", "b"), _VAL)


def uncurry_graphe(g, b="B", c="C"):
    """uncurry_graphe(g) := graphe_terme( B×C , val2(g,k) , « k » ) = { ((b,c), g(c)(b)) }."""
    vb, vc = _t(b), _t(c)
    return E.graphe_terme(E.produit(vb, vc), _val2(g, var(_PTK)), _PTK)


def uncurry_appli(g, a="A", b="B", c="C"):
    """uncurry_appli(g) := ( ( uncurry_graphe(g) , B×C ) , A )   (la fonction EMBALLÉE B×C→A)."""
    va, vb, vc = _t(a), _t(b), _t(c)
    return E.couple(E.couple(uncurry_graphe(g, vb, vc), E.produit(vb, vc)), va)


# ── domaine / codomaine de U ────────────────────────────────────────────────────
def domaine_U(a="A", b="B", c="C"):
    """𝓕(C; 𝓕(B;A))   (source de U)."""
    va, vb, vc = _t(a), _t(b), _t(c)
    return E.applications(vc, E.applications(vb, va))


def codomaine_U(a="A", b="B", c="C"):
    """𝓕(B×C; A)   (but de U)."""
    va, vb, vc = _t(a), _t(b), _t(c)
    return E.applications(E.produit(vb, vc), va)


def W_U(a="A", b="B", c="C"):
    """W_U := graphe_terme( 𝓕(C;𝓕(B;A)) , uncurry_appli(g) , « g » )   (le GRAPHE de U)."""
    va, vb, vc = _t(a), _t(b), _t(c)
    return E.graphe_terme(domaine_U(va, vb, vc),
                          uncurry_appli(var(_POINT), va, vb, vc), _POINT)


# ═══════════════════════════════════════════════════════════════════════════════
#  CONJOINTS FACILES (C54)  :  W_U fonctionnel, dom W_U = 𝓕(C;𝓕(B;A))
# ═══════════════════════════════════════════════════════════════════════════════
def W_U_fonctionnel(a="A", b="B", c="C"):
    """⊢ est_fonctionnel(W_U).   (graphe-terme toujours fonctionnel, C54.)"""
    va, vb, vc = _t(a), _t(b), _t(c)
    return graphe_terme_fonctionnel(domaine_U(va, vb, vc),
                                    uncurry_appli(var(_POINT), va, vb, vc), _POINT, "y")


def W_U_domaine(a="A", b="B", c="C"):
    """⊢ dom(W_U) = 𝓕(C; 𝓕(B;A)).   (U définie sur toute la source ; C54.)"""
    va, vb, vc = _t(a), _t(b), _t(c)
    return graphe_terme_domaine(domaine_U(va, vb, vc),
                                uncurry_appli(var(_POINT), va, vb, vc), _POINT, "y", "z")


def W_U_valeur(g="h", a="A", b="B", c="C"):
    """{g ∈ 𝓕(C;𝓕(B;A))} ⊢ W_U(g) = uncurry_appli(g).   (point d'éval NOM ≠ g,k,m,a,b,y.)"""
    if not isinstance(g, str):
        raise ValueError("W_U_valeur : point d'évaluation = NOM (string)")
    va, vb, vc = _t(a), _t(b), _t(c)
    return graphe_terme_valeur(domaine_U(va, vb, vc),
                               uncurry_appli(var(_POINT), va, vb, vc), g, _POINT, "y")


def _cut(thm, paires):
    """Remplace chaque hypothèse `hyp` de `thm` par sa preuve `preuve`
    (loi_deduction puis modus_ponens), pour une liste de (hyp, preuve)."""
    out = thm
    for hyp_formule, preuve in paires:
        out = N.modus_ponens(preuve, N.loi_deduction(hyp_formule, out))
    return out


# ═══════════════════════════════════════════════════════════════════════════════
#  BIEN-DÉFINITION (LE CŒUR) :  val2(g,k) ∈ A   sous  g∈𝓕(C;𝓕(B;A)) et k∈B×C
# ───────────────────────────────────────────────────────────────────────────────
#   DEUX évaluations « au sens Bourbaki » (valeur_application_dans_but) :
#     g(c)   = valeur(graphe_de(g), pr₂ k) ∈ 𝓕(B;A)   le long de pr₂ k ∈ C ;
#     g(c)(b)= valeur(graphe_de(g(c)), pr₁ k) ∈ A       le long de pr₁ k ∈ B.
#   Recollage du τ-liant : valeur_application_dans_but produit la valeur avec « y »
#   (E.valeur défaut) ; nos termes utilisent « m » → α-renommage CS1 (N.alpha_tau).
# ═══════════════════════════════════════════════════════════════════════════════
def _rebind_m_y(vG, vx):
    """⊢ valeur(G, x, « m ») = valeur(G, x, « y »).   (α-renommage du liant τ, CS1.)"""
    r = appartient(E.couple(vx, var(_VAL)), vG)      # (x,m)∈G  (liant courant m)
    return N.alpha_tau(r, _VAL, "y")                 # valeur(G,x,m) = valeur(G,x,y)


def _gc_dans_FBA(vg, va, vb, vc, vk):
    """{ g∈𝓕(C;𝓕(B;A)), k∈B×C } ⊢ g(c) = valeur(graphe_de(g),pr₂ k,« m ») ∈ 𝓕(B;A).

    valeur_application_dans_but(g, C, 𝓕(B;A), pr₂ k) ⊢ valeur(graphe_de(g),pr₂ k,«y»)∈𝓕(B;A)
    sous {g∈𝓕(C;𝓕(B;A)), pr₂ k∈C} ; pr₂ k∈C via _membre_produit_pr2_ab (sous k∈B×C) ;
    recollage «y»→«m» (Leibniz sur _rebind_m_y) donne g(c)=valeur(·,«m»)∈𝓕(B;A)."""
    FBA = E.applications(vb, va)                      # 𝓕(B;A)
    pr2k = E.pr2(vk, "a", "b")                        # pr₂ k = c
    Gg = graphe_de(vg)
    gc_y = E.valeur(Gg, pr2k)                         # valeur(graphe_de(g),pr₂ k,«y»)
    gc_m = _gc(vg, vk)                                # valeur(graphe_de(g),pr₂ k,«m»)  = g(c)
    # pr₂ k ∈ C  (sous k∈B×C)
    pr2k_inC = _cut(_membre_produit_pr2_ab(vb, vc, vk),
                    [(appartient(vk, E.produit(vb, vc)),
                      N.assume(appartient(vk, E.produit(vb, vc))))])   # pr₂ k∈C  [k∈B×C]
    # valeur_application_dans_but : valeur(graphe_de(g),pr₂ k,«y»)∈𝓕(B;A)
    vadb = valeur_application_dans_but(vg, vc, FBA, pr2k)              # {g∈𝓕(C;𝓕(B;A)), pr₂ k∈C}⊢gc_y∈𝓕(B;A)
    gc_y_in = _cut(vadb, [(appartient(pr2k, vc), pr2k_inC)])          # {g∈…, k∈B×C} ⊢ gc_y∈𝓕(B;A)
    # g(c)=gc_m=gc_y  (Leibniz sur _rebind_m_y) → gc_m∈𝓕(B;A)
    reb = _rebind_m_y(Gg, pr2k)                                       # gc_m = gc_y
    gc_m_in = N.modus_ponens(gc_y_in, equivalence_arriere(
        N.modus_ponens(reb, N.s6(gc_m, gc_y, "w", appartient(var("w"), FBA)))))  # gc_m∈𝓕(B;A)
    return gc_m_in


def _val2_dans_A(vg, va, vb, vc, vk):
    """{ g∈𝓕(C;𝓕(B;A)), k∈B×C } ⊢ val2(g,k) = g(c)(b) ∈ A.

    Sous gc=g(c)∈𝓕(B;A) (_gc_dans_FBA), valeur_application_dans_but(gc, B, A, pr₁ k)
    ⊢ valeur(graphe_de(gc),pr₁ k,«y»)∈A sous {gc∈𝓕(B;A), pr₁ k∈B} ; pr₁ k∈B via
    _membre_produit_pr1_ab ; recollage «y»→«m» donne val2(g,k)=valeur(·,«m»)∈A."""
    pr1k = E.pr1(vk, "a", "b")                        # pr₁ k = b
    gc = _gc(vg, vk)                                  # g(c)  (= valeur(graphe_de(g),pr₂ k,«m»))
    Ggc = graphe_de(gc)
    val2_y = E.valeur(Ggc, pr1k)                      # valeur(graphe_de(gc),pr₁ k,«y»)
    val2_m = _val2(vg, vk)                            # valeur(graphe_de(gc),pr₁ k,«m»)  = val2(g,k)
    # gc∈𝓕(B;A)
    gc_in = _gc_dans_FBA(vg, va, vb, vc, vk)          # {g∈…, k∈B×C} ⊢ gc∈𝓕(B;A)
    # pr₁ k∈B  (sous k∈B×C)
    pr1k_inB = _cut(_membre_produit_pr1_ab(vb, vc, vk),
                    [(appartient(vk, E.produit(vb, vc)),
                      N.assume(appartient(vk, E.produit(vb, vc))))])   # pr₁ k∈B  [k∈B×C]
    # valeur_application_dans_but : valeur(graphe_de(gc),pr₁ k,«y»)∈A
    vadb = valeur_application_dans_but(gc, vb, va, pr1k)              # {gc∈𝓕(B;A), pr₁ k∈B}⊢val2_y∈A
    val2_y_in = _cut(vadb, [(appartient(gc, E.applications(vb, va)), gc_in),
                            (appartient(pr1k, vb), pr1k_inB)])        # {g∈…, k∈B×C} ⊢ val2_y∈A
    # val2(g,k)=val2_m=val2_y  (Leibniz) → val2_m∈A
    reb = _rebind_m_y(Ggc, pr1k)                                      # val2_m = val2_y
    val2_m_in = N.modus_ponens(val2_y_in, equivalence_arriere(
        N.modus_ponens(reb, N.s6(val2_m, val2_y, "w", appartient(var("w"), va)))))  # val2_m∈A
    return val2_m_in


# ═══════════════════════════════════════════════════════════════════════════════
#  uncurry_graphe(g) ⊂ (B×C)×A   (BIEN-DÉFINITION du graphe, via _val2_dans_A)
# ═══════════════════════════════════════════════════════════════════════════════
def _membre_produit_ssi(vu, vv, vA, vB):
    """⊢ ((u,v)∈A×B) ⇔ (u∈A et v∈B)   (couple_dans_produit_ssi, TERMES)."""
    return couple_dans_produit_ssi(vu, vv, vA, vB)


def uncurry_graphe_inclus(g="g", a="A", b="B", c="C"):
    """{ g ∈ 𝓕(C;𝓕(B;A)) } ⊢ uncurry_graphe(g) ⊂ (B×C)×A.

    BIEN-DÉFINITION du graphe.  uncurry_graphe(g)={ (k, val2(g,k)) | k∈B×C }.  Tout
    z'∈uncurry_graphe(g) s'écrit (k,r) avec k∈B×C et r=val2(g,k) (axiome C54, liant
    valeur « r »).  Or, sous g∈𝓕(C;𝓕(B;A)) et k∈B×C, val2(g,k)∈A (_val2_dans_A, le
    DOUBLE valeur_application_dans_but) — i.e. r∈A.  Avec k∈B×C, (k,r)∈(B×C)×A, d'où
    z'=(k,r)∈(B×C)×A.  Conclusion (∀z')(z'∈uncurry_graphe ⇒ z'∈(B×C)×A)."""
    vg, va, vb, vc = _t(g), _t(a), _t(b), _t(c)
    BC = E.produit(vb, vc)                              # B×C
    BCA = E.produit(BC, va)                             # (B×C)×A
    T = _val2(vg, var(_PTK))                            # val2(g,k)  (point courant k)
    ug = uncurry_graphe(vg, vb, vc)                     # graphe_terme(B×C, T, "k")
    h_g = appartient(vg, domaine_U(va, vb, vc))         # g∈𝓕(C;𝓕(B;A))

    vz = var("z")
    vk, vr = var(_PTK), var(_DEC)
    # axiome C54 de uncurry_graphe, sur z' : z'∈ug ⇔ (∃k)(∃r)(z'=(k,r) et k∈B×C et r=T)
    th = E.theorie_graphe_terme(BC, T, _PTK, _DEC, "z")
    ax = N.axiome(th, E.axiome_graphe_terme(BC, T, _PTK, _DEC, "z"))   # (∀z)(...)
    car = instancie(ax, vz)
    body = et(et(egal(vz, E.couple(vk, vr)), appartient(vk, BC)), egal(vr, T))
    hb = N.assume(body)
    z_eq = conjonction_elim_gauche(conjonction_elim_gauche(hb))    # z'=(k,r)
    k_inBC = conjonction_elim_droite(conjonction_elim_gauche(hb))  # k∈B×C
    r_eq_T = conjonction_elim_droite(hb)                          # r=T=val2(g,k)

    # T = val2(g,k) ∈ A  (sous g∈𝓕(C;𝓕(B;A)) et k∈B×C)
    T_inA = _cut(_val2_dans_A(vg, va, vb, vc, vk),
                 [(appartient(vk, BC), k_inBC)])                  # {g∈…} ⊢ T∈A  [k∈B×C déchargé]
    # r=T et T∈A ⇒ r∈A (Leibniz)
    r_inA = N.modus_ponens(T_inA, equivalence_arriere(
        N.modus_ponens(r_eq_T, N.s6(vr, T, "w", appartient(var("w"), va)))))  # r∈A
    # (k,r)∈(B×C)×A
    kr_in_BCA = N.modus_ponens(conjonction_intro(k_inBC, r_inA),
        equivalence_arriere(_membre_produit_ssi(vk, vr, BC, va)))   # (k,r)∈(B×C)×A
    # z'=(k,r) ⇒ z'∈(B×C)×A (Leibniz)
    z_in_BCA = N.modus_ponens(kr_in_BCA, equivalence_arriere(
        N.modus_ponens(z_eq, N.s6(vz, E.couple(vk, vr), "w",
                                  appartient(var("w"), BCA)))))     # z'∈(B×C)×A
    imp_body = N.loi_deduction(body, z_in_BCA)
    elim = existe_elimination(existe_elimination(imp_body, _DEC), _PTK)
    hz = N.assume(appartient(vz, ug))
    ex_body = N.modus_ponens(hz, equivalence_avant(car))
    z_in_BCA_f = N.modus_ponens(ex_body, elim)
    imp_z = N.loi_deduction(appartient(vz, ug), z_in_BCA_f)        # {g∈…} ⊢ z'∈ug ⇒ z'∈(B×C)×A
    return N.generalisation("z", imp_z)                           # {g∈…} ⊢ uncurry_graphe(g)⊂(B×C)×A


def uncurry_graphe_fonctionnel(g="g", a="A", b="B", c="C"):
    """⊢ est_fonctionnel(uncurry_graphe(g)).   (k ↦ val2(g,k) a une valeur unique ; C54.)"""
    vg, va, vb, vc = _t(g), _t(a), _t(b), _t(c)
    T = _val2(vg, var(_PTK))
    return graphe_terme_fonctionnel(E.produit(vb, vc), T, _PTK, "y")


def uncurry_graphe_domaine(g="g", a="A", b="B", c="C"):
    """⊢ dom(uncurry_graphe(g)) = B×C.   (k ↦ val2(g,k) définie sur tout B×C ; C54.)"""
    vg, va, vb, vc = _t(g), _t(a), _t(b), _t(c)
    T = _val2(vg, var(_PTK))
    return graphe_terme_domaine(E.produit(vb, vc), T, _PTK, "y", "z")


def uncurry_graphe_dans_exposant(g="g", a="A", b="B", c="C"):
    """{ g ∈ 𝓕(C;𝓕(B;A)) } ⊢ uncurry_graphe(g) ∈ A^(B×C).

    axiome_exposant(B×C,A) : G∈A^(B×C) ⇔ (G⊂(B×C)×A et G fonctionnel et dom G=B×C).
    Les trois conjoints : uncurry_graphe_inclus (sous g∈dom_U), uncurry_graphe_fonctionnel
    (C54), uncurry_graphe_domaine (C54)."""
    vg, va, vb, vc = _t(g), _t(a), _t(b), _t(c)
    BC = E.produit(vb, vc)
    ug = uncurry_graphe(vg, vb, vc)
    ax = N.axiome(E.theorie_exposant(BC, va), E.axiome_exposant(BC, va))   # (∀G)(...)
    car = instancie(ax, ug)        # ug∈A^(B×C) ⇔ (ug⊂(B×C)×A et ug fonct et dom ug=B×C)
    incl = uncurry_graphe_inclus(vg, va, vb, vc)         # ug⊂(B×C)×A  [sous g∈…]
    fonct = uncurry_graphe_fonctionnel(vg, va, vb, vc)   # est_fonctionnel(ug)
    dom_eq = uncurry_graphe_domaine(vg, va, vb, vc)      # dom ug=B×C
    corps = conjonction_intro(conjonction_intro(incl, fonct), dom_eq)
    return N.modus_ponens(corps, equivalence_arriere(car))   # ug∈A^(B×C)  [sous g∈…]


def uncurry_appli_dans_codomaine(g="g", a="A", b="B", c="C"):
    """{ g ∈ 𝓕(C;𝓕(B;A)) } ⊢ uncurry_appli(g) = ((uncurry_graphe(g),B×C),A) ∈ 𝓕(B×C;A).

    BIEN-DÉFINITION COMPLÈTE de U : l'image U(g)=uncurry_appli(g) est une vraie
    application B×C→A dès que g∈𝓕(C;𝓕(B;A)).  axiome_applications(B×C,A) : t∈𝓕(B×C;A)
    ⇔ (∃G)(t=((G,B×C),A) et G∈A^(B×C)).  Témoin G:=uncurry_graphe(g) : uncurry_appli(g)
    =((uncurry_graphe(g),B×C),A) (réflexivité) et uncurry_graphe(g)∈A^(B×C)
    (uncurry_graphe_dans_exposant, sous g∈dom_U)."""
    vg, va, vb, vc = _t(g), _t(a), _t(b), _t(c)
    BC = E.produit(vb, vc)
    ug = uncurry_graphe(vg, vb, vc)
    triple = uncurry_appli(vg, va, vb, vc)               # ((uncurry_graphe(g),B×C),A)
    ax = N.axiome(E.theorie_applications(BC, va), E.axiome_applications(BC, va))  # (∀t)(...)
    car = instancie(ax, triple)    # triple∈𝓕(B×C;A) ⇔ (∃G)(triple=((G,B×C),A) et G∈A^(B×C))
    in_exp = uncurry_graphe_dans_exposant(vg, va, vb, vc)   # uncurry_graphe(g)∈A^(B×C)  [sous g∈…]
    refl = N.reflexivite(triple)                          # triple=((uncurry_graphe(g),B×C),A)
    wit = conjonction_intro(refl, in_exp)
    body = et(egal(triple, E.couple(E.couple(var("G"), BC), va)),
              appartient(var("G"), E.exposant(BC, va)))
    ex_G = N.modus_ponens(wit, N.s5(body, ug, "G"))       # (∃G)body
    return N.modus_ponens(ex_G, equivalence_arriere(car))  # triple∈𝓕(B×C;A)  [sous g∈…]


# ═══════════════════════════════════════════════════════════════════════════════
#  CONJOINT image :  image(W_U, 𝓕(C;𝓕(B;A))) ⊂ 𝓕(B×C;A)   (BIEN-DÉFINITION de U)
# ═══════════════════════════════════════════════════════════════════════════════
def _U_cod_en_point(va, vb, vc, vt, t_in_thm):
    """De {t∈dom_U} (t_in_thm) ⊢ U(t) = uncurry_appli(t) ∈ cod, par instanciation-terme de
    uncurry_appli_dans_codomaine au point t (hyp t∈dom déchargée)."""
    dom = domaine_U(va, vb, vc)
    base = uncurry_appli_dans_codomaine("g", va, vb, vc)   # {g∈dom} ⊢ U(g)∈cod
    base_imp = N.loi_deduction(appartient(var("g"), dom), base)   # g∈dom ⇒ U(g)∈cod
    gen = N.generalisation("g", base_imp)            # (∀g)(g∈dom ⇒ U(g)∈cod)
    inst = instancie(gen, vt)                        # t∈dom ⇒ U(t)∈cod
    return N.modus_ponens(t_in_thm, inst)            # U(t)∈cod   [hyp t∈dom]


def W_U_image_incluse(a="A", b="B", c="C"):
    """⊢ image(W_U, 𝓕(C;𝓕(B;A))) ⊂ 𝓕(B×C;A).

    BIEN-DÉFINITION de U.  z∈W_U⟨dom⟩ ⇔ (∃t)(t∈dom et (t,z)∈W_U) ; (t,z)∈W_U ⇔
    (t∈dom et z=U(t)) (membre_graphe_terme), donc z=U(t) avec t∈dom ;
    uncurry_appli_dans_codomaine ⊢ U(t)∈cod, d'où z∈cod (Leibniz).  Conclusion = inclusion.
    MIROIR de W_phi_image_incluse (gabarit prop9_close)."""
    va, vb, vc = _t(a), _t(b), _t(c)
    dom = domaine_U(va, vb, vc)
    cod = codomaine_U(va, vb, vc)
    W = W_U(va, vb, vc)
    UU = uncurry_appli(var(_POINT), va, vb, vc)      # U(g), point g
    vz, vt = var("z"), var("t")
    from bourbaki.logique.tactiques.tactiques_abrege_quantif import alpha_existe

    # z∈W⟨dom⟩ ⇔ (∃t)(t∈dom et (t,z)∈W)  (AXIOME_IMAGE ; liant frais α-renommé t)
    ax_img = N.axiome(E.theorie_ensembles(), E.AXIOME_IMAGE)
    img0 = instancie(instancie(instancie(ax_img, W), dom), vz)
    impl_LtoEX = img0.conclusion.sous[0].sous[0].sous[0]
    rhs_ex = impl_LtoEX.sous[1]
    assert rhs_ex.tag == "exists"
    nom = rhs_ex.lieur
    inner = et(appartient(var(nom), dom), appartient(E.couple(var(nom), vz), W))
    ren = alpha_existe(nom, "t", inner)
    img_car = equivalence_transitivite(img0, ren)    # z∈W⟨dom⟩ ⇔ (∃t)(t∈dom et (t,z)∈W)

    # (t,z)∈W ⇔ (t∈dom et z=U(t))   [membre_graphe_terme, point g, coords t,z]
    mem = membre_graphe_terme(dom, UU, "t", "z", _POINT, "y")  # ((t,z)∈W)⇔(t∈dom et z=U[t])
    U_t = subst_t(vt, _POINT, UU)                    # U(t) = U[g:=t]

    body = et(appartient(vt, dom), appartient(E.couple(vt, vz), W))
    hb = N.assume(body)
    t_in = conjonction_elim_gauche(hb)               # t∈dom
    tz_in = conjonction_elim_droite(hb)              # (t,z)∈W
    cond = N.modus_ponens(tz_in, equivalence_avant(mem))   # t∈dom et z=U(t)
    z_eq = conjonction_elim_droite(cond)             # z=U(t)
    # U(t)∈cod
    U_t_in = _U_cod_en_point(va, vb, vc, vt, t_in)   # U(t)∈cod
    # z∈cod  (z=U(t), Leibniz)
    z_in_cod = N.modus_ponens(U_t_in, equivalence_arriere(N.modus_ponens(
        z_eq, N.s6(vz, U_t, "w", appartient(var("w"), cod)))))   # z∈cod
    ex_imp = existe_elimination(N.loi_deduction(body, z_in_cod), "t")  # (∃t)body ⇒ z∈cod
    h_z = N.assume(appartient(vz, E.image(W, dom)))
    ex = N.modus_ponens(h_z, equivalence_avant(img_car))   # (∃t)body
    z_in = N.modus_ponens(ex, ex_imp)                # z∈cod
    return N.generalisation("z", N.loi_deduction(appartient(vz, E.image(W, dom)), z_in))


# ═══════════════════════════════════════════════════════════════════════════════
#  INJECTIVITÉ de U  :  U(g₁)=U(g₂) ⇒ g₁=g₂.  Back-and-forth REDOUBLÉ (deux niveaux).
# ───────────────────────────────────────────────────────────────────────────────
#   U(gᵢ)=uncurry_appli(gᵢ) ⇒ (strip triple) ug₁=ug₂ ⇒ (graphe_terme_valeur sur k=(b,c))
#   val2(g₁,(b,c))=val2(g₂,(b,c)) ⇒ (pr₁,pr₂) g₁(c)(b)=g₂(c)(b) ⇒ (niv.0 sur b∈B)
#   g₁(c)=g₂(c) ⇒ (niv.1 sur c∈C) g₁=g₂.
# ═══════════════════════════════════════════════════════════════════════════════
def _gval(g, cterm):
    """g(c) « direct » = valeur(graphe_de(g), c, « m »)   (c = TERME, pas pr₂ d'un couple).

    Pour k=(b,c), _gc(g,k)=valeur(graphe_de(g),pr₂ k,«m») ; après pr₂((b,c))=c on a
    _gc(g,(b,c)) = _gval(g,c)."""
    return E.valeur(graphe_de(_t(g)), _t(cterm), _VAL)


def _val2_egal_gval(vg, vb_t, vc_t):
    """⊢ val2(g,(b,c)) = valeur(graphe_de(g(c)), b, « y »).   (identité de termes, sans hyp.)

    val2(g,(b,c)) = valeur(graphe_de( valeur(graphe_de(g),pr₂(b,c),«m») ), pr₁(b,c), «m»).
    pr₂((b,c))=c, pr₁((b,c))=b (projections), puis rebind «m»→«y».  Le résultat est
    valeur(graphe_de(_gval(g,c)), b, «y»), forme attendue par egalite_valeurs_application."""
    bc = E.couple(vb_t, vc_t)
    Gg = graphe_de(vg)
    pr1bc = E.pr1(bc, "a", "b")
    pr2bc = E.pr2(bc, "a", "b")
    gc_pr2 = _gc(vg, bc)                              # valeur(graphe_de(g),pr₂(b,c),«m»)
    gc_c = _gval(vg, vc_t)                            # valeur(graphe_de(g),c,«m»)  (= g(c))
    val2_bc = _val2(vg, bc)                           # valeur(graphe_de(gc_pr2),pr₁(b,c),«m»)

    # gc_pr2 = gc_c   (pr₂((b,c))=c → congruence valeur(graphe_de(g),·,«m»))
    pr2_eq_c = _projection_seconde_ab(vb_t, vc_t, "a", "b")   # pr₂((b,c))=c
    gc_eq = N.modus_ponens(pr2_eq_c,
        congruence_terme(pr2bc, vc_t, E.valeur(Gg, var("w"), _VAL)))   # gc_pr2 = gc_c
    # graphe_de(gc_pr2) = graphe_de(gc_c)   (congruence)
    Ggc_eq = N.modus_ponens(gc_eq,
        congruence_terme(gc_pr2, gc_c, graphe_de(var("w"))))          # graphe_de(gc_pr2)=graphe_de(gc_c)
    # val2(g,(b,c)) = valeur(graphe_de(gc_c), pr₁(b,c), «m»)   (réécrire graphe_de(gc_pr2))
    step1 = N.modus_ponens(Ggc_eq,
        congruence_terme(graphe_de(gc_pr2), graphe_de(gc_c),
                         E.valeur(var("w"), pr1bc, _VAL)))            # val2_bc = valeur(graphe_de(gc_c),pr₁(b,c),«m»)
    # pr₁((b,c))=b → valeur(graphe_de(gc_c), pr₁(b,c), «m») = valeur(graphe_de(gc_c), b, «m»)
    pr1_eq_b = _projection_premiere_ab(vb_t, vc_t, "a", "b")          # pr₁((b,c))=b
    step2 = N.modus_ponens(pr1_eq_b,
        congruence_terme(pr1bc, vb_t, E.valeur(graphe_de(gc_c), var("w"), _VAL)))  # =valeur(graphe_de(gc_c),b,«m»)
    # rebind «m»→«y»
    reb = _rebind_m_y(graphe_de(gc_c), vb_t)                          # valeur(·,b,«m»)=valeur(·,b,«y»)
    # chaîne : val2_bc = valeur(graphe_de(gc_c),pr₁(b,c),«m») = valeur(graphe_de(gc_c),b,«m») = valeur(graphe_de(gc_c),b,«y»)
    chain = composer_egalites(composer_egalites(step1, step2), reb)
    return chain                                     # val2(g,(b,c)) = valeur(graphe_de(g(c)), b, «y»)


def _ug_valeur_couple(vg, vb, vc, vu, vv):
    """{ u∈B, v∈C } ⊢ uncurry_graphe(g)((u,v)) = val2(g,(u,v)).

    graphe_terme_valeur (point frais « kk », généralisé puis instancié au TERME (u,v),
    car le point d'évaluation doit être un NOM) : ug(kk)=T[k:=kk] ; T[k:=(u,v)]=val2(g,(u,v)).
    (u,v)∈B×C via couple_dans_produit_ssi."""
    BC = E.produit(vb, vc)
    T = _val2(vg, var(_PTK))                          # val2(g,k)  (point « k »)
    uv = E.couple(vu, vv)
    _POINT_EV = "kk"                                  # nom de point frais ≠ binder « k »
    gtv = graphe_terme_valeur(BC, T, _POINT_EV, _PTK, "y")   # {kk∈B×C} ⊢ ug(kk)=T[k:=kk]
    gtv_imp = N.loi_deduction(appartient(var(_POINT_EV), BC), gtv)
    gtv_gen = N.generalisation(_POINT_EV, gtv_imp)    # (∀kk)(kk∈B×C ⇒ ug(kk)=T[k:=kk])
    # (u,v)∈B×C
    h_uB = N.assume(appartient(vu, vb))
    h_vC = N.assume(appartient(vv, vc))
    uv_in_BC = N.modus_ponens(conjonction_intro(h_uB, h_vC),
        equivalence_arriere(couple_dans_produit_ssi(vu, vv, vb, vc)))   # (u,v)∈B×C
    return N.modus_ponens(uv_in_BC, instancie(gtv_gen, uv))   # ug((u,v))=val2(g,(u,v))


def _val_coincide_niv0(vg1, vg2, vb, vc, vu, vv):
    """{ uncurry_graphe(g₁)=uncurry_graphe(g₂), u∈B, v∈C }
       ⊢ valeur(graphe_de(g₁(v)),u,«y») = valeur(graphe_de(g₂(v)),u,«y»).

    ug₁((u,v))=val2(g₁,(u,v)), ug₂((u,v))=val2(g₂,(u,v)) (_ug_valeur_couple) ; ug₁=ug₂
    ⇒ ug₁((u,v))=ug₂((u,v)) (congruence) ⇒ val2(g₁,(u,v))=val2(g₂,(u,v)) ; chaque
    val2(gᵢ,(u,v))=valeur(graphe_de(gᵢ(v)),u,«y») (_val2_egal_gval).  Chaîner."""
    ug1 = uncurry_graphe(vg1, vb, vc)
    ug2 = uncurry_graphe(vg2, vb, vc)
    uv = E.couple(vu, vv)
    val2_1 = _val2(vg1, uv)                            # val2(g₁,(u,v))
    val2_2 = _val2(vg2, uv)                            # val2(g₂,(u,v))
    gv1_u = E.valeur(graphe_de(_gval(vg1, vv)), vu, "y")   # valeur(graphe_de(g₁(v)),u,«y»)
    gv2_u = E.valeur(graphe_de(_gval(vg2, vv)), vu, "y")
    # ug_i((u,v)) = val2(g_i,(u,v))
    uval1 = _ug_valeur_couple(vg1, vb, vc, vu, vv)    # ug₁((u,v))=val2(g₁,(u,v))
    uval2 = _ug_valeur_couple(vg2, vb, vc, vu, vv)    # ug₂((u,v))=val2(g₂,(u,v))
    # ug₁=ug₂ ⇒ ug₁((u,v))=ug₂((u,v))
    h_ug_eq = N.assume(egal(ug1, ug2))
    ug_uv_eq = N.modus_ponens(h_ug_eq,
        congruence_terme(ug1, ug2, E.valeur(var("w"), uv)))   # ug₁((u,v))=ug₂((u,v))
    # val2(g₁,(u,v)) = ug₁((u,v)) = ug₂((u,v)) = val2(g₂,(u,v))
    val2_1_eq_ug1 = N.modus_ponens(uval1, symetrie(E.valeur(ug1, uv), val2_1))  # val2(g₁,·)=ug₁(·)
    val2_eq = composer_egalites(composer_egalites(val2_1_eq_ug1, ug_uv_eq), uval2)  # val2(g₁,·)=val2(g₂,·)
    # val2(g_i,(u,v)) = valeur(graphe_de(g_i(v)),u,«y»)  (_val2_egal_gval)
    id1 = _val2_egal_gval(vg1, vu, vv)                # val2(g₁,(u,v))=gv1_u
    id2 = _val2_egal_gval(vg2, vu, vv)                # val2(g₂,(u,v))=gv2_u
    # gv1_u = val2(g₁,(u,v)) = val2(g₂,(u,v)) = gv2_u
    gv1_eq_val2_1 = N.modus_ponens(id1, symetrie(val2_1, gv1_u))   # gv1_u=val2(g₁,·)
    return composer_egalites(composer_egalites(gv1_eq_val2_1, val2_eq), id2)  # gv1_u=gv2_u


def _gval_dans_FBA(vg, va, vb, vc, vv):
    """{ g∈𝓕(C;𝓕(B;A)), v∈C } ⊢ g(v) = valeur(graphe_de(g),v,«m») ∈ 𝓕(B;A).

    valeur_application_dans_but(g, C, 𝓕(B;A), v) ⊢ valeur(graphe_de(g),v,«y»)∈𝓕(B;A) ;
    rebind «y»→«m» (Leibniz)."""
    FBA = E.applications(vb, va)
    Gg = graphe_de(vg)
    gv_y = E.valeur(Gg, vv)                            # valeur(graphe_de(g),v,«y»)
    gv_m = _gval(vg, vv)                               # valeur(graphe_de(g),v,«m»)  = g(v)
    vadb = valeur_application_dans_but(vg, vc, FBA, vv)   # {g∈𝓕(C;𝓕(B;A)), v∈C}⊢gv_y∈𝓕(B;A)
    reb = _rebind_m_y(Gg, vv)                          # gv_m = gv_y
    return N.modus_ponens(vadb, equivalence_arriere(
        N.modus_ponens(reb, N.s6(gv_m, gv_y, "w", appartient(var("w"), FBA)))))   # gv_m∈𝓕(B;A)


def _gval_egal_niv0(vg1, vg2, va, vb, vc, vv):
    """{ uncurry_graphe(g₁)=uncurry_graphe(g₂), g₁∈𝓕(C;𝓕(B;A)), g₂∈𝓕(C;𝓕(B;A)), v∈C }
       ⊢ g₁(v) = g₂(v).

    NIVEAU 0 du back-and-forth.  Les valeurs coïncident sur B (_val_coincide_niv0,
    généralisé sur le point « x ») ; g₁(v),g₂(v)∈𝓕(B;A) (_gval_dans_FBA) ;
    application_egale_par_valeurs ⊢ g₁(v)=g₂(v)."""
    FBA = E.applications(vb, va)
    gv1 = _gval(vg1, vv)                               # g₁(v)
    gv2 = _gval(vg2, vv)                               # g₂(v)
    ug1 = uncurry_graphe(vg1, vb, vc)
    ug2 = uncurry_graphe(vg2, vb, vc)
    # (∀x)(x∈B ⇒ valeur(graphe_de(g₁(v)),x)=valeur(graphe_de(g₂(v)),x))   [hyp ug₁=ug₂, v∈C]
    coinc_x = _val_coincide_niv0(vg1, vg2, vb, vc, var("x"), vv)   # {x∈B,v∈C,ug eq}⊢ valeurs(x)
    coinc_imp = N.loi_deduction(appartient(var("x"), vb), coinc_x) # {v∈C,ug eq}⊢ x∈B ⇒ valeurs(x)
    vals = N.generalisation("x", coinc_imp)            # {v∈C,ug eq} ⊢ egalite_valeurs_application(g₁(v),g₂(v),B)
    # g₁(v),g₂(v)∈𝓕(B;A)
    gv1_in = _gval_dans_FBA(vg1, va, vb, vc, vv)       # {g₁∈…,v∈C} ⊢ g₁(v)∈𝓕(B;A)
    gv2_in = _gval_dans_FBA(vg2, va, vb, vc, vv)       # {g₂∈…,v∈C} ⊢ g₂(v)∈𝓕(B;A)
    # application_egale_par_valeurs : {g₁(v),g₂(v)∈𝓕(B;A), vals} ⊢ g₁(v)=g₂(v)
    aev = application_egale_par_valeurs(gv1, gv2, vb, va)
    return _cut(aev, [
        (appartient(gv1, FBA), gv1_in),
        (appartient(gv2, FBA), gv2_in),
        (egalite_valeurs_application(gv1, gv2, vb), vals)])   # g₁(v)=g₂(v)


def _strip_triple(triple_eq, g1, mid, top, g2):
    """De ⊢ ((g₁,mid),top)=((g₂,mid),top), tire ⊢ g₁=g₂.  (deux décompos de couples.)"""
    from bourbaki.ensembles.base.ensembles_couples import couple_egal_implique_composantes
    inner1 = E.couple(g1, mid)
    inner2 = E.couple(g2, mid)
    comp1 = N.modus_ponens(triple_eq,
                           couple_egal_implique_composantes(inner1, top, inner2, top))
    inner_eq = conjonction_elim_gauche(comp1)        # (g₁,mid)=(g₂,mid)
    comp2 = N.modus_ponens(inner_eq,
                           couple_egal_implique_composantes(g1, mid, g2, mid))
    return conjonction_elim_gauche(comp2)            # g₁=g₂


def _gval_egal_donne_valeur_y(vg1, vg2, va, vb, vc):
    """{ uncurry_graphe(g₁)=uncurry_graphe(g₂), g₁,g₂∈𝓕(C;𝓕(B;A)) }
       ⊢ (∀x)(x∈C ⇒ valeur(graphe_de(g₁),x,«y») = valeur(graphe_de(g₂),x,«y»)).

    NIVEAU 1 (préparation).  Pour v∈C : g₁(v)=g₂(v) (_gval_egal_niv0, dont le liant
    INTERNE de niveau 0 est « x ») ; g₁(v)=valeur(graphe_de(g₁),v,«m»), rebind «m»→«y»
    des deux côtés donne valeur(graphe_de(g₁),v,«y»)=valeur(graphe_de(g₂),v,«y») ;
    généraliser sur « v » (≠ « x » interne) puis α-renommer « v »→« x » pour s'apparier
    à egalite_valeurs_application(g₁,g₂,C) (binder « x »)."""
    G1, G2 = graphe_de(vg1), graphe_de(vg2)
    vv = var("v")                                     # C-élément (≠ « x » interne de niveau 0)
    gv1 = _gval(vg1, vv)                              # valeur(graphe_de(g₁),v,«m»)
    gv2 = _gval(vg2, vv)
    g1y = E.valeur(G1, vv)                            # valeur(graphe_de(g₁),v,«y»)
    g2y = E.valeur(G2, vv)
    # g₁(v)=g₂(v)  [hyp ug eq, g_i∈…, v∈C]
    eq_m = _gval_egal_niv0(vg1, vg2, va, vb, vc, vv)  # gv1=gv2  (binder « m »)
    # rebind « m »→« y » des deux côtés
    reb1 = _rebind_m_y(G1, vv)                        # gv1 = g1y
    reb2 = _rebind_m_y(G2, vv)                        # gv2 = g2y
    # g1y = gv1 = gv2 = g2y
    g1y_eq_gv1 = N.modus_ponens(reb1, symetrie(gv1, g1y))   # g1y=gv1
    chain = composer_egalites(composer_egalites(g1y_eq_gv1, eq_m), reb2)   # g1y=g2y  [hyps]
    imp = N.loi_deduction(appartient(vv, vc), chain)
    raw = N.generalisation("v", imp)                 # (∀v)(v∈C⇒...)  [hyp ug eq, g_i∈…]
    # α-renommer (∀v)P → (∀x)P (instancier puis re-généraliser) pour matcher egalite_valeurs_application
    return N.generalisation("x", instancie(raw, var("x")))   # (∀x)(x∈C⇒g1y=g2y)


def uncurry_injective_sous_appartenance(g1="g1", g2="g2", a="A", b="B", c="C"):
    """{ g₁∈𝓕(C;𝓕(B;A)), g₂∈𝓕(C;𝓕(B;A)), U(g₁)=U(g₂) } ⊢ g₁ = g₂.

    INJECTIVITÉ de U (cœur, back-and-forth REDOUBLÉ).  U(gᵢ)=uncurry_appli(gᵢ)=
    ((uncurry_graphe(gᵢ),B×C),A) ; strip du triple ⇒ uncurry_graphe(g₁)=uncurry_graphe(g₂).
    NIVEAU 0 : g₁(v)=g₂(v) ∀v∈C, d'où valeurs de g₁,g₂ coïncident sur C
    (_gval_egal_donne_valeur_y).  NIVEAU 1 : application_egale_par_valeurs(g₁,g₂,C,𝓕(B;A))
    ⇒ g₁=g₂."""
    vg1, vg2, va, vb, vc = _t(g1), _t(g2), _t(a), _t(b), _t(c)
    BC = E.produit(vb, vc)
    FBA = E.applications(vb, va)
    ua1 = uncurry_appli(vg1, va, vb, vc)              # ((uncurry_graphe(g₁),B×C),A)
    ua2 = uncurry_appli(vg2, va, vb, vc)
    ug1 = uncurry_graphe(vg1, vb, vc)
    ug2 = uncurry_graphe(vg2, vb, vc)
    h_U = N.assume(egal(ua1, ua2))                    # U(g₁)=U(g₂)  (= uncurry_appli eq)
    # strip : ((ug₁,B×C),A)=((ug₂,B×C),A) ⇒ ug₁=ug₂
    ug_eq = _strip_triple(h_U, ug1, BC, va, ug2)      # ug₁=ug₂
    # NIVEAU 1 préparé : (∀x)(x∈C⇒valeur(graphe_de(g₁),x)=valeur(graphe_de(g₂),x))  [ug eq]
    vals = _gval_egal_donne_valeur_y(vg1, vg2, va, vb, vc)   # {ug eq, g_i∈…} ⊢ vals
    vals = _cut(vals, [(egal(ug1, ug2), ug_eq)])      # {g_i∈…, U eq} ⊢ vals
    # application_egale_par_valeurs : {g₁,g₂∈𝓕(C;𝓕(B;A)), vals} ⊢ g₁=g₂
    aev = application_egale_par_valeurs(vg1, vg2, vc, FBA)
    return _cut(aev, [
        (appartient(vg1, domaine_U(va, vb, vc)), N.assume(appartient(vg1, domaine_U(va, vb, vc)))),
        (appartient(vg2, domaine_U(va, vb, vc)), N.assume(appartient(vg2, domaine_U(va, vb, vc)))),
        (egalite_valeurs_application(vg1, vg2, vc), vals)])   # g₁=g₂


def W_U_injective(a="A", b="B", c="C"):
    """⊢ injective_dans(W_U, 𝓕(C;𝓕(B;A))).

    MIROIR de W_phi_injective.  W_U(·)=uncurry_appli(·) (W_U_valeur, sous ·∈dom) ⇒
    U(g₁)=U(g₂) ; uncurry_injective_sous_appartenance ⇒ g₁=g₂.  Variables-fonction
    « g1 », « g2 » SÛRES (≠ liants internes), α-renommées ENSUITE en « u », « up »
    pour s'apparier à la forme injective_dans attendue par est_injection_de."""
    va, vb, vc = _t(a), _t(b), _t(c)
    dom = domaine_U(va, vb, vc)
    Wt = W_U(va, vb, vc)
    vg1, vg2 = var("g1"), var("g2")
    ua1 = uncurry_appli(vg1, va, vb, vc)
    ua2 = uncurry_appli(vg2, va, vb, vc)

    hyp = et(et(appartient(vg1, dom), appartient(vg2, dom)),
             egal(E.valeur(Wt, vg1), E.valeur(Wt, vg2)))   # g₁∈dom et g₂∈dom et W(g₁)=W(g₂)
    h = N.assume(hyp)
    g1_in = conjonction_elim_gauche(conjonction_elim_gauche(h))
    g2_in = conjonction_elim_droite(conjonction_elim_gauche(h))
    W_eq = conjonction_elim_droite(h)                            # W(g₁)=W(g₂)
    Wg1 = _cut(W_U_valeur("g1", va, vb, vc), [(appartient(vg1, dom), g1_in)])    # W(g₁)=U(g₁)
    Wg2 = _cut(W_U_valeur("g2", va, vb, vc), [(appartient(vg2, dom), g2_in)])    # W(g₂)=U(g₂)
    U_eq = composer_egalites(composer_egalites(
        N.modus_ponens(Wg1, symetrie(E.valeur(Wt, vg1), ua1)), W_eq), Wg2)   # U(g₁)=U(g₂)
    g_eq = uncurry_injective_sous_appartenance("g1", "g2", va, vb, vc)
    g_eq = _cut(g_eq, [(appartient(vg1, dom), g1_in),
                       (appartient(vg2, dom), g2_in),
                       (egal(ua1, ua2), U_eq)])             # g₁=g₂  [hyp]
    inner = N.loi_deduction(hyp, g_eq)
    raw = N.generalisation("g1", N.generalisation("g2", inner))  # (∀g1)(∀g2)…
    inst = instancie(instancie(raw, var("u")), var("up"))        # P[g1:=u, g2:=up]
    return N.generalisation("u", N.generalisation("up", inst))   # (∀u)(∀up)… = injective_dans


# ═══════════════════════════════════════════════════════════════════════════════
#  DIRECTION B :  𝓕(C;𝓕(B;A)) ≤ 𝓕(B×C;A)   (U est une injection)
# ═══════════════════════════════════════════════════════════════════════════════
def W_U_est_injection(a="A", b="B", c="C"):
    """⊢ est_injection_de(W_U, 𝓕(C;𝓕(B;A)), 𝓕(B×C;A)).

    Les QUATRE conjoints (E.III.3.2) : W_U fonctionnel, dom W_U=𝓕(C;𝓕(B;A)), injective
    sur 𝓕(C;𝓕(B;A)), image⊂𝓕(B×C;A).  Tous CLOS (graphe de U via le PONT graphe_de,
    bien-déf = double valeur_application_dans_but, injectivité = back-and-forth redoublé)."""
    va, vb, vc = _t(a), _t(b), _t(c)
    return conjonction_intro(conjonction_intro(conjonction_intro(
        W_U_fonctionnel(va, vb, vc), W_U_domaine(va, vb, vc)),
        W_U_injective(va, vb, vc)), W_U_image_incluse(va, vb, vc))


def inf_egal_uncurry(a="A", b="B", c="C"):
    """⊢ inf_egal_card( 𝓕(C;𝓕(B;A)) , 𝓕(B×C;A) ).   ((a^b)^c ≤ a^(b·c) — DIRECTION B de Prop 10.)

    L'injection-témoin est W_U (W_U_est_injection) : par S5 (témoin F:=W_U),
    (∃F) est_injection_de(F, 𝓕(C;𝓕(B;A)), 𝓕(B×C;A)) = inf_egal_card(·,·).
    Mime inf_egal_phi / inf_egal_psi."""
    va, vb, vc = _t(a), _t(b), _t(c)
    source = domaine_U(va, vb, vc)                   # 𝓕(C;𝓕(B;A)) — SOURCE de U
    but = codomaine_U(va, vb, vc)                    # 𝓕(B×C;A)     — BUT de U
    Wt = W_U(va, vb, vc)
    inj = W_U_est_injection(va, vb, vc)              # est_injection_de(W_U, source, but)
    return N.modus_ponens(inj, N.s5(est_injection_de(var("F"), source, but), Wt, "F"))


__all__ = [
    "uncurry_graphe", "uncurry_appli", "W_U", "domaine_U", "codomaine_U",
    "W_U_fonctionnel", "W_U_domaine", "W_U_valeur",
    "uncurry_graphe_inclus", "uncurry_graphe_fonctionnel", "uncurry_graphe_domaine",
    "uncurry_graphe_dans_exposant", "uncurry_appli_dans_codomaine",
    "W_U_image_incluse",
    "uncurry_injective_sous_appartenance", "W_U_injective",
    "W_U_est_injection", "inf_egal_uncurry",
]
