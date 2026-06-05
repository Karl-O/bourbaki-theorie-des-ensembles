"""§III.3.3 — DISTRIBUTIVITÉ du produit sur la somme cardinale (E.III.3.3, Prop. 3) :

        ⊢ Card(A × (B⊔C)) = Card((A×B) ⊔ (A×C))      [ = a·(b+c) = a·b + a·c ].

Le cœur est la bijection ensembliste

        D : A × (B⊔C)  →  (A×B) ⊔ (A×C),
        (x, (y,0)) ↦ ((x,y), 0)        (copie de gauche, marqueur 0 = ∅)
        (x, (z,1)) ↦ ((x,z), 1)        (copie de droite, marqueur 1 = {∅}).

CLÉ : contrairement à la somme (ensembles_somme_equipotence) il n'y a PAS de
cas-analyse dans le TERME.  Un élément k ∈ A×(B⊔C) est un couple (pr₁k, pr₂k) avec
pr₁k ∈ A et pr₂k ∈ B⊔C ; or pr₂k est lui-même un couple (coord, marqueur).  Quel
que soit le marqueur, l'image est ((pr₁k, coord), marqueur), donc le terme est le
RÉ-ARRANGEMENT pur

        T(k) := ((pr₁k, pr₁(pr₂k)), pr₂(pr₂k))            (= (x, (y, m)) ↦ ((x, y), m)).

C'est le MÊME patron que la réassociation (X×Y)×Z ≅ X×(Y×Z)
(ensembles_arith_cardinale._reassoc_terme) : un graphe défini par un terme de
projections imbriquées, donc fonctionnel (C54), de domaine A×(B⊔C), injectif et
surjectif — tout en liants UNIFORMES a,b (projections externes sur k) / c,d
(projections internes sur pr₂k), comme reassoc et swap.  La disjonction des copies
0 ≠ 1 (vide_distinct_singleton) n'intervient que pour l'injectivité/surjectivité,
PAS dans le terme.

PALIERS (chacun testé, cf. test_distributivite_cardinale.py) :
  • distrib_graphe_fonctionnel  (clos)        — D fonctionnel             (PALIER 1) ;
  • distrib_graphe_domaine      (clos)        — dom D = A×(B⊔C)           (PALIER 2) ;
  • distrib_graphe_valeur       {u∈A×(B⊔C)}   — D(u)=((pr₁u,pr₁pr₂u),pr₂pr₂u) (PALIER 3) ;
  • distrib_graphe_valeur_gauche {x∈A,y∈B}    — D((x,(y,0)))=((x,y),0)    (PALIER 3g) ;
  • distrib_graphe_valeur_droite {x∈A,z∈C}    — D((x,(z,1)))=((x,z),1)    (PALIER 3d) ;
  • distrib_graphe_injective    (clos)        — injective_dans(D, A×(B⊔C)) (PALIER 4) ;
  • distrib_graphe_image        (clos)        — image(D, A×(B⊔C))=(A×B)⊔(A×C) (PALIER 5) ;
  • distrib_est_bijection       (clos)        — est_bijection_de(D, …) ;
  • eq_distributivite           (clos)        — Eq(A×(B⊔C), (A×B)⊔(A×C)) ;
  • distributivite_cardinale    (clos)        — Card(A×(B⊔C))=Card((A×B)⊔(A×C)).

Les marqueurs 0=∅, 1={∅} sont importés d'ensembles_somme_disjointe (ZERO, UN).
"""
from __future__ import annotations

from bourbaki.logique.formule import (Terme, var, egal, et, ou, non, appartient, existe,
                     subst_t, subst_f)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.logique.tactiques.tactiques_abrege import a_implique_a, syllogisme
from bourbaki.logique.tactiques.tactiques_abrege2 import (conjonction_intro, conjonction_elim_gauche,
                               conjonction_elim_droite, equivalence_avant,
                               equivalence_arriere, equivalence_transitivite,
                               instancie, cas)
from bourbaki.logique.tactiques.tactiques_abrege_egalite import (symetrie, composer_egalites, congruence_terme)
from bourbaki.logique.tactiques.tactiques_abrege_quantif import (existe_elimination, alpha_existe,
                                      congruence_existe)
from bourbaki.ensembles.familles.ensembles_somme_disjointe import (somme_disjointe, ZERO, UN,
                                       injection_gauche_dans_somme,
                                       injection_droite_dans_somme,
                                       membre_somme_caracterise, _ou_congruence)
from bourbaki.cardinaux.arithmetique.ensembles_produit_commute import (_membre_produit_egal_couple_ab,
                                       _membre_produit_pr1_ab,
                                       _membre_produit_pr2_ab,
                                       _projection_premiere_ab,
                                       _projection_seconde_ab,
                                       _couple_dans_produit_t, _inst_produit)
from bourbaki.ensembles.base.ensembles_couples import couple_egal_implique_composantes
from bourbaki.ensembles.fonctions.ensembles_fonction_terme import membre_graphe_terme, graphe_terme_fonctionnel
from bourbaki.cardinaux.ensembles_cantor import (graphe_terme_domaine, graphe_terme_valeur,
                              graphe_terme_couple_dans)
from bourbaki.ensembles.fonctions.ensembles_fonctions import valeur_caracterisation
from bourbaki.cardinaux.ensembles_vide_singleton import vide_distinct_singleton
from bourbaki.ensembles.ensembles_theoremes import egalite_par_extension


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# ── Le terme de distributivité  T(k) = ((pr₁k, pr₁(pr₂k)), pr₂(pr₂k)) ─────────
def _distrib_terme(k="k"):
    """T = ((pr₁k, pr₁(pr₂k)), pr₂(pr₂k))   (ré-arrangement (x,(y,m)) ↦ ((x,y),m)).

    Liants : projections EXTERNES sur k en a,b ; projections INTERNES sur pr₂k en
    c,d (≠ a,b) — pas de capture inter-niveaux, comme reassoc/swap en liants
    uniformes."""
    vk = var(k)
    pr1k = E.pr1(vk, "a", "b")            # pr₁ k   (1ʳᵉ coord = x∈A)
    pr2k = E.pr2(vk, "a", "b")            # pr₂ k   (∈ B⊔C : couple (coord, marqueur))
    pr1pr2k = E.pr1(pr2k, "c", "d")       # pr₁(pr₂ k)  (coord = y∈B ou z∈C)
    pr2pr2k = E.pr2(pr2k, "c", "d")       # pr₂(pr₂ k)  (marqueur 0 ou 1)
    return E.couple(E.couple(pr1k, pr1pr2k), pr2pr2k)


def _distrib_graphe(a, b, c, k="k"):
    """D := graphe_terme(A×(B⊔C), T, "k")  (graphe de la bijection distributive)."""
    Dom = E.produit(_t(a), somme_disjointe(_t(b), _t(c)))
    return E.graphe_terme(Dom, _distrib_terme(k), k)


# ── PALIER 1 : D est fonctionnel  (CERTIFIÉ, clos) ────────────────────────────
def distrib_graphe_fonctionnel(a="A", b="B", c="C"):
    """⊢ D est fonctionnel,  D = graphe de la bijection distributive.   (cas C54, clos.)

    Application directe de graphe_terme_fonctionnel : le graphe d'une fonction
    définie par un terme est toujours fonctionnel (E.II.46)."""
    Dom = E.produit(_t(a), somme_disjointe(_t(b), _t(c)))
    return graphe_terme_fonctionnel(Dom, _distrib_terme("k"), "k", "t")


# ── PALIER 2 : dom D = A×(B⊔C)  (CERTIFIÉ, clos) ──────────────────────────────
def distrib_graphe_domaine(a="A", b="B", c="C"):
    """⊢ dom(D) = A×(B⊔C).   (la bijection distributive est définie sur tout A×(B⊔C) ; clos.)

    Application directe de graphe_terme_domaine au terme distributif (le liant des
    valeurs/projections évite la collision avec le ∃y du domaine)."""
    Dom = E.produit(_t(a), somme_disjointe(_t(b), _t(c)))
    return graphe_terme_domaine(Dom, _distrib_terme("k"), "k", "y", "z")


# ── PALIER 3 : VALEUR générique  D(u) = T[u]  pour u∈A×(B⊔C) ──────────────────
def distrib_graphe_valeur(a="A", b="B", c="C", u="u"):
    """{u ∈ A×(B⊔C)} ⊢ D(u) = ((pr₁u, pr₁(pr₂u)), pr₂(pr₂u)).

    (u,T[u])∈D (couple) → u dans le domaine ; valeur_caracterisation (C46, sous
    « D fonctionnel ») donne T[u]=D(u) ; symétrie conclut.  Même recette que
    reassoc_graphe_valeur, avec les liants a,b/c,d de _distrib_terme."""
    Dom = E.produit(_t(a), somme_disjointe(_t(b), _t(c)))
    T = _distrib_terme("k")
    xb = "k"
    F = E.graphe_terme(Dom, T, xb)
    vu = _t(u)
    Tu = subst_t(vu, xb, T)                                  # T[u]
    fu = E.valeur(F, vu)                                     # D(u)
    cpl = graphe_terme_couple_dans(Dom, T, u, xb, "t")       # {u∈A×(B⊔C)} ⊢ (u,T[u])∈D
    dom_membre = N.modus_ponens(cpl, N.s5(appartient(E.couple(vu, var("y")), F), Tu, "y"))
    vc = valeur_caracterisation(F, vu)                       # y libre
    vc_all = N.generalisation("y", vc)                       # (∀y)(((u,y)∈F)⇔(y=D(u)))
    vc_Tu = instancie(vc_all, Tu)                            # ((u,T[u])∈F) ⇔ (T[u]=D(u))
    Tu_fu = N.modus_ponens(cpl, equivalence_avant(vc_Tu))    # T[u]=D(u)
    fu_Tu = N.modus_ponens(Tu_fu, symetrie(Tu, fu))         # D(u)=T[u]
    fu_Tu = N.modus_ponens(distrib_graphe_fonctionnel(a, b, c),
                           N.loi_deduction(E.est_fonctionnel(F), fu_Tu))
    fu_Tu = N.modus_ponens(dom_membre,
        N.loi_deduction(existe("y", appartient(E.couple(vu, var("y")), F)), fu_Tu))
    return fu_Tu                                             # {u∈A×(B⊔C)} ⊢ D(u)=T[u]


# ── T[(x,(w,m))] = ((x,w),m)  (calcul des projections imbriquées sur un couple concret) ─
def _T_sur_couple(x, w, m):
    """⊢ T[(x,(w,m))] = ((x,w),m).   (calcul du terme distributif sur un couple concret.)

    cpl = (x,(w,m)).  pr₁cpl=x, pr₂cpl=(w,m) [liants a,b] ; pr₁(pr₂cpl)=w,
    pr₂(pr₂cpl)=m [liants c,d, après réécriture pr₂cpl→(w,m)].  T[cpl] =
    ((pr₁cpl,pr₁pr₂cpl),pr₂pr₂cpl) → ((x,w),m) par trois congruences (comme le
    calcul de T[t₀] dans reassoc_graphe_image)."""
    vx, vw, vm = _t(x), _t(w), _t(m)
    wm = E.couple(vw, vm)                                    # (w,m)
    cpl = E.couple(vx, wm)                                   # (x,(w,m))
    pr1cpl = E.pr1(cpl, "a", "b")
    pr2cpl = E.pr2(cpl, "a", "b")
    pr1pr2cpl = E.pr1(pr2cpl, "c", "d")
    pr2pr2cpl = E.pr2(pr2cpl, "c", "d")
    Tcpl = E.couple(E.couple(pr1cpl, pr1pr2cpl), pr2pr2cpl)  # T[(x,(w,m))]
    # pr₁cpl = x  ;  pr₂cpl = (w,m)
    pr1_eq = _projection_premiere_ab(vx, wm, "a", "b")       # pr₁cpl = x
    pr2_eq = _projection_seconde_ab(vx, wm, "a", "b")        # pr₂cpl = (w,m)
    # pr₁(pr₂cpl) = pr₁((w,m)) = w   (réécrire pr₂cpl → (w,m), puis projection c,d)
    cong_p1 = N.modus_ponens(pr2_eq, congruence_terme(pr2cpl, wm, E.pr1(var("w"), "c", "d")))
    pr1pr2_eq = composer_egalites(cong_p1, _projection_premiere_ab(vw, vm, "c", "d"))   # pr₁(pr₂cpl)=w
    # pr₂(pr₂cpl) = pr₂((w,m)) = m
    cong_p2 = N.modus_ponens(pr2_eq, congruence_terme(pr2cpl, wm, E.pr2(var("w"), "c", "d")))
    pr2pr2_eq = composer_egalites(cong_p2, _projection_seconde_ab(vw, vm, "c", "d"))    # pr₂(pr₂cpl)=m
    # T[cpl] = ((pr₁cpl,pr₁pr₂cpl),pr₂pr₂cpl) → ((x,w),m)  (trois congruences)
    s1 = N.modus_ponens(pr1_eq, congruence_terme(pr1cpl, vx,
            E.couple(E.couple(var("w"), pr1pr2cpl), pr2pr2cpl)))   # = ((x,pr₁pr₂cpl),pr₂pr₂cpl)
    s2 = N.modus_ponens(pr1pr2_eq, congruence_terme(pr1pr2cpl, vw,
            E.couple(E.couple(vx, var("w")), pr2pr2cpl)))          # = ((x,w),pr₂pr₂cpl)
    s3 = N.modus_ponens(pr2pr2_eq, congruence_terme(pr2pr2cpl, vm,
            E.couple(E.couple(vx, vw), var("w"))))                # = ((x,w),m)
    return composer_egalites(composer_egalites(s1, s2), s3)       # T[(x,(w,m))]=((x,w),m)


def _distrib_graphe_valeur_t(a, b, c, cpl):
    """{cpl ∈ A×(B⊔C)} ⊢ D(cpl) = T[cpl],  cpl un TERME (couple concret).

    (cpl,T[cpl])∈D directement via l'axiome du graphe (témoins k:=cpl, yb:=T[cpl]),
    puis valeur_caracterisation (C46, sous « D fonctionnel » déchargé) donne
    T[cpl]=D(cpl) ; symétrie conclut.  Term-tolérant (cpl quelconque)."""
    va, vb, vc = _t(a), _t(b), _t(c)
    Dom = E.produit(va, somme_disjointe(vb, vc))
    T = _distrib_terme("k")
    K = E.graphe_terme(Dom, T, "k")
    Tcpl = subst_t(cpl, "k", T)                             # T[cpl]
    ax_K = N.axiome(E.theorie_graphe_terme(Dom, T, "k", "yb", "zz"),
                    E.axiome_graphe_terme(Dom, T, "k", "yb", "zz"))
    paire_cpl = E.couple(cpl, Tcpl)
    car = instancie(ax_K, paire_cpl)                       # (cpl,T[cpl])∈D ⇔ (∃k)(∃yb)body
    gbody_k = et(et(egal(paire_cpl, E.couple(var("k"), var("yb"))),
                    appartient(var("k"), Dom)), egal(var("yb"), T))
    body_k0 = subst_f(cpl, "k", gbody_k)
    h_in = N.assume(appartient(cpl, Dom))
    wit_yb = conjonction_intro(conjonction_intro(N.reflexivite(paire_cpl), h_in),
                               N.reflexivite(Tcpl))
    ex_yb = N.modus_ponens(wit_yb, N.s5(body_k0, Tcpl, "yb"))
    ex_kyb = N.modus_ponens(ex_yb, N.s5(existe("yb", gbody_k), cpl, "k"))
    cpl_in_K = N.modus_ponens(ex_kyb, equivalence_arriere(car))   # (cpl,T[cpl])∈D  [hyp cpl∈Dom]
    dom_membre = N.modus_ponens(cpl_in_K,
        N.s5(appartient(E.couple(cpl, var("y")), K), Tcpl, "y"))
    vcar = valeur_caracterisation(K, cpl)
    vc_all = N.generalisation("y", vcar)
    vc_Tcpl = instancie(vc_all, Tcpl)                     # ((cpl,T[cpl])∈D)⇔(T[cpl]=D(cpl))
    Tcpl_K = N.modus_ponens(cpl_in_K, equivalence_avant(vc_Tcpl))   # T[cpl]=D(cpl)
    K_Tcpl = N.modus_ponens(Tcpl_K, symetrie(Tcpl, E.valeur(K, cpl)))   # D(cpl)=T[cpl]
    K_Tcpl = N.modus_ponens(distrib_graphe_fonctionnel(a, b, c),
                            N.loi_deduction(E.est_fonctionnel(K), K_Tcpl))
    K_Tcpl = N.modus_ponens(dom_membre, N.loi_deduction(
        existe("y", appartient(E.couple(cpl, var("y")), K)), K_Tcpl))
    return K_Tcpl                                          # {cpl∈A×(B⊔C)} ⊢ D(cpl)=T[cpl]


# ── (x,(w,m)) ∈ A×(B⊔C)  pour la copie gauche (m=0,w∈B) / droite (m=1,w∈C) ─────
def _couple_dans_domaine(x, w, marker, a, b, c):
    """{x∈A, w∈(B si gauche / C si droite)} ⊢ (x,(w,marker)) ∈ A×(B⊔C).

    (w,marker)∈B⊔C par injection_gauche/droite_dans_somme ; puis couple produit."""
    va, vb, vc = _t(a), _t(b), _t(c)
    vx, vw = _t(x), _t(w)
    BC = somme_disjointe(vb, vc)
    wm = E.couple(vw, marker)
    if marker is ZERO:
        wm_in = injection_gauche_dans_somme(vw, vb, vc)    # (w∈B) ⇒ (w,0)∈B⊔C
        wm_in = N.modus_ponens(N.assume(appartient(vw, vb)), wm_in)   # {w∈B} ⊢ (w,0)∈B⊔C
    else:
        wm_in = injection_droite_dans_somme(vw, vb, vc)    # (w∈C) ⇒ (w,1)∈B⊔C
        wm_in = N.modus_ponens(N.assume(appartient(vw, vc)), wm_in)   # {w∈C} ⊢ (w,1)∈B⊔C
    # (x, (w,marker)) ∈ A×(B⊔C)
    cpl_in = N.modus_ponens(conjonction_intro(N.assume(appartient(vx, va)), wm_in),
                            _couple_dans_produit_t(vx, wm, va, BC))   # (x,(w,m))∈A×(B⊔C)
    return cpl_in                                          # {x∈A, w∈(B|C)} ⊢ (x,(w,m))∈A×(B⊔C)


# ── PALIER 3g/3d : valeur de D sur chaque copie ───────────────────────────────
def distrib_graphe_valeur_gauche(a="A", b="B", c="C", x="x", y="e"):
    """{x∈A, y∈B} ⊢ D((x,(y,0))) = ((x,y),0).   (la bijection distributive, copie gauche.)

    (x,(y,0))∈A×(B⊔C) (_couple_dans_domaine), donc D((x,(y,0)))=T[(x,(y,0))]
    (_distrib_graphe_valeur_t) ; T[(x,(y,0))]=((x,y),0) (_T_sur_couple).
    NB coordonnées : la 2ᵉ coordonnée « e » (≠ y/yb/zz/k internes du graphe)
    évite la capture du liant interne « y » de _distrib_graphe_valeur_t."""
    va, vb, vc = _t(a), _t(b), _t(c)
    vx, vy = _t(x), _t(y)
    Dom = E.produit(va, somme_disjointe(vb, vc))
    cpl = E.couple(vx, E.couple(vy, ZERO))                 # (x,(y,0))
    cpl_in = _couple_dans_domaine(vx, vy, ZERO, a, b, c)   # {x∈A,y∈B} ⊢ (x,(y,0))∈A×(B⊔C)
    val0 = _distrib_graphe_valeur_t(a, b, c, cpl)          # {(x,(y,0))∈Dom} ⊢ D(cpl)=T[cpl]
    Dval = N.modus_ponens(cpl_in, N.loi_deduction(appartient(cpl, Dom), val0))  # D(cpl)=T[cpl]
    T_eq = _T_sur_couple(vx, vy, ZERO)                     # T[(x,(y,0))]=((x,y),0)
    return composer_egalites(Dval, T_eq)                  # {x∈A,y∈B} ⊢ D((x,(y,0)))=((x,y),0)


def distrib_graphe_valeur_droite(a="A", b="B", c="C", x="x", z="e"):
    """{x∈A, z∈C} ⊢ D((x,(z,1))) = ((x,z),1).   (la bijection distributive, copie droite.)

    NB coordonnées : la 2ᵉ coordonnée « e » (≠ y/yb/zz/k internes) évite la capture
    du liant interne « y » de _distrib_graphe_valeur_t."""
    va, vb, vc = _t(a), _t(b), _t(c)
    vx, vz = _t(x), _t(z)
    Dom = E.produit(va, somme_disjointe(vb, vc))
    cpl = E.couple(vx, E.couple(vz, UN))                   # (x,(z,1))
    cpl_in = _couple_dans_domaine(vx, vz, UN, a, b, c)     # {x∈A,z∈C} ⊢ (x,(z,1))∈A×(B⊔C)
    val0 = _distrib_graphe_valeur_t(a, b, c, cpl)
    Dval = N.modus_ponens(cpl_in, N.loi_deduction(appartient(cpl, Dom), val0))
    T_eq = _T_sur_couple(vx, vz, UN)                       # T[(x,(z,1))]=((x,z),1)
    return composer_egalites(Dval, T_eq)


# ── Tout élément de B⊔C est un couple : m∈B⊔C ⇒ m = (pr₁m, pr₂m) ──────────────
def _membre_somme_est_couple(b, c, m="m", bx="c", by="d"):
    """{m ∈ B⊔C} ⊢ m = (pr₁m[bx,by], pr₂m[bx,by]).   (reconstruction d'un élément de B⊔C.)

    m∈B⊔C ⇔ (∃p)(p∈B et m=(p,0)) ou (∃q)(q∈C et m=(q,1)) (membre_somme_caracterise).
    Dans chaque copie, m=(w,marker) → pr₁m=w, pr₂m=marker → m=(pr₁m,pr₂m).  Liants
    de projection bx,by (par défaut c,d, alignés sur _distrib_terme)."""
    vb, vc = _t(b), _t(c)
    vm = _t(m)
    BC = somme_disjointe(vb, vc)
    pr1m, pr2m = E.pr1(vm, bx, by), E.pr2(vm, bx, by)
    cible = egal(vm, E.couple(pr1m, pr2m))
    # dériver la disjonction directement (comme somme_graphe_injective)
    dec0 = N.modus_ponens(N.assume(appartient(vm, BC)),
                          equivalence_avant(membre_somme_caracterise(b, c, vm)))  # (∃u)(...) ou (∃v)(...)
    exB0, exC0 = dec0.conclusion.sous[0], dec0.conclusion.sous[1]
    # renommer les binders internes (u,v par défaut) en p1,p2 (anti-collision)
    renB = alpha_existe(exB0.lieur, "p1", exB0.sous[0])
    renC = alpha_existe(exC0.lieur, "p2", exC0.sous[0])
    dec = N.modus_ponens(dec0, equivalence_avant(_ou_congruence(renB, renC)))  # (∃p1)bB ou (∃p2)bC
    exB, exC = dec.conclusion.sous[0], dec.conclusion.sous[1]
    nB, bB = exB.lieur, exB.sous[0]                       # p1 ; (p1∈B et m=(p1,0))
    nC, bC = exC.lieur, exC.sous[0]                       # p2 ; (p2∈C et m=(p2,1))

    def branche(body, witness_name, marker):
        vw = var(witness_name)
        wm = E.couple(vw, marker)                         # (w,marker)
        h = N.assume(body)
        m_eq = conjonction_elim_droite(h)                # m=(w,marker)
        # pr₁m = w  (réécrire m→(w,marker), projection bx,by)
        cong1 = N.modus_ponens(m_eq, congruence_terme(vm, wm, E.pr1(var("w"), bx, by)))
        pr1m_eq = composer_egalites(cong1, _projection_premiere_ab(vw, marker, bx, by))  # pr₁m=w
        cong2 = N.modus_ponens(m_eq, congruence_terme(vm, wm, E.pr2(var("w"), bx, by)))
        pr2m_eq = composer_egalites(cong2, _projection_seconde_ab(vw, marker, bx, by))   # pr₂m=marker
        # (pr₁m,pr₂m) = (w,marker) = m
        c1 = N.modus_ponens(pr1m_eq, congruence_terme(pr1m, vw, E.couple(var("w"), pr2m)))  # (pr₁m,pr₂m)=(w,pr₂m)
        c2 = N.modus_ponens(pr2m_eq, congruence_terme(pr2m, marker, E.couple(vw, var("w"))))  # =(w,marker)
        pr_eq_wm = composer_egalites(c1, c2)             # (pr₁m,pr₂m)=(w,marker)
        wm_eq_pr = N.modus_ponens(pr_eq_wm, symetrie(E.couple(pr1m, pr2m), wm))  # (w,marker)=(pr₁m,pr₂m)
        m_eq_pr = composer_egalites(m_eq, wm_eq_pr)      # m=(w,marker)=(pr₁m,pr₂m)
        return N.loi_deduction(body, m_eq_pr)            # body ⇒ m=(pr₁m,pr₂m)

    impB = existe_elimination(branche(bB, nB, ZERO), nB)   # exB ⇒ cible
    impC = existe_elimination(branche(bC, nC, UN), nC)     # exC ⇒ cible
    return cas(dec, impB, impC)                            # {m∈B⊔C} ⊢ m=(pr₁m,pr₂m)


# ── PALIER 4 : injective_dans(D, A×(B⊔C))  (CERTIFIÉ, clos) ────────────────────
def distrib_graphe_injective(a="A", b="B", c="C"):
    """⊢ injective_dans(D, A×(B⊔C)).   (la bijection distributive est injective.)

    D(u)=((pr₁u,pr₁pr₂u),pr₂pr₂u)=D(u') ⇒ (double couple_egal) pr₁u=pr₁u',
    pr₁pr₂u=pr₁pr₂u', pr₂pr₂u=pr₂pr₂u'.  Or u=(pr₁u,pr₂u) (liants a,b) et pr₂u est un
    couple (pr₂u∈B⊔C) → pr₂u=(pr₁pr₂u,pr₂pr₂u) (_membre_somme_est_couple, liants c,d) ;
    deux niveaux de congruence donnent pr₂u=pr₂u' puis u=u'.  Pas de cas-analyse de
    marqueur : reconstruction pure, comme reassoc_graphe_injective."""
    va, vb, vc = _t(a), _t(b), _t(c)
    BC = somme_disjointe(vb, vc)
    Dom = E.produit(va, BC)
    R = _distrib_graphe(a, b, c)
    # élément liants « s », « sp » (≠ u,v internes de membre_somme_caracterise via
    # _membre_somme_est_couple sur pr₂u, ≠ p1,p2 témoins, ≠ a,b,c,d,w des termes)
    vu, vup = var("s"), var("sp")
    # projections : a,b externes sur u ; c,d internes sur pr₂u
    pr1u, pr2u = E.pr1(vu, "a", "b"), E.pr2(vu, "a", "b")
    pr1up, pr2up = E.pr1(vup, "a", "b"), E.pr2(vup, "a", "b")
    pr1pr2u, pr2pr2u = E.pr1(pr2u, "c", "d"), E.pr2(pr2u, "c", "d")
    pr1pr2up, pr2pr2up = E.pr1(pr2up, "c", "d"), E.pr2(pr2up, "c", "d")
    Tu = E.couple(E.couple(pr1u, pr1pr2u), pr2pr2u)          # D(u)=T[u]
    Tup = E.couple(E.couple(pr1up, pr1pr2up), pr2pr2up)      # D(u')
    hyp = et(et(appartient(vu, Dom), appartient(vup, Dom)),
             egal(E.valeur(R, vu), E.valeur(R, vup)))
    h = N.assume(hyp)
    uinA = conjonction_elim_gauche(conjonction_elim_gauche(h))     # u∈A×(B⊔C)
    upinA = conjonction_elim_droite(conjonction_elim_gauche(h))    # u'∈A×(B⊔C)
    val_eq = conjonction_elim_droite(h)                           # D(u)=D(u')
    Ru_T = N.modus_ponens(uinA, N.loi_deduction(appartient(vu, Dom),
                                                distrib_graphe_valeur(a, b, c, "s")))    # D(u)=T[u]
    Rup_T = N.modus_ponens(upinA, N.loi_deduction(appartient(vup, Dom),
                                                  distrib_graphe_valeur(a, b, c, "sp")))  # D(u')=T[u']
    Tu_Ru = N.modus_ponens(Ru_T, symetrie(E.valeur(R, vu), Tu))   # T[u]=D(u)
    Tu_Tup = composer_egalites(composer_egalites(Tu_Ru, val_eq), Rup_T)  # T[u]=T[u']
    # outer : (pr₁u,pr₁pr₂u)=(pr₁u',pr₁pr₂u')  et  pr₂pr₂u=pr₂pr₂u'
    outer = N.modus_ponens(Tu_Tup,
        couple_egal_implique_composantes(E.couple(pr1u, pr1pr2u), pr2pr2u,
                                         E.couple(pr1up, pr1pr2up), pr2pr2up))
    eq_head = conjonction_elim_gauche(outer)                      # (pr₁u,pr₁pr₂u)=(pr₁u',pr₁pr₂u')
    eq_pr2pr2 = conjonction_elim_droite(outer)                    # pr₂pr₂u=pr₂pr₂u'
    inner = N.modus_ponens(eq_head,
        couple_egal_implique_composantes(pr1u, pr1pr2u, pr1up, pr1pr2up))
    eq_pr1 = conjonction_elim_gauche(inner)                       # pr₁u=pr₁u'
    eq_pr1pr2 = conjonction_elim_droite(inner)                    # pr₁pr₂u=pr₁pr₂u'
    # pr₂u et pr₂u' sont des couples (∈B⊔C) → reconstruction en liants c,d
    pr2u_inBC = N.modus_ponens(uinA, N.loi_deduction(appartient(vu, Dom),
                                                     _membre_produit_pr2_ab(va, BC, "s")))   # pr₂u∈B⊔C
    pr2up_inBC = N.modus_ponens(upinA, N.loi_deduction(appartient(vup, Dom),
                                                       _membre_produit_pr2_ab(va, BC, "sp")))  # pr₂u'∈B⊔C
    pr2u_rec = N.modus_ponens(pr2u_inBC, N.loi_deduction(appartient(pr2u, BC),
                                _membre_somme_est_couple(vb, vc, pr2u, "c", "d")))   # pr₂u=(pr₁pr₂u,pr₂pr₂u)
    pr2up_rec = N.modus_ponens(pr2up_inBC, N.loi_deduction(appartient(pr2up, BC),
                                _membre_somme_est_couple(vb, vc, pr2up, "c", "d")))  # pr₂u'=(...)
    # pr₂u = pr₂u' : congruences sur le couple (pr₁pr₂·, pr₂pr₂·)
    d1 = N.modus_ponens(eq_pr1pr2, congruence_terme(pr1pr2u, pr1pr2up,
                                                    E.couple(var("w"), pr2pr2u)))   # (pr₁pr₂u,pr₂pr₂u)=(pr₁pr₂u',pr₂pr₂u)
    d2 = N.modus_ponens(eq_pr2pr2, congruence_terme(pr2pr2u, pr2pr2up,
                                                    E.couple(pr1pr2up, var("w"))))  # =(pr₁pr₂u',pr₂pr₂u')
    cpl_pr2 = composer_egalites(d1, d2)                           # (pr₁pr₂u,pr₂pr₂u)=(pr₁pr₂u',pr₂pr₂u')
    pr2u_eq = composer_egalites(composer_egalites(pr2u_rec, cpl_pr2),
                                N.modus_ponens(pr2up_rec,
                                    symetrie(pr2up, E.couple(pr1pr2up, pr2pr2up))))   # pr₂u=pr₂u'
    # u = u' : u=(pr₁u,pr₂u), congruences avec pr₁u=pr₁u' et pr₂u=pr₂u'
    u_rec = N.modus_ponens(uinA, N.loi_deduction(appartient(vu, Dom),
                                                 _membre_produit_egal_couple_ab(va, BC, "s", "a", "b")))   # u=(pr₁u,pr₂u)
    up_rec = N.modus_ponens(upinA, N.loi_deduction(appartient(vup, Dom),
                                                   _membre_produit_egal_couple_ab(va, BC, "sp", "a", "b")))  # u'=(pr₁u',pr₂u')
    e1 = N.modus_ponens(eq_pr1, congruence_terme(pr1u, pr1up, E.couple(var("w"), pr2u)))    # (pr₁u,pr₂u)=(pr₁u',pr₂u)
    e2 = N.modus_ponens(pr2u_eq, congruence_terme(pr2u, pr2up, E.couple(pr1up, var("w"))))  # (pr₁u',pr₂u)=(pr₁u',pr₂u')
    rec_eq = composer_egalites(e1, e2)                           # (pr₁u,pr₂u)=(pr₁u',pr₂u')
    u_eq_up = composer_egalites(composer_egalites(u_rec, rec_eq),
                                N.modus_ponens(up_rec, symetrie(vup, E.couple(pr1up, pr2up))))
    body = N.loi_deduction(hyp, u_eq_up)
    return N.generalisation("s", N.generalisation("sp", body))   # injective_dans(D, A×(B⊔C)) [liants s,sp]


# ── Couple (t₀,z)∈D directement via l'axiome du graphe (témoins k:=t₀, yb:=z) ──
def _couple_dans_D(a, b, c, t0, vz, z_eq_Tt0, t0_in_thm):
    """De t0∈A×(B⊔C) et z=T[t0], déduire (t0,z)∈D   (axiome du graphe)."""
    va, vb, vc = _t(a), _t(b), _t(c)
    Dom = E.produit(va, somme_disjointe(vb, vc))
    T = _distrib_terme("k")
    K = E.graphe_terme(Dom, T, "k")
    ax_K = N.axiome(E.theorie_graphe_terme(Dom, T, "k", "yb", "zz"),
                    E.axiome_graphe_terme(Dom, T, "k", "yb", "zz"))
    cpl_z = E.couple(t0, vz)
    car_z = instancie(ax_K, cpl_z)                                # (t0,z)∈D ⇔ (∃k)(∃yb)body
    gbody_k = et(et(egal(cpl_z, E.couple(var("k"), var("yb"))),
                    appartient(var("k"), Dom)), egal(var("yb"), T))
    body_k0 = subst_f(t0, "k", gbody_k)
    wit_yb = conjonction_intro(conjonction_intro(N.reflexivite(cpl_z), t0_in_thm), z_eq_Tt0)
    ex_yb = N.modus_ponens(wit_yb, N.s5(body_k0, vz, "yb"))
    ex_kyb = N.modus_ponens(ex_yb, N.s5(existe("yb", gbody_k), t0, "k"))
    return N.modus_ponens(ex_kyb, equivalence_arriere(car_z))      # (t0,z)∈D


# ── PALIER 5 : image(D, A×(B⊔C)) = (A×B)⊔(A×C)  (surjectivité) ─────────────────
def distrib_graphe_image(a="A", b="B", c="C"):
    """⊢ image(D, A×(B⊔C)) = (A×B) ⊔ (A×C).   (la bijection distributive est surjective.)

    z∈D⟨Dom⟩ ⇔ (∃t)(t∈Dom et z=T[t]).
    ⇒ : t=(x,m)∈A×(B⊔C) (x∈A, m∈B⊔C) ; m=(y,0) (y∈B) ⇒ z=T[(x,(y,0))]=((x,y),0)
        avec (x,y)∈A×B ⇒ z∈(A×B)⊔(A×C) (injection_gauche) ; symétrique m=(y,1).
    ⇐ : z=(p,0)∈(A×B)⊔(A×C) (p∈A×B) ⇒ p=(pr₁p,pr₂p) (pr₁p∈A, pr₂p∈B) ; antécédent
        t₀=(pr₁p,(pr₂p,0))∈A×(B⊔C), D(t₀)=T[t₀]=((pr₁p,pr₂p),0)=(p,0)=z ; symétrique."""
    va, vb, vc = _t(a), _t(b), _t(c)
    BC = somme_disjointe(vb, vc)
    Dom = E.produit(va, BC)
    AB = E.produit(va, vb)                                   # A×B
    AC = E.produit(va, vc)                                   # A×C
    Cod = somme_disjointe(AB, AC)                            # (A×B)⊔(A×C)
    T = _distrib_terme("k")
    K = E.graphe_terme(Dom, T, "k")
    vz = var("z")
    # caractérisation de l'image (liant t)
    ax_img = N.axiome(E.theorie_ensembles(), E.AXIOME_IMAGE)
    img_car0 = instancie(instancie(instancie(ax_img, K), Dom), vz)
    inner_x = et(appartient(var("x"), Dom), appartient(E.couple(var("x"), vz), K))
    ren = alpha_existe("x", "t", inner_x)
    img_car = equivalence_transitivite(img_car0, ren)       # z∈D⟨Dom⟩ ⇔ (∃t)(t∈Dom et (t,z)∈D)
    vt = var("t")

    # ── ⇒ : z∈D⟨Dom⟩ ⇒ z∈(A×B)⊔(A×C) ────────────────────────────────────────
    bodyR = et(appartient(vt, Dom), appartient(E.couple(vt, vz), K))
    hbR = N.assume(bodyR)
    t_in = conjonction_elim_gauche(hbR)                     # t∈Dom
    cpl_in = conjonction_elim_droite(hbR)                   # (t,z)∈D
    mem = membre_graphe_terme(Dom, T, "t", "m", "k", "yb")  # ((t,m)∈D)⇔(t∈Dom et m=T[t]) ; coord m≠y
    mem_z = instancie(N.generalisation("m", mem), vz)       # ((t,z)∈D)⇔(t∈Dom et z=T[t])
    z_eq_Tt = conjonction_elim_droite(N.modus_ponens(cpl_in, equivalence_avant(mem_z)))  # z=T[t]
    # décomposer t∈A×(B⊔C) en (x,m)  : t∈Dom ⇔ (∃e)(∃f)((t=(e,f) et e∈A) et f∈B⊔C)
    prod_car0 = _inst_produit(va, BC, vt)                   # liants p,q internes
    inner_q = et(et(egal(vt, E.couple(var("p"), var("q"))), appartient(var("p"), va)),
                 appartient(var("q"), BC))
    ren_f = alpha_existe("q", "f", inner_q)                 # (∃q)…q… ⇔ (∃f)…f…
    inner_ef = et(et(egal(vt, E.couple(var("p"), var("f"))), appartient(var("p"), va)),
                  appartient(var("f"), BC))
    ren_e = alpha_existe("p", "e", existe("f", inner_ef))   # (∃p)(∃f)… ⇔ (∃e)(∃f)…
    ren_f_under_p = congruence_existe(ren_f, "p")           # (∃p)(∃q)… ⇔ (∃p)(∃f)…
    prod_car = equivalence_transitivite(prod_car0,
                  equivalence_transitivite(ren_f_under_p, ren_e))   # t∈Dom ⇔ (∃e)(∃f)bodyF
    ve, vf = var("e"), var("f")
    bodyF = et(et(egal(vt, E.couple(ve, vf)), appartient(ve, va)), appartient(vf, BC))
    hF = N.assume(bodyF)
    t_eq_ef = conjonction_elim_gauche(conjonction_elim_gauche(hF))  # t=(e,f)
    e_in_A = conjonction_elim_droite(conjonction_elim_gauche(hF))  # e∈A
    f_in_BC = conjonction_elim_droite(hF)                         # f∈B⊔C
    # décomposer f∈B⊔C : f=(y,0) (y∈B) ou f=(y,1) (y∈C)  (membre_somme_caracterise)
    dec_f0 = N.modus_ponens(f_in_BC, equivalence_avant(membre_somme_caracterise(b, c, vf)))
    exB0, exC0 = dec_f0.conclusion.sous[0], dec_f0.conclusion.sous[1]
    renB = alpha_existe(exB0.lieur, "g1", exB0.sous[0])
    renC = alpha_existe(exC0.lieur, "g2", exC0.sous[0])
    dec_f = N.modus_ponens(dec_f0, equivalence_avant(_ou_congruence(renB, renC)))
    exB, exC = dec_f.conclusion.sous[0], dec_f.conclusion.sous[1]
    nB, bB = exB.lieur, exB.sous[0]      # g1 ; (g1∈B et f=(g1,0))
    nC, bC = exC.lieur, exC.sous[0]      # g2 ; (g2∈C et f=(g2,1))

    def fwd_copy(witness_name, marker, body_w, in_set, inj_into):
        """copie : témoin w∈in_set, f=(w,marker) ⊢ z∈(A×B)⊔(A×C)."""
        vw = var(witness_name)
        wm = E.couple(vw, marker)                           # (w,marker)
        hw = N.assume(body_w)
        w_in = conjonction_elim_gauche(hw)                  # w∈in_set
        f_eq = conjonction_elim_droite(hw)                  # f=(w,marker)
        # t = (e, f) = (e, (w,marker))
        f_to_wm = N.modus_ponens(f_eq, congruence_terme(vf, wm, E.couple(ve, var("w"))))   # (e,f)=(e,(w,marker))
        t_eq_cpl = composer_egalites(t_eq_ef, f_to_wm)      # t=(e,(w,marker))
        cpl = E.couple(ve, wm)                              # (e,(w,marker))
        # T[t] = T[(e,(w,marker))] = ((e,w),marker)  via Leibniz + _T_sur_couple
        Tt = subst_t(vt, "k", T)
        Tcpl = subst_t(cpl, "k", T)
        Tt_Tcpl = N.modus_ponens(t_eq_cpl, N.s6(vt, cpl, "w",
                                    egal(subst_t(vt, "k", T), subst_t(var("w"), "k", T))))
        Tt_Tcpl = N.modus_ponens(N.reflexivite(Tt), equivalence_avant(Tt_Tcpl))   # T[t]=T[cpl]
        Tcpl_eq = _T_sur_couple(ve, vw, marker)             # T[(e,(w,marker))]=((e,w),marker)
        z_eq_cpl = composer_egalites(composer_egalites(z_eq_Tt, Tt_Tcpl), Tcpl_eq)   # z=((e,w),marker)
        # (e,w)∈prod_set (=A×B ou A×C)
        ew_in = N.modus_ponens(conjonction_intro(e_in_A, w_in),
                               _couple_dans_produit_t(ve, vw, va, in_set))   # (e,w)∈A×(B|C)
        ew = E.couple(ve, vw)
        # ((e,w),marker)∈(A×B)⊔(A×C)  via injection_gauche/droite
        cpl_in_cod = N.modus_ponens(ew_in, inj_into(ew, AB, AC))   # ((e,w),marker)∈Cod
        # z=((e,w),marker) ⇒ z∈Cod
        z_in = N.modus_ponens(cpl_in_cod, equivalence_arriere(N.modus_ponens(
            z_eq_cpl, N.s6(vz, E.couple(ew, marker), "w", appartient(var("w"), Cod)))))
        return N.loi_deduction(body_w, z_in)                # body_w ⇒ z∈Cod

    impB = existe_elimination(fwd_copy(nB, ZERO, bB, vb,
        lambda ew, ab, ac: injection_gauche_dans_somme(ew, ab, ac)), nB)
    impC = existe_elimination(fwd_copy(nC, UN, bC, vc,
        lambda ew, ab, ac: injection_droite_dans_somme(ew, ab, ac)), nC)
    z_in_cod = cas(dec_f, impB, impC)                       # z∈Cod  [sous bodyF]
    fwd_inner = existe_elimination(existe_elimination(
        N.loi_deduction(bodyF, z_in_cod), "f"), "e")        # (∃e)(∃f)bodyF ⇒ z∈Cod
    fwd_t = syllogisme(equivalence_avant(prod_car), fwd_inner)  # t∈Dom ⇒ z∈Cod
    # combiner avec z=T[t] : on a sous bodyR  z=T[t] et t∈Dom ; donc z∈Cod
    z_in_cod_R = N.modus_ponens(t_in, fwd_t)                # z∈Cod  [sous bodyR]
    fwd = existe_elimination(N.loi_deduction(bodyR, z_in_cod_R), "t")
    fwd_full = syllogisme(equivalence_avant(img_car), fwd)  # z∈D⟨Dom⟩ ⇒ z∈Cod

    # ── ⇐ : z∈(A×B)⊔(A×C) ⇒ z∈D⟨Dom⟩ ─────────────────────────────────────────
    bwd_full = _distrib_image_backward(a, b, c, vz, K, Dom, Cod, T, img_car, bodyR)

    equiv_z = conjonction_intro(fwd_full, bwd_full)
    char_u = N.generalisation("z", equiv_z)
    selfCod = N.generalisation("z", conjonction_intro(
        a_implique_a(appartient(vz, Cod)), a_implique_a(appartient(vz, Cod))))
    return egalite_par_extension(char_u, selfCod, E.image(K, Dom), Cod, "z")


def _distrib_image_backward(a, b, c, vz, K, Dom, Cod, T, img_car, bodyR):
    """z∈(A×B)⊔(A×C) ⇒ z∈D⟨Dom⟩  (surjectivité, sens réciproque).

    z=(p,0)∈Cod (p∈A×B) → p=(pr₁p,pr₂p) (pr₁p∈A, pr₂p∈B) ; t₀=(pr₁p,(pr₂p,0))∈Dom,
    D(t₀)=T[t₀]=((pr₁p,pr₂p),0)=(p,0)=z → (t₀,z)∈D → z∈D⟨Dom⟩.  Symétrique à droite."""
    va, vb, vc = _t(a), _t(b), _t(c)
    AB = E.produit(va, vb)
    AC = E.produit(va, vc)
    # décomposer z∈Cod
    dec_z0 = N.modus_ponens(N.assume(appartient(vz, Cod)),
                            equivalence_avant(membre_somme_caracterise(AB, AC, vz)))
    exP0, exQ0 = dec_z0.conclusion.sous[0], dec_z0.conclusion.sous[1]
    renP = alpha_existe(exP0.lieur, "n1", exP0.sous[0])
    renQ = alpha_existe(exQ0.lieur, "n2", exQ0.sous[0])
    dec_z = N.modus_ponens(dec_z0, equivalence_avant(_ou_congruence(renP, renQ)))
    exP, exQ = dec_z.conclusion.sous[0], dec_z.conclusion.sous[1]
    nP, bP = exP.lieur, exP.sous[0]        # n1 ; (n1∈A×B et z=(n1,0))
    nQ, bQ = exQ.lieur, exQ.sous[0]        # n2 ; (n2∈A×C et z=(n2,1))

    def back_copy(witness_name, marker, body_p, prod_set, val_lemma):
        """copie : p∈prod_set, z=(p,marker) ⊢ z∈D⟨Dom⟩."""
        vp = var(witness_name)
        hp = N.assume(body_p)
        p_in = conjonction_elim_gauche(hp)             # p∈A×prod (=A×B ou A×C)
        z_eq = conjonction_elim_droite(hp)             # z=(p,marker)
        # p=(pr₁p,pr₂p), pr₁p∈A, pr₂p∈prod_set.  LIANTS « r1,r2 » des projections de p
        # ≠ a,b,c,d internes de _T_sur_couple (évite la capture quand pr₂p est
        # nourri à distrib_graphe_valeur_* comme coordonnée).
        pr1p, pr2p = E.pr1(vp, "r1", "r2"), E.pr2(vp, "r1", "r2")
        p_rec = N.modus_ponens(p_in, N.loi_deduction(appartient(vp, E.produit(va, prod_set)),
                                _membre_produit_egal_couple_ab(va, prod_set, witness_name, "r1", "r2")))  # p=(pr₁p,pr₂p)
        pr1p_in = N.modus_ponens(p_in, N.loi_deduction(appartient(vp, E.produit(va, prod_set)),
                                _membre_produit_pr1_ab(va, prod_set, witness_name, "r1", "r2")))   # pr₁p∈A
        pr2p_in = N.modus_ponens(p_in, N.loi_deduction(appartient(vp, E.produit(va, prod_set)),
                                _membre_produit_pr2_ab(va, prod_set, witness_name, "r1", "r2")))   # pr₂p∈prod_set
        # antécédent t₀ = (pr₁p, (pr₂p, marker)) ∈ Dom
        t0 = E.couple(pr1p, E.couple(pr2p, marker))
        t0_in = N.modus_ponens(conjonction_intro(pr1p_in, pr2p_in),
            _couple_dans_domaine_t(pr1p, pr2p, marker, va, vb, vc))   # t₀∈A×(B⊔C)
        # D(t₀)=T[t₀]=((pr₁p,pr₂p),marker)  via val_lemma sous {pr₁p∈A, pr₂p∈prod_set}
        Dt0 = val_lemma(pr1p, pr2p)                    # {pr₁p∈A, pr₂p∈prod_set}⊢D(t₀)=((pr₁p,pr₂p),marker)
        Dt0 = N.modus_ponens(pr1p_in, N.loi_deduction(appartient(pr1p, va), Dt0))     # décharge pr₁p∈A
        Dt0 = N.modus_ponens(pr2p_in, N.loi_deduction(appartient(pr2p, prod_set), Dt0))  # décharge pr₂p∈prod_set
        # ((pr₁p,pr₂p),marker) = (p,marker) = z   (Leibniz p=(pr₁p,pr₂p) puis z=(p,marker))
        prp = E.couple(pr1p, pr2p)
        pmk_eq = N.modus_ponens(p_rec, congruence_terme(vp, prp, E.couple(var("w"), marker)))  # (p,marker)=(prp,marker)
        prpmk_eq_pmk = N.modus_ponens(pmk_eq, symetrie(E.couple(vp, marker), E.couple(prp, marker)))  # (prp,marker)=(p,marker)
        Dt0_eq_pmk = composer_egalites(Dt0, prpmk_eq_pmk)   # D(t₀)=(p,marker)
        pmk_eq_z = N.modus_ponens(z_eq, symetrie(vz, E.couple(vp, marker)))  # (p,marker)=z
        Dt0_eq_z = composer_egalites(Dt0_eq_pmk, pmk_eq_z)   # D(t₀)=z
        # z = T[t₀]  : D(t₀)=T[t₀] (val term) et z=D(t₀)
        Tt0 = subst_t(t0, "k", T)
        Dt0_Tt0 = N.modus_ponens(t0_in, N.loi_deduction(appartient(t0, Dom),
                                  _distrib_graphe_valeur_t(a, b, c, t0)))   # D(t₀)=T[t₀]
        z_eq_Dt0 = N.modus_ponens(Dt0_eq_z, symetrie(E.valeur(K, t0), vz))   # z=D(t₀)
        z_eq_Tt0 = composer_egalites(z_eq_Dt0, Dt0_Tt0)   # z=T[t₀]
        # (t₀,z)∈D  → z∈D⟨Dom⟩
        memb = _couple_dans_D(a, b, c, t0, vz, z_eq_Tt0, t0_in)   # (t₀,z)∈D
        wit = conjonction_intro(t0_in, memb)                     # t₀∈Dom et (t₀,z)∈D
        ex_t = N.modus_ponens(wit, N.s5(bodyR, t0, "t"))
        z_in_img = N.modus_ponens(ex_t, equivalence_arriere(img_car))   # z∈D⟨Dom⟩
        return N.loi_deduction(body_p, z_in_img)        # body_p ⇒ z∈D⟨Dom⟩

    impP = existe_elimination(back_copy(nP, ZERO, bP, vb,
        lambda p1, p2: distrib_graphe_valeur_gauche(a, b, c, p1, p2)), nP)
    impQ = existe_elimination(back_copy(nQ, UN, bQ, vc,
        lambda p1, p2: distrib_graphe_valeur_droite(a, b, c, p1, p2)), nQ)
    z_in_img = cas(dec_z, impP, impQ)                  # z∈D⟨Dom⟩  [sous z∈Cod]
    return N.loi_deduction(appartient(vz, Cod), z_in_img)   # z∈Cod ⇒ z∈D⟨Dom⟩


def _couple_dans_domaine_t(x, w, marker, va, vb, vc):
    """⊢ (x∈A et w∈(B|C)) ⇒ (x,(w,marker)) ∈ A×(B⊔C),  x,w TERMES (version close-implication)."""
    vx, vw = _t(x), _t(w)
    BC = somme_disjointe(vb, vc)
    wm = E.couple(vw, marker)
    h = N.assume(et(appartient(vx, va), appartient(vw, vb if marker is ZERO else vc)))
    if marker is ZERO:
        wm_in = N.modus_ponens(conjonction_elim_droite(h),
                               injection_gauche_dans_somme(vw, vb, vc))   # (w,0)∈B⊔C
    else:
        wm_in = N.modus_ponens(conjonction_elim_droite(h),
                               injection_droite_dans_somme(vw, vb, vc))   # (w,1)∈B⊔C
    cpl_in = N.modus_ponens(conjonction_intro(conjonction_elim_gauche(h), wm_in),
                            _couple_dans_produit_t(vx, wm, va, BC))   # (x,(w,m))∈A×(B⊔C)
    return N.loi_deduction(et(appartient(vx, va),
                              appartient(vw, vb if marker is ZERO else vc)), cpl_in)


# ── PALIER 6 : est_bijection_de(D, A×(B⊔C), (A×B)⊔(A×C)) puis Eq ──────────────
def _corps_pourtout(concl):
    """R tel que concl = pourtout(x, R)  (pourtout(x,R)=¬∃x¬R)."""
    return concl.sous[0].sous[0].sous[0]


def _renomme_injective(c3):
    """⊢ injective_dans(D,Dom) [liants s,sp] → même avec liants u,up (forme défaut).

    Renomme-α les deux ∀ (s→u puis sp→up) pour aligner sur est_bijection_de."""
    from bourbaki.logique.tactiques.tactiques_abrege_quantif import alpha_pour_tout, congruence_pour_tout
    R_outer = _corps_pourtout(c3.conclusion)              # (∀sp)body
    ren_outer = alpha_pour_tout("s", "u", R_outer)        # (∀s)R_outer ⇔ (∀u)(u|s)R_outer
    step1 = N.modus_ponens(c3, equivalence_avant(ren_outer))   # (∀u)(∀sp)body'
    Rin = _corps_pourtout(step1.conclusion)               # (∀sp)body' (sous u)
    body2 = _corps_pourtout(Rin)                          # body' (sous sp)
    ren_inner = alpha_pour_tout("sp", "up", body2)        # (∀sp)body2 ⇔ (∀up)…
    cong = congruence_pour_tout(ren_inner, "u")           # (∀u)(∀sp)… ⇔ (∀u)(∀up)…
    return N.modus_ponens(step1, equivalence_avant(cong))  # injective_dans(D,Dom) [u,up]


def distrib_est_bijection(a="A", b="B", c="C"):
    """⊢ est_bijection_de(D, A×(B⊔C), (A×B)⊔(A×C)).   (D = (x,(y,m))↦((x,y),m) bijection.)

    Les 4 conjoints : fonctionnel, domaine A×(B⊔C), injectif, image (A×B)⊔(A×C).
    est_bijection_de = ((func et dom) et (inj et img))."""
    func = distrib_graphe_fonctionnel(a, b, c)            # est_fonctionnel(D)
    dom = distrib_graphe_domaine(a, b, c)                 # dom D = A×(B⊔C)
    inj = _renomme_injective(distrib_graphe_injective(a, b, c))  # injective_dans(D, A×(B⊔C)) [u,up]
    img = distrib_graphe_image(a, b, c)                  # image(D, A×(B⊔C)) = (A×B)⊔(A×C)
    bijective = conjonction_intro(inj, img)              # est_bijective(D, Dom, Cod)
    return conjonction_intro(conjonction_intro(func, dom), bijective)


def eq_distributivite(a="A", b="B", c="C"):
    """⊢ Eq(A×(B⊔C), (A×B)⊔(A×C)).   (distributivité du produit sur la somme,
    à équipotence près, E.III.3.3.)

    Témoin = le graphe distributif D ; S5 sur est_bijection_de(F,·,·) donne
    (∃F)bij = Eq(A×(B⊔C), (A×B)⊔(A×C))."""
    from bourbaki.cardinaux.ensembles_cardinaux import est_bijection_de
    va, vb, vc = _t(a), _t(b), _t(c)
    Dom = E.produit(va, somme_disjointe(vb, vc))
    AB, AC = E.produit(va, vb), E.produit(va, vc)
    Cod = somme_disjointe(AB, AC)
    D = _distrib_graphe(a, b, c)
    bij = distrib_est_bijection(a, b, c)                 # est_bijection_de(D, Dom, Cod)
    return N.modus_ponens(bij, N.s5(est_bijection_de(var("F"), Dom, Cod), D, "F"))


def distributivite_cardinale(a="A", b="B", c="C"):
    """⊢ Card(A×(B⊔C)) = Card((A×B)⊔(A×C)).   (a·(b+c) = a·b + a·c, E.III.3.3, Prop. 3.)

    Eq(A×(B⊔C), (A×B)⊔(A×C)) (bijection distributive) ; la Proposition 1 (sens
    direct, version TERME _prop1_direct_t) conclut l'égalité des cardinaux.  Côté
    membre droit : Card((A×B)⊔(A×C)) = a·b + a·c (somme cardinale de produits
    cardinaux), côté gauche : Card(A×(B⊔C)) = a·(b+c)."""
    from bourbaki.cardinaux.arithmetique.ensembles_arith_cardinale import _prop1_direct_t
    va, vb, vc = _t(a), _t(b), _t(c)
    Dom = E.produit(va, somme_disjointe(vb, vc))
    AB, AC = E.produit(va, vb), E.produit(va, vc)
    Cod = somme_disjointe(AB, AC)
    eq = eq_distributivite(a, b, c)                      # Eq(A×(B⊔C), (A×B)⊔(A×C))
    prop1 = _prop1_direct_t(Dom, Cod)                    # Eq(...) ⇒ Card(...)=Card(...)
    return N.modus_ponens(eq, prop1)                     # Card(A×(B⊔C))=Card((A×B)⊔(A×C))


__all__ = ["somme_disjointe", "ZERO", "UN",
           "distrib_graphe_fonctionnel", "distrib_graphe_domaine",
           "distrib_graphe_valeur", "distrib_graphe_valeur_gauche",
           "distrib_graphe_valeur_droite", "distrib_graphe_injective",
           "distrib_graphe_image", "distrib_est_bijection",
           "eq_distributivite", "distributivite_cardinale"]
