"""§III.3.5 — Card(𝔓(X)) = 2^Card X  (Proposition 12) : FINITION — EMBALLAGE TRIPLE
de la fonction caractéristique χ_Y et UN SENS DU ROUND-TRIP (ρ∘χ = id sur 𝔓X).

Ce module ASSEMBLE l'infra des rounds 24/25/26 (rien redéfini, additif) pour
fermer les DEUX premières étapes du plan de la Proposition 12 :

  ÉTAPE 1 — χ_Y est une APPLICATION X → 2  (emballage TRIPLE 𝓕(X;2)) :
    • chi_inclus_produit(Y,X)   {Y⊂X} ⊢ χ_Y ⊂ X×2          [tout couple est (z,1) z∈Y⊂X
          ou (z,0) z∈X∖Y⊂X ; 1,0 ∈ 2 = {∅,{∅}}] ;
    • chi_dans_exposant(Y,X)    {Y⊂X} ⊢ χ_Y ∈ 2^X           [axiome_exposant : G⊂X×2
          ∧ G fonctionnel (round 26) ∧ dom G = X (round 26)] ;
    • chi_appli(Y,X)            le TRIPLE ((χ_Y, X), 2)        [une application = triple] ;
    • chi_dans_applications(Y,X){Y⊂X} ⊢ chi_appli(Y) ∈ 𝓕(X;2) [axiome_applications,
          témoin G = χ_Y].

  ÉTAPE 2 — ROUND-TRIP ρ∘χ = id sur 𝔓X  (ρ lit le graphe sous-jacent χ_Y) :
    • couple_un_dans_chi(Y,X,z) ⊢ ((z,1) ∈ χ_Y) ⇔ (z ∈ Y)    [⇐ chi_valeur_dans_Y ;
          ⇒ : hors Y, χ_Y donne (z,0), et 1=0 contredit 0≠1 (deux_elements_distincts)] ;
    • rho_chi_identite(Y,X)     {Y⊂X} ⊢ Pre(χ_Y) = Y           [Pre(χ_Y)={z∈X|(z,1)∈χ_Y}
          = {z∈X | z∈Y} = Y, par A1 ; ρ appliqué au GRAPHE χ_Y récupère Y].

Le pont graphe↔triple : une application f∈𝓕(E;F) est le TRIPLE ((G,E),F) de son
graphe G (axiome_applications) ; ρ (round 24, `preimage_un`) lit (z,1)∈f sur le
terme f passé.  Ici on relie χ (qui PRODUIT le graphe χ_Y) et ρ (qui LIT le
graphe) en appliquant ρ au graphe sous-jacent χ_Y — exactement l'alignement
demandé par la fiche (preimage lit (z,1)∈f sur le graphe).

REPORTÉ (raison précise dans `bijection_prop12_REPORTE`) : l'autre sens du
round-trip χ∘ρ = id sur 𝓕(X;2) (extensionnalité fonctionnelle sur le graphe d'une
f arbitraire), la bijection complète χ : 𝔓X → 𝓕(X;2), Card 𝔓X = 2^Card X, et la
restatement de Cantor 2^Card X > Card X.  Ce module livre l'EMBALLAGE TRIPLE
(χ_Y ∈ 𝓕(X;2)) et le SENS ρ∘χ = id, le crux graphe↔triple demandé.
"""
from __future__ import annotations

from bourbaki.logique.formule import (Terme, var, egal, et, non, ou, impl, equiv,
                     appartient, existe, pourtout, inclus, subst_t)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.logique.tactiques.tactiques_abrege import a_implique_a, syllogisme
from bourbaki.logique.tactiques.tactiques_abrege2 import (conjonction_intro,
                               conjonction_elim_gauche, conjonction_elim_droite,
                               equivalence_avant, equivalence_arriere,
                               equivalence_transitivite, instancie, cas)
from bourbaki.logique.tactiques.tactiques_abrege_egalite import (symetrie,
                               composer_egalites, congruence_terme)
from bourbaki.logique.tactiques.tactiques_abrege_quantif import existe_elimination
from bourbaki.ensembles.ensembles_theoremes import extensionnalite_appliquee
# socle 2-élément (0=∅, 1={∅}) — RÉUTILISÉ, jamais redéfini :
from bourbaki.ensembles.familles.ensembles_somme_disjointe import ZERO, UN
# infra réunion de graphes (recollement) — RÉUTILISÉE :
from bourbaki.ensembles.fonctions.hors_ii_3.iii_3_recollement.ensembles_restriction_somme import (
    membre_reunion_graphes, _ex_falso)
# infra graphe-terme (constante) — RÉUTILISÉE :
from bourbaki.ensembles.fonctions.ii_3_6_fonction_terme.ensembles_fonction_terme import membre_graphe_terme
# produit binaire — RÉUTILISÉ :
from bourbaki.ensembles.familles.ensembles_produit import couple_dans_produit
# ── ACQUIS round 26 (χ_Y fonction X→{0,1}) — RÉUTILISÉS, jamais redéfinis ──
from bourbaki.cardinaux.arithmetique.ensembles_prop12_powerset import (
    chi, _chi_gauche, _chi_droite, chi_fonctionnel, chi_domaine,
    chi_valeur_dans_Y, chi_valeur_hors_Y)
# ── ACQUIS round 24 (ρ : 𝓕(X;2)→𝔓X, sens facile) — RÉUTILISÉS ──
from bourbaki.cardinaux.arithmetique.ensembles_powerset_deux import (
    preimage_un, preimage_membre)
# ── socle 2-élément (0≠1, 0∈2, 1∈2) — RÉUTILISÉS ──
from bourbaki.cardinaux.arithmetique.ensembles_powerset_exp import (
    deux, deux_elements_distincts, zero_dans_deux, un_dans_deux)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# ═══════════════════════════════════════════════════════════════════════════════
# ÉTAPE 1a — χ_Y ⊂ X × 2   (tout couple de χ_Y est (z,1) z∈Y⊂X ou (z,0) z∈X∖Y⊂X)
# ═══════════════════════════════════════════════════════════════════════════════
def _graphe_terme_inclus(a, t, ainc, b, hzinA, hTinB, z="z"):
    """⊢ graphe_terme(A,T) ⊂ Ainc × B,   sous   {A ⊂ Ainc}  et  ⊢ T ∈ B  (T constant).

    Tout z'∈graphe_terme(A,T) s'écrit (z, T) avec z∈A (membre_graphe_terme,
    généralisé) ; A⊂Ainc donne z∈Ainc, T∈B donne T∈B, donc (z,T)∈Ainc×B
    (couple_dans_produit) ; z' = (z,T) recolle.  T NE dépend PAS de z (constante)."""
    vA, vAi, vB = _t(a), _t(ainc), _t(b)
    F = E.graphe_terme(vA, t, "x")
    vzc = var(z)
    vu, vv = var("u"), var("v")          # u,v binders (≠ x,y liants internes du graphe-terme)
    # axiome C54 sur z', binders existentiels u,v : z'∈F ⇔ (∃u)(∃v)(z'=(u,v) et u∈A et v=T)
    th = E.theorie_graphe_terme(vA, t, "u", "v", "w")
    ax = N.axiome(th, E.axiome_graphe_terme(vA, t, "u", "v", "w"))   # (∀w)(...)
    car = instancie(ax, vzc)                              # z'∈F ⇔ (∃u)(∃v)(z'=(u,v) et u∈A et v=T)
    body = et(et(egal(vzc, E.couple(vu, vv)), appartient(vu, vA)), egal(vv, t))
    # sous body : z'=(u,v), u∈A⊂Ainc, v=T∈B  →  (u,v)∈Ainc×B  →  z'∈Ainc×B (réécriture)
    hb = N.assume(body)
    z_eq_uv = conjonction_elim_gauche(conjonction_elim_gauche(hb))   # z'=(u,v)
    u_inA = conjonction_elim_droite(conjonction_elim_gauche(hb))     # u∈A
    v_eq_T = conjonction_elim_droite(hb)                            # v=T
    u_inAi = N.modus_ponens(u_inA, hzinA(vu))                       # u∈Ainc
    v_inB = N.modus_ponens(hTinB,                                   # v∈B (v=T, T∈B, Leibniz S6)
        equivalence_arriere(N.modus_ponens(v_eq_T,
            N.s6(vv, t, "w", appartient(var("w"), vB)))))
    uv_in_prod = N.modus_ponens(conjonction_intro(u_inAi, v_inB),
                                _couple_dans_produit_imp(vu, vv, vAi, vB))   # (u,v)∈Ainc×B
    z_in_prod = N.modus_ponens(uv_in_prod, equivalence_arriere(N.modus_ponens(
        z_eq_uv, N.s6(vzc, E.couple(vu, vv), "w",
                      appartient(var("w"), E.produit(vAi, vB))))))  # z'∈Ainc×B
    imp_body = N.loi_deduction(body, z_in_prod)           # body ⇒ z'∈Ainc×B
    elim = existe_elimination(existe_elimination(imp_body, "v"), "u")  # (∃u∃v)body ⇒ z'∈prod
    hz = N.assume(appartient(vzc, F))
    ex_body = N.modus_ponens(hz, equivalence_avant(car))  # (∃u)(∃v)body
    z_in_prod_final = N.modus_ponens(ex_body, elim)       # z'∈Ainc×B
    imp_z = N.loi_deduction(appartient(vzc, F), z_in_prod_final)
    return N.generalisation(z, imp_z)                     # F ⊂ Ainc×B


def _couple_dans_produit_imp(vu, vv, vA, vB):
    """⊢ (u∈A et v∈B) ⇒ (u,v)∈A×B  (généralisation en A,B puis instanciation aux termes)."""
    gen = N.generalisation("A", N.generalisation("B", couple_dans_produit("u", "v", "A", "B")))
    return instancie(instancie(gen, vA), vB)


def chi_inclus_produit(y="Y", x="X"):
    """{Y ⊂ X} ⊢ χ_Y ⊂ X × 2.   (χ_Y est un graphe de couples (z, w) avec z∈X, w∈2.)

    χ_Y = G ∪ H, G = Y×{1}, H = (X∖Y)×{0}.  z'∈χ_Y ⇒ z'∈G ou z'∈H.
      • z'∈G : z'=(z,1), z∈Y⊂X (Y⊂X), 1∈2 ⇒ z'∈X×2 ;
      • z'∈H : z'=(z,0), z∈X∖Y⊂X (AXIOME_DIFF), 0∈2 ⇒ z'∈X×2.
    Donc χ_Y ⊂ X×2 (le support de 2^X = {graphes ⊂ X×2 fonctionnels, dom=X})."""
    vy, vx = _t(y), _t(x)
    deux_ens = deux()
    G, H = _chi_gauche(vy), _chi_droite(vy, vx)
    GuH = E.reunion(G, H)
    diff = E.difference(vx, vy)
    hsub = N.assume(inclus(vy, vx))                       # Y ⊂ X

    # G ⊂ X×2  :  Y ⊂ X (hsub instancié) ,  1 = UN ∈ 2 (un_dans_deux)
    def zinX_from_Y(vz):
        return instancie(hsub, vz)                       # (z∈Y) ⇒ (z∈X)
    inclG = _graphe_terme_inclus(vy, UN, vx, deux_ens, zinX_from_Y, un_dans_deux())   # G ⊂ X×2

    # H ⊂ X×2  :  X∖Y ⊂ X (AXIOME_DIFF) ,  0 = ZERO ∈ 2 (zero_dans_deux)
    def zinX_from_diff(vz):
        return _diff_inclus_imp(vz, vx, vy)              # (z∈X∖Y) ⇒ (z∈X)
    inclH = _graphe_terme_inclus(diff, ZERO, vx, deux_ens, zinX_from_diff, zero_dans_deux())  # H ⊂ X×2

    # χ_Y = G∪H ⊂ X×2 : z'∈G∪H ⇒ (z'∈G ou z'∈H) ⇒ z'∈X×2 (cas)
    vz = var("z")
    car = membre_reunion_graphes(G, H, vz)               # z'∈G∪H ⇔ (z'∈G ou z'∈H)
    hz = N.assume(appartient(vz, GuH))
    disj = N.modus_ponens(hz, equivalence_avant(car))    # z'∈G ou z'∈H
    z_in_prod = cas(disj, instancie(inclG, vz), instancie(inclH, vz))   # z'∈X×2
    imp = N.loi_deduction(appartient(vz, GuH), z_in_prod)
    incl = N.generalisation("z", imp)                    # χ_Y ⊂ X×2  [sous Y⊂X]
    return N.loi_deduction(inclus(vy, vx), incl)         # ⊢ Y⊂X ⇒ χ_Y ⊂ X×2


def _diff_inclus_imp(vz, vx, vy):
    """⊢ (z ∈ X∖Y) ⇒ (z ∈ X).   (toute différence est incluse dans le minuende.)"""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_DIFF)  # (∀x)(∀y)(∀z)(z∈x∖y ⇔ (z∈x et ¬z∈y))
    car = instancie(instancie(instancie(ax, vx), vy), vz)   # z∈X∖Y ⇔ (z∈X et ¬z∈Y)
    hzd = N.assume(appartient(vz, E.difference(vx, vy)))
    z_inX = conjonction_elim_gauche(N.modus_ponens(hzd, equivalence_avant(car)))   # z∈X
    return N.loi_deduction(appartient(vz, E.difference(vx, vy)), z_inX)


# ═══════════════════════════════════════════════════════════════════════════════
# ÉTAPE 1b — χ_Y ∈ 2^X  (axiome_exposant : graphe ⊂ X×2, fonctionnel, dom = X)
# ═══════════════════════════════════════════════════════════════════════════════
def chi_dans_exposant(y="Y", x="X"):
    """{Y ⊂ X} ⊢ χ_Y ∈ 2^X.   (χ_Y est un GRAPHE FONCTIONNEL de X dans 2 = {0,1}.)

    axiome_exposant : G ∈ 2^X ⇔ (G ⊂ X×2 et G fonctionnel et dom G = X).  Les trois
    conjoints sont chi_inclus_produit (sous Y⊂X), chi_fonctionnel (round 26, clos),
    chi_domaine (round 26, sous Y⊂X)."""
    vy, vx = _t(y), _t(x)
    deux_ens = deux()
    chiY = chi(vy, vx)
    ax = N.axiome(E.theorie_exposant(vx, deux_ens), E.axiome_exposant(vx, deux_ens))  # (∀G)(...)
    car = instancie(ax, chiY)                            # χ_Y∈2^X ⇔ (χ_Y⊂X×2 et fonct et dom=X)
    hsub = N.assume(inclus(vy, vx))
    incl = N.modus_ponens(hsub, chi_inclus_produit(vy, vx))   # χ_Y ⊂ X×2
    fonct = chi_fonctionnel(vy, vx)                      # est_fonctionnel(χ_Y)  (clos)
    dom_eq = N.modus_ponens(hsub, chi_domaine(vy, vx))   # dom χ_Y = X
    corps = conjonction_intro(conjonction_intro(incl, fonct), dom_eq)
    in_exp = N.modus_ponens(corps, equivalence_arriere(car))  # χ_Y ∈ 2^X  [sous Y⊂X]
    return N.loi_deduction(inclus(vy, vx), in_exp)       # ⊢ Y⊂X ⇒ χ_Y ∈ 2^X


# ═══════════════════════════════════════════════════════════════════════════════
# ÉTAPE 1c — chi_appli(Y) = ((χ_Y, X), 2) ∈ 𝓕(X; 2)   (EMBALLAGE TRIPLE)
# ═══════════════════════════════════════════════════════════════════════════════
def chi_appli(y="Y", x="X"):
    """chi_appli(Y) := ((χ_Y, X), 2)   (l'APPLICATION X→2 de graphe χ_Y, Déf. 4).

    Une application de 𝓕(X;2) est le triple (graphe, source, but) ; ici graphe χ_Y,
    source X, but 2 = {∅, {∅}}.  C'est l'image de Y ⊂ X par la bijection χ : 𝔓X → 𝓕(X;2)."""
    vy, vx = _t(y), _t(x)
    return E.couple(E.couple(chi(vy, vx), vx), deux())


def chi_dans_applications(y="Y", x="X"):
    """{Y ⊂ X} ⊢ chi_appli(Y) ∈ 𝓕(X; 2).   (l'EMBALLAGE TRIPLE est une APPLICATION.)

    axiome_applications : t∈𝓕(X;2) ⇔ (∃G)(t=((G,X),2) et G∈2^X).  Témoin G = χ_Y :
    chi_appli(Y) = ((χ_Y,X),2) (réflexivité) et χ_Y∈2^X (chi_dans_exposant, sous Y⊂X)."""
    vy, vx = _t(y), _t(x)
    deux_ens = deux()
    chiY = chi(vy, vx)
    triple = chi_appli(vy, vx)
    ax = N.axiome(E.theorie_applications(vx, deux_ens), E.axiome_applications(vx, deux_ens))  # (∀t)(...)
    car = instancie(ax, triple)                          # triple∈𝓕(X;2) ⇔ (∃G)(triple=((G,X),2) et G∈2^X)
    hsub = N.assume(inclus(vy, vx))
    in_exp = N.modus_ponens(hsub, chi_dans_exposant(vy, vx))   # χ_Y ∈ 2^X
    # corps témoin G:=χ_Y : (triple = ((χ_Y,X),2)) et χ_Y∈2^X
    refl = N.reflexivite(triple)                         # triple = ((χ_Y,X),2)
    wit = conjonction_intro(refl, in_exp)                # = (χ_Y|G)body
    # (∃G)body
    body = et(egal(triple, E.couple(E.couple(var("G"), vx), deux_ens)),
              appartient(var("G"), E.exposant(vx, deux_ens)))
    ex_G = N.modus_ponens(wit, N.s5(body, chiY, "G"))    # (∃G)body
    in_appl = N.modus_ponens(ex_G, equivalence_arriere(car))   # triple ∈ 𝓕(X;2)  [sous Y⊂X]
    return N.loi_deduction(inclus(vy, vx), in_appl)      # ⊢ Y⊂X ⇒ chi_appli(Y) ∈ 𝓕(X;2)


# ═══════════════════════════════════════════════════════════════════════════════
# ÉTAPE 2a — (z, 1) ∈ χ_Y  ⇔  z ∈ Y   (la valeur 1 repère EXACTEMENT Y)
# ═══════════════════════════════════════════════════════════════════════════════
def couple_un_dans_chi(y="Y", x="X", z="z"):
    """⊢ ((z, 1) ∈ χ_Y) ⇔ (z ∈ Y).   (χ_Y(z)=1 ssi z∈Y ; 1 = {∅} = UN.)

    ⇐ : chi_valeur_dans_Y (round 26).
    ⇒ : (z,1)∈χ_Y ⇒ (z,1)∈G ou (z,1)∈H.  Si (z,1)∈H=(X∖Y)×{0}, membre_graphe_terme
        donne 1=0 (la 2ᵉ coord. vaut 0), contredisant 0≠1 (deux_elements_distincts)
        ⇒ ex falso ⇒ z∈Y.  Si (z,1)∈G=Y×{1}, membre_graphe_terme donne z∈Y."""
    vy, vx, vz = _t(y), _t(x), _t(z)
    G, H = _chi_gauche(vy), _chi_droite(vy, vx)
    diff = E.difference(vx, vy)
    cpl = E.couple(vz, UN)
    car_reun = membre_reunion_graphes(G, H, cpl)         # (z,1)∈χ_Y ⇔ ((z,1)∈G ou (z,1)∈H)

    # ── ⇒ : (z,1)∈χ_Y ⇒ z∈Y ──────────────────────────────────────────────────
    h = N.assume(appartient(cpl, E.reunion(G, H)))
    disj = N.modus_ponens(h, equivalence_avant(car_reun))   # (z,1)∈G ou (z,1)∈H
    # (z,1)∈G ⇒ z∈Y   (G = graphe_terme(Y,1) : 2ᵉ coord. = 1, 1ʳᵉ ∈ Y)
    carG_at = _membre_graphe_terme_coord(vy, UN, vz, UN)  # ((z,1)∈G) ⇔ (z∈Y et 1=1)
    hG = N.assume(appartient(cpl, G))
    z_inY_G = conjonction_elim_gauche(N.modus_ponens(hG, equivalence_avant(carG_at)))   # z∈Y
    brG = N.loi_deduction(appartient(cpl, G), z_inY_G)   # (z,1)∈G ⇒ z∈Y
    # (z,1)∈H ⇒ z∈Y   (H = graphe_terme(X∖Y,0) : (z,1)∈H ⇒ 1=0 ⇒ ⊥ ⇒ z∈Y)
    carH_at = _membre_graphe_terme_coord(diff, ZERO, vz, UN)   # ((z,1)∈H) ⇔ (z∈X∖Y et 1=0)
    hH = N.assume(appartient(cpl, H))
    un_eq_zero = conjonction_elim_droite(N.modus_ponens(hH, equivalence_avant(carH_at)))  # 1=0 (UN=ZERO)
    n_un_eq_zero = N.modus_ponens(deux_elements_distincts(),   # ¬(0=1) → ¬(1=0) par symétrie
                                  _non_egal_sym(ZERO, UN))
    z_inY_H = _ex_falso(un_eq_zero, n_un_eq_zero, appartient(vz, vy))   # z∈Y (ex falso)
    brH = N.loi_deduction(appartient(cpl, H), z_inY_H)   # (z,1)∈H ⇒ z∈Y
    z_inY = cas(disj, brG, brH)                          # z∈Y
    avant = N.loi_deduction(appartient(cpl, E.reunion(G, H)), z_inY)   # (z,1)∈χ_Y ⇒ z∈Y

    # ── ⇐ : z∈Y ⇒ (z,1)∈χ_Y ──────────────────────────────────────────────────
    hzY = N.assume(appartient(vz, vy))
    in_chi = N.modus_ponens(hzY, N.loi_deduction(appartient(vz, vy),
                            chi_valeur_dans_Y(vy, vx, z)))   # (z,1)∈χ_Y  [round 26]
    arriere = N.loi_deduction(appartient(vz, vy), in_chi)    # z∈Y ⇒ (z,1)∈χ_Y
    return conjonction_intro(avant, arriere)             # ((z,1)∈χ_Y) ⇔ (z∈Y)


def _membre_graphe_terme_coord(a, tconst, vz, vw):
    """⊢ ((z, W) ∈ graphe_terme(A,Tconst)) ⇔ (z∈A et W=Tconst),  Tconst CONSTANTE.

    membre_graphe_terme avec u libre puis fixé à z et v fixé à W (Tconst ne dépend
    pas de la variable liée, donc T[z]=Tconst)."""
    vA = _t(a)
    car_uv = membre_graphe_terme(vA, tconst, "u", "v", "x", "y")   # ((u,v)∈F)⇔(u∈A et v=Tconst)
    car_all = N.generalisation("u", N.generalisation("v", car_uv))
    return instancie(instancie(car_all, vz), vw)         # ((z,W)∈F) ⇔ (z∈A et W=Tconst)


def _non_egal_sym(a, b):
    """⊢ ¬(a=b) ⇒ ¬(b=a).   (contraposée de la symétrie de l'égalité.)

    symetrie(b,a) ⊢ (b=a) ⇒ (a=b) ; sa contraposée (tactiques_abrege2) est
    ⊢ ¬(a=b) ⇒ ¬(b=a)."""
    from bourbaki.logique.tactiques.tactiques_abrege2 import contraposition
    va, vb = _t(a), _t(b)
    sym = symetrie(vb, va)                                # ⊢ (b=a) ⇒ (a=b)
    return contraposition(sym)                            # ⊢ ¬(a=b) ⇒ ¬(b=a)


# ═══════════════════════════════════════════════════════════════════════════════
# ÉTAPE 2b — ROUND-TRIP  ρ(χ_Y) = Pre(χ_Y) = Y   (ρ lit le GRAPHE sous-jacent)
# ═══════════════════════════════════════════════════════════════════════════════
def rho_chi_identite(y="Y", x="X"):
    """{Y ⊂ X} ⊢ Pre(χ_Y) = Y.   (ρ∘χ = id sur 𝔓X : ρ appliqué au graphe χ_Y rend Y.)

    Pre(χ_Y) = {z∈X | (z,1)∈χ_Y} (round 24).  Par A1 (extensionnalité), double
    inclusion :
      ⊂ : z∈Pre(χ_Y) ⇒ z∈X et (z,1)∈χ_Y ⇒ z∈Y  (couple_un_dans_chi, sens ⇒) ;
      ⊃ : z∈Y ⇒ z∈X (Y⊂X) et (z,1)∈χ_Y (couple_un_dans_chi, sens ⇐) ⇒ z∈Pre(χ_Y).
    C'est le pont graphe↔triple demandé : ρ (qui LIT (z,1)∈f) appliqué au GRAPHE χ_Y
    (que χ PRODUIT) récupère exactement la partie de départ Y."""
    vy, vx = _t(y), _t(x)
    chiY = chi(vy, vx)
    Pre = preimage_un(chiY, vx)                          # {z∈X | (z,1)∈χ_Y}
    vz = var("z")
    hsub = N.assume(inclus(vy, vx))                      # Y ⊂ X
    car_pre = preimage_membre(chiY, vx, vz)              # z∈Pre(χ_Y) ⇔ (z∈X et (z,1)∈χ_Y)
    car_un = couple_un_dans_chi(vy, vx, "z")             # (z,1)∈χ_Y ⇔ z∈Y

    # ── ⊂ : z∈Pre(χ_Y) ⇒ z∈Y ──────────────────────────────────────────────────
    hz = N.assume(appartient(vz, Pre))
    conj = N.modus_ponens(hz, equivalence_avant(car_pre))   # z∈X et (z,1)∈χ_Y
    z1_in = conjonction_elim_droite(conj)               # (z,1)∈χ_Y
    z_inY = N.modus_ponens(z1_in, equivalence_avant(car_un))   # z∈Y
    fwd = N.loi_deduction(appartient(vz, Pre), z_inY)   # z∈Pre ⇒ z∈Y
    incl_PY = N.generalisation("z", fwd)                # Pre ⊂ Y

    # ── ⊃ : z∈Y ⇒ z∈Pre(χ_Y) ──────────────────────────────────────────────────
    hzY = N.assume(appartient(vz, vy))                  # z∈Y
    z_inX = N.modus_ponens(hzY, instancie(hsub, vz))    # z∈X  (Y⊂X)
    z1_in2 = N.modus_ponens(hzY, equivalence_arriere(car_un))   # (z,1)∈χ_Y
    z_inPre = N.modus_ponens(conjonction_intro(z_inX, z1_in2),
                             equivalence_arriere(car_pre))   # z∈Pre(χ_Y)
    bwd = N.loi_deduction(appartient(vz, vy), z_inPre)  # z∈Y ⇒ z∈Pre
    incl_YP = N.generalisation("z", bwd)                # Y ⊂ Pre

    ext = extensionnalite_appliquee(Pre, vy)            # (Pre⊂Y et Y⊂Pre) ⇒ Pre=Y
    eq = N.modus_ponens(conjonction_intro(incl_PY, incl_YP), ext)   # Pre(χ_Y) = Y  [sous Y⊂X]
    return N.loi_deduction(inclus(vy, vx), eq)          # ⊢ Y⊂X ⇒ Pre(χ_Y) = Y


# ═══════════════════════════════════════════════════════════════════════════════
# CRUX REPORTÉ : la bijection complète + Card 𝔓X = 2^Card X + Cantor restaté
# ═══════════════════════════════════════════════════════════════════════════════
def bijection_prop12_REPORTE():
    """REPORTÉ (non clos) — bijection χ : 𝔓X → 𝓕(X;2), Card 𝔓X = 2^Card X, Cantor.

    Ce module CLÔT l'EMBALLAGE TRIPLE (χ_Y ∈ 𝓕(X;2), chi_dans_applications) et le
    SENS ρ∘χ = id sur 𝔓X (rho_chi_identite : Pre(χ_Y) = Y) — le crux graphe↔triple.
    Restent REPORTÉS :
      (iii) χ∘ρ = id sur 𝓕(X;2) : pour f∈𝓕(X;2) arbitraire, χ_{Pre(f)} = f par
            graphe_egal_par_valeurs (extensionnalité fonctionnelle) — exige de relier
            le graphe sous-jacent de f (pr₁(pr₁ f)) aux valeurs de χ_{Pre(f)} sur tout
            X (f(z)=1 ⇔ z∈Pre(f) ⇔ (z,1)∈f) ; volumineux, round dédié ;
      (iv)  BIJECTION : assembler le graphe { (Y, chi_appli(Y)) | Y∈𝔓X } et prouver
            fonctionnel/dom=𝔓X/injectif/image=𝓕(X;2) (injectivité depuis ρ∘χ=id,
            surjectivité depuis χ∘ρ=id), puis Eq(𝔓X, 𝓕(X;2)) (témoin S5) ;
      (v)   _prop1_direct_t : Card 𝔓X = Card 𝓕(X;2) = 2^Card X (exposant_deux_base) ;
      (vi)  Cantor restaté : cantor_strict + (v) ⇒ 2^Card X > Card X (Théorème 2).
    L'emballage triple (ÉTAPE 1) et ρ∘χ=id (ÉTAPE 2) sont le gain de ce round."""
    raise NotImplementedError(
        "Bijection complète χ : 𝔓X → 𝓕(X;2) reportée : χ∘ρ=id (extensionnalité "
        "fonctionnelle sur le graphe d'une f arbitraire) + assemblage du graphe "
        "bijectif + Card 𝔓X = 2^Card X + Cantor restaté. Ce module livre l'EMBALLAGE "
        "TRIPLE χ_Y∈𝓕(X;2) (ÉTAPE 1) et le SENS ρ∘χ=id, Pre(χ_Y)=Y (ÉTAPE 2).")


__all__ = [
    "chi_inclus_produit", "chi_dans_exposant",
    "chi_appli", "chi_dans_applications",
    "couple_un_dans_chi", "rho_chi_identite",
    "bijection_prop12_REPORTE",
]
