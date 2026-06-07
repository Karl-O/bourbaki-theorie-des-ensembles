"""§III.3.5 — Card(𝔓(X)) = 2^Card X  (E.III.3.5, Proposition 12) : LE SENS DIFFICILE
(la fonction caractéristique χ : 𝔓(X) → 𝓕(X; 2), Y ↦ χ_Y), construite MAINTENANT
par RECOLLEMENT de deux graphes constants à domaines disjoints (round 25).

Bourbaki (Prop. 12) : « Soient X un ensemble et a son cardinal ; le cardinal de
l'ensemble 𝔓(X) des parties de X est 2^a. »  Le « 2 » est le 2-élément
2 = {0, 1} = {∅, {∅}} = paire(∅, {∅}).  La preuve complète passe par la BIJECTION
        χ : 𝔓(X) → 𝓕(X; 2),   Y ↦ χ_Y   (x ↦ 1 si x∈Y, 0 sinon),
réciproque (à équipotence près) du SENS FACILE ρ : f ↦ f⁻¹(1) déjà certifié
(round 24, `ensembles_powerset_deux`).

CLÉ DE CONSTRUCTION (round 25) : χ_Y est définie « par cas » par RECOLLEMENT de
deux graphes CONSTANTS à domaines DISJOINTS :

    χ_Y  :=  recollement( graphe_terme(Y, 1) , graphe_terme(X∖Y, 0) )
          =  ( Y × {1} )  ∪  ( (X∖Y) × {0} )

  • graphe_terme(Y, 1)   = { (z, 1) | z ∈ Y }    = la fonction constante z↦1 sur Y ;
  • graphe_terme(X∖Y, 0) = { (z, 0) | z ∈ X∖Y }  = la fonction constante z↦0 sur X∖Y.

Domaines Y et X∖Y DISJOINTS (Y ∩ (X∖Y) = ∅, car z∈X∖Y ⇔ z∈X et ¬(z∈Y)) ⇒
reunion_graphes_fonctionnelle (round 25, PIVOT) donne χ_Y FONCTIONNEL, et
dom_reunion_graphes + graphe_terme_domaine donnent dom χ_Y = Y ∪ (X∖Y) = X (si Y⊂X).

═══════════════════════════════════════════════════════════════════════════════
PALIERS LIVRÉS (tous CERTIFIÉS par le noyau — rien postulé) :

PALIER 1 — χ_Y EST UNE FONCTION X → {0,1}  (le « gros gain » de la mission) :
  • chi(Y, X)                       le terme χ_Y = (Y×{1}) ∪ ((X∖Y)×{0})  (recollement) ;
  • chi_domaines_disjoints(Y, X)    ⊢ (∀u)¬(u∈dom(Y×{1}) et u∈dom((X∖Y)×{0}))  [Y∩(X∖Y)=∅] ;
  • chi_fonctionnel(Y, X)           ⊢ est_fonctionnel(χ_Y)        [PIVOT recollement] ;
  • chi_est_graphe(Y, X)            ⊢ est_un_graphe(χ_Y)          [réunion de 2 graphes] ;
  • chi_domaine(Y, X)               {Y⊂X} ⊢ dom(χ_Y) = X          [domaines recollés = Y∪(X∖Y)=X] ;
  • chi_valeur_dans_Y(Y, X, z)      {z∈Y} ⊢ (z, 1) ∈ χ_Y          [χ_Y(z)=1 sur Y] ;
  • chi_valeur_hors_Y(Y, X, z)      {z∈X∖Y} ⊢ (z, 0) ∈ χ_Y        [χ_Y(z)=0 hors Y].

(Le pont vers l'ÉNONCÉ-CIBLE Card(𝔓X)=2^Card X — bijection χ⇄ρ par
extensionnalité fonctionnelle puis _prop1_direct_t — est REPORTÉ : voir
`bijection_chi_complete_REPORTE`.)

Aucun fichier existant n'est modifié : ce module ne fait qu'ASSEMBLER l'infra des
rounds 24/25 (graphe_terme, reunion_graphes_fonctionnelle, dom_reunion_graphes,
graphe_terme_domaine) avec l'axiome de la différence (AXIOME_DIFF) pour la
disjonction des domaines.
"""
from __future__ import annotations

from bourbaki.logique.formule import (Terme, var, egal, et, non, ou, impl,
                     appartient, existe, pourtout, inclus, subst_t)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.logique.tactiques.tactiques_abrege import a_implique_a, syllogisme
from bourbaki.logique.tactiques.tactiques_abrege2 import (conjonction_intro,
                               conjonction_elim_gauche, conjonction_elim_droite,
                               equivalence_avant, equivalence_arriere,
                               equivalence_transitivite, instancie, contraposition)
from bourbaki.logique.tactiques.tactiques_abrege_egalite import (symetrie,
                               composer_egalites, congruence_terme)
# socle 2-élément (0=∅, 1={∅}) — RÉUTILISÉ, jamais redéfini :
from bourbaki.ensembles.familles.ensembles_somme_disjointe import ZERO, UN
# infra round 25 (recollement) — RÉUTILISÉE, jamais redéfinie :
from bourbaki.ensembles.fonctions.ensembles_restriction_somme import (
    recollement, reunion_graphes_fonctionnelle, dom_reunion_graphes,
    membre_reunion_graphes, _ex_falso)
# infra graphe-terme (constante) — RÉUTILISÉE, jamais redéfinie :
from bourbaki.ensembles.fonctions.ensembles_fonction_terme import (
    graphe_terme_fonctionnel, membre_graphe_terme)
from bourbaki.cardinaux.ensembles_cantor import (
    graphe_terme_domaine, graphe_terme_couple_dans)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# ═══════════════════════════════════════════════════════════════════════════════
# Les deux MORCEAUX CONSTANTS de χ_Y  (recollés sur des domaines disjoints)
# ═══════════════════════════════════════════════════════════════════════════════
def _chi_gauche(y):
    """χ_gauche := graphe_terme(Y, 1) = { (z, 1) | z ∈ Y } = Y × {1}  (z↦1 sur Y)."""
    return E.graphe_terme(_t(y), UN, "x")


def _chi_droite(y, x):
    """χ_droite := graphe_terme(X∖Y, 0) = { (z, 0) | z ∈ X∖Y } = (X∖Y) × {0}  (z↦0 hors Y)."""
    return E.graphe_terme(E.difference(_t(x), _t(y)), ZERO, "x")


def chi(y="Y", x="X"):
    """χ_Y := (Y × {1}) ∪ ((X∖Y) × {0})  = recollement(graphe_terme(Y,1), graphe_terme(X∖Y,0)).

    LA FONCTION CARACTÉRISTIQUE de Y ⊂ X (x↦1 si x∈Y, 0 sinon), définie « par
    cas » par RECOLLEMENT de deux graphes constants à domaines disjoints (Y et
    X∖Y).  C'est l'image de Y par la bijection χ : 𝔓(X) → 𝓕(X; 2) (Prop. 12)."""
    return recollement(_chi_gauche(y), _chi_droite(y, x))


# ═══════════════════════════════════════════════════════════════════════════════
# PALIER 1a — DISJONCTION DES DOMAINES  (Y ∩ (X∖Y) = ∅, car z∈X∖Y ⇔ z∈X et ¬(z∈Y))
# ═══════════════════════════════════════════════════════════════════════════════
def _membre_diff(z, x, y):
    """⊢ (z ∈ X∖Y) ⇔ (z∈X et ¬(z∈Y)).   (instance d'AXIOME_DIFF aux termes X, Y, z.)"""
    vz, vx, vy = _t(z), _t(x), _t(y)
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_DIFF)      # (∀x)(∀y)(∀z)(z∈x∖y ⇔ (z∈x et ¬z∈y))
    return instancie(instancie(instancie(ax, vx), vy), vz)


def domaines_recolle_disjoints(y="Y", x="X", u="u"):
    """⊢ ¬((u ∈ Y) et (u ∈ X∖Y)).   (Y et X∖Y sont disjoints : z∈X∖Y ⇒ ¬(z∈Y).)

    Si u∈Y et u∈X∖Y alors (AXIOME_DIFF) u∈X et ¬(u∈Y) ; or u∈Y, contradiction.
    Donc ¬(u∈Y et u∈X∖Y)."""
    vu, vy, vx = _t(u), _t(y), _t(x)
    diff = E.difference(vx, vy)
    car = _membre_diff(vu, vx, vy)                           # u∈X∖Y ⇔ (u∈X et ¬u∈Y)
    hboth = N.assume(et(appartient(vu, vy), appartient(vu, diff)))
    u_inY = conjonction_elim_gauche(hboth)                   # u∈Y
    u_inDiff = conjonction_elim_droite(hboth)                # u∈X∖Y
    n_u_inY = conjonction_elim_droite(                       # ¬(u∈Y)
        N.modus_ponens(u_inDiff, equivalence_avant(car)))
    # ex falso : de u∈Y et ¬(u∈Y) on tire n'importe quoi, ici ¬both
    cible = non(et(appartient(vu, vy), appartient(vu, diff)))
    absurd = _ex_falso(u_inY, n_u_inY, cible)               # ¬both   [sous both]
    # ⊢ both ⇒ ¬both, puis idempotence S1 → ¬both
    imp2 = N.loi_deduction(et(appartient(vu, vy), appartient(vu, diff)), absurd)
    return N.modus_ponens(imp2, N.s1(cible))                 # ¬(u∈Y et u∈X∖Y)


def chi_domaines_disjoints(y="Y", x="X"):
    """⊢ (∀u)¬((u ∈ dom(Y×{1})) et (u ∈ dom((X∖Y)×{0}))).

    L'hypothèse de DISJONCTION DES DOMAINES requise par le PIVOT du recollement
    (reunion_graphes_fonctionnelle).  dom(graphe_terme(Y,1)) = Y et
    dom(graphe_terme(X∖Y,0)) = X∖Y (graphe_terme_domaine) sont disjoints
    (domaines_recolle_disjoints), donc ¬(u∈dom_gauche et u∈dom_droite) pour tout u."""
    vy, vx = _t(y), _t(x)
    vu = var("u")
    G, H = _chi_gauche(vy), _chi_droite(vy, vx)
    domG_eq_Y = graphe_terme_domaine(vy, UN, "x", "y", "z")          # dom(Y×{1}) = Y
    domH_eq_Diff = graphe_terme_domaine(E.difference(vx, vy), ZERO, "x", "y", "z")  # dom((X∖Y)×{0})=X∖Y
    diff = E.difference(vx, vy)
    # ¬(u∈Y et u∈X∖Y)  →  ¬(u∈dom G et u∈dom H)  (réécriture Y→dom G, X∖Y→dom H par symétrie)
    base = domaines_recolle_disjoints(vy, vx, vu)                    # ¬(u∈Y et u∈X∖Y)
    # u∈dom G ⇔ u∈Y  (de dom G = Y, Leibniz S6)
    dG_to_Y = N.s6(E.dom(G), vy, "w", appartient(vu, var("w")))
    leibG = N.modus_ponens(domG_eq_Y, dG_to_Y)                       # (u∈dom G) ⇔ (u∈Y)
    dH_to_Diff = N.s6(E.dom(H), diff, "w", appartient(vu, var("w")))
    leibH = N.modus_ponens(domH_eq_Diff, dH_to_Diff)                 # (u∈dom H) ⇔ (u∈X∖Y)
    # sous (u∈dom G et u∈dom H) : u∈Y et u∈X∖Y → contradiction avec base
    hdom = N.assume(et(appartient(vu, E.dom(G)), appartient(vu, E.dom(H))))
    u_inY = N.modus_ponens(conjonction_elim_gauche(hdom), equivalence_avant(leibG))   # u∈Y
    u_inDiff = N.modus_ponens(conjonction_elim_droite(hdom), equivalence_avant(leibH))  # u∈X∖Y
    cible = non(et(appartient(vu, E.dom(G)), appartient(vu, E.dom(H))))
    # base = ¬(u∈Y et u∈X∖Y) ; both_YDiff = (u∈Y et u∈X∖Y) ; ex falso
    both_YDiff = conjonction_intro(u_inY, u_inDiff)                  # u∈Y et u∈X∖Y
    absurd = _ex_falso(both_YDiff, base, cible)                      # ¬both_dom  [sous hdom]
    imp2 = N.loi_deduction(et(appartient(vu, E.dom(G)), appartient(vu, E.dom(H))), absurd)
    ndom = N.modus_ponens(imp2, N.s1(cible))                         # ¬(u∈dom G et u∈dom H)
    return N.generalisation("u", ndom)


# ═══════════════════════════════════════════════════════════════════════════════
# PALIER 1b — χ_Y EST FONCTIONNEL  (PIVOT du recollement, domaines disjoints)
# ═══════════════════════════════════════════════════════════════════════════════
def chi_fonctionnel(y="Y", x="X"):
    """⊢ est_fonctionnel(χ_Y).   (χ_Y = G∪H, G,H fonctionnels à domaines disjoints.)

    G = Y×{1} et H = (X∖Y)×{0} sont fonctionnels (graphe_terme_fonctionnel) et
    leurs domaines sont disjoints (chi_domaines_disjoints) : le PIVOT
    reunion_graphes_fonctionnelle conclut que G∪H = χ_Y est fonctionnel —
    aucun conflit de valeur (chaque z est traité par UNE seule branche)."""
    vy, vx = _t(y), _t(x)
    G, H = _chi_gauche(vy), _chi_droite(vy, vx)
    fG = graphe_terme_fonctionnel(vy, UN, "x", "y")                  # G fonctionnel
    fH = graphe_terme_fonctionnel(E.difference(vx, vy), ZERO, "x", "y")  # H fonctionnel
    disj = chi_domaines_disjoints(vy, vx)                            # (∀u)¬(u∈dom G et u∈dom H)
    # reunion_graphes_fonctionnelle : {fonct G, fonct H, disj} ⊢ fonct(G∪H)
    pivot = reunion_graphes_fonctionnelle(G, H)
    # décharger ses trois hypothèses dans l'ordre (G fonct, H fonct, disj)
    disj_form = pourtout("u", non(et(appartient(var("u"), E.dom(G)),
                                     appartient(var("u"), E.dom(H)))))
    imp = N.loi_deduction(E.est_fonctionnel(G),
            N.loi_deduction(E.est_fonctionnel(H),
              N.loi_deduction(disj_form, pivot)))
    return N.modus_ponens(disj, N.modus_ponens(fH, N.modus_ponens(fG, imp)))


# ═══════════════════════════════════════════════════════════════════════════════
# PALIER 1c — χ_Y EST UN GRAPHE  (réunion de deux graphes ⇒ tout élément couple)
# ═══════════════════════════════════════════════════════════════════════════════
def _graphe_terme_est_graphe(a, t, z="z"):
    """⊢ est_un_graphe(graphe_terme(A,T)).   (tout z∈F s'écrit (x,y), via membre_graphe_terme.)

    z∈F ⇔ (z∈A_couple…) : on prend la coordonnée z et membre_graphe_terme donne
    ((u,v)∈F)⇔… ; ici plus simple : (u,v)∈F ⇒ couple par construction.  On utilise
    l'axiome C54 sur la coordonnée z directement."""
    vA, vz = _t(a), var(z)
    F = E.graphe_terme(vA, t, "x")
    # axiome C54 sur w=z : (z∈F) ⇔ (∃x)(∃y)(z=(x,y) et x∈A et y=T)
    from bourbaki.ensembles.fonctions.ensembles_fonction_terme import _inst_axiome
    inst = _inst_axiome(vA, t, vz, "x", "y")                         # (z∈F)⇔(∃x∃y)(z=(x,y) et …)
    # corps ⇒ (∃x)(∃y)(z=(x,y)) = est_un_couple(z)
    from bourbaki.logique.tactiques.tactiques_abrege_quantif import existe_elimination
    vx2, vy2 = var("x"), var("y")
    body = et(et(egal(vz, E.couple(vx2, vy2)), appartient(vx2, vA)), egal(vy2, t))
    hb = N.assume(body)
    zc = conjonction_elim_gauche(conjonction_elim_gauche(hb))        # z=(x,y)
    ex_cpl = N.modus_ponens(zc, N.s5(egal(vz, E.couple(vx2, vy2)), vy2, "y"))   # (∃y)(z=(x,y))
    ex_cpl2 = N.modus_ponens(ex_cpl, N.s5(existe("y", egal(vz, E.couple(vx2, vy2))), vx2, "x"))  # (∃x)(∃y)
    inner = existe_elimination(existe_elimination(
        N.loi_deduction(body, ex_cpl2), "y"), "x")                   # (∃x∃y)body ⇒ est_un_couple(z)
    z_in_F = N.assume(appartient(vz, F))
    couple_z = N.modus_ponens(N.modus_ponens(z_in_F, equivalence_avant(inst)), inner)
    imp = N.loi_deduction(appartient(vz, F), couple_z)               # z∈F ⇒ est_un_couple(z)
    return N.generalisation("z", imp)                               # est_un_graphe(F)


def chi_est_graphe(y="Y", x="X"):
    """⊢ est_un_graphe(χ_Y).   (χ_Y = G∪H ; tout z∈G∪H est dans G ou H, donc un couple.)

    G = Y×{1} et H = (X∖Y)×{0} sont des graphes (_graphe_terme_est_graphe) ;
    membre_reunion_graphes : z∈G∪H ⇔ (z∈G ou z∈H), d'où z est un couple dans les
    deux cas."""
    from bourbaki.logique.tactiques.tactiques_abrege2 import cas
    vy, vx = _t(y), _t(x)
    vz = var("z")
    G, H = _chi_gauche(vy), _chi_droite(vy, vx)
    GuH = E.reunion(G, H)
    grG = _graphe_terme_est_graphe(vy, UN)                           # est_un_graphe(G)
    grH = _graphe_terme_est_graphe(E.difference(vx, vy), ZERO)       # est_un_graphe(H)
    car = membre_reunion_graphes(G, H, vz)                           # z∈G∪H ⇔ (z∈G ou z∈H)
    couple_z = E.est_un_couple(vz)
    # z∈G ⇒ couple ; z∈H ⇒ couple
    impG = instancie(grG, vz)                                        # z∈G ⇒ couple(z)
    impH = instancie(grH, vz)                                        # z∈H ⇒ couple(z)
    hz = N.assume(appartient(vz, GuH))
    disj = N.modus_ponens(hz, equivalence_avant(car))               # z∈G ou z∈H
    couple = cas(disj, impG, impH)                                  # couple(z)
    imp = N.loi_deduction(appartient(vz, GuH), couple)              # z∈G∪H ⇒ couple(z)
    return N.generalisation("z", imp)                              # est_un_graphe(G∪H)


# ═══════════════════════════════════════════════════════════════════════════════
# PALIER 1d — VALEURS de χ_Y  :  χ_Y(z)=1 sur Y ,  χ_Y(z)=0 hors Y
# ═══════════════════════════════════════════════════════════════════════════════
def chi_valeur_dans_Y(y="Y", x="X", z="z"):
    """{z ∈ Y} ⊢ (z, 1) ∈ χ_Y.   (χ_Y vaut 1 sur Y : (z,1) est dans la branche gauche.)

    (z,1)∈graphe_terme(Y,1) (graphe_terme_couple_dans, sous z∈Y), donc, comme
    χ_Y = G∪H ⊇ G, on a (z,1)∈G∪H (sens ⇐ de membre_reunion_graphes)."""
    vy, vx, vz = _t(y), _t(x), _t(z)
    zname = z if isinstance(z, str) else z.nom        # nom de variable pour graphe_terme_couple_dans
    G, H = _chi_gauche(vy), _chi_droite(vy, vx)
    cpl = E.couple(vz, UN)
    in_G = graphe_terme_couple_dans(vy, UN, zname, "x", "y")         # {z∈Y} ⊢ (z,1)∈G
    car = membre_reunion_graphes(G, H, cpl)                          # (z,1)∈G∪H ⇔ ((z,1)∈G ou (z,1)∈H)
    disj = N.modus_ponens(in_G, N.s2(appartient(cpl, G), appartient(cpl, H)))   # (z,1)∈G ou (z,1)∈H
    return N.modus_ponens(disj, equivalence_arriere(car))           # (z,1)∈χ_Y


def chi_valeur_hors_Y(y="Y", x="X", z="z"):
    """{z ∈ X∖Y} ⊢ (z, 0) ∈ χ_Y.   (χ_Y vaut 0 hors Y : (z,0) est dans la branche droite.)

    (z,0)∈graphe_terme(X∖Y,0) (graphe_terme_couple_dans, sous z∈X∖Y), donc, comme
    χ_Y = G∪H ⊇ H, on a (z,0)∈G∪H (sens ⇐ de membre_reunion_graphes)."""
    vy, vx, vz = _t(y), _t(x), _t(z)
    zname = z if isinstance(z, str) else z.nom        # nom de variable pour graphe_terme_couple_dans
    G, H = _chi_gauche(vy), _chi_droite(vy, vx)
    diff = E.difference(vx, vy)
    cpl = E.couple(vz, ZERO)
    in_H = graphe_terme_couple_dans(diff, ZERO, zname, "x", "y")     # {z∈X∖Y} ⊢ (z,0)∈H
    car = membre_reunion_graphes(G, H, cpl)                          # (z,0)∈G∪H ⇔ ((z,0)∈G ou (z,0)∈H)
    # (z,0)∈H ⇒ ((z,0)∈G ou (z,0)∈H)  (disjonction droite, S2+S3)
    disj = N.modus_ponens(
        N.modus_ponens(in_H, N.s2(appartient(cpl, H), appartient(cpl, G))),
        N.s3(appartient(cpl, H), appartient(cpl, G)))               # (z,0)∈G ou (z,0)∈H
    return N.modus_ponens(disj, equivalence_arriere(car))           # (z,0)∈χ_Y


# ═══════════════════════════════════════════════════════════════════════════════
# PALIER 1e — dom(χ_Y) = X   (les domaines recollés Y ∪ (X∖Y) = X, si Y ⊂ X)
# ═══════════════════════════════════════════════════════════════════════════════
def reunion_Y_diff_egale_X(y="Y", x="X"):
    """{Y ⊂ X} ⊢ (Y ∪ (X∖Y)) = X.   (réunion d'une partie et de son complémentaire.)

    Double inclusion + extensionnalité A1 :
      ⊂ : z∈Y∪(X∖Y) ⇒ (z∈Y ⇒ z∈X par Y⊂X ; z∈X∖Y ⇒ z∈X par AXIOME_DIFF) ;
      ⊃ : z∈X ⇒ (z∈Y ou ¬z∈Y ; si z∈Y alors z∈Y∪… ; si ¬z∈Y alors z∈X∖Y donc ∈…).
    """
    from bourbaki.ensembles.ensembles_theoremes import extensionnalite_appliquee
    from bourbaki.logique.tactiques.tactiques_abrege2 import cas, tiers_exclu
    vy, vx = _t(y), _t(x)
    vz = var("z")
    diff = E.difference(vx, vy)
    reun = E.reunion(vy, diff)
    hsub = N.assume(inclus(vy, vx))                                  # Y ⊂ X = (∀z)(z∈Y⇒z∈X)
    car_reun = membre_reunion_graphes(vy, diff, vz)                 # z∈Y∪(X∖Y) ⇔ (z∈Y ou z∈X∖Y)
    car_diff = _membre_diff(vz, vx, vy)                            # z∈X∖Y ⇔ (z∈X et ¬z∈Y)

    # ── ⊂ : z∈Y∪(X∖Y) ⇒ z∈X ──────────────────────────────────────────────────
    hz = N.assume(appartient(vz, reun))
    disj = N.modus_ponens(hz, equivalence_avant(car_reun))         # z∈Y ou z∈X∖Y
    # z∈Y ⇒ z∈X   (Y⊂X)
    brY = instancie(hsub, vz)                                       # z∈Y ⇒ z∈X
    # z∈X∖Y ⇒ z∈X
    hzd = N.assume(appartient(vz, diff))
    z_inX = conjonction_elim_gauche(N.modus_ponens(hzd, equivalence_avant(car_diff)))  # z∈X
    brDiff = N.loi_deduction(appartient(vz, diff), z_inX)          # z∈X∖Y ⇒ z∈X
    z_inX_final = cas(disj, brY, brDiff)                           # z∈X
    fwd = N.loi_deduction(appartient(vz, reun), z_inX_final)       # z∈reun ⇒ z∈X
    incl_LR = N.generalisation("z", fwd)                           # reun ⊂ X

    # ── ⊃ : z∈X ⇒ z∈Y∪(X∖Y) ──────────────────────────────────────────────────
    hzX = N.assume(appartient(vz, vx))                             # z∈X
    te = tiers_exclu(appartient(vz, vy))                           # (z∈Y) ou ¬(z∈Y)
    # z∈Y ⇒ z∈reun  (disjonction gauche)
    hzY = N.assume(appartient(vz, vy))
    inreun_Y = N.modus_ponens(
        N.modus_ponens(hzY, N.s2(appartient(vz, vy), appartient(vz, diff))),
        equivalence_arriere(car_reun))                            # z∈reun
    brTE_Y = N.loi_deduction(appartient(vz, vy), inreun_Y)        # z∈Y ⇒ z∈reun
    # ¬(z∈Y) ⇒ z∈reun  (z∈X et ¬z∈Y ⇒ z∈X∖Y ⇒ ∈reun)
    hnzY = N.assume(non(appartient(vz, vy)))
    z_inDiff = N.modus_ponens(conjonction_intro(hzX, hnzY), equivalence_arriere(car_diff))  # z∈X∖Y
    inreun_D = N.modus_ponens(
        N.modus_ponens(
            N.modus_ponens(z_inDiff, N.s2(appartient(vz, diff), appartient(vz, vy))),
            N.s3(appartient(vz, diff), appartient(vz, vy))),
        equivalence_arriere(car_reun))                            # z∈reun
    brTE_nY = N.loi_deduction(non(appartient(vz, vy)), inreun_D)  # ¬(z∈Y) ⇒ z∈reun
    z_inreun = cas(te, brTE_Y, brTE_nY)                           # z∈reun
    bwd = N.loi_deduction(appartient(vz, vx), z_inreun)           # z∈X ⇒ z∈reun
    incl_RL = N.generalisation("z", bwd)                          # X ⊂ reun

    ext = extensionnalite_appliquee(reun, vx)                     # (reun⊂X et X⊂reun) ⇒ reun=X
    eq = N.modus_ponens(conjonction_intro(incl_LR, incl_RL), ext)  # reun = X
    return N.loi_deduction(inclus(vy, vx), eq)                    # ⊢ Y⊂X ⇒ (Y∪(X∖Y))=X


def chi_domaine(y="Y", x="X"):
    """{Y ⊂ X} ⊢ dom(χ_Y) = X.   (χ_Y est total sur X : son domaine recolle Y et X∖Y.)

    dom(χ_Y) = dom(G∪H) = dom G ∪ dom H (dom_reunion_graphes) = Y ∪ (X∖Y)
    (graphe_terme_domaine) = X (reunion_Y_diff_egale_X, sous Y⊂X)."""
    vy, vx = _t(y), _t(x)
    G, H = _chi_gauche(vy), _chi_droite(vy, vx)
    diff = E.difference(vx, vy)
    # dom(G∪H) = dom G ∪ dom H
    dom_reun = dom_reunion_graphes(G, H)                            # dom(χ_Y) = dom G ∪ dom H
    # dom G = Y , dom H = X∖Y
    domG_eq_Y = graphe_terme_domaine(vy, UN, "x", "y", "z")        # dom G = Y
    domH_eq_Diff = graphe_terme_domaine(diff, ZERO, "x", "y", "z")  # dom H = X∖Y
    # dom G ∪ dom H = Y ∪ (X∖Y)  (congruence sur les deux arguments de ∪)
    #   dom G ∪ dom H = Y ∪ dom H  (congruence gauche), puis = Y ∪ (X∖Y) (congruence droite)
    step1 = N.modus_ponens(domG_eq_Y,
        congruence_terme(E.dom(G), vy, E.reunion(var("w"), E.dom(H)), "w"))  # domG∪domH = Y∪domH
    step2 = N.modus_ponens(domH_eq_Diff,
        congruence_terme(E.dom(H), diff, E.reunion(vy, var("w")), "w"))      # Y∪domH = Y∪(X∖Y)
    domGH_eq_reun = composer_egalites(step1, step2)                # domG∪domH = Y∪(X∖Y)
    # dom(χ_Y) = Y ∪ (X∖Y)
    dom_chi_eq_reun = composer_egalites(dom_reun, domGH_eq_reun)   # dom(χ_Y) = Y∪(X∖Y)
    # Y ∪ (X∖Y) = X  (sous Y⊂X)
    hsub = N.assume(inclus(vy, vx))
    reun_eq_X = N.modus_ponens(hsub, reunion_Y_diff_egale_X(vy, vx))   # Y∪(X∖Y) = X
    dom_chi_eq_X = composer_egalites(dom_chi_eq_reun, reun_eq_X)   # dom(χ_Y) = X  [sous Y⊂X]
    return N.loi_deduction(inclus(vy, vx), dom_chi_eq_X)          # ⊢ Y⊂X ⇒ dom(χ_Y)=X


# ═══════════════════════════════════════════════════════════════════════════════
# CRUX REPORTÉ : la bijection complète χ : 𝔓(X) → 𝓕(X; 2) et l'égalité finale
# ═══════════════════════════════════════════════════════════════════════════════
def bijection_chi_complete_REPORTE():
    """REPORTÉ (non clos) — la bijection χ : 𝔓(X) → 𝓕(X; 2) et Card(𝔓X)=2^Card X.

    Ce module CERTIFIE χ_Y (PALIER 1, tous clos) : GRAPHE FONCTIONNEL de domaine X
    (fonction X→{0,1}), valeurs χ_Y(z)=1 sur Y, χ_Y(z)=0 hors Y.  Restent REPORTÉS :
      (i)  χ_Y ∈ 𝓕(X;2) : emballer χ_Y dans le TRIPLE ((χ_Y,X),2) et vérifier χ_Y∈2^X
           via axiome_exposant (manque χ_Y⊂X×2, faisable mais hors budget) ;
      (ii) χ et ρ inverses : ρ(χ_Y)=Y (extensionnalité A1) et χ_{ρ(f)}=f
           (graphe_egal_par_valeurs).  VERROU : le ρ du round 24 lit la préimage DANS
           le triple f=((G,X),2), pas dans son graphe G ; aligner « graphe » (produit
           par χ) et « triple » (lu par ρ) est le cœur restant d'un round dédié ;
      (iii)bijection ⇒ Eq(𝔓X,𝓕(X;2)) ⇒ Card= via _prop1_direct_t (immédiat après i+ii).
    Le PALIER 1 (χ_Y fonction X→{0,1} bien définie), permis par le recollement
    (round 25), est le gain majeur de ce round."""
    raise NotImplementedError(
        "Bijection caractéristique complète χ : 𝔓(X) → 𝓕(X;2) reportée : emballage "
        "triple χ_Y∈𝓕(X;2) (i) + inverses χ↔ρ via alignement graphe/triple (ii). "
        "Ce module livre χ_Y comme FONCTION X→{0,1} bien définie (PALIER 1, certifié).")


__all__ = [
    "chi",
    "domaines_recolle_disjoints", "chi_domaines_disjoints",
    "chi_fonctionnel", "chi_est_graphe",
    "chi_valeur_dans_Y", "chi_valeur_hors_Y",
    "reunion_Y_diff_egale_X", "chi_domaine",
    "bijection_chi_complete_REPORTE",
]
