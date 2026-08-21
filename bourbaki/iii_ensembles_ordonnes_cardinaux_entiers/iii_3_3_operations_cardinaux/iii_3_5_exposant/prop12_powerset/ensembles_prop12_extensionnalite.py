# -*- coding: utf-8 -*-
"""§III.3.5 Prop.12, brique (iii) — χ∘ρ = id sur 𝓕(X;2) : χ_{Pre(f)} = f.

CHANTIER OUVERT (21 août 2026, file Cantor rectifiée, DECISIONS 21h30) :
c'est LE verrou de Card 𝔓X = 2^Card X, donc du Théorème 2 (Cantor, 2^a > a,
E III.30 L.20-21, scan lu). Rien n'est encore dérivé ici — ce module pose le
PLAN VÉRIFIÉ CONTRE LES PIÈCES EXISTANTES, et se remplit sous-lemme par
sous-lemme, chacun testé.

OUTIL-CLÉ (clos) : `graphe_egal_par_valeurs` (II.3.4, extensionnalité
fonctionnelle) — six conjoints à établir pour F := graphe(χ_{Pre₁(f)}) et
G := graphe sous-jacent de f (= pr₁(pr₁ f) si f est le triple (G, X, 2)) :

  (a) χ_{Pre(f)} FONCTIONNEL      — existe (rounds χ précédents) ;
  (b) G_f FONCTIONNEL             — depuis f ∈ 𝓕(X;2) (le triple est une
                                    application : son graphe est fonctionnel) ;
  (c) χ graphe / (d) G_f graphe   — idem, structurel ;
  (e) dom χ_{Pre(f)} = dom G_f    — les deux valent X (dom χ_Y = X connu ;
                                    dom G_f = X depuis le triple) ;
  (f) (∀z)(z ∈ X ⇒ χ_{Pre(f)}(z) = G_f(z)) — LE CŒUR : par cas z∈Pre(f) /
      z∉Pre(f) : χ vaut 1 resp. 0 (valeurs de χ, rounds précédents) ; f vaut
      1 ⇔ (z,1)∈G_f ⇔ z∈Pre(f) (définition de Pre, preimage_membre) et f ne
      prend que les valeurs 0/1 (f à valeurs dans 2 = {0,1} : dichotomie
      depuis l'image ⊂ 2 — sous-lemme deux_valeurs à écrire).

ORDRE D'ÉCRITURE (un sous-lemme = un commit testé) :
  1. `f_graphe_fonctionnel(f, x)`   — (b)+(d) depuis f ∈ 𝓕(X;2) ;
  2. `f_domaine(f, x)`              — (e) côté f ;
  3. FAIT SANS BRIQUE : deux_membre(z) (powerset_exp l.72) donne la
     dichotomie z∈2 ⇔ (z=∅ ou z={∅}) ; zero_dans_deux / un_dans_deux dispo.
  3bis. (ancien 3) `f_deux_valeurs`      — f(z) ∈ {0,1} (dichotomie image ⊂ 2) ;
  4. `valeurs_coincident(f, x, z)`  — (f), par cas via 3 + valeurs de χ ;
  5. `chi_rho_identite(f, x)`       — l'assemblage par graphe_egal_par_valeurs.

FORMES EXACTES vérifiées (21 août, 22h00) :
  · axiome_exposant (via N.axiome(E.theorie_exposant(X, deux()), …) puis
    instancie à G) : G ∈ 2^X ⇔ (G ⊂ X×2 et G fonctionnel et dom G = X) —
    l'équivalence-avant sous assume(G∈2^X) donne d'un coup les sous-lemmes
    1 (fonctionnel) et 2 (dom = X) ;
  · _conjonction_hypotheses de graphe_egal_par_valeurs exige AUSSI
    est_un_graphe(F) et est_un_graphe(G) : pour G, à dériver de G ⊂ X×2
    (un ensemble de couples est un graphe — lemme-pont « inclus dans un
    produit ⇒ graphe » : TROUVÉ — _inclus_produit_est_graphe(vG, vE, vF)
    (ii_5_2/ensembles_application_valeur l.163, {G⊂E×F} ⊢ est_un_graphe(G),
    prend des TERMES) ;
    pour F = χ_{Pre(f)} : chi_inclus_produit + le même pont ;
  · l'ordre de la conjonction (gauche-associée) : ((((fonct F et fonct G)
    et graphe F) et graphe G) et dom=dom) et ∀-valeurs.

RECETTE DU CŒUR (sous-lemme 4), formes vérifiées 22h15 :
  · egalite_valeurs = (∀x)(x∈dom F ⇒ E.valeur(F,x) = E.valeur(G,x)) — il faut
    donc le PONT VALEUR : (z,v)∈G et fonctionnel(G) ⇒ E.valeur(G,z)=v
    (à localiser : grep def.*valeur dans ii_3_1/ii_3_4/ii_5_2 —
    graphe_terme_valeur n'est que pour graphe_terme) ;
  · côté χ : chi_valeur_dans_Y {z∈Y} ⊢ (z,1)∈χ_Y ; chi_valeur_hors_Y
    {z∈X∖Y} ⊢ (z,0)∈χ_Y — niveau COUPLE, à remonter au niveau valeur
    par le même pont ;
  · preimage_un(f,x)/preimage_membre (powerset_deux l.102/126) : version
    GRAPHE (z∈Pre ⇔ z∈X et (z,1)∈f) — compatible témoin G ;
  · par cas sur G(z) via deux_membre + l'appartenance de la valeur à 2
    (dom G=X, z∈X ⇒ (z, G(z))∈G — pont valeur inverse — puis G⊂X×2 ⇒
    G(z)∈2) ; cas G(z)={∅} ⇒ (z,1)∈G ⇒ z∈Pre ⇒ (z,1)∈χ ⇒ valeurs 1=1 ;
    cas G(z)=∅ ⇒ z∉Pre (sinon (z,1)∈G et fonctionnel ⇒ ∅={∅}, absurde
    par singleton≠vide — lemme à localiser) ⇒ z∈X∖Y-forme ⇒ (z,0)∈χ.

PONTS DU CŒUR TOUS LOCALISÉS (22h20) :
  · valeur_caracterisation(f, x) (ii_3_4/ensembles_fonctions l.32, C46,
    E II.13 L.32-33) : {F fonctionnel, ∃y((x,y)∈F)} ⊢ ((x,y)∈F) ⇔ (y=f(x)) —
    accepte les TERMES ; valeur_dans_graphe pour (x, f(x))∈F ;
  · singleton_vide_different_du_vide (ii_5_definitions/
    ensembles_produit_famille_graphe l.173) pour l'absurde du cas 0.

DERNIÈRES FORMES (22h25) : couple_dans_dom {(x,y)∈F} ⊢ x∈dom F et
_inst_dom(vf,vx) : (x∈dom F)⇔(∃y)((x,y)∈F) (extensionnalite.py, privé
importable) — l'étape (0) passe par dom G=X réécrit puis equivalence_avant ;
l'étape (2) est DIRECTE : couple_dans_produit_ssi (ii_2_2/
ensembles_produit l.78) ⊢ ((u,v)∈A×B) ⇔ (u∈A et v∈B), termes-ok —
G⊂X×2 instancié à (z, G(z)) puis equivalence_avant + elim_droite ; le plan par cas passe par z∈Pre ∨ ¬(z∈Pre)
(tiers exclu) MAIS l'étape (2) G(z)∈2 reste nécessaire au cas négatif
(G(z)≠1 et G(z)∈2 ⇒ G(z)=0).

Pièces existantes vérifiées ce jour : chi_dans_applications (χ_Y ∈ 𝓕(X;2)),
rho_chi_identite (Pre(χ_Y) = Y), preimage_membre, chi_inclus_produit,
graphe_egal_par_valeurs (clos, 6 conjoints).
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, inclus, appartient)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_elim_gauche, conjonction_elim_droite, instancie, equivalence_avant)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.ii_theorie_des_ensembles.ii_5_produit_famille.ii_5_2_ensemble_applications.ensembles_application_valeur import (
    _inclus_produit_est_graphe)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_5_exposant.prop12_powerset.ensembles_powerset_deux import (
    deux)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def _cut(thm, P, pr):
    """Décharge l'hypothèse P de `thm` en la remplaçant par sa preuve `pr`."""
    return N.modus_ponens(pr, N.loi_deduction(P, thm))


# Sous-lemmes 1+2 (+graphe) — (b), (d), (e) du plan, d'un coup.
def g_decompose(g="Gext", x="Xext"):
    """{G ∈ 2^X} ⊢ le quadruplet (G ⊂ X×2, G fonctionnel, dom G = X,
    est_un_graphe(G)) — tuple de quatre théorèmes, chacun sous la seule
    hypothèse d'appartenance à l'exposant.

    axiome_exposant (E.II.5.2, via theorie_exposant) : G ∈ 2^X ⇔
    (G ⊂ X×2 et G fonctionnel et dom G = X) ; le quatrième membre vient du
    pont `_inclus_produit_est_graphe` (un ensemble de couples est un graphe),
    son hypothèse d'inclusion étant coupée par la première conclusion."""
    vg, vx = _t(g), _t(x)
    deux_ens = deux()
    ax = N.axiome(E.theorie_exposant(vx, deux_ens),
                  E.axiome_exposant(vx, deux_ens))       # (∀G)(G∈2^X ⇔ …)
    car = instancie(ax, vg)                              # G∈2^X ⇔ (⊂ et fonct et dom)
    h = N.assume(appartient(vg, E.exposant(vx, deux_ens)))
    corps = N.modus_ponens(h, equivalence_avant(car))    # (G⊂X×2 et fonct) et dom=X
    dom_eq = conjonction_elim_droite(corps)              # dom G = X
    gauche = conjonction_elim_gauche(corps)
    incl = conjonction_elim_gauche(gauche)               # G ⊂ X×2
    fonct = conjonction_elim_droite(gauche)              # est_fonctionnel(G)
    graphe = _cut(_inclus_produit_est_graphe(vg, vx, deux_ens),
                  inclus(vg, E.produit(vx, deux_ens)), incl)   # est_un_graphe(G)
    return incl, fonct, dom_eq, graphe


def _gen_inst(thm, nom, terme):
    """∀-clôture sur `nom` puis instance au TERME (jamais var() sur un Terme)."""
    return instancie(N.generalisation(nom, thm), terme)


# Sous-lemme 4 — LE CŒUR : les valeurs de χ_{Pre(G)} et de G coïncident sur X.
def valeurs_coincident(g="Gext", x="Xext", z="zext"):
    """{G ∈ 2^X, z ∈ X} ⊢ valeur(χ_{Pre(G)}, z) = valeur(G, z).

    Par cas sur z ∈ Pre(G) (tiers exclu) ; toutes les pièces sont des lemmes
    clos du dépôt (recette et formes : docstring de module). ZERO = ∅ et
    UN = {∅} LITTÉRALEMENT (somme_disjointe l.51-52) — la dichotomie de
    deux_membre recolle sans pont."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
        egal, et, existe, non)
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
        conjonction_intro, equivalence_arriere, tiers_exclu, cas, contraposition)
    from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
        symetrie, composer_egalites)
    from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_4_fonctions.ensembles_fonctions import (
        valeur_dans_graphe, valeur_caracterisation)
    from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_4_fonctions.ensembles_extensionnalite import (
        _inst_dom)
    from bourbaki.ii_theorie_des_ensembles.ii_2_couples.ii_2_2_produit_deux_ensembles.ensembles_produit import (
        couple_dans_produit_ssi)
    from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_recollement_somme.ensembles_somme_disjointe import (
        ZERO, UN)
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_5_exposant.prop12_powerset.ensembles_powerset_deux import (
        preimage_un, preimage_membre)
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_5_exposant.prop12_powerset.ensembles_powerset_exp import (
        deux_membre)
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_5_exposant.prop12_powerset.ensembles_prop12_powerset import (
        chi, chi_fonctionnel, chi_valeur_dans_Y, chi_valeur_hors_Y)

    vg, vx, vz = _t(g), _t(x), _t(z)
    deux_ens = deux()
    Pre = preimage_un(vg, vx)
    Chi = chi(Pre, vx)
    Gz = E.valeur(vg, vz)
    Cz = E.valeur(Chi, vz)

    incl, fonct, dom_eq, _ = g_decompose(g, x)
    h_zX = N.assume(appartient(vz, vx))                       # z ∈ X

    #   (0) z ∈ dom G puis ∃y((z,y)∈G)
    x_eq_dom = N.modus_ponens(dom_eq, symetrie(E.dom(vg), vx))  # X = dom G
    z_domG = N.modus_ponens(h_zX, equivalence_avant(N.modus_ponens(
        x_eq_dom, N.s6(vx, E.dom(vg), "w", appartient(vz, var("w"))))))
    ex_y = N.modus_ponens(z_domG, equivalence_avant(_inst_dom(vg, vz)))

    #   (1) (z, G(z)) ∈ G
    zGz_in = N.modus_ponens(ex_y, N.loi_deduction(
        existe("y", appartient(E.couple(vz, var("y")), vg)),
        valeur_dans_graphe(vg, vz)))

    #   (2) G(z) ∈ 2
    zGz_prod = N.modus_ponens(zGz_in, instancie(incl, E.couple(vz, Gz)))
    Gz_in_2 = conjonction_elim_droite(N.modus_ponens(
        zGz_prod, equivalence_avant(couple_dans_produit_ssi(vz, Gz, vx, deux_ens))))

    #   caractérisations (∀-clôturées sur y puis instanciées au bon terme)
    carG = valeur_caracterisation(vg, vz)                     # ((z,y)∈G)⇔... y libre
    #   couper ses hypothèses (fonctionnel G ; ∃y — z LIBRE dedans, le noyau
    #   refuserait la généralisation finale de l'assemblage sinon — mesuré)
    carG = _cut(carG, E.est_fonctionnel(vg), fonct)
    carG = _cut(carG, existe("y", appartient(E.couple(vz, var("y")), vg)), ex_y)
    carG_fwd_UN = _gen_inst(conjonction_elim_gauche(carG), "y", UN)   # ((z,UN)∈G)⇒(UN=G(z))
    carG_bwd_UN = _gen_inst(conjonction_elim_droite(carG), "y", UN)   # (UN=G(z))⇒((z,UN)∈G)

    car_pre = preimage_membre(vg, vx, vz)                     # z∈Pre ⇔ (z∈X et (z,UN)∈G)

    #   CAS 1 : z ∈ Pre
    h_in = N.assume(appartient(vz, Pre))
    zUN_G = conjonction_elim_droite(N.modus_ponens(h_in, equivalence_avant(car_pre)))
    UN_eq_Gz = N.modus_ponens(zUN_G, carG_fwd_UN)             # UN = G(z)
    zUN_chi = N.modus_ponens(h_in, N.loi_deduction(
        appartient(vz, Pre), chi_valeur_dans_Y(Pre, vx, vz)))  # (z,UN)∈χ
    ex_chi = N.modus_ponens(zUN_chi, N.s5(
        appartient(E.couple(vz, var("y")), Chi), UN, "y"))     # ∃y((z,y)∈χ)
    carC = valeur_caracterisation(Chi, vz)
    carC = _cut(carC, E.est_fonctionnel(Chi), chi_fonctionnel(Pre, vx))
    carC = _cut(carC, existe("y", appartient(E.couple(vz, var("y")), Chi)), ex_chi)
    carC_fwd_UN = _gen_inst(conjonction_elim_gauche(carC), "y", UN)
    UN_eq_Cz = N.modus_ponens(zUN_chi, carC_fwd_UN)           # UN = χ(z)
    egal_cas1 = composer_egalites(
        N.modus_ponens(UN_eq_Cz, symetrie(UN, Cz)),           # χ(z) = UN
        UN_eq_Gz)                                             # χ(z) = G(z)
    br1 = N.loi_deduction(appartient(vz, Pre), egal_cas1)

    #   CAS 2 : ¬(z ∈ Pre)
    h_out = N.assume(non(appartient(vz, Pre)))
    #   G(z) ≠ UN : sinon (z,UN)∈G puis z∈Pre, contre h_out
    to_pre = N.loi_deduction(egal(UN, Gz), N.modus_ponens(
        conjonction_intro(h_zX, N.modus_ponens(N.assume(egal(UN, Gz)), carG_bwd_UN)),
        equivalence_arriere(car_pre)))                        # (UN=G(z)) ⇒ z∈Pre
    Gz_ne_UN = N.modus_ponens(h_out, contraposition(to_pre))  # ¬(UN = G(z))
    #   dichotomie → G(z) = ∅ (=ZERO) ; deux_membre : G(z)=∅ ou G(z)={∅}=UN
    dm = N.modus_ponens(Gz_in_2, equivalence_avant(deux_membre(Gz)))
    #   (G(z)=∅ ou G(z)=UN) et ¬(UN=G(z)) → G(z)=∅ : cas() avec branche droite absurde
    br_gauche = N.loi_deduction(egal(Gz, ZERO), N.assume(egal(Gz, ZERO)))
    #   branche droite : G(z)={∅}=UN → UN=G(z) → contradiction → ex falso G(z)=∅
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux_consequences import (
        _ex_falso)
    h_un = N.assume(egal(Gz, E.singleton(E.VIDE)))            # G(z)={∅} = UN
    un_eq_gz = N.modus_ponens(h_un, symetrie(Gz, E.singleton(E.VIDE)))  # UN=G(z)
    br_droite = N.loi_deduction(egal(Gz, E.singleton(E.VIDE)),
                                _ex_falso(un_eq_gz, Gz_ne_UN, egal(Gz, ZERO)))
    Gz_eq_0 = cas(dm, br_gauche, br_droite)                   # G(z) = ∅
    #   z ∈ X∖Pre puis (z,ZERO)∈χ puis χ(z)=ZERO
    car_diff = instancie(instancie(instancie(
        N.axiome(E.theorie_ensembles(), E.AXIOME_DIFF), vx), Pre), vz)
    z_diff = N.modus_ponens(conjonction_intro(h_zX, h_out),
                            equivalence_arriere(car_diff))
    z0_chi = N.modus_ponens(z_diff, N.loi_deduction(
        appartient(vz, E.difference(vx, Pre)), chi_valeur_hors_Y(Pre, vx, vz)))
    ex_chi0 = N.modus_ponens(z0_chi, N.s5(
        appartient(E.couple(vz, var("y")), Chi), ZERO, "y"))
    carC0 = valeur_caracterisation(Chi, vz)
    carC0 = _cut(carC0, E.est_fonctionnel(Chi), chi_fonctionnel(Pre, vx))
    carC0 = _cut(carC0, existe("y", appartient(E.couple(vz, var("y")), Chi)), ex_chi0)
    Z_eq_Cz = N.modus_ponens(z0_chi, _gen_inst(conjonction_elim_gauche(carC0), "y", ZERO))
    egal_cas2 = composer_egalites(
        N.modus_ponens(Z_eq_Cz, symetrie(ZERO, Cz)),          # χ(z) = ZERO
        N.modus_ponens(Gz_eq_0, symetrie(Gz, ZERO)))          # χ(z) = G(z)
    br2 = N.loi_deduction(non(appartient(vz, Pre)), egal_cas2)

    #   (4) fusion par tiers exclu
    return cas(tiers_exclu(appartient(vz, Pre)), br1, br2)


# Sous-lemme 5 — L'ASSEMBLAGE : χ∘ρ = id sur 2^X.
def chi_rho_identite(g="Gext", x="Xext"):
    """🎯 {G ∈ 2^X} ⊢ χ_{Pre(G)} = G.   (La brique (iii) de la file Cantor.)

    Extensionnalité fonctionnelle (graphe_egal_par_valeurs, 6 conjoints dans
    l'ordre EXACT de _conjonction_hypotheses) avec F := χ_{Pre(G)} et G."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
        egal, impl)
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
        conjonction_intro)
    from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
        symetrie, composer_egalites)
    from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_4_fonctions.ensembles_extensionnalite import (
        graphe_egal_par_valeurs, _conjonction_hypotheses)
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_5_exposant.prop12_powerset.ensembles_powerset_deux import (
        preimage_un, preimage_inclus)
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_5_exposant.prop12_powerset.ensembles_prop12_powerset import (
        chi, chi_fonctionnel, chi_domaine)
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_5_exposant.prop12_powerset.ensembles_prop12_fin import (
        chi_inclus_produit)

    vg, vx = _t(g), _t(x)
    deux_ens = deux()
    Pre = preimage_un(vg, vx)
    Chi = chi(Pre, vx)
    #   variable de travail "z" (le nom "x" collisionne avec les lieurs
    #   internes des lemmes de couples — 3e échec mesuré) ; l'α-passage vers
    #   le lieur "x" d'egalite_valeurs se fait à la fin par inst+gen
    vz = var("z")

    incl_G, fonct_G, dom_G, graphe_G = g_decompose(g, x)
    pre_sub = preimage_inclus(vg, vx)                          # ⊢ Pre ⊂ X (clos)

    #   côté χ : fonctionnel (clos), inclusion ⊂ X×2 sous Pre⊂X, graphe, dom=X
    fonct_C = chi_fonctionnel(Pre, vx)
    incl_C = N.modus_ponens(pre_sub, chi_inclus_produit(Pre, vx))
    graphe_C = _cut(_inclus_produit_est_graphe(Chi, vx, deux_ens),
                    __import__("bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule", fromlist=["inclus"]).inclus(Chi, E.produit(vx, deux_ens)),
                    incl_C)
    dom_C = N.modus_ponens(pre_sub, chi_domaine(Pre, vx))      # dom χ = X
    dom_eq = composer_egalites(dom_C, N.modus_ponens(dom_G, symetrie(E.dom(vg), vx)))
    #   dom χ = dom G

    #   ∀-valeurs : (∀z)(z ∈ dom χ ⇒ χ(z) = G(z))
    h_zdom = N.assume(appartient(vz, E.dom(Chi)))
    x_from_dom = N.modus_ponens(h_zdom, equivalence_avant(N.modus_ponens(
        dom_C, N.s6(E.dom(Chi), vx, "w", appartient(vz, var("w"))))))   # z ∈ X
    vals = valeurs_coincident(g, x, vz)                        # {G∈2^X, z∈X} ⊢ χ(z)=G(z)
    vals = _cut(vals, appartient(vz, vx), x_from_dom)          # hyp z∈X → z∈dom χ
    val_imp = N.loi_deduction(appartient(vz, E.dom(Chi)), vals)
    #   α-passage z → x : ∀z puis instance à var("x") puis ∀x (légal : ni z
    #   ni x libres dans les hypothèses restantes)
    val_all = N.generalisation("x", instancie(
        N.generalisation("z", val_imp), var("x")))

    #   la grande conjonction, ordre EXACT
    corps = conjonction_intro(conjonction_intro(conjonction_intro(
        conjonction_intro(conjonction_intro(
            fonct_C, fonct_G), graphe_C), graphe_G), dom_eq), val_all)
    assert corps.conclusion == _conjonction_hypotheses(Chi, vg), \
        "chi_rho_identite : conjonction mal ordonnée"
    res = N.modus_ponens(corps, graphe_egal_par_valeurs(Chi, vg))
    assert res.conclusion == egal(Chi, vg), "chi_rho_identite : conclusion inattendue"
    return res


__all__ = ["g_decompose", "valeurs_coincident", "chi_rho_identite"]
