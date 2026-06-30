"""§II.5 — COROLLAIRE de la Proposition 8 (E II.36, n°6 « Formules de distributivité »).

ÉNONCÉ VERBATIM (Bourbaki, E II.36, Corollaire de la Prop. 8) :
    « Soient (X_ι)_{ι∈I} et (Y_κ)_{κ∈K} deux familles d'ensembles dont les
      ensembles d'indices sont non vides.  On a
          ( ⋂_{ι∈I} X_ι ) ∪ ( ⋂_{κ∈K} Y_κ )  =  ⋂_{(ι,κ)∈I×K} ( X_ι ∪ Y_κ )   (1)
      et   ( ⋃_{ι∈I} X_ι ) ∩ ( ⋃_{κ∈K} Y_κ )  =  ⋃_{(ι,κ)∈I×K} ( X_ι ∩ Y_κ ). »  (2)

CIBLE DE CE MODULE — la SECONDE formule (2), ÉGALITÉ PLEINE (les deux sens) :

    ⊢  ( ⋃_{ι∈I} X_ι ) ∩ ( ⋃_{κ∈K} Y_κ )  =  ⋃_{(ι,κ)∈I×K} ( X_ι ∩ Y_κ ).

POURQUOI C'EST CHOICE-FREE (et même plus simple que la formule (1), qui consomme un
tiers exclu au sens ⊃) : ICI, AUCUN choix NI tiers exclu n'est requis.  Les deux sens
sont purement ponctuels : chaque réunion ⋃ donne un TÉMOIN par ∃-élimination, chaque
intersection ∩ binaire se décompose/recompose par conjonction.

  • ⊃  (droite ⊂ gauche) ponctuel : soit x ∈ ⋃_{(ι,κ)}(X_ι∩Y_κ).  ∃-élim sur la réunion
    de Z : témoin u∈I×K avec x∈Z(u).  Décomposition u=(ι₀,κ₀) (témoins AXIOME_PRODUIT) ;
    réécriture Z(u)=Z((ι₀,κ₀))=X_{ι₀}∩Y_{κ₀}.  Donc x∈X_{ι₀} et x∈Y_{κ₀}.  Comme ι₀∈I,
    (ι₀∈I et x∈X_{ι₀}) injecte x dans ⋃X ; comme κ₀∈K, (κ₀∈K et x∈Y_{κ₀}) injecte x
    dans ⋃Y.  D'où x ∈ (⋃X)∩(⋃Y).
  • ⊂  (gauche ⊂ droite) ponctuel : soit x ∈ (⋃X)∩(⋃Y).  ∃-élim sur x∈⋃X : témoin ι₀∈I,
    x∈X_{ι₀}.  ∃-élim sur x∈⋃Y : témoin κ₀∈K, x∈Y_{κ₀}.  (ι₀,κ₀)∈I×K (couple_dans_produit) ;
    (x∈X_{ι₀} et x∈Y_{κ₀}) recompose x∈X_{ι₀}∩Y_{κ₀}=Z((ι₀,κ₀)) ; ((ι₀,κ₀)∈I×K et x∈Z(…))
    injecte x dans ⋃_{(ι,κ)} Z.

PARAMÉTRAGE FIDÈLE (mécanisme C54 « famille définie par un terme »).  IDENTIQUE au module
de la formule (1) `ensembles_cor_prop8_deux_familles_ii5`, au DUAL ∪→∩ près sur Z :
la famille DROITE Z = ((ι,κ) ↦ X_ι∩Y_κ)_{(ι,κ)∈I×K} n'est pas un terme calculable ; on la
NOMME par un paramètre `Z` et on la CARACTÉRISE par son terme SUR LES COUPLES EXPLICITES,
via un axiome-schéma (C54) porté par une THÉORIE LOCALE dédiée `theorie_cor_distrib_2(...)` :

    AX_Z : (∀ι)(∀κ)  valeur_famille(Z, (ι,κ))  =  X_ι ∩ Y_κ.

Cette théorie locale n'entre PAS dans `theorie_ensembles()`, qui reste à 22 axiomes :
l'axiome-schéma est une DÉFINITION (légitimée S8+A1), pas une hypothèse ;
`N.axiome(theorie_cor_distrib_2, AX_Z)` produit `∅ ⊢ AX_Z` (théorème CLOS).

Notations (XX, YY, I, K, Z paramètres libres) :
  • X_ι = valeur_famille(XX, ι),  Y_κ = valeur_famille(YY, κ) ;
  • gauche = ( ⋃_{ι∈I} X_ι ) ∩ ( ⋃_{κ∈K} Y_κ ) = inter(reunion_famille(XX,I), reunion_famille(YY,K)) ;
  • I×K = produit(I, K) ;
  • droite = ⋃_{(ι,κ)∈I×K} Z((ι,κ)) = reunion_famille(Z, produit(I, K)).

STATUT : CLOS (0 hypothèse pendante).  theorie_ensembles() = 22 axiomes (inchangée).
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (Terme, var, et, ou, non, impl,
                                       appartient, egal, pourtout, existe)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    instancie, equivalence_avant, equivalence_arriere, conjonction_intro,
    conjonction_elim_gauche, conjonction_elim_droite)
from bourbaki.logique.i_3_quantifies.tactiques_abrege_quantif import existe_elimination, alpha_existe
from bourbaki.logique.i_4_egalitaires.tactiques_abrege_egalite import symetrie
from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_theoremes import extensionnalite_appliquee
from bourbaki.ensembles.familles.ii_2_produit_deux_ensembles.ensembles_produit import couple_dans_produit_ssi
# helpers génériques RÉUTILISÉS du module de la formule (1) (mêmes constructeurs, dual ∪→∩)
from bourbaki.ensembles.familles.ii_5_produit_famille.ii_5_6_7_algebre_produit.ensembles_cor_prop8_deux_familles_ii5 import (
    _membre_produit, _sym, _congruence_terme, _reecrit)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# ── notations dérivées ────────────────────────────────────────────────────────
def _X(xx, iota):
    """X_ι = valeur_famille(XX, ι)."""
    return E.valeur_famille(_t(xx), _t(iota))


def _Y(yy, kappa):
    """Y_κ = valeur_famille(YY, κ)."""
    return E.valeur_famille(_t(yy), _t(kappa))


def _membre_gauche(xx="XX", yy="YY", i="I", k="K"):
    """( ⋃_{ι∈I} X_ι ) ∩ ( ⋃_{κ∈K} Y_κ ) = inter(reunion_famille(XX,I), reunion_famille(YY,K))."""
    return E.intersection(E.reunion_famille(_t(xx), _t(i)), E.reunion_famille(_t(yy), _t(k)))


def _membre_droit(z="Z", i="I", k="K"):
    """⋃_{(ι,κ)∈I×K} ( X_ι∩Y_κ ) = reunion_famille(Z, I×K),  Z((ι,κ)) = X_ι∩Y_κ."""
    return E.reunion_famille(_t(z), E.produit(_t(i), _t(k)))


# ── axiome-schéma (C54) de définition de la famille Z sur I×K ──────────────────
def _ax_z(xx, yy, z, iota="i", kappa="k"):
    """AX_Z : (∀ι)(∀κ)  valeur_famille(Z, (ι,κ)) = X_ι ∩ Y_κ.

    « Z est la famille (ι,κ) ↦ X_ι∩Y_κ. »  (déf. par un terme SUR COUPLES, C54.)"""
    vi, vk = var(iota), var(kappa)
    return pourtout(iota, pourtout(kappa,
        egal(E.valeur_famille(_t(z), E.couple(vi, vk)), E.intersection(_X(xx, vi), _Y(yy, vk)))))


def theorie_cor_distrib_2(xx="XX", yy="YY", z="Z"):
    """Théorie LOCALE portant l'axiome-schéma C54 de définition de la famille Z.

    N'entre PAS dans theorie_ensembles() (qui reste à 22) : AX_Z est une DÉFINITION
    (S8+A1), pas une hypothèse ; `N.axiome(theorie_cor_distrib_2, AX_Z)` donne `∅ ⊢ AX_Z`."""
    return N.Theorie("Cor-Distributivite-2fam-reunion", [_ax_z(_t(xx), _t(yy), _t(z))])


# ── cible ─────────────────────────────────────────────────────────────────────
def _cible(xx="XX", yy="YY", z="Z", i="I", k="K"):
    """⊢-cible : ( ⋃_{ι∈I}X_ι ) ∩ ( ⋃_{κ∈K}Y_κ ) = ⋃_{(ι,κ)∈I×K}( X_ι∩Y_κ )."""
    return egal(_membre_gauche(xx, yy, i, k), _membre_droit(z, i, k))


# ── théorème principal ────────────────────────────────────────────────────────
# @livre Ch.II §5.6 Cor.- | E II.36 L.19-19 | PDF p.87
def cor_distributivite_reunion_inter_deux_familles(xx="XX", yy="YY", z="Z", i="I", k="K"):
    """⊢ ( ⋃_{ι∈I}X_ι ) ∩ ( ⋃_{κ∈K}Y_κ ) = ⋃_{(ι,κ)∈I×K}( X_ι∩Y_κ ).

    COROLLAIRE de la PROPOSITION 8, seconde formule (2), E II.36.  ÉGALITÉ PLEINE,
    SANS choix NI tiers exclu (cas L={1,2}) : les deux sens sont ponctuels directs
    (∃-éliminations + conjonctions).  Clos (0 hyp).  Z : famille externe sur I×K
    définie par `theorie_cor_distrib_2` (axiome C54 sur les couples explicites)."""
    vXX, vYY, vZ, vI, vK = _t(xx), _t(yy), _t(z), _t(i), _t(k)
    th = theorie_cor_distrib_2(vXX, vYY, vZ)
    ax_z = N.axiome(th, _ax_z(vXX, vYY, vZ))            # (∀ι)(∀κ) Z((ι,κ)) = X_ι∩Y_κ

    gauche = _membre_gauche(vXX, vYY, vI, vK)
    droite = _membre_droit(vZ, vI, vK)

    incl_gd = _inclusion_directe(vXX, vYY, vZ, vI, vK, ax_z)     # gauche ⊂ droite
    incl_dg = _inclusion_reciproque(vXX, vYY, vZ, vI, vK, ax_z)  # droite ⊂ gauche

    ext = extensionnalite_appliquee(gauche, droite)
    eq = N.modus_ponens(conjonction_intro(incl_gd, incl_dg), ext)   # gauche = droite
    assert eq.conclusion == _cible(xx, yy, z, i, k), \
        "cor_distributivite_reunion_inter_deux_familles : conclusion ≠ cible"
    return eq


# ── sens ⊂ :  (⋃X)∩(⋃Y)  ⊂  ⋃_{(ι,κ)∈I×K}(X_ι∩Y_κ)  (ponctuel, sans choix) ─────
def _inclusion_directe(vXX, vYY, vZ, vI, vK, ax_z):
    """gauche ⊂ droite.  x∈(⋃X)∩(⋃Y) → ∃-élim sur ⋃X (témoin ι₀∈I, x∈X_{ι₀}) et sur ⋃Y
    (témoin κ₀∈K, x∈Y_{κ₀}) ; (ι₀,κ₀)∈I×K et x∈X_{ι₀}∩Y_{κ₀}=Z((ι₀,κ₀)) → x∈⋃Z."""
    vx = var("z")
    vi, vk = var("i"), var("k")                                # témoins (eigenvariables ∃)
    gauche = _membre_gauche(vXX, vYY, vI, vK)
    reun_X = E.reunion_famille(vXX, vI)
    reun_Y = E.reunion_famille(vYY, vK)
    hx = N.assume(appartient(vx, gauche))                      # x ∈ (⋃X)∩(⋃Y)
    conj = N.modus_ponens(hx, equivalence_avant(_membre_inter_bin(reun_X, reun_Y, vx)))  # x∈⋃X et x∈⋃Y
    x_in_uX = conjonction_elim_gauche(conj)                    # x ∈ ⋃X
    x_in_uY = conjonction_elim_droite(conj)                    # x ∈ ⋃Y
    ex_i = N.modus_ponens(x_in_uX, equivalence_avant(_membre_reunion_fam(vXX, vI, vx)))  # (∃i)(i∈I et x∈X_i)
    ex_k0 = N.modus_ponens(x_in_uY, equivalence_avant(_membre_reunion_fam(vYY, vK, vx)))  # (∃i)(i∈K et x∈Y_i)

    # corps sous témoins ι₀ (puis κ₀) : (ι₀∈I et x∈X_{ι₀}) , (κ₀∈K et x∈Y_{κ₀}) ⊢ x∈⋃Z
    body_i = et(appartient(vi, vI), appartient(vx, _X(vXX, vi)))
    body_k = et(appartient(vk, vK), appartient(vx, _Y(vYY, vk)))
    # le binder du ∃ de REUNION_FAM est « i » dans les DEUX cas ; α-renomme celui de ⋃Y
    # en « k » pour disposer de DEUX témoins distincts (ι₀ et κ₀) simultanément.
    body_k_i = et(appartient(vi, vK), appartient(vx, _Y(vYY, vi)))                 # (i∈K et x∈Y_i)
    ex_k = N.modus_ponens(ex_k0, equivalence_avant(alpha_existe("i", "k", body_k_i)))  # (∃k)(k∈K et x∈Y_k)
    hbi = N.assume(body_i)
    hbk = N.assume(body_k)
    i_in = conjonction_elim_gauche(hbi)                        # ι₀ ∈ I
    x_Xi = conjonction_elim_droite(hbi)                        # x ∈ X_{ι₀}
    k_in = conjonction_elim_gauche(hbk)                        # κ₀ ∈ K
    x_Yk = conjonction_elim_droite(hbk)                        # x ∈ Y_{κ₀}
    Xi, Yk = _X(vXX, vi), _Y(vYY, vk)
    inter_t = E.intersection(Xi, Yk)                                  # X_{ι₀}∩Y_{κ₀}

    # (ι₀,κ₀) ∈ I×K
    ck_in = N.modus_ponens(conjonction_intro(i_in, k_in),
                           equivalence_arriere(couple_dans_produit_ssi(vi, vk, vI, vK)))
    # x ∈ X_{ι₀}∩Y_{κ₀}  (recomposition de l'intersection binaire)
    x_in_inter = N.modus_ponens(conjonction_intro(x_Xi, x_Yk),
                                equivalence_arriere(_membre_inter_bin(Xi, Yk, vx)))
    # X_{ι₀}∩Y_{κ₀} = Z((ι₀,κ₀))  (AX_Z, symétrisé), réécriture x∈inter → x∈Z((ι₀,κ₀))
    eq_z = _sym(instancie(instancie(ax_z, vi), vk))            # X_{ι₀}∩Y_{κ₀} = Z((ι₀,κ₀))
    x_in_Zc = _reecrit(x_in_inter, eq_z, vx, inter_t,
                       E.valeur_famille(vZ, E.couple(vi, vk)))  # x ∈ Z((ι₀,κ₀))
    # ((ι₀,κ₀)∈I×K et x∈Z((ι₀,κ₀))) → x ∈ ⋃_{u∈I×K} Z(u)  (témoin u=(ι₀,κ₀), binder « i »)
    inj_body = et(appartient(var("i"), E.produit(vI, vK)),
                  appartient(vx, E.valeur_famille(vZ, var("i"))))
    ex_u = N.modus_ponens(conjonction_intro(ck_in, x_in_Zc),
                          N.s5(inj_body, E.couple(vi, vk), "i"))  # (∃u)(u∈I×K et x∈Z(u))
    x_in_droite = N.modus_ponens(ex_u, equivalence_arriere(
        _membre_reunion_fam(vZ, E.produit(vI, vK), vx)))       # x ∈ ⋃_{u∈I×K} Z(u)

    # décharger les témoins κ₀ puis ι₀ (eigenvariables k, i)
    imp_k = existe_elimination(N.loi_deduction(body_k, x_in_droite), "k")   # (∃κ)body_k ⇒ x∈⋃Z
    x_via_k = N.modus_ponens(ex_k, imp_k)
    imp_i = existe_elimination(N.loi_deduction(body_i, x_via_k), "i")       # (∃ι)body_i ⇒ x∈⋃Z
    x_droite = N.modus_ponens(ex_i, imp_i)                     # x ∈ ⋃Z  {hx}
    imp_x = N.loi_deduction(appartient(vx, gauche), x_droite)
    return N.generalisation("z", imp_x)                       # gauche ⊂ droite


# ── sens ⊃ :  ⋃_{(ι,κ)∈I×K}(X_ι∩Y_κ)  ⊂  (⋃X)∩(⋃Y)  (ponctuel, sans choix) ─────
def _inclusion_reciproque(vXX, vYY, vZ, vI, vK, ax_z):
    """droite ⊂ gauche.  x∈⋃Z → ∃-élim (témoin u∈I×K, x∈Z(u)) ; u=(ι₀,κ₀) (témoins
    AXIOME_PRODUIT) ; Z(u)=X_{ι₀}∩Y_{κ₀} → x∈X_{ι₀} (donc x∈⋃X) et x∈Y_{κ₀} (donc x∈⋃Y)."""
    vx, vu = var("z"), var("u")                                # x : élément ; u : point de I×K
    vi, vk = var("p"), var("q")                                # témoins (= binders AXIOME_PRODUIT)
    droite = _membre_droit(vZ, vI, vK)
    reun_X = E.reunion_famille(vXX, vI)
    reun_Y = E.reunion_famille(vYY, vK)
    hx = N.assume(appartient(vx, droite))                      # x ∈ ⋃_{(ι,κ)} Z
    ex_u0 = N.modus_ponens(hx, equivalence_avant(
        _membre_reunion_fam(vZ, E.produit(vI, vK), vx)))       # (∃i)(i∈I×K et x∈Z(i))
    # le binder du ∃ de REUNION_FAM est « i » ; α-renomme en « u » (eigenvariable du témoin).
    body_u_i = et(appartient(var("i"), E.produit(vI, vK)), appartient(vx, E.valeur_famille(vZ, var("i"))))
    ex_u = N.modus_ponens(ex_u0, equivalence_avant(alpha_existe("i", "u", body_u_i)))  # (∃u)(u∈I×K et x∈Z(u))

    # corps sous témoin u : (u∈I×K et x∈Z(u)) ⊢ x∈gauche
    body_u = et(appartient(vu, E.produit(vI, vK)), appartient(vx, E.valeur_famille(vZ, vu)))
    hbu = N.assume(body_u)
    u_in = conjonction_elim_gauche(hbu)                        # u ∈ I×K
    x_Zu = conjonction_elim_droite(hbu)                        # x ∈ Z(u)
    decomp = N.modus_ponens(u_in, equivalence_avant(_membre_produit(vI, vK, vu)))  # (∃p)(∃q)(u=(p,q) ∧ p∈I ∧ q∈K)

    # corps sous témoins (ι₀,κ₀) : (u=(ι₀,κ₀) ∧ ι₀∈I ∧ κ₀∈K) ⊢ x∈gauche
    body_c = et(et(egal(vu, E.couple(vi, vk)), appartient(vi, vI)), appartient(vk, vK))
    hbc = N.assume(body_c)
    u_eq = conjonction_elim_gauche(conjonction_elim_gauche(hbc))  # u = (ι₀,κ₀)
    i_in = conjonction_elim_droite(conjonction_elim_gauche(hbc))  # ι₀ ∈ I
    k_in = conjonction_elim_droite(hbc)                          # κ₀ ∈ K
    Xi, Yk = _X(vXX, vi), _Y(vYY, vk)
    inter_t = E.intersection(Xi, Yk)                                  # X_{ι₀}∩Y_{κ₀}

    # Z(u) = Z((ι₀,κ₀)) = X_{ι₀}∩Y_{κ₀}  (congruence sur u=(ι₀,κ₀) puis AX_Z), réécritures
    eq_uc = N.modus_ponens(u_eq, _congruence_terme(vu, E.couple(vi, vk),
                                                   E.valeur_famille(vZ, var("@w")), "@w"))  # Z(u)=Z((ι₀,κ₀))
    x_in_Zc = _reecrit(x_Zu, eq_uc, vx, E.valeur_famille(vZ, vu),
                       E.valeur_famille(vZ, E.couple(vi, vk)))  # x ∈ Z((ι₀,κ₀))
    eq_z = instancie(instancie(ax_z, vi), vk)                  # Z((ι₀,κ₀)) = X_{ι₀}∩Y_{κ₀}
    x_in_inter = _reecrit(x_in_Zc, eq_z, vx, E.valeur_famille(vZ, E.couple(vi, vk)),
                          inter_t)                             # x ∈ X_{ι₀}∩Y_{κ₀}
    split = N.modus_ponens(x_in_inter, equivalence_avant(_membre_inter_bin(Xi, Yk, vx)))  # x∈X_{ι₀} et x∈Y_{κ₀}
    x_Xi = conjonction_elim_gauche(split)                      # x ∈ X_{ι₀}
    x_Yk = conjonction_elim_droite(split)                      # x ∈ Y_{κ₀}

    # (ι₀∈I et x∈X_{ι₀}) → x∈⋃X  (témoin ι=ι₀, binder « i » de REUNION_FAM)
    inj_X = et(appartient(var("i"), vI), appartient(vx, E.valeur_famille(vXX, var("i"))))
    ex_iX = N.modus_ponens(conjonction_intro(i_in, x_Xi), N.s5(inj_X, vi, "i"))
    x_in_uX = N.modus_ponens(ex_iX, equivalence_arriere(_membre_reunion_fam(vXX, vI, vx)))  # x∈⋃X
    # (κ₀∈K et x∈Y_{κ₀}) → x∈⋃Y  (témoin κ=κ₀)
    inj_Y = et(appartient(var("i"), vK), appartient(vx, E.valeur_famille(vYY, var("i"))))
    ex_kY = N.modus_ponens(conjonction_intro(k_in, x_Yk), N.s5(inj_Y, vk, "i"))
    x_in_uY = N.modus_ponens(ex_kY, equivalence_arriere(_membre_reunion_fam(vYY, vK, vx)))  # x∈⋃Y
    # recomposer x ∈ (⋃X)∩(⋃Y)
    x_gauche = N.modus_ponens(conjonction_intro(x_in_uX, x_in_uY),
                              equivalence_arriere(_membre_inter_bin(reun_X, reun_Y, vx)))  # x∈gauche

    # décharger témoins (ι₀,κ₀) — eigenvariables q puis p — puis le témoin u
    imp_c = N.loi_deduction(body_c, x_gauche)                  # body_c ⇒ x∈gauche
    elim_q = existe_elimination(imp_c, "q")                    # (∃q)body_c ⇒ x∈gauche
    elim_p = existe_elimination(elim_q, "p")                   # (∃p)(∃q)body_c ⇒ x∈gauche
    x_gauche2 = N.modus_ponens(decomp, elim_p)                # x∈gauche  {hx, body_u}
    imp_u = existe_elimination(N.loi_deduction(body_u, x_gauche2), "u")   # (∃u)body_u ⇒ x∈gauche
    x_gauche3 = N.modus_ponens(ex_u, imp_u)                   # x∈gauche  {hx}
    imp_x = N.loi_deduction(appartient(vx, droite), x_gauche3)
    return N.generalisation("z", imp_x)                       # droite ⊂ gauche


# ── micro-helpers (instances à TERMES) ────────────────────────────────────────
def _membre_reunion_fam(fam, idx, z):
    """⊢ (z∈⋃_{ι∈idx} fam_ι) ⇔ (∃i)(i∈idx ∧ z∈fam_i)  (instance de AXIOME_REUNION_FAM)."""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_REUNION_FAM)
    return instancie(instancie(instancie(ax, fam), idx), z)


def _membre_inter_bin(a, b, z):
    """⊢ (z∈a∩b) ⇔ (z∈a ∧ z∈b)  (instance de AXIOME_INTER binaire, dans les 22)."""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_INTER)
    return instancie(instancie(instancie(ax, a), b), z)


__all__ = ["cor_distributivite_reunion_inter_deux_familles", "_cible",
           "theorie_cor_distrib_2", "_membre_gauche", "_membre_droit"]
