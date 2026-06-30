"""§II.5 — COROLLAIRE de la Proposition 8 (E II.36, n°6 « Formules de distributivité »).

ÉNONCÉ VERBATIM (Bourbaki, E II.36, Corollaire de la Prop. 8) :
    « Soient (X_ι)_{ι∈I} et (Y_κ)_{κ∈K} deux familles d'ensembles dont les
      ensembles d'indices sont non vides.  On a
          ( ⋂_{ι∈I} X_ι ) ∪ ( ⋂_{κ∈K} Y_κ )  =  ⋂_{(ι,κ)∈I×K} ( X_ι ∪ Y_κ )   (1)
      et   ( ⋃_{ι∈I} X_ι ) ∩ ( ⋃_{κ∈K} Y_κ )  =  ⋃_{(ι,κ)∈I×K} ( X_ι ∩ Y_κ ). »  (2)

CIBLE DE CE MODULE — la PREMIÈRE formule (1), ÉGALITÉ PLEINE (les deux sens) :

    ⊢  ( ⋂_{ι∈I} X_ι ) ∪ ( ⋂_{κ∈K} Y_κ )  =  ⋂_{(ι,κ)∈I×K} ( X_ι ∪ Y_κ ).

POURQUOI C'EST CHOICE-FREE (contrairement au cas général Prop. 8, où ⊃ consomme
le choix-τ « cor. 2 de la prop. 5 ») : ICI il n'y a que DEUX familles, donc L = {1,2}.
Aucune fonction de choix sur une famille d'ensembles d'indices n'est requise ; le sens
⊃ se prouve par TIERS EXCLU classique (tactique `cas`), le sens ⊂ est ponctuel direct.

  • ⊃  (E II.36, raisonnement transposé au cas binaire) : soit x ∈ ⋂_{(ι,κ)}(X_ι∪Y_κ).
    Cas (∀ι∈I)(x∈X_ι) ⇒ x∈⋂X_ι.  Cas ¬(∀ι∈I)(x∈X_ι), i.e. (∃ι₀∈I)(x∉X_{ι₀}) :
    pour tout κ∈K, le couple (ι₀,κ)∈I×K donne x∈X_{ι₀}∪Y_κ (membre de l'∩) ; comme
    x∉X_{ι₀}, syllogisme disjonctif ⇒ x∈Y_κ.  Donc x∈⋂Y_κ.  Dans les deux cas
    x ∈ (⋂X_ι)∪(⋂Y_κ).
  • ⊂  ponctuel : x ∈ (⋂X)∪(⋂Y).  Soit p∈I×K ; p=(ι₀,κ₀) (AXIOME_PRODUIT, témoins).
    Si x∈⋂X alors x∈X_{ι₀}, sinon x∈⋂Y donc x∈Y_{κ₀} ; dans les deux cas
    x ∈ X_{ι₀}∪Y_κ₀ = Z(p).  Donc x ∈ ⋂_{(ι,κ)} Z.

PARAMÉTRAGE FIDÈLE (mécanisme C54 « famille définie par un terme »).
──────────────────────────────────────────────────────────────────────────────────
La famille DROITE Z = ((ι,κ) ↦ X_ι∪Y_κ)_{(ι,κ)∈I×K} n'est pas un terme calculable
(une famille est un graphe fonctionnel quelconque, E.II.4.1, et `valeur_famille(Z,p)`
est un TERME OPAQUE).  On la NOMME par un paramètre `Z` et on la CARACTÉRISE par son
terme SUR LES COUPLES EXPLICITES, via un axiome-schéma (C54) porté par une THÉORIE
LOCALE dédiée `theorie_cor_distrib(...)` — comme `theorie_distrib` (Prop. 8) /
`theorie_graphe_terme` / `theorie_diagonale_cantor` :

    AX_Z : (∀ι)(∀κ)  valeur_famille(Z, (ι,κ))  =  X_ι ∪ Y_κ.

La caractérisation EN COUPLES EXPLICITES évite pr₁/pr₂ : on n'instancie l'intersection
⋂_{p∈I×K} Z(p) qu'en des couples (ι,κ) qu'on FORME soi-même ; pour le sens ⊂, un
élément générique p∈I×K est décomposé en (ι₀,κ₀) par les TÉMOINS de AXIOME_PRODUIT
(p=(ι₀,κ₀), ι₀∈I, κ₀∈K), puis réécriture Z(p)=Z((ι₀,κ₀)).

Cette théorie locale n'entre PAS dans `theorie_ensembles()`, qui reste à 22 axiomes :
l'axiome-schéma est une DÉFINITION (légitimée S8+A1), pas une hypothèse ;
`N.axiome(theorie_cor_distrib, AX_Z)` produit `∅ ⊢ AX_Z` (théorème CLOS).

Notations (XX, YY, I, K, Z paramètres libres) :
  • X_ι = valeur_famille(XX, ι),  Y_κ = valeur_famille(YY, κ) ;
  • gauche = ( ⋂_{ι∈I} X_ι ) ∪ ( ⋂_{κ∈K} Y_κ ) = reunion(inter_famille(XX,I), inter_famille(YY,K)) ;
  • I×K = produit(I, K) ;
  • droite = ⋂_{(ι,κ)∈I×K} Z((ι,κ)) = inter_famille(Z, produit(I, K)).

STATUT : CLOS (0 hypothèse pendante).  theorie_ensembles() = 22 axiomes (inchangée).
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (Terme, var, et, ou, non, impl,
                                       appartient, egal, pourtout, existe)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    instancie, equivalence_avant, equivalence_arriere, conjonction_intro,
    conjonction_elim_gauche, conjonction_elim_droite, cas, tiers_exclu,
    dne, demorgan_ou, disj_syll_thm)
from bourbaki.logique.i_3_quantifies.tactiques_abrege_quantif import existe_elimination
from bourbaki.logique.i_4_egalitaires.tactiques_abrege_egalite import symetrie
from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_theoremes import extensionnalite_appliquee
from bourbaki.ensembles.familles.ii_2_produit_deux_ensembles.ensembles_produit import couple_dans_produit_ssi


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
    """( ⋂_{ι∈I} X_ι ) ∪ ( ⋂_{κ∈K} Y_κ ) = reunion(inter_famille(XX,I), inter_famille(YY,K))."""
    return E.reunion(E.inter_famille(_t(xx), _t(i)), E.inter_famille(_t(yy), _t(k)))


def _membre_droit(z="Z", i="I", k="K"):
    """⋂_{(ι,κ)∈I×K} ( X_ι∪Y_κ ) = inter_famille(Z, I×K),  Z((ι,κ)) = X_ι∪Y_κ."""
    return E.inter_famille(_t(z), E.produit(_t(i), _t(k)))


# ── axiome-schéma (C54) de définition de la famille Z sur I×K ──────────────────
def _ax_z(xx, yy, z, iota="i", kappa="k"):
    """AX_Z : (∀ι)(∀κ)  valeur_famille(Z, (ι,κ)) = X_ι ∪ Y_κ.

    « Z est la famille (ι,κ) ↦ X_ι∪Y_κ. »  (déf. par un terme SUR COUPLES, C54.)"""
    vi, vk = var(iota), var(kappa)
    return pourtout(iota, pourtout(kappa,
        egal(E.valeur_famille(_t(z), E.couple(vi, vk)), E.reunion(_X(xx, vi), _Y(yy, vk)))))


def theorie_cor_distrib(xx="XX", yy="YY", z="Z"):
    """Théorie LOCALE portant l'axiome-schéma C54 de définition de la famille Z.

    N'entre PAS dans theorie_ensembles() (qui reste à 22) : AX_Z est une DÉFINITION
    (S8+A1), pas une hypothèse ; `N.axiome(theorie_cor_distrib, AX_Z)` donne `∅ ⊢ AX_Z`."""
    return N.Theorie("Cor-Distributivite-2fam", [_ax_z(_t(xx), _t(yy), _t(z))])


# ── cible ─────────────────────────────────────────────────────────────────────
def _cible(xx="XX", yy="YY", z="Z", i="I", k="K"):
    """⊢-cible : ( ⋂_{ι∈I}X_ι ) ∪ ( ⋂_{κ∈K}Y_κ ) = ⋂_{(ι,κ)∈I×K}( X_ι∪Y_κ )."""
    return egal(_membre_gauche(xx, yy, i, k), _membre_droit(z, i, k))


# ── théorème principal ────────────────────────────────────────────────────────
# @livre Ch.II §5.6 Cor.- | E II.36 L.15-19 | PDF p.87
def cor_distributivite_inter_reunion_deux_familles(xx="XX", yy="YY", z="Z", i="I", k="K"):
    """⊢ ( ⋂_{ι∈I}X_ι ) ∪ ( ⋂_{κ∈K}Y_κ ) = ⋂_{(ι,κ)∈I×K}( X_ι∪Y_κ ).

    COROLLAIRE de la PROPOSITION 8, première formule (1), E II.36.  ÉGALITÉ PLEINE,
    SANS choix (cas L={1,2}) : sens ⊃ par tiers exclu (`cas`), sens ⊂ ponctuel direct.
    Clos (0 hyp).  Z : famille externe sur I×K définie par `theorie_cor_distrib`
    (axiome C54 sur les couples explicites)."""
    vXX, vYY, vZ, vI, vK = _t(xx), _t(yy), _t(z), _t(i), _t(k)
    th = theorie_cor_distrib(vXX, vYY, vZ)
    ax_z = N.axiome(th, _ax_z(vXX, vYY, vZ))            # (∀ι)(∀κ) Z((ι,κ)) = X_ι∪Y_κ

    gauche = _membre_gauche(vXX, vYY, vI, vK)
    droite = _membre_droit(vZ, vI, vK)

    incl_cs = _inclusion_directe(vXX, vYY, vZ, vI, vK, ax_z)   # gauche ⊂ droite
    incl_cd = _inclusion_reciproque(vXX, vYY, vZ, vI, vK, ax_z)  # droite ⊂ gauche

    ext = extensionnalite_appliquee(gauche, droite)
    eq = N.modus_ponens(conjonction_intro(incl_cs, incl_cd), ext)   # gauche = droite
    assert eq.conclusion == _cible(xx, yy, z, i, k), \
        "cor_distributivite_inter_reunion_deux_familles : conclusion ≠ cible"
    return eq


# ── sens ⊂ :  (⋂X)∪(⋂Y)  ⊂  ⋂_{(ι,κ)∈I×K}(X_ι∪Y_κ) ───────────────────────────
def _inclusion_directe(vXX, vYY, vZ, vI, vK, ax_z):
    """gauche ⊂ droite.  x∈gauche=(⋂X)∪(⋂Y) ; u∈I×K → u=(ι₀,κ₀) (témoins AXIOME_PRODUIT,
    liés `p,q`) ; par cas sur (x∈⋂X)∨(x∈⋂Y) on obtient x∈X_{ι₀}∪Y_{κ₀}=Z(u)."""
    vx, vu = var("z"), var("u")                                 # x : élément ; u : point de I×K
    vi, vk = var("p"), var("q")                                 # témoins (= binders AXIOME_PRODUIT)
    gauche = _membre_gauche(vXX, vYY, vI, vK)
    hx = N.assume(appartient(vx, gauche))                       # x ∈ (⋂X)∪(⋂Y)
    disj = N.modus_ponens(hx, equivalence_avant(_membre_reunion(
        E.inter_famille(vXX, vI), E.inter_famille(vYY, vK), vx)))   # (x∈⋂X) ∨ (x∈⋂Y)

    # ── but : x ∈ ⋂_{u∈I×K} Z(u)  ⇐  (∀u)(u∈I×K ⇒ x∈Z(u)) ────────────────────
    hu = N.assume(appartient(vu, E.produit(vI, vK)))            # u ∈ I×K
    decomp = N.modus_ponens(hu, equivalence_avant(_membre_produit(vI, vK, vu)))  # (∃p)(∃q)(u=(p,q) ∧ p∈I ∧ q∈K)

    # corps sous témoins (ι₀,κ₀) : (u=(ι₀,κ₀) ∧ ι₀∈I ∧ κ₀∈K) ⊢ x∈Z(u)
    body = et(et(egal(vu, E.couple(vi, vk)), appartient(vi, vI)), appartient(vk, vK))
    hb = N.assume(body)
    p_eq = conjonction_elim_gauche(conjonction_elim_gauche(hb))   # u = (ι₀,κ₀)
    i_in = conjonction_elim_droite(conjonction_elim_gauche(hb))   # ι₀ ∈ I
    k_in = conjonction_elim_droite(hb)                           # κ₀ ∈ K
    Xi, Yk = _X(vXX, vi), _Y(vYY, vk)
    union = E.reunion(Xi, Yk)                                   # X_{ι₀}∪Y_{κ₀}

    # branche x∈⋂X : x∈X_{ι₀}  →  x∈X_{ι₀}∪Y_{κ₀}
    hX = N.assume(appartient(vx, E.inter_famille(vXX, vI)))
    xXi = N.modus_ponens(i_in, N.modus_ponens(hX, _inter_elim(vXX, vI, vi, vx)))  # x∈X_{ι₀}
    xU_X = N.modus_ponens(N.modus_ponens(xXi, N.s2(appartient(vx, Xi), appartient(vx, Yk))),
                          equivalence_arriere(_membre_reunion(Xi, Yk, vx)))       # x∈X∪Y
    brX = N.loi_deduction(appartient(vx, E.inter_famille(vXX, vI)), xU_X)
    # branche x∈⋂Y : x∈Y_{κ₀}  →  x∈X_{ι₀}∪Y_{κ₀}
    hY = N.assume(appartient(vx, E.inter_famille(vYY, vK)))
    xYk = N.modus_ponens(k_in, N.modus_ponens(hY, _inter_elim(vYY, vK, vk, vx)))  # x∈Y_{κ₀}
    xU_Y = N.modus_ponens(N.modus_ponens(N.modus_ponens(xYk, N.s2(appartient(vx, Yk), appartient(vx, Xi))),
                                         N.s3(appartient(vx, Yk), appartient(vx, Xi))),
                          equivalence_arriere(_membre_reunion(Xi, Yk, vx)))       # x∈X∪Y
    brY = N.loi_deduction(appartient(vx, E.inter_famille(vYY, vK)), xU_Y)
    x_in_union = cas(disj, brX, brY)                           # x ∈ X_{ι₀}∪Y_{κ₀}  {hx,hb}

    # X_{ι₀}∪Y_{κ₀} = Z((ι₀,κ₀)) = Z(u)  (AX_Z + u=(ι₀,κ₀)), réécriture
    eq_z = _sym(instancie(instancie(ax_z, vi), vk))            # X_{ι₀}∪Y_{κ₀} = Z((ι₀,κ₀))
    x_in_Zc = _reecrit(x_in_union, eq_z, vx, union, E.valeur_famille(vZ, E.couple(vi, vk)))  # x∈Z((ι₀,κ₀))
    eq_uc = _sym(N.modus_ponens(p_eq, _congruence_terme(vu, E.couple(vi, vk),
                                                        E.valeur_famille(vZ, var("@w")), "@w")))  # Z((ι₀,κ₀))=Z(u)
    x_in_Zu = _reecrit(x_in_Zc, eq_uc, vx, E.valeur_famille(vZ, E.couple(vi, vk)),
                       E.valeur_famille(vZ, vu))               # x ∈ Z(u)

    # décharger les témoins (ι₀,κ₀), puis u∈I×K, généraliser u
    imp_b = N.loi_deduction(body, x_in_Zu)                     # body ⇒ x∈Z(u)
    elim_q = existe_elimination(imp_b, "q")                    # (∃q)body ⇒ x∈Z(u)
    elim_p = existe_elimination(elim_q, "p")                   # (∃p)(∃q)body ⇒ x∈Z(u)
    x_in_Zu2 = N.modus_ponens(decomp, elim_p)                 # x∈Z(u)  {hx, u∈I×K}
    imp_u = N.loi_deduction(appartient(vu, E.produit(vI, vK)), x_in_Zu2)   # u∈I×K ⇒ x∈Z(u)
    forall_u = N.generalisation("u", imp_u)                   # (∀u)(u∈I×K ⇒ x∈Z(u))
    forall_b = _rebind(forall_u, _inter_binder(vZ, E.produit(vI, vK), vx))
    x_in_droite = N.modus_ponens(forall_b, equivalence_arriere(
        _membre_inter(vZ, E.produit(vI, vK), vx)))            # x ∈ ⋂_{u∈I×K} Z(u)

    imp_x = N.loi_deduction(appartient(vx, gauche), x_in_droite)
    return N.generalisation("z", imp_x)                       # gauche ⊂ droite


# ── sens ⊃ :  ⋂_{(ι,κ)∈I×K}(X_ι∪Y_κ)  ⊂  (⋂X)∪(⋂Y)  (TIERS EXCLU, sans choix) ─
def _inclusion_reciproque(vXX, vYY, vZ, vI, vK, ax_z):
    """droite ⊂ gauche.  x∈⋂_{(ι,κ)}(X_ι∪Y_κ).  Tiers exclu sur A=(∀ι)(ι∈I⇒x∈X_ι) :
    cas A ⇒ x∈⋂X ; cas ¬A ⇒ témoin ι₀∈I avec x∉X_{ι₀}, donc (∀κ)(κ∈K⇒x∈Y_κ) ⇒ x∈⋂Y."""
    vx, vi, vk = var("z"), var("i"), var("k")
    droite = _membre_droit(vZ, vI, vK)
    gauche = _membre_gauche(vXX, vYY, vI, vK)
    inter_g = E.inter_famille(vXX, vI)
    inter_d = E.inter_famille(vYY, vK)
    hx = N.assume(appartient(vx, droite))                      # x ∈ ⋂_{(ι,κ)} Z

    A = pourtout("i", impl(appartient(vi, vI), appartient(vx, _X(vXX, vi))))  # (∀ι)(ι∈I⇒x∈X_ι)
    te = tiers_exclu(A)                                        # A ∨ ¬A

    # ── branche A : x∈⋂X → x∈gauche ──────────────────────────────────────────
    hA = N.assume(A)
    forall_i = _rebind(hA, _inter_binder(vXX, vI, vx))
    xX = N.modus_ponens(forall_i, equivalence_arriere(_membre_inter(vXX, vI, vx)))  # x∈⋂X
    xg_A = N.modus_ponens(N.modus_ponens(xX, N.s2(appartient(vx, inter_g), appartient(vx, inter_d))),
                          equivalence_arriere(_membre_reunion(inter_g, inter_d, vx)))  # x∈gauche
    brA = N.loi_deduction(A, xg_A)

    # ── branche ¬A : (∃ι)¬(ι∈I⇒x∈X_ι) → x∈⋂Y → x∈gauche ──────────────────────
    hnA = N.assume(non(A))
    ex_i = N.modus_ponens(hnA, dne(existe("i", non(impl(appartient(vi, vI), appartient(vx, _X(vXX, vi)))))))  # (∃ι)¬(…)
    # corps sous témoin ι₀ : ¬(ι₀∈I ⇒ x∈X_{ι₀}) ⊢ x∈gauche
    notimp = non(impl(appartient(vi, vI), appartient(vx, _X(vXX, vi))))
    hni = N.assume(notimp)
    # ¬(P⇒Q) = ¬(¬P∨Q) ⇔ (¬¬P et ¬Q) : extraire ι₀∈I et x∉X_{ι₀}
    conj = N.modus_ponens(hni, equivalence_avant(demorgan_ou(
        non(appartient(vi, vI)), appartient(vx, _X(vXX, vi)))))   # ¬¬(ι₀∈I) et ¬(x∈X_{ι₀})
    i_in = N.modus_ponens(conjonction_elim_gauche(conj), dne(appartient(vi, vI)))  # ι₀∈I
    x_notXi = conjonction_elim_droite(conj)                     # ¬(x∈X_{ι₀})

    # (∀κ)(κ∈K ⇒ x∈Y_κ) : pour κ frais, (ι₀,κ)∈I×K → x∈Z((ι₀,κ))=X_{ι₀}∪Y_κ ; ¬(x∈X_{ι₀}) ⇒ x∈Y_κ
    hk = N.assume(appartient(vk, vK))                          # κ∈K
    ck_in = N.modus_ponens(conjonction_intro(i_in, hk),
                           equivalence_arriere(couple_dans_produit_ssi(vi, vk, vI, vK)))  # (ι₀,κ)∈I×K
    x_in_Zc = N.modus_ponens(ck_in, N.modus_ponens(hx, _inter_elim(
        vZ, E.produit(vI, vK), E.couple(vi, vk), vx)))          # x∈Z((ι₀,κ))
    eq_z = instancie(instancie(ax_z, vi), vk)                  # Z((ι₀,κ)) = X_{ι₀}∪Y_κ
    Xi, Yk = _X(vXX, vi), _Y(vYY, vk)
    x_in_union = _reecrit(x_in_Zc, eq_z, vx, E.valeur_famille(vZ, E.couple(vi, vk)),
                          E.reunion(Xi, Yk))                    # x∈X_{ι₀}∪Y_κ
    disj = N.modus_ponens(x_in_union, equivalence_avant(_membre_reunion(Xi, Yk, vx)))  # x∈X_{ι₀} ∨ x∈Y_κ
    x_Yk = N.modus_ponens(x_notXi, N.modus_ponens(disj,
        disj_syll_thm(appartient(vx, Xi), appartient(vx, Yk))))  # x∈Y_κ
    imp_k = N.loi_deduction(appartient(vk, vK), x_Yk)          # κ∈K ⇒ x∈Y_κ
    forall_k = N.generalisation("k", imp_k)                    # (∀κ)(κ∈K⇒x∈Y_κ)
    forall_k = _rebind(forall_k, _inter_binder(vYY, vK, vx))
    xY = N.modus_ponens(forall_k, equivalence_arriere(_membre_inter(vYY, vK, vx)))  # x∈⋂Y
    xg = N.modus_ponens(N.modus_ponens(N.modus_ponens(xY, N.s2(appartient(vx, inter_d), appartient(vx, inter_g))),
                                       N.s3(appartient(vx, inter_d), appartient(vx, inter_g))),
                        equivalence_arriere(_membre_reunion(inter_g, inter_d, vx)))  # x∈gauche
    elim = existe_elimination(N.loi_deduction(notimp, xg), "i")  # (∃ι)¬(…) ⇒ x∈gauche
    xg_nA = N.modus_ponens(ex_i, elim)                         # x∈gauche  {hx, ¬A}
    brnA = N.loi_deduction(non(A), xg_nA)

    x_in_gauche = cas(te, brA, brnA)                          # x∈gauche  {hx}
    imp_x = N.loi_deduction(appartient(vx, droite), x_in_gauche)
    return N.generalisation("z", imp_x)                       # droite ⊂ gauche


# ── micro-helpers (instances à TERMES, réécriture) ────────────────────────────
def _membre_reunion(a, b, z):
    """⊢ (z∈a∪b) ⇔ (z∈a ∨ z∈b)  (instance de AXIOME_REUNION, dans les 22)."""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_REUNION)
    return instancie(instancie(instancie(ax, a), b), z)


def _membre_produit(gx, gy, z):
    """⊢ (z∈gx×gy) ⇔ (∃p)(∃q)(z=(p,q) ∧ p∈gx ∧ q∈gy)  (instance de AXIOME_PRODUIT).

    Le liant interne de l'axiome est « p, q » ; on l'appariera aux témoins i, k via
    α-renommage du ∃ externe dans `_inclusion_directe` (témoins nommés i, k)."""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_PRODUIT)
    return instancie(instancie(instancie(ax, gx), gy), z)


def _membre_inter(fam, idx, z):
    """⊢ (z∈⋂_{ι∈idx} fam_ι) ⇔ (∀b)(b∈idx ⇒ z∈fam_b)  (instance de AXIOME_INTER_FAM)."""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_INTER_FAM)
    return instancie(instancie(instancie(ax, fam), idx), z)


def _inter_elim(fam, idx, a, z):
    """⊢ (z∈⋂_{ι∈idx} fam_ι) ⇒ (a∈idx ⇒ z∈fam_a)  (élim ∩-famille à TERMES)."""
    inst = _membre_inter(fam, idx, z)
    h = N.assume(appartient(z, E.inter_famille(fam, idx)))
    forall = N.modus_ponens(h, equivalence_avant(inst))        # (∀b)(b∈idx⇒z∈fam_b)
    at_a = instancie(forall, a)                                # (a∈idx ⇒ z∈fam_a)
    return N.loi_deduction(appartient(z, E.inter_famille(fam, idx)), at_a)


def _inter_binder(fam, idx, z):
    """Nom du liant du ∀ au membre droit de `_membre_inter` : (∀b)(b∈idx⇒z∈fam_b)."""
    from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import antecedent_consequent
    ante, _ = antecedent_consequent(equivalence_arriere(_membre_inter(fam, idx, z)).conclusion)
    return _forall_binder(ante)


def _forall_binder(formule_forall):
    """Nom du liant d'un ∀ encodé ¬(∃x)¬R  →  x."""
    if formule_forall.tag == "non" and formule_forall.sous and formule_forall.sous[0].tag == "exists":
        return formule_forall.sous[0].lieur
    raise ValueError("liant ∀ introuvable")


def _rebind(thm_forall, cible):
    """Alpha-renomme ⊢ (∀src)R en ⊢ (∀cible)(cible|src)R (si src≠cible)."""
    from bourbaki.logique.i_3_quantifies.tactiques_abrege_quantif import alpha_pour_tout
    f = thm_forall.conclusion
    src = _forall_binder(f)
    if src == cible:
        return thm_forall
    R = f.sous[0].sous[0].sous[0]                              # (∀src)R = ¬(∃src)¬R → R
    return N.modus_ponens(thm_forall, equivalence_avant(alpha_pour_tout(src, cible, R)))


def _sym(thm_eq):
    """De ⊢ a=b déduire ⊢ b=a."""
    a, b = thm_eq.conclusion.termes
    return N.modus_ponens(thm_eq, symetrie(a, b))


def _congruence_terme(a, b, terme_motif, w="w"):
    """⊢ a=b ⇒ T[a]=T[b]  (congruence le long de a=b dans le terme T, trou `w`)."""
    from bourbaki.logique.i_4_egalitaires.tactiques_abrege_egalite import congruence_terme
    return congruence_terme(a, b, terme_motif, w)


def _reecrit(thm_t_in_a, thm_eq_ab, t, a, b):
    """⊢ t∈a , ⊢ a=b  ⟹  ⊢ t∈b   (réécriture de l'appartenance le long de a=b, S6)."""
    R = appartient(t, var("@rw"))
    equ = N.modus_ponens(thm_eq_ab, N.s6(a, b, "@rw", R))      # (t∈a) ⇔ (t∈b)
    return N.modus_ponens(thm_t_in_a, equivalence_avant(equ))


__all__ = ["cor_distributivite_inter_reunion_deux_familles", "_cible",
           "theorie_cor_distrib", "_membre_gauche", "_membre_droit"]
