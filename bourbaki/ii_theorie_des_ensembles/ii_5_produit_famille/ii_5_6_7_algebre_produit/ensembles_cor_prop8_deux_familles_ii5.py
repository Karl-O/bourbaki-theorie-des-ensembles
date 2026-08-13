"""§II.5 — COROLLAIRE de la Proposition 8 (E II.36, n°6 « Formules de distributivité »).

ÉNONCÉ VERBATIM (Bourbaki, E II.36, Corollaire de la Prop. 8) :
    « Soient (X_ι)_{ι∈I} et (Y_κ)_{κ∈K} deux familles d'ensembles dont les
      ensembles d'indices sont non vides.  On a
          ( ⋂_{ι∈I} X_ι ) ∪ ( ⋂_{κ∈K} Y_κ )  =  ⋂_{(ι,κ)∈I×K} ( X_ι ∪ Y_κ )   (1)
      et   ( ⋃_{ι∈I} X_ι ) ∩ ( ⋃_{κ∈K} Y_κ )  =  ⋃_{(ι,κ)∈I×K} ( X_ι ∩ Y_κ ). »  (2)

CIBLE DE CE MODULE — la PREMIÈRE formule (1), ÉGALITÉ PLEINE (les deux sens),
SOUS L'HYPOTHÈSE « les ensembles d'indices sont non vides » que Bourbaki écrit :

    ⊢  (∃i)(i∈I) ⇒ ( (∃i)(i∈K) ⇒
           ( ⋂_{ι∈I} X_ι ) ∪ ( ⋂_{κ∈K} Y_κ )  =  ⋂_{(ι,κ)∈I×K} ( X_ι ∪ Y_κ ) ).

⚠️ RENFORCEMENT D'ÉNONCÉ (2026-07-26, migration « ⋂ = sélection dans ⋃ », II.4.1 Déf. 2).
Ce module concluait autrefois l'égalité SANS hypothèse — et cette forme-là est FAUSSE.
Contre-exemple : I = ∅ et K ≠ ∅.  Alors ⋂_{ι∈∅} X_ι = ∅ (`inter_famille_vide_egale_vide`),
donc le membre gauche vaut ⋂_{κ∈K} Y_κ, qui peut être non vide ; mais I×K = ∅, donc le
membre droit vaut ⋂_{p∈∅} Z_p = ∅.  L'égalité tombe.  L'ancien énoncé n'était « démontrable »
que parce que l'ANCIEN AXIOME_INTER_FAM était contradictoire (⋂ sur ∅ = ensemble universel,
cf. outils_ia/audit/preuve_incoherence_inter_vide.py).  L'hypothèse rétablie est EXACTEMENT
celle de la première ligne du corollaire : « … dont les ensembles d'indices sont non vides ».

RÉPARTITION DE L'HYPOTHÈSE — un seul des deux sens la consomme.
  • ⊃ (`_inclusion_reciproque`) reste INCONDITIONNEL : son hypothèse de travail est
    x ∈ ⋂_{(ι,κ)∈I×K} Z, qui FOURNIT les deux témoins d'indice gratuitement — ⋂ ⊂ ⋃
    (`inter_inclus_reunion`) donne un p₀ ∈ I×K, que AXIOME_PRODUIT décompose en
    (ι₀,κ₀) avec ι₀∈I et κ₀∈K (`_indices_depuis_inter`).  Énoncé INCHANGÉ.
  • ⊂ (`_inclusion_directe`) la consomme VRAIMENT : partant de x ∈ (⋂X)∪(⋂Y) on ne
    dispose que d'un témoin dans I OU d'un témoin dans K, jamais des deux ; et pour
    I≠∅, K=∅ l'inclusion est déjà fausse (gauche ⊃ ⋂X non vide, droite = ∅).
Seule l'ÉGALITÉ porte donc les deux antécédents, et elle reste CLOSE (0 hyp pendante).

POURQUOI C'EST CHOICE-FREE (contrairement au cas général Prop. 8, où ⊃ consomme
le choix-τ « cor. 2 de la prop. 5 ») : ICI il n'y a que DEUX familles, donc L = {1,2}.
Aucune fonction de choix sur une famille d'ensembles d'indices n'est requise ; le sens
⊃ se prouve par TIERS EXCLU classique (tactique `cas`), le sens ⊂ est ponctuel direct.

  • ⊃  (E II.36, raisonnement transposé au cas binaire) : soit x ∈ ⋂_{(ι,κ)}(X_ι∪Y_κ).
    Cas (∀ι∈I)(x∈X_ι) ⇒ x∈⋂X_ι.  Cas ¬(∀ι∈I)(x∈X_ι), i.e. (∃ι₀∈I)(x∉X_{ι₀}) :
    pour tout κ∈K, le couple (ι₀,κ)∈I×K donne x∈X_{ι₀}∪Y_κ (membre de l'∩) ; comme
    x∉X_{ι₀}, syllogisme disjonctif ⇒ x∈Y_κ.  Donc x∈⋂Y_κ.  Dans les deux cas
    x ∈ (⋂X_ι)∪(⋂Y_κ).  (Les introductions dans ⋂X et ⋂Y passent par les témoins
    tirés de x ∈ ⋂_{(ι,κ)} Z — d'où la gratuité annoncée plus haut.)
  • ⊂  ponctuel : x ∈ (⋂X)∪(⋂Y).  Soit p∈I×K ; p=(ι₀,κ₀) (AXIOME_PRODUIT, témoins).
    Si x∈⋂X alors x∈X_{ι₀}, sinon x∈⋂Y donc x∈Y_{κ₀} ; dans les deux cas
    x ∈ X_{ι₀}∪Y_κ₀ = Z(p).  Donc (∀p∈I×K) x∈Z(p) ; l'introduction dans ⋂ réclame
    de plus x ∈ ⋃_{p∈I×K} Z(p), obtenu au témoin (τi(i∈I), τi(i∈K)) ∈ I×K.

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

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (Terme, var, et, ou, non, impl,
                                       appartient, egal, pourtout, existe, tau)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    instancie, equivalence_avant, equivalence_arriere, conjonction_intro,
    conjonction_elim_gauche, conjonction_elim_droite, cas, tiers_exclu,
    dne, demorgan_ou, disj_syll_thm)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import existe_elimination
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import symetrie
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_theoremes import extensionnalite_appliquee
from bourbaki.ii_theorie_des_ensembles.ii_2_couples.ii_2_2_produit_deux_ensembles.ensembles_produit import couple_dans_produit_ssi
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_intersection_fondation.ensembles_inter_selection_ii4 import (
    corps_membres_famille, inter_inclus_reunion)
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_intersection_fondation.ensembles_inter_migration_ii4 import (
    indices_non_vides, caracterisation_inter_famille_non_vide)


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
def _hyp_indices(i="I", k="K"):
    """( (∃i)(i∈I) , (∃i)(i∈K) ) — « les ensembles d'indices sont non vides » (E II.36).

    Forme utilisable de l'hypothèse que Bourbaki écrit à la première ligne du
    corollaire ; `indices_non_vides` est la brique commune de la migration ⋂, dont
    le liant canonique « i » est IMPOSÉ (celui d'AXIOME_REUNION_FAM/INTER_FAM) — on
    l'emploie pour les DEUX ensembles d'indices, ce qui évite tout pont-α."""
    return indices_non_vides(_t(i), "i"), indices_non_vides(_t(k), "i")


def _cible(xx="XX", yy="YY", z="Z", i="I", k="K"):
    """⊢-cible : (∃i)(i∈I) ⇒ ( (∃i)(i∈K) ⇒
                  ( ⋂_{ι∈I}X_ι ) ∪ ( ⋂_{κ∈K}Y_κ ) = ⋂_{(ι,κ)∈I×K}( X_ι∪Y_κ ) ).

    Les deux antécédents sont le RENFORCEMENT du 2026-07-26 (cf. en-tête du module) :
    sans eux l'égalité est FAUSSE (I=∅, K≠∅ : gauche = ⋂_{κ∈K}Y_κ, droite = ∅)."""
    hI, hK = _hyp_indices(i, k)
    return impl(hI, impl(hK, egal(_membre_gauche(xx, yy, i, k), _membre_droit(z, i, k))))


# ── théorème principal ────────────────────────────────────────────────────────
# @livre Ch.II §5.6 Cor.- | E II.36 L.15-19 | PDF p.87
# @livre Ch.R §4 Prop.- | E.R.19 item 8 ((42) distributivité (⋂X_ι)∪(⋂Y_κ)=⋂(X_ι∪Y_κ)) | PDF p.322
def cor_distributivite_inter_reunion_deux_familles(xx="XX", yy="YY", z="Z", i="I", k="K"):
    """⊢ (∃i)(i∈I) ⇒ ( (∃i)(i∈K) ⇒
           ( ⋂_{ι∈I}X_ι ) ∪ ( ⋂_{κ∈K}Y_κ ) = ⋂_{(ι,κ)∈I×K}( X_ι∪Y_κ ) ).

    COROLLAIRE de la PROPOSITION 8, première formule (1), E II.36.  ÉGALITÉ PLEINE,
    SANS choix (cas L={1,2}) : sens ⊃ par tiers exclu (`cas`), sens ⊂ ponctuel direct.
    Clos (0 hyp).  Z : famille externe sur I×K définie par `theorie_cor_distrib`
    (axiome C54 sur les couples explicites).

    ÉNONCÉ RENFORCÉ (migration « ⋂ = sélection dans ⋃ », 2026-07-26).  Les deux
    antécédents sont l'hypothèse EXPLICITE du corollaire (« deux familles d'ensembles
    dont les ensembles d'indices sont non vides », E II.36 L.15).  L'ancienne forme,
    sans hypothèse, était FAUSSE : pour I=∅ et K≠∅ le membre gauche vaut ⋂_{κ∈K}Y_κ
    (car ⋂_{ι∈∅}X_ι = ∅) tandis que I×K=∅ rend le membre droit vide.  Elle n'était
    « démontrable » que via l'ancien AXIOME_INTER_FAM, contradictoire.  Seule
    l'inclusion ⊂ consomme l'hypothèse ; ⊃ reste inconditionnelle (voir l'en-tête)."""
    vXX, vYY, vZ, vI, vK = _t(xx), _t(yy), _t(z), _t(i), _t(k)
    th = theorie_cor_distrib(vXX, vYY, vZ)
    ax_z = N.axiome(th, _ax_z(vXX, vYY, vZ))            # (∀ι)(∀κ) Z((ι,κ)) = X_ι∪Y_κ

    gauche = _membre_gauche(vXX, vYY, vI, vK)
    droite = _membre_droit(vZ, vI, vK)
    hyp_I, hyp_K = _hyp_indices(vI, vK)                 # (∃i)(i∈I) , (∃i)(i∈K)

    incl_cs = _inclusion_directe(vXX, vYY, vZ, vI, vK, ax_z)   # gauche ⊂ droite {hyp_I,hyp_K}
    incl_cd = _inclusion_reciproque(vXX, vYY, vZ, vI, vK, ax_z)  # droite ⊂ gauche (CLOS)

    ext = extensionnalite_appliquee(gauche, droite)
    eq = N.modus_ponens(conjonction_intro(incl_cs, incl_cd), ext)   # gauche = droite
    # décharge des deux hypothèses d'indices : ni ι ni κ n'y sont libres, et la
    # généralisation sur z a déjà été faite sous elles (licite : z ∉ libres(hyp)).
    res = N.loi_deduction(hyp_I, N.loi_deduction(hyp_K, eq))
    assert res.conclusion == _cible(xx, yy, z, i, k), \
        "cor_distributivite_inter_reunion_deux_familles : conclusion ≠ cible"
    assert res.hypotheses == frozenset(), \
        "cor_distributivite_inter_reunion_deux_familles : doit être CLOS (0 hypothèse)"
    return res


# ── sens ⊂ :  (⋂X)∪(⋂Y)  ⊂  ⋂_{(ι,κ)∈I×K}(X_ι∪Y_κ) ───────────────────────────
def _inclusion_directe(vXX, vYY, vZ, vI, vK, ax_z):
    """gauche ⊂ droite,  SOUS les hypothèses (∃i)(i∈I) et (∃i)(i∈K) (rendues pendantes).

    x∈gauche=(⋂X)∪(⋂Y) ; u∈I×K → u=(ι₀,κ₀) (témoins AXIOME_PRODUIT, liés `p,q`) ;
    par cas sur (x∈⋂X)∨(x∈⋂Y) on obtient x∈X_{ι₀}∪Y_{κ₀}=Z(u).

    C'EST ICI que l'hypothèse du corollaire est consommée (motif (b) de la migration) :
    conclure x ∈ ⋂_{u∈I×K} Z(u) réclame désormais AUSSI x ∈ ⋃_{u∈I×K} Z(u), donc un
    TÉMOIN d'indice dans I×K — et x∈(⋂X)∪(⋂Y) n'en fournit jamais qu'un seul côté.
    Sans hypothèse l'inclusion est d'ailleurs FAUSSE (I≠∅, K=∅ : droite = ∅)."""
    vx, vu = var("z"), var("u")                                 # x : élément ; u : point de I×K
    vi, vk = var("p"), var("q")                                 # témoins (= binders AXIOME_PRODUIT)
    gauche = _membre_gauche(vXX, vYY, vI, vK)
    hyp_I, hyp_K = _hyp_indices(vI, vK)
    hI, hK = N.assume(hyp_I), N.assume(hyp_K)                   # « I≠∅ », « K≠∅ » (E II.36)
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
    # INTRODUCTION dans ⋂ : elle exige un témoin d'indice dans I×K (motif (b)).
    # (τi(i∈I), τi(i∈K)) en est un sous hyp_I/hyp_K (`_temoin_indice_produit`), et
    # `caracterisation_inter_famille_non_vide` restitue alors l'ANCIENNE équivalence.
    eq_Z = instancie(N.modus_ponens(_temoin_indice_produit(vI, vK, hI, hK),
                                    caracterisation_inter_famille_non_vide(
                                        vZ, E.produit(vI, vK), "z")), vx)
    x_in_droite = N.modus_ponens(forall_b, equivalence_arriere(eq_Z))  # x ∈ ⋂_{u∈I×K} Z(u)

    imp_x = N.loi_deduction(appartient(vx, gauche), x_in_droite)
    # généralisation licite : « z » n'est libre ni dans hyp_I ((∃i)(i∈I)) ni dans hyp_K
    return N.generalisation("z", imp_x)                       # gauche ⊂ droite {hyp_I,hyp_K}


# ── sens ⊃ :  ⋂_{(ι,κ)∈I×K}(X_ι∪Y_κ)  ⊂  (⋂X)∪(⋂Y)  (TIERS EXCLU, sans choix) ─
def _inclusion_reciproque(vXX, vYY, vZ, vI, vK, ax_z):
    """droite ⊂ gauche.  x∈⋂_{(ι,κ)}(X_ι∪Y_κ).  Tiers exclu sur A=(∀ι)(ι∈I⇒x∈X_ι) :
    cas A ⇒ x∈⋂X ; cas ¬A ⇒ témoin ι₀∈I avec x∉X_{ι₀}, donc (∀κ)(κ∈K⇒x∈Y_κ) ⇒ x∈⋂Y.

    ÉNONCÉ INCHANGÉ par la migration (issue A), et SANS hypothèse d'indices : les
    deux introductions (dans ⋂X et dans ⋂Y) réclament certes un témoin d'indice,
    mais l'hypothèse de travail x ∈ ⋂_{(ι,κ)∈I×K} Z le fournit GRATUITEMENT —
    `_indices_depuis_inter` le lit dans ⋂ ⊂ ⋃ puis le décompose par AXIOME_PRODUIT."""
    vx, vi, vk = var("z"), var("i"), var("k")
    droite = _membre_droit(vZ, vI, vK)
    gauche = _membre_gauche(vXX, vYY, vI, vK)
    inter_g = E.inter_famille(vXX, vI)
    inter_d = E.inter_famille(vYY, vK)
    hx = N.assume(appartient(vx, droite))                      # x ∈ ⋂_{(ι,κ)} Z
    # témoins d'indice GRATUITS, tirés de hx ; ils rendent les deux introductions
    # ci-dessous licites sans rien ajouter à l'énoncé.
    ex_I, ex_K = _indices_depuis_inter(vZ, vI, vK, vx, hx)      # (∃i)(i∈I) , (∃i)(i∈K)  {hx}
    eq_X = instancie(N.modus_ponens(                            # (x∈⋂X) ⇔ (∀i)(i∈I⇒x∈X_i)
        ex_I, caracterisation_inter_famille_non_vide(vXX, vI, "z")), vx)
    eq_Y = instancie(N.modus_ponens(                            # (x∈⋂Y) ⇔ (∀i)(i∈K⇒x∈Y_i)
        ex_K, caracterisation_inter_famille_non_vide(vYY, vK, "z")), vx)

    A = pourtout("i", impl(appartient(vi, vI), appartient(vx, _X(vXX, vi))))  # (∀ι)(ι∈I⇒x∈X_ι)
    te = tiers_exclu(A)                                        # A ∨ ¬A

    # ── branche A : x∈⋂X → x∈gauche ──────────────────────────────────────────
    hA = N.assume(A)
    forall_i = _rebind(hA, _inter_binder(vXX, vI, vx))
    xX = N.modus_ponens(forall_i, equivalence_arriere(eq_X))   # x∈⋂X  (témoin : ex_I)
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
    xY = N.modus_ponens(forall_k, equivalence_arriere(eq_Y))   # x∈⋂Y  (témoin : ex_K)
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

    Les liants internes de l'axiome sont « p » et « q » ; les DEUX sites d'usage
    (`_inclusion_directe`, `_indices_depuis_inter`) nomment donc leurs témoins
    var("p") et var("q") — aucun α-renommage n'est nécessaire, ni effectué.
    (Correction 2026-07-26 : la note précédente annonçait un α-renommage vers des
    témoins « i, k » qui n'a jamais existé dans le code.)"""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_PRODUIT)
    return instancie(instancie(instancie(ax, gx), gy), z)


def _membre_inter(fam, idx, z):
    """⊢ (z∈⋂_{ι∈idx} fam_ι) ⇔ ( z∈⋃_{ι∈idx} fam_ι  et  (∀i)(i∈idx ⇒ z∈fam_i) ).

    Instance d'AXIOME_INTER_FAM sous sa forme de SÉLECTION (II.4.1 Déf. 2, migration
    du 2026-07-26).  Le membre droit est une CONJONCTION : l'ÉLIMINATION en prend la
    projection droite (inconditionnelle, `_inter_elim`) ; l'INTRODUCTION réclame en
    plus la projection gauche, donc un témoin d'indice — elle passe désormais par
    `caracterisation_inter_famille_non_vide` et n'utilise plus cette instance brute."""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_INTER_FAM)
    return instancie(instancie(instancie(ax, fam), idx), z)


def _inter_elim(fam, idx, a, z):
    """⊢ (z∈⋂_{ι∈idx} fam_ι) ⇒ (a∈idx ⇒ z∈fam_a)  (élim ∩-famille à TERMES).

    ÉNONCÉ INCHANGÉ par la migration (issue A) : l'élimination reste INCONDITIONNELLE
    (cf. `ensembles_inter_selection_ii4.inter_donne_membres`).  Seule la PREUVE change :
    on projette à DROITE la conjonction de sélection avant d'instancier au témoin a."""
    h = N.assume(appartient(z, E.inter_famille(fam, idx)))
    conj = N.modus_ponens(h, equivalence_avant(_membre_inter(fam, idx, z)))
    at_a = instancie(conjonction_elim_droite(conj), a)         # (a∈idx ⇒ z∈fam_a)
    return N.loi_deduction(appartient(z, E.inter_famille(fam, idx)), at_a)


def _inter_binder(fam, idx, z):
    """Nom du liant du ∀ dans le CORPS de la Déf. 2 : (∀i)((i∈idx) ⇒ z∈fam_i).

    Lu sur `corps_membres_famille` (la brique de la migration) et non plus sur le
    membre droit de l'axiome, devenu une conjonction."""
    return _forall_binder(corps_membres_famille(fam, idx, z))


def _membre_reunion_fam(fam, idx, z):
    """⊢ (z∈⋃_{ι∈idx} fam_ι) ⇔ (∃i)(i∈idx et z∈fam_i)  (instance de AXIOME_REUNION_FAM)."""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_REUNION_FAM)
    return instancie(instancie(instancie(ax, fam), idx), z)


def _indices_depuis_inter(vZ, vI, vK, vx, hx):
    """De ⊢ x ∈ ⋂_{u∈I×K} Z(u) déduire ( ⊢ (∃i)(i∈I) , ⊢ (∃i)(i∈K) ) — témoins GRATUITS.

    Route : ⋂ ⊂ ⋃ (`inter_inclus_reunion`, projection gauche de la sélection) donne
    x ∈ ⋃_{u∈I×K} Z(u), donc (∃u)(u∈I×K et x∈Z(u)) par AXIOME_REUNION_FAM ; sous ce
    témoin, AXIOME_PRODUIT décompose u = (p,q) avec p∈I et q∈K, d'où les deux
    existentiels par S5 ; on décharge par `existe_elimination` (p, q puis u).
    Les hypothèses rendues sont celles de `hx` — rien n'est ajouté à l'énoncé."""
    P = E.produit(vI, vK)
    vu, vp, vq = var("i"), var("p"), var("q")     # « i » = liant d'AXIOME_REUNION_FAM
    x_in_U = N.modus_ponens(hx, instancie(inter_inclus_reunion(vZ, P, "z"), vx))
    ex_u = N.modus_ponens(x_in_U, equivalence_avant(_membre_reunion_fam(vZ, P, vx)))
    body_u = et(appartient(vu, P), appartient(vx, E.valeur_famille(vZ, vu)))
    hbu = N.assume(body_u)
    decomp = N.modus_ponens(conjonction_elim_gauche(hbu),      # (∃p)(∃q)(u=(p,q) et p∈I et q∈K)
                            equivalence_avant(_membre_produit(vI, vK, vu)))
    body_pq = et(et(egal(vu, E.couple(vp, vq)), appartient(vp, vI)), appartient(vq, vK))
    hpq = N.assume(body_pq)
    sorties = []
    for ens, proj, temoin in (
            (vI, conjonction_elim_droite(conjonction_elim_gauche(hpq)), vp),
            (vK, conjonction_elim_droite(hpq), vq)):
        ex0 = N.modus_ponens(proj, N.s5(appartient(vu, ens), temoin, "i"))
        imp = existe_elimination(existe_elimination(
            N.loi_deduction(body_pq, ex0), "q"), "p")          # (∃p)(∃q)body ⇒ (∃i)(i∈ens)
        imp_u = existe_elimination(N.loi_deduction(            # (∃i)body_u ⇒ (∃i)(i∈ens)
            body_u, N.modus_ponens(decomp, imp)), "i")
        sorties.append(N.modus_ponens(ex_u, imp_u))
    return sorties[0], sorties[1]


def _temoin_indice_produit(vI, vK, hI, hK):
    """Sous ⊢(∃i)(i∈I) et ⊢(∃i)(i∈K) : ⊢ (∃i)( i ∈ I×K ) — le témoin d'indice de I×K.

    Témoins canoniques τi(i∈I) et τi(i∈K) (identité-τ, `N.existe_temoin`) ; leur
    couple est dans I×K (`couple_dans_produit_ssi`), d'où l'existentiel par S5.
    C'est la seule brique qui consomme l'hypothèse « ensembles d'indices non vides »."""
    vi = var("i")
    T_I, T_K = tau("i", appartient(vi, vI)), tau("i", appartient(vi, vK))
    i_in = N.modus_ponens(hI, N.existe_temoin(appartient(vi, vI), "i"))
    k_in = N.modus_ponens(hK, N.existe_temoin(appartient(vi, vK), "i"))
    c_in = N.modus_ponens(conjonction_intro(i_in, k_in),       # (τi(i∈I), τi(i∈K)) ∈ I×K
                          equivalence_arriere(couple_dans_produit_ssi(T_I, T_K, vI, vK)))
    return N.modus_ponens(c_in, N.s5(appartient(vi, E.produit(vI, vK)),
                                     E.couple(T_I, T_K), "i"))


def _forall_binder(formule_forall):
    """Nom du liant d'un ∀ encodé ¬(∃x)¬R  →  x."""
    if formule_forall.tag == "non" and formule_forall.sous and formule_forall.sous[0].tag == "exists":
        return formule_forall.sous[0].lieur
    raise ValueError("liant ∀ introuvable")


def _rebind(thm_forall, cible):
    """Alpha-renomme ⊢ (∀src)R en ⊢ (∀cible)(cible|src)R (si src≠cible)."""
    from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import alpha_pour_tout
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
    from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import congruence_terme
    return congruence_terme(a, b, terme_motif, w)


def _reecrit(thm_t_in_a, thm_eq_ab, t, a, b):
    """⊢ t∈a , ⊢ a=b  ⟹  ⊢ t∈b   (réécriture de l'appartenance le long de a=b, S6)."""
    R = appartient(t, var("@rw"))
    equ = N.modus_ponens(thm_eq_ab, N.s6(a, b, "@rw", R))      # (t∈a) ⇔ (t∈b)
    return N.modus_ponens(thm_t_in_a, equivalence_avant(equ))


__all__ = ["cor_distributivite_inter_reunion_deux_familles", "_cible", "_hyp_indices",
           "theorie_cor_distrib", "_membre_gauche", "_membre_droit"]
