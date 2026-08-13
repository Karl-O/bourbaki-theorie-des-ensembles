"""§II.5 — PROPOSITION 10 (E II.37, n°6 « Formules de distributivité »).

ÉNONCÉ (Bourbaki, E II.37, Prop. 10) : « Soit (X_{ι,κ})_{(ι,κ)∈I×K} une famille
d'ensembles d'indices I×K.  Si K ≠ ∅ : ⋂_{κ∈K}(∏_{ι∈I} X_{ι,κ}) = ∏_{ι∈I}(⋂_{κ∈K} X_{ι,κ}). »

CIBLE — égalité PLEINE, K-GÉNÉRALE (⋂ d'une FAMILLE, pas binaire), SANS choix :
    ⊢ ( K≠∅ ∧ (∀κ)(κ∈K ⇒ P_κ=∏_{ι∈I} X_{ι,κ}) ∧ (∀ι)(ι∈I ⇒ Φ_ι=⋂_{κ∈K} X_{ι,κ})
          ∧ (∀ι)(∀κ)(col(κ)_ι = row(ι)_κ) )  ⇒  ( ⋂_{κ∈K} P_κ = ∏_{ι∈I} Φ_ι ).

Généralise la commutation BINAIRE `produit_inter_egal_inter_produits` (∏(X∩Y)=∏X∩∏Y) :
familles-composites P (κ↦∏_ι X_{ι,κ}) et Φ (ι↦⋂_κ X_{ι,κ}) en PARAMÈTRES, identifiées à
leurs valeurs par hypothèses honnêtes — col(κ)=valeur_famille(COL,κ), row(ι)=valeur_famille(ROW,ι),
X_{ι,κ}=col(κ)_ι=row(ι)_κ ; membre gauche=inter_famille(P,K), droit=produit_famille(Φ,I).

Les 4 hyps sont HONNÊTES (déf. des composites + K≠∅), ∉ conclusion, TOUTES déchargées dans
l'implication ⇒ théorème CLOS (0 hyp). Preuve : extensionnalité A1 + double inclusion
d'appartenance, double permutation (∀κ)(∀ι)↔(∀ι)(∀κ). theorie_ensembles() = 22.

K≠∅ EST LOAD-BEARING DANS LES DEUX SENS (et l'énoncé, lui, n'a pas bougé) :
  • sens ⋂P ⊂ ∏Φ — le bloc func∧dom, indépendant de κ, se récupère via un témoin κ₀∈K (S5) ;
    et l'INTRODUCTION de F(ι) dans ⋂_κ X_{ι,κ} réclame le même témoin (voir ci-dessous) ;
  • sens ∏Φ ⊂ ⋂P — l'INTRODUCTION de F dans ⋂_κ P_κ le réclame aussi.  Contre-exemple si on
    l'ôtait : K=∅ et I=∅ donnent ∏_{ι∈∅}Φ_ι = {∅} ∋ ∅ alors que ⋂_{κ∈∅}P_κ = ∅.

MIGRATION « ⋂ = SÉLECTION DANS ⋃ » (cf. `ii_4_intersection_fondation`).  AXIOME_INTER_FAM
caractérise désormais z∈⋂ par la CONJONCTION ( z∈⋃  ∧  (∀i)(i∈I ⇒ z∈X_i) ) — la Déf. 2 du
livre (E II.22), qui EXIGE I≠∅.  Conséquences ici, ÉNONCÉ INCHANGÉ (issue A) :
  • ÉLIMINATION (`_inter_elim`) : projeter à DROITE ; inconditionnelle, route seule modifiée.
  • INTRODUCTION (`_inter_intro`) : fournir en plus la BORNE z∈⋃, d'où un témoin d'indice —
    ici κ₀∈K, DÉJÀ disponible puisque K≠∅ est une hypothèse du théorème.  Rien n'est ajouté.
  • on n'emprunte plus `ensembles_familles.membre_inter_famille` (devenu un B « (∃i)(i∈I) ⇒
    équivalence ») : les deux directions se tirent DIRECTEMENT de l'axiome de sélection, ce
    qui évite de porter un antécédent superflu.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (Terme, var, et, impl, appartient, egal,
                                       pourtout, existe)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    instancie, equivalence_avant, equivalence_arriere, conjonction_intro,
    conjonction_elim_gauche, conjonction_elim_droite,
    antecedent_consequent, composantes_conjonction)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import alpha_pour_tout, existe_elimination
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import symetrie
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_theoremes import extensionnalite_appliquee
from bourbaki.ii_theorie_des_ensembles.ii_5_produit_famille.ii_5_definitions.ensembles_produit_famille import membre_produit_famille
from bourbaki.ii_theorie_des_ensembles.ii_5_produit_famille.ii_5_definitions.ensembles_produit_ecriture import (
    transporter_dans_produit)
from bourbaki.ii_theorie_des_ensembles.ii_5_produit_famille.ii_5_6_7_algebre_produit.ensembles_produit_props2 import _congruence_appartient

def _t(v):
    return v if isinstance(v, Terme) else var(v)


def _col(COL, kappa):
    return E.valeur_famille(_t(COL), _t(kappa))           # col(κ) = COLONNE ι↦X_{ι,κ}

def _row(ROW, iota):
    return E.valeur_famille(_t(ROW), _t(iota))            # row(ι) = LIGNE κ↦X_{ι,κ}

def _Xcol(COL, kappa, iota):
    return E.valeur_famille(_col(COL, kappa), _t(iota))   # X_{ι,κ} vu COLONNE

def _Xrow(ROW, iota, kappa):
    return E.valeur_famille(_row(ROW, iota), _t(kappa))   # X_{ι,κ} vu LIGNE

def _prod_col(COL, kappa, vI):
    return E.produit_famille(_col(COL, kappa), vI)        # ∏_{ι∈I} X_{ι,κ}

def _inter_row(ROW, iota, vK):
    return E.inter_famille(_row(ROW, iota), vK)           # ⋂_{κ∈K} X_{ι,κ}


def _hyp_P(P, COL, vI, vK, kappa="k"):
    """H_P : (∀κ)(κ∈K ⇒ P_κ = ∏_{ι∈I} X_{ι,κ}).  « P est la famille κ↦∏_ι X_{ι,κ}. »"""
    vk = var(kappa)
    return pourtout(kappa, impl(appartient(vk, vK),
                               egal(E.valeur_famille(_t(P), vk), _prod_col(COL, vk, vI))))

def _hyp_Phi(Phi, ROW, vI, vK, iota="i"):
    """H_Φ : (∀ι)(ι∈I ⇒ Φ_ι = ⋂_{κ∈K} X_{ι,κ}).  « Φ est la famille ι↦⋂_κ X_{ι,κ}. »"""
    vi = var(iota)
    return pourtout(iota, impl(appartient(vi, vI),
                              egal(E.valeur_famille(_t(Phi), vi), _inter_row(ROW, vi, vK))))

def _hyp_coh(COL, ROW, iota="i", kappa="k"):
    """H_coh : (∀ι)(∀κ)( col(κ)_ι = row(ι)_κ )  — même double famille X_{ι,κ}."""
    vi, vk = var(iota), var(kappa)
    return pourtout(iota, pourtout(kappa, egal(_Xcol(COL, vk, vi), _Xrow(ROW, vi, vk))))

def _hyp_K_non_vide(vK, kappa="k0"):
    """K ≠ ∅  :=  (∃κ)(κ ∈ K).   (« K non vide » ; liant κ₀ = témoin extrait par S5.)"""
    return existe(kappa, appartient(var(kappa), vK))


def _membre_gauche(P, vK):
    return E.inter_famille(_t(P), vK)                     # ⋂_{κ∈K} P_κ

def _membre_droit(Phi, vI):
    return E.produit_famille(_t(Phi), vI)                 # ∏_{ι∈I} Φ_ι

def _hypotheses(P, Phi, COL, ROW, vI, vK):
    """Conjonction des 4 hypothèses honnêtes (K≠∅ ∧ H_P ∧ H_Φ ∧ H_coh)."""
    return et(et(et(_hyp_K_non_vide(vK), _hyp_P(P, COL, vI, vK)),
                 _hyp_Phi(Phi, ROW, vI, vK)),
              _hyp_coh(COL, ROW))

def _cible(p="P", phi="Phi", col="COL", row="ROW", i="I", k="K"):
    """⊢-cible : ( K≠∅ ∧ H_P ∧ H_Φ ∧ H_coh ) ⇒ ( ⋂_{κ∈K}P_κ = ∏_{ι∈I}Φ_ι )."""
    vI, vK = var(i), var(k)
    return impl(_hypotheses(var(p), var(phi), var(col), var(row), vI, vK),
                egal(_membre_gauche(var(p), vK), _membre_droit(var(phi), vI)))


# ── théorème principal ────────────────────────────────────────────────────────
# @livre Ch.II §5.6 Prop.10 | E II.37 L.40-45 | PDF p.88
def inter_produit_egal_produit_inter(p="P", phi="Phi", col="COL", row="ROW",
                                     i="I", k="K", ff="F"):
    """⊢ ( K≠∅ ∧ (∀κ)(κ∈K⇒P_κ=∏_ι X_{ι,κ}) ∧ (∀ι)(ι∈I⇒Φ_ι=⋂_κ X_{ι,κ}) ∧ H_coh )
         ⇒ ( ⋂_{κ∈K}P_κ = ∏_{ι∈I}Φ_ι ).
       (PROPOSITION 10, E II.37 — commutation intersection/produit, K-générale.)

    Égalité PLEINE, version K-GÉNÉRALE, SANS choix : la double permutation de
    quantificateurs (∀κ)(∀ι) ↔ (∀ι)(∀κ) sur F(ι)∈X_{ι,κ}, bornée à un bloc
    fonctionnel/domaine récupéré via K≠∅.  Clos modulo les hypothèses honnêtes
    {K≠∅, P_κ=∏colonne, Φ_ι=⋂ligne, cohérence colonne/ligne}, TOUTES déchargées
    dans l'implication finale → théorème CLOS (0 hyp), comme le gabarit binaire."""
    vP, vPhi, vCOL, vROW = var(p), var(phi), var(col), var(row)
    vI, vK = var(i), var(k)

    hyp = _hypotheses(vP, vPhi, vCOL, vROW, vI, vK)
    hH = N.assume(hyp)
    h_Knv = conjonction_elim_gauche(conjonction_elim_gauche(conjonction_elim_gauche(hH)))
    h_P = conjonction_elim_droite(conjonction_elim_gauche(conjonction_elim_gauche(hH)))
    h_Phi = conjonction_elim_droite(conjonction_elim_gauche(hH))
    h_coh = conjonction_elim_droite(hH)

    gauche = _membre_gauche(vP, vK)
    droite = _membre_droit(vPhi, vI)

    incl_av = _inclusion_avant(vP, vPhi, vCOL, vROW, vI, vK, h_Knv, h_P, h_Phi, h_coh, ff)
    incl_ar = _inclusion_arriere(vP, vPhi, vCOL, vROW, vI, vK, h_Knv, h_P, h_Phi, h_coh, ff)

    ext = extensionnalite_appliquee(gauche, droite)
    eq = N.modus_ponens(conjonction_intro(incl_av, incl_ar), ext)   # ⋂P = ∏Φ
    res = N.loi_deduction(hyp, eq)
    assert res.conclusion == _cible(p, phi, col, row, i, k), \
        "inter_produit_egal_produit_inter : conclusion ≠ cible"
    return res


# ── sens ⊂ :  ⋂_{κ∈K} P_κ ⊂ ∏_{ι∈I} Φ_ι  (sous les hyps) ──────────────────────
def _inclusion_avant(vP, vPhi, vCOL, vROW, vI, vK, h_Knv, h_P, h_Phi, h_coh,
                     ff="F", iota="i", kappa="k"):
    """⋂_κ P_κ ⊂ ∏_ι Φ_ι.  F∈⋂P → (∀κ)(κ∈K⇒F∈∏_ι X_{·,κ}) ; un κ₀ témoin (K≠∅)
    donne le bloc func∧dom ; à ι fixé (∀κ)(κ∈K⇒F(ι)∈X_{ι,κ}) → F(ι)∈⋂_κ X_{ι,κ}=Φ_ι.

    Post-migration : le témoin κ₀ sert MAINTENANT deux fois — pour le bloc func∧dom
    (comme avant) ET pour la BORNE F(ι)∈⋃_κ X_{ι,κ} qu'exige l'introduction dans ⋂
    (`_inter_intro`).  Il est déjà là (K≠∅ est une hypothèse) : l'énoncé ne bouge pas."""
    vF, vi, vk, vk0 = var(ff), var(iota), var(kappa), var("k0")
    Fi = E.valeur(vF, vi)
    Pk = E.valeur_famille(vP, vk)
    Phi_i = E.valeur_famille(vPhi, vi)
    inter_i = _inter_row(vROW, vi, vK)

    # F ∈ ⋂_κ P_κ  →  (∀κ)(κ∈K ⇒ F∈P_κ)   [ÉLIMINATION : inconditionnelle]
    hF = N.assume(appartient(vF, _membre_gauche(vP, vK)))
    forall_k_inP = _inter_elim(vP, vK, vF, hF)              # (∀κ)(κ∈K⇒F∈P_κ)

    # κ témoin κ₀ de K≠∅ : F∈P_{κ₀} → F∈∏_ι X_{·,κ₀} → bloc func∧dom
    hk0 = N.assume(appartient(vk0, vK))                     # κ₀∈K
    FinPk0 = N.modus_ponens(hk0, instancie(forall_k_inP, vk0))   # F∈P_{κ₀}
    eqPk0 = N.modus_ponens(hk0, instancie(h_P, vk0))
    FinProd0 = _reecrit(FinPk0, eqPk0, vF, E.valeur_famille(vP, vk0), _prod_col(vCOL, vk0, vI))   # F∈∏X_{·,κ₀}

    hi = N.assume(appartient(vi, vI))                          # ι∈I
    hk = N.assume(appartient(vk, vK))                          # κ∈K
    FinPk = N.modus_ponens(hk, instancie(forall_k_inP, vk))    # F∈P_κ
    eqPk = N.modus_ponens(hk, instancie(h_P, vk))              # P_κ=∏_ι X_{·,κ}
    FinProdk = _reecrit(FinPk, eqPk, vF, Pk, _prod_col(vCOL, vk, vI))   # F∈∏_ι X_{·,κ}
    corpsk = N.modus_ponens(FinProdk, equivalence_avant(_membre_produit_terme(_col(vCOL, vk), vI, vF)))
    forall_i_col = conjonction_elim_droite(corpsk)             # (∀ι)(ι∈I⇒F(ι)∈X_{ι,κ})  [colonne]
    Fi_in_Xcol = N.modus_ponens(hi, instancie(forall_i_col, vi))   # F(ι)∈X_{ι,κ}  [colonne]
    eqcoh = instancie(instancie(h_coh, vi), vk)               # col(κ)_ι = row(ι)_κ
    Fi_in_Xrow = _reecrit(Fi_in_Xcol, eqcoh, Fi, _Xcol(vCOL, vk, vi), _Xrow(vROW, vi, vk))  # F(ι)∈X_{ι,κ} [ligne]
    imp_k = N.loi_deduction(appartient(vk, vK), Fi_in_Xrow)   # κ∈K ⇒ F(ι)∈row(ι)_κ
    forall_k_row = N.generalisation(kappa, imp_k)             # (∀κ)(κ∈K⇒F(ι)∈row(ι)_κ)
    # → F(ι) ∈ ⋂_κ X_{ι,κ} = inter_famille(row(ι), K)   [INTRODUCTION : témoin κ₀ requis]
    Fi_in_inter = _inter_intro(_row(vROW, vi), vK, vk0, Fi, hk0, forall_k_row)
    eqPhi = N.modus_ponens(hi, instancie(h_Phi, vi))         # Φ_ι=⋂_κ X_{ι,κ}
    Fi_in_Phi = _reecrit(Fi_in_inter, _sym(eqPhi), Fi, inter_i, Phi_i)   # F(ι)∈Φ_ι
    imp_i = N.loi_deduction(appartient(vi, vI), Fi_in_Phi)   # ι∈I ⇒ F(ι)∈Φ_ι
    forall_i_phi = N.generalisation(iota, imp_i)             # (∀ι)(ι∈I⇒F(ι)∈Φ_ι)

    # F∈∏Φ : TRANSPORT depuis ∏X_{·,κ₀} (le témoin κ₀ porte func ∧ dom ∧ « F graphe »),
    # le conjoint de tête F ⊂ I×⋃Φ_ι étant RECONSTRUIT par le pivot (Φ ≠ colonne κ₀).
    eq_Phi = membre_produit_famille(vPhi.nom, vI.nom, ff)
    forall_i_phi = _rebind(forall_i_phi, _prod_binder(eq_Phi))
    FinPhi = transporter_dans_produit(FinProd0, forall_i_phi, vF, _col(vCOL, vk0),
                                      vPhi, vI, _prod_binder(eq_Phi))
    imp_k0 = N.loi_deduction(appartient(vk0, vK), FinPhi)    # κ₀∈K ⇒ F∈∏Φ
    elim_k0 = existe_elimination(imp_k0, "k0")              # (∃κ₀)(κ₀∈K) ⇒ F∈∏Φ
    FinPhi2 = N.modus_ponens(h_Knv, elim_k0)                # F∈∏Φ  (K≠∅ consommé)

    imp_F = N.loi_deduction(appartient(vF, _membre_gauche(vP, vK)), FinPhi2)  # F∈⋂P⇒F∈∏Φ
    incl_F = N.generalisation(ff, imp_F)
    membre = impl(appartient(vF, _membre_gauche(vP, vK)), appartient(vF, _membre_droit(vPhi, vI)))
    return N.modus_ponens(incl_F, equivalence_avant(alpha_pour_tout(ff, "z", membre)))


# ── sens ⊃ :  ∏_{ι∈I} Φ_ι ⊂ ⋂_{κ∈K} P_κ  (sous les hyps) ──────────────────────
def _inclusion_arriere(vP, vPhi, vCOL, vROW, vI, vK, h_Knv, h_P, h_Phi, h_coh,
                       ff="F", iota="i", kappa="k"):
    """∏_ι Φ_ι ⊂ ⋂_κ P_κ.  F∈∏Φ → func∧dom ∧ (∀ι)(ι∈I⇒F(ι)∈Φ_ι=⋂_κ X_{ι,κ}) ;
    à κ fixé, (∀ι)(ι∈I⇒F(ι)∈X_{ι,κ}) → F∈∏_ι X_{·,κ}=P_κ.

    K≠∅ EST REQUIS ICI (le commentaire « K≠∅ inutile ici » de l'avant-migration était
    un artefact de l'axiome contradictoire) : le pas final (∀κ)(κ∈K⇒F∈P_κ) → F∈⋂_κ P_κ
    est une INTRODUCTION, qui réclame la borne F∈⋃_κ P_κ donc un témoin κ₀∈K.  Sans lui
    l'inclusion est FAUSSE : pour K=∅ et I=∅, ∏_{ι∈∅}Φ_ι = {∅} ∋ ∅ mais ⋂_{κ∈∅}P_κ = ∅.
    K≠∅ étant déjà une hypothèse du théorème, l'ÉNONCÉ ne bouge pas (issue A)."""
    vF, vi, vk, vk0 = var(ff), var(iota), var(kappa), var("k0")
    Fi = E.valeur(vF, vi)
    Pk = E.valeur_famille(vP, vk)
    Phi_i = E.valeur_famille(vPhi, vi)
    inter_i = _inter_row(vROW, vi, vK)

    eq_Phi = membre_produit_famille(vPhi.nom, vI.nom, ff)    # Φ atomique : lemme à NOM
    hF = N.assume(appartient(vF, _membre_droit(vPhi, vI)))    # F∈∏Φ
    corps = N.modus_ponens(hF, equivalence_avant(eq_Phi))
    forall_i_phi = conjonction_elim_droite(corps)            # (∀ι)(ι∈I⇒F(ι)∈Φ_ι)

    hk = N.assume(appartient(vk, vK))                        # κ∈K
    hi = N.assume(appartient(vi, vI))                        # ι∈I
    Fi_in_Phi = N.modus_ponens(hi, instancie(forall_i_phi, vi))   # F(ι)∈Φ_ι
    eqPhi = N.modus_ponens(hi, instancie(h_Phi, vi))         # Φ_ι=⋂_κ X_{ι,κ}
    Fi_in_inter = _reecrit(Fi_in_Phi, eqPhi, Fi, Phi_i, inter_i)   # F(ι)∈⋂_κ X_{ι,κ}=inter(row(ι),K)
    # (F(ι)∈⋂) → (∀κ)(κ∈K⇒F(ι)∈row(ι)_κ)   [ÉLIMINATION : inconditionnelle]
    forall_k_row = _inter_elim(_row(vROW, vi), vK, Fi, Fi_in_inter)
    Fi_in_Xrow = N.modus_ponens(hk, instancie(forall_k_row, vk))   # F(ι)∈row(ι)_κ  [ligne]
    eqcoh = instancie(instancie(h_coh, vi), vk)             # col(κ)_ι = row(ι)_κ
    Fi_in_Xcol = _reecrit(Fi_in_Xrow, _sym(eqcoh), Fi, _Xrow(vROW, vi, vk), _Xcol(vCOL, vk, vi))  # F(ι)∈X_{ι,κ} [col]
    imp_i = N.loi_deduction(appartient(vi, vI), Fi_in_Xcol) # ι∈I ⇒ F(ι)∈col(κ)_ι
    forall_i_col = N.generalisation(iota, imp_i)            # (∀ι)(ι∈I⇒F(ι)∈col(κ)_ι)
    eq_col = _membre_produit_terme(_col(vCOL, vk), vI, vF)
    forall_i_col = _rebind(forall_i_col, _prod_binder(eq_col))
    # TRANSPORT ∏Φ → ∏X_{·,κ} : le conjoint de tête F ⊂ I×⋃X_{ι,κ} est reconstruit.
    FinProdk = transporter_dans_produit(hF, forall_i_col, vF, vPhi,
                                        _col(vCOL, vk), vI, _prod_binder(eq_col))
    eqPk = N.modus_ponens(hk, instancie(h_P, vk))           # P_κ=∏_ι X_{·,κ}
    FinPk = _reecrit(FinProdk, _sym(eqPk), vF, _prod_col(vCOL, vk, vI), Pk)   # F∈P_κ
    imp_k = N.loi_deduction(appartient(vk, vK), FinPk)      # κ∈K ⇒ F∈P_κ
    forall_k = N.generalisation(kappa, imp_k)               # (∀κ)(κ∈K⇒F∈P_κ)
    # F ∈ ⋂_κ P_κ   [INTRODUCTION : borne F∈⋃P, donc témoin κ₀∈K fourni par K≠∅]
    hk0 = N.assume(appartient(vk0, vK))                     # κ₀∈K
    FinInterP = _inter_intro(vP, vK, vk0, vF, hk0, forall_k)
    imp_k0 = N.loi_deduction(appartient(vk0, vK), FinInterP)          # κ₀∈K ⇒ F∈⋂P
    FinInterP = N.modus_ponens(h_Knv, existe_elimination(imp_k0, "k0"))   # K≠∅ consommé
    imp_F = N.loi_deduction(appartient(vF, _membre_droit(vPhi, vI)), FinInterP)
    incl_F = N.generalisation(ff, imp_F)
    membre = impl(appartient(vF, _membre_droit(vPhi, vI)), appartient(vF, _membre_gauche(vP, vK)))
    return N.modus_ponens(incl_F, equivalence_avant(alpha_pour_tout(ff, "z", membre)))


# ── micro-helpers (instances à TERMES) ────────────────────────────────────────

def _membre_produit_terme(fam, idx, ff):
    """⊢ (F∈∏_{ι∈idx} fam_ι) ⇔ (F func ∧ dom F=idx ∧ (∀ι)(ι∈idx⇒F(ι)∈fam_ι))  (TERMES)."""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_PRODUIT_FAM)
    return instancie(instancie(instancie(ax, fam), idx), ff)

def _membre_inter_terme(fam, idx, z):
    """⊢ (z∈⋂_{ι∈idx} fam_ι) ⇔ ( z∈⋃_{ι∈idx} fam_ι ∧ (∀@)(@∈idx⇒z∈fam_@) )  (TERMES).

    Forme de SÉLECTION (Déf. 2, E II.22) : le membre droit est une CONJONCTION depuis
    la migration `ii_4_intersection_fondation`.  Le liant du ∀ est celui de l'axiome
    (« i ») SAUF si `fam`/`z` contiennent déjà « i » libre — subst le rend alors frais
    (« @0 ») ; c'est pourquoi on le LIT (`_inter_binder`) au lieu de le supposer."""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_INTER_FAM)
    return instancie(instancie(instancie(ax, fam), idx), z)

def _membre_reunion_terme(fam, idx, z):
    """⊢ (z∈⋃_{ι∈idx} fam_ι) ⇔ (∃@)(@∈idx et z∈fam_@)  (TERMES ; liant @ lu, cf. supra)."""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_REUNION_FAM)
    return instancie(instancie(instancie(ax, fam), idx), z)

def _forall_binder(formule_forall):
    """Nom du liant d'un ∀ encodé ¬(∃x)¬R  →  x (gère les liants canoniques « @0 »)."""
    if formule_forall.tag == "non" and formule_forall.sous and formule_forall.sous[0].tag == "exists":
        return formule_forall.sous[0].lieur
    raise ValueError("liant ∀ introuvable")

def _existe_binder(formule_existe):
    """Nom du liant d'un ∃ (tag « exists »)  →  x (gère les liants canoniques « @0 »)."""
    if formule_existe.tag == "exists":
        return formule_existe.lieur
    raise ValueError("liant ∃ introuvable")

def _binder_dernier_conjoint(eq_terme):
    """Liant du ∀ formant le DERNIER conjoint du membre droit d'une équivalence."""
    _, corps = antecedent_consequent(equivalence_avant(eq_terme).conclusion)
    return _forall_binder(composantes_conjonction(corps)[-1])

def _inter_binder(eq_terme):
    """Liant du ∀ au membre droit de `_membre_inter_terme` : ( z∈⋃ ∧ (∀b)(b∈idx⇒z∈fam_b) ).

    Post-migration ce membre droit est une CONJONCTION (sélection dans ⋃) et non plus le
    seul (∀b) : le liant se lit sur le DERNIER conjoint, exactement comme pour le produit
    — d'où la brique commune `_binder_dernier_conjoint`."""
    return _binder_dernier_conjoint(eq_terme)

def _prod_binder(eq_terme):
    """Liant du ∀ (dernier conjoint) au membre droit de `_membre_produit_terme`."""
    return _binder_dernier_conjoint(eq_terme)                  # [(func ∧ dom), ∀]

def _inter_elim(fam, idx, z, thm_z_in_inter):
    """⊢ z ∈ ⋂_{ι∈idx} fam_ι  ⟹  ⊢ (∀@)((@∈idx) ⇒ z∈fam_@).   INCONDITIONNEL.

    Projection DROITE de la conjonction de sélection : la direction gratuite, sans
    témoin d'indice — énoncé identique à celui de l'avant-migration, route seule changée."""
    eq = _membre_inter_terme(fam, idx, z)
    return conjonction_elim_droite(N.modus_ponens(thm_z_in_inter, equivalence_avant(eq)))

def _reunion_intro(fam, idx, temoin, z, thm_T_in_idx, thm_z_in_fam_T):
    """⊢ T∈idx , ⊢ z∈fam_T  ⟹  ⊢ z ∈ ⋃_{ι∈idx} fam_ι   (S5, témoin TERME T).

    Version CAPTURE-SÛRE de `ensembles_inter_selection_ii4.reunion_intro_terme`, qui code
    en dur le liant « i » : ici fam = row(ι) et z = F(ι) contiennent ι libre, ce liant
    serait CAPTURÉ.  On le lit donc sur l'instance d'axiome, que subst a rendu frais."""
    eq = _membre_reunion_terme(fam, idx, z)
    ex_f, _ = antecedent_consequent(equivalence_arriere(eq).conclusion)     # (∃@)(…)
    ex = N.modus_ponens(conjonction_intro(thm_T_in_idx, thm_z_in_fam_T),
                        N.s5(ex_f.sous[0], temoin, _existe_binder(ex_f)))
    return N.modus_ponens(ex, equivalence_arriere(eq))

def _inter_intro(fam, idx, temoin, z, thm_T_in_idx, thm_forall):
    """⊢ T∈idx , ⊢ (∀κ)((κ∈idx) ⇒ z∈fam_κ)  ⟹  ⊢ z ∈ ⋂_{ι∈idx} fam_ι.

    LA direction qui change : l'équivalence de la Déf. 2 étant devenue une SÉLECTION dans
    ⋃, l'introduction réclame en plus la BORNE z∈⋃, donc le TÉMOIN d'indice T∈idx que
    Bourbaki exige (E II.22 : « … dont l'ensemble d'indices I n'est pas vide »).  Sans lui
    on peuplerait ⋂_{ι∈∅}, qui vaut ∅.  Le liant de `thm_forall` est α-renommé sur celui
    de l'axiome (`_rebind`), frais dès que fam/z contiennent « i » libre."""
    eq = _membre_inter_terme(fam, idx, z)
    thm_forall = _rebind(thm_forall, _inter_binder(eq))
    z_in_fam_T = N.modus_ponens(thm_T_in_idx, instancie(thm_forall, temoin))   # z ∈ fam_T
    z_in_reunion = _reunion_intro(fam, idx, temoin, z, thm_T_in_idx, z_in_fam_T)
    return N.modus_ponens(conjonction_intro(z_in_reunion, thm_forall),
                          equivalence_arriere(eq))

def _rebind(thm_forall, cible):
    """Alpha-renomme ⊢ (∀src)R  en  ⊢ (∀cible)(cible|src)R  (si src≠cible).

    Le ∀ est encodé ¬(∃src)¬R ; on récupère R = (∃-nié).sous.sous puis alpha_pour_tout."""
    f = thm_forall.conclusion
    src = _forall_binder(f)
    if src == cible:
        return thm_forall
    R = f.sous[0].sous[0].sous[0]                            # (∀src)R = ¬(∃src)¬R → R
    return N.modus_ponens(thm_forall, equivalence_avant(alpha_pour_tout(src, cible, R)))

def _sym(thm_eq):
    """De ⊢ a=b déduire ⊢ b=a."""
    a, b = thm_eq.conclusion.termes
    return N.modus_ponens(thm_eq, symetrie(a, b))

def _reecrit(thm_t_in_a, thm_eq_ab, t, a, b):
    """⊢ t∈a , ⊢ a=b  ⟹  ⊢ t∈b   (réécriture de l'appartenance le long de a=b)."""
    cong = N.modus_ponens(thm_eq_ab, _congruence_appartient(t, a, b))
    return N.modus_ponens(thm_t_in_a, cong)


__all__ = ["inter_produit_egal_produit_inter", "_cible", "_hypotheses",
           "_membre_gauche", "_membre_droit"]
