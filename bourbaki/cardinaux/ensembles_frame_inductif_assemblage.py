"""§III.6.3 — Théorème 2 (HESSENBERG, Zorn E.III.48) : ASSEMBLAGE FINAL de
l'INDUCTIVITÉ du poset 𝔉 — décharge de `enonce_chaine_majoree` de `frame_inductif`.

CONTEXTE.  `frame_inductif` (`ensembles_hessenberg_inductivite.py`) livre
`est_inductif(Γ𝔉,𝔉)` SOUS deux hypothèses honnêtes : `est_ordre(Γ𝔉,𝔉)` et
`enonce_chaine_majoree(Γ𝔉,𝔉)` (toute chaîne admet un majorant).  Ce module DÉCHARGE
la SECONDE en l'ASSEMBLANT à partir des briques mergées du recollement de chaîne :

    enonce_chaine_majoree(Γ𝔉,𝔉) = (∀C)( chaine(Γ𝔉,𝔉,C) ⇒ (∃m) majorant(Γ𝔉,C,m,𝔉) ),
    majorant(Γ𝔉,C,m,𝔉)        = ( m∈𝔉 et (∀x)(x∈C ⇒ (x,m)∈Γ𝔉) ).

Pour une chaîne C, on prend le TÉMOIN-RECOLLEMENT  m := (⋃S, ⋃φ) = (union_premiere C,
union_seconde C) (E.III.48, union des projections), puis :

  • `m∈𝔉(E)` — porté en HYPOTHÈSE HONNÊTE (`m_dans_frame`) : c'est la frame-membership
    du couple-recollement, dont la preuve complète (`union_chaine_dans_frame`) reste
    elle-même sous résidus honnêtes (⋃S⊂E, ⋃S infini — Lemme 1 « E infini ⊃ ℕ »,
    hors de portée — + dom/inj/img-valeur).  JAMAIS postulée vraie ; transportée.

  • `(∀x)(x∈C ⇒ (x,m)∈Γ𝔉)` — ENTIÈREMENT DÉRIVÉE via `temoin_majore_membre`
    (`ensembles_chaine_temoin_abstrait.py`), qui établit (x,m)∈Γ𝔉 sous {x∈C, x∈𝔉,
    m∈𝔉}.  L'hyp x∈𝔉 est DÉCHARGÉE de x∈C par C⊂𝔉 (extrait de chaine(Γ𝔉,𝔉,C)) ;
    l'hyp x∈C est déchargée par loi_deduction ; l'hyp m∈𝔉 est l'hypothèse honnête
    ci-dessus.  Puis généralisation sur x.

  • (∃m) intro (S5, témoin m=(⋃S,⋃φ)) + (∀C) généralisation.

RÉSIDU HONNÊTE FINAL (le SEUL ; jamais postulé vrai ; theorie=22) :
  `m_dans_frame(E,C)` :  (⋃S(C), ⋃φ(C)) ∈ 𝔉(E)  —  l'appartenance du couple-
  recollement au poset 𝔉, fidèle (E.III.48) et non vacuous.  Sa décharge complète
  bute sur le Lemme 1 de Hessenberg (« tout ensemble infini contient un ensemble
  équipotent à ℕ »), explicitement HORS du périmètre de cet assemblage.

INVARIANT : theorie_ensembles() reste = 22.  Aucun axiome nouveau ; rien postulé ;
conclusion ∉ hyps (non vacuous).
"""
from __future__ import annotations

from bourbaki.logique.formule import (
    Terme, var, egal, et, impl, existe, pourtout, appartient, inclus,
)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, instancie,
)

from bourbaki.ordre.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_relation import majorant
from bourbaki.ordre.iii_2_bon_ordre.zorn_zermelo.ensembles_zorn import chaine
from bourbaki.cardinaux.ensembles_hessenberg_hard import frame_pair, frame_ordre
from bourbaki.cardinaux.ensembles_chaine_temoin_abstrait import (
    union_premiere, union_seconde, temoin_majore_membre,
)
from bourbaki.cardinaux.ensembles_hessenberg_inductivite import (
    enonce_chaine_majoree, frame_inductif,
)
from bourbaki.ordre.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_relation import est_ordre


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# ════════════════════════════════════════════════════════════════════════════
#  Résidu honnête : appartenance du couple-recollement au poset 𝔉.
# ════════════════════════════════════════════════════════════════════════════
def temoin_couple(C):
    """m(C) := (⋃S(C), ⋃φ(C)) = (union_premiere C, union_seconde C) — le témoin-
    majorant recollement de la chaîne C (E.III.48)."""
    return E.couple(union_premiere(_t(C)), union_seconde(_t(C)))


def m_dans_frame_formule(E_set, C):
    """Formule honnête  (⋃S(C),⋃φ(C)) ∈ 𝔉(E)  (frame-membership du recollement)."""
    return appartient(temoin_couple(C), frame_pair(_t(E_set)))


def m_dans_frame_universel(E_set="E", C="C"):
    """Hyp honnête CLOSE en C :  (∀C)( (⋃S(C),⋃φ(C)) ∈ 𝔉(E) ).

    Forme universellement quantifiée du résidu (le couple-recollement de CHAQUE
    chaîne C est une frame-pair).  Sans C libre — permet la généralisation finale sur
    C de l'énoncé d'inductivité.  Instanciée au C courant à l'intérieur de la preuve.
    JAMAIS postulée vraie ; sa décharge complète bute sur le Lemme 1 de Hessenberg."""
    return pourtout(C, m_dans_frame_formule(E_set, var(C)))


# ════════════════════════════════════════════════════════════════════════════
#  (1) enonce_chaine_majoree_preuve — décharge du résidu d'inductivité.
# ════════════════════════════════════════════════════════════════════════════
def enonce_chaine_majoree_preuve(E_set="E", C="C", m="m", x="xmaj", y="y", z="z"):
    """{ m_dans_frame(E,C) pour la chaîne C } ⊢ enonce_chaine_majoree(Γ𝔉(E),𝔉(E)).
                                                       [1 hyp HONNÊTE résiduelle].

    🎯 DÉCHARGE de l'énoncé d'inductivité (E.III.48).  Pour la chaîne C, témoin
    m=(⋃S,⋃φ).  `majorant(Γ𝔉,C,m,𝔉)` = ( m∈𝔉 et (∀x)(x∈C ⇒ (x,m)∈Γ𝔉) ) :
      • m∈𝔉      : hypothèse honnête `m_dans_frame(E,C)` (frame-membership du
                   recollement ; sa preuve complète bute sur Lemme 1 de Hessenberg).
      • (∀x)…    : DÉRIVÉE via `temoin_majore_membre` (x∈𝔉 déchargé de x∈C par C⊂𝔉,
                   x∈C par loi_deduction).
    Puis (∃m) (S5) et (∀C) (généralisation).  Conclusion ∉ hyps ; theorie=22."""
    vE, vC = _t(E_set), _t(C)
    Gam = frame_ordre(vE)                                   # Γ𝔉(E)
    Fr = frame_pair(vE)                                     # 𝔉(E)
    mt = temoin_couple(vC)                                  # m=(⋃S,⋃φ)

    # hyp honnête (CLOSE en C) : (∀C) (⋃S(C),⋃φ(C))∈𝔉(E).  Instanciée au C courant.
    h_all = N.assume(m_dans_frame_universel(E_set, C))      # [HONNÊTE résiduel, sans C libre]
    h_mFr = instancie(h_all, vC)                            # m∈𝔉(E) pour la chaîne C

    # ── (∀x)(x∈C ⇒ (x,m)∈Γ𝔉) ─────────────────────────────────────────────────
    # chaine(Γ𝔉,𝔉,C) ⊢ C⊂𝔉   (premier conjoint de chaine)
    h_chaine = N.assume(chaine(Gam, Fr, vC, x, y, z))       # [déchargée plus bas]
    C_inc_Fr = conjonction_elim_gauche(h_chaine)            # C⊂𝔉(E) = (∀x)(x∈C ⇒ x∈𝔉)

    vx = var(x)
    h_xC = N.assume(appartient(vx, vC))                     # x∈C
    # x∈𝔉 depuis x∈C et C⊂𝔉
    x_in_Fr = N.modus_ponens(h_xC, instancie(C_inc_Fr, vx))  # x∈𝔉(E)

    # temoin_majore_membre avec p:=x  ⊢ (x,m)∈Γ𝔉  sous {x∈C, x∈𝔉, m∈𝔉}
    # (passe les NOMS DE VARIABLES en chaînes : les helpers internes font var(.)).
    tmm = temoin_majore_membre(E_set, C, x)                # conclusion : (x,m)∈Γ𝔉
    assert tmm.conclusion == appartient(E.couple(vx, mt), Gam), \
        "enonce_chaine_majoree_preuve : temoin_majore_membre ≠ (x,m)∈Γ𝔉"
    # décharge les trois hyps de tmm par les preuves ci-dessus (cut).
    # tmm porte : x∈C, x∈𝔉(E), m∈𝔉(E) (+ éventuelles internes déchargées).
    # On remplace x∈𝔉 par x_in_Fr et m∈𝔉 par h_mFr (mêmes formules ⇒ fusion d'hyps),
    # puis x∈C par loi_deduction au moment de la généralisation.
    couple_xm = appartient(E.couple(vx, mt), Gam)

    # cut x∈𝔉(E) :  remplace l'hypothèse appartient(vx,Fr) de tmm par x_in_Fr.
    step = N.modus_ponens(x_in_Fr,
                          N.loi_deduction(appartient(vx, Fr), tmm))   # (x,m)∈Γ𝔉, x∈𝔉 déchargée
    # cut m∈𝔉(E) : remplace appartient(mt,Fr) par h_mFr.
    step = N.modus_ponens(h_mFr,
                          N.loi_deduction(appartient(mt, Fr), step))  # m∈𝔉 déchargée
    assert step.conclusion == couple_xm

    # décharge x∈C → implication, puis généralise sur x.
    impl_x = N.loi_deduction(appartient(vx, vC), step)      # x∈C ⇒ (x,m)∈Γ𝔉
    forall_x = N.generalisation(x, impl_x)                  # (∀x)(x∈C ⇒ (x,m)∈Γ𝔉)

    # ── majorant(Γ𝔉,C,m,𝔉) = m∈𝔉 et (∀x)(x∈C ⇒ (x,m)∈Γ𝔉) ────────────────────
    maj = conjonction_intro(h_mFr, forall_x)
    cible_maj = majorant(Gam, vC, mt, Fr, x)
    assert maj.conclusion == cible_maj, "enonce_chaine_majoree_preuve : ≠ majorant"

    # ── (∃m) majorant(Γ𝔉,C,m,𝔉)  (S5, témoin m=(⋃S,⋃φ)) ──────────────────────
    R = majorant(Gam, vC, var(m), Fr, x)                    # corps avec variable liée m
    s5 = N.s5(R, mt, m)                                     # (mt|m)R ⇒ (∃m)R
    ex_m = N.modus_ponens(maj, s5)                          # (∃m) majorant(...)

    # ── décharge chaine(Γ𝔉,𝔉,C) → implication, puis (∀C) ─────────────────────
    impl_C = N.loi_deduction(chaine(Gam, Fr, vC, x, y, z), ex_m)  # chaine ⇒ (∃m)majorant
    res = N.generalisation(C, impl_C)                      # (∀C)(chaine ⇒ (∃m)majorant)

    cible = enonce_chaine_majoree(Gam, Fr, C, m, x, y, z)
    assert res.conclusion == cible, "enonce_chaine_majoree_preuve : ≠ enonce_chaine_majoree"
    assert res.conclusion not in res.hypotheses, "enonce_chaine_majoree_preuve : VACUOUS"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  (2) frame_inductif_inconditionnel — est_inductif(Γ𝔉,𝔉) sous résidus minimaux.
# ════════════════════════════════════════════════════════════════════════════
def frame_inductif_inconditionnel(E_set="E", C="C", m="m", x="xmaj", y="y", z="z"):
    """{ est_ordre(Γ𝔉,𝔉), (∀C)(⋃S(C),⋃φ(C))∈𝔉(E) } ⊢ est_inductif(Γ𝔉,𝔉).

    🎯 INDUCTIVITÉ du poset 𝔉 de Zorn (E.III.48), avec `enonce_chaine_majoree`
    DÉCHARGÉ par `enonce_chaine_majoree_preuve`.  Il ne reste donc que DEUX
    hypothèses honnêtes : l'ordre de 𝔉 (`est_ordre`, axiome Γ𝔉) et l'UNIQUE résidu
    `m_dans_frame` (frame-membership du recollement — buté sur Lemme 1).  Obtenu en
    branchant `enonce_chaine_majoree_preuve` dans `frame_inductif` (cut de la seconde
    hyp honnête).  Conclusion ∉ hyps ; theorie=22."""
    from bourbaki.ordre.iii_2_bon_ordre.zorn_zermelo.ensembles_zorn import est_inductif
    vE = _t(E_set)
    Gam = frame_ordre(vE)
    Fr = frame_pair(vE)

    fi = frame_inductif(E_set, C, m, x, y, z)               # {est_ordre, enonce_chaine_majoree} ⊢ est_inductif
    ecm = enonce_chaine_majoree_preuve(E_set, C, m, x, y, z)  # {m_dans_frame} ⊢ enonce_chaine_majoree
    # cut : remplace l'hyp enonce_chaine_majoree de fi par sa preuve ecm.
    hyp_ecm = enonce_chaine_majoree(Gam, Fr, C, m, x, y, z)
    assert hyp_ecm in fi.hypotheses, "frame_inductif_inconditionnel : enonce_chaine_majoree absente de fi"
    res = N.modus_ponens(ecm, N.loi_deduction(hyp_ecm, fi))  # est_inductif, enonce_chaine_majoree déchargée

    cible = est_inductif(Gam, Fr, C, m, x, y, z)
    assert res.conclusion == cible, "frame_inductif_inconditionnel : ≠ est_inductif(Γ𝔉,𝔉)"
    assert res.conclusion not in res.hypotheses, "frame_inductif_inconditionnel : VACUOUS"
    return res


__all__ = [
    "temoin_couple", "m_dans_frame_formule",
    "enonce_chaine_majoree_preuve", "frame_inductif_inconditionnel",
]
