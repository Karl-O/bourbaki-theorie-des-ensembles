"""§III.7.4 — conditions (i)-(iv) et Théorème 1 : limite projective non vide.

────────────────────────────────────────────────────────────────────────────────
Page E III.59 — la DERNIÈRE page du livre non couverte par les manifestes.
On formalise ici ses notions (les conditions imposées aux 𝔖_α et au système
projectif) et on ÉNONCE le Théorème 1 ; les preuves a)/b) restent REPORTÉES
(elles reposent sur la propriété d'intersection finie, cf. REPORTES de
ensembles_limites_props2) — mais les énoncés sont désormais des formules du
projet, vérifiables et citables.

  (i)   `stable_par_intersections(𝔖, i)` : toute intersection d'ensembles de
        𝔖_α appartient à 𝔖_α  (d'où E_α ∈ 𝔖_α, intersection de la famille vide) ;
  (ii)  `propriete_intersection_finie(𝔖, …)` : si toute intersection finie
        d'une sous-famille 𝔉 ⊂ 𝔖_α est non vide, alors ⋂𝔉 est non vide ;
  (ii') `filtrant_decroissant_non_vide(…)` : forme équivalente (sous (i)) pour
        les familles filtrantes décroissantes ;
  (iii) `condition_iii(…)` : f_αβ⁻¹(x_α) ∈ 𝔖_β pour α≤β, x_α∈E_α ;
  (iv)  `condition_iv(…)`  : f_αβ⟨M_β⟩ ∈ 𝔖_α pour α≤β, M_β∈𝔖_β.

  `cible_th1_a` : f_α⟨E⟩ = ⋂_{β≥α} f_αβ⟨E_β⟩                          (19)
  `cible_th1_b` : (∀α)(E_α ≠ ∅) ⇒ E ≠ ∅.
INVARIANT : theorie_ensembles()=22 ; rien postulé (aucun Theoreme ici : ce
module ne contient que des ÉNONCÉS — les preuves sont reportées, honnêtement).
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, et, non, impl, equiv, appartient, inclus, existe, pourtout,
)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites import (
    ensembles_limites as L, ensembles_limites_canoniques as C,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (
    est_fini,
)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def _S(Sfam, a):
    """𝔖_α — l'ensemble de parties attaché à l'indice α."""
    return E.valeur_famille(_t(Sfam), _t(a))


def _non_vide(t):
    """t ≠ ∅  (écrit « (∃u)(u ∈ t) », forme positive utilisable)."""
    return existe("uv", appartient(var("uv"), _t(t)))


# @livre Ch.III §7.4 Def.- | E III.59 L.14-18 | PDF p.162  (condition (i) : 𝔖_α est stable par intersections quelconques ; en particulier E_α ∈ 𝔖_α, intersection de la famille vide)
def stable_par_intersections(Sfam, i, a="ai", m="Mi", j="Ji"):
    """(∀a)(∀J)(∀M)( (a∈I et (∀j)(j∈J ⇒ M_j ∈ 𝔖_a)) ⇒ ⋂_{j∈J} M_j ∈ 𝔖_a )."""
    vS, vi = _t(Sfam), _t(i)
    va, vM, vJ, vj = var(a), var(m), var(j), var("jw")
    fam_dans = pourtout("jw", impl(appartient(vj, vJ),
                                   appartient(E.valeur_famille(vM, vj), _S(vS, va))))
    return pourtout(a, pourtout(j, pourtout(m, impl(
        et(appartient(va, vi), fam_dans),
        appartient(E.inter_famille(vM, vJ), _S(vS, va))))))


# @livre Ch.III §7.4 Def.- | E III.59 L.19-24 | PDF p.162  (condition (ii) : propriété d'intersection finie — si toute intersection finie de 𝔉 est non vide, ⋂𝔉 l'est)
def propriete_intersection_finie(Sfam, i, a="ai", ff="Fi", j="Ji"):
    """(∀a)(∀J)(∀F)( (a∈I et F famille ⊂ 𝔖_a et toute intersection FINIE non vide)
        ⇒ ⋂_{j∈J} F_j ≠ ∅ ).

    « toute intersection FINIE non vide » est écrit explicitement : pour toute
    partie K ⊂ J finie et non vide, ⋂_{j∈K} F_j ≠ ∅ — le prédicat de finitude
    est `est_fini` (§III.4.1), le seul du projet, donc l'énoncé est fidèle et
    autonome (aucune hypothèse fantôme)."""
    vS, vi = _t(Sfam), _t(i)
    va, vF, vJ, vj, vK = var(a), var(ff), var(j), var("jw"), var("Kw")
    fam_dans = pourtout("jw", impl(appartient(vj, vJ),
                                   appartient(E.valeur_famille(vF, vj), _S(vS, va))))
    # « toute intersection FINIE d'ensembles de 𝔉 est non vide » : pour toute
    # partie K ⊂ J finie et non vide, ⋂_{j∈K} F_j ≠ ∅   (est_fini, §III.4.1)
    inter_finies = pourtout("Kw", impl(
        et(et(inclus(vK, vJ), est_fini(vK)), _non_vide(vK)),
        _non_vide(E.inter_famille(vF, vK))))
    return pourtout(a, pourtout(j, pourtout(ff, impl(
        et(et(appartient(va, vi), fam_dans), inter_finies),
        _non_vide(E.inter_famille(vF, vJ))))))


# @livre Ch.III §7.4 Def.- | E III.59 L.25-30 | PDF p.162  (condition (ii') : forme filtrante décroissante, équivalente à (ii) sous (i))
def filtrant_decroissant_non_vide(Sfam, i, a="ai", gg="Gi", j="Ji"):
    """(∀a)(∀J)(∀G)( (a∈I et G ⊂ 𝔖_a filtrante décroissante à éléments non vides)
        ⇒ ⋂_{j∈J} G_j ≠ ∅ )."""
    vS, vi = _t(Sfam), _t(i)
    va, vG, vJ, vj = var(a), var(gg), var(j), var("jw")
    dans_et_non_vide = pourtout("jw", impl(appartient(vj, vJ), et(
        appartient(E.valeur_famille(vG, vj), _S(vS, va)),
        _non_vide(E.valeur_famille(vG, vj)))))
    return pourtout(a, pourtout(j, pourtout(gg, impl(
        et(appartient(va, vi), dans_et_non_vide),
        _non_vide(E.inter_famille(vG, vJ))))))


# @livre Ch.III §7.4 Th.1 | E III.59 L.34-37 | PDF p.162  (condition (iii) du Théorème 1 : les fibres des transitions sont dans 𝔖_β)
def condition_iii(Efam, f, Sfam, i, leq=None, a="ai", b="bi", x="xi"):
    """(∀a)(∀b)(∀x)( (a∈I et b∈I et a≤b et x∈E_a) ⇒ f_ab⁻¹⟨{x}⟩ ∈ 𝔖_b )."""
    if leq is None:
        leq = C._gleq()
    vE, vf, vS, vi = _t(Efam), _t(f), _t(Sfam), _t(i)
    va, vb, vx = var(a), var(b), var(x)
    fab = L.appl_proj(vf, va, vb)
    return pourtout(a, pourtout(b, pourtout(x, impl(
        et(et(et(appartient(va, vi), appartient(vb, vi)), leq(va, vb)),
           appartient(vx, E.valeur_famille(vE, va))),
        appartient(E.image(E.reciproque(fab), E.singleton(vx)), _S(vS, vb))))))


# @livre Ch.III §7.4 Th.1 | E III.59 L.38-40 | PDF p.162  (condition (iv) du Théorème 1 : les images directes des 𝔖_β sont dans 𝔖_α)
def condition_iv(f, Sfam, i, leq=None, a="ai", b="bi", m="Mi"):
    """(∀a)(∀b)(∀M)( (a∈I et b∈I et a≤b et M∈𝔖_b) ⇒ f_ab⟨M⟩ ∈ 𝔖_a )."""
    if leq is None:
        leq = C._gleq()
    vf, vS, vi = _t(f), _t(Sfam), _t(i)
    va, vb, vM = var(a), var(b), var(m)
    fab = L.appl_proj(vf, va, vb)
    return pourtout(a, pourtout(b, pourtout(m, impl(
        et(et(et(appartient(va, vi), appartient(vb, vi)), leq(va, vb)),
           appartient(vM, _S(vS, vb))),
        appartient(E.image(fab, vM), _S(vS, va))))))


# @livre Ch.III §7.4 Th.1 | E III.59 L.41-45 | PDF p.162  (Théorème 1 a) : relation (19), f_α⟨E⟩ = ⋂_{β≥α} f_αβ⟨E_β⟩ — ÉNONCÉ, preuve REPORTÉE)
def cible_th1_a(Efam, f, i, leq=None, gleq=None, a="ai", b="bi"):
    """f_a⟨E⟩ = ⋂_{β≥a} f_ab⟨E_b⟩   (relation (19) ; ÉNONCÉ seul)."""
    if leq is None:
        leq = C._gleq()
    vE, vf, vi, va, vb = _t(Efam), _t(f), _t(i), var(a), var(b)
    lim = L.lim_proj(vE, vf)                               # E = lim← E_β
    gauche = E.image(C.f_canon_proj(vE, vf, va), lim)      # f_α⟨E⟩
    # famille β ↦ f_αβ⟨E_β⟩, indexée par la section {β∈I : α≤β}
    images = E.graphe_terme(vi, E.image(L.appl_proj(vf, va, vb),
                                        E.valeur_famille(vE, vb)), b)
    majorants = E.graphe_terme(vi, vb, b)                  # support {β∈I}
    return egal(gauche, E.inter_famille(images, E.dom(majorants)))


# @livre Ch.III §7.4 Th.1 | E III.59 L.46-48 | PDF p.162  (Théorème 1 b) : si tous les E_α sont non vides, E l'est — ÉNONCÉ, preuve REPORTÉE)
def cible_th1_b(Efam, f, i, a="ai"):
    """(∀a)( a∈I ⇒ E_a ≠ ∅ ) ⇒ E ≠ ∅.                        (ÉNONCÉ seul)."""
    vE, vf, vi, va = _t(Efam), _t(f), _t(i), var(a)
    lim = L.lim_proj(vE, vf)
    hyp = pourtout(a, impl(appartient(va, vi),
                           _non_vide(E.valeur_famille(vE, va))))
    return impl(hyp, _non_vide(lim))


REPORTES = [
    "Théorème 1 §III.7.4 a) et b) — ÉNONCÉS ci-dessus (cible_th1_a / cible_th1_b), "
    "preuves REPORTÉES : elles reposent sur la propriété d'intersection finie (ii) "
    "et sur un argument de récurrence/cofinalité dénombrable (Prop. 5).",
    "Équivalence (ii) ⇔ (ii') sous (i) — énoncée par Bourbaki (« il est clair »), "
    "non démontrée ici (exige le prédicat de finitude de §III.4 sur les familles).",
]

__all__ = ["stable_par_intersections", "propriete_intersection_finie",
           "filtrant_decroissant_non_vide", "condition_iii", "condition_iv",
           "cible_th1_a", "cible_th1_b", "REPORTES"]
