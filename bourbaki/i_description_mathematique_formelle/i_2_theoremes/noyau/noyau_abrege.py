"""Noyau ABRÉGÉ — règles LCF sur `Formule` (chemin Bourbaki, sans gonflement τ).

Mêmes primitives que `noyau.py`, mais sur l'arbre abrégé `formule.Formule` :
∀/∃ sont des lieurs primitifs, ⇒/et/⇔ des nœuds. Avantage : le modus ponens est
TRIVIAL (décomposer un nœud `impl`), plus de parsing d'assemblage.

SOUNDNESS : chaque règle correspond, via `formule.developper` (→ assemblage-τ),
à une règle du noyau-τ déjà vérifiée ; la substitution abrégée `subst_f`
correspond à `(T|x)` justifiée par les critères CS (CS1–CS5, vérifiés). La
fondation τ (chap. I) reste la sémantique ; ce noyau est la pratique fidèle.

Un `Theoreme` (séquent Γ⊢B sur des Formule) n'est créable que par ces règles
(clé privée `_CLE`).
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (Formule, ou, non, impl, equiv, egal, pourtout, existe, tau,
                     subst_f, libres_f, var, developper_t)

_CLE = object()


# @livre Ch.I §2.2 Def.- | E I.22 L.26-26 | PDF p.22  (« est un théorème » — séquent Γ⊢B au niveau abrégé, miroir de i_2_2_demonstration)
class Theoreme:
    __slots__ = ("hypotheses", "conclusion", "justification")

    def __init__(self, hypotheses, conclusion, justification, cle):
        if cle is not _CLE:
            raise PermissionError("Theoreme créable seulement par le noyau abrégé.")
        object.__setattr__(self, "hypotheses", frozenset(hypotheses))
        object.__setattr__(self, "conclusion", conclusion)
        object.__setattr__(self, "justification", justification)

    def __setattr__(self, *_):
        raise AttributeError("Theoreme immuable")

    @property
    def est_clos(self) -> bool:
        return not self.hypotheses

    def __eq__(self, o):
        return (isinstance(o, Theoreme) and self.hypotheses == o.hypotheses
                and self.conclusion == o.conclusion)

    def __hash__(self):
        return hash((self.hypotheses, self.conclusion))

    def __repr__(self):
        from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import afficher_f
        base = afficher_f(self.conclusion)
        if self.est_clos:
            return f"⊢ {base}   [{self.justification}]"
        return f"{len(self.hypotheses)} hyp ⊢ {base}   [{self.justification}]"


# @livre Ch.I §2.1 Def.- | E I.21 L.28-35 | PDF p.21  (théorie : signes, axiomes explicites — version abrégée, miroir de noyau.py)
class Theorie:
    __slots__ = ("nom", "axiomes")

    def __init__(self, nom, axiomes=None):
        self.nom = nom
        self.axiomes = list(axiomes) if axiomes else []

    def ajouter_axiome(self, f: Formule):
        if not isinstance(f, Formule):
            raise ValueError("un axiome doit être une Formule")
        self.axiomes.append(f)


# ── Règles primitives ─────────────────────────────────────────────────────────
def _t(hyps, concl, j):
    return Theoreme(hyps, concl, j, _CLE)


def assume(f: Formule) -> Theoreme:
    return _t(frozenset({f}), f, "hypothèse")


# @livre Ch.I §3.1 Sch.1 | E I.25 L.6-6 | PDF p.25
def s1(r): return _t(frozenset(), impl(ou(r, r), r), "S1")
# @livre Ch.I §3.1 Sch.2 | E I.25 L.7-7 | PDF p.25
def s2(r, s): return _t(frozenset(), impl(r, ou(r, s)), "S2")
# @livre Ch.I §3.1 Sch.3 | E I.25 L.8-9 | PDF p.25
def s3(r, s): return _t(frozenset(), impl(ou(r, s), ou(s, r)), "S3")
# @livre Ch.I §3.1 Sch.4 | E I.25 L.10-12 | PDF p.25
def s4(r, s, t): return _t(frozenset(), impl(impl(r, s), impl(ou(t, r), ou(t, s))), "S4")


# @livre Ch.I §4.2 Sch.5 | E I.33 L.10-11 | PDF p.33
def s5(r, t, x):
    """⊢ (T|x)R ⇒ (∃x)R."""
    return _t(frozenset(), impl(subst_f(t, x, r), existe(x, r)), "S5")


# @livre Ch.I §4.1 Def.- | E I.32 L.1-6 | PDF p.32  ((∃x)R EST (τx(R)|x)R au niveau τ — l'identité définitionnelle que ce transport rend au nœud ∃ abrégé)
def existe_temoin(r, x):
    """⊢ (∃x)R ⇒ (τx(R)|x)R.   Réciproque de S5 pour le témoin canonique T=τx(R).

    Primitive JUSTIFIÉE par l'IDENTITÉ-τ : au niveau τ, (∃x)R EST littéralement
    (τx(R)|x)R (def. E.I.32) — `developper_f` les envoie sur le MÊME assemblage —,
    donc cette implication s'y développe en F⇒F (théorème). Même statut que S5 et
    la réflexivité : transport fidèle d'une vérité τ que le nœud ∃ abrégé masque."""
    return _t(frozenset(), impl(existe(x, r), subst_f(tau(x, r), x, r)), "témoin-∃(déf-τ)")


# @livre Ch.I §5.1 Sch.6 | E I.38 L.20-21 | PDF p.38
def s6(t, u, x, r):
    """⊢ (T=U) ⇒ ((T|x)R ⇔ (U|x)R)."""
    return _t(frozenset(), impl(egal(t, u), equiv(subst_f(t, x, r), subst_f(u, x, r))), "S6")


# @livre Ch.I §5.1 Sch.7 | E I.38 L.22-24 | PDF p.38
def s7(r, s, x):
    """⊢ (∀x)(R⇔S) ⇒ (τx(R) = τx(S))."""
    return _t(frozenset(), impl(pourtout(x, equiv(r, s)), egal(tau(x, r), tau(x, s))), "S7")


# @livre Ch.I §5.2 Th.1 | E I.39 L.22-28 | PDF p.39  (Théorème 1, x = x — transporté du niveau τ où il est démontré, cf. i_5_2_tactiques_egalite)
def reflexivite(t) -> Theoreme:
    """⊢ T = T.  Primitive JUSTIFIÉE par le Théorème 1 (E.I.39), démontré et
    vérifié au niveau τ (test_reflexivite). Au niveau abrégé, ∃ est un nœud
    primitif (≠ τ-substitution), donc on transporte ce théorème τ comme primitive."""
    return _t(frozenset(), egal(t, t), "réflexivité(Th1)")


# @livre Ch.I §1.2 Crit.3 | E I.17 L.14-15 | PDF p.17  (CS3 : τx(A) = τx'((x'|x)A) — l'identité d'assemblages qui fonde ce renommage, vérifiée à chaque appel)
def alpha_tau(r, x, y) -> Theoreme:
    """⊢ τx(R) = τy((y|x)R)   (α-renommage du liant d'un τ-terme).

    Primitive JUSTIFIÉE — et VÉRIFIÉE à chaque appel — par l'identité d'assemblages
    CS1 (renommage des lettres liées, E.I.1.2, déjà certifiée dans criteres_CS) :
    les deux τ-termes se DÉVELOPPENT sur le MÊME assemblage-τ (les lettres liées
    deviennent des indices de De Bruijn), donc l'égalité s'y développe en T=T
    (réflexivité, Théorème 1).  Même statut que `reflexivite`/`existe_temoin` :
    transport fidèle d'une vérité-τ que le nœud τ abrégé masque par un nom de liant.
    GARDE-FOU : on REFUSE si le développement diffère (renommage capturant ou y
    libre dans R), donc cette règle ne peut jamais fabriquer une fausse égalité."""
    g = tau(x, r)
    d = tau(y, subst_f(var(y), x, r))
    if developper_t(g) != developper_t(d):
        raise ValueError("alpha_tau : renommage non valide (développements distincts)")
    return _t(frozenset(), egal(g, d), "α-τ(CS1)")


# @livre Ch.I §2.1 Def.- | E I.22 L.1-14 | PDF p.22  (axiomes explicites — miroir abrégé de noyau.axiome)
def axiome(theorie: Theorie, f: Formule) -> Theoreme:
    if not any(f == ax for ax in theorie.axiomes):
        raise ValueError("cette formule n'est pas un axiome explicite")
    return _t(frozenset(), f, f"axiome[{theorie.nom}]")


# @livre Ch.I §2.2 Crit.1 | E I.23 L.10-17 | PDF p.23  (C1 syllogisme : énoncé L.10-11, démo L.12-17)
def modus_ponens(thm_r: Theoreme, thm_imp: Theoreme) -> Theoreme:
    """C1 — Γ⊢R, Δ⊢(R⇒S) ⟹ Γ∪Δ⊢S.  (décomposition triviale du nœud impl.)"""
    i = thm_imp.conclusion                       # A⇒B  est  ¬A ∨ B
    if not (i.tag == "ou" and i.sous[0].tag == "non"):
        raise ValueError("la majeure n'est pas une implication (¬R ∨ S)")
    r, s = i.sous[0].sous[0], i.sous[1]
    if r != thm_r.conclusion:
        raise ValueError("modus ponens : mineure ≠ antécédent")
    return _t(thm_r.hypotheses | thm_imp.hypotheses, s, "MP(C1)")


# @livre Ch.I §3.3 Crit.14 | E I.27 L.4-5 | PDF p.27  (C14, critère de la déduction — l'étiquette de justification historique reste C6)
def loi_deduction(a: Formule, thm: Theoreme) -> Theoreme:
    """C14 (critère de la déduction, E I.27) — Γ⊢B ⟹ (Γ\\{A})⊢(A⇒B).  (primitive de confiance.)"""
    return _t(thm.hypotheses - {a}, impl(a, thm.conclusion), "C6(déduction)")


# @livre Ch.I §4.1 Crit.27 | E I.32 L.37-39 | PDF p.32  (C27 : énoncé L.37-38, démo L.39 via C3)
def generalisation(x: str, thm: Theoreme) -> Theoreme:
    """C27 — Γ⊢R (x non libre dans Γ) ⟹ Γ⊢(∀x)R.  (primitive de confiance.)"""
    for h in thm.hypotheses:
        if x in libres_f(h):
            raise ValueError(f"généralisation : {x!r} libre dans une hypothèse")
    return _t(thm.hypotheses, pourtout(x, thm.conclusion), "C27(généralisation)")


__all__ = ["Theoreme", "Theorie", "assume", "s1", "s2", "s3", "s4", "s5", "existe_temoin", "s6", "s7",
           "reflexivite", "axiome", "modus_ponens", "loi_deduction", "generalisation"]
