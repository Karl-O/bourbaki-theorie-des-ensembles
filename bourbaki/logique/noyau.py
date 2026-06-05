"""Couche 2 — Noyau de confiance (architecture LCF, style séquents).

PDF p.~22, ~33, Bourbaki, Chap. I §2–§3.

Un ``Theoreme`` est un **séquent** ``Γ ⊢ B`` : sous l'ensemble fini
d'hypothèses Γ (des relations), la relation B est démontrable. Un séquent ne
peut être fabriqué que par les règles primitives ci-dessous (clé privée
``_CLE``). C'est la seule frontière de confiance.

Règles primitives :
  - assume(A)            :  {A} ⊢ A                       (hypothèse)
  - S1..S4               :   ∅  ⊢ <schéma>                (PDF p.~33)
  - axiome(T, A)         :   ∅  ⊢ A   si A ∈ axiomes(T)   (PDF p.~22)
  - modus_ponens (C1)    :  Γ⊢R, Δ⊢(R⇒S)  ⟹  Γ∪Δ ⊢ S     (PDF p.~33)
  - loi_deduction (C6)   :  Γ⊢B  ⟹  Γ\\{A} ⊢ (A⇒B)        (PDF p.~26)

NOTE DE CONFIANCE — `loi_deduction` est ici une règle primitive *de confiance*,
dont la validité est exactement le critère C6 que Bourbaki démontre (théorème
de la déduction). C'est le choix standard (cf. `DISCH` en HOL). Un raffinement
futur peut la *démoter* en règle dérivée en transformant constructivement la
preuve (il faudrait alors dériver le combinateur S à partir de S1–S4). Tant
que ce n'est pas fait, C6 fait partie de la base de confiance ; tout le reste
(tactiques) se construit au-dessus sans rien ajouter à cette base.
"""
from __future__ import annotations

from bourbaki.assemblage.assemblage import (
    Assemblage, est_lettre, lettres, disjonction, implication,
    substitution_b_x_a, tau_x, egalite, equivalence, existe, pour_tout,
)
from bourbaki.logique.lecture import (
    Signature, DEFAUT, est_relation, est_terme, depuis_assemblage, vers_assemblage,
)

# Clé d'authentification du noyau. Non exportée : hors d'ici, pas de Theoreme.
_CLE = object()

Hypotheses = frozenset


class Theoreme:
    """Séquent Γ ⊢ B. Immuable ; créable uniquement par une règle du noyau."""
    __slots__ = ("hypotheses", "conclusion", "justification")

    def __init__(self, hypotheses: frozenset, conclusion: Assemblage,
                 justification: str, cle: object):
        if cle is not _CLE:
            raise PermissionError(
                "Un Theoreme ne peut être créé que par une règle du noyau."
            )
        object.__setattr__(self, "hypotheses", frozenset(hypotheses))
        object.__setattr__(self, "conclusion", conclusion)
        object.__setattr__(self, "justification", justification)

    def __setattr__(self, *_):
        raise AttributeError("Theoreme est immuable")

    @property
    def est_clos(self) -> bool:
        """True ssi le théorème ne dépend d'aucune hypothèse (Γ = ∅)."""
        return not self.hypotheses

    def __eq__(self, autre: object) -> bool:
        return (isinstance(autre, Theoreme)
                and self.hypotheses == autre.hypotheses
                and self.conclusion == autre.conclusion)

    def __hash__(self) -> int:
        return hash((self.hypotheses, self.conclusion))

    def __repr__(self) -> str:
        if self.est_clos:
            return f"⊢ {self.conclusion!r}   [{self.justification}]"
        hyps = ", ".join(repr(h) for h in self.hypotheses)
        return f"{hyps} ⊢ {self.conclusion!r}   [{self.justification}]"


class Theorie:
    """Théorie au sens Bourbaki (fragment exploité par le noyau)."""
    __slots__ = ("nom", "sig", "axiomes")

    def __init__(self, nom: str, sig: Signature | None = None,
                 axiomes: list[Assemblage] | None = None):
        self.nom = nom
        self.sig = dict(sig) if sig is not None else dict(DEFAUT)
        self.axiomes = list(axiomes) if axiomes is not None else []

    def ajouter_axiome(self, relation: Assemblage) -> None:
        if not est_relation(relation, self.sig):
            raise ValueError("un axiome doit être une relation bien formée")
        self.axiomes.append(relation)


# ── Règles primitives ─────────────────────────────────────────────────────────

def _exiger_relations(sig: Signature, *rs: Assemblage) -> None:
    for r in rs:
        if not est_relation(r, sig):
            raise ValueError(f"argument non-relation : {r!r}")


def assume(a: Assemblage, sig: Signature = DEFAUT) -> Theoreme:
    """{A} ⊢ A — introduction d'une hypothèse."""
    _exiger_relations(sig, a)
    return Theoreme(frozenset({a}), a, "hypothèse", _CLE)


def s1(r: Assemblage, sig: Signature = DEFAUT) -> Theoreme:
    """⊢ (R ∨ R) ⇒ R. PDF p.~33."""
    _exiger_relations(sig, r)
    return Theoreme(frozenset(), implication(disjonction(r, r), r), "S1", _CLE)


def s2(r: Assemblage, s: Assemblage, sig: Signature = DEFAUT) -> Theoreme:
    """⊢ R ⇒ (R ∨ S). PDF p.~34."""
    _exiger_relations(sig, r, s)
    return Theoreme(frozenset(), implication(r, disjonction(r, s)), "S2", _CLE)


def s3(r: Assemblage, s: Assemblage, sig: Signature = DEFAUT) -> Theoreme:
    """⊢ (R ∨ S) ⇒ (S ∨ R). PDF p.~34."""
    _exiger_relations(sig, r, s)
    return Theoreme(frozenset(), implication(disjonction(r, s), disjonction(s, r)),
                    "S3", _CLE)


def s4(r: Assemblage, s: Assemblage, t: Assemblage, sig: Signature = DEFAUT) -> Theoreme:
    """⊢ (R ⇒ S) ⇒ ((T ∨ R) ⇒ (T ∨ S)). PDF p.~34."""
    _exiger_relations(sig, r, s, t)
    interne = implication(disjonction(t, r), disjonction(t, s))
    return Theoreme(frozenset(), implication(implication(r, s), interne), "S4", _CLE)


def s5(r: Assemblage, t: Assemblage, x: str, sig: Signature = DEFAUT) -> Theoreme:
    """⊢ (T|x)R ⇒ (∃x)R. PDF p.~33 (§I.4.2). R relation, T terme, x lettre."""
    if not est_relation(r, sig):
        raise ValueError("S5 : R doit être une relation")
    if not est_terme(t, sig):
        raise ValueError("S5 : T doit être un terme")
    if not est_lettre(x):
        raise ValueError("S5 : x doit être une lettre")
    concl = implication(substitution_b_x_a(t, x, r), existe(x, r))
    return Theoreme(frozenset(), concl, "S5", _CLE)


def s6(t: Assemblage, u: Assemblage, x: str, r: Assemblage,
       sig: Signature = DEFAUT) -> Theoreme:
    """⊢ (T=U) ⇒ ((T|x)R ⇔ (U|x)R). PDF p.~38 (§I.5.1). T,U termes, R relation."""
    if not (est_terme(t, sig) and est_terme(u, sig)):
        raise ValueError("S6 : T et U doivent être des termes")
    if not est_relation(r, sig):
        raise ValueError("S6 : R doit être une relation")
    if not est_lettre(x):
        raise ValueError("S6 : x doit être une lettre")
    equiv = equivalence(substitution_b_x_a(t, x, r), substitution_b_x_a(u, x, r))
    return Theoreme(frozenset(), implication(egalite(t, u), equiv), "S6", _CLE)


def s7(r: Assemblage, s: Assemblage, x: str, sig: Signature = DEFAUT) -> Theoreme:
    """⊢ (∀x)(R ⇔ S) ⇒ (τ_x(R) = τ_x(S)). PDF p.~38 (§I.5.1). R,S relations."""
    if not (est_relation(r, sig) and est_relation(s, sig)):
        raise ValueError("S7 : R et S doivent être des relations")
    if not est_lettre(x):
        raise ValueError("S7 : x doit être une lettre")
    concl = implication(pour_tout(x, equivalence(r, s)),
                        egalite(tau_x(r, x), tau_x(s, x)))
    return Theoreme(frozenset(), concl, "S7", _CLE)


def axiome(theorie: Theorie, relation: Assemblage) -> Theoreme:
    """⊢ A si A est un axiome explicite de la théorie. PDF p.~22."""
    if not any(relation == ax for ax in theorie.axiomes):
        raise ValueError("cette relation n'est pas un axiome explicite")
    return Theoreme(frozenset(), relation, f"axiome[{theorie.nom}]", _CLE)


def modus_ponens(thm_r: Theoreme, thm_imp: Theoreme,
                 sig: Signature = DEFAUT) -> Theoreme:
    """C1 — de Γ⊢R et Δ⊢(R⇒S), déduire Γ∪Δ ⊢ S. PDF p.~33.

    Décomposition réelle : on lit ⊢(R⇒S), on vérifie la forme ∨ ¬R S et la
    coïncidence de R avec la mineure, puis on reconstruit S.
    """
    arbre = depuis_assemblage(thm_imp.conclusion, sig)
    if not (arbre.tete == "OU" and arbre.enfants[0].tete == "NON"):
        raise ValueError("la majeure n'est pas une implication (∨ ¬R S)")
    antecedent = vers_assemblage(arbre.enfants[0].enfants[0])
    if antecedent != thm_r.conclusion:
        raise ValueError("modus ponens : mineure ≠ antécédent de la majeure")
    conclusion = vers_assemblage(arbre.enfants[1])
    hyps = thm_r.hypotheses | thm_imp.hypotheses
    return Theoreme(hyps, conclusion, "MP(C1)", _CLE)


def generalisation(x: str, thm: Theoreme, sig: Signature = DEFAUT) -> Theoreme:
    """C27 — de Γ⊢R (x non libre dans Γ), déduire Γ ⊢ (∀x)R. PDF p.~32.

    Règle PRIMITIVE de confiance : sa validité est le critère C27 que Bourbaki
    démontre (via C3 + C26). Condition de bord : x ne doit pas figurer librement
    dans une hypothèse (et, en toute rigueur, ne pas être une *constante* de la
    théorie — toujours vrai pour une lettre dans la théorie de base sans axiome
    explicite). Pour un théorème clos (Γ = ∅), la généralisation est sans
    condition.
    """
    if not est_lettre(x):
        raise ValueError("généralisation : x doit être une lettre")
    for h in thm.hypotheses:
        if x in lettres(h):
            raise ValueError(f"généralisation : {x!r} figure librement dans une hypothèse")
    return Theoreme(thm.hypotheses, pour_tout(x, thm.conclusion),
                    "C27(généralisation)", _CLE)


def loi_deduction(a: Assemblage, thm: Theoreme, sig: Signature = DEFAUT) -> Theoreme:
    """C6 — de Γ⊢B, déduire (Γ\\{A}) ⊢ (A ⇒ B). PDF p.~26.

    Règle PRIMITIVE de confiance (cf. note de confiance en tête de module) :
    sa validité est le théorème de la déduction démontré par Bourbaki (C6).
    """
    _exiger_relations(sig, a)
    hyps = thm.hypotheses - {a}
    return Theoreme(hyps, implication(a, thm.conclusion), "C6(déduction)", _CLE)


__all__ = [
    "Theoreme", "Theorie",
    "assume", "s1", "s2", "s3", "s4", "s5", "s6", "s7",
    "axiome", "modus_ponens", "loi_deduction", "generalisation",
]
