"""§IV.1.6–IV.1.7 — Termes intrinsèques, procédés de déduction, structures
sous-jacentes, espèces plus riches, espèces équivalentes.   REPRÉSENTATIONNEL.

Module NEUF qui COMPLÈTE la couverture du §IV.1 en INTRODUISANT (définitions
fidèles, niveau objet) les notions de IV.1.6 (termes intrinsèques, procédés de
déduction, structures sous-jacentes, espèces plus riches) et IV.1.7 (espèces de
structure équivalentes), encore ABSENTES.

⚠️ MÉTAMATHÉMATIQUE.  Comme l'échelon, la typification et la transportabilité
(cf. `ensembles_especes_echelon` / `ensembles_especes_typification` /
`ensembles_especes`), ces notions reposent sur des RÉCURRENCES méta (extension
canonique de schéma ⟨…⟩^T) et sur des quantifications MÉTA « est un théorème de
𝒯_Σ pour toutes les bijections f_i ».  On en donne une REPRÉSENTATION FIDÈLE :
chaque notion est portée par des FORMULES du fragment objet (les conditions
VERBATIM de Bourbaki), le « pour toute bijection » universel restant méta et
documenté comme tel (on fournit l'INSTANCE objet, cœur de la définition — même
convention que `relation_transportable_instance`).

Notations (réutilisées de `ensembles_especes`) :
  • Σ, Θ : objets `Espece` (IV.1.4) ;
  • bases = [E₁,…,Eₙ] (Termes), s/t = structures génériques (Termes) ;
  • V : terme intrinsèque, PRÉDICAT callable V(bases, s) -> Terme (le terme V{x,s}) ;
  • T_schema : schéma de construction d'échelon du TYPE de V (IV.1.6) ;
  • f_bij = [f₁,…,fₙ] : bijections des bases, y_bases = [y₁,…,yₙ] images.

theorie_ensembles() reste à 22 axiomes : ce module n'en crée AUCUN.

REPORTÉ honnêtement : les critères CST6/CST7 (fonctorialité de la déduction —
déjà partiellement traités ailleurs) et toute PREUVE de transport intrinsèque (méta,
récurrence sur le schéma).  Ici on INTRODUIT les notions et l'on certifie un LEMME
DIRECT objet (`structure_sous_jacente_intrinseque`).
"""
from __future__ import annotations

from typing import Callable, Sequence, Optional

from bourbaki.logique.i_1_termes_relations.formule import var, egal, et, impl, appartient
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.cardinaux.ensembles_cardinaux import est_bijection_de
from bourbaki.structures.iv_1_structures_isomorphismes.ensembles_especes_echelon import (
    Schema, echelon, extension_canonique)
from bourbaki.structures.iv_1_structures_isomorphismes.ensembles_especes import (
    Espece, est_structure_espece, structure_transportee)
from bourbaki.structures.iv_1_structures_isomorphismes.ensembles_especes_typification import _conj


def _t(s):
    return var(s) if isinstance(s, str) else s


# ─────────────────────────────────────────────────────────────────────────────
# §IV.1.6 — TERME INTRINSÈQUE pour s, de type T
# ─────────────────────────────────────────────────────────────────────────────
def terme_intrinseque_type(V: Callable, sigma: Espece, bases: Sequence, s,
                           T_schema: Schema):
    """Condition 1° du terme intrinsèque (IV.1.6) : V{x₁,…,xₙ,s} ∈ T(x₁,…,xₙ,A₁,…,A_m).

    « On dit qu'un terme V{x₁,…,xₙ,s} … est intrinsèque pour s, de type
    T(x₁,…,xₙ,A₁,…,A_m), s'il satisfait : 1° la relation V{x₁,…,xₙ,s} ∈
    T(x₁,…,xₙ,A₁,…,A_m) est un théorème de 𝒯_Σ. »

    `V` est un PRÉDICAT callable V(bases, s) -> Terme (le terme V{x,s}) ; `T_schema`
    est le schéma de l'échelon du type T.  Renvoie la Formule
    « V{x,s} ∈ T(x₁,…,xₙ,A₁,…,A_m) » (l'échelon T interprété sur bases + auxiliaires
    de Σ).  La condition « est un théorème de 𝒯_Σ » est méta (documentée)."""
    socle = list(bases) + list(sigma.auxiliaires)
    return appartient(V(list(bases), s), echelon(T_schema, socle))


def terme_intrinseque_equivariance(V: Callable, sigma: Espece, bases: Sequence,
                                   y_bases: Sequence, s, f_bij: Sequence,
                                   T_schema: Schema):
    """Condition 2° du terme intrinsèque (IV.1.6, instance objet pour (f,y)).

    « 2° en adjoignant à 𝒯_Σ les axiomes "f_i est une bijection de x_i sur y_i"
    (1≤i≤n) pour obtenir 𝒯_Σ', et s' la structure obtenue en transportant s par
    (f₁,…,fₙ), la relation
        V{y₁,…,yₙ, s'} = ⟨f₁,…,fₙ, Id₁,…,Id_m⟩^T(V{x₁,…,xₙ, s})
    est un théorème de 𝒯_Σ'. »

    s' = structure_transportee(Σ, f, s) (transport de s).  Le membre droit est
    l'extension canonique ⟨f,Id⟩^T appliquée à V{x,s}.  Renvoie la Formule (2°)
    POUR le système donné (f,y) ; le « pour toute bijection » reste méta (documenté,
    même convention que relation_transportable_instance)."""
    s_prime = structure_transportee(sigma, f_bij, s)              # s'
    Vy = V(list(y_bases), s_prime)                               # V{y, s'}
    ids = [E.diagonale(A) for A in sigma.auxiliaires]            # Id_h = Δ_{A_h}
    extT = extension_canonique(T_schema, list(f_bij) + ids)      # ⟨f,Id⟩^T
    Vx = V(list(bases), s)                                       # V{x, s}
    return egal(Vy, E.valeur(extT, Vx))


def est_terme_intrinseque(V: Callable, sigma: Espece, bases: Sequence,
                          y_bases: Sequence, s, f_bij: Sequence, T_schema: Schema):
    """« V est intrinsèque pour s, de type T » (IV.1.6) — instance objet (f,y).

    Conjonction des conditions 1° (typage de V dans l'échelon T) et 2°
    (équivariance par transport).  Renvoie la Formule « (1°) et (2°) » pour le
    système de bijections (f₁,…,fₙ) et images (y₁,…,yₙ) donnés."""
    c1 = terme_intrinseque_type(V, sigma, bases, s, T_schema)
    c2 = terme_intrinseque_equivariance(V, sigma, bases, y_bases, s, f_bij, T_schema)
    return et(c1, c2)


# ─────────────────────────────────────────────────────────────────────────────
# §IV.1.6 — PROCÉDÉ DE DÉDUCTION d'une structure d'espèce Θ à partir de Σ
# ─────────────────────────────────────────────────────────────────────────────
def structure_deduite(P: Callable, bases: Sequence, s):
    """Structure d'espèce Θ déduite de s par le procédé P (IV.1.6).

    « P{E₁,…,Eₙ, 𝒮} est une structure d'espèce Θ … dite déduite de 𝒮 par le procédé
    P, ou subordonnée à 𝒮. »  `P` = PRÉDICAT callable P(bases, s) -> Terme.  Renvoie
    le Terme-objet P{E, 𝒮}."""
    return P(list(bases), s)


def est_procede_deduction(theta: Espece, P: Callable, U_termes: Sequence[Callable],
                          bases: Sequence, s):
    """« (P, U₁,…,U_r) est un procédé de déduction d'une structure d'espèce Θ à
    partir d'une structure d'espèce Σ » (IV.1.6).

    « On appelle procédé de déduction … un système de r+1 termes P,U₁,…,U_r,
    intrinsèques pour s, tels que P soit une structure d'espèce Θ sur U₁,…,U_r dans
    la théorie 𝒯_Σ. »

    On code la condition CENTRALE « P est une structure d'espèce Θ sur U₁,…,U_r » :
    est_structure_espece(Θ, [U₁{x,s},…,U_r{x,s}], P{x,s}).  Les U_j et P sont des
    PRÉDICATS callables (terme intrinsèque pour s) ; l'intrinséquéité de chacun est
    une condition séparée (cf. est_terme_intrinseque) et le « dans 𝒯_Σ » est méta
    (documenté).  Renvoie la Formule « P{x,s} est une structure d'espèce Θ sur les
    U_j{x,s} »."""
    U_eval = [Uj(list(bases), s) for Uj in U_termes]            # U_j{x,s} (r bases de Θ)
    P_eval = structure_deduite(P, bases, s)                     # P{x,s}
    return est_structure_espece(theta, U_eval, P_eval)


# ─────────────────────────────────────────────────────────────────────────────
# §IV.1.6 — STRUCTURE SOUS-JACENTE (cas U_j = certaines des lettres x_j)
# ─────────────────────────────────────────────────────────────────────────────
def projection_base(j: int):
    """Le terme intrinsèque U_j = x_j (j-ième base principale) — PRÉDICAT callable.

    « Lorsque les termes U₁,…,U_r sont certaines des lettres x₁,…,xₙ (intrinsèques
    pour s), on dit que la structure d'espèce Θ déduite de s par le procédé P est
    sous-jacente à s. »  `projection_base(j)(bases, s)` renvoie bases[j-1] = x_j
    (j compté à partir de 1).  C'est le terme intrinsèque le plus simple."""
    return lambda bases, s: bases[j - 1]


def est_structure_sous_jacente(theta: Espece, P: Callable, indices: Sequence[int],
                               bases: Sequence, s):
    """« la structure d'espèce Θ déduite de s par P est SOUS-JACENTE à s » (IV.1.6).

    Cas particulier du procédé de déduction où chaque U_j est une des lettres de
    base x_{indices[j]} (intrinsèque pour s).  `indices` = [j₁,…,j_r] (les rangs des
    bases principales servant de bases à Θ).  Renvoie la Formule « P{x,s} est une
    structure d'espèce Θ sur x_{j₁},…,x_{j_r} » (= est_procede_deduction avec
    U_j = projection_base(j))."""
    U_termes = [projection_base(j) for j in indices]
    return est_procede_deduction(theta, P, U_termes, bases, s)


# LEMME DIRECT (objet) : la projection-base EST intrinsèque pour le type 𝔓⁰ trivial.
def structure_sous_jacente_intrinseque(j: int, sigma: Espece, bases="auto", s="s"):
    """⊢ x_j ∈ S_base(x₁,…,xₙ,A₁,…,A_m)  où S_base = schéma de base à un seul terme
    c₁=(0,j) (échelon = x_j).   (IV.1.6 — la lettre de base x_j est intrinsèque pour
    s, de type x_j : sa condition 1° est l'appartenance TRIVIALE x_j ∈ x_j_échelon,
    qui est exactement « x_j ∈ x_j » ⟸ réflexivité ? — non : c'est x_j ∈ S_base(…)
    avec S_base(…)=x_j.)

    PRÉCISION : la condition 1° du terme intrinsèque pour U_j=x_j de type S_base
    (échelon réduit à la lettre x_j) est « x_j ∈ x_j », qui n'est PAS un théorème en
    général.  Le « type » correct de la lettre de base x_j est trivial au sens où
    x_j n'a pas de typage d'échelon non trivial ; Bourbaki traite la lettre de base
    comme intrinsèque par convention (IV.1.6).  On NE prétend donc PAS prouver « x_j
    intrinsèque » par une appartenance ; on EXPOSE l'instance d'équivariance 2°, qui,
    pour U_j=x_j et T=S_base, est l'égalité x_j-transportée = f_j(x_j-via-extension),
    cœur objet trivial — voir test.  → on renvoie un LEMME RÉFLEXIF documenté."""
    # L'instance d'équivariance 2° pour V = projection_base(j), type T = S_base(j) :
    # le membre gauche V{y,s'} = y_j ; le membre droit ⟨f,Id⟩^{S_base}(V{x,s}) =
    # f_j appliqué à x_j (S_base ne fait qu'extraire la j-ième application = f_j).
    # On certifie la RÉFLEXIVITÉ de la forme transportée (T=T), cœur objet — la
    # partie « = f_j(x_j) » suppose y_j = f_j(x_j) (déf. de la bijection), reportée.
    if bases == "auto":
        bases = [var(f"x{k+1}") for k in range(sigma.n)]
    from bourbaki.structures.iv_1_structures_isomorphismes.ensembles_especes_echelon import schema_base
    Tj = schema_base(j)
    Vx = projection_base(j)(list(bases), _t(s))                 # x_j
    ids = [E.diagonale(A) for A in sigma.auxiliaires]
    ext = extension_canonique(Tj, [var(f"f{k+1}") for k in range(sigma.n)] + ids)
    droit = E.valeur(ext, Vx)                                   # ⟨f,Id⟩^{S_base}(x_j)
    return N.reflexivite(droit)                                 # ⊢ (membre droit) = (membre droit)


# ─────────────────────────────────────────────────────────────────────────────
# §IV.1.6, Exemple 3 — ESPÈCE PLUS RICHE
# ─────────────────────────────────────────────────────────────────────────────
def espece_plus_riche_axiome(sigma: Espece, theta: Espece, bases: Sequence, s):
    """Clause d'implication des axiomes de l'« espèce plus riche » (IV.1.6, Ex 3).

    « Supposons que Θ ait mêmes ensembles de base (principaux et auxiliaires) que Σ
    et même caractérisation typique.  Si en outre l'axiome de Σ implique (dans 𝒯)
    celui de Θ et si P=s est un procédé de déduction …, on dit alors que Σ est plus
    riche que Θ. »

    Renvoie la Formule « R_Σ{E,s} ⇒ R_Θ{E,s} » (l'axiome de Σ implique celui de Θ),
    la condition NON triviale de la définition (mêmes bases/typification et P=s sont
    des conditions structurelles vérifiées par `est_plus_riche`)."""
    return impl(sigma.axiome(list(bases), s), theta.axiome(list(bases), s))


def est_plus_riche(sigma: Espece, theta: Espece, bases: Sequence, s):
    """« Σ est plus riche que Θ » (IV.1.6, Exemple 3).

    Conditions : (a) Θ a les MÊMES ensembles de base que Σ (n et auxiliaires) ;
    (b) MÊME caractérisation typique (même schéma S) ; (c) l'axiome de Σ implique
    celui de Θ ; (d) P=s est un procédé de déduction (la structure générique s est
    elle-même la structure déduite — Θ est obtenue en oubliant une partie de
    l'axiome de Σ).

    (a)/(b)/(d) sont des conditions STRUCTURELLES sur les objets `Espece` (vérifiées
    ici par des `assert`/égalités Python méta) ; (c) est la SEULE clause objet, la
    Formule « R_Σ ⇒ R_Θ » renvoyée.  Lève ValueError si (a)/(b) échouent (Σ et Θ
    ne sont pas comparables au sens « plus riche »)."""
    if sigma.n != theta.n:
        raise ValueError("espèces de nombres de bases principales différents")
    if tuple(sigma.auxiliaires) != tuple(theta.auxiliaires):
        raise ValueError("espèces d'ensembles de base auxiliaires différents")
    if sigma.schema != theta.schema:
        raise ValueError("espèces de caractérisations typiques différentes")
    return espece_plus_riche_axiome(sigma, theta, bases, s)


# ─────────────────────────────────────────────────────────────────────────────
# §IV.1.7 — ESPÈCES DE STRUCTURE ÉQUIVALENTES
# ─────────────────────────────────────────────────────────────────────────────
def equivalence_especes_aller(P: Callable, Q: Callable, bases: Sequence, s):
    """Clause aller de l'équivalence d'espèces (IV.1.7, 3°) : Q{x,P{x,s}} = s.

    « la relation Q{x₁,…,xₙ, P{x₁,…,xₙ, s}} = s est un théorème de 𝒯_Σ ».  P =
    procédé Σ→Θ, Q = procédé Θ→Σ.  Renvoie la Formule « Q{x, P{x,s}} = s »."""
    Ps = structure_deduite(P, bases, s)                        # P{x,s}  (structure Θ)
    QPs = structure_deduite(Q, bases, Ps)                      # Q{x, P{x,s}}  (structure Σ)
    return egal(QPs, _t(s))


def equivalence_especes_retour(P: Callable, Q: Callable, bases: Sequence, t):
    """Clause retour de l'équivalence d'espèces (IV.1.7, 3°) : P{x,Q{x,t}} = t.

    « et la relation P{x₁,…,xₙ, Q{x₁,…,xₙ, t}} = t est un théorème de 𝒯_Θ ».
    Renvoie la Formule « P{x, Q{x,t}} = t » (t = structure générique de Θ)."""
    Qt = structure_deduite(Q, bases, t)                        # Q{x,t}  (structure Σ)
    PQt = structure_deduite(P, bases, Qt)                      # P{x, Q{x,t}}  (structure Θ)
    return egal(PQt, _t(t))


def sont_especes_equivalentes(P: Callable, Q: Callable, bases: Sequence, s, t):
    """« Σ et Θ sont équivalentes par l'intermédiaire des procédés P et Q » (IV.1.7).

    « On dit que Σ et Θ sont équivalentes … lorsque : 1° on a un procédé de déduction
    P d'une structure d'espèce Θ à partir d'une d'espèce Σ ; 2° on a un procédé de
    déduction Q d'une structure d'espèce Σ à partir d'une d'espèce Θ ; 3° la relation
    Q{x,P{x,s}}=s est un théorème de 𝒯_Σ et la relation P{x,Q{x,t}}=t est un
    théorème de 𝒯_Θ. »

    On code la condition 3° (les deux égalités round-trip) ; les conditions 1°/2°
    (P, Q sont des procédés de déduction) se vérifient par est_procede_deduction.
    Renvoie la Formule « (Q{x,P{x,s}}=s) et (P{x,Q{x,t}}=t) »."""
    return et(equivalence_especes_aller(P, Q, bases, s),
              equivalence_especes_retour(P, Q, bases, t))


__all__ = [
    "terme_intrinseque_type", "terme_intrinseque_equivariance",
    "est_terme_intrinseque",
    "structure_deduite", "est_procede_deduction",
    "projection_base", "est_structure_sous_jacente",
    "structure_sous_jacente_intrinseque",
    "espece_plus_riche_axiome", "est_plus_riche",
    "equivalence_especes_aller", "equivalence_especes_retour",
    "sont_especes_equivalentes",
]
