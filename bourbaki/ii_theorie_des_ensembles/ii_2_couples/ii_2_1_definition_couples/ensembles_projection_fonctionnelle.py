"""§II.2 — CARACTÉRISATION FONCTIONNELLE DES PROJECTIONS (Bourbaki E II.7, §2.1).

Énoncé Bourbaki verbatim (E II.7, le passage qui DÉFINIT pr₁/pr₂) :

  « La relation (∃x)(∃y)(z = (x, y)) se désigne par "z est un couple". Si z est
    un couple, les relations (∃y)(z = (x, y)) et (∃x)(z = (x, y)) sont
    fonctionnelles par rapport à x et y respectivement [...]. On désigne les
    termes τx((∃y)(z=(x,y))) et τy((∃x)(z=(x,y))) par pr₁z et pr₂z [...]. Si z
    est un couple, la relation (∃y)(z = (x, y)) est donc équivalente à x = pr₁z
    et la relation (∃x)(z = (x, y)) à y = pr₂z (I, p. 41). »

C'est la propriété qui CARACTÉRISE la première (resp. seconde) projection :
pr₁z est l'unique x tel que (∃y)(z=(x,y)), lorsque cet x existe (z couple).

RÉSULTATS (conditionnels HONNÊTES, certifiés par le noyau LCF) :

  { univoque_x(R₁), est_couple(z) } ⊢ (∃y)(z=(x,y)) ⇔ x = pr₁z
  { univoque_y(R₂), est_couple(z) } ⊢ (∃x)(z=(x,y)) ⇔ y = pr₂z

avec R₁{x} := (∃y)(z=(x,y)), R₂{y} := (∃x)(z=(x,y)).

POURQUOI DEUX HYPOTHÈSES HONNÊTES (et pourquoi c'est FIDÈLE).  Bourbaki dit « R
est FONCTIONNELLE par rapport à x », ce qui réunit deux faits :
  · UNIVOCITÉ (au plus un x) — `relation_univoque_x(R)` ; c'est elle qui, via le
    critère C45 (E I.41, « (I, p. 41) » cité par Bourbaki), donne le sens ⇒
    R ⇒ (x = τx(R)).  Elle découle de la Proposition 1 (résidu honnête, cf.
    `ensembles_couples.proposition_1`), donc n'est PAS un axiome.
  · EXISTENCE (au moins un x) — `est_couple(z)` = (∃x)R ; c'est elle qui, via
    l'identité-τ (`existe_temoin` : (∃x)R ⇒ (τx(R)|x)R), donne le sens ⇐.

LEVÉE DU PIÈGE DE CAPTURE.  pr₁z = τx(R₁) LIE le x de l'énoncé.  Au lieu de
∃-éliminer un conséquent contenant pr₁z (ce qui α-renomme son liant), on passe
INTÉGRALEMENT par des primitives qui construisent τx(R) en interne et le rendent
STRUCTURELLEMENT identique à pr₁z :
  · ⇒ : `c45_avant(R, "x")` — sa conclusion est R ⇒ (x = τx(R)), et
    τx(R₁) ≡ pr₁z (même assemblage) ;
  · ⇐ : `s6(pr₁z, x, "x", R)` donne (pr₁z=x) ⇒ ((pr₁z|x)R ⇔ R), et
    `existe_temoin(R, "x")` donne (∃x)R ⇒ (pr₁z|x)R — les deux (pr₁z|x)R sont le
    MÊME `subst_f(τx(R), "x", R)`, donc se recollent sans renommage.
Aucune ∃-élimination d'un conséquent portant pr₁z : pas de capture.

theorie_ensembles() INCHANGÉE (= 22) : recollement pur, primitives N.* seules.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, existe, equiv)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, equivalence_avant)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import existe_commute
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import symetrie
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_3_relations_fonctionnelles_c45 import (
    relation_univoque_x, c45_avant)


def _T(v):
    """Coercion nom → terme : accepte un Terme ou un nom de variable."""
    return v if isinstance(v, Terme) else var(v)


def _R1(vz):
    """R₁{x} := (∃y)(z = (x, y))  (relation FONCTIONNELLE en x si z couple)."""
    return existe("y", egal(vz, E.couple(var("x"), var("y"))))


def _R2(vz):
    """R₂{y} := (∃x)(z = (x, y))  (relation FONCTIONNELLE en y si z couple)."""
    return existe("x", egal(vz, E.couple(var("x"), var("y"))))


# @livre Ch.II §2.1 Rem.- | E II.7 L.22-26 | PDF p.58
def pr1_caracterisation(z="z"):
    """{ univoque_x(R₁), est_couple(z) } ⊢ (∃y)(z=(x,y)) ⇔ x = pr₁z.

    R₁{x} = (∃y)(z=(x,y)) ; pr₁z = τx(R₁).  Sens ⇒ = critère C45 (univocité,
    E I.41) ; sens ⇐ = identité-τ (existence, est_couple) recollée par S6.
    z : nom OU terme ; doit être ≠ x, y, u, v (liants/lettres fraîches internes)."""
    vz = _T(z)
    R = _R1(vz)
    pr1z = E.pr1(vz)                                      # = τx(R₁), structurel
    # ── ⇒ : { univoque_x(R₁) } ⊢ R₁ ⇒ (x = pr₁z)   (C45, E I.41) ──────────────
    fwd = c45_avant(R, "x", "u", "v")
    # ── ⇐ : { est_couple(z) } ⊢ (x = pr₁z) ⇒ R₁ ──────────────────────────────
    eq = egal(var("x"), pr1z)
    h_eq = N.assume(eq)                                  # x = pr₁z
    eq_sym = N.modus_ponens(h_eq, symetrie(var("x"), pr1z))      # pr₁z = x
    s6thm = N.s6(pr1z, var("x"), "x", R)                 # (pr₁z=x) ⇒ ((pr₁z|x)R₁ ⇔ R₁)
    equivR = N.modus_ponens(eq_sym, s6thm)               # (pr₁z|x)R₁ ⇔ R₁
    h_cpl = N.assume(E.est_un_couple(vz))                # (∃x)R₁ = est_couple(z)
    Rat = N.modus_ponens(h_cpl, N.existe_temoin(R, "x")) # (pr₁z|x)R₁
    Rproven = N.modus_ponens(Rat, equivalence_avant(equivR))     # R₁
    bwd = N.loi_deduction(eq, Rproven)                   # {est_couple} ⊢ (x=pr₁z) ⇒ R₁
    return conjonction_intro(fwd, bwd)


def pr1_caracterisation_cible(z="z"):
    """Énoncé visé de `pr1_caracterisation` (vérification stricte)."""
    vz = _T(z)
    return equiv(_R1(vz), egal(var("x"), E.pr1(vz)))


# @livre Ch.II §2.1 Rem.- | E II.7 L.22-26 | PDF p.58
def pr2_caracterisation(z="z"):
    """{ univoque_y(R₂), est_couple(z) } ⊢ (∃x)(z=(x,y)) ⇔ y = pr₂z.

    Dual de `pr1_caracterisation`.  R₂{y} = (∃x)(z=(x,y)) ; pr₂z = τy(R₂).
    est_couple(z) = (∃x)(∃y)(...) est ramené à (∃y)R₂ = (∃y)(∃x)(...) par
    `existe_commute` (commutation des deux ∃).
    z : nom OU terme ; doit être ≠ x, y, u, v (liants/lettres fraîches internes)."""
    vz = _T(z)
    R = _R2(vz)
    pr2z = E.pr2(vz)                                     # = τy(R₂), structurel
    # ── ⇒ : { univoque_y(R₂) } ⊢ R₂ ⇒ (y = pr₂z)   (C45, E I.41) ──────────────
    fwd = c45_avant(R, "y", "u", "v")
    # ── ⇐ : { est_couple(z) } ⊢ (y = pr₂z) ⇒ R₂ ──────────────────────────────
    eq = egal(var("y"), pr2z)
    h_eq = N.assume(eq)
    eq_sym = N.modus_ponens(h_eq, symetrie(var("y"), pr2z))      # pr₂z = y
    s6thm = N.s6(pr2z, var("y"), "y", R)                 # (pr₂z=y) ⇒ ((pr₂z|y)R₂ ⇔ R₂)
    equivR = N.modus_ponens(eq_sym, s6thm)
    h_cpl = N.assume(E.est_un_couple(vz))                # (∃x)(∃y)(z=(x,y))
    comm = existe_commute("x", "y", egal(vz, E.couple(var("x"), var("y"))))
    cpl_yx = N.modus_ponens(h_cpl, equivalence_avant(comm))      # (∃y)(∃x)(...) = (∃y)R₂
    Rat = N.modus_ponens(cpl_yx, N.existe_temoin(R, "y"))        # (pr₂z|y)R₂
    Rproven = N.modus_ponens(Rat, equivalence_avant(equivR))     # R₂
    bwd = N.loi_deduction(eq, Rproven)
    return conjonction_intro(fwd, bwd)


def pr2_caracterisation_cible(z="z"):
    """Énoncé visé de `pr2_caracterisation` (vérification stricte)."""
    vz = _T(z)
    return equiv(_R2(vz), egal(var("y"), E.pr2(vz)))


__all__ = ["pr1_caracterisation", "pr1_caracterisation_cible",
           "pr2_caracterisation", "pr2_caracterisation_cible"]
