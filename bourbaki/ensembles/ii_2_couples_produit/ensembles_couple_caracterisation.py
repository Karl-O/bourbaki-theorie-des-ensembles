"""§II.2 — CARACTÉRISATION DU COUPLE (Bourbaki E II.7, §2.1, n°1).

Énoncé Bourbaki verbatim (E II.7) :

  « La relation z = (x, y) est équivalente à "z est un couple et x = pr₁z et
    y = pr₂z" ».

où « z est un couple » désigne (∃x)(∃y)(z = (x, y)).  Ici on l'exprime INLINE
avec le quantificateur existentiel (pas de prédicat nommé) :

  est_couple(z) := (∃a)(∃b)(z = (a, b))   (liants a, b).

RÉSULTAT (CLOS, 0 hypothèse — équivalence pure, certifié par le noyau LCF) :

  ⊢ ( z = (x, y) )  ⇔  ( est_couple(z)  et  x = pr₁z  et  y = pr₂z ).

DIFFICULTÉ DE HYGIÈNE.  pr₁z := τx((∃y)(z=(x,y))) et pr₂z := τy((∃x)(z=(x,y)))
LIENT les lettres x, y — les MÊMES que les variables libres de l'énoncé.  On ne
peut donc PAS former pr₁((x,y)) (capture) ni ∃-éliminer un conséquent contenant
pr₁z ET la variable libre x (la tactique forge τb(x=pr₁z), qui porte x libre, et
α-renomme le liant x de pr₁z → l'égalité n'est plus syntaxiquement pr₁z).

STRATÉGIE (évite toute ∃-élimination d'un conséquent contenant pr₁z/pr₂z) :
  Sens ⇒ : de z = (x, y) on prend les TÉMOINS CANONIQUES de est_couple :
      A := τa((∃b)(z=(a,b))),  B := τb(z=(A,b))  (variables libres ⊆ {z}, ∌ x,y),
    pour lesquels z = (A, B) sans aucune ∃-élimination (S5 + existe_temoin).  Les
    composantes A, B étant disjointes de x, y, on a pr₁z = A, pr₂z = B (congruence
    + projection_terme), et la Proposition 1 sur (x,y)=(A,B) donne x = A, y = B ;
    par transitivité x = pr₁z, y = pr₂z, et est_couple(z) (témoins a:=x, b:=y).
  Sens ⇐ : de est_couple(z), témoins frais a, b avec z = (a, b) ; pr₁z = a,
    pr₂z = b, donc x = pr₁z = a, y = pr₂z = b, d'où (x,y) = (a,b) = z, soit
    z = (x, y).  Ici l'∃-élimination porte sur le conséquent z = (x,y) (sans
    pr₁z/pr₂z), donc PROPRE.

theorie_ensembles() INCHANGÉE (= 22) : aucun axiome ajouté (recollement pur,
primitives N.* uniquement).
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (
    Terme, var, egal, et, existe, equiv, tau)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant)
from bourbaki.logique.i_3_quantifies.tactiques_abrege_quantif import existe_elimination
from bourbaki.logique.i_4_egalitaires.tactiques_abrege_egalite import (
    symetrie, composer_egalites, congruence_terme)
from bourbaki.ensembles.ii_2_couples_produit.ensembles_couples import (
    proposition_1, couple_egal_implique_composantes)


def _T(v):
    """Coercion nom → terme : accepte un Terme ou un nom de variable."""
    return v if isinstance(v, Terme) else var(v)


# Témoins frais (sens ⇐) ≠ x, y (liants des τ-termes pr₁/pr₂) et ≠ w, c (trous des
# tactiques composer_egalites/symetrie/congruence_terme).
_A, _B = "a", "b"


def est_couple(vz):
    """« z est un couple » := (∃a)(∃b)(z = (a, b))  (E II.7, exprimé inline)."""
    va, vb = var(_A), var(_B)
    return existe(_A, existe(_B, egal(vz, E.couple(va, vb))))


# ── Projection sur des composantes-TERMES (disjointes des liants x, y) ─────────
def _tau_egal_terme(vt):
    """⊢ τx(x = t) = t   (t terme, x ∉ libres(t)).  (Calque de `tau_egal`, en termes.)"""
    vx = var("x")
    ex = N.modus_ponens(N.reflexivite(vt), N.s5(egal(vx, vt), vt, "x"))   # (∃x)(x=t)
    return N.modus_ponens(ex, N.existe_temoin(egal(vx, vt), "x"))         # τx(x=t)=t


def _proj1_terme(vt1, vt2):
    """⊢ pr₁((t1, t2)) = t1   (t1, t2 termes, x, y ∉ libres(t1)∪libres(t2)).

    Calque exact de `projection_premiere`, mais sur des composantes-TERMES."""
    vx, vy = var("x"), var("y")
    cuv = E.couple(vt1, vt2)
    R = existe("y", egal(cuv, E.couple(vx, vy)))
    dur = couple_egal_implique_composantes(vt1, vt2, "x", "y")
    heq = N.assume(egal(cuv, E.couple(vx, vy)))
    xu = N.modus_ponens(conjonction_elim_gauche(N.modus_ponens(heq, dur)), symetrie(vt1, vx))
    inner = N.loi_deduction(egal(cuv, E.couple(vx, vy)), xu)              # R{y} ⇒ (x=t1)
    F = existe_elimination(inner, "y")                                    # R ⇒ (x=t1)
    hxu = N.assume(egal(vx, vt1))
    uv_xv = N.modus_ponens(N.modus_ponens(hxu, symetrie(vx, vt1)),
                           congruence_terme(vt1, vx, E.couple(var("w"), vt2)))
    Rx = N.modus_ponens(uv_xv, N.s5(egal(cuv, E.couple(vx, vy)), vt2, "y"))
    B = N.loi_deduction(egal(vx, vt1), Rx)                               # (x=t1) ⇒ R
    gen = N.generalisation("x", conjonction_intro(F, B))                 # (∀x)(R ⇔ (x=t1))
    tau_eq = N.modus_ponens(gen, N.s7(R, egal(vx, vt1), "x"))            # τx(R) = τx(x=t1)
    return composer_egalites(tau_eq, _tau_egal_terme(vt1))               # pr₁((t1,t2)) = t1


def _proj2_terme(vt1, vt2):
    """⊢ pr₂((t1, t2)) = t2   (t1, t2 termes, x, y ∉ libres(t1)∪libres(t2)).

    Calque exact de `projection_seconde`, mais sur des composantes-TERMES."""
    vx, vy = var("x"), var("y")
    cuv = E.couple(vt1, vt2)
    R = existe("x", egal(cuv, E.couple(vx, vy)))
    dur = couple_egal_implique_composantes(vt1, vt2, "x", "y")
    heq = N.assume(egal(cuv, E.couple(vx, vy)))
    yv = N.modus_ponens(conjonction_elim_droite(N.modus_ponens(heq, dur)), symetrie(vt2, vy))
    inner = N.loi_deduction(egal(cuv, E.couple(vx, vy)), yv)              # R{x} ⇒ (y=t2)
    F = existe_elimination(inner, "x")                                    # R ⇒ (y=t2)
    hyv = N.assume(egal(vy, vt2))
    uv_uy = N.modus_ponens(N.modus_ponens(hyv, symetrie(vy, vt2)),
                           congruence_terme(vt2, vy, E.couple(vt1, var("w"))))
    Ry = N.modus_ponens(uv_uy, N.s5(egal(cuv, E.couple(vx, vy)), vt1, "x"))
    B = N.loi_deduction(egal(vy, vt2), Ry)                               # (y=t2) ⇒ R
    gen = N.generalisation("y", conjonction_intro(F, B))                 # (∀y)(R ⇔ (y=t2))
    tau_eq = N.modus_ponens(gen, N.s7(R, egal(vy, vt2), "y"))            # τy(R) = τy(y=t2)
    # τy(y=t2)=t2 : calque de _tau_egal_terme en liant y.
    ex = N.modus_ponens(N.reflexivite(vt2), N.s5(egal(vy, vt2), vt2, "y"))
    return composer_egalites(tau_eq, N.modus_ponens(ex, N.existe_temoin(egal(vy, vt2), "y")))


# ── Cœur du sens ⇐ : pr₁z = a, pr₂z = b sous z = (a, b) (témoins frais a, b) ───
def _pr1_de_couple(vz):
    """{ z = (a, b) } ⊢ pr₁z = a   (témoins frais a, b ≠ x, y des liants de pr₁)."""
    va, vb = var(_A), var(_B)
    h = N.assume(egal(vz, E.couple(va, vb)))                 # z = (a, b)
    pr1z_pr1ab = N.modus_ponens(
        h, congruence_terme(vz, E.couple(va, vb), E.pr1(var("c")), w="c"))   # pr₁z = pr₁((a,b))
    return composer_egalites(pr1z_pr1ab, _proj1_terme(va, vb))               # pr₁z = a


def _pr2_de_couple(vz):
    """{ z = (a, b) } ⊢ pr₂z = b   (témoins frais a, b ≠ x, y des liants de pr₂)."""
    va, vb = var(_A), var(_B)
    h = N.assume(egal(vz, E.couple(va, vb)))                 # z = (a, b)
    pr2z_pr2ab = N.modus_ponens(
        h, congruence_terme(vz, E.couple(va, vb), E.pr2(var("c")), w="c"))   # pr₂z = pr₂((a,b))
    return composer_egalites(pr2z_pr2ab, _proj2_terme(va, vb))               # pr₂z = b


def caracterisation_couple(x="x", y="y", z="z"):
    """⊢ ( z = (x, y) )  ⇔  ( z est un couple  et  x = pr₁z  et  y = pr₂z ).

    CARACTÉRISATION DU COUPLE (Bourbaki E II.7, §2.1, n°1) — équivalence CLOSE.
    « z est un couple » = est_couple(z) = (∃a)(∃b)(z = (a, b)) (inline).
    x, y, z : noms OU termes ; doivent être ≠ a, b, c, w (témoins/trous internes)."""
    vx, vy, vz = _T(x), _T(y), _T(z)
    va, vb = var(_A), var(_B)
    cpl = est_couple(vz)
    droite = et(et(cpl, egal(vx, E.pr1(vz))), egal(vy, E.pr2(vz)))

    # ── Sens ⇒ : z = (x, y) ⊢ est_couple(z) et x = pr₁z et y = pr₂z ──────────────
    h_dir = N.assume(egal(vz, E.couple(vx, vy)))            # z = (x, y)
    # est_couple(z) : témoins a := x, b := y (S5 ×2, sans ∃-élim).
    ec_x = N.modus_ponens(h_dir, N.s5(egal(vz, E.couple(vx, vb)), vy, _B))     # (∃b)(z=(x,b))
    ec = N.modus_ponens(ec_x, N.s5(existe(_B, egal(vz, E.couple(va, vb))),
                                   vx, _A))                                   # est_couple(z)

    # TÉMOINS CANONIQUES de est_couple(z) — variables libres ⊆ {z} (∌ x, y) :
    #   cap_a := τa((∃b)(z=(a,b))) ,  cap_b := τb(z=(cap_a, b))
    corps_b_a = existe(_B, egal(vz, E.couple(va, vb)))                       # (∃b)(z=(a,b))
    cap_a = tau(_A, corps_b_a)
    cap_b = tau(_B, egal(vz, E.couple(cap_a, vb)))
    # z = (cap_a, cap_b)  sous {h_dir}, PAR TÉMOIN canonique (existe_temoin ×2).
    z_a = N.modus_ponens(ec, N.existe_temoin(corps_b_a, _A))                 # (∃b)(z=(cap_a,b))
    z_ab = N.modus_ponens(z_a, N.existe_temoin(egal(vz, E.couple(cap_a, vb)), _B))  # z=(cap_a,cap_b)

    # pr₁z = cap_a , pr₂z = cap_b  (cap_a, cap_b disjoints de x, y → projection propre).
    pr1z_capa = composer_egalites(
        N.modus_ponens(z_ab, congruence_terme(vz, E.couple(cap_a, cap_b), E.pr1(var("c")), w="c")),
        _proj1_terme(cap_a, cap_b))                                          # pr₁z = cap_a
    pr2z_capb = composer_egalites(
        N.modus_ponens(z_ab, congruence_terme(vz, E.couple(cap_a, cap_b), E.pr2(var("c")), w="c")),
        _proj2_terme(cap_a, cap_b))                                          # pr₂z = cap_b

    # (x, y) = (cap_a, cap_b)  (h_dir symétrisé, composé à z=(cap_a,cap_b)), puis Prop 1.
    xy_eq_ab = composer_egalites(
        N.modus_ponens(h_dir, symetrie(vz, E.couple(vx, vy))), z_ab)         # (x,y)=(cap_a,cap_b)
    prop = N.modus_ponens(xy_eq_ab,
                          equivalence_avant(proposition_1(vx, vy, cap_a, cap_b)))
    x_eq_capa = conjonction_elim_gauche(prop)              # x = cap_a
    y_eq_capb = conjonction_elim_droite(prop)              # y = cap_b
    x_eq = composer_egalites(x_eq_capa, N.modus_ponens(pr1z_capa, symetrie(E.pr1(vz), cap_a)))
    y_eq = composer_egalites(y_eq_capb, N.modus_ponens(pr2z_capb, symetrie(E.pr2(vz), cap_b)))

    conj = conjonction_intro(conjonction_intro(ec, x_eq), y_eq)     # {h_dir} ⊢ droite
    sens_aller = N.loi_deduction(egal(vz, E.couple(vx, vy)), conj)  # ⊢ (z=(x,y)) ⇒ droite

    # ── Sens ⇐ : est_couple(z) et x = pr₁z et y = pr₂z ⊢ z = (x, y) ──────────────
    h_ret = N.assume(droite)
    ec_ret = conjonction_elim_gauche(conjonction_elim_gauche(h_ret))   # est_couple(z)
    x_pr1z_ret = conjonction_elim_droite(conjonction_elim_gauche(h_ret))  # x = pr₁z
    y_pr2z_ret = conjonction_elim_droite(h_ret)                         # y = pr₂z

    hab2 = N.assume(egal(vz, E.couple(va, vb)))            # z = (a, b)  (témoins frais)
    x_eq_a2 = composer_egalites(x_pr1z_ret, _pr1_de_couple(vz))   # x = pr₁z = a
    y_eq_b2 = composer_egalites(y_pr2z_ret, _pr2_de_couple(vz))   # y = pr₂z = b
    # (x, y) = (a, b) : congruence sur chaque coordonnée (trou « c »), puis = z.
    xy_xb = N.modus_ponens(y_eq_b2, congruence_terme(vy, vb, E.couple(vx, var("c")), w="c"))
    xb_ab = N.modus_ponens(x_eq_a2, congruence_terme(vx, va, E.couple(var("c"), vb), w="c"))
    xy_eq_ab2 = composer_egalites(xy_xb, xb_ab)           # (x,y)=(x,b)=(a,b)
    ab_eq_z = N.modus_ponens(hab2, symetrie(vz, E.couple(va, vb)))      # (a,b) = z
    xy_eq_z = composer_egalites(xy_eq_ab2, ab_eq_z)       # (x, y) = z
    z_eq_xy = N.modus_ponens(xy_eq_z, symetrie(E.couple(vx, vy), vz))   # z = (x, y)
    # décharger z = (a,b), ∃-éliminer b puis a (conséquent z=(x,y) sans pr₁z/pr₂z → propre)
    imp_ret = N.loi_deduction(egal(vz, E.couple(va, vb)), z_eq_xy)
    elim = existe_elimination(existe_elimination(imp_ret, _B), _A)
    z_eq_xy_ret = N.modus_ponens(ec_ret, elim)            # {droite} ⊢ z = (x, y)
    sens_retour = N.loi_deduction(droite, z_eq_xy_ret)    # ⊢ droite ⇒ (z=(x,y))

    # ── Équivalence (⇔ = (⇒) et (⇐)) ────────────────────────────────────────────
    return conjonction_intro(sens_aller, sens_retour)


def caracterisation_couple_cible(x="x", y="y", z="z"):
    """Énoncé visé de `caracterisation_couple` (pour vérification stricte)."""
    vx, vy, vz = _T(x), _T(y), _T(z)
    droite = et(et(est_couple(vz), egal(vx, E.pr1(vz))), egal(vy, E.pr2(vz)))
    return equiv(egal(vz, E.couple(vx, vy)), droite)


__all__ = ["est_couple", "caracterisation_couple", "caracterisation_couple_cible"]
