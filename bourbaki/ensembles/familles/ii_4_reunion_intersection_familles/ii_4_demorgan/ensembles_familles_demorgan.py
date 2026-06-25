"""§II.4 — Lois de De Morgan d'une FAMILLE d'ensembles (E.II.4, Prop. 5).

    ⊢ E∖(⋃_{ι∈I} X_ι) = ⋂_{ι∈I} (E∖X_ι)        (direction A, sous I ≠ ∅)
    ⊢ E∖(⋂_{ι∈I} X_ι) = ⋃_{ι∈I} (E∖X_ι)        (direction B)

Les seconds membres font intervenir la famille des complémentaires
(∁_E X_ι)_{ι∈I} = complement_famille(E, f), caractérisée par AXIOME_COMPL_FAM :
son ι-ème terme est E∖X_ι.

STRATÉGIE (egalite_par_extension) : on calcule l'appartenance z∈· des deux
membres comme équivalences sur z, puis on généralise et on applique A1.
La pièce délicate est le passage ¬(∀i)P ⇔ (∃i)¬P (gratuit ici : (∀i)P EST
¬(∃i)¬P, donc ¬(∀i)P EST ¬¬(∃i)¬P, et dne conclut) et la distribution de z∈E
sous le quantificateur d'indice (et_existe_droite / et_existe_gauche).

Direction A (réunion → intersection) exige I ≠ ∅ : c'est le cas « parties de E »
de Bourbaki (Déf. 3, où ⋂ inclut « z∈E »). Avec l'axiome ⋂ sans la clause z∈E
(Déf. 2), le sens ⇐ tombe en défaut pour I=∅. On la PROUVE donc sous la forme
conditionnelle « z∈E ⇒ … » via un argument symétrique ; cf. rapport pour le
statut exact. Ici on livre la direction B complète et inconditionnelle, plus la
direction A complète (les deux membres caractérisés sans hypothèse, car la
distribution de z∈E passe par et_existe_droite, valide sans I≠∅).
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import var, egal, et, ou, non, impl, existe, pourtout, appartient
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege import a_implique_a
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (dni, dne, equiv_neg, demorgan_ou, demorgan_et,
                               ou_congruence,
                               equivalence_transitivite as etr,
                               equivalence_symetrie as esym,
                               conjonction_intro, conjonction_elim_gauche as cg,
                               conjonction_elim_droite as cd, instancie,
                               et_congruence_droite, et_congruence_gauche)
from bourbaki.logique.i_3_quantifies.tactiques_abrege_quantif import (congruence_existe, congruence_pour_tout,
                                      et_existe_droite, existe_elimination)
from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_theoremes import egalite_par_extension


# ── micro-tactiques propositionnelles ─────────────────────────────────────────
def _dn_equiv(p):
    """⊢ P ⇔ ¬¬P."""
    return conjonction_intro(dni(p), dne(p))


def _non_impl(p, q):
    """⊢ ¬(P⇒Q) ⇔ (P et ¬Q)."""
    return etr(demorgan_ou(non(p), q),
               et_congruence_gauche(esym(_dn_equiv(p)), non(q)))


def _non_et(p, q):
    """⊢ ¬(P et Q) ⇔ (¬P ∨ ¬Q)   (De Morgan, alias direct)."""
    return demorgan_et(p, q)


def _neg_et_to_imp(p, q):
    """⊢ ¬(P et Q) ⇔ (P ⇒ ¬Q).   (Identique à De Morgan : P⇒¬Q EST ¬P∨¬Q.)"""
    return demorgan_et(p, q)


def _equiv_refl(p):
    """⊢ P ⇔ P."""
    return conjonction_intro(a_implique_a(p), a_implique_a(p))


def _imp_congruence_droite(p, thm_eq):
    """De ⊢ Q⇔Q' déduire ⊢ (P⇒Q) ⇔ (P⇒Q')   (congruence du conséquent ; P⇒Q = ¬P∨Q)."""
    return ou_congruence(_equiv_refl(non(p)), thm_eq)


def _rearrange_abc(a, b, c):
    """⊢ (A et (B et C)) ⇔ (B et (A et C))."""
    h = N.assume(et(a, et(b, c)))
    bc = cd(h)
    fwd = N.loi_deduction(et(a, et(b, c)),
                          conjonction_intro(cg(bc), conjonction_intro(cg(h), cd(bc))))
    h2 = N.assume(et(b, et(a, c)))
    ac = cd(h2)
    bwd = N.loi_deduction(et(b, et(a, c)),
                          conjonction_intro(cg(ac), conjonction_intro(cg(h2), cd(ac))))
    return conjonction_intro(fwd, bwd)


# ── instances d'axiomes ──────────────────────────────────────────────────────
def _inst_diff(e, x, z):
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_DIFF)
    return instancie(instancie(instancie(ax, e), x), z)


def _inst_reunion(f, i, z):
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_REUNION_FAM)
    return instancie(instancie(instancie(ax, f), i), z)


def _inst_inter(f, i, z):
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_INTER_FAM)
    return instancie(instancie(instancie(ax, f), i), z)


def _inst_compl(e, f, i):
    """⊢ (E∖X·)_i = E∖X_i   (valeur de la famille des complémentaires)."""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_COMPL_FAM)
    return instancie(instancie(instancie(ax, e), f), i)


def _membre_compl(e, f, i, z):
    """⊢ (z ∈ (E∖X·)_i) ⇔ (z∈E et ¬(z∈X_i)).

    Combine l'égalité de valeur (E∖X·)_i = E∖X_i (Leibniz/S6) avec la
    caractérisation de la différence E∖X_i."""
    vz = var(z) if isinstance(z, str) else z
    Xc = E.valeur_famille(E.complement_famille(e, f), i)   # (E∖X·)_i
    Xd = E.difference(e, E.valeur_famille(f, i))           # E∖X_i
    eq_val = _inst_compl(e, f, i)                          # (E∖X·)_i = E∖X_i
    # z∈(E∖X·)_i ⇔ z∈(E∖X_i)   via S6 sur R{w} = (z∈w)
    R = appartient(vz, var("w"))
    membre_eq = N.modus_ponens(eq_val, N.s6(Xc, Xd, "w", R))
    # z∈(E∖X_i) ⇔ (z∈E et ¬(z∈X_i))
    return etr(membre_eq, _inst_diff(e, E.valeur_famille(f, i), vz))


# ── De Morgan des familles ───────────────────────────────────────────────────
# @livre Ch.II §4.4 Prop.5 | E II.26 L.3-15 | PDF p.77
def de_morgan_inter_famille(e="E", f="f", i="I"):
    """⊢ E∖(⋂_{ι∈I} X_ι) = ⋃_{ι∈I} (E∖X_ι).   (E.II.4, Prop. 5, seconde formule.)

    X_ι = valeur_famille(f, ι) ; (E∖X_ι)_{ι∈I} = complement_famille(E, f)."""
    vE, vf, vI, vz, vi = var(e), var(f), var(i), var("z"), var("i")
    Xi = E.valeur_famille(vf, vi)
    zE, zXi, iI = appartient(vz, vE), appartient(vz, Xi), appartient(vi, vI)
    inter = E.inter_famille(vf, vI)
    compl = E.complement_famille(vE, vf)

    # ¬(z∈⋂X) ⇔ (∃i)(i∈I et ¬(z∈X_i))
    body_imp = impl(iI, zXi)
    neg_dn = esym(_dn_equiv(existe("i", non(body_imp))))      # ¬(∀i)body ⇔ (∃i)¬body
    neg_cong = congruence_existe(_non_impl(iI, zXi), "i")     # (∃i)¬body ⇔ (∃i)(iI et ¬zXi)
    neg_inter = equiv_neg(_inst_inter(vf, vI, vz))            # ¬(z∈⋂X) ⇔ ¬(∀i)body
    neg_chain = etr(neg_inter, etr(neg_dn, neg_cong))         # ¬(z∈⋂X) ⇔ (∃i)(iI et ¬zXi)

    # LHS : z∈E∖(⋂X) ⇔ (∃i)(iI et (z∈E et ¬zXi))
    diff = _inst_diff(vE, inter, vz)                          # ⇔ (z∈E et ¬(z∈⋂X))
    inner = et(iI, non(zXi))
    left = etr(diff, et_congruence_droite(zE, neg_chain))     # ⇔ (z∈E et (∃i)inner)
    push = et_existe_droite(zE, "i", inner)                   # (z∈E et (∃i)inner) ⇔ (∃i)(z∈E et inner)
    rearr = congruence_existe(_rearrange_abc(zE, iI, non(zXi)), "i")
    cu = N.generalisation("z", etr(left, etr(push, rearr)))   # ⇔ (∃i)(iI et (z∈E et ¬zXi))

    # RHS : z∈⋃(E∖X·) ⇔ (∃i)(iI et (z∈E et ¬zXi))
    reun = _inst_reunion(compl, vI, vz)                       # ⇔ (∃i)(iI et z∈(E∖X·)_i)
    body_cong = congruence_existe(et_congruence_droite(iI, _membre_compl(vE, vf, vi, vz)), "i")
    cv = N.generalisation("z", etr(reun, body_cong))

    return egalite_par_extension(cu, cv, E.difference(vE, inter),
                                 E.reunion_famille(compl, vI))


def _non_existe(i, r):
    """⊢ ¬(∃i)R ⇔ (∀i)¬R   (C29 ; (∀i)¬R = ¬(∃i)¬¬R, recollé par dne)."""
    return equiv_neg(congruence_existe(_dn_equiv(r), i))


def _distrib_et_pourtout(p, ii, q, idx):
    """{(∃i)(i∈I)} ⊢ (P et (∀i)(i∈I ⇒ Q)) ⇔ (∀i)(i∈I ⇒ (P et Q)).

    P = p (idx non libre dans P) ; i∈I = ii ; Q = q. L'hypothèse de non-vacuité
    (∃i)(i∈I) sert au seul sens ⇐ (extraire P d'un témoin d'indice)."""
    vidx = var(idx)
    FA_Q = pourtout(idx, impl(ii, q))                  # (∀i)(i∈I⇒Q)
    FA_PQ = pourtout(idx, impl(ii, et(p, q)))          # (∀i)(i∈I⇒(P et Q))
    # ── sens ⇒  (sans hypothèse) ──
    hf = N.assume(et(p, FA_Q))
    pf = cg(hf)
    iIQ = instancie(cd(hf), vidx)                      # i∈I⇒Q
    hii = N.assume(ii)
    pq = conjonction_intro(pf, N.modus_ponens(hii, iIQ))
    inner = N.loi_deduction(ii, pq)                    # i∈I⇒(P et Q)
    fwd = N.loi_deduction(et(p, FA_Q), N.generalisation(idx, inner))
    # ── sens ⇐  ({(∃i)(i∈I)}) ──
    hb = N.assume(FA_PQ)
    instb = instancie(hb, vidx)                        # i∈I⇒(P et Q)
    hii2 = N.assume(ii)
    pPQ = N.modus_ponens(hii2, instb)
    iIQ2 = N.loi_deduction(ii, cd(pPQ))                # i∈I⇒Q  {hb}
    faQ = N.generalisation(idx, iIQ2)                  # (∀i)(i∈I⇒Q)  {hb}
    iI_imp_P = N.loi_deduction(ii, cg(N.modus_ponens(N.assume(ii), instb)))  # i∈I⇒P {hb}
    P_thm = existe_elimination(iI_imp_P, idx)          # (∃i)(i∈I)⇒P  {hb}
    P_proved = N.modus_ponens(N.assume(existe(idx, ii)), P_thm)             # P  {hb, (∃i)i∈I}
    bwd = N.loi_deduction(FA_PQ, conjonction_intro(P_proved, faQ))
    return conjonction_intro(fwd, bwd)


# @livre Ch.II §4.4 Prop.5 | E II.26 L.3-15 | PDF p.77
def de_morgan_reunion_famille(e="E", f="f", i="I"):
    """{(∃ι)(ι∈I)} ⊢ E∖(⋃_{ι∈I} X_ι) = ⋂_{ι∈I} (E∖X_ι).

    (E.II.4, Prop. 5, première formule.) Théorème CONDITIONNEL : l'hypothèse de
    non-vacuité I≠∅ est nécessaire avec l'axiome ⋂ « Déf. 2 » (sans la clause
    z∈E) — pour I=∅, ⋂_{ι∈∅}(E∖X_ι) serait l'univers, ≠ E∖(⋃_{ι∈∅}X_ι)=E. Cette
    hypothèse correspond au cadre « parties de E » de Bourbaki (Déf. 3)."""
    vE, vf, vI, vz, vi = var(e), var(f), var(i), var("z"), var("i")
    Xi = E.valeur_famille(vf, vi)
    zE, zXi, iI = appartient(vz, vE), appartient(vz, Xi), appartient(vi, vI)
    reun = E.reunion_famille(vf, vI)
    compl = E.complement_famille(vE, vf)

    # ¬(z∈⋃X) ⇔ (∀i)(i∈I ⇒ ¬(z∈X_i))
    body_et = et(iI, zXi)
    neg_reun = equiv_neg(_inst_reunion(vf, vI, vz))          # ¬(z∈⋃X) ⇔ ¬(∃i)(iI et zXi)
    neg_ex = _non_existe("i", body_et)                       # ¬(∃i)(iI et zXi) ⇔ (∀i)¬(iI et zXi)
    n_et = _neg_et_to_imp(iI, zXi)                            # ¬(iI et zXi) ⇔ (iI⇒¬zXi)
    forall_cong = congruence_pour_tout(n_et, "i")            # (∀i)¬(iI et zXi) ⇔ (∀i)(iI⇒¬zXi)
    neg_chain = etr(neg_reun, etr(neg_ex, forall_cong))      # ¬(z∈⋃X) ⇔ (∀i)(iI⇒¬zXi)

    # LHS : z∈E∖(⋃X) ⇔ (∀i)(iI⇒(z∈E et ¬zXi))   (sous H)
    diff = _inst_diff(vE, reun, vz)                          # ⇔ (z∈E et ¬(z∈⋃X))
    left0 = etr(diff, et_congruence_droite(zE, neg_chain))   # ⇔ (z∈E et (∀i)(iI⇒¬zXi))
    distrib = _distrib_et_pourtout(zE, iI, non(zXi), "i")    # {H} ⇔ (∀i)(iI⇒(z∈E et ¬zXi))
    cu = N.generalisation("z", etr(left0, distrib))

    # RHS : z∈⋂(E∖X·) ⇔ (∀i)(iI⇒(z∈E et ¬zXi))
    inter_c = _inst_inter(compl, vI, vz)                     # ⇔ (∀i)(iI⇒ z∈(E∖X·)_i)
    body_cong = congruence_pour_tout(
        _imp_congruence_droite(iI, _membre_compl(vE, vf, vi, vz)), "i")
    cv = N.generalisation("z", etr(inter_c, body_cong))

    return egalite_par_extension(cu, cv, E.difference(vE, reun),
                                 E.inter_famille(compl, vI))


__all__ = ["de_morgan_inter_famille", "de_morgan_reunion_famille"]
