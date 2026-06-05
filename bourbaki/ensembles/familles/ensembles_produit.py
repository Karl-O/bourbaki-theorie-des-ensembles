"""§II.2.2 — Produit de deux ensembles : théorèmes (sens ne requérant pas pr₁/pr₂).

z∈X×Y ⇔ (∃x)(∃y)(z=(x,y) et x∈X et y∈Y)  (AXIOME_PRODUIT, légitimé par le
Théorème 1 via S8 + l'unicité par A1, comme AXIOME_REUNION). On prouve ici la
Proposition 2 (sens facile) — monotonie du produit pour l'inclusion.
"""
from __future__ import annotations

from bourbaki.logique.formule import var, egal, et, ou, non, impl, appartient, existe, inclus, subst_f
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.logique.tactiques.tactiques_abrege import syllogisme
from bourbaki.logique.tactiques.tactiques_abrege2 import (conjonction_intro, conjonction_elim_gauche,
                               conjonction_elim_droite, equivalence_avant,
                               equivalence_arriere, instancie, contraposition,
                               projection_gauche, projection_droite, cas, tiers_exclu)
from bourbaki.logique.tactiques.tactiques_abrege_quantif import (monotonie_existe, existe_elimination,
                                      alpha_pour_tout, alpha_existe)
from bourbaki.logique.tactiques.tactiques_abrege_egalite import composer_egalites, congruence_terme
from bourbaki.ensembles.fonctions.ensembles_projections import projection_premiere, projection_seconde
from bourbaki.ensembles.base.ensembles_vide import vide_ssi_sans_element, non_vide_ssi_element


def _instance_produit(gx, gy, z):
    """⊢ (z ∈ gx×gy) ⇔ (∃x)(∃y)(z=(x,y) et x∈gx et y∈gy)."""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_PRODUIT)
    return instancie(instancie(instancie(ax, gx), gy), z)


def produit_inclusion_facile(a="A", b="B", ap="Ap", bp="Bp"):
    """⊢ ((A'⊂A) et (B'⊂B)) ⇒ (A'×B' ⊂ A×B).  (Proposition 2, sens direct.)"""
    vA, vB, vAp, vBp = var(a), var(b), var(ap), var(bp)
    vp, vq, vz = var("p"), var("q"), var("z")
    hyp = et(inclus(vAp, vA), inclus(vBp, vB))                  # (A'⊂A) et (B'⊂B)
    h = N.assume(hyp)
    # des inclusions, par ∀-élim : p∈A'⇒p∈A et q∈B'⇒q∈B
    pap_pa = instancie(conjonction_elim_gauche(h), vp)          # p∈A' ⇒ p∈A
    qbp_qb = instancie(conjonction_elim_droite(h), vq)          # q∈B' ⇒ q∈B
    eq = egal(vz, E.couple(vp, vq))                            # z=(p,q)
    ante = et(et(eq, appartient(vp, vAp)), appartient(vq, vBp))
    ha = N.assume(ante)
    eq_thm = conjonction_elim_gauche(conjonction_elim_gauche(ha))   # z=(p,q)
    pap = conjonction_elim_droite(conjonction_elim_gauche(ha))      # p∈A'
    qbp = conjonction_elim_droite(ha)                              # q∈B'
    conc = conjonction_intro(conjonction_intro(eq_thm, N.modus_ponens(pap, pap_pa)),
                             N.modus_ponens(qbp, qbp_qb))           # z=(p,q) et p∈A et q∈B
    inner = N.loi_deduction(ante, conc)                            # ⇒ (hyp {h})
    mono = monotonie_existe(monotonie_existe(inner, "q"), "p")     # (∃p∃q …A'B') ⇒ (∃p∃q …AB)
    instAp = _instance_produit(vAp, vBp, vz)                       # z∈A'×B' ⇔ ∃∃…A'B'
    instA = _instance_produit(vA, vB, vz)                          # z∈A×B  ⇔ ∃∃…AB
    z_imp = syllogisme(equivalence_avant(instAp),
                       syllogisme(mono, equivalence_arriere(instA)))   # z∈A'×B' ⇒ z∈A×B
    gen = N.generalisation("z", z_imp)                            # A'×B' ⊂ A×B
    return N.loi_deduction(hyp, gen)


def couple_dans_produit(u="u", v="v", a="A", b="B"):
    """⊢ (u∈A et v∈B) ⇒ ((u,v) ∈ A×B).   (u, v distincts de x, y.)"""
    vu, vv, vA, vB = var(u), var(v), var(a), var(b)
    inst = _instance_produit(vA, vB, E.couple(vu, vv))   # (u,v)∈A×B ⇔ (∃p)(∃q)((u,v)=(p,q) et p∈A et q∈B)
    pinner = et(et(egal(E.couple(vu, vv), E.couple(var("p"), var("q"))),
                   appartient(var("p"), vA)), appartient(var("q"), vB))
    h = N.assume(et(appartient(vu, vA), appartient(vv, vB)))
    # corps témoin (p:=u, q:=v) : (u,v)=(u,v) et u∈A et v∈B
    temoin = conjonction_intro(conjonction_intro(N.reflexivite(E.couple(vu, vv)),
                                                 conjonction_elim_gauche(h)),
                               conjonction_elim_droite(h))
    gbody = subst_f(vu, "p", pinner)                     # (u|p)Pinner ; corps après ∃p
    qq = N.modus_ponens(temoin, N.s5(gbody, vv, "q"))    # (∃q)(u|p)Pinner
    full = N.modus_ponens(qq, N.s5(existe("q", pinner), vu, "p"))   # (∃p)(∃q)Pinner
    dans = N.modus_ponens(full, equivalence_arriere(inst))         # (u,v)∈A×B
    return N.loi_deduction(et(appartient(vu, vA), appartient(vv, vB)), dans)


def couple_dans_produit_ssi(u="u", v="v", a="A", b="B"):
    """⊢ ((u,v) ∈ A×B) ⇔ (u∈A et v∈B).   (u, v noms OU termes, distincts de p, q.)"""
    from bourbaki.logique.formule import Terme
    from bourbaki.logique.tactiques.tactiques_abrege2 import equivalence_transitivite
    from bourbaki.logique.tactiques.tactiques_abrege_egalite import congruence_terme
    from bourbaki.ensembles.base.ensembles_couples import couple_egal_implique_composantes
    vu = u if isinstance(u, Terme) else var(u)
    vv = v if isinstance(v, Terme) else var(v)
    vA = a if isinstance(a, Terme) else var(a)
    vB = b if isinstance(b, Terme) else var(b)
    vp, vq = var("p"), var("q")
    inst = _instance_produit(vA, vB, E.couple(vu, vv))   # (u,v)∈A×B ⇔ (∃p)(∃q)((u,v)=(p,q) et p∈A et q∈B)
    body = et(et(egal(E.couple(vu, vv), E.couple(vp, vq)), appartient(vp, vA)),
              appartient(vq, vB))

    # ── ⇒ : (∃p)(∃q)body ⇒ (u∈A et v∈B) ────────────────────────────────────────
    hb = N.assume(body)
    comps = N.modus_ponens(conjonction_elim_gauche(conjonction_elim_gauche(hb)),
                           couple_egal_implique_composantes(vu, vv, "p", "q"))   # u=p et v=q
    uA = N.modus_ponens(conjonction_elim_droite(conjonction_elim_gauche(hb)),    # p∈A
                        equivalence_arriere(N.modus_ponens(
                            conjonction_elim_gauche(comps),                     # u=p
                            N.s6(vu, vp, "w", appartient(var("w"), vA)))))      # u∈A
    vB_in = N.modus_ponens(conjonction_elim_droite(hb),                         # q∈B
                           equivalence_arriere(N.modus_ponens(
                               conjonction_elim_droite(comps),                 # v=q
                               N.s6(vv, vq, "w", appartient(var("w"), vB)))))   # v∈B
    avant = existe_elimination(existe_elimination(
        N.loi_deduction(body, conjonction_intro(uA, vB_in)), "q"), "p")

    # ── ⇐ : (u∈A et v∈B) ⇒ (∃p)(∃q)body ────────────────────────────────────────
    h = N.assume(et(appartient(vu, vA), appartient(vv, vB)))
    temoin = conjonction_intro(conjonction_intro(N.reflexivite(E.couple(vu, vv)),
                                                 conjonction_elim_gauche(h)),
                               conjonction_elim_droite(h))    # (u,v)=(u,v) et u∈A et v∈B
    gbody = subst_f(vu, "p", body)
    full = N.modus_ponens(N.modus_ponens(temoin, N.s5(gbody, vv, "q")),
                          N.s5(existe("q", body), vu, "p"))   # (∃p)(∃q)body
    arriere = N.loi_deduction(et(appartient(vu, vA), appartient(vv, vB)), full)

    return equivalence_transitivite(inst, conjonction_intro(avant, arriere))


def produit_projections(a="A", b="B", z="z"):
    """⊢ (z ∈ A×B) ⇒ (pr₁z ∈ A et pr₂z ∈ B).   (z appartient au produit ⇒ ses
    projections sont dans les facteurs — sens utilisé dans les Prop. 2-3.
    z : nom de variable ou TERME quelconque sans p, q libres.)"""
    from bourbaki.logique.formule import Terme
    vA, vB = var(a), var(b)
    vz = z if isinstance(z, Terme) else var(z)
    vp, vq = var("p"), var("q")
    ante = et(et(egal(vz, E.couple(vp, vq)), appartient(vp, vA)), appartient(vq, vB))
    ha = N.assume(ante)
    zpq = conjonction_elim_gauche(conjonction_elim_gauche(ha))   # z=(p,q)
    pA = conjonction_elim_droite(conjonction_elim_gauche(ha))    # p∈A
    qB = conjonction_elim_droite(ha)                            # q∈B
    # pr₁z = pr₁((p,q)) = p, puis pr₁z∈A
    pr1z_p = composer_egalites(
        N.modus_ponens(zpq, congruence_terme(vz, E.couple(vp, vq), E.pr1(var("w")))),
        projection_premiere("p", "q"))                          # pr₁z = p
    pr1z_in = N.modus_ponens(pA, equivalence_arriere(
        N.modus_ponens(pr1z_p, N.s6(E.pr1(vz), vp, "w", appartient(var("w"), vA)))))
    pr2z_q = composer_egalites(
        N.modus_ponens(zpq, congruence_terme(vz, E.couple(vp, vq), E.pr2(var("w")))),
        projection_seconde("p", "q"))                           # pr₂z = q
    pr2z_in = N.modus_ponens(qB, equivalence_arriere(
        N.modus_ponens(pr2z_q, N.s6(E.pr2(vz), vq, "w", appartient(var("w"), vB)))))
    conc = conjonction_intro(pr1z_in, pr2z_in)                  # pr₁z∈A et pr₂z∈B
    inner = N.loi_deduction(ante, conc)
    chaine = existe_elimination(existe_elimination(inner, "q"), "p")   # (∃p∃q…) ⇒ conc
    inst = _instance_produit(vA, vB, vz)                        # z∈A×B ⇔ (∃p∃q…)
    return syllogisme(equivalence_avant(inst), chaine)          # z∈A×B ⇒ (pr₁z∈A et pr₂z∈B)


def produit_inclusion_reciproque_gauche(a="A", b="B", ap="Ap", bp="Bp"):
    """⊢ (B'≠∅) ⇒ ((A'×B' ⊂ A×B) ⇒ (A' ⊂ A)).   (Proposition 2, réciproque, à gauche.)"""
    vA, vB, vAp, vBp = var(a), var(b), var(ap), var(bp)
    vz, vv = var("z"), var("v")                            # z : élément de A' ; v : témoin de B'
    hBp = N.assume(non(egal(vBp, E.VIDE)))
    bp_ex = N.modus_ponens(N.modus_ponens(hBp, equivalence_avant(non_vide_ssi_element(vBp))),
                           equivalence_avant(alpha_existe("z", "v", appartient(vz, vBp))))  # (∃v)(v∈B')
    hsub = N.assume(inclus(E.produit(vAp, vBp), E.produit(vA, vB)))    # A'×B'⊂A×B (liant z)
    hz = N.assume(appartient(vz, vAp))                    # z∈A'
    # (v∈B') ⇒ z∈A  (sous {z∈A', hsub})
    zv_in_AB = N.modus_ponens(
        N.modus_ponens(conjonction_intro(hz, N.assume(appartient(vv, vBp))),
                       couple_dans_produit("z", "v", ap, bp)),       # (z,v)∈A'×B'
        instancie(hsub, E.couple(vz, vv)))                            # (z,v)∈A×B
    pr1zv_in_A = conjonction_elim_gauche(
        N.modus_ponens(zv_in_AB, produit_projections(a, b, E.couple(vz, vv))))   # pr₁((z,v))∈A
    zA = N.modus_ponens(pr1zv_in_A, equivalence_avant(N.modus_ponens(
        projection_premiere("z", "v"),
        N.s6(E.pr1(E.couple(vz, vv)), vz, "w", appartient(var("w"), vA)))))       # z∈A
    z_in_A = N.modus_ponens(bp_ex, existe_elimination(
        N.loi_deduction(appartient(vv, vBp), zA), "v"))               # z∈A (élim témoin)
    a_sub = N.generalisation("z", N.loi_deduction(appartient(vz, vAp), z_in_A))   # A'⊂A
    return N.loi_deduction(non(egal(vBp, E.VIDE)),
        N.loi_deduction(inclus(E.produit(vAp, vBp), E.produit(vA, vB)), a_sub))


def produit_inclusion_reciproque_droite(a="A", b="B", ap="Ap", bp="Bp"):
    """⊢ (A'≠∅) ⇒ ((A'×B' ⊂ A×B) ⇒ (B' ⊂ B)).   (Proposition 2, réciproque, à droite.)"""
    vA, vB, vAp, vBp = var(a), var(b), var(ap), var(bp)
    vz, vv = var("z"), var("v")                            # z : élément de B' ; v : témoin de A'
    hAp = N.assume(non(egal(vAp, E.VIDE)))
    ap_ex = N.modus_ponens(N.modus_ponens(hAp, equivalence_avant(non_vide_ssi_element(vAp))),
                           equivalence_avant(alpha_existe("z", "v", appartient(vz, vAp))))  # (∃v)(v∈A')
    hsub = N.assume(inclus(E.produit(vAp, vBp), E.produit(vA, vB)))
    hz = N.assume(appartient(vz, vBp))                    # z∈B'
    vz_in_AB = N.modus_ponens(
        N.modus_ponens(conjonction_intro(N.assume(appartient(vv, vAp)), hz),
                       couple_dans_produit("v", "z", ap, bp)),       # (v,z)∈A'×B'
        instancie(hsub, E.couple(vv, vz)))                            # (v,z)∈A×B
    pr2vz_in_B = conjonction_elim_droite(
        N.modus_ponens(vz_in_AB, produit_projections(a, b, E.couple(vv, vz))))   # pr₂((v,z))∈B
    zB = N.modus_ponens(pr2vz_in_B, equivalence_avant(N.modus_ponens(
        projection_seconde("v", "z"),
        N.s6(E.pr2(E.couple(vv, vz)), vz, "w", appartient(var("w"), vB)))))       # z∈B
    z_in_B = N.modus_ponens(ap_ex, existe_elimination(
        N.loi_deduction(appartient(vv, vAp), zB), "v"))
    b_sub = N.generalisation("z", N.loi_deduction(appartient(vz, vBp), z_in_B))   # B'⊂B
    return N.loi_deduction(non(egal(vAp, E.VIDE)),
        N.loi_deduction(inclus(E.produit(vAp, vBp), E.produit(vA, vB)), b_sub))


def produit_vide_si(a="A", b="B"):
    """⊢ (A=∅ ou B=∅) ⇒ A×B=∅.   (Proposition 3, sens ⇐.)"""
    vA, vB, vz = var(a), var(b), var("z")
    disj = ou(egal(vA, E.VIDE), egal(vB, E.VIDE))
    hd = N.assume(disj)
    pp = produit_projections(a, b, "z")                    # z∈A×B ⇒ (pr₁z∈A et pr₂z∈B)
    vide_ab = equivalence_arriere(vide_ssi_sans_element(E.produit(vA, vB)))   # (∀z)¬(z∈A×B) ⇒ A×B=∅

    def branche(set_var, proj_term, sel):
        z_proj = syllogisme(pp, sel(appartient(E.pr1(vz), vA), appartient(E.pr2(vz), vB)))
        h = N.assume(egal(set_var, E.VIDE))
        sans = N.modus_ponens(h, equivalence_avant(vide_ssi_sans_element(set_var)))   # (∀z)¬(z∈set)
        nz = N.modus_ponens(instancie(sans, proj_term), contraposition(z_proj))       # ¬(z∈A×B)
        return N.loi_deduction(egal(set_var, E.VIDE),
                               N.modus_ponens(N.generalisation("z", nz), vide_ab))

    brA = branche(vA, E.pr1(vz), projection_gauche)        # (A=∅)⇒(A×B=∅)
    brB = branche(vB, E.pr2(vz), projection_droite)        # (B=∅)⇒(A×B=∅)
    return N.loi_deduction(disj, cas(hd, brA, brB))


def produit_vide_dur(a="A", b="B"):
    """⊢ A×B=∅ ⇒ (A=∅ ou B=∅).   (Proposition 3, sens ⇒.)"""
    vA, vB, vz, vv = var(a), var(b), var("z"), var("v")
    prod_vide = egal(E.produit(vA, vB), E.VIDE)
    hAB = N.assume(prod_vide)
    te = tiers_exclu(egal(vA, E.VIDE))                     # (A=∅) ou ¬(A=∅)
    brA = N.s2(egal(vA, E.VIDE), egal(vB, E.VIDE))         # (A=∅) ⇒ (A=∅ ou B=∅)
    # branche ¬(A=∅) : il existe z∈A ; alors B est vide, donc (A=∅ ou B=∅)
    h_nA = N.assume(non(egal(vA, E.VIDE)))
    pA_ex = N.modus_ponens(h_nA, equivalence_avant(non_vide_ssi_element(vA)))   # (∃z)(z∈A)
    z_thm = N.assume(appartient(vz, vA))                  # z∈A
    sans_AB = N.modus_ponens(hAB, equivalence_avant(vide_ssi_sans_element(E.produit(vA, vB))))
    cdp = couple_dans_produit("z", "v", a, b)             # (z∈A et v∈B) ⇒ (z,v)∈A×B
    vB_imp = N.loi_deduction(appartient(vv, vB),
                             N.modus_ponens(conjonction_intro(z_thm, N.assume(appartient(vv, vB))), cdp))
    nvB = N.modus_ponens(instancie(sans_AB, E.couple(vz, vv)), contraposition(vB_imp))   # ¬(v∈B)
    genz = N.modus_ponens(N.generalisation("v", nvB),
                          equivalence_avant(alpha_pour_tout("v", "z", non(appartient(vv, vB)))))
    B_vide = N.modus_ponens(genz, equivalence_arriere(vide_ssi_sans_element(vB)))   # B=∅
    or_t = N.modus_ponens(N.modus_ponens(B_vide, N.s2(egal(vB, E.VIDE), egal(vA, E.VIDE))),
                          N.s3(egal(vB, E.VIDE), egal(vA, E.VIDE)))                  # (A=∅ ou B=∅)
    elim = existe_elimination(N.loi_deduction(appartient(vz, vA), or_t), "z")        # (∃z)(z∈A)⇒…
    brB = N.loi_deduction(non(egal(vA, E.VIDE)), N.modus_ponens(pA_ex, elim))
    return N.loi_deduction(prod_vide, cas(te, brA, brB))


def produit_vide(a="A", b="B"):
    """⊢ (A×B = ∅) ⇔ (A = ∅ ou B = ∅).   (Proposition 3, E.II.34.)"""
    return conjonction_intro(produit_vide_dur(a, b), produit_vide_si(a, b))


__all__ = ["produit_inclusion_facile", "couple_dans_produit",
           "couple_dans_produit_ssi", "produit_projections",
           "produit_inclusion_reciproque_gauche", "produit_inclusion_reciproque_droite",
           "produit_vide_si", "produit_vide_dur", "produit_vide"]
