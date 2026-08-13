"""§IV.1.2 — CST1-IDENTITÉ GÉNÉRÉ : ⟨Δ_{E₁},…⟩^S = Δ_{S(E)}, par schéma concret.

────────────────────────────────────────────────────────────────────────────────
Le pendant IDENTITÉ du générateur CST1 (ensembles_cst1_genere) : pour chaque
schéma concret S, l'extension canonique RÉELLE de la famille des identités est
LA diagonale de l'échelon — le Theoreme noyau, attendu CLOS (0 hyp) :

    cst1_identite_prouve(s, bases)  ⊢  ⟨Δ_{E₁},…,Δ_{Eₙ}⟩^S_réel = Δ_{S(E₁,…,Eₙ)}.

Pièces : (i) image_diagonale_sous {X∈𝔓A} ⊢ Δ_A⟨X⟩=X ; (ii) identite_parties
ext_P(Δ_A,A)=Δ_𝔓A [CLOS] ; (iii) identite_produit prod(Δ_A,Δ_B,A,B)=Δ_{A×B}
[CLOS] ; (iv) la récurrence par étage (variable-par-étage, congruences-IH).
Briques diagonale (equipotence, NOMS-seulement → wrappers noms→termes ; valeur
porte une hyp → décharge en antécédent _dval_t) : membre:53, fonctionnelle:105,
domaine:129, valeur:211 ; est_un_graphe(Δ) DÉRIVÉ ici (_diag_est_graphe, depuis
AXIOME_DIAGONALE) ; couple_egal_projections (couple_caracterisation:227).
INVARIANT : theorie_ensembles()=22 ; rien postulé.
"""
from __future__ import annotations

from typing import Sequence

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, et, appartient, existe,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, instancie,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.outil_portage import (
    porter_aux_termes,
)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import (
    existe_elimination,
)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
    symetrie, composer_egalites, congruence_terme,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.equipotence.ensembles_equipotence import (
    diagonale_membre, diagonale_fonctionnelle, diagonale_domaine, diagonale_valeur,
)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_theoremes import (
    egalite_par_extension,
)
from bourbaki.iv_structures.iv_1_structures_isomorphismes.ensembles_extension_echelon_reelle import (
    ext_parties_reelle, produit_app_reelle, terme_ext_parties, terme_produit_app,
)
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_6_fonction_terme.ensembles_graphe_terme_egalite import (
    egalite_graphe_terme,
)
from bourbaki.iv_structures.iv_1_structures_isomorphismes.ensembles_especes_echelon import (
    Schema, construction_echelon,
)
from bourbaki.iv_structures.iv_2_morphismes_structures_derivees.cst_criteres.ensembles_cst1_genere import (
    extension_canonique_reelle,
)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def _cut(thm, *preuves):
    for p in preuves:
        c = p.conclusion
        if c in thm.hypotheses:
            thm = N.modus_ponens(p, N.loi_deduction(c, thm))
    return thm


def _nt(base_fn, noms, termes):
    """Motif noms→termes : construire la brique aux NOMS, puis la porter.

    Délègue à `porter_aux_termes`.  Ces briques-ci sont closes, donc le portage
    se réduit à « généraliser puis instancier » — mais passer par la tactique
    les rend ROBUSTES : si l'une gagnait un jour une hypothèse mentionnant l'un
    des noms, la version écrite à la main lèverait (généralisation illicite)
    alors que celle-ci la déchargerait et la ré-assumerait substituée."""
    return porter_aux_termes(base_fn(*noms),
                             {n: _t(t) for n, t in zip(noms, termes)})


def _dval_t(set_t, point_t):
    """diagonale_valeur aux TERMES : {p∈X} ⊢ Δ_X(p)=p.

    Ce helper était le motif « décharger l'hypothèse portante, généraliser,
    instancier, ré-assumer » écrit à la main ; il délègue désormais à la
    tactique générique `porter_aux_termes` (i_2_theoremes/tactiques/
    outil_portage), qui découvre elle-même l'hypothèse portante au lieu qu'on
    la nomme.  Comportement identique — l'énoncé produit est le même terme."""
    return porter_aux_termes(diagonale_valeur("Xdv", "udv"),
                             {"udv": _t(point_t), "Xdv": _t(set_t)})


def _diag_est_graphe(set_t):
    """⊢ est_un_graphe(Δ_X), X TERME.                              [CLOS, 0 hyp].

    z∈Δ_X ⇒ ∃d0(d0∈X ∧ z=(d0,d0)) [AXIOME_DIAGONALE] ⇒ ∃x∃y(z=(x,y))
    (S5 y:=d0 puis x:=d0, existe_elimination sur d0)."""
    vX, vz = _t(set_t), var("z")
    DX = E.diagonale(vX)
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_DIAGONALE)
    car = instancie(instancie(ax, vX), vz)
    h = N.assume(appartient(vz, DX))
    ex = N.modus_ponens(h, equivalence_avant(car))
    corps = et(appartient(var("d0"), vX), egal(vz, E.couple(var("d0"), var("d0"))))
    hb = N.assume(corps)
    j1 = N.modus_ponens(conjonction_elim_droite(hb),
                        N.s5(egal(vz, E.couple(var("d0"), var("y"))),
                             var("d0"), "y"))
    j2 = N.modus_ponens(j1, N.s5(
        existe("y", egal(vz, E.couple(var("x"), var("y")))), var("d0"), "x"))
    ec = N.modus_ponens(ex, existe_elimination(
        N.loi_deduction(corps, j2), "d0"))
    res = N.generalisation("z", N.loi_deduction(appartient(vz, DX), ec))
    assert res.conclusion == E.est_un_graphe(DX), "_diag_est_graphe : ≠ cible"
    assert not res.hypotheses, "_diag_est_graphe : NON clos"
    return res


# @livre Ch.II §5.3 Prop.- | E II.30 L.5-9 | PDF p.81  (l'image d'une partie par l'application identique : Δ_A⟨X⟩ = X)
def image_diagonale_sous(A, pt="pwid"):
    """{ pt ∈ 𝔓(A) } ⊢ image( Δ_A, pt ) = pt.               [1 hyp, A TERME ok].

    Extension au liant z : z∈Δ_A⟨pt⟩ ⇔ ∃x(x∈pt ∧ (x,z)∈Δ_A) ⇔ z∈pt (le membre
    de la diagonale force x=z ; réciproque par témoin z, z∈A venant de pt⊂A)."""
    vA, vpt, vz = _t(A), var(pt), var("z")
    DA = E.diagonale(vA)
    Im = E.image(DA, vpt)
    h_pt = N.assume(appartient(vpt, E.parties(vA)))
    pt_inc = N.modus_ponens(h_pt, equivalence_avant(instancie(instancie(
        N.axiome(E.theorie_ensembles(), E.AXIOME_PARTIES), vA), vpt)))   # pt⊂A
    ax_img = N.axiome(E.theorie_ensembles(), E.AXIOME_IMAGE)
    car = instancie(instancie(instancie(ax_img, DA), vpt), vz)
    #     z∈Δ_A⟨pt⟩ ⇔ ∃x(x∈pt ∧ (x,z)∈Δ_A)
    membre_xz = _nt(diagonale_membre, ["Xdm", "udm", "vdm"],
                    [vA, var("x"), vz])                    # ((x,z)∈Δ_A) ⇔ (x∈A ∧ x=z)

    # → : sous le témoin x : x∈pt ∧ (x,z)∈Δ_A ⇒ z∈pt (x=z + S6)
    corps = et(appartient(var("x"), vpt), appartient(E.couple(var("x"), vz), DA))
    hb = N.assume(corps)
    x_pt = conjonction_elim_gauche(hb)
    dm = N.modus_ponens(conjonction_elim_droite(hb), equivalence_avant(membre_xz))
    x_eq_z = conjonction_elim_droite(dm)                   # x=z
    z_pt = N.modus_ponens(x_pt, equivalence_avant(N.modus_ponens(
        x_eq_z, N.s6(var("x"), vz, "h6i", appartient(var("h6i"), vpt)))))
    fwd_imp = existe_elimination(N.loi_deduction(corps, z_pt), "x")
    hzi = N.assume(appartient(vz, Im))
    fwd = N.loi_deduction(appartient(vz, Im), N.modus_ponens(
        N.modus_ponens(hzi, equivalence_avant(car)), fwd_imp))

    # ← : z∈pt ⇒ z∈A ⇒ (z,z)∈Δ_A ⇒ ∃x(...) ⇒ z∈Im
    hzp = N.assume(appartient(vz, vpt))
    z_A = N.modus_ponens(hzp, instancie(pt_inc, vz))       # z∈A
    membre_zz = _nt(diagonale_membre, ["Xdm", "udm", "vdm"], [vA, vz, vz])
    zz_in = N.modus_ponens(conjonction_intro(z_A, N.reflexivite(vz)),
                           equivalence_arriere(membre_zz)) # (z,z)∈Δ_A
    wit = conjonction_intro(hzp, zz_in)
    ex = N.modus_ponens(wit, N.s5(
        et(appartient(var("x"), vpt),
           appartient(E.couple(var("x"), vz), DA)), vz, "x"))
    bwd = N.loi_deduction(appartient(vz, vpt),
                          N.modus_ponens(ex, equivalence_arriere(car)))

    R = appartient(vz, vpt)
    thm_u = N.generalisation("z", conjonction_intro(fwd, bwd))
    triv = N.loi_deduction(R, N.assume(R))
    thm_v = N.generalisation("z", conjonction_intro(triv, triv))
    res = egalite_par_extension(thm_u, thm_v, Im, vpt, x="z")
    assert res.conclusion == egal(Im, vpt), "image_diagonale_sous : ≠ cible"
    assert len(res.hypotheses) == 1, "image_diagonale_sous : hyps ≠ 1"
    return res


# @livre Ch.IV §1.2 Crit.CST1 | E IV.2 L.33-34 | PDF p.205  (CST1-identité, cas 𝔓 : l'extension aux parties de l'identité est l'identité)
def identite_parties(A, xi="xg1"):
    """⊢ ext_parties_reelle(Δ_A, A) = Δ_𝔓(A).                    [CLOS, 0 hyp]."""
    vA = _t(A)
    PA = E.parties(vA)
    G = E.diagonale(PA)
    t_id = terme_ext_parties(E.diagonale(vA), xi)          # image(Δ_A, xi)

    # hyp_valeurs : (∀pw)(pw∈𝔓A ⇒ G(pw)=image(Δ_A,pw))
    vpw = var("pw")
    hpw = N.assume(appartient(vpw, PA))
    dv = _cut(_dval_t(PA, vpw), hpw)                   # Δ_𝔓A(pw)=pw
    ids = _cut(image_diagonale_sous(vA, "pw"), hpw)        # Δ_A⟨pw⟩=pw
    chain = composer_egalites(dv, N.modus_ponens(
        ids, symetrie(E.image(E.diagonale(vA), vpw), vpw)))
    fd = N.generalisation("pw", N.loi_deduction(appartient(vpw, PA), chain))

    base = egalite_graphe_terme(PA, t_id, G, xi, "pw")
    res = _cut(base,
               _diag_est_graphe(PA),
               _nt(diagonale_fonctionnelle, ["Xdf"], [PA]),
               _nt(diagonale_domaine, ["Xdd"], [PA]),
               fd)
    cible = egal(ext_parties_reelle(E.diagonale(vA), vA, xi), G)
    assert res.conclusion == cible, "identite_parties : ≠ cible"
    assert not res.hypotheses, "identite_parties : NON clos"
    return res


# @livre Ch.IV §1.2 Crit.CST1 | E IV.2 L.33-34 | PDF p.205  (CST1-identité, cas × : le produit des identités est l'identité du produit)
def identite_produit(A, B, xi="xg1"):
    """⊢ produit_app_reelle(Δ_A, Δ_B, A, B) = Δ_{A×B}.           [CLOS, 0 hyp]."""
    from bourbaki.ii_theorie_des_ensembles.ii_2_couples.ii_2_1_definition_couples.ensembles_couple_caracterisation import (
        couple_egal_projections,
    )
    from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_6_fonction_terme.ensembles_fonctorialite_produit_termes import (
        pr_dans,
    )
    vA, vB = _t(A), _t(B)
    AxB = E.produit(vA, vB)
    G = E.diagonale(AxB)
    DA, DB = E.diagonale(vA), E.diagonale(vB)
    t_id = terme_produit_app(DA, DB, xi)

    vpw = var("pw")
    p1, p2 = E.pr1(vpw), E.pr2(vpw)
    hpw = N.assume(appartient(vpw, AxB))
    dv = _cut(_dval_t(AxB, vpw), hpw)                  # Δ_{A×B}(pw)=pw
    # pw = (pr₁pw, pr₂pw)  : est_couple(pw) depuis pw∈A×B (affaiblissement + re-intro a,b)
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_PRODUIT)
    exn = N.modus_ponens(hpw, equivalence_avant(
        instancie(instancie(instancie(ax, vA), vB), vpw)))
    corps = et(et(egal(vpw, E.couple(var("p"), var("q"))),
                  appartient(var("p"), vA)), appartient(var("q"), vB))
    hb = N.assume(corps)
    eqc = conjonction_elim_gauche(conjonction_elim_gauche(hb))
    j1 = N.modus_ponens(eqc, N.s5(egal(vpw, E.couple(var("p"), var("b"))),
                                  var("q"), "b"))
    j2 = N.modus_ponens(j1, N.s5(
        existe("b", egal(vpw, E.couple(var("a"), var("b")))), var("p"), "a"))
    imp = existe_elimination(existe_elimination(
        N.loi_deduction(corps, j2), "q"), "p")
    ec = N.modus_ponens(exn, imp)                          # est_couple(pw)
    pw_eq = N.modus_ponens(ec, equivalence_arriere(couple_egal_projections(vpw)))
    #     pw = (pr₁pw, pr₂pw)
    prs = _cut(pr_dans(vpw, vA, vB), hpw)
    dva = _cut(_dval_t(vA, p1),
               conjonction_elim_gauche(prs))               # Δ_A(pr₁pw)=pr₁pw
    dvb = _cut(_dval_t(vB, p2),
               conjonction_elim_droite(prs))               # Δ_B(pr₂pw)=pr₂pw
    # cible RHS : couple(Δ_A(pr₁pw), Δ_B(pr₂pw)) — remonter depuis pw
    c1 = N.modus_ponens(N.modus_ponens(dva, symetrie(E.valeur(DA, p1), p1)),
                        congruence_terme(p1, E.valeur(DA, p1),
                                         E.couple(var("w"), p2)))
    c2 = N.modus_ponens(N.modus_ponens(dvb, symetrie(E.valeur(DB, p2), p2)),
                        congruence_terme(p2, E.valeur(DB, p2),
                                         E.couple(E.valeur(DA, p1), var("w"))))
    chain = composer_egalites(composer_egalites(
        composer_egalites(dv, pw_eq), c1), c2)
    #     G(pw) = couple(Δ_A(pr₁pw), Δ_B(pr₂pw)) = T[pw]
    fd = N.generalisation("pw", N.loi_deduction(appartient(vpw, AxB), chain))

    base = egalite_graphe_terme(AxB, t_id, G, xi, "pw")
    res = _cut(base,
               _diag_est_graphe(AxB),
               _nt(diagonale_fonctionnelle, ["Xdf"], [AxB]),
               _nt(diagonale_domaine, ["Xdd"], [AxB]),
               fd)
    cible = egal(produit_app_reelle(DA, DB, vA, vB, xi), G)
    assert res.conclusion == cible, "identite_produit : ≠ cible"
    assert not res.hypotheses, "identite_produit : NON clos"
    return res


# @livre Ch.IV §1.2 Crit.CST1 | E IV.2 L.33-34 | PDF p.205  (CST1-identité GÉNÉRÉ : ⟨Δ⟩^S = Δ_{S(E)} par récurrence sur le schéma concret)
def cst1_identite_prouve(s: Schema, bases: Sequence, xg: str = "xg"):
    """⊢ ⟨Δ_{E₁},…⟩^S_réel = Δ_{S(E₁,…,Eₙ)}   pour le schéma CONCRET s.  [CLOS]."""
    diags = [E.diagonale(_t(b)) for b in bases]
    A = construction_echelon(s, [_t(b) for b in bases])
    D = extension_canonique_reelle(s, diags, bases, xg)

    thms: list = []
    for i, (a, b) in enumerate(s.couples):
        xi = f"{xg}{i + 1}"
        if a == 0:
            thms.append(N.reflexivite(D[i]))               # D[i] = Δ_{A[i]} littéral
        elif b == 0:
            ih = thms[a - 1]
            trou = E.graphe_terme(E.parties(A[a - 1]),
                                  E.image(var("w"), var(xi)), xi)
            cong = N.modus_ponens(ih, congruence_terme(
                D[a - 1], E.diagonale(A[a - 1]), trou))
            thms.append(composer_egalites(cong, identite_parties(A[a - 1], xi)))
        else:
            ih_a, ih_b = thms[a - 1], thms[b - 1]
            AxB = E.produit(A[a - 1], A[b - 1])
            trou_a = E.graphe_terme(AxB, E.couple(
                E.valeur(var("w"), E.pr1(var(xi))),
                E.valeur(D[b - 1], E.pr2(var(xi)))), xi)
            cong_a = N.modus_ponens(ih_a, congruence_terme(
                D[a - 1], E.diagonale(A[a - 1]), trou_a))
            trou_b = E.graphe_terme(AxB, E.couple(
                E.valeur(E.diagonale(A[a - 1]), E.pr1(var(xi))),
                E.valeur(var("w"), E.pr2(var(xi)))), xi)
            cong_b = N.modus_ponens(ih_b, congruence_terme(
                D[b - 1], E.diagonale(A[b - 1]), trou_b))
            cong = composer_egalites(cong_a, cong_b)
            thms.append(composer_egalites(
                cong, identite_produit(A[a - 1], A[b - 1], xi)))
    res = thms[-1]
    cible = egal(D[-1], E.diagonale(A[-1]))
    assert res.conclusion == cible, "cst1_identite_prouve : ≠ Δ_{S(E)}"
    assert not res.hypotheses, "cst1_identite_prouve : NON clos"
    return res


__all__ = ["image_diagonale_sous", "identite_parties", "identite_produit",
           "cst1_identite_prouve"]
