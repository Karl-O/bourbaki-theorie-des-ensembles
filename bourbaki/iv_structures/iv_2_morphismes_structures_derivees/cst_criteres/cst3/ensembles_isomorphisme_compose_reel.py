"""§IV.1.5 — Composition d'isomorphismes RÉELLE : la transitivité.

────────────────────────────────────────────────────────────────────────────────
  isomorphisme_compose_reel(s, fs, gs, bases, bases_p, bases_pp, U, V, W) :
  { Q(f_i), Q(g_i), bornes CST1, U∈S(E), ⟨f⟩^S(U)=V, ⟨g⟩^S(V)=W }  ⊢
      est_bijection_de(⟨g∘f⟩^S, S(E), S(E''))  ∧  ⟨g∘f⟩^S(U) = W
— le composé de deux isomorphismes réels est un isomorphisme réel, ET son
graphe est LUI-MÊME une extension canonique (CST1 : ⟨g∘f⟩^S = ⟨g⟩^S∘⟨f⟩^S).
Avec la réflexivité (automorphisme_identite_reel) et la symétrie
(reciproque_isomorphisme_reel), l'isomorphie réelle est une ÉQUIVALENCE.
Bijectivité : composee_bijection_conjoints (III.3.1) sur les deux ponts
cst2 ; valeur : composition_valeur_t (3 hyps déchargées par Q) + congruences.
INVARIANT : theorie_ensembles()=22 ; rien postulé.
"""
from __future__ import annotations

from typing import Sequence

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, et, appartient,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, instancie,
)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
    symetrie, composer_egalites, congruence_terme,
)
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_4_fonctions.ensembles_fonctions import (
    valeur_dans_graphe,
)
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_8_retractions_sections.ensembles_composee_valeurs import (
    composition_valeur_t,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    est_bijection_de,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.equipotence.ensembles_composee_bijection import (
    composee_bijection,
)
from bourbaki.iv_structures.iv_1_structures_isomorphismes.ensembles_especes_echelon import (
    Schema, construction_echelon,
)
from bourbaki.iv_structures.iv_2_morphismes_structures_derivees.cst_criteres.ensembles_cst1_genere import (
    extension_canonique_reelle, cst1_termes_prouve,
)
from bourbaki.iv_structures.iv_2_morphismes_structures_derivees.cst_criteres.cst2.ensembles_cst2_genere import (
    cst2_prouve, pont_bijection_de, _q_conjoints,
)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def _cut(thm, *preuves):
    for p in preuves:
        c = p.conclusion
        if c in thm.hypotheses:
            thm = N.modus_ponens(p, N.loi_deduction(c, thm))
    return thm


# @livre Ch.IV §1.5 Prop.- | E IV.6 L.24-28 | PDF p.209  (le composé de deux isomorphismes est un isomorphisme — VERSION RÉELLE : bijectivité par composee_bijection, transport par CST1, toutes hypothèses CST déchargées)
def isomorphisme_compose_reel(s: Schema, fs: Sequence, gs: Sequence,
                              bases: Sequence, bases_p: Sequence,
                              bases_pp: Sequence, u: str = "U", v: str = "V",
                              w: str = "W", xg: str = "xg"):
    """(thm, hyps) ⊢ est_bijection_de(⟨g∘f⟩^S, S(E), S(E'')) ∧ ⟨g∘f⟩^S(U)=W."""
    fs_t = [_t(x) for x in fs]
    gs_t = [_t(x) for x in gs]
    A = construction_echelon(s, [_t(b) for b in bases])
    App = construction_echelon(s, [_t(b) for b in bases_pp])
    Ap = construction_echelon(s, [_t(b) for b in bases_p])
    SE, SEp, SEpp = A[-1], Ap[-1], App[-1]
    vU, vV, vW = _t(u), _t(v), _t(w)
    Gf = extension_canonique_reelle(s, fs_t, bases, xg)[-1]
    Gg = extension_canonique_reelle(s, gs_t, bases_p, xg)[-1]
    comps = [E.composee(g, f) for g, f in zip(gs_t, fs_t)]
    GC = extension_canonique_reelle(s, comps, bases, xg)[-1]

    qf, hqf = cst2_prouve(s, fs, bases, bases_p, xg)
    qg, hqg = cst2_prouve(s, gs, bases_p, bases_pp, xg)
    bijF = pont_bijection_de(qf, Gf, SE, SEp)
    bijG = pont_bijection_de(qg, Gg, SEp, SEpp)
    # composee_bijection : internes noms-seulement ⇒ forme implicative CLOSE
    # aux noms frais, généralisée puis instanciée aux termes (relais standard).
    cb = composee_bijection("Fc", "Gc", "Xc", "Yc", "Zc")
    cb_g = N.generalisation("Fc", N.generalisation("Gc", N.generalisation(
        "Xc", N.generalisation("Yc", N.generalisation("Zc", cb)))))
    cb_i = instancie(instancie(instancie(instancie(instancie(
        cb_g, Gf), Gg), SE), SEp), SEpp)
    comp_bij = N.modus_ponens(conjonction_intro(bijF, bijG), cb_i)
    #   bij(Gg∘Gf, S(E), S(E''))
    c1t, h1 = cst1_termes_prouve(s, fs, gs, bases, bases_p, bases_pp, xg)
    #   ⟨g∘f⟩^S = Gg∘Gf ; transport de la bijectivité (S6 arrière)
    bij = N.modus_ponens(comp_bij, equivalence_arriere(N.modus_ponens(
        c1t, N.s6(GC, E.composee(Gg, Gf), "w",
                  est_bijection_de(var("w"), SE, SEpp)))))

    # ── valeur : ⟨g∘f⟩(U) = (Gg∘Gf)(U) = Gg(Gf(U)) = Gg(V) = W ──────────────
    _, dom_f, _, img_f = _q_conjoints(qf)
    _, dom_g, _, _ = _q_conjoints(qg)
    hU = N.assume(appartient(vU, SE))
    hV = N.assume(egal(E.valeur(Gf, vU), vV))
    hW = N.assume(egal(E.valeur(Gg, vV), vW))
    dom_ax = N.axiome(E.theorie_ensembles(), E.AXIOME_DOM)

    def _ex_dom(G_t, pt, in_thm, dom_eq, dom_set):
        pt_dom = N.modus_ponens(N.modus_ponens(dom_eq, symetrie(
            E.dom(G_t), dom_set)), N.s6(dom_set, E.dom(G_t), "w",
                                        appartient(pt, var("w"))))
        return N.modus_ponens(N.modus_ponens(in_thm, equivalence_avant(pt_dom)),
                              equivalence_avant(
                                  instancie(instancie(dom_ax, G_t), pt)))

    ex1 = _ex_dom(Gf, vU, hU, dom_f, SE)                   # (∃y)(U,y)∈Gf
    GfU = E.valeur(Gf, vU)
    cplU = _cut(valeur_dans_graphe(Gf, vU), ex1)
    ax_img = N.axiome(E.theorie_ensembles(), E.AXIOME_IMAGE)
    car = instancie(instancie(instancie(ax_img, Gf), SE), GfU)
    body = et(appartient(var("x"), SE), appartient(E.couple(var("x"), GfU), Gf))
    in_img = N.modus_ponens(N.modus_ponens(conjonction_intro(hU, cplU),
                                           N.s5(body, vU, "x")),
                            equivalence_arriere(car))
    GfU_SEp = N.modus_ponens(in_img, equivalence_avant(N.modus_ponens(
        img_f, N.s6(E.image(Gf, SE), SEp, "w", appartient(GfU, var("w"))))))
    ex2 = _ex_dom(Gg, GfU, GfU_SEp, dom_g, SEp)            # (∃y)(Gf(U),y)∈Gg
    func_C = conjonction_elim_gauche(conjonction_elim_gauche(comp_bij))
    cv = _cut(composition_valeur_t(Gg, Gf, vU), ex1, ex2, func_C)
    e0 = N.modus_ponens(c1t, congruence_terme(
        GC, E.composee(Gg, Gf), E.valeur(var("w"), vU)))   # ⟨g∘f⟩(U)=(Gg∘Gf)(U)
    e2 = N.modus_ponens(hV, congruence_terme(GfU, vV, E.valeur(Gg, var("w"))))
    val = composer_egalites(composer_egalites(composer_egalites(e0, cv), e2), hW)

    res = conjonction_intro(bij, val)
    hyps = sorted(set(hqf) | set(hqg) | set(h1)
                  | {hU.conclusion, hV.conclusion, hW.conclusion}, key=str)
    cible = et(est_bijection_de(GC, SE, SEpp), egal(E.valeur(GC, vU), vW))
    assert res.conclusion == cible, "isomorphisme_compose_reel : ≠ cible"
    assert set(res.hypotheses) <= set(hyps), "isomorphisme_compose_reel : hyps"
    return res, hyps


__all__ = ["isomorphisme_compose_reel"]
