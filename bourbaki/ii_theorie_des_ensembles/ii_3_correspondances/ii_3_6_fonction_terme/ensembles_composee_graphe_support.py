"""§II.3.3 (support B3-CST) — la COMPOSÉE de graphes : est un graphe, domaine borné.

────────────────────────────────────────────────────────────────────────────────
Deux lemmes-support pour appliquer l'extensionnalité (egalite_graphe_terme, B2)
à G := composée de deux graphes de termes (fonctorialité F1/F2-TERMES) :

  • composee_est_graphe : ⊢ est_un_graphe(G'∘G)                    [CLOS, 0 hyp] ;
  • dom_composee_borne  : { dom(G)=D, (∀wd)(wd∈D ⇒ valeur(G,wd)∈dom(G')) }
                          ⊢ dom(G'∘G) = D                          [2 hyps].

MOTIFS : affaiblissement sous ∃ + ré-intro canonique (B1, ev. 122) ; extension
au liant z (AXIOME_DOM/COMPOSEE) ; valeur_dans_graphe ; témoins frais pw/rw/tw.
INVARIANT : theorie_ensembles()=22 ; rien postulé.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, et, impl, appartient, existe, pourtout,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege import syllogisme
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, instancie,
)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import (
    existe_elimination, monotonie_existe,
)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
    symetrie,
)
from bourbaki.ii_theorie_des_ensembles.ii_2_couples.ii_2_1_definition_couples.ensembles_couples import (
    couple_egal_implique_composantes,
)
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_4_fonctions.ensembles_fonctions import (
    valeur_dans_graphe,
)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_theoremes import (
    egalite_par_extension,
)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def _inst_composee(gp, g, w):
    """⊢ (w∈G'∘G) ⇔ (∃p)(∃r)( w=(p,r) et (∃y)((p,y)∈G et (y,r)∈G') )."""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_COMPOSEE)
    return instancie(instancie(instancie(ax, _t(gp)), _t(g)), _t(w))


# @livre Ch.II §3.3 Prop.- | E II.11 L.5-9 | PDF p.62  (le graphe composé est un graphe : tout membre est un couple)
def composee_est_graphe(gp="Gp", g="G"):
    """⊢ est_un_graphe( G'∘G ).                                    [CLOS, 0 hyp]."""
    vGp, vG, vz = _t(gp), _t(g), var("z")
    C = E.composee(vGp, vG)
    inst = _inst_composee(vGp, vG, vz)
    corps = et(egal(vz, E.couple(var("p"), var("r"))),
               existe("y", et(appartient(E.couple(var("p"), var("y")), vG),
                              appartient(E.couple(var("y"), var("r")), vGp))))
    hb = N.assume(corps)
    eq = conjonction_elim_gauche(hb)                         # z=(p,r)
    # ré-intro canonique ∃x∃y(z=(x,y)) (témoins p,r)
    j1 = N.modus_ponens(eq, N.s5(egal(vz, E.couple(var("p"), var("y"))),
                                 var("r"), "y"))
    j2 = N.modus_ponens(j1, N.s5(
        existe("y", egal(vz, E.couple(var("x"), var("y")))), var("p"), "x"))
    imp = N.loi_deduction(corps, j2)
    m = existe_elimination(existe_elimination(imp, "r"), "p")
    res = N.generalisation("z", syllogisme(equivalence_avant(inst), m))
    assert res.conclusion == E.est_un_graphe(C), "composee_est_graphe : ≠ cible"
    assert not res.hypotheses, "composee_est_graphe : NON clos"
    return res


# @livre Ch.II §3.3 Prop.- | E II.11 L.10-16 | PDF p.62  (domaine de la composée quand les valeurs de G tombent dans dom G' : dom(G'∘G)=dom G)
def dom_composee_borne(gp="Gp", g="G", D="D", wd="wd"):
    """{ dom(G)=D,  (∀wd)( wd∈D ⇒ valeur(G,wd) ∈ dom(G') ) } ⊢ dom(G'∘G) = D.

    → : z∈dom(∘) donne un témoin (z,y)∈∘, l'axiome-composée un couple (p,r) et
    un pivot t avec (p,t)∈G ; z=p ∈ dom G = D.
    ← : z∈D ⊂ dom G ⇒ (z,G(z))∈G ; l'hyp de bornes place G(z) dans dom G' d'où
    un r₂ avec (G(z),r₂)∈G' ; l'axiome-composée recolle (z,r₂)∈∘.   [2 hyps]."""
    vGp, vG, vD = _t(gp), _t(g), _t(D)
    vz = var("z")
    C = E.composee(vGp, vG)
    ax_dom = N.axiome(E.theorie_ensembles(), E.AXIOME_DOM)
    h_dom = N.assume(egal(E.dom(vG), vD))
    h_born = N.assume(pourtout(wd, impl(
        appartient(var(wd), vD),
        appartient(E.valeur(vG, var(wd)), E.dom(vGp)))))

    # ══ → : z∈dom(∘) ⇒ z∈D ══
    car_dom_C = instancie(instancie(ax_dom, C), vz)          # z∈dom∘ ⇔ ∃y((z,y)∈∘)
    #   sous témoin yw : (z,yw)∈∘ → axiome → sous témoins pw,rw + pivot tw : z=pw∈domG=D
    body_y = appartient(E.couple(vz, var("yw")), C)
    hby = N.assume(body_y)
    instc = _inst_composee(vGp, vG, E.couple(vz, var("yw")))
    expr = N.modus_ponens(hby, equivalence_avant(instc))     # ∃p∃r((z,yw)=(p,r) ∧ ∃y…)
    corps_pr = et(egal(E.couple(vz, var("yw")), E.couple(var("pw"), var("rw"))),
                  existe("y", et(appartient(E.couple(var("pw"), var("y")), vG),
                                 appartient(E.couple(var("y"), var("rw")), vGp))))
    # renommer (p,r)→(pw,rw) : 2 étages S5/élim (motif _renomme_ex2)
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import subst_f
    corps_p_rw = subst_f(var("p"), "pw", corps_pr)
    i1 = existe_elimination(N.s5(corps_p_rw, var("r"), "rw"), "r")
    i1 = monotonie_existe(i1, "p")
    i2 = existe_elimination(N.s5(existe("rw", corps_pr), var("p"), "pw"), "p")
    ex_w = N.modus_ponens(N.modus_ponens(expr, i1), i2)      # ∃pw∃rw corps
    hbpr = N.assume(corps_pr)
    eq_c = conjonction_elim_gauche(hbpr)                     # (z,yw)=(pw,rw)
    z_pw = conjonction_elim_gauche(N.modus_ponens(eq_c,
        couple_egal_implique_composantes(vz, var("yw"), var("pw"), var("rw"))))  # z=pw
    ex_pivot = conjonction_elim_droite(hbpr)                 # ∃y((pw,y)∈G ∧ …)
    body_t = et(appartient(E.couple(var("pw"), var("tw")), vG),
                appartient(E.couple(var("tw"), var("rw")), vGp))
    it = existe_elimination(N.s5(body_t, var("y"), "tw"), "y")
    ex_t = N.modus_ponens(ex_pivot, it)                      # ∃tw(…)
    hbt = N.assume(body_t)
    pwG = conjonction_elim_gauche(hbt)                       # (pw,tw)∈G
    ex_y2 = N.modus_ponens(pwG, N.s5(
        appartient(E.couple(var("pw"), var("y")), vG), var("tw"), "y"))
    pw_domG = N.modus_ponens(ex_y2, equivalence_arriere(
        instancie(instancie(ax_dom, vG), var("pw"))))        # pw∈dom G
    pw_D = N.modus_ponens(pw_domG, equivalence_avant(N.modus_ponens(
        h_dom, N.s6(E.dom(vG), vD, "h6c", appartient(var("pw"), var("h6c"))))))  # pw∈D
    z_D = N.modus_ponens(pw_D, equivalence_arriere(N.modus_ponens(
        z_pw, N.s6(vz, var("pw"), "h6c", appartient(var("h6c"), vD)))))          # z∈D
    imp_t = existe_elimination(N.loi_deduction(body_t, z_D), "tw")
    z_D = N.modus_ponens(ex_t, imp_t)
    imp_pr = existe_elimination(existe_elimination(
        N.loi_deduction(corps_pr, z_D), "rw"), "pw")
    z_D = N.modus_ponens(ex_w, imp_pr)
    imp_y = existe_elimination(N.loi_deduction(body_y, z_D), "yw")
    # (∃yw…)⇒z∈D — mais car_dom_C parle de ∃y : α-aligner via renommage S5
    i_al = existe_elimination(N.s5(body_y, var("y"), "yw"), "y")
    fwd = N.loi_deduction(appartient(vz, E.dom(C)), N.modus_ponens(
        N.modus_ponens(N.modus_ponens(N.assume(appartient(vz, E.dom(C))),
                                      equivalence_avant(car_dom_C)), i_al),
        imp_y))                                              # z∈dom∘ ⇒ z∈D

    # ══ ← : z∈D ⇒ z∈dom(∘) ══
    hzD = N.assume(appartient(vz, vD))
    z_domG = N.modus_ponens(hzD, equivalence_arriere(N.modus_ponens(
        h_dom, N.s6(E.dom(vG), vD, "h6c", appartient(vz, var("h6c"))))))  # z∈dom G
    ex_zy = N.modus_ponens(z_domG, equivalence_avant(
        instancie(instancie(ax_dom, vG), vz)))               # ∃y((z,y)∈G)
    Gz = E.valeur(vG, vz)
    zGz = N.modus_ponens(ex_zy, N.loi_deduction(
        existe("y", appartient(E.couple(vz, var("y")), vG)),
        valeur_dans_graphe(vG, vz)))                         # (z,G(z))∈G
    Gz_domGp = N.modus_ponens(hzD, instancie(h_born, vz))    # G(z)∈dom G'
    ex_r2 = N.modus_ponens(Gz_domGp, equivalence_avant(
        instancie(instancie(ax_dom, vGp), Gz)))              # ∃y((G(z),y)∈G')
    body_r2 = appartient(E.couple(Gz, var("rw")), vGp)
    ir = existe_elimination(N.s5(body_r2, var("y"), "rw"), "y")
    ex_rw = N.modus_ponens(ex_r2, ir)                        # ∃rw((G(z),rw)∈G')
    hbr2 = N.assume(body_r2)
    pivot = conjonction_intro(zGz, hbr2)                     # (z,G(z))∈G ∧ (G(z),rw)∈G'
    ex_piv = N.modus_ponens(pivot, N.s5(
        et(appartient(E.couple(vz, var("y")), vG),
           appartient(E.couple(var("y"), var("rw")), vGp)), Gz, "y"))
    w2 = E.couple(vz, var("rw"))
    corps2 = conjonction_intro(N.reflexivite(w2), ex_piv)
    r1 = N.modus_ponens(corps2, N.s5(
        et(egal(w2, E.couple(vz, var("r"))),
           existe("y", et(appartient(E.couple(vz, var("y")), vG),
                          appartient(E.couple(var("y"), var("r")), vGp)))),
        var("rw"), "r"))
    r2s = N.modus_ponens(r1, N.s5(
        existe("r", et(egal(w2, E.couple(var("p"), var("r"))),
                       existe("y", et(appartient(E.couple(var("p"), var("y")), vG),
                                      appartient(E.couple(var("y"), var("r")), vGp))))),
        vz, "p"))
    w2_in = N.modus_ponens(r2s, equivalence_arriere(
        _inst_composee(vGp, vG, w2)))                        # (z,rw)∈∘
    ex_dc = N.modus_ponens(w2_in, N.s5(
        appartient(E.couple(vz, var("y")), C), var("rw"), "y"))   # ∃y((z,y)∈∘)
    z_domC = N.modus_ponens(ex_dc, equivalence_arriere(car_dom_C))
    imp_rw = existe_elimination(N.loi_deduction(body_r2, z_domC), "rw")
    bwd = N.loi_deduction(appartient(vz, vD), N.modus_ponens(ex_rw, imp_rw))

    # ══ extension (∀z)(z∈dom∘ ⇔ z∈D) — via A1 sur les deux ensembles ══
    R = appartient(vz, vD)
    thm_u = N.generalisation("z", conjonction_intro(fwd, bwd))     # z∈dom∘ ⇔ z∈D
    triv = N.loi_deduction(R, N.assume(R))
    thm_v = N.generalisation("z", conjonction_intro(triv, triv))   # z∈D ⇔ z∈D
    res = egalite_par_extension(thm_u, thm_v, E.dom(C), vD, x="z")
    assert res.conclusion == egal(E.dom(C), vD), "dom_composee_borne : ≠ cible"
    assert len(res.hypotheses) == 2, \
        "dom_composee_borne : hyps ≠ 2 (%d)" % len(res.hypotheses)
    return res


__all__ = ["composee_est_graphe", "dom_composee_borne"]
