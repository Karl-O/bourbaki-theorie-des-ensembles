"""§II.3 — Extensionnalité fonctionnelle : deux graphes fonctionnels de même
domaine et mêmes valeurs sont égaux  (propriété de base des fonctions, E.II.3).

Énoncé (INFRA réutilisable, débloque Prop. 9/12 « deux fonctions égales ssi
mêmes valeurs ») :

  `graphe_egal_par_valeurs` ⊢
     ( est_fonctionnel(F) et est_fonctionnel(G)
       et F graphe et G graphe
       et dom F = dom G
       et (∀x)(x∈dom F ⇒ F(x)=G(x)) )
     ⇒  F = G.

PREUVE : par l'axiome A1 (extensionnalité, via `extensionnalite_appliquee`) il
suffit de prouver F⊂G et G⊂F, c.-à-d. (∀z)(z∈F ⇒ z∈G) et la réciproque.

  Sens F⊂G : soit z∈F.  Comme F est un GRAPHE (tout élément est un couple),
  z=(x,y) pour certains x,y (est_un_couple, déf. E.II.31).  De (x,y)∈F :
    · x∈dom F  (couple_dans_dom, déf. du domaine AXIOME_DOM) ;
    · y=F(x)   (valeur_caracterisation / C46, sous F fonctionnel).
  Or dom F = dom G donc x∈dom G, et F(x)=G(x) (hyp. des valeurs), d'où y=G(x).
  Donc (x,G(x))∈G (valeur_dans_graphe, sous x∈dom G), i.e. (x,y)∈G (réécriture
  G(x)→y), i.e. z=(x,y)∈G.  Élimination des témoins x,y (z∈G sans x,y libres).

  Sens G⊂F : symétrique (dom et valeurs symétrisés à l'intérieur).

L'hypothèse « F,G sont des graphes » est REQUISE : est_fonctionnel(F) n'impose
que l'unicité de la valeur, pas que tout élément soit un couple ; sans elle,
« z∈F ⇒ z est un couple » manque (cf. consigne de mission).

Liants : la décomposition z=(x,y) emploie x,y — y=var("y") s'apparie exactement
avec la coordonnée de valeur_caracterisation/C46 (qui τ-lie « y » dans F(x)) et
avec le liant « y » de AXIOME_DOM/est_un_couple.
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (Terme, var, egal, et, impl, appartient,
                                       existe, pourtout)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_theoremes import extensionnalite_appliquee
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, instancie)
from bourbaki.logique.i_4_egalitaires.tactiques_abrege_egalite import (
    symetrie, composer_egalites)
from bourbaki.logique.i_3_quantifies.tactiques_abrege_quantif import existe_elimination
from bourbaki.ensembles.fonctions.ii_3_4_fonctions_valeur.ensembles_fonctions import (
    valeur_dans_graphe, valeur_caracterisation)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def egalite_valeurs(f, g, x="x"):
    """(∀x)(x∈dom F ⇒ F(x)=G(x))  (les deux fonctions prennent les mêmes valeurs)."""
    vf, vg, vx = _t(f), _t(g), var(x)
    return pourtout(x, impl(appartient(vx, E.dom(vf)),
                            egal(E.valeur(vf, vx), E.valeur(vg, vx))))


def _inst_dom(f, x):
    """⊢ (x ∈ dom F) ⇔ (∃y)((x,y) ∈ F).   (instance de AXIOME_DOM en F, x.)"""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_DOM)
    return instancie(instancie(ax, f), x)


def couple_dans_dom(f="F", x="x", y="y"):
    """{(x,y) ∈ F} ⊢ x ∈ dom F.   (le premier terme d'un couple de F est défini.)

    f, x, y : noms OU termes.  x est la 1ʳᵉ coordonnée, y la 2ᵈᵉ (témoin du ∃)."""
    vf, vx, vy = _t(f), _t(x), _t(y)
    car = _inst_dom(vf, vx)                                  # (x∈dom F)⇔(∃y)((x,y)∈F)
    in_couple = N.assume(appartient(E.couple(vx, vy), vf))   # (x,y)∈F
    exists_y = N.modus_ponens(                               # (∃y)((x,y)∈F), témoin vy
        in_couple, N.s5(appartient(E.couple(vx, var("y")), vf), vy, "y"))
    return N.modus_ponens(exists_y, conjonction_elim_droite(car))   # x∈dom F


def _couple_dans_dom_imp(vf, vx, vy):
    """⊢ ((x,y)∈F) ⇒ (x∈dom F)  (forme implicative, hypothèse déchargée)."""
    return N.loi_deduction(appartient(E.couple(vx, vy), vf),
                           couple_dans_dom(vf, vx, vy))


def _exists_y_dom(vf, vx):
    """⊢ (x∈dom F) ⇒ (∃y)((x,y)∈F)  (sens ⇒ de AXIOME_DOM, pour valeur_dans_graphe)."""
    return equivalence_avant(_inst_dom(vf, vx))


def _inclusion(src, tgt, h_src_func, h_src_graphe, dom_eq, val_eq):
    """src ⊂ tgt = (∀z)(z∈src ⇒ z∈tgt), un sens de l'extensionnalité.

    Prémisses (théorèmes, mêmes hypothèses Γ pour pouvoir composer/décharger) :
      h_src_func   : Γ ⊢ est_fonctionnel(src)
      h_src_graphe : Γ ⊢ est_un_graphe(src)
      dom_eq       : Γ ⊢ dom src = dom tgt
      val_eq       : Γ ⊢ (∀x)(x∈dom src ⇒ src(x)=tgt(x))
    Renvoie Γ ⊢ src ⊂ tgt."""
    vS, vT = _t(src), _t(tgt)
    vz, vx, vy = var("z"), var("x"), var("y")

    hz = N.assume(appartient(vz, vS))                       # z∈src
    inst_graphe = instancie(h_src_graphe, vz)              # z∈src ⇒ (z est un couple)
    z_est_couple = N.modus_ponens(hz, inst_graphe)         # (∃x)(∃y)(z=(x,y))

    # ── corps sous témoins x, y : de (z=(x,y), z∈src) déduire z∈tgt ──────────────
    h_zxy = N.assume(egal(vz, E.couple(vx, vy)))           # z=(x,y)
    # (x,y)∈src   (réécriture z→(x,y) dans z∈src ; Leibniz par S6)
    xy_in_src = N.modus_ponens(
        hz, equivalence_avant(N.modus_ponens(
            h_zxy, N.s6(vz, E.couple(vx, vy), "w", appartient(var("w"), vS)))))
    # x∈dom src
    x_in_domS = N.modus_ponens(xy_in_src, _couple_dans_dom_imp(vS, vx, vy))
    # y = src(x)   (C46, sous src fonctionnel + x∈dom src déjà présent comme hyp témoin)
    car = _valeur_carac_sous(vS, vx, vy, h_src_func, x_in_domS)   # ((x,y)∈src)⇔(y=src(x))
    y_eq_sx = N.modus_ponens(xy_in_src, equivalence_avant(car))   # y=src(x)
    # x∈dom tgt   (dom src = dom tgt)
    x_in_domT = N.modus_ponens(
        x_in_domS, equivalence_avant(N.modus_ponens(
            dom_eq, N.s6(E.dom(vS), E.dom(vT), "w", appartient(vx, var("w"))))))
    # src(x) = tgt(x)   (hyp. des valeurs)
    sx_eq_tx = N.modus_ponens(x_in_domS, instancie(val_eq, vx))   # src(x)=tgt(x)
    y_eq_tx = composer_egalites(y_eq_sx, sx_eq_tx)               # y=src(x)=tgt(x)
    # (x, tgt(x)) ∈ tgt   (valeur_dans_graphe, sous x∈dom tgt)
    ex_y_tgt = N.modus_ponens(x_in_domT, _exists_y_dom(vT, vx))   # (∃y)((x,y)∈tgt)
    # valeur_dans_graphe renvoie {(∃y)((x,y)∈tgt)} ⊢ (x,tgt(x))∈tgt : on décharge
    # cette hypothèse puis on la fournit par ex_y_tgt (porté par Γ).
    vdg = valeur_dans_graphe(vT, vx)
    vdg_imp = N.loi_deduction(
        existe("y", appartient(E.couple(vx, var("y")), vT)), vdg)   # (∃y)…⇒(x,tgt(x))∈tgt
    xtx_in_tgt = N.modus_ponens(ex_y_tgt, vdg_imp)               # (x,tgt(x))∈tgt
    # (x,y) ∈ tgt   (réécriture tgt(x)→y via tgt(x)=y)
    tx_eq_y = N.modus_ponens(y_eq_tx, symetrie(vy, E.valeur(vT, vx)))   # tgt(x)=y
    xy_in_tgt = N.modus_ponens(
        xtx_in_tgt, equivalence_avant(N.modus_ponens(
            tx_eq_y, N.s6(E.valeur(vT, vx), vy, "w",
                          appartient(E.couple(vx, var("w")), vT)))))
    # z ∈ tgt   (réécriture (x,y)→z via (x,y)=z)
    zxy_sym = N.modus_ponens(h_zxy, symetrie(vz, E.couple(vx, vy)))     # (x,y)=z
    z_in_tgt = N.modus_ponens(
        xy_in_tgt, equivalence_avant(N.modus_ponens(
            zxy_sym, N.s6(E.couple(vx, vy), vz, "w", appartient(var("w"), vT)))))

    # décharger z=(x,y), éliminer témoins y puis x  (z∈tgt sans x,y libres)
    imp_y = N.loi_deduction(egal(vz, E.couple(vx, vy)), z_in_tgt)       # z=(x,y) ⇒ z∈tgt
    elim_y = existe_elimination(imp_y, "y")               # (∃y)(z=(x,y)) ⇒ z∈tgt
    elim_xy = existe_elimination(elim_y, "x")             # (∃x)(∃y)(z=(x,y)) ⇒ z∈tgt
    z_in_tgt_final = N.modus_ponens(z_est_couple, elim_xy)              # z∈tgt
    imp_z = N.loi_deduction(appartient(vz, vS), z_in_tgt_final)         # z∈src ⇒ z∈tgt
    return N.generalisation("z", imp_z)                  # (∀z)(z∈src ⇒ z∈tgt)


def _valeur_carac_sous(vS, vx, vy, h_src_func, x_in_domS):
    """⊢ ((x,y)∈src)⇔(y=src(x))  avec les hypothèses Γ (et non les assume locaux).

    valeur_caracterisation pose deux hypothèses : est_fonctionnel(src) et
    (∃y)((x,y)∈src).  On les remplace par les théorèmes Γ-portés h_src_func et
    (∃y)((x,y)∈src) dérivé de x∈dom src, via MP sur la forme déchargée."""
    # forme entièrement déchargée : ⊢ (F fonctionnel) ⇒ ((∃y)((x,y)∈F) ⇒ (((x,y)∈F)⇔(y=F(x))))
    carac = valeur_caracterisation(vS, vx)                # {func, dom} ⊢ ((x,y)∈src)⇔(y=src(x))
    func_f = E.est_fonctionnel(vS)
    dom_f = existe("y", appartient(E.couple(vx, var("y")), vS))
    imp = N.loi_deduction(func_f, N.loi_deduction(dom_f, carac))
    ex_y = N.modus_ponens(x_in_domS, _exists_y_dom(vS, vx))   # (∃y)((x,y)∈src)
    return N.modus_ponens(ex_y, N.modus_ponens(h_src_func, imp))


# @livre Ch.II §3.5 Def.- | E II.15 L.6-10 | PDF p.66
def graphe_egal_par_valeurs(f="F", g="G"):
    """⊢ ( F fonctionnel et G fonctionnel et F graphe et G graphe
          et dom F = dom G et (∀x)(x∈dom F ⇒ F(x)=G(x)) )  ⇒  F = G.

    Extensionnalité fonctionnelle (E.II.3) : deux graphes fonctionnels de même
    domaine prenant les mêmes valeurs sont identiques.  Preuve par A1 (F⊂G, G⊂F)."""
    vF, vG = _t(f), _t(g)
    hyp = _conjonction_hypotheses(vF, vG)
    hh = N.assume(hyp)

    # projections de la grande conjonction (toutes portent l'hypothèse {hyp})
    p_val = conjonction_elim_droite(hh)                  # (∀x)(x∈dom F⇒F(x)=G(x))
    r1 = conjonction_elim_gauche(hh)
    p_dom = conjonction_elim_droite(r1)                  # dom F = dom G
    r2 = conjonction_elim_gauche(r1)
    p_gG = conjonction_elim_droite(r2)                   # G graphe
    r3 = conjonction_elim_gauche(r2)
    p_gF = conjonction_elim_droite(r3)                   # F graphe
    r4 = conjonction_elim_gauche(r3)
    p_fF = conjonction_elim_gauche(r4)                   # F fonctionnel
    p_fG = conjonction_elim_droite(r4)                   # G fonctionnel

    # dom G = dom F  et  (∀x)(x∈dom G ⇒ G(x)=F(x))  (symétrisation pour G⊂F)
    p_dom_sym = N.modus_ponens(p_dom, symetrie(E.dom(vF), E.dom(vG)))
    p_val_sym = _val_symetrise(vF, vG, p_val, p_dom)

    incl_FG = _inclusion(vF, vG, p_fF, p_gF, p_dom, p_val)
    incl_GF = _inclusion(vG, vF, p_fG, p_gG, p_dom_sym, p_val_sym)

    ext = extensionnalite_appliquee(vF, vG)              # (F⊂G et G⊂F) ⇒ F=G
    egal_FG = N.modus_ponens(conjonction_intro(incl_FG, incl_GF), ext)   # {hyp} ⊢ F=G
    return N.loi_deduction(hyp, egal_FG)                 # ⊢ HYP ⇒ F=G


def _val_symetrise(vF, vG, p_val, p_dom):
    """De {hyp}⊢(∀x)(x∈dom F⇒F(x)=G(x)) et dom F=dom G, déduire
       {hyp}⊢(∀x)(x∈dom G⇒G(x)=F(x))."""
    vx = var("x")
    hxG = N.assume(appartient(vx, E.dom(vG)))            # x∈dom G
    # x∈dom F   (dom F=dom G ⇒ (x∈dom F ⇔ x∈dom G), sens ⇐)
    leib = N.modus_ponens(p_dom, N.s6(E.dom(vF), E.dom(vG), "w", appartient(vx, var("w"))))
    x_in_domF = N.modus_ponens(hxG, conjonction_elim_droite(leib))   # x∈dom F
    fx_eq_gx = N.modus_ponens(x_in_domF, instancie(p_val, vx))       # F(x)=G(x)
    gx_eq_fx = N.modus_ponens(fx_eq_gx, symetrie(E.valeur(vF, vx), E.valeur(vG, vx)))
    imp = N.loi_deduction(appartient(vx, E.dom(vG)), gx_eq_fx)       # x∈dom G ⇒ G(x)=F(x)
    return N.generalisation("x", imp)


def _conjonction_hypotheses(vF, vG):
    """La conjonction (gauche-associée) des hypothèses de l'énoncé."""
    return et(et(et(et(et(
        E.est_fonctionnel(vF), E.est_fonctionnel(vG)),
        E.est_un_graphe(vF)), E.est_un_graphe(vG)),
        egal(E.dom(vF), E.dom(vG))),
        egalite_valeurs(vF, vG))


__all__ = ["couple_dans_dom", "egalite_valeurs", "graphe_egal_par_valeurs"]
