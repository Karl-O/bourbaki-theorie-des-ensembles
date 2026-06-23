"""§II.5.3 — EXTENSIONNALITÉ DU PRODUIT ∏_{ι∈I} X_ι (infra réutilisable).

Un élément F ∈ ∏_{ι∈I} X_ι est un GRAPHE FONCTIONNEL de domaine I (Déf. 1,
E.II.5.3) : F « est » la fonction ι ↦ F(ι) = pr_ι(F).  Donc deux points du produit
qui ont les MÊMES PROJECTIONS en tout ι∈I sont la MÊME fonction, donc le MÊME
ensemble (extensionnalité fonctionnelle A1) :

  `extensionnalite_produit` ⊢
     ( x ∈ ∏  et  y ∈ ∏
       et  est_un_graphe(x)  et  est_un_graphe(y)
       et  (∀ι)(ι∈I ⇒ pr_ι(x) = pr_ι(y)) )
     ⇒  x = y.

PREUVE.  De x∈∏, y∈∏ : est_fonctionnel(x), est_fonctionnel(y) (produit_fonctionnel)
et dom x = I = dom y (produit_domaine), d'où dom x = dom y.  L'hypothèse des
projections, sous ι∈dom x (= ι∈I via dom x = I), donne pr_ι(x)=pr_ι(y),
c.-à-d. valeur(x,ι)=valeur(y,ι) (car pr_ι = valeur(·,ι), E.II.5.3).  Les six
prémisses de `graphe_egal_par_valeurs` (extensionnalité fonctionnelle, E.II.3) sont
réunies ⇒ x = y.

HYPOTHÈSES HONNÊTES (non vacuous — la conclusion x=y n'y figure pas) :
  • x ∈ ∏, y ∈ ∏          — les deux points sont dans le produit ;
  • est_un_graphe(x), est_un_graphe(y)  — « x, y sont des ensembles de couples ».
    L'axiome de membership encodé (AXIOME_PRODUIT_FAM) n'expose que est_fonctionnel
    et dom = I, PAS « tout élément est un couple » (le produit est sélectionné dans
    P(I×A), donc cette propriété est VRAIE dans la théorie complète, mais l'axiome
    encodé ne la fournit pas) ; on l'expose donc comme hypothèse honnête, exactement
    comme application_egale_par_valeurs dérive est_un_graphe de G⊂E×F ;
  • (∀ι)(ι∈I ⇒ pr_ι(x) = pr_ι(y))  — l'égalité des projections.

Rien postulé : tout sort de produit_fonctionnel / produit_domaine (instances de
AXIOME_PRODUIT_FAM), de l'extensionnalité fonctionnelle graphe_egal_par_valeurs, et
de la substitution de Leibniz (S6).  theorie_ensembles() reste à 22.

Liants : l'indice du produit / le liant interne de la projection-égalité est « i »
(défaut, ≠ « x » qui apparaît dans le liant interne de graphe_egal_par_valeurs).
Le liant interne de l'extensionnalité fonctionnelle est « x » ; pour éviter toute
collision avec le point « x » du produit, l'appelant peut renommer (les défauts ci-
dessous prennent x_pt/y_pt comme noms de points, distincts du liant « x » interne).
"""
from __future__ import annotations

from bourbaki.logique.formule import (Terme, var, egal, et, impl, appartient,
                                       pourtout)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.logique.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, instancie)
from bourbaki.logique.tactiques.tactiques_abrege_egalite import (
    symetrie, composer_egalites)
from bourbaki.ensembles.fonctions.ii_3_general.ensembles_extensionnalite import (
    graphe_egal_par_valeurs)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def egalite_projections(f, i, x_pt, y_pt, idx="i"):
    """(∀ι)(ι∈I ⇒ pr_ι(x) = pr_ι(y))  (les deux points du produit ont mêmes
    projections en tout indice).  pr_ι(·) = projection_indice(·, ι) = valeur(·, ι)."""
    vx, vy, vi = _t(x_pt), _t(y_pt), var(idx)
    vI = _t(i)
    return pourtout(idx, impl(appartient(vi, vI),
                              egal(E.projection_indice(vx, vi),
                                   E.projection_indice(vy, vi))))


def _conjonction_hypotheses(vf, vI, vx, vy, idx):
    """La conjonction (gauche-associée) des hypothèses honnêtes de l'énoncé."""
    prod = E.produit_famille(vf, vI)
    return et(et(et(et(
        appartient(vx, prod), appartient(vy, prod)),
        E.est_un_graphe(vx)), E.est_un_graphe(vy)),
        egalite_projections(vf, vI, vx, vy, idx))


def _valeurs_depuis_projections(vf, vI, vx, vy, dom_x_eq_I, h_proj, val_bnd="x"):
    """{ pr-égalité, dom x = I } ⊢ (∀x)(x∈dom x_pt ⇒ valeur(x_pt,x)=valeur(y_pt,x)).

    Sous w∈dom x : dom x = I donne w∈I (Leibniz S6), d'où pr_w(x)=pr_w(y) (h_proj) ;
    et pr_w(·) EST valeur(·,w) par définition (projection_indice = valeur), donc
    c'est déjà l'égalité des valeurs sur le domaine de x.  Le liant de l'égalité-
    valeurs est « x » (val_bnd) pour APPARIER egalite_valeurs(x,y) qu'attend
    graphe_egal_par_valeurs (son binder interne par défaut)."""
    vt = var(val_bnd)                                      # variable courante (liée à val_bnd)
    h_idom = N.assume(appartient(vt, E.dom(vx)))           # w ∈ dom x
    # w∈dom x et dom x=I ⇒ w∈I  (Leibniz S6 sur le 2ᵉ argument de ∈)
    leib = N.s6(E.dom(vx), vI, "u", appartient(vt, var("u")))
    i_in_I = N.modus_ponens(h_idom, equivalence_avant(
        N.modus_ponens(dom_x_eq_I, leib)))                 # w ∈ I
    # pr_w(x)=pr_w(y)  i.e. valeur(x,w)=valeur(y,w)  (projection_indice = valeur)
    prx_eq_pry = N.modus_ponens(i_in_I, instancie(h_proj, vt))
    imp = N.loi_deduction(appartient(vt, E.dom(vx)), prx_eq_pry)
    return N.generalisation(val_bnd, imp)  # (∀x)(x∈dom x_pt ⇒ valeur(x_pt,x)=valeur(y_pt,x))


def extensionnalite_produit(f="f", i="I", x_pt="x_pt", y_pt="y_pt", idx="i"):
    """⊢ ( x ∈ ∏_{ι∈I} X_ι  et  y ∈ ∏  et  est_un_graphe(x)  et  est_un_graphe(y)
          et  (∀ι)(ι∈I ⇒ pr_ι(x) = pr_ι(y)) )  ⇒  x = y.

    EXTENSIONNALITÉ DU PRODUIT (E.II.5.3) : deux points du produit qui ont les mêmes
    projections en tout indice sont égaux.  Preuve par graphe_egal_par_valeurs (deux
    graphes fonctionnels de même domaine et mêmes valeurs sont égaux, E.II.3).

    f = la famille (X_ι), I = l'ensemble d'indices, x_pt/y_pt = les deux points.
    Hypothèses honnêtes (voir docstring du module).  CLOS au sens : 0 hypothèse
    résiduelle — les cinq prémisses sont l'antécédent de l'implication renvoyée."""
    vf, vI, vx, vy = _t(f), _t(i), _t(x_pt), _t(y_pt)
    hyp = _conjonction_hypotheses(vf, vI, vx, vy, idx)
    hh = N.assume(hyp)

    # projections de la grande conjonction (toutes portent l'hypothèse {hyp})
    h_proj = conjonction_elim_droite(hh)                   # (∀ι)(ι∈I ⇒ pr_ι x=pr_ι y)
    r1 = conjonction_elim_gauche(hh)
    h_gy = conjonction_elim_droite(r1)                     # est_un_graphe(y)
    r2 = conjonction_elim_gauche(r1)
    h_gx = conjonction_elim_droite(r2)                     # est_un_graphe(x)
    r3 = conjonction_elim_gauche(r2)
    h_x_in = conjonction_elim_gauche(r3)                   # x ∈ ∏
    h_y_in = conjonction_elim_droite(r3)                   # y ∈ ∏

    prod = E.produit_famille(vf, vI)
    # est_fonctionnel(x), est_fonctionnel(y)  (produit_fonctionnel : x∈∏ ⇒ fonct(x))
    func_x = N.modus_ponens(h_x_in, _fonctionnel_imp(vf, vI, vx))
    func_y = N.modus_ponens(h_y_in, _fonctionnel_imp(vf, vI, vy))
    # dom x = I,  dom y = I  (produit_domaine : x∈∏ ⇒ dom x = I)
    dom_x_eq_I = N.modus_ponens(h_x_in, _domaine_imp(vf, vI, vx))   # dom x = I
    dom_y_eq_I = N.modus_ponens(h_y_in, _domaine_imp(vf, vI, vy))   # dom y = I
    # dom x = dom y   (dom x = I = dom y)
    I_eq_dom_y = N.modus_ponens(dom_y_eq_I, symetrie(E.dom(vy), vI))  # I = dom y
    dom_eq = composer_egalites(dom_x_eq_I, I_eq_dom_y)             # dom x = dom y

    # (∀x)(x∈dom x_pt ⇒ valeur(x_pt,x)=valeur(y_pt,x))  (de la pr-égalité, via dom x=I)
    # liant « x » pour apparier egalite_valeurs(x_pt,y_pt) attendu par gev.
    val_eq = _valeurs_depuis_projections(vf, vI, vx, vy, dom_x_eq_I, h_proj, "x")

    # graphe_egal_par_valeurs : (fonct x et fonct y et x graphe et y graphe
    #   et dom x=dom y et (∀ι)(ι∈dom x ⇒ x(ι)=y(ι))) ⇒ x=y
    gev = graphe_egal_par_valeurs(vx, vy)
    hyp_conj = conjonction_intro(conjonction_intro(conjonction_intro(conjonction_intro(
        conjonction_intro(func_x, func_y), h_gx), h_gy), dom_eq), val_eq)
    x_eq_y = N.modus_ponens(hyp_conj, gev)                 # {hyp} ⊢ x = y
    return N.loi_deduction(hyp, x_eq_y)                    # ⊢ HYP ⇒ x = y


def _inst_produit(vf, vI, vF):
    """⊢ (F ∈ ∏) ⇔ ( fonct(F) et dom F = I et (∀i)(i∈I ⇒ F(i)∈X_i) ).

    Instance de AXIOME_PRODUIT_FAM en (f, I, F) — VERSION ACCEPTANT DES TERMES (le
    helper déposé fait var(...), qui corromprait un terme complexe)."""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_PRODUIT_FAM)
    return instancie(instancie(instancie(ax, vf), vI), vF)


def _fonctionnel_imp(vf, vI, vF):
    """⊢ (F ∈ ∏) ⇒ est_fonctionnel(F)  (Terme-safe, cf. produit_fonctionnel)."""
    h = N.assume(appartient(vF, E.produit_famille(vf, vI)))
    corps = N.modus_ponens(h, equivalence_avant(_inst_produit(vf, vI, vF)))
    fonctionnel = conjonction_elim_gauche(conjonction_elim_gauche(corps))
    return N.loi_deduction(appartient(vF, E.produit_famille(vf, vI)), fonctionnel)


def _domaine_imp(vf, vI, vF):
    """⊢ (F ∈ ∏) ⇒ (dom F = I)  (Terme-safe, cf. produit_domaine)."""
    h = N.assume(appartient(vF, E.produit_famille(vf, vI)))
    corps = N.modus_ponens(h, equivalence_avant(_inst_produit(vf, vI, vF)))
    domaine = conjonction_elim_droite(conjonction_elim_gauche(corps))
    return N.loi_deduction(appartient(vF, E.produit_famille(vf, vI)), domaine)


__all__ = ["egalite_projections", "extensionnalite_produit"]
