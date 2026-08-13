"""§III.1 n°12 — REMARQUE (E.III.14, après les Exemples de la Déf. 9) : un ensemble
TOTALEMENT ordonné est RÉTICULÉ (et a fortiori filtrant à droite et à gauche).

Énoncé Bourbaki (verbatim, E III.14, après les Exemples) :

  « Un ensemble totalement ordonné est aussi totalement ordonné pour l'ordre
  opposé ; il est réticulé et a fortiori filtrant à droite et à gauche. »

On formalise ici l'assertion « réticulé ».  Convention « graphe G »
(ensembles_ordre_relation) : x ≤ y := (x,y)∈G.  L'ensemble réticulé (E.III.1.11,
Déf. 8) est l'ordre dans lequel toute paire {x,y} admet une borne supérieure ET
une borne inférieure :

  est_reticule(G,E) := est_ordre(G,E) et
      (∀x)(∀y)((x∈E et y∈E) ⇒
          (∃s)(∃i)(borne_superieure(G,{x,y},s,E) et borne_inferieure(G,{x,y},i,E))).

SÉQUENT CIBLE (CLOS sous les deux hypothèses HONNÊTES de l'énoncé) :

  { est_ordre(G,E), totalite(G,E) }  ⊢  est_reticule(G,E)

  où totalite(G,E) := (∀x)(∀y)((x∈E et y∈E) ⇒ ((x,y)∈G ou (y,x)∈G))  EST la
  seconde conjointe de totalement_ordonne(G,E) (E.III.1.12, Déf. 9).  On prend
  est_ordre et totalite comme deux antécédents SÉPARÉS afin d'exposer exactement
  les deux hypothèses qui servent.

STRATÉGIE.  La 1ʳᵉ conjointe de est_reticule(G,E) EST est_ordre(G,E) : on la
réutilise telle quelle (Hord).  Reste la clause des bornes.  Pour x,y∈E frais, la
totalité (instanciée + MP) donne (x,y)∈G OU (y,x)∈G.  RAISONNEMENT PAR CAS
(tactique `cas`), les deux branches concluant la MÊME formule existentielle
(∃s)(∃i)(BS(s) et BI(i)) :

  • branche (x,y)∈G : témoins  s := y (borne sup),  i := x (borne inf) ;
  • branche (y,x)∈G : témoins  s := x (borne sup),  i := y (borne inf).

Construire « y est borne supérieure de {x,y} » (branche (x,y)∈G) exige la
construction COMPLÈTE :
  (1) y MAJORANT : y∈E, et (∀u)(u∈{x,y} ⇒ (u,y)∈G) — case-split u=x∨u=y (axiome de
      la paire) : cas u=x via l'hypothèse de branche (x,y)∈G, cas u=y via la
      réflexivité (y,y)∈G ; chaque preuve est transportée vers (u,y)∈G par Leibniz.
  (2) y PLUS PETIT majorant : (∀m)(majorant(G,{x,y},m,E) ⇒ (y,m)∈G) — comme
      y∈{x,y}, tout majorant m domine y : on instancie le quantificateur du
      majorant m en u:=y (lemme membre_paire_droite).
La borne inférieure x est construite dualement (minorant + plus grand minorant).

Liants RESPECTÉS (alpha-égalité avec la cible) : majorant/minorant interne « u » ;
plus-petit-majorant « mbs », plus-grand-minorant « mbi » (liants FRAIS du projet,
cf. admet_borne_sup_inf — sans eux il y aurait capture du y de la paire).  Les
existentielles (∃s)(∃i) sont introduites par S5 (témoins de la branche) ; comme
mbs,mbi ≠ s,i,x,y, la substitution S5 ne renomme RIEN et l'antécédent S5 coïncide
STRUCTURELLEMENT avec la borne construite.  La clause est recollée par
loi_deduction (sur x∈E et y∈E) et double généralisation ; conjonction_intro(Hord,
clause) = est_reticule(G,E) ; décharge des hypothèses ⇒ séquent.

INVARIANTS : conclusion alpha-égale à est_reticule("G","E") ; hypothèses ==
{ est_ordre("G","E"), totalite("G","E") } exactement (aucune parasite).
theorie_ensembles INTANGIBLE = 22 : tout est DÉRIVÉ (primitives N.* du noyau LCF).
STATUT : CLOS sous les deux hypothèses honnêtes.  (E.III.14, Remarque.)
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, et, ou, impl, appartient, existe, pourtout,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_theoremes import _instance_paire
from bourbaki.ii_theorie_des_ensembles.ii_2_couples.ii_2_1_definition_couples.ensembles_couples import (
    membre_paire_gauche, membre_paire_droite,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    instancie, cas, equivalence_avant,
)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import symetrie
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_relation import (
    est_ordre, borne_superieure, borne_inferieure, majorant, minorant, _couple_dans,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_monotone import (
    est_reticule,
)


def _t(t):
    return t if isinstance(t, Terme) else var(t)


# ── liants par défaut de est_reticule / admet_borne_sup_inf (À RESPECTER pour
#    l'alpha-égalité structurelle avec la cible) :
#    • « u »   = liant interne du majorant/minorant (∀u)(u∈{x,y}⇒…) ;
#    • « mbs » = liant du « plus petit majorant »  (FRAIS, anti-capture) ;
#    • « mbi » = liant du « plus grand minorant »  (FRAIS, anti-capture) ;
#    • « s », « i » = liants existentiels des bornes sup/inf.
_U, _MBS, _MBI, _S, _I = "u", "mbs", "mbi", "s", "i"


# ════════════════════════════════════════════════════════════════════════════
#  totalité = seconde conjointe de totalement_ordonne (E.III.1.12, Déf. 9)
# ════════════════════════════════════════════════════════════════════════════
def totalite(G="G", E_set="E", x="x", y="y"):
    """totalite(G,E) := (∀x)(∀y)((x∈E et y∈E) ⇒ ((x,y)∈G ou (y,x)∈G)).

    « Deux éléments quelconques de E sont comparables » : la clause de comparabilité
    de l'ordre TOTAL (E.III.1.12, Déf. 9), ici prise comme hypothèse séparée."""
    vx, vy, vE = var(x), var(y), _t(E_set)
    return pourtout(x, pourtout(y,
        impl(et(appartient(vx, vE), appartient(vy, vE)),
             ou(_couple_dans(vx, vy, G), _couple_dans(vy, vx, G)))))


def hypotheses_total_reticule(G="G", E_set="E"):
    """Les DEUX hypothèses honnêtes du séquent : { est_ordre(G,E), totalite(G,E) }."""
    return frozenset({est_ordre(G, E_set), totalite(G, E_set)})


def cible_total_implique_reticule(G="G", E_set="E"):
    """Conclusion attendue : est_reticule(G,E)  (E.III.1.11, Déf. 8 ; liants par défaut)."""
    return est_reticule(G, E_set)


# ── bornes sup/inf aux liants EXACTS de la cible ───────────────────────────────
def _bs(G, P, m, E_set):
    """borne_superieure(G,{x,y},m,E) — majorant interne « u », plus-petit-maj « mbs »."""
    return borne_superieure(G, P, _t(m), E_set, _U, _MBS)


def _bi(G, P, m, E_set):
    """borne_inferieure(G,{x,y},m,E) — minorant interne « u », plus-grand-min « mbi »."""
    return borne_inferieure(G, P, _t(m), E_set, _U, _MBI)


def _quant_couple(G, P, vx, vy, m, preuve_x, preuve_y, gauche):
    """Construit (∀u)(u∈{x,y} ⇒ C(u))  où C(u) = (m,u)∈G si gauche, sinon (u,m)∈G.

    `preuve_x` ⊢ C(x), `preuve_y` ⊢ C(y) (déjà aux bons sens).  Pour u∈{x,y} on
    case-split u=x∨u=y (axiome de la paire), et on transporte C(x) ou C(y) vers
    C(u) par Leibniz (S6) sur le trou « u »."""
    vP, vu = _t(P), var(_U)

    def C(t):
        return _couple_dans(m, t, G) if gauche else _couple_dans(t, m, G)

    Hu = N.assume(appartient(vu, vP))                     # u∈{x,y}
    disj = N.modus_ponens(Hu, equivalence_avant(_instance_paire(vx, vy, vu)))  # u=x ∨ u=y
    phi = C(vu)                                           # Φ(u) = C(u), trou « u »

    def branche(w, preuve_w):
        # (u=w) ⇒ C(u) : symétrie u=w↦w=u, Leibniz (w=u)⇒(C(w)⇔C(u)), MP.
        Heq = N.assume(egal(vu, _t(w)))                  # u=w
        w_eq_u = N.modus_ponens(Heq, symetrie(vu, _t(w)))   # w=u
        leib = N.s6(_t(w), vu, _U, phi)                  # (w=u) ⇒ (C(w) ⇔ C(u))
        equiv_wu = N.modus_ponens(w_eq_u, leib)
        Cu = N.modus_ponens(preuve_w, equivalence_avant(equiv_wu))   # C(u)
        return N.loi_deduction(egal(vu, _t(w)), Cu)      # (u=w) ⇒ C(u)

    body = N.loi_deduction(appartient(vu, vP),
                           cas(disj, branche(vx, preuve_x), branche(vy, preuve_y)))
    return N.generalisation(_U, body)


def _plus_extremal(G, E_set, P, ext, ext_membre_thm, gauche):
    """Construit le « plus petit majorant » (gauche=False) ou « plus grand minorant »
    (gauche=True) de la borne `ext` :

        (∀mbs)(majorant(G,{x,y},mbs,E) ⇒ (ext,mbs)∈G)   [gauche=False]
        (∀mbi)(minorant(G,{x,y},mbi,E) ⇒ (mbi,ext)∈G)   [gauche=True]

    `ext_membre_thm` ⊢ ext∈{x,y}.  Pour un majorant/minorant n, son quantificateur
    interne (∀u)(u∈{x,y}⇒(·)∈G) instancié en u:=ext donne la relation cherchée
    entre ext et n (puisque ext∈{x,y})."""
    vext = _t(ext)
    lieur = _MBI if gauche else _MBS                      # liant plus-grand-min / plus-petit-maj
    vn = var(lieur)
    pred_n = (minorant(G, P, vn, E_set, _U) if gauche
              else majorant(G, P, vn, E_set, _U))
    Hn = N.assume(pred_n)                                 # majorant/minorant n
    quant_n = conjonction_elim_droite(Hn)                # (∀u)(u∈{x,y}⇒(·)∈G)
    rel = N.modus_ponens(ext_membre_thm, instancie(quant_n, vext))   # (ext,n)∈G ou (n,ext)∈G
    return N.generalisation(lieur, N.loi_deduction(pred_n, rel))


def _bornes_de_branche(G, E_set, P, vx, vy, x_in_E, y_in_E, refl_E, hyp_rel, sup, inf):
    """Construit  ( BS(sup) et BI(inf) )  pour une branche, où :
      • sup, inf ∈ {vx, vy} sont les témoins de la branche (borne sup et inf) ;
      • hyp_rel ⊢ l'hypothèse de branche, p.ex. (x,y)∈G dans la branche (x,y)∈G ;
      • refl_E ⊢ (∀t)(t∈E⇒(t,t)∈G) (réflexivité, extraite de est_ordre) ;
      • x_in_E, y_in_E ⊢ x∈E, y∈E.

    Branche (x,y)∈G : sup=y, inf=x.  Branche (y,x)∈G : sup=x, inf=y."""
    vsup, vinf = _t(sup), _t(inf)
    sup_in_E = y_in_E if vsup == vy else x_in_E
    inf_in_E = x_in_E if vinf == vx else y_in_E
    refl_sup = N.modus_ponens(sup_in_E, instancie(refl_E, vsup))   # (sup,sup)∈G
    refl_inf = N.modus_ponens(inf_in_E, instancie(refl_E, vinf))   # (inf,inf)∈G

    # ── BORNE SUPÉRIEURE = sup ────────────────────────────────────────────────
    #   MAJORANT sup : (∀u)(u∈{x,y} ⇒ (u,sup)∈G).  u=sup : réflexivité ;
    #   u=autre : hyp_rel = (autre,sup)∈G.
    if vsup == vy:        # branche (x,y)∈G : (x,y)∈G = (autre=x, sup=y)
        px_sup, py_sup = hyp_rel, refl_sup        # C(x)=(x,y)∈G ; C(y)=(y,y)∈G
        sup_membre = membre_paire_droite(vx, vy)  # y∈{x,y}
    else:                # branche (y,x)∈G : (y,x)∈G = (autre=y, sup=x)
        px_sup, py_sup = refl_sup, hyp_rel        # C(x)=(x,x)∈G ; C(y)=(y,x)∈G
        sup_membre = membre_paire_gauche(vx, vy)  # x∈{x,y}
    maj_quant = _quant_couple(G, P, vx, vy, vsup, px_sup, py_sup, gauche=False)
    maj_sup = conjonction_intro(sup_in_E, maj_quant)               # majorant(G,P,sup,E)
    pp_sup = _plus_extremal(G, E_set, P, vsup, sup_membre, gauche=False)  # plus petit majorant
    bs = conjonction_intro(maj_sup, pp_sup)                        # borne_superieure(...)

    # ── BORNE INFÉRIEURE = inf ────────────────────────────────────────────────
    #   MINORANT inf : (∀u)(u∈{x,y} ⇒ (inf,u)∈G).  u=inf : réflexivité ;
    #   u=autre : hyp_rel = (inf,autre)∈G.
    if vinf == vx:        # branche (x,y)∈G : (x,y)∈G = (inf=x, autre=y)
        px_inf, py_inf = refl_inf, hyp_rel        # C(x)=(x,x)∈G ; C(y)=(x,y)∈G
        inf_membre = membre_paire_gauche(vx, vy)  # x∈{x,y}
    else:                # branche (y,x)∈G : (y,x)∈G = (inf=y, autre=x)
        px_inf, py_inf = hyp_rel, refl_inf        # C(x)=(y,x)∈G ; C(y)=(y,y)∈G
        inf_membre = membre_paire_droite(vx, vy)  # y∈{x,y}
    min_quant = _quant_couple(G, P, vx, vy, vinf, px_inf, py_inf, gauche=True)
    min_inf = conjonction_intro(inf_in_E, min_quant)              # minorant(G,P,inf,E)
    pg_inf = _plus_extremal(G, E_set, P, vinf, inf_membre, gauche=True)  # plus grand minorant
    bi = conjonction_intro(min_inf, pg_inf)                       # borne_inferieure(...)

    return conjonction_intro(bs, bi)                              # BS(sup) et BI(inf)


def _s5_corps_i(G, P, E_set, vsup, vinf):
    """⊢ ( BS(sup) et BI(inf) ) ⇒ (∃i)( BS(sup) et BI(i) )  par S5 sur i.

    Motif R(i) = BS(sup) et BI(i) ; témoin T = inf ; (inf|i)R EST BS(sup) et BI(inf)
    (sans renommage : le liant mbi ≠ inf)."""
    vi = var(_I)
    R = et(_bs(G, P, vsup, E_set), _bi(G, P, vi, E_set))            # BS(sup) et BI(i)
    return N.s5(R, _t(vinf), _I)                                    # (inf|i)R ⇒ (∃i)R


def _s5_corps_s(G, P, E_set, vsup):
    """⊢ (∃i)( BS(sup) et BI(i) ) ⇒ (∃s)(∃i)( BS(s) et BI(i) )  par S5 sur s.

    Motif R(s) = (∃i)( BS(s) et BI(i) ) ; témoin T = sup ; (sup|s)R EST (∃i)(BS(sup)…)
    (sans renommage : le liant mbs ≠ sup, et i ≠ sup)."""
    vs, vi = var(_S), var(_I)
    R = existe(_I, et(_bs(G, P, vs, E_set), _bi(G, P, vi, E_set)))  # (∃i)(BS(s) et BI(i))
    return N.s5(R, _t(vsup), _S)                                    # (sup|s)R ⇒ (∃s)R


def _clause_bornes(G, E_set, x, y):
    """Construit la clause des bornes de est_reticule sous Htot, Hord :
        (∀x)(∀y)((x∈E et y∈E) ⇒ (∃s)(∃i)(BS(s) et BI(i))).

    Pour x,y∈E : totalité ⇒ (x,y)∈G ou (y,x)∈G.  Chaque branche fournit (BS et BI)
    avec ses témoins (sup,inf), puis S5×2 réintroduit (∃s)(∃i) ; les deux branches
    concluent la même formule existentielle, recollée par `cas`."""
    vx, vy, vE = var(x), var(y), _t(E_set)
    P = E.paire(vx, vy)

    Hord = N.assume(est_ordre(G, E_set))
    Htot = N.assume(totalite(G, E_set))
    refl_E = conjonction_elim_gauche(conjonction_elim_gauche(Hord))   # (∀t)(t∈E⇒(t,t)∈G)

    Hxy = N.assume(et(appartient(vx, vE), appartient(vy, vE)))        # x∈E et y∈E
    x_in_E = conjonction_elim_gauche(Hxy)
    y_in_E = conjonction_elim_droite(Hxy)

    # totalité en (x,y) : (x,y)∈G ou (y,x)∈G
    comp_xy = instancie(instancie(Htot, vx), vy)
    disj = N.modus_ponens(Hxy, comp_xy)                              # (x,y)∈G ou (y,x)∈G

    def branche(hyp_rel_formule, sup, inf):
        Hrel = N.assume(hyp_rel_formule)                             # (x,y)∈G ou (y,x)∈G
        bornes = _bornes_de_branche(G, E_set, P, vx, vy,
                                    x_in_E, y_in_E, refl_E, Hrel, sup, inf)
        # bornes ⊢ BS(sup) et BI(inf) ; injecter dans (∃s)(∃i)(BS(s) et BI(i)).
        ex_i = N.modus_ponens(bornes, _s5_corps_i(G, P, E_set, vsup=sup, vinf=inf))
        ex_si = N.modus_ponens(ex_i, _s5_corps_s(G, P, E_set, vsup=sup))
        return N.loi_deduction(hyp_rel_formule, ex_si)               # rel ⇒ but

    cas_xy = branche(_couple_dans(vx, vy, G), sup=vy, inf=vx)        # branche (x,y)∈G
    cas_yx = branche(_couple_dans(vy, vx, G), sup=vx, inf=vy)        # branche (y,x)∈G
    but_thm = cas(disj, cas_xy, cas_yx)                              # (∃s)(∃i)(...)

    body = N.loi_deduction(et(appartient(vx, vE), appartient(vy, vE)), but_thm)
    return N.generalisation(x, N.generalisation(y, body))


# ════════════════════════════════════════════════════════════════════════════
#  REMARQUE (E.III.14) — totalement ordonné ⇒ réticulé
# ════════════════════════════════════════════════════════════════════════════
# @livre Ch.III §1.12 Rem.- | E III.14 L.23-24 | PDF p.117
def totalement_ordonne_implique_reticule(G="G", E_set="E"):
    """🎯 { est_ordre(G,E), totalite(G,E) } ⊢ est_reticule(G,E).

    REMARQUE (E.III.14) : « Un ensemble totalement ordonné est […] réticulé […]. »
    La 1ʳᵉ conjointe de est_reticule EST est_ordre (réutilisée) ; la clause des
    bornes se prouve pour x,y∈E en comparant x,y par totalité, la borne sup étant
    le plus grand des deux et la borne inf le plus petit.  (E.III.14, Remarque.)"""
    clause = _clause_bornes(G, E_set, "x", "y")
    Hord = N.assume(est_ordre(G, E_set))
    reticule = conjonction_intro(Hord, clause)            # est_reticule(G,E)  (sous {Hord,Htot})
    assert reticule.conclusion == cible_total_implique_reticule(G, E_set), \
        "conclusion ≠ est_reticule(G,E)"
    return reticule


__all__ = [
    "totalement_ordonne_implique_reticule",
    "cible_total_implique_reticule",
    "hypotheses_total_reticule",
    "totalite",
]
