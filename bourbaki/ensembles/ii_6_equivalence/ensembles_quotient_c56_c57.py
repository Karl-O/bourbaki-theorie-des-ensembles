"""§II.6 — Critères C56 et C57 (passage au quotient).

Module NEUF.  On NE MODIFIE AUCUN fichier déposé ; on RÉUTILISE strictement les
NOTIONS et THÉORÈMES déjà présents :

  • `est_compatible(P, R)` = (∀x)(∀y)((P{x} et R{x,y}) ⇒ P{y})   (E.II.6.3, abrégé) ;
  • `relation_quotient(P, e, g)` = t∈E/R et (∃x)(x∈t et P{x})      (E.II.6.3, abrégé) ;
  • `est_compatible_application(f, R)` = (∀x)(∀x')(R{x,x'} ⇒ f(x)=f(x'))  (E.II.6.5) ;
  • C55 sous la forme `projection_valeur_classe`/`relation_ssi_classe_egale`
    (`ensembles_quotient_props`) : p(x)=p(y) ⇔ x R y ;
  • la factorisation C57 « f=h∘p ⇒ f compatible » (`relations.ensembles_quotient_props`).

────────────────────────────────────────────────────────────────────────────────
CRITÈRE C56  (E.II.6.3) — relation déduite de P par passage au quotient.

  Bourbaki : « Soit R{x,x'} une relation d'équivalence dans E, P{x} une relation
  compatible avec R.  Alors, si t désigne un élément de E/R, la relation
        « t∈E/R et (∃x)(x∈t et P{x}) »
  est équivalente à la relation
        « t∈E/R et (∀x)((x∈t) ⇒ P{x}) ».  »

  C'est le cœur du critère : sous compatibilité, « il EXISTE x∈t avec P{x} » ⟺
  « P{x} POUR TOUT x∈t » (P est constante-au-sens-vrai sur la classe t).

  `c56_quotient_existe_ssi_pourtout` ⊢, sous les hypothèses HONNÊTES
        { P compatible avec R,
          t non vide : (∃x)(x∈t),
          membres de t mutuellement R-liés : (∀x)(∀a)((a∈t et x∈t) ⇒ R{a,x}) }
        (∃x)(x∈t et P{x})  ⇔  (∀x)((x∈t) ⇒ P{x}).
  Les deux hypothèses « t non vide » et « membres R-liés » sont des propriétés
  VRAIES d'une classe d'équivalence t = Cl_R(a) (non-vide car a∈Cl_R(a) ;
  R-liés car z,z'∈Cl_R(a) ⇒ R{a,z}, R{a,z'} ⇒ R{z,z'}).  On les laisse
  EXPLICITES dans le séquent (jamais postulées).

────────────────────────────────────────────────────────────────────────────────
CRITÈRE C57  (E.II.6.5) — propriété universelle du quotient.

  Bourbaki : « Soit R une relation d'équivalence dans E, g l'application canonique
  de E sur E/R.  Pour qu'une application f de E dans F soit compatible avec R, il
  faut et il suffit que f puisse se mettre sous la forme h∘g, h étant une
  application de E/R dans F.  L'application h est uniquement déterminée par f. »

  • Sens « il FAUT » (f=h∘p ⇒ f compatible) : DÉJÀ clos dans le dépôt
    (`factorisation_compatible_Rp`, `factorisation_implique_compatible`).
  • UNICITÉ de h : DÉJÀ close (`factorisation_unique`).
  • Sens « il SUFFIT » — BIEN-DÉFINITION de h(p(x)):=f(x).  Le seul point dur :
    h est bien définie ⟺ p(x)=p(y) entraîne f(x)=f(y).  C'est exactement
    `c57_bien_definie` ci-dessous : sous { f compatible avec R, C55 : p(x)=p(y)⇔xRy }
        p(x)=p(y) ⇒ f(x)=f(y).
    C'est LA justification « well-defined BECAUSE f compatible » de la construction
    de l'application déduite h.

theorie_ensembles() RESTE à 22 axiomes (AUCUN axiome neuf).  Toutes les preuves
sortent du noyau abrégé.  Rien postulé ; aucune tautologie (conclusion ∉ hyp).

Liants : « x », « a » (membres de la classe t) ; « yc » (témoin de t non vide,
distinct des liants internes).
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (Terme, var, egal, et, impl, equiv,
                                       appartient, existe, pourtout)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, instancie)
from bourbaki.logique.i_3_quantifies.tactiques_abrege_quantif import existe_elimination


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# ═══════════════════════════════════════════════════════════════════════════════
# C56 — « (∃x)(x∈t et P{x}) ⇔ (∀x)((x∈t)⇒P{x}) »  sous P compatible avec R
# ═══════════════════════════════════════════════════════════════════════════════
def membres_t_R_lies(g, t, x="x", a="a"):
    """« les membres de t sont mutuellement R-liés » := (∀x)(∀a)((a∈t et x∈t) ⇒ R{a,x}).

    Propriété VRAIE d'une classe t = Cl_R(a₀) (deux éléments d'une même classe sont
    R-équivalents).  R = rel_graphe(g) ; t : terme (la classe).  Renvoie une Formule."""
    R = E.rel_graphe(g)
    vt, vx, va = _t(t), var(x), var(a)
    return pourtout(x, pourtout(a, impl(et(appartient(va, vt), appartient(vx, vt)),
                                        R(va, vx))))


# @livre Ch.II §6.3 Crit.C56 | E II.43 L.3-6 | PDF p.94
def c56_quotient_existe_ssi_pourtout(P=None, g="G", t="t", x="x", a="a", yc="yc"):
    """C56 (E.II.6.3) — cœur du passage au quotient ; clos modulo hyp.

    { P compatible avec R,
      (∃x)(x∈t)                            [t non vide],
      (∀x)(∀a)((a∈t et x∈t)⇒R{a,x})        [membres de t R-liés] }
        ⊢  (∃x)(x∈t et P{x})  ⇔  (∀x)((x∈t)⇒P{x}).

    Preuve (fidèle à Bourbaki E.II.43) :
      ⇒ : soit a∈t tel que P{a} (témoin du ∃).  Pour x∈t arbitraire : a,x∈t donc
          R{a,x} (hyp R-liés) ; P{a} et R{a,x} ⇒ P{x} (compatibilité).  D'où
          (∀x)((x∈t)⇒P{x}).  Le témoin a est éliminé (existe_elimination) car la
          conclusion ne le contient pas.
      ⇐ : (∃x)(x∈t) donne un témoin yc∈t ; (∀x)((x∈t)⇒P{x}) donne P{yc} ; d'où
          (∃x)(x∈t et P{x}).

    P : relation (fonction (Terme)→Formule) à graphe par défaut.  g : graphe de R ;
    t : la classe.  Clos modulo les 3 hypothèses EXPLICITES ci-dessus."""
    if P is None:
        P = lambda u: appartient(u, var("GP"))       # relation P{x} := x∈GP (graphe arbitraire)
    R = E.rel_graphe(g)
    vt = _t(t)
    vx, va, vyc = var(x), var(a), var(yc)

    hcompat = N.assume(E.est_compatible(P, R, x, a))      # (∀x)(∀a)((P{x}et R{x,a})⇒P{a})
    hlies = N.assume(membres_t_R_lies(g, vt, x, a))       # (∀x)(∀a)((a∈t et x∈t)⇒R{a,x})

    # ─── sens ⇒ : (∃x)(x∈t et P{x}) ⇒ (∀x)((x∈t)⇒P{x}) ───────────────────────────
    # corps du ∃ avec témoin lettre « a » : a∈t et P{a}
    body_ex = et(appartient(va, vt), P(va))
    h_body = N.assume(body_ex)                            # a∈t et P{a}
    h_aint = conjonction_elim_gauche(h_body)              # a∈t
    h_Pa = conjonction_elim_droite(h_body)                # P{a}
    # sous x∈t : R{a,x} (hyp R-liés instanciée en (x,a)), puis P{x} (compatibilité)
    h_xint = N.assume(appartient(vx, vt))                 # x∈t
    lies_xa = instancie(instancie(hlies, vx), va)         # (a∈t et x∈t)⇒R{a,x}
    R_ax = N.modus_ponens(conjonction_intro(h_aint, h_xint), lies_xa)   # R{a,x}
    compat_ax = instancie(instancie(hcompat, va), vx)     # (P{a}et R{a,x})⇒P{x}
    P_x = N.modus_ponens(conjonction_intro(h_Pa, R_ax), compat_ax)      # P{x}
    imp_xint = N.loi_deduction(appartient(vx, vt), P_x)   # (x∈t)⇒P{x}
    forall_under_body = N.generalisation(x, imp_xint)     # (∀x)((x∈t)⇒P{x})  [sous body_ex]
    imp_body = N.loi_deduction(body_ex, forall_under_body)  # (a∈t et P{a})⇒(∀x)(…)
    fwd = existe_elimination(imp_body, a)                 # (∃a)(a∈t et P{a}) ⇒ (∀x)(…)
    # (∃a)(a∈t et P{a}) est α-équiv à (∃x)(x∈t et P{x}) — on garde le liant « a »
    # pour l'énoncé ; voir _enonce_c56 ci-dessous (liant « a » pour le ∃).

    # ─── sens ⇐ : (∀x)((x∈t)⇒P{x}) ⇒ (∃a)(a∈t et P{a}) ───────────────────────────
    h_forall = N.assume(pourtout(x, impl(appartient(vx, vt), P(vx))))   # (∀x)((x∈t)⇒P{x})
    h_ex = N.assume(existe(yc, appartient(vyc, vt)))      # (∃yc)(yc∈t)  [t non vide]
    # sous yc∈t : P{yc}, donc yc∈t et P{yc}, donc (∃a)(a∈t et P{a})
    h_ycint = N.assume(appartient(vyc, vt))               # yc∈t
    P_yc = N.modus_ponens(h_ycint, instancie(h_forall, vyc))   # P{yc}
    witness = conjonction_intro(h_ycint, P_yc)            # yc∈t et P{yc}
    ex_intro = N.modus_ponens(witness, N.s5(et(appartient(va, vt), P(va)), vyc, a))
    #   S5 : (yc|a)(a∈t et P{a}) ⇒ (∃a)(a∈t et P{a})
    imp_ycint = N.loi_deduction(appartient(vyc, vt), ex_intro)   # (yc∈t)⇒(∃a)(…)
    elim_yc = existe_elimination(imp_ycint, yc)           # (∃yc)(yc∈t) ⇒ (∃a)(…)
    ex_witness = N.modus_ponens(h_ex, elim_yc)            # (∃a)(a∈t et P{a})  [sous h_forall,h_ex]
    bwd = N.loi_deduction(pourtout(x, impl(appartient(vx, vt), P(vx))), ex_witness)

    return conjonction_intro(fwd, bwd)                    # (∃a)(a∈t et P{a}) ⇔ (∀x)((x∈t)⇒P{x})


# ═══════════════════════════════════════════════════════════════════════════════
# C57 — bien-définition de h (sens « il suffit » : f compatible ⇒ h existe)
# ═══════════════════════════════════════════════════════════════════════════════
# @livre Ch.II §6.5 Crit.C57 | E II.44 L.17-21 | PDF p.95
def c57_bien_definie(f="f", g="G", e="E", x="x", y="yb"):
    """C57 (E.II.6.5), bien-définition de h(p(x)):=f(x) ; clos modulo hyp.

    { f compatible avec R (est_compatible_application),
      C55 : p(x)=p(y) ⇔ R{x,y}   [p = appli. canonique de E sur E/R] }
        ⊢  p(x)=p(y)  ⇒  f(x)=f(y).

    C'est LA justification du « il suffit » de C57 : la formule h(p(x)) := f(x) est
    BIEN DÉFINIE (ne dépend pas du représentant x de la classe p(x)) PRÉCISÉMENT
    PARCE QUE f est compatible avec R.  En effet, si p(x)=p(y) alors x R y (C55),
    donc f(x)=f(y) (compatibilité) : f est constante sur les fibres de p, ce qui
    permet de poser h sur le quotient.  Combiné à `factorisation_unique` (unicité de
    h) et `factorisation_compatible_Rp` (réciproque « il faut »), ceci ferme C57.

    f : application (graphe) ; g : graphe de R ; e = E.  R = rel_graphe(g),
    p = application_canonique(g,e).  Clos modulo { f compatible, C55 }."""
    R = E.rel_graphe(g)
    vf, vg, ve = _t(f), _t(g), _t(e)
    vx, vy = var(x), var(y)
    p = E.application_canonique(vg, ve)
    px, py = E.valeur(p, vx), E.valeur(p, vy)
    fx, fy = E.valeur(vf, vx), E.valeur(vf, vy)

    # hyp 1 : f compatible avec R  → instance R{x,y} ⇒ f(x)=f(y)
    hcompat = N.assume(E.est_compatible_application(vf, R, x, y))
    compat_xy = instancie(instancie(hcompat, vx), vy)    # R{x,y} ⇒ f(x)=f(y)
    # hyp 2 : C55  p(x)=p(y) ⇔ R{x,y}
    hC55 = N.assume(equiv(egal(px, py), R(vx, vy)))      # (p(x)=p(y)) ⇔ R{x,y}
    # sous p(x)=p(y) : R{x,y} (C55 avant), puis f(x)=f(y) (compatibilité)
    h_pxy = N.assume(egal(px, py))                       # p(x)=p(y)
    R_xy = N.modus_ponens(h_pxy, equivalence_avant(hC55))   # R{x,y}
    eq_fxy = N.modus_ponens(R_xy, compat_xy)             # f(x)=f(y)
    return N.loi_deduction(egal(px, py), eq_fxy)         # (p(x)=p(y)) ⇒ (f(x)=f(y))


__all__ = [
    "membres_t_R_lies",
    "c56_quotient_existe_ssi_pourtout",
    "c57_bien_definie",
]
