"""CŒUR Prop. 8 — CAS 1 assemblé : h(*)=* ⟹ Eq(A×{0}, B×{0}).

On combine les quatre conjoints de est_bijection_de(g, A×{0}, B×{0}) où
g := h|(A×{0}) :

  • g_fonctionnel  — {h fonctionnel} ⊢ est_fonctionnel(g) ;
  • g_domaine      — {A×{0}⊂dom h} ⊢ dom g = A×{0} ;
  • g_injective    — {inj(h,A⊔{∅}), A×{0}⊂dom h, h fonct, A×{0}⊂A⊔{∅}} ⊢ inj(g,A×{0}) ;
  • g_image        — {h fonct, inj(h,·), dom h=A⊔{∅}, image h=B⊔{∅}, h(*)=*} ⊢
                       image(g,A×{0}) = B×{0}.

Les hypothèses dérivées (A×{0}⊂dom h depuis dom h=A⊔{∅}, A×{0}⊂A⊔{∅} clos) sont
coupées ; il ne reste que est_bijection_de(h,A⊔{∅},B⊔{∅}) et h(*)=*.  S5 donne
Eq(A×{0},B×{0}).

  • cas_fixe_bijection — {est_bijection_de(h,A⊔{∅},B⊔{∅}), h(*)=*} ⊢
                           est_bijection_de(g, A×{0}, B×{0}) ;
  • eq_copies_cas_fixe — ⊢ est_bijection_de(h,A⊔{∅},B⊔{∅}) ⇒ (h(*)=* ⇒ Eq(A×{0},B×{0})).
"""
from __future__ import annotations

from bourbaki.logique.formule import var, egal, impl
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.tactiques.tactiques_abrege2 import (conjonction_intro,
                               conjonction_elim_gauche, conjonction_elim_droite)
from bourbaki.ensembles.familles.ii_4_reunion_intersection_familles.ii_4_recollement_somme.ensembles_somme_disjointe import UN, somme_disjointe
from bourbaki.cardinaux.ensembles_cardinaux import est_bijection_de, equipotent
from bourbaki.cardinaux.arithmetique.ensembles_prop8_coeur._g import (
    A0_terme, G_RESTR, g_fonctionnel, g_injective, _cut)
from bourbaki.cardinaux.arithmetique.ensembles_prop8_coeur._domaine import g_domaine
from bourbaki.cardinaux.arithmetique.ensembles_prop8_coeur._image import g_image
from bourbaki.cardinaux.arithmetique.ensembles_prop8_coeur._incl import (
    A0_inclus_AS, A0_inclus_dom)


_STAR = E.couple(E.VIDE, UN)            # * = (∅, 1)
_H = "h"


def cas_fixe_bijection(a="A", b="B", h=_H):
    """{est_bijection_de(h,A⊔{∅},B⊔{∅}), h(*)=*} ⊢ est_bijection_de(g, A×{0}, B×{0}).

    g = h|(A×{0}).  Les 4 conjoints, avec leurs hypothèses dérivées coupées."""
    vh = var(h)
    va = var(a) if isinstance(a, str) else a
    vb = var(b) if isinstance(b, str) else b
    AS = somme_disjointe(va, E.singleton(E.VIDE))     # A⊔{∅}
    BS = somme_disjointe(vb, E.singleton(E.VIDE))     # B⊔{∅}
    A0 = A0_terme(a)
    g = G_RESTR(a, h)

    # Extraire fun, dom, inj, img de est_bijection_de(h, A⊔{∅}, B⊔{∅})
    bij = N.assume(est_bijection_de(vh, AS, BS))
    fun = conjonction_elim_gauche(conjonction_elim_gauche(bij))    # est_fonctionnel(h)
    domh = conjonction_elim_droite(conjonction_elim_gauche(bij))   # dom h = A⊔{∅}
    inj = conjonction_elim_gauche(conjonction_elim_droite(bij))    # injective_dans(h, A⊔{∅})
    img = conjonction_elim_droite(conjonction_elim_droite(bij))    # image h = B⊔{∅}

    # Inclusions dérivées
    A0_dom = _cut(egal(E.dom(vh), AS), domh, A0_inclus_dom(a, h))  # A×{0}⊂dom h (sous bij)
    A0_AS = A0_inclus_AS(a)                                        # A×{0}⊂A⊔{∅} (clos)

    # Conjoint 1 : fonctionnel(g)  (hyp : h fonctionnel)
    c1 = _cut(E.est_fonctionnel(vh), fun, g_fonctionnel(a, h))

    # Conjoint 2 : dom g = A×{0}  (hyp : A×{0}⊂dom h)
    from bourbaki.logique.formule import inclus
    c2 = _cut(inclus(A0, E.dom(vh)), A0_dom, g_domaine(a, h))

    # Conjoint 3 : injective_dans(g, A×{0})
    c3 = g_injective(a, AS, h)                # hyps : inj(h), A0⊂dom h, h fonct, A0⊂AS
    c3 = _cut(E.injective_dans(vh, AS), inj, c3)
    c3 = _cut(inclus(A0, E.dom(vh)), A0_dom, c3)
    c3 = _cut(E.est_fonctionnel(vh), fun, c3)
    c3 = _cut(inclus(A0, AS), A0_AS, c3)

    # Conjoint 4 : image(g, A×{0}) = B×{0}   (hyps : fun, inj, dom h=AS, img, fix)
    c4 = g_image(a, b, h)
    c4 = _cut(E.est_fonctionnel(vh), fun, c4)
    c4 = _cut(E.injective_dans(vh, AS), inj, c4)
    c4 = _cut(egal(E.dom(vh), AS), domh, c4)
    c4 = _cut(egal(E.image(vh, AS), BS), img, c4)
    # reste l'hypothèse h(*)=* (CAS 1)

    # est_bijection_de(g, A×{0}, B×{0}) = ((fonctionnel ∧ dom) ∧ (inj ∧ surj))
    return conjonction_intro(conjonction_intro(c1, c2), conjonction_intro(c3, c4))


def eq_copies_cas_fixe(a="A", b="B", h=_H):
    """⊢ est_bijection_de(h,A⊔{∅},B⊔{∅}) ⇒ ((h(*)=*) ⇒ Eq(A×{0}, B×{0})).

    CAS 1 du cœur back-and-forth : si la bijection h fixe le marqueur *, sa
    restriction g = h|(A×{0}) est une bijection A×{0}→B×{0}, d'où l'équipotence des
    copies de gauche (S5 sur est_bijection_de)."""
    vh = var(h)
    va = var(a) if isinstance(a, str) else a
    vb = var(b) if isinstance(b, str) else b
    AS = somme_disjointe(va, E.singleton(E.VIDE))
    BS = somme_disjointe(vb, E.singleton(E.VIDE))
    A0 = A0_terme(a)
    B0 = E.produit(vb, E.singleton(__import__(
        "bourbaki.ensembles.familles.ii_4_reunion_intersection_familles.ii_4_recollement_somme.ensembles_somme_disjointe", fromlist=["ZERO"]).ZERO))
    g = G_RESTR(a, h)
    bijg = cas_fixe_bijection(a, b, h)        # {bij(h), h(*)=*} ⊢ bij(g, A0, B0)
    # Eq(A×{0}, B×{0}) via S5 (témoin g)
    eq = N.modus_ponens(bijg, N.s5(est_bijection_de(var("F"), A0, B0), g, "F"))
    # décharger les 2 hypothèses
    fix = egal(E.valeur(vh, _STAR), _STAR)
    eq = N.loi_deduction(fix, eq)             # bij(h) ⊢ (h(*)=* ⇒ Eq(A0,B0))
    return N.loi_deduction(est_bijection_de(vh, AS, BS), eq)


__all__ = ["cas_fixe_bijection", "eq_copies_cas_fixe"]
