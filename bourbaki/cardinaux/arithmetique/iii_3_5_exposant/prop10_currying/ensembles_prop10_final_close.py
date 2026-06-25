"""§III.3.5 — PROPOSITION 10 CLOSE : a^(b·c) = (a^b)^c (currying), assemblage final.

    ⊢ Card(𝓕(B×C; A)) = Card(𝓕(C; 𝓕(B;A)))          (= cible_prop10)

Route CANTOR–BERNSTEIN (deux injections), strictement identique à
prop9_depuis_deux_injections :
  • DIRECTION A : inf_egal_curry   ⊢ inf_egal_card(𝓕(B×C;A), 𝓕(C;𝓕(B;A)))  (a^(bc)≤(a^b)^c) ;
  • DIRECTION B : inf_egal_uncurry ⊢ inf_egal_card(𝓕(C;𝓕(B;A)), 𝓕(B×C;A))  ((a^b)^c≤a^(bc)) ;
  • cantor_bernstein(dom,cod) (généralise-puis-instancie, term-tolérant) ⊢
        (dom≤cod et cod≤dom) ⇒ Eq(dom,cod) ;
  • MP avec (inf_A et inf_B) ⊢ Eq(dom,cod) ;
  • _prop1_direct_t(dom,cod) ⊢ Eq(dom,cod) ⇒ Card dom = Card cod.

dom = 𝓕(B×C;A) = domaine_lambda, cod = 𝓕(C;𝓕(B;A)) = codomaine_lambda.  Aucun axiome
ajouté : tout dérive des deux injections (graphe_de + pont + application_egale_par_valeurs)
et de cantor_bernstein.  Rien postulé.
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import Terme, var
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import conjonction_intro, instancie
from bourbaki.cardinaux.arithmetique.iii_3_5_exposant.prop10_currying.ensembles_prop10_currying import (
    domaine_lambda, codomaine_lambda)
from bourbaki.cardinaux.arithmetique.iii_3_5_exposant.prop10_currying.ensembles_prop10_inj_curry import inf_egal_curry
from bourbaki.cardinaux.arithmetique.iii_3_5_exposant.prop10_currying.ensembles_prop10_inj_uncurry import inf_egal_uncurry
from bourbaki.cardinaux.arithmetique.iii_3_3_produit.ensembles_arith_cardinale import _prop1_direct_t


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# @livre Ch.III §3.5 Cor.3 | E III.29 L.6-9 | PDF p.132
def prop10_close(a="A", b="B", c="C"):
    """⊢ Card(𝓕(B×C; A)) = Card(𝓕(C; 𝓕(B;A))).   (PROP 10, E.III.3.5 ; a^(b·c)=(a^b)^c.)

    INCONDITIONNEL.  Cantor–Bernstein sur les deux injections curry/uncurry, puis
    Proposition 1 (sens direct).  Conclusion LITTÉRALEMENT cible_prop10(A,B,C)."""
    from bourbaki.cardinaux.ensembles_cantor_bernstein_final import cantor_bernstein
    va, vb, vc = _t(a), _t(b), _t(c)
    dom = domaine_lambda(va, vb, vc)        # 𝓕(B×C; A)
    cod = codomaine_lambda(va, vb, vc)      # 𝓕(C; 𝓕(B;A))
    inf_A = inf_egal_curry(va, vb, vc)      # inf_egal_card(dom, cod)   (Direction A)
    inf_B = inf_egal_uncurry(va, vb, vc)    # inf_egal_card(cod, dom)   (Direction B)
    # cantor_bernstein term-tolérant : généralise (A,B) puis instancie (dom,cod)
    cb_nom = cantor_bernstein("A", "B", "f", "g")            # (A≤B et B≤A) ⇒ Eq(A,B)
    cb_gen = N.generalisation("A", N.generalisation("B", cb_nom))
    cb = instancie(instancie(cb_gen, dom), cod)             # (dom≤cod et cod≤dom) ⇒ Eq(dom,cod)
    eq = N.modus_ponens(conjonction_intro(inf_A, inf_B), cb)  # Eq(dom, cod)
    prop1 = _prop1_direct_t(dom, cod)                       # Eq(dom,cod) ⇒ Card dom = Card cod
    return N.modus_ponens(eq, prop1)                       # Card(𝓕(B×C;A)) = Card(𝓕(C;𝓕(B;A)))


__all__ = ["prop10_close"]
