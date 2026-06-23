"""§III.3.4 — Existence de transposition pour la Proposition 8 :  HT(B, c₀).

On instancie `transposition_existe` à  S = B⊔{∅},  p = * = (∅,1),  q = c₀  pour
fournir la brique de transposition exigée par ensembles_prop8_transposition :

    HT(B, c₀) := (∃τ)( est_bijection_de(τ, B⊔{∅}, B⊔{∅})  et  τ(c₀) = * ).

On la prouve sous l'hypothèse  c₀ ∈ B×{0}  (le CAS 2 de la Proposition 8, où la
bijection h envoie le marqueur DANS la copie de gauche de droite) :

  • *∈B⊔{∅}        : marqueur_dans_somme(B)            [clos] ;
  • c₀∈B⊔{∅}       : c₀∈B×{0} ⊂ B⊔{∅}                  [somme_un_plus_point ⇐ gauche] ;
  • ¬(*=c₀)        : *∉B×{0} (marqueur_hors_copie_gauche) mais c₀∈B×{0}  ⇒ *≠c₀.

D'où  ht_de_copie_gauche(B,c₀) : ⊢ (c₀∈B×{0}) ⇒ HT(B,c₀).  Puis, pour h, en posant
c₀=h(*) :  ht_glob_conditionnel(A,B) : ⊢ (∀h)((bij(h,·) et h(*)∈B×{0}) ⇒ HT(B,h(*))).

⚠ HONNÊTETÉ (anti-faux) : la forme INCONDITIONNELLE  HT_glob(A,B)=(∀h)HT(B,h(*))
de ensembles_prop8_transposition.transposition_globale N'EST PAS un théorème pour h
arbitraire : si h n'est pas une bijection, h(*) peut tomber HORS de B⊔{∅}, et aucune
bijection de B⊔{∅} n'envoie un point extérieur sur * (valeur τ(c₀) indéterminée hors
dom τ = B⊔{∅}).  La version CORRECTE est CONDITIONNÉE par (bij(h) et h(*)∈B×{0}),
exactement le cadre du CAS 2.  Voir le rapport : le verrou résiduel de la Prop. 8
est l'ADAPTATION de prop8_via_transposition_mod_HT à cette HT CONDITIONNELLE.
"""
from __future__ import annotations

from bourbaki.logique.formule import (Terme, var, egal, et, non, appartient, existe,
                                       pourtout)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, instancie)
from bourbaki.logique.tactiques.tactiques_abrege_egalite import symetrie
from bourbaki.ensembles.familles.ii_4_reunion_intersection_familles.ii_4_recollement_somme.ensembles_somme_disjointe import (somme_disjointe,
                                                                   ZERO, UN)
from bourbaki.cardinaux.ensembles_cardinaux import est_bijection_de
from bourbaki.cardinaux.arithmetique.ensembles_transposition._existence import (
    transposition_existe)
from bourbaki.cardinaux.arithmetique.ensembles_prop8_plus_point import (
    marqueur_dans_somme, marqueur_hors_copie_gauche, somme_un_plus_point)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


_STAR = E.couple(E.VIDE, UN)            # * = (∅, 1)


def _BS(b):
    return somme_disjointe(_t(b), E.singleton(E.VIDE))


def _B0(b):
    return E.produit(_t(b), E.singleton(ZERO))


def _transposition_existe_t(tS, tp, tq):
    """⊢ (p∈S et q∈S et ¬(p=q)) ⇒ (∃F)(bij(F,S,S) et F(q)=p)  pour des TERMES S,p,q.

    transposition_existe n'est SAINE que sur des NOMS de variables (transpo_membre
    déroule des De Morgan sur (x,y) et casse si x,y sont des termes composés) ; on la
    généralise sur S,p,q puis on instancie aux termes (renommage déterministe,
    capture-évitant), même contournement que _prop1_direct_t / _composee_bijection_t."""
    gen = N.generalisation("S", N.generalisation("p", N.generalisation("q",
        transposition_existe("S", "p", "q"))))
    return instancie(instancie(instancie(gen, _t(tS)), _t(tp)), _t(tq))


def _hstar_in_BS(b, c0):
    """⊢ (c₀ ∈ B×{0}) ⇒ (c₀ ∈ B⊔{∅}).   (la copie de gauche est dans la somme.)"""
    vb = _t(b)
    B0 = _B0(b)
    sup = somme_un_plus_point(b, c0)                          # c₀∈B⊔{∅} ⇔ (c₀∈B×{0} ou c₀=*)
    h = N.assume(appartient(c0, B0))                          # c₀∈B×{0}
    disj = N.modus_ponens(h, N.s2(appartient(c0, B0), egal(c0, _STAR)))   # (c₀∈B×{0} ou c₀=*)
    in_BS = N.modus_ponens(disj, equivalence_arriere(sup))   # c₀∈B⊔{∅}
    return N.loi_deduction(appartient(c0, B0), in_BS)


def _star_ne_hstar(b, c0):
    """⊢ (c₀ ∈ B×{0}) ⇒ ¬(* = c₀).   (* ∉ B×{0} mais c₀ ∈ B×{0}, donc *≠c₀.)"""
    vb = _t(b)
    B0 = _B0(b)
    star_hors = marqueur_hors_copie_gauche(b)                 # ¬(*∈B×{0})
    h = N.assume(appartient(c0, B0))                          # c₀∈B×{0}
    # si *=c₀ alors *∈B×{0}  (Leibniz c₀→* sur ·∈B×{0}), contredit ¬(*∈B×{0})
    heq = N.assume(egal(_STAR, c0))                           # *=c₀
    c0_eq_star = N.modus_ponens(heq, symetrie(_STAR, c0))     # c₀=*
    star_in = N.modus_ponens(h, equivalence_avant(N.modus_ponens(
        c0_eq_star, N.s6(c0, _STAR, "w", appartient(var("w"), B0)))))   # *∈B×{0}
    falso = N.modus_ponens(star_in, N.modus_ponens(star_hors,
        N.s2(non(appartient(_STAR, B0)), non(egal(_STAR, c0)))))
    ne = N.modus_ponens(N.loi_deduction(egal(_STAR, c0), falso), N.s1(non(egal(_STAR, c0))))   # ¬(*=c₀)
    return N.loi_deduction(appartient(c0, B0), ne)            # (c₀∈B×{0}) ⇒ ¬(*=c₀)


def ht_de_copie_gauche(b="B", c0=None, tau="tau"):
    """⊢ (c₀ ∈ B×{0}) ⇒ (∃τ)(est_bijection_de(τ, B⊔{∅}, B⊔{∅}) et τ(c₀) = *).

    = (c₀∈B×{0}) ⇒ HT(B,c₀).  On instancie transposition_existe à S=B⊔{∅}, p=*, q=c₀ :
    (*∈S et c₀∈S et ¬(*=c₀)) ⇒ (∃τ)(bij(τ,S,S) et τ(c₀)=*).  Les trois conditions sont
    réunies sous c₀∈B×{0} : *∈S (marqueur_dans_somme), c₀∈S (_hstar_in_BS), *≠c₀
    (_star_ne_hstar).  L'existentiel donne EXACTEMENT HT(B,c₀)."""
    vb = _t(b)
    BS, B0 = _BS(b), _B0(b)
    c0 = _STAR if c0 is None else c0
    # transposition_existe(S=B⊔{∅}, p=*, q=c₀)  (version TERME, par gén.-instanciation)
    te = _transposition_existe_t(BS, _STAR, c0)              # (*∈S et c₀∈S et ¬(*=c₀)) ⇒ (∃F)(bij(F,S,S) et F(c₀)=*)
    in_c0_B0 = N.assume(appartient(c0, B0))                   # c₀∈B×{0}
    star_in = marqueur_dans_somme(b)                         # *∈B⊔{∅}
    c0_in = N.modus_ponens(in_c0_B0, _hstar_in_BS(b, c0))    # c₀∈B⊔{∅}
    ne = N.modus_ponens(in_c0_B0, _star_ne_hstar(b, c0))    # ¬(*=c₀)
    conds = conjonction_intro(conjonction_intro(star_in, c0_in), ne)   # (*∈S et c₀∈S et ¬(*=c₀))
    ex = N.modus_ponens(conds, te)                           # (∃F)(bij(F,S,S) et F(c₀)=*)  [hyp c₀∈B×{0}]
    # α-renommer ∃F → ∃tau pour coïncider avec transposition_hypothese (lieur "tau")
    from bourbaki.logique.tactiques.tactiques_abrege_quantif import alpha_existe
    matrice_F = et(est_bijection_de(var("F"), BS, BS), egal(E.valeur(var("F"), c0), _STAR))
    al = alpha_existe("F", tau, matrice_F)                   # (∃F)matrice ⇔ (∃tau)matrice
    ex_tau = N.modus_ponens(ex, equivalence_avant(al))       # (∃tau)(bij(tau,S,S) et tau(c₀)=*) = HT(B,c₀)
    return N.loi_deduction(appartient(c0, B0), ex_tau)       # (c₀∈B×{0}) ⇒ HT(B,c₀)


def ht_glob_conditionnel(a="A", b="B", h="h", tau="tau"):
    """⊢ (∀h)((bij(h,A⊔{∅},B⊔{∅}) et h(*)∈B×{0}) ⇒ HT(B,h(*))).

    La forme CORRECTE (conditionnelle) de l'hypothèse de transposition : pour toute
    bijection h envoyant le marqueur dans la copie de gauche de droite (CAS 2), il
    EXISTE une transposition de B⊔{∅} ramenant h(*) sur *.  On pose c₀=h(*) dans
    ht_de_copie_gauche ; l'hypothèse bij(h) n'est pas requise pour la transposition
    elle-même (seule h(*)∈B×{0} l'est), mais elle reste dans l'antécédent pour coller
    au cadre CAS 2 (cas2_via_transposition).  CONSTRUIT, jamais postulé."""
    vh = _t(h)
    AS = somme_disjointe(_t(a), E.singleton(E.VIDE))
    BS, B0 = _BS(b), _B0(b)
    hstar = E.valeur(vh, _STAR)                              # h(*)
    ht_imp = ht_de_copie_gauche(b, hstar, tau)              # (h(*)∈B×{0}) ⇒ HT(B,h(*))
    # antécédent CAS 2 : (bij(h) et h(*)∈B×{0})
    ante = et(est_bijection_de(vh, AS, BS), appartient(hstar, B0))
    hante = N.assume(ante)
    h_in_B0 = conjonction_elim_droite(hante)                # h(*)∈B×{0}
    ht = N.modus_ponens(h_in_B0, ht_imp)                    # HT(B,h(*))  [hyp ante]
    body = N.loi_deduction(ante, ht)                        # (bij(h) et h(*)∈B×{0}) ⇒ HT(B,h(*))
    return N.generalisation(h, body)                        # (∀h)(...)


__all__ = ["ht_de_copie_gauche", "ht_glob_conditionnel"]
