"""§II.3.8 — Rétractions et sections (Définition 11, Proposition 8, Théorème 1,
Proposition 9).

Encodage MATRICIEL (cf. Implémentation du Texte.tex §3.8, fidèle à Bourbaki) :
  • r est une rétraction associée à f (f : A→B injective) ⇔ r∘f = Id_A
    ⇔ (∀x)(x∈A ⇒ r(f(x))=x)                     [E.est_retraction]
  • s est une section associée à f (f : A→B surjective) ⇔ f∘s = Id_B
    ⇔ (∀y)(y∈B ⇒ f(s(y))=y)                      [E.est_section]
où r(f(x)) = valeur(R, valeur(F, x)) et f(s(y)) = valeur(F, valeur(S, y)).

Théorèmes CERTIFIÉS par le noyau (clos) :
  - retraction_implique_injective  (Prop. 8, sens direct, cas injectif)
        ⊢ (r rétraction de f) ⇒ f injective-sur-A (variante gardée par x∈A,
          fidèle à « où x∈A et y∈A » de la démonstration)
  - section_construite_par_tau     (Prop. 8, sens réciproque, cas surjectif —
          CONSTRUCTION EFFECTIVE de la section via τ)
        ⊢ (∀y)(y∈B ⇒ (∃x)(y=f(x)))  ⇒  s := (y ↦ τx(y=f(x))) est une section de f
          [le cœur : f(τx(y=f(x)))=y dès qu'un antécédent existe (existe_temoin)]

REPORTÉ honnêtement (cf. champ « reportes » du rapport) : les parties exigeant
la composition-de-fonctions au niveau des VALEURS ((g∘f)(x)=g(f(x))), une
bijection-réciproque f⁻¹, ou le passage surjectivité-image ↔ surjectivité-valeur
(image(f,A)=B ⇔ (∀y∈B)(∃x)y=f(x)) — infrastructure absente / preuves lourdes.
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (var, egal, et, appartient, impl, pourtout, existe, tau, subst_f)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (conjonction_elim_gauche, conjonction_elim_droite,
                               instancie)
from bourbaki.logique.i_4_egalitaires.tactiques_abrege_egalite import symetrie, composer_egalites, congruence_terme


def retraction_implique_injective(r="R", f="F", a="A", u="u", up="up"):
    """⊢ (r rétraction associée à f) ⇒ (f injective sur A).   (Prop. 8, sens direct.)

    Conclusion EXACTE :
      E.est_retraction(R,F,A) ⇒ E.injective_dans(F,A)
    soit  (∀x)(x∈A ⇒ r(f(x))=x)  ⇒  (∀u)(∀u')((u∈A et u'∈A et f(u)=f(u'))⇒u=u').

    Preuve de Bourbaki : f(u)=f(u') ⟹ u = r(f(u)) = r(f(u')) = u'."""
    vR, vF, vA, vu, vup = var(r), var(f), var(a), var(u), var(up)
    hret = N.assume(E.est_retraction(vR, vF, vA))          # (∀x)(x∈A ⇒ r(f(x))=x)
    iu = instancie(hret, vu)                                # u∈A ⇒ r(f(u))=u
    iup = instancie(hret, vup)                              # u'∈A ⇒ r(f(u'))=u'
    hyp = et(et(appartient(vu, vA), appartient(vup, vA)),
             egal(E.valeur(vF, vu), E.valeur(vF, vup)))
    hg = N.assume(hyp)
    uA = conjonction_elim_gauche(conjonction_elim_gauche(hg))      # u∈A
    upA = conjonction_elim_droite(conjonction_elim_gauche(hg))     # u'∈A
    feq = conjonction_elim_droite(hg)                             # f(u)=f(u')
    rfu_u = N.modus_ponens(uA, iu)                               # r(f(u))=u
    rfup_up = N.modus_ponens(upA, iup)                          # r(f(u'))=u'
    # f(u)=f(u') ⟹ r(f(u))=r(f(u'))   (congruence du terme r(·))
    cong = N.modus_ponens(feq, congruence_terme(
        E.valeur(vF, vu), E.valeur(vF, vup), E.valeur(vR, var("w")), "w"))
    u_rfu = N.modus_ponens(rfu_u, symetrie(E.valeur(vR, E.valeur(vF, vu)), vu))  # u=r(f(u))
    chain1 = composer_egalites(u_rfu, cong)                     # u = r(f(u'))
    chain2 = composer_egalites(chain1, rfup_up)                 # u = u'
    imp = N.loi_deduction(hyp, chain2)
    gen = N.generalisation(u, N.generalisation(up, imp))
    return N.loi_deduction(E.est_retraction(vR, vF, vA), gen)


def section_construite_par_tau(f="F", b="B"):
    """⊢ (∀y)(y∈B ⇒ (∃x)(y=f(x))) ⇒ (∀y)(y∈B ⇒ f(s(y))=y), où s := y ↦ τx(y=f(x)).
       (Prop. 8, sens réciproque, cas surjectif — CONSTRUCTION EFFECTIVE de la
       section, §3.8 : « désignons par T le terme τ_y(x=f(y)) ; on a f(T)=x ».)

    Cœur : dès qu'un antécédent de y existe, le témoin canonique τx(y=f(x)) en
    est un, donc y = f(τx(y=f(x))) = f(s(y))  (via existe_temoin, réciproque de S5).
    La conclusion exhibe le graphe de la section s(y)=τx(y=f(x))."""
    vF, vB, vy, vx = var(f), var(b), var("y"), var("x")
    R = egal(vy, E.valeur(vF, vx))                              # y = f(x)
    hyp_surj = pourtout("y", impl(appartient(vy, vB), existe("x", R)))
    hsurj = N.assume(hyp_surj)
    inst = instancie(hsurj, vy)                                # y∈B ⇒ (∃x)(y=f(x))
    hyB = N.assume(appartient(vy, vB))
    exwit = N.modus_ponens(hyB, inst)                          # (∃x)(y=f(x))
    tw = N.existe_temoin(R, "x")                               # (∃x)(y=f(x)) ⇒ y=f(τxR)
    inst_wit = N.modus_ponens(exwit, tw)                       # y = f(s(y))
    lhs, rhs = inst_wit.conclusion.termes                      # lhs=y, rhs=f(s(y))
    sym = N.modus_ponens(inst_wit, symetrie(lhs, rhs))         # f(s(y)) = y
    inner = N.loi_deduction(appartient(vy, vB), sym)           # y∈B ⇒ f(s(y))=y
    gen = N.generalisation("y", inner)
    return N.loi_deduction(hyp_surj, gen)


def cible_retraction_implique_injective(r="R", f="F", a="A"):
    """Cible exacte de retraction_implique_injective (pour les tests)."""
    return impl(E.est_retraction(var(r), var(f), var(a)),
                E.injective_dans(var(f), var(a)))


def cible_section_construite_par_tau(f="F", b="B"):
    """Cible exacte de section_construite_par_tau (pour les tests).

    f(s(y)), avec s(y)=τx(y=f(x)), est l'instance-témoin de R={y=f(x)} en
    T=τx(R) : c'est subst_f(τx R, x, valeur(F,x)) = membre droit de existe_temoin.
    On reconstruit la cible par CE MÊME mécanisme (capture-évitante), ce qui rend
    le binder interne de valeur(F,·) cohérent avec la preuve."""
    vF, vB, vy, vx = var(f), var(b), var("y"), var("x")
    R = egal(vy, E.valeur(vF, vx))                             # y = f(x)
    hyp_surj = pourtout("y", impl(appartient(vy, vB), existe("x", R)))
    wit = subst_f(tau("x", R), "x", R)                         # y = f(s(y))  [= (τxR|x)R]
    fsy = wit.termes[1]                                        # f(s(y))
    return impl(hyp_surj, pourtout("y", impl(appartient(vy, vB), egal(fsy, vy))))


__all__ = ["retraction_implique_injective", "section_construite_par_tau",
           "cible_retraction_implique_injective", "cible_section_construite_par_tau"]
