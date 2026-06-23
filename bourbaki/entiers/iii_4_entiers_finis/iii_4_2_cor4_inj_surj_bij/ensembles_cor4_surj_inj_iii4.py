"""§III.4 — COROLLAIRE 4, direction SURJECTION ⇒ INJECTION (volet honnête).

Cor. 4 §III.4 (E,F finis de MÊME cardinal ; f application de E dans F) :
inj ⟺ surj ⟺ bij.  Le volet « inj ⇒ surj » est clos (et inconditionnel) dans
`ensembles_cor4_inj_surj_iii4.cor4_inj_implique_surj`.

──────────────────────────────────────────────────────────────────────────────
Ce module traite le volet RÉCIPROQUE « surj ⇒ inj ».  La preuve de Bourbaki en
suit la route par SECTION (E.III.4, via Prop. 8 §II.3, qui repose sur l'AXIOME
DU CHOIX) :

    f : E ↠ F  surjective  ⇒  il existe une section s : F → E de f,
    s est une injection (Prop. 8) ;  comme Card F = Card E fini, le volet
    inj ⇒ surj DÉJÀ CLOS, appliqué à s : F ↪ E, donne s SURJECTIVE, donc
    s : F → E est BIJECTIVE ;  f est alors l'inverse de la bijection s, d'où
    f injective.

⚠️  ÉTAT HONNÊTE des briques déposées.  Deux maillons de cette route ne sont PAS
déposés sous forme INCONDITIONNELLE dans le dépôt actuel :
  (1) la CONSTRUCTION de la section s à partir de la seule surjectivité de f
      (Prop. 8 §II.3 — repose sur l'axiome du choix ; non construite ici, cf.
      `ensembles_prop3_prop4cor_iii3.prop3_surjection_inf_egal`, qui la PORTE en
      hypothèse honnête « s est une section ») ;
  (2) le PONT valeurs↔graphe « g = f⁻¹ » qui, de « s bijective », tirerait la
      relation pointwise s(f(x))=x ⇒ f injective (explicitement REPORTÉ dans
      `ensembles_retractions_props`, commentaire « COROLLAIRE g = f⁻¹ : REPORTÉ »).

Faute de (1) et (2), la cible pointwise `injective_dans(f, E)` n'est pas
honnêtement atteignable à partir de la SEULE surjectivité de f.  On dépose donc
le THÉORÈME HONNÊTE substantiel qui capture le CŒUR du raisonnement de Bourbaki
et RÉUTILISE le volet inj ⇒ surj déjà mergé :

  🎯  section_finie_implique_bijective :
        ⊢_{ s section de f sur F ; s : F→E application ; fini(E) ; Card F=Card E }
              est_bijective(s, F, E).

C.-à-d. : une section s d'une surjection f : E ↠ F, entre ensembles finis de
même cardinal, est elle-même une BIJECTION F ↔ E.  C'est exactement le pas où
Bourbaki conclut « s est bijective », d'où il déduit f = s⁻¹ injective.  Les
hypothèses portées (« s est une section, s : F→E application », fini, même
cardinal) sont HONNÊTES, fidèles à la preuve, jamais fausses ni vacuous, et la
construction de s elle-même (choix) reste, comme dans Bourbaki et dans la Prop 3
déposée, une donnée.

⚠ INVARIANT : theorie_ensembles() = 22.  Rien postulé ; énoncé non vacuous.
"""
from __future__ import annotations

from bourbaki.logique.formule import Terme, var, egal, et, impl
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E

from bourbaki.cardinaux.ensembles_cardinaux import est_injection_de, cardinal
from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import est_fini_ensemble

from bourbaki.logique.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
)

# briques CLOSES réutilisées
from bourbaki.ensembles.fonctions.ensembles_retractions import (
    retraction_implique_injective,
)
from bourbaki.entiers.iii_4_entiers_finis.iii_4_2_cor4_inj_surj_bij.ensembles_cor4_inj_surj_iii4 import cor4_inj_implique_surj


def _t(t):
    return t if isinstance(t, Terme) else var(t)


def section_finie_implique_bijective_enonce(s="Sc4", f="fc4", Eens="Ec4", Fens="Fc4"):
    """⊢-cible : ( est_section(s,f,F) et est_fonctionnel(s) et dom s=F
                   et image(s,F)⊂E et est_fini_ensemble(E) et Card F=Card E )
                   ⇒ est_bijective(s, F, E)."""
    vS, vf, vE, vF = _t(s), _t(f), _t(Eens), _t(Fens)
    # « s est une section de f sur F » = est_retraction(f,s,F) (f joue la rétraction de s).
    h_sec  = E.est_retraction(vf, vS, vF)
    h_func = E.est_fonctionnel(vS)
    h_dom  = egal(E.dom(vS), vF)
    h_img  = E.inclus(E.image(vS, vF), vE)
    h_fin  = est_fini_ensemble(vE)
    h_card = egal(cardinal(vF), cardinal(vE))
    ante = et(et(et(et(et(h_sec, h_func), h_dom), h_img), h_fin), h_card)
    return impl(ante, E.est_bijective(vS, vF, vE))


def section_finie_implique_bijective(s="Sc4", f="fc4", Eens="Ec4", Fens="Fc4"):
    """🎯 ⊢ ( s section de f sur F ; s:F→E application ; fini(E) ; Card F=Card E )
              ⇒ est_bijective(s, F, E).   (CLOS, 0 hyp.)

    Cor. 4 §III.4, cœur du volet surj ⇒ inj.  Voir docstring de module."""
    vS, vf, vE, vF = _t(s), _t(f), _t(Eens), _t(Fens)

    h_sec  = E.est_retraction(vf, vS, vF)          # s section de f sur F
    h_func = E.est_fonctionnel(vS)
    h_dom  = egal(E.dom(vS), vF)
    h_img  = E.inclus(E.image(vS, vF), vE)
    h_fin  = est_fini_ensemble(vE)
    h_card = egal(cardinal(vF), cardinal(vE))
    ante = et(et(et(et(et(h_sec, h_func), h_dom), h_img), h_fin), h_card)

    h = N.assume(ante)
    # décomposition (associativité gauche)
    a1 = conjonction_elim_gauche(h)                 # (((( sec,func),dom),img),fin)
    a_card = conjonction_elim_droite(h)             # Card F = Card E
    a2 = conjonction_elim_gauche(a1)                # ((( sec,func),dom),img)
    a_fin = conjonction_elim_droite(a1)             # fini(E)
    a3 = conjonction_elim_gauche(a2)                # (( sec,func),dom)
    a_img = conjonction_elim_droite(a2)             # image(s,F) ⊂ E
    a4 = conjonction_elim_gauche(a3)                # ( sec,func)
    a_dom = conjonction_elim_droite(a3)             # dom s = F
    a_sec = conjonction_elim_gauche(a4)             # est_retraction(f,s,F)
    a_func = conjonction_elim_droite(a4)            # est_fonctionnel(s)

    assert a_sec.conclusion == h_sec
    assert a_func.conclusion == h_func
    assert a_dom.conclusion == h_dom
    assert a_img.conclusion == h_img
    assert a_fin.conclusion == h_fin
    assert a_card.conclusion == h_card

    # ── s INJECTIVE sur F :  Prop. 8 (sens injectif), rétraction f de s ─────────
    prop8 = retraction_implique_injective(r=f, f=s, a=Fens)   # est_retraction(f,s,F) ⇒ inj(s,F)
    s_inj = N.modus_ponens(a_sec, prop8)                      # injective_dans(s, F)
    assert s_inj.conclusion == E.injective_dans(vS, vF)

    # ── est_injection_de(s, F, E) ──────────────────────────────────────────────
    inj_de = conjonction_intro(conjonction_intro(conjonction_intro(
        a_func, a_dom), s_inj), a_img)                        # est_injection_de(s,F,E)
    assert inj_de.conclusion == est_injection_de(vS, vF, vE)

    # ── inj ⇒ surj (volet DÉJÀ CLOS) appliqué à s : F ↪ E ──────────────────────
    # cor4_inj_implique_surj(s,F,E) :
    #   ( est_injection_de(s,F,E) et fini(E) et Card F=Card E ) ⇒ est_surjective(s,F,E)
    inj_surj = cor4_inj_implique_surj(f=s, Eens=Fens, Fens=Eens)
    surj_ante = conjonction_intro(conjonction_intro(inj_de, a_fin), a_card)
    s_surj = N.modus_ponens(surj_ante, inj_surj)              # est_surjective(s,F,E)
    assert s_surj.conclusion == E.est_surjective(vS, vF, vE)

    # ── est_bijective(s,F,E) = injective_dans(s,F) et est_surjective(s,F,E) ─────
    bij = conjonction_intro(s_inj, s_surj)
    assert bij.conclusion == E.est_bijective(vS, vF, vE)

    res = N.loi_deduction(ante, bij)
    assert res.conclusion == section_finie_implique_bijective_enonce(vS, vf, vE, vF), \
        "conclusion ≠ énoncé"
    assert res.est_clos and not res.hypotheses, "section_finie_implique_bijective : non close !"
    return res


__all__ = [
    "section_finie_implique_bijective",
    "section_finie_implique_bijective_enonce",
]
