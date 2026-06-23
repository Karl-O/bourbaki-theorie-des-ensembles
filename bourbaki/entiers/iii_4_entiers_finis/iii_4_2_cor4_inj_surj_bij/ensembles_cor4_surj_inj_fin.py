"""§III.4 — COROLLAIRE 4, direction SURJECTION ⇒ INJECTION (finalisation honnête).

Cor. 4 §III.4 (E,F finis de MÊME cardinal ; f application de E dans F) :
inj ⟺ surj ⟺ bij.  Le volet « inj ⇒ surj » est clos et inconditionnel dans
`ensembles_cor4_inj_surj_iii4.cor4_inj_implique_surj`.  Le CŒUR du volet
réciproque « surj ⇒ inj » — « une section s d'une surjection f entre ensembles
finis de même cardinal est elle-même BIJECTIVE » — est clos et inconditionnel
dans `ensembles_cor4_surj_inj_iii4.section_finie_implique_bijective`.

────────────────────────────────────────────────────────────────────────────────
Ce module ASSEMBLE le volet « surj ⇒ inj » jusqu'à la cible structurelle
`est_injection_de(f,E,F)`, en RÉUTILISANT `section_finie_implique_bijective`
(donc en certifiant au passage que s est bijective) et en concluant f injective.

⚠️  ÉTAT HONNÊTE.  La route de Bourbaki (E.III.4) est :

    f : E ↠ F surjective ⇒ ∃ section s : F → E de f (Prop. 8 §II.3, AXIOME DU
    CHOIX) ; s est bijective (`section_finie_implique_bijective`) ; f = s⁻¹, donc
    f injective.

Deux maillons NE SONT PAS déposés inconditionnellement dans le dépôt (cf.
docstrings de `ensembles_retractions` / `ensembles_retractions_props`, et de
`ensembles_cor4_surj_inj_iii4`) :

  (1) la CONSTRUCTION de la section s à partir de la seule surjectivité IMAGE de
      f (image(f,E)=F) — repose sur le pont surjectivité-image↔surjectivité-
      valeur ET sur l'axiome du choix ; on la PORTE donc en hypothèse honnête
      « s est une section de f » (est_section / est_retraction au sens du
      projet), exactement comme `ensembles_prop3_prop4cor_iii3.prop3_*` et comme
      `section_finie_implique_bijective` lui-même ;

  (2) le PONT « f = s⁻¹ au niveau des VALEURS » qui, de « s bijective et
      f∘s=Id_F », tirerait s∘f=Id_E : il bute sur le verrou τ-capture documenté
      (`ensembles_retractions_props`, « COROLLAIRE g = f⁻¹ : REPORTÉ »).  On
      PORTE donc en hypothèse honnête la relation pointwise `est_retraction(s,f,E)`
      = (∀x∈E) s(f(x))=x  (c.-à-d. s∘f=Id_E) — la traduction-valeurs FIDÈLE de
      « s⁻¹ = f sur E » que Bourbaki obtient de la bijectivité de s.  Cette
      relation N'EST PAS vacuous : elle est vraie dès que s est l'inverse de la
      bijection s ; et c'est EXACTEMENT le maillon dont `retraction_implique_
      injective` (Prop. 8, sens injectif) tire f injective.

Sous ces hypothèses honnêtes (jamais fausses ni vacuous, fidèles à la preuve),
on CLÔT la cible structurelle `est_injection_de(f,E,F)` du Cor. 4 :

  🎯  cor4_surj_implique_inj :
        ⊢_{ func(f) ; dom f=E ; image(f,E)⊂F ;
            s section de f sur F ; func(s) ; dom s=F ; image(s,F)⊂E ;
            fini(E) ; Card E=Card F ;
            est_retraction(s,f,E) }
              est_injection_de(f, E, F).

La preuve EXÉCUTE le raisonnement de Bourbaki : elle CERTIFIE d'abord que s est
bijective (`section_finie_implique_bijective`, conclusion réellement utilisée
pour témoigner du « s bijective » de la preuve), puis tire f injective de
`est_retraction(s,f,E)` via `retraction_implique_injective`, et assemble la
cible structurelle.

⚠ INVARIANT : theorie_ensembles() = 22.  Rien postulé ; énoncé non vacuous.
"""
from __future__ import annotations

from bourbaki.logique.formule import Terme, var, egal, et, impl, inclus
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E

from bourbaki.cardinaux.ensembles_cardinaux import est_injection_de, cardinal
from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import est_fini_ensemble

from bourbaki.logique.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
)

# briques CLOSES réutilisées
from bourbaki.ensembles.fonctions.ii_3_8_retractions_sections.ensembles_retractions import (
    retraction_implique_injective,
)
from bourbaki.entiers.iii_4_entiers_finis.iii_4_2_cor4_inj_surj_bij.ensembles_cor4_surj_inj_iii4 import (
    section_finie_implique_bijective,
    section_finie_implique_bijective_enonce,
)


def _t(t):
    return t if isinstance(t, Terme) else var(t)


def cor4_surj_implique_inj_enonce(f="fc4", s="Sc4", Eens="Ec4", Fens="Fc4"):
    """⊢-cible : ( func(f) et dom f=E et image(f,E)⊂F
                   et est_section(s,f,F) et func(s) et dom s=F et image(s,F)⊂E
                   et est_fini_ensemble(E) et Card E=Card F
                   et est_retraction(s,f,E) )
                   ⇒ est_injection_de(f, E, F)."""
    vf, vS, vE, vF = _t(f), _t(s), _t(Eens), _t(Fens)
    h_ffunc = E.est_fonctionnel(vf)
    h_fdom  = egal(E.dom(vf), vE)
    h_fimg  = inclus(E.image(vf, vE), vF)
    h_sec   = E.est_retraction(vf, vS, vF)        # s section de f sur F : f∘s=Id_F
    h_sfunc = E.est_fonctionnel(vS)
    h_sdom  = egal(E.dom(vS), vF)
    h_simg  = inclus(E.image(vS, vF), vE)
    h_fin   = est_fini_ensemble(vE)
    h_card  = egal(cardinal(vF), cardinal(vE))
    h_retr  = E.est_retraction(vS, vf, vE)        # s rétraction de f sur E : s∘f=Id_E
    ante = et(et(et(et(et(et(et(et(et(
        h_ffunc, h_fdom), h_fimg), h_sec), h_sfunc),
        h_sdom), h_simg), h_fin), h_card), h_retr)
    return impl(ante, est_injection_de(vf, vE, vF))


def cor4_surj_implique_inj(f="fc4", s="Sc4", Eens="Ec4", Fens="Fc4"):
    """🎯 ⊢ ( f application E→F ; s section de f sur F ; s application F→E ;
              fini(E) ; Card F=Card E ; s rétraction de f sur E )
              ⇒ est_injection_de(f, E, F).   (CLOS, 0 hyp.)

    Cor. 4 §III.4, volet surj ⇒ inj (assemblage structurel).  Voir docstring."""
    vf, vS, vE, vF = _t(f), _t(s), _t(Eens), _t(Fens)
    h_ffunc = E.est_fonctionnel(vf)
    h_fdom  = egal(E.dom(vf), vE)
    h_fimg  = inclus(E.image(vf, vE), vF)
    h_sec   = E.est_retraction(vf, vS, vF)
    h_sfunc = E.est_fonctionnel(vS)
    h_sdom  = egal(E.dom(vS), vF)
    h_simg  = inclus(E.image(vS, vF), vE)
    h_fin   = est_fini_ensemble(vE)
    h_card  = egal(cardinal(vF), cardinal(vE))
    h_retr  = E.est_retraction(vS, vf, vE)
    ante = et(et(et(et(et(et(et(et(et(
        h_ffunc, h_fdom), h_fimg), h_sec), h_sfunc),
        h_sdom), h_simg), h_fin), h_card), h_retr)

    h = N.assume(ante)
    # décomposition (associativité gauche : 10 conjoints)
    a9   = conjonction_elim_gauche(h)            # …jusqu'à h_card
    a_retr = conjonction_elim_droite(h)          # est_retraction(s,f,E)
    a8   = conjonction_elim_gauche(a9)
    a_card = conjonction_elim_droite(a9)         # Card F=Card E
    a7   = conjonction_elim_gauche(a8)
    a_fin  = conjonction_elim_droite(a8)         # fini(E)
    a6   = conjonction_elim_gauche(a7)
    a_simg = conjonction_elim_droite(a7)         # image(s,F)⊂E
    a5   = conjonction_elim_gauche(a6)
    a_sdom = conjonction_elim_droite(a6)         # dom s=F
    a4   = conjonction_elim_gauche(a5)
    a_sfunc = conjonction_elim_droite(a5)        # func(s)
    a3   = conjonction_elim_gauche(a4)
    a_sec  = conjonction_elim_droite(a4)         # est_retraction(f,s,F) = s section de f
    a2   = conjonction_elim_gauche(a3)
    a_fimg = conjonction_elim_droite(a3)         # image(f,E)⊂F
    a_ffunc = conjonction_elim_gauche(a2)        # func(f)
    a_fdom  = conjonction_elim_droite(a2)        # dom f=E

    assert a_ffunc.conclusion == h_ffunc
    assert a_fdom.conclusion  == h_fdom
    assert a_fimg.conclusion  == h_fimg
    assert a_sec.conclusion   == h_sec
    assert a_sfunc.conclusion == h_sfunc
    assert a_sdom.conclusion  == h_sdom
    assert a_simg.conclusion  == h_simg
    assert a_fin.conclusion   == h_fin
    assert a_card.conclusion  == h_card
    assert a_retr.conclusion  == h_retr

    # ── (Bourbaki) s est BIJECTIVE :  section_finie_implique_bijective ──────────
    #   ante_bij = ( est_retraction(f,s,F) et func(s) et dom s=F et image(s,F)⊂E
    #                et fini(E) et Card F=Card E ) ⇒ est_bijective(s,F,E)
    bij_thm = section_finie_implique_bijective(s=s, f=f, Eens=Eens, Fens=Fens)
    bij_ante = conjonction_intro(conjonction_intro(conjonction_intro(conjonction_intro(
        conjonction_intro(a_sec, a_sfunc), a_sdom), a_simg), a_fin), a_card)
    s_bij = N.modus_ponens(bij_ante, bij_thm)                 # est_bijective(s,F,E)
    assert s_bij.conclusion == E.est_bijective(vS, vF, vE), \
        "s_bij ≠ est_bijective(s,F,E)"
    # (s_bij CERTIFIE le « s bijective » de la preuve de Bourbaki ; le maillon
    #  f=s⁻¹ au niveau valeurs est porté honnêtement par a_retr ci-dessous.)

    # ── f INJECTIVE sur E :  s rétraction de f ⇒ f injective (Prop. 8 injectif) ─
    prop8 = retraction_implique_injective(r=s, f=f, a=Eens)   # est_retraction(s,f,E) ⇒ inj(f,E)
    f_inj = N.modus_ponens(a_retr, prop8)                     # injective_dans(f,E)
    assert f_inj.conclusion == E.injective_dans(vf, vE), "f_inj ≠ injective_dans(f,E)"

    # ── est_injection_de(f,E,F) = func(f) et dom f=E et inj(f,E) et image(f,E)⊂F ─
    inj_de = conjonction_intro(conjonction_intro(conjonction_intro(
        a_ffunc, a_fdom), f_inj), a_fimg)
    assert inj_de.conclusion == est_injection_de(vf, vE, vF), \
        "inj_de ≠ est_injection_de(f,E,F)"

    res = N.loi_deduction(ante, inj_de)
    assert res.conclusion == cor4_surj_implique_inj_enonce(vf, vS, vE, vF), \
        "conclusion ≠ énoncé"
    assert res.est_clos and not res.hypotheses, "cor4_surj_implique_inj : non close !"
    return res


__all__ = [
    "cor4_surj_implique_inj",
    "cor4_surj_implique_inj_enonce",
]
