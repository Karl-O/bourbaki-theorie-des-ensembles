"""§III.4 — COROLLAIRE 4, direction INJECTION ⇒ SURJECTION.

🎯  cor4_inj_implique_surj :
        ⊢ ( est_injection_de(f,E,F)  et  est_fini_ensemble(F)  et  Card E = Card F )
              ⇒  est_surjective(f, E, F).

Cor. 4 §III.4 (E,F finis de même cardinal ; f application de E dans F) :
inj ⟺ surj ⟺ bij.  Ici le sens « inj ⇒ surj », fidèle à la preuve de Bourbaki :

    f injective  ⇒  Card(f⟨E⟩) = Card E = Card F   (Prop. 1 + hyp) ;
    f⟨E⟩ ⊂ F  et  F fini  ⇒  f⟨E⟩ = F   (cor. 2 = partie_egal_cardinal_egal) ;
    f⟨E⟩ = F  =  f surjective.

L'antécédent « f application injective de E dans F » est codé par le prédicat
GRAPHE `est_injection_de(f,E,F)` = (fonctionnel ∧ dom f=E ∧ injective_dans(f,E)
∧ f⟨E⟩⊂F), fidèle à E.III.3.2.  La conclusion `est_surjective(f,E,F)` = f⟨E⟩=F
(E.II.49, Déf. 10) est exactement la définition déposée de la surjectivité.

ROUTE (briques CLOSES uniquement) :
  • injection_donne_equipotent_image(f,E,F) : injection ⇒ Eq(E, f⟨E⟩) ;
  • cardinal_egal_si_equipotent (version TERME) : Eq(E,f⟨E⟩) ⇒ Card E=Card(f⟨E⟩) ;
  • composer avec Card E=Card F ⇒ Card(f⟨E⟩)=Card F ;
  • partie_egal_cardinal_egal(f⟨E⟩, F) : (f⟨E⟩⊂F et fini F et Card(f⟨E⟩)=Card F)
    ⇒ f⟨E⟩=F.

⚠ INVARIANT : theorie_ensembles() = 22.  Rien postulé ; non vacueux.
"""
from __future__ import annotations

from bourbaki.logique.formule import Terme, var, egal, et, impl
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E

from bourbaki.cardinaux.ensembles_cardinaux import (
    est_injection_de, cardinal,
)
from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import est_fini_ensemble

from bourbaki.logique.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
)
from bourbaki.logique.tactiques.tactiques_abrege_egalite import (
    symetrie, composer_egalites,
)

# ── briques CLOSES réutilisées ────────────────────────────────────────────────
from bourbaki.cardinaux.ensembles_realisation_segment_close import (
    injection_donne_equipotent_image,
)
from bourbaki.cardinaux.ensembles_cardinaux_theoremes import (
    cardinal_egal_si_equipotent,
)
from bourbaki.entiers.iii_4_entiers_finis.iii_4_2_pigeonhole_surgery.ensembles_pigeonhole_sous_lemme import partie_egal_cardinal_egal


def _t(t):
    return t if isinstance(t, Terme) else var(t)


def _cardinal_egal_si_equipotent_t(tX, tY):
    """⊢ Eq(X, Y) ⇒ (Card X = Card Y)  pour des TERMES X, Y (Prop 1, sens direct).

    Version TERME (généralise-puis-instancie) de cardinal_egal_si_equipotent,
    capture-safe pour des termes quelconques (ici f⟨E⟩)."""
    gen = N.generalisation("X", N.generalisation("Y",
        cardinal_egal_si_equipotent("X", "Y")))
    from bourbaki.logique.tactiques.tactiques_abrege2 import instancie
    return instancie(instancie(gen, _t(tX)), _t(tY))


def cor4_inj_implique_surj_enonce(f="f4", Eens="E4", Fens="F4"):
    """⊢-cible : ( est_injection_de(f,E,F) et est_fini_ensemble(F) et Card E=Card F )
                   ⇒ est_surjective(f, E, F)."""
    vf, vE, vF = _t(f), _t(Eens), _t(Fens)
    ante = et(et(est_injection_de(vf, vE, vF), est_fini_ensemble(vF)),
              egal(cardinal(vE), cardinal(vF)))
    return impl(ante, E.est_surjective(vf, vE, vF))


def cor4_inj_implique_surj(f="f4", Eens="E4", Fens="F4"):
    """🎯🎯 ⊢ ( est_injection_de(f,E,F) et est_fini_ensemble(F) et Card E=Card F )
                ⇒ est_surjective(f, E, F).   (CLOS, 0 hyp.)

    Cor. 4 §III.4, direction inj ⇒ surj.  Voir docstring de module."""
    vf, vE, vF = _t(f), _t(Eens), _t(Fens)
    inj = est_injection_de(vf, vE, vF)
    img = E.image(vf, vE)                                  # f⟨E⟩
    cE, cF, cImg = cardinal(vE), cardinal(vF), cardinal(img)

    ante = et(et(inj, est_fini_ensemble(vF)), egal(cE, cF))
    h = N.assume(ante)
    h_inj   = conjonction_elim_gauche(conjonction_elim_gauche(h))   # est_injection_de(f,E,F)
    h_Ffini = conjonction_elim_droite(conjonction_elim_gauche(h))   # est_fini_ensemble(F)
    h_card  = conjonction_elim_droite(h)                            # Card E = Card F

    # ── f⟨E⟩ ⊂ F  (4e conjoint de est_injection_de) ─────────────────────────
    h_img_incl = conjonction_elim_droite(h_inj)                     # f⟨E⟩ ⊂ F
    from bourbaki.logique.formule import inclus
    assert h_img_incl.conclusion == inclus(img, vF), "img_incl ≠ (f⟨E⟩⊂F)"

    # ── Eq(E, f⟨E⟩) ─────────────────────────────────────────────────────────
    eq_E_img = N.modus_ponens(h_inj, injection_donne_equipotent_image(vf, vE, vF))
    from bourbaki.cardinaux.ensembles_cardinaux import equipotent
    assert eq_E_img.conclusion == equipotent(vE, img), "eq_E_img ≠ Eq(E,f⟨E⟩)"

    # ── Card E = Card(f⟨E⟩)  (Prop 1, sens direct, version terme) ────────────
    cardE_eq_img = N.modus_ponens(eq_E_img, _cardinal_egal_si_equipotent_t(vE, img))
    assert cardE_eq_img.conclusion == egal(cE, cImg)

    # ── Card(f⟨E⟩) = Card F :  Card(f⟨E⟩)=Card E=Card F ──────────────────────
    img_eq_cardE = N.modus_ponens(cardE_eq_img, symetrie(cE, cImg))   # Card(f⟨E⟩)=Card E
    img_eq_cardF = composer_egalites(img_eq_cardE, h_card)            # Card(f⟨E⟩)=Card F
    assert img_eq_cardF.conclusion == egal(cImg, cF)

    # ── f⟨E⟩ = F  (pigeonhole sous-lemme : partie de même cardinal d'un fini) ─
    pigeon = partie_egal_cardinal_egal(img, vF)   # (f⟨E⟩⊂F et fini F et Card(f⟨E⟩)=Card F)⇒f⟨E⟩=F
    pigeon_ante = conjonction_intro(conjonction_intro(h_img_incl, h_Ffini), img_eq_cardF)
    img_eq_F = N.modus_ponens(pigeon_ante, pigeon)                   # f⟨E⟩ = F
    assert img_eq_F.conclusion == egal(img, vF)

    # f⟨E⟩ = F  EST  est_surjective(f,E,F)
    assert img_eq_F.conclusion == E.est_surjective(vf, vE, vF), \
        "img=F ≠ est_surjective(f,E,F)"

    res = N.loi_deduction(ante, img_eq_F)
    assert res.conclusion == cor4_inj_implique_surj_enonce(vf, vE, vF), "conclusion ≠ énoncé"
    assert res.est_clos and not res.hypotheses, "cor4_inj_implique_surj : non close !"
    return res


__all__ = ["cor4_inj_implique_surj", "cor4_inj_implique_surj_enonce"]
