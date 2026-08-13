"""§II.6.9 — la classe d'objets θ_{R_f} CARACTÉRISE la relation : θ(x)=θ(y) ⇔ f(x)=f(y).

────────────────────────────────────────────────────────────────────────────────
`ensembles_decomposition_effective` établit le sens FACILE (passage au
quotient, CLOS) :   R_f{x,y}  ⇒  θ(x) = θ(y).
Le sens RÉCIPROQUE manquait ; il est démontré ici, et avec lui la
caractérisation complète du quotient par la classe d'objets :

  • `theta_temoin`    {x∈E} ⊢ R_f{ x, θ(x) }
    — x appartient à sa propre classe : R_f{x,x} est vraie (réflexivité de =),
      donc (∃w)R_f{x,w}, donc le TÉMOIN CANONIQUE τ_w la satisfait
      (existe_temoin) ; au passage θ(x)∈E.
  • `theta_injectif`  {x∈E, y∈E, θ(x)=θ(y)} ⊢ f(x) = f(y)
    — f(x)=f(θ(x))=f(θ(y))=f(y) par le témoin et la congruence.

Ces deux briques ferment la caractérisation « p(x)=p(y) ⇔ R_f{x,y} » exigée
par C57 (ensembles_c57_passage_quotient) lorsque la canonique est la classe
d'objets — c'est-à-dire pour la DÉCOMPOSITION CANONIQUE f = i∘b∘p.
INVARIANT : theorie_ensembles()=22 ; rien postulé.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, et, appartient, existe,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_droite,
)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
    symetrie, composer_egalites, congruence_terme,
)
from bourbaki.ii_theorie_des_ensembles.ii_6_relations_equivalence.ii_6_5_decomposition.ensembles_decomposition_effective import (
    classe_objets_Rf, _Rf_corps, _valf,
)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# @livre Ch.II §6.9 Prop.- | E II.47 L.16-39 | PDF p.98  (x appartient à sa classe : le témoin canonique τ_w de R_f{x,·} la satisfait)
def theta_temoin(f="f", e=None, x="x", w="w"):
    """{ x ∈ E } ⊢ R_f{ x, θ_{R_f}(x) }.

    Donne en particulier θ(x)∈E ET f(x)=f(θ(x)) (conjoints), les deux faits
    dont dépend la réciproque du passage au quotient."""
    vf, vx = _t(f), _t(x)
    ve = E.dom(vf) if e is None else _t(e)
    hx = N.assume(appartient(vx, ve))
    refl = conjonction_intro(conjonction_intro(hx, hx),
                             N.reflexivite(_valf(vf, vx)))     # R_f{x,x}
    corps = _Rf_corps(vf, vx, var(w), ve)
    ex = N.modus_ponens(refl, N.s5(corps, vx, w))              # (∃w) R_f{x,w}
    res = N.modus_ponens(ex, N.existe_temoin(corps, w))        # R_f{x, θ(x)}
    assert res.conclusion == _Rf_corps(
        vf, vx, classe_objets_Rf(vf, vx, e=ve, w=w), ve), "theta_temoin : ≠ cible"
    assert set(res.hypotheses) == {hx.conclusion}, "theta_temoin : hyps ≠ 1"
    return res


# @livre Ch.II §6.5 Prop.- | E II.44 L.25-28 | PDF p.95  (réciproque du passage au quotient : deux points de même classe ont même image — ferme la caractérisation)
def theta_injectif(f="f", e=None, x="x", y="y", w="w"):
    """{ x∈E, y∈E, θ(x)=θ(y) } ⊢ f(x) = f(y).

    RÉCIPROQUE de `passage_quotient_Rf` : la classe d'objets détermine la
    valeur.  f(x) = f(θ(x)) [théorème du témoin] = f(θ(y)) [congruence sur
    θ(x)=θ(y)] = f(y) [témoin en y]."""
    vf, vx, vy = _t(f), _t(x), _t(y)
    ve = E.dom(vf) if e is None else _t(e)
    tx = classe_objets_Rf(vf, vx, e=ve, w=w)
    ty = classe_objets_Rf(vf, vy, e=ve, w=w)
    fx_ftx = conjonction_elim_droite(theta_temoin(vf, ve, vx, w))   # f(x)=f(θ(x))
    fy_fty = conjonction_elim_droite(theta_temoin(vf, ve, vy, w))   # f(y)=f(θ(y))
    heq = N.assume(egal(tx, ty))
    cong = N.modus_ponens(heq, congruence_terme(
        tx, ty, _valf(vf, var("w6h")), w="w6h"))                    # f(θx)=f(θy)
    res = composer_egalites(composer_egalites(fx_ftx, cong), N.modus_ponens(
        fy_fty, symetrie(_valf(vf, vy), _valf(vf, ty))))
    assert res.conclusion == egal(_valf(vf, vx), _valf(vf, vy)), \
        "theta_injectif : ≠ (f(x)=f(y))"
    assert len(res.hypotheses) == 3, "theta_injectif : hyps ≠ 3"
    return res


__all__ = ["theta_temoin", "theta_injectif"]
