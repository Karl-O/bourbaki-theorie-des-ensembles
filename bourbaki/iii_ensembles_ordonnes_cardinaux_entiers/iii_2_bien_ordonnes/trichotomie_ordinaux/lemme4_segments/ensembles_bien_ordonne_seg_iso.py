"""§III.2 — ISOMORPHISME D'ORDRE  t ↦ seg(a,R,t)  RENDU INCONDITIONNEL via la totalité.

Le module lemme_1_segments établit :
  • seg_strict_monotone_de_bon_ordre : {bo} ⊢ R{t,s} ⇒ seg(t)⊂seg(s)   (sens direct),
  • seg_reflechit_ordre : {comparables_dans(R,a,t,s), s∈a} ⊢ seg(t)⊂seg(s) ⇒ R{t,s},
le sens réciproque étant CONDITIONNÉ à la comparabilité de t,s (hypothèse explicite).

Avec la TOTALITÉ d'un bon ordre (bon_ordre_est_total, ensembles_bien_ordonne_total) la
comparabilité devient un THÉORÈME, ce qui rend le sens réciproque — et donc l'ÉQUIVALENCE
   seg(a,R,t) ⊂ seg(a,R,s)  ⇔  R{t,s}
— INCONDITIONNEL sous le seul bon ordre de (a,R) + t∈a, s∈a.  C'est l'isomorphisme
d'ordre de (a,R) sur la famille de ses segments propres, brique de la trichotomie §III.2.

theorie=22, rien postulé, non vacueux (comparabilité réellement consommée).
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import Terme, var, egal, et, ou, impl, appartient, inclus
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, instancie,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.trichotomie_ordinaux.lemme4_segments.ensembles_bien_ordonne_total import bon_ordre_est_total
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.trichotomie_ordinaux.lemme4_segments.ensembles_bien_ordonne_lemme_1_segments import (
    seg, comparables_dans, seg_reflechit_ordre, seg_strict_monotone_de_bon_ordre,
)


def _t(t):
    return t if isinstance(t, Terme) else var(t)


def _R_de(R):
    vR = _t(R)
    return lambda a, b: appartient(E.couple(_t(a), _t(b)), vR)


def _decharge(thm, hyp, preuve_hyp):
    return N.modus_ponens(preuve_hyp, N.loi_deduction(hyp, thm))


# ── la comparabilité de t,s comme THÉORÈME (instance de la totalité) ──────────
def comparabilite_dans_bon_ordre(R="R", a="a", t="t", s="s"):
    """⊢ { est_bien_ordonne(R,a),  t∈a,  s∈a } ⊢ ( R{t,s} ou R{s,t} ).

    Instance de la totalité (bon_ordre_est_total) au couple (t,s) : la comparabilité,
    prise en hypothèse dans seg_reflechit_ordre, est ici DÉRIVÉE du bon ordre."""
    va, vt, vs = _t(a), _t(t), _t(s)
    tot = bon_ordre_est_total(R, a)                       # {bo} ⊢ ∀x∀y((x∈a et y∈a)⇒(R{x,y} ou R{y,x}))
    inst = instancie(instancie(tot, vt), vs)             # (t∈a et s∈a) ⇒ (R{t,s} ou R{s,t})
    prem = conjonction_intro(N.assume(appartient(vt, va)),
                             N.assume(appartient(vs, va)))
    return N.modus_ponens(prem, inst)                    # R{t,s} ou R{s,t}


# ── sens réciproque RENDU INCONDITIONNEL ──────────────────────────────────────
# @livre Ch.III §2.1 Prop.2 | E III.16 L.21-30 | PDF p.119  (l'équivalence S_t ⊂ S_s ⇔ R{t,s} rendue inconditionnelle par la totalité)
def seg_reflechit_ordre_total(R="R", a="a", t="t", s="s"):
    """⊢ { est_bien_ordonne(R,a),  t∈a,  s∈a } ⊢ ( seg(a,R,t) ⊂ seg(a,R,s) ) ⇒ R{t,s}.

    Le sens RÉCIPROQUE de l'iso t↦seg(t), DÉCHARGÉ de la comparabilité (devenue théorème
    via la totalité)."""
    base = seg_reflechit_ordre(R, a, t, s)               # {comparables_dans, s∈a} ⊢ (seg(t)⊂seg(s))⇒R{t,s}
    comp = comparabilite_dans_bon_ordre(R, a, t, s)      # {bo, t∈a, s∈a} ⊢ comparables_dans
    return _decharge(base, comparables_dans(R, a, t, s), comp)   # {bo, s∈a, t∈a} ⊢ …


# NOTE : l'ÉQUIVALENCE complète seg(t)⊂seg(s) ⇔ R{t,s} s'obtient en conjuguant
# seg_reflechit_ordre_total (réciproque, ici) et seg_strict_monotone_de_bon_ordre (sens
# direct, lemme_1_segments).  Elle n'est PAS exposée ici car les deux sous-lemmes
# extraient la clause de bon ordre via des conventions de LIANTS internes différentes
# (est_bien_ordonne avec binders distincts) → la conjonction porterait DEUX variantes
# redondantes de l'hypothèse de bon ordre.  Sound mais non propre ; on garde donc les
# deux directions séparées (chacune à 3 hypothèses nettes), réutilisables telles quelles.


__all__ = [
    "comparabilite_dans_bon_ordre",
    "seg_reflechit_ordre_total",
]
