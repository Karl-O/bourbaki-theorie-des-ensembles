"""§III.4 — FERMETURE du GATE ℕ : `bon_ordre_intervalle(a)` / `cardinaux_bien_ordonnes(a)`
RÉDUITS au SEUL maillon HONNÊTE, PUREMENT ORDRE-THÉORIQUE,

    subset_realise_segment(Ro,a) :=
        (∀B)( B ⊂ a  ⇒  (∃t)( t∈a  et  Eq( B , seg(a,Ro,t) ) ) )

« tout sous-ensemble B de l'ensemble bien ordonné (a,Ro) est ÉQUIPOTENT à un segment
initial seg(a,Ro,t) de (a,Ro) » — l'EFFONDREMENT DE MOSTOWSKI / représentation
ordinale §III.2 dépouillé de toute comptabilité cardinale.

────────────────────────────────────────────────────────────────────────────────
CE QUE CE MODULE LIVRE (résumé exécutif, vérifié — voir cibles & test).

  🎯🎯 `bon_ordre_intervalle_depuis_subset(a)` :
        ⊢ { subset_realise_segment(Ro,a) }  ⊢  bon_ordre_intervalle(a)
                                               (== est_bien_ordonne(≤_induit,[0,a]), LITTÉRAL).

  🎯🎯 `cardinaux_bien_ordonnes_depuis_subset(a)` :
        ⊢ { subset_realise_segment(Ro,a) }  ⊢  cardinaux_bien_ordonnes(a)  (LITTÉRAL).

  ✅ `iso_implique_equipotent(...)`  (CLOSED, 0 hyp) :
        ⊢ ( est_isomorphisme_ordre(f,X,Y,R,R')  et  est_fonctionnel(f)  et  dom f=X )
             ⇒  Eq(X,Y).
     C'est la « RÉCUPÉRATION func/dom ⇒ équipotence » : un iso d'ordre AUGMENTÉ de la
     structure d'application (fonctionnel + domaine) DONNE l'équipotence.  Débloque le
     passage `sont_isomorphes_ordre` (témoin nu : est_bijective+compatible, SANS
     fonctionnel/dom) → `equipotent` (qui exige est_bijection_de = fonctionnel∧dom∧bij).

  ✅ `injection_donne_equipotent_image(F,c,a)`  (CLOSED, 0 hyp) :
        ⊢ est_injection_de(F,c,a)  ⇒  Eq( c , image(F,c) ).
     L'injection F:c→a est une BIJECTION sur SON image (domaine PLEIN c, donc AUCUNE
     restriction — le conjoint surjectif image(F,c)=image(F,c) est la RÉFLEXIVITÉ).

────────────────────────────────────────────────────────────────────────────────
POURQUOI `subset_realise_segment` ET PAS `realisation_segment` (la SUBTILITÉ CARDINALE).

`bon_ordre_intervalle_depuis_realisation` (ensembles_realisation_segment_preuve) prouve
`bon_ordre_intervalle(a)` sous l'UNIQUE hypothèse résiduelle

    realisation_hypothese(Ro,a) = (∀c) realisation_segment(Ro,a,c)  où
    realisation_segment(Ro,a,c) = ( c ≤ a ) ⇒ (∃t)( t∈a et Card(seg(a,Ro,t)) = c ).

⚠️ CETTE FORME LITTÉRALE EST MATHÉMATIQUEMENT FAUSSE pour c NON cardinal : son
antécédent `c ≤ a` (= (∃F) F injecte c dans a) N'IMPOSE PAS que c soit un cardinal,
alors que sa conclusion EXIGE `Card(seg…) = c` — or `Card(seg…)` est TOUJOURS un
cardinal.  Donc `(∀c) realisation_segment` est FAUX (instances c≤a, c non cardinal),
DONC NON dérivable d'aucune hypothèse vraie.  (Le défaut est dans l'énoncé littéral,
pas dans l'usage : voir ci-dessous.)

LA CORRECTION HONNÊTE — la GARDE `est_cardinal`.  Dans TOUS les sites consommateurs
(`pullback_onto`, `pullback_non_vide`), realisation n'est instancié qu'en `c∈S⊂[0,a]`,
et `c∈[0,a] = intervalle_entiers(0,a)` ENTRAÎNE `est_cardinal(c)` (premier conjoint du
corps de l'intervalle ; `intervalle_implique_cardinal`, CLOS).  On prouve donc la
VERSION GARDÉE, VRAIE :

    realisation_segment_garde(Ro,a) :=
        (∀c)( est_cardinal(c)  ⇒  realisation_segment(Ro,a,c) ).

`pullback_onto`/`pullback_non_vide` SE RECONSTRUISENT à l'identique (MÊME conclusion
`hyp_realisation_onto`/`PB≠∅`) en DÉCHARGEANT la garde par `est_cardinal(c)` tiré de
`c∈[0,a]` — sites où `c∈[0,a]` est DÉJÀ établi.  La chaîne `corps_garde → clause →
gate` reproduit alors `bon_ordre_intervalle_depuis_realisation` mot pour mot, avec la
SEULE hypothèse honnête `realisation_segment_garde` au lieu de la fausse `(∀c)real`.

LE DERNIER MAILLON — `subset_realise_segment ⊢ realisation_segment_garde`.  Pour
c CARDINAL avec c≤a : F:c→a (témoin de c≤a), B:=image(F)⊂a, Eq(c,B)
(injection_donne_equipotent_image) ; `subset_realise_segment` donne t∈a, Eq(B,seg) ;
donc Card(c)=Card(B)=Card(seg) (Prop 1), et Card(c)=c (`est_cardinal(c)`,
_cardinal_est_son_cardinal) ⇒ Card(seg)=c.  D'où realisation_segment(Ro,a,c), gardé
par est_cardinal(c), généralisé sur c.

────────────────────────────────────────────────────────────────────────────────
LE SEUL MAILLON RESTANT (honnête, ISOLÉ, JAMAIS postulé) :

    subset_realise_segment(Ro,a)  —  « tout B⊂a est équipotent à un segment initial
    seg(a,Ro,t) de (a,Ro) ».

C'est le THÉORÈME DE REPRÉSENTATION ORDINALE (§III.2, Théorème 3 / effondrement de
Mostowski), PUR : aucune comptabilité cardinale, juste l'ordre.  Dans le dépôt il
correspond à la TRICHOTOMIE de deux bons ordres `trichotomie_ordinaux_canon_prouve`
(ensembles_trichotomie_assemble), qui n'est PAS close — il subsiste le RÉSIDU
STRUCTUREL irréductible R1–R4 (residu_univ_app, val_dans_F, h_graphe_hyp,
est_segment(pr₂h)).  Le présent module RÉDUIT le GATE ℕ EXACTEMENT à ce maillon
order-théorique, sans plus aucune comptabilité cardinale parasite ni énoncé faux.

INVARIANT (vérifié) : theorie_ensembles() = 22.  RIEN POSTULÉ : tout DÉRIVE des
théorèmes CLOS du dépôt (bijection_implique_equipotent, cardinal_egal_si_equipotent,
_cardinal_est_son_cardinal, intervalle_implique_cardinal, la machinerie pullback/
clause/Zermelo de ensembles_realisation_segment_preuve & ensembles_hyp_transport_
ordinal_preuve) plus l'UNIQUE hypothèse `subset_realise_segment`, isolée, jamais
postulée.  NE MODIFIE AUCUN fichier existant.
"""
from __future__ import annotations

from bourbaki.logique.formule import (
    Terme, var, egal, et, non, impl, appartient, existe, pourtout, inclus, tau,
)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.logique.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite, instancie,
    equivalence_avant, equivalence_arriere,
)
from bourbaki.logique.tactiques.tactiques_abrege_quantif import (
    existe_elimination, alpha_existe,
)
from bourbaki.logique.tactiques.tactiques_abrege_egalite import (
    composer_egalites, symetrie as _sym_eq,
)

from bourbaki.ordre import ensembles_ordre_vocab as V
from bourbaki.cardinaux.ensembles_cardinaux import (
    est_bijection_de, equipotent, est_injection_de, inf_egal_card, cardinal, est_cardinal,
)
from bourbaki.cardinaux.ensembles_segments_construction import seg
from bourbaki.entiers.ensembles_cardinal_pas_entre import bijection_implique_equipotent
from bourbaki.cardinaux.ensembles_cardinaux_theoremes import cardinal_egal_si_equipotent
from bourbaki.cardinaux.ensembles_cardinaux_props_restantes_ordre import (
    _cardinal_est_son_cardinal,
)
from bourbaki.entiers.ensembles_entiers_theoremes import intervalle_implique_cardinal
from bourbaki.cardinaux.ensembles_ordinal_cardinal_correspondance import (
    ZERO, intervalle_0a, bon_ordre_intervalle, cardinaux_bien_ordonnes_de_bon_ordre,
)
from bourbaki.cardinaux.ensembles_ordinal_cardinal_ordre import (
    relation_ordre_dans_intervalle,
)
from bourbaki.entiers.ensembles_recurrence_C61 import cardinaux_bien_ordonnes

import bourbaki.cardinaux.ensembles_hyp_transport_ordinal_preuve as HTP
import bourbaki.cardinaux.ensembles_bon_ordre_intervalle_ordinal as BOIO
import bourbaki.cardinaux.ensembles_realisation_segment_preuve as RSP


def _t(t):
    return t if isinstance(t, Terme) else var(t)


# ── binders canoniques (alignés sur ensembles_realisation_segment_preuve) ──────
#   c='x', t='xw' : binders de realisation_segment consommés par le GATE.
#   _TPB/_BM/_BX/_BT/_BC : binders du contournement liant-TERME (cf. RSP).
_LIT_C, _LIT_T = "x", "xw"
_TPB, _BM, _BX, _BT, _BC = RSP._TPB, RSP._BM, RSP._BX, RSP._BT, RSP._BC


# ════════════════════════════════════════════════════════════════════════════
#  ✅ BRIQUE 1 (CLOSED) — RÉCUPÉRATION func/dom ⇒ équipotence.
# ════════════════════════════════════════════════════════════════════════════
def iso_implique_equipotent(f="f", X="X", Y="Y", R="R", Rp="Rp", x="x", y="y"):
    """⊢ ( est_isomorphisme_ordre(f,X,Y,R,R')  et  est_fonctionnel(f)  et  dom f=X )
            ⇒  Eq(X,Y).   CLOSED, 0 hypothèse.

    🎯 LE PONT « iso d'ordre nu → équipotence ».  `est_isomorphisme_ordre(f,X,Y,R,R')`
    = est_bijective(f,X,Y) ∧ compatible_ordre — il porte est_bijective MAIS PAS la
    structure d'application (fonctionnel + dom).  Or `equipotent(X,Y)` = (∃f)
    est_bijection_de(f,X,Y) avec est_bijection_de = (fonctionnel ∧ dom=X) ∧ est_bijective.
    AUGMENTÉ de est_fonctionnel(f) et dom f=X, l'iso RECOMPOSE est_bijection_de, d'où
    Eq(X,Y) par `bijection_implique_equipotent` (CLOS).  theorie=22, NON vacueux."""
    vf, vX, vY = _t(f), _t(X), _t(Y)
    R_de = lambda u, v: appartient(E.couple(_t(u), _t(v)), _t(R))
    Rp_de = lambda u, v: appartient(E.couple(_t(u), _t(v)), _t(Rp))
    iso = V.est_isomorphisme_ordre(vf, vX, vY, R_de, Rp_de, x, y)
    func = E.est_fonctionnel(vf)
    domeq = egal(E.dom(vf), vX)
    H = N.assume(et(et(iso, func), domeq))
    h_iso = conjonction_elim_gauche(conjonction_elim_gauche(H))      # est_isomorphisme_ordre
    h_func = conjonction_elim_droite(conjonction_elim_gauche(H))     # est_fonctionnel(f)
    h_dom = conjonction_elim_droite(H)                               # dom f = X
    bijective = conjonction_elim_gauche(h_iso)                       # est_bijective(f,X,Y)
    bij = conjonction_intro(conjonction_intro(h_func, h_dom), bijective)
    assert bij.conclusion == est_bijection_de(vf, vX, vY), \
        "recomposition est_bijection_de incorrecte"
    eq = N.modus_ponens(bij, bijection_implique_equipotent(vf, vX, vY))
    return N.loi_deduction(et(et(iso, func), domeq), eq)


def iso_implique_equipotent_cible(f="f", X="X", Y="Y", R="R", Rp="Rp", x="x", y="y"):
    """ÉNONCÉ-cible (test miroir) de iso_implique_equipotent."""
    vf, vX, vY = _t(f), _t(X), _t(Y)
    R_de = lambda u, v: appartient(E.couple(_t(u), _t(v)), _t(R))
    Rp_de = lambda u, v: appartient(E.couple(_t(u), _t(v)), _t(Rp))
    iso = V.est_isomorphisme_ordre(vf, vX, vY, R_de, Rp_de, x, y)
    return impl(et(et(iso, E.est_fonctionnel(vf)), egal(E.dom(vf), vX)),
                equipotent(vX, vY))


# ════════════════════════════════════════════════════════════════════════════
#  ✅ BRIQUE 2 (CLOSED) — injection F:c→a est une bijection sur SON image.
# ════════════════════════════════════════════════════════════════════════════
def injection_donne_equipotent_image(F="F", c="x", a="a"):
    """⊢ est_injection_de(F,c,a)  ⇒  Eq( c , image(F,c) ).   CLOSED, 0 hypothèse.

    🎯 L'injection F:c→a est une BIJECTION sur SON IMAGE.  est_injection_de(F,c,a) =
    ((fonctionnel ∧ dom=c) ∧ injective_dans(F,c)) ∧ image(F,c)⊂a.  Le DOMAINE est PLEIN
    (=c), donc AUCUNE restriction : on recompose est_bijection_de(F,c,image(F,c)) avec
    le conjoint surjectif image(F,c)=image(F,c) = RÉFLEXIVITÉ.  `bijection_implique_
    equipotent` (CLOS) conclut Eq(c,image(F,c)).  theorie=22, NON vacueux."""
    vF, vc, va = _t(F), _t(c), _t(a)
    img = E.image(vF, vc)
    inj = est_injection_de(vF, vc, va)
    H = N.assume(inj)
    fonc_dom = conjonction_elim_gauche(conjonction_elim_gauche(H))   # fonctionnel ∧ dom=c
    inj_dans = conjonction_elim_droite(conjonction_elim_gauche(H))   # injective_dans(F,c)
    bijective = conjonction_intro(inj_dans, N.reflexivite(img))      # est_bijective(F,c,image)
    bij = conjonction_intro(fonc_dom, bijective)                     # est_bijection_de(F,c,image)
    assert bij.conclusion == est_bijection_de(vF, vc, img), \
        "recomposition est_bijection_de(F,c,image) incorrecte"
    eq = N.modus_ponens(bij, bijection_implique_equipotent(vF, vc, img))
    return N.loi_deduction(inj, eq)


def injection_donne_equipotent_image_cible(F="F", c="x", a="a"):
    """ÉNONCÉ-cible (test miroir) de injection_donne_equipotent_image."""
    vF, vc, va = _t(F), _t(c), _t(a)
    return impl(est_injection_de(vF, vc, va), equipotent(vc, E.image(vF, vc)))


# ════════════════════════════════════════════════════════════════════════════
#  ÉNONCÉS — le maillon order-théorique HONNÊTE et sa GARDE cardinale.
# ════════════════════════════════════════════════════════════════════════════
def subset_realise_segment(Ro="Ro", a="a", B="Bsr", t=_LIT_T):
    """ÉNONCÉ (LE SEUL maillon honnête, PUR ORDRE) — « tout sous-ensemble de (a,Ro) est
    équipotent à un segment initial » :

        (∀B)( B ⊂ a  ⇒  (∃t)( t∈a  et  Eq( B , seg(a,Ro,t) ) ) ).

    ⚠️ NON PROUVÉ ICI — effondrement de Mostowski / représentation ordinale §III.2 ;
    correspond à la trichotomie de deux bons ordres (résidu structurel R1–R4 non clos,
    ensembles_trichotomie_assemble).  Isolé en HYPOTHÈSE, JAMAIS postulé."""
    vB, va = _t(B), _t(a)
    Bn = B if isinstance(B, str) else B.nom
    tn = t if isinstance(t, str) else t.nom
    vt = var(tn)
    return pourtout(Bn, impl(inclus(vB, va),
                             existe(tn, et(appartient(vt, va),
                                           equipotent(vB, seg(Ro, va, vt))))))


def realisation_segment_garde(Ro="Ro", a="a", c=_LIT_C, t=_LIT_T):
    """ÉNONCÉ — la VERSION GARDÉE (VRAIE) de la réalisation : la garde `est_cardinal`
    EST la correction du défaut littéral de `(∀c) realisation_segment` :

        (∀c)( est_cardinal(c)  ⇒  realisation_segment(Ro,a,c) ).

    binder c='x' (de est_cardinal/realisation), t='xw' (de realisation)."""
    cn = c if isinstance(c, str) else c.nom
    return pourtout(cn, impl(est_cardinal(var(cn)), HTP.realisation_segment(Ro, a, cn, t)))


# ════════════════════════════════════════════════════════════════════════════
#  helpers de réalisation gardée (instances-termes des bridges CLOS)
# ════════════════════════════════════════════════════════════════════════════
def _card_eq_si_eq(u, v):
    """⊢ Eq(u,v) ⇒ ( Card u = Card v )  aux TERMES u,v  (cardinal_egal_si_equipotent)."""
    gen = N.generalisation("Xq", N.generalisation("Yq", cardinal_egal_si_equipotent("Xq", "Yq")))
    return instancie(instancie(gen, _t(u)), _t(v))


def _est_cardinal_de_interv(a, c):
    """⊢ ( c ∈ [0,a] ) ⇒ est_cardinal(c)  (intervalle_implique_cardinal, [0,a])."""
    gen = N.generalisation("Xb", N.generalisation("Yb", N.generalisation("xb",
        intervalle_implique_cardinal("Xb", "Yb", "xb"))))
    return instancie(instancie(instancie(gen, ZERO), _t(a)), _t(c))


# ════════════════════════════════════════════════════════════════════════════
#  🎯 réalisation gardée DÉRIVÉE de subset_realise_segment.
# ════════════════════════════════════════════════════════════════════════════
def realisation_garde_depuis_subset(Ro="Ro", a="a", c=_LIT_C, t=_LIT_T):
    """⊢ { subset_realise_segment(Ro,a) }  ⊢  realisation_segment_garde(Ro,a).

    🎯 Pour c CARDINAL avec c≤a : F:c→a (témoin de c≤a via existe_temoin), B:=image(F)
    ⊂a (4e conjoint de est_injection_de), Eq(c,B) (injection_donne_equipotent_image) ;
    subset_realise_segment(B) donne t∈a, Eq(B,seg(a,Ro,t)) ; d'où Card(c)=Card(B)=
    Card(seg) (Prop 1, cardinal_egal_si_equipotent) et Card(c)=c (est_cardinal(c),
    _cardinal_est_son_cardinal) ⇒ Card(seg)=c.  On bâtit (∃t)(t∈a et Card(seg)=c),
    décharge c≤a → realisation_segment(Ro,a,c), garde par est_cardinal(c), généralise
    sur c.  theorie=22, NON vacueux."""
    va, vc = _t(a), var(c)
    tn = t if isinstance(t, str) else t.nom
    vt = var(tn)
    inj_F = est_injection_de(var("F"), vc, va)

    # témoin F de c≤a, B := image(F,c), B⊂a, Eq(c,B)
    Hle = N.assume(inf_egal_card(vc, va))
    wit = N.modus_ponens(Hle, N.existe_temoin(inj_F, "F"))          # est_injection_de(τF,c,a)
    Ft = tau("F", inj_F)
    B = E.image(Ft, vc)
    B_sub_a = conjonction_elim_droite(wit)                          # image(τF,c) ⊂ a
    eq_cB = N.modus_ponens(wit, injection_donne_equipotent_image(Ft, vc, va))   # Eq(c,B)

    # subset_realise_segment appliqué à B
    H_srs = N.assume(subset_realise_segment(Ro, a))
    ex_t = N.modus_ponens(B_sub_a, instancie(H_srs, B))            # (∃t)(t∈a et Eq(B,seg))

    # Card(c)=c (garde) et Card(c)=Card(B)
    H_card = N.assume(est_cardinal(vc))
    cc_eq_c = N.modus_ponens(H_card, _cardinal_est_son_cardinal(vc))   # Card c = c
    cardC_eq_B = N.modus_ponens(eq_cB, _card_eq_si_eq(vc, B))          # Card c = Card B

    # per-témoin t : ( t∈a et Eq(B,seg) ) ⊢ ( t∈a et Card(seg)=c )
    segt = seg(Ro, va, vt)
    corps_t = et(appartient(vt, va), equipotent(B, segt))
    Ht = N.assume(corps_t)
    t_in_a = conjonction_elim_gauche(Ht)
    eq_B_seg = conjonction_elim_droite(Ht)                         # Eq(B,seg)
    cardB_eq_seg = N.modus_ponens(eq_B_seg, _card_eq_si_eq(B, segt))   # Card B = Card seg
    cardC_eq_seg = composer_egalites(cardC_eq_B, cardB_eq_seg)         # Card c = Card seg
    c_eq_cardC = N.modus_ponens(cc_eq_c, _sym_eq(cardinal(vc), vc))    # c = Card c
    c_eq_seg = composer_egalites(c_eq_cardC, cardC_eq_seg)            # c = Card seg
    cardseg_eq_c = N.modus_ponens(c_eq_seg, _sym_eq(vc, cardinal(segt)))   # Card seg = c

    target_body = et(appartient(vt, va), egal(cardinal(segt), vc))
    body = conjonction_intro(t_in_a, cardseg_eq_c)
    assert body.conclusion == target_body, "corps réalisation mal formé"
    ex_concl = N.modus_ponens(body, N.s5(target_body, vt, tn))     # (∃t) target_body
    body_imp = N.loi_deduction(corps_t, ex_concl)
    real_concl = N.modus_ponens(ex_t, existe_elimination(body_imp, tn))   # (∃t)(t∈a et Card seg=c)

    real_seg = N.loi_deduction(inf_egal_card(vc, va), real_concl)  # realisation_segment(Ro,a,c)
    guarded_body = N.loi_deduction(est_cardinal(vc), real_seg)     # est_cardinal(c) ⇒ real
    res = N.generalisation(c, guarded_body)                        # (∀c)(est_cardinal ⇒ real)
    assert res.conclusion == realisation_segment_garde(Ro, a, c, t), \
        "conclusion ≠ realisation_segment_garde"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  ONTO/≠∅ gardés — MÊME conclusion que HTP.pullback_onto / pullback_non_vide,
#  garde `est_cardinal(c)` DÉCHARGÉE par c∈[0,a] (site où c∈S⊂[0,a]).
# ════════════════════════════════════════════════════════════════════════════
def pullback_onto_garde(a="a", Ro="Ro", S="S", c=_LIT_C, t=_LIT_T):
    """⊢ { S⊂[0,a],  realisation_segment_garde(Ro,a) }
            ⊢ (∀c)( c∈S ⇒ (∃t)( t∈pullback(a,Ro,S) et c=Card(seg(a,Ro,t)) ) ).

    🎯 MIROIR EXACT de `HTP.pullback_onto` (conclusion == hyp_realisation_onto), avec
    la garde `est_cardinal(c)` (de realisation_segment_garde) DÉCHARGÉE par c∈[0,a]
    (établi ICI : c∈S⊂[0,a]).  theorie=22, conclusion == HTP.pullback_onto."""
    cn = c if isinstance(c, str) else c.nom
    tn = t if isinstance(t, str) else t.nom
    vc, vt = var(cn), var(tn)
    va, vS = _t(a), _t(S)
    PB = HTP.pullback(a, Ro, S)

    H_realg = N.assume(realisation_segment_garde(Ro, a, cn, tn))
    Hc = N.assume(appartient(vc, vS))                              # c∈S
    c_interv = N.modus_ponens(Hc, HTP._inclus_S_interv(a, S, vc))  # c∈[0,a]   (S⊂[0,a])
    c_le_a = HTP._c_le_a(a, vc, c_interv)                          # c ≤ a
    est_card_c = N.modus_ponens(c_interv, _est_cardinal_de_interv(a, vc))   # est_cardinal(c)
    real_c = N.modus_ponens(est_card_c, instancie(H_realg, vc))    # c≤a ⇒ (∃t)…
    ex_t = N.modus_ponens(c_le_a, real_c)                          # (∃t)( t∈a et Card seg=c )

    cardseg = cardinal(seg(Ro, a, vt))
    corps_t = et(appartient(vt, va), egal(cardseg, vc))
    Ht = N.assume(corps_t)
    t_in_a = conjonction_elim_gauche(Ht)
    eq_cardseg_c = conjonction_elim_droite(Ht)
    c_eq_cardseg = HTP._sym(cardseg, vc, eq_cardseg_c)
    cardseg_in_S = HTP._leib_transport(vc, cardseg, c_eq_cardseg,
                                       lambda w: appartient(w, vS), Hc)   # Card(seg)∈S
    corps_membre = conjonction_intro(t_in_a, cardseg_in_S)
    t_in_PB = N.modus_ponens(corps_membre, equivalence_arriere(HTP.pullback_membre(a, Ro, S, tn)))
    cible_corps = conjonction_intro(t_in_PB, c_eq_cardseg)
    body_ex = et(appartient(vt, PB), egal(vc, cardseg))
    ex_intro = N.modus_ponens(cible_corps, N.s5(body_ex, vt, tn))
    wit_imp = N.loi_deduction(corps_t, ex_intro)
    ex_from = N.modus_ponens(ex_t, existe_elimination(wit_imp, tn))
    res = N.generalisation(cn, N.loi_deduction(appartient(vc, vS), ex_from))
    assert res.conclusion == HTP.pullback_onto(a, Ro, S, cn, tn).conclusion, \
        "pullback_onto_garde ≠ HTP.pullback_onto (conclusion)"
    return res


def pullback_non_vide_garde(a="a", Ro="Ro", S="S", c=BOIO._BC, t=BOIO._BX):
    """⊢ { S⊂[0,a],  S≠∅,  realisation_segment_garde(Ro,a) }  ⊢  ¬( pullback(a,Ro,S)=∅ ).

    🎯 MIROIR EXACT de `HTP.pullback_non_vide`, ONTO fourni par `pullback_onto_garde`.
    theorie=22, conclusion == HTP.pullback_non_vide."""
    from bourbaki.ensembles.base.ensembles_vide import non_vide_ssi_element
    cn = c if isinstance(c, str) else c.nom
    tn = t if isinstance(t, str) else t.nom
    vc, vt = var(cn), var(tn)
    vS = _t(S)
    PB = HTP.pullback(a, Ro, S)

    nv = non_vide_ssi_element(vS)
    H_ne = N.assume(non(egal(vS, E.VIDE)))
    ex_z = N.modus_ponens(H_ne, equivalence_avant(nv))
    ex_c = N.modus_ponens(ex_z, equivalence_avant(
        alpha_existe("z", cn, appartient(var("z"), vS))))          # (∃c) c∈S

    onto = pullback_onto_garde(a, Ro, S, cn, tn)
    onto_c = instancie(onto, vc)
    Hc = N.assume(appartient(vc, vS))
    ex_t = N.modus_ponens(Hc, onto_c)
    corps_t = et(appartient(vt, PB), egal(vc, cardinal(seg(Ro, a, vt))))
    Ht = N.assume(corps_t)
    t_in_PB = conjonction_elim_gauche(Ht)
    Heq = N.assume(egal(PB, E.VIDE))
    t_in_vide = HTP._leib_transport(PB, E.VIDE, Heq, lambda w: appartient(vt, w), t_in_PB)
    not_t_vide = HTP._vide_sans_element_t(vt)
    falso = HTP._ex_falso(t_in_vide, not_t_vide, non(egal(PB, E.VIDE)))
    not_PB_vide = HTP._refute_self(N.loi_deduction(egal(PB, E.VIDE), falso))
    body_t = N.loi_deduction(corps_t, not_PB_vide)
    not_from_t = N.modus_ponens(ex_t, existe_elimination(body_t, tn))
    body_c = N.loi_deduction(appartient(vc, vS), not_from_t)
    res = N.modus_ponens(ex_c, existe_elimination(body_c, cn))
    assert res.conclusion == HTP.pullback_non_vide(a, Ro, S).conclusion, \
        "pullback_non_vide_garde ≠ HTP.pullback_non_vide (conclusion)"
    return res


def corps_garde(a="a", Ro="Ro", S="S"):
    """⊢ { S⊂[0,a],  S≠∅,  realisation_segment_garde(Ro,a) }
            ⊢ ( PB⊂a  et  PB≠∅  et  INTO  et  ONTO )   (== HTP.hyp_transport_corps_cible).

    🎯 MIROIR EXACT de `HTP.hyp_transport_corps_preuve` avec ONTO/≠∅ GARDÉS.  Assemble
    pullback_inclus_a (CLOS) + pullback_non_vide_garde + pullback_into (CLOS) +
    pullback_onto_garde.  theorie=22, conclusion == HTP.hyp_transport_corps_cible."""
    pb_sub = HTP.pullback_inclus_a(a, Ro, S)                       # PB⊂a   [CLOS]
    pb_ne = pullback_non_vide_garde(a, Ro, S)                      # PB≠∅
    into = HTP.pullback_into(a, Ro, S, BOIO._BT)                   # INTO   [CLOS]
    onto = pullback_onto_garde(a, Ro, S, BOIO._BC, BOIO._BX)       # ONTO
    g2 = conjonction_intro(pb_sub, pb_ne)
    g1 = conjonction_intro(g2, into)
    res = conjonction_intro(g1, onto)
    assert res.conclusion == HTP.hyp_transport_corps_cible(a, Ro, S), \
        "corps_garde ≠ HTP.hyp_transport_corps_cible"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  CLAUSE de plus petit (PIÈCE A–B) — réplique RSP avec corps_garde.
# ════════════════════════════════════════════════════════════════════════════
def clause_pour_S_garde(Ro="Ro", a="a", S="S", T=_TPB):
    """⊢ { realisation_segment_garde(Ro,a), S⊂[0,a], S≠∅ }
            ⊢ (∃m)( m∈S et (∀x)( x∈S ⇒ R_induit{m,x} ) ).

    🎯 MIROIR EXACT de `RSP.clause_pour_S_sans_terme` (même contournement liant-TERME
    via T='Tpb'), le témoin (∃Tpb)B(Tpb) étant fourni par `corps_garde` au lieu de
    HTP.hyp_transport_corps_preuve.  bo_form ABSENT (la clause-min n'en a pas besoin :
    bo_form est consommé plus loin, par clause_min_intervalle_de_pullback qui le porte
    déjà — cf. RSP).  theorie=22."""
    va, vT = _t(a), _t(T)
    PB = HTP.pullback(a, Ro, S)
    Tn = T if isinstance(T, str) else T.nom

    cm = BOIO.clause_min_intervalle_de_pullback(Ro, a, S, Tn, m=_BM, x=_BX, c=_BC)
    into = BOIO.hyp_realisation_min(Ro, a, S, Tn, t=_BT)
    onto = BOIO.hyp_realisation_onto(Ro, a, S, Tn, _BC, _BX)
    Tsub = inclus(vT, va)
    Tne = non(egal(vT, E.VIDE))
    B_T = RSP._corps_B(Ro, a, S, Tn)

    HB = N.assume(B_T)
    g1 = conjonction_elim_gauche(HB)
    onto_p = conjonction_elim_droite(HB)
    g2 = conjonction_elim_gauche(g1)
    into_p = conjonction_elim_droite(g1)
    Tsub_p = conjonction_elim_gauche(g2)
    Tne_p = conjonction_elim_droite(g2)
    cm2 = RSP._dech(cm, Tsub, Tsub_p)
    cm2 = RSP._dech(cm2, Tne, Tne_p)
    cm2 = RSP._dech(cm2, into, into_p)
    cm2 = RSP._dech(cm2, onto, onto_p)

    ex_imp = existe_elimination(N.loi_deduction(B_T, cm2), Tn)
    corps = corps_garde(a, Ro, S)                                 # B(PB)  [garde, S⊂[0,a], S≠∅]
    ex_B = N.modus_ponens(corps, N.s5(B_T, PB, Tn))              # (∃Tpb)B(Tpb)
    return N.modus_ponens(ex_B, ex_imp)


def clause_plus_petit_garde(Ro="Ro", a="a", S="S"):
    """⊢ { realisation_segment_garde(Ro,a) }  ⊢  clause_plus_petit( ≤_induit , [0,a] ).

    🎯 MIROIR EXACT de `RSP.clause_plus_petit_depuis_realisation` : décharge
    (S⊂[0,a] et S≠∅) sur la clause pour S (clause_pour_S_garde), généralise sur S.
    theorie=22."""
    va, vS = _t(a), _t(S)
    Ssub = inclus(vS, intervalle_0a(a))
    Sne = non(egal(vS, E.VIDE))
    HsS = et(Ssub, Sne)
    cs = clause_pour_S_garde(Ro, a, S, _TPB)
    HHsS = N.assume(HsS)
    cs2 = RSP._dech(cs, Ssub, conjonction_elim_gauche(HHsS))
    cs2 = RSP._dech(cs2, Sne, conjonction_elim_droite(HHsS))
    imp_body = N.loi_deduction(HsS, cs2)
    return N.generalisation(S, imp_body)


# ════════════════════════════════════════════════════════════════════════════
#  PIÈCE C — bon_ordre_intervalle(a) sous { bo_form(Ro), realisation_segment_garde }.
# ════════════════════════════════════════════════════════════════════════════
def bon_ordre_intervalle_sous_bo_form_garde(Ro="Ro", a="a", S="S"):
    """⊢ { bo_form(Ro,a),  realisation_segment_garde(Ro,a) }  ⊢  bon_ordre_intervalle(a).

    🎯 MIROIR EXACT de `RSP.bon_ordre_intervalle_sous_bo_form` (PIÈCE C), version GARDÉE.
    Conjoint la PARTIE ORDRE (relation_ordre_dans_intervalle, CLOSE) et la CLAUSE
    (clause_plus_petit_garde).  `clause_min_intervalle_de_pullback` (via
    clause_plus_petit_garde) PORTE bo_form(Ro,a) = est_bien_ordonne(_R_de(Ro),a) — BIEN
    FORMÉ (∀Tpb = chaîne) — qui sera éliminé par ZERMELO dans le GATE.  theorie=22,
    conclusion == bon_ordre_intervalle(a)."""
    clause = clause_plus_petit_garde(Ro, a, S)                   # [bo_form, garde]
    rod = relation_ordre_dans_intervalle(a)                      # CLOS
    res = conjonction_intro(rod, clause)
    assert res.conclusion == bon_ordre_intervalle(a), \
        "conclusion ≠ bon_ordre_intervalle(a)"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  🎯🎯 LE GATE ℕ — bon_ordre_intervalle(a) sous le SEUL maillon subset_realise_segment.
# ════════════════════════════════════════════════════════════════════════════
def bon_ordre_intervalle_depuis_subset(a="a", Ro="Ro", S="S"):
    """⊢ { subset_realise_segment(Ro,a) }  ⊢  bon_ordre_intervalle(a)
                                              (== est_bien_ordonne(≤_induit,[0,a]), LITTÉRAL).

    🎯🎯 LE GATE ℕ FERMÉ AU SEUL maillon HONNÊTE order-théorique.  En quatre temps :
      • bon_ordre_intervalle(a) sous { bo_form(Ro), realisation_segment_garde }
        (bon_ordre_intervalle_sous_bo_form_garde, PIÈCE C) ;
      • bo_form(Ro) DÉCHARGÉ : ZERMELO (RSP.zermelo_bo_form, CLOS) ÉLIMINE ∃Ro (bo_form
        bien formé) ; `realisation_segment_garde` est Ro-INDÉPENDANTE (seg(a,·,t) ne
        porte pas Ro syntaxiquement — terme seg_ext(a,t)), donc inchangée par ∃Ro ;
      • realisation_segment_garde DÉRIVÉE de subset_realise_segment
        (realisation_garde_depuis_subset, Ro-indépendante elle aussi) ;
      • on décharge la garde.
    HYPOTHÈSE SURVIVANTE UNIQUE : `subset_realise_segment(Ro,a)` — pur ordre, JAMAIS
    postulé.  theorie=22.  Conclusion == bon_ordre_intervalle(a) LITTÉRALEMENT."""
    bo = BOIO._bo_form_canon(a, Ro, _TPB, _BM, _BX)              # est_bien_ordonne(_R_de(Ro),a)
    boi = bon_ordre_intervalle_sous_bo_form_garde(Ro, a, S)      # [bo_form, garde]
    # ÉLIMINER ∃Ro via Zermelo (bo_form bien formé ; garde Ro-indépendante)
    imp_Ro = N.loi_deduction(bo, boi)                           # bo_form(Ro) ⇒ boi  [garde]
    ex_Ro_imp = existe_elimination(imp_Ro, Ro)                  # (∃Ro)bo_form ⇒ boi  [garde]
    boi_garde = N.modus_ponens(RSP.zermelo_bo_form(a), ex_Ro_imp)   # bon_ordre_intervalle(a)  [garde]
    # DÉCHARGER la garde sur subset_realise_segment
    garde = realisation_segment_garde(Ro, a)
    rg = realisation_garde_depuis_subset(Ro, a)                 # [subset] ⊢ garde
    res = N.modus_ponens(rg, N.loi_deduction(garde, boi_garde))
    assert res.conclusion == bon_ordre_intervalle(a), \
        "conclusion ≠ bon_ordre_intervalle(a)"
    return res


def cardinaux_bien_ordonnes_depuis_subset(a="a", Ro="Ro", S="S"):
    """⊢ { subset_realise_segment(Ro,a) }  ⊢  cardinaux_bien_ordonnes(a)  (LITTÉRAL).

    🎯🎯 Décharge `bon_ordre_intervalle_depuis_subset` dans
    `cardinaux_bien_ordonnes_de_bon_ordre` (CLOS modulo bon_ordre_intervalle(a)).
    SEULE hypothèse : subset_realise_segment.  theorie=22, conclusion ==
    cardinaux_bien_ordonnes(a)."""
    gd = bon_ordre_intervalle_depuis_subset(a, Ro, S)            # [subset] ⊢ bon_ordre_intervalle(a)
    cbo = cardinaux_bien_ordonnes_de_bon_ordre(a)               # [bon_ordre_intervalle] ⊢ cbo
    res = N.modus_ponens(gd, N.loi_deduction(bon_ordre_intervalle(a), cbo))
    assert res.conclusion == cardinaux_bien_ordonnes(a), \
        "conclusion ≠ cardinaux_bien_ordonnes(a)"
    return res


# ── cibles / hypothèses attendues (tests miroir) ──────────────────────────────
def bon_ordre_intervalle_depuis_subset_cible(a="a"):
    """ÉNONCÉ-cible : bon_ordre_intervalle(a)."""
    return bon_ordre_intervalle(a)


def cardinaux_bien_ordonnes_depuis_subset_cible(a="a"):
    """ÉNONCÉ-cible : cardinaux_bien_ordonnes(a)."""
    return cardinaux_bien_ordonnes(a)


def hypothese_unique(a="a", Ro="Ro"):
    """L'UNIQUE hypothèse SURVIVANTE ATTENDUE : { subset_realise_segment(Ro,a) }."""
    return {subset_realise_segment(Ro, a)}


__all__ = [
    "iso_implique_equipotent", "iso_implique_equipotent_cible",
    "injection_donne_equipotent_image", "injection_donne_equipotent_image_cible",
    "subset_realise_segment", "realisation_segment_garde",
    "realisation_garde_depuis_subset",
    "pullback_onto_garde", "pullback_non_vide_garde", "corps_garde",
    "clause_pour_S_garde", "clause_plus_petit_garde",
    "bon_ordre_intervalle_sous_bo_form_garde",
    "bon_ordre_intervalle_depuis_subset", "cardinaux_bien_ordonnes_depuis_subset",
    "bon_ordre_intervalle_depuis_subset_cible",
    "cardinaux_bien_ordonnes_depuis_subset_cible", "hypothese_unique",
]
