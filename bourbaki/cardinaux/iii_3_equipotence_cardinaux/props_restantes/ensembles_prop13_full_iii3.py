"""§III.3.6 — PROPOSITION 13 (ÉQUIVALENCE COMPLÈTE) : a ≥ b ⟺ (∃c) a = b + c.

🎯🎯 ASSEMBLE l'équivalence bourbakiste EXACTE (E III.29, LUE au PDF source) :

    « PROPOSITION 13. — Soient a et b des cardinaux ; pour que l'on ait a ≥ b, il
      faut et il suffit qu'il existe un cardinal c tel que a = b + c. »

soit, en notant ≤ (b ≤ a) la relation bourbakiste « a ≥ b » :

    prop13_equivalence(a, b) :
        ⊢ ( est_cardinal(a) et est_cardinal(b) )
              ⇒ ( b ≤ a  ⟺  (∃c)( est_cardinal(c) et a = b + c ) ).

────────────────────────────────────────────────────────────────────────────────
SENS ⇒ (b ≤ a ⇒ (∃c)(card c et a = b+c)) — le cœur combinatoire est DÉJÀ CLOS dans
`existe_complement_depuis_inf_egal` (témoin c := Card(a∖f⟨b⟩), donc LITTÉRALEMENT un
cardinal).  On le ré-emploie en CONJOIGNANT est_cardinal(c) (trivial : Card R = Card R
témoigne (∃X) Card R = Card X) AVANT la quantification existentielle, puis on réécrit
Card a ↦ a sous est_cardinal(a).

SENS ⇐ ((∃c)(card c et a = b+c) ⇒ b ≤ a) — de a = b + c et b ≤ b + c on conclut b ≤ a
(Leibniz).  Le sous-lemme b ≤ b + c (= b ≤ Card(b⊔c)) :
    inf_egal_somme_gauche : b ≤ b⊔c  (injection gauche u↦(u,0), niveau ensembles) ;
    inf_egal_transporte_cardinal : Card b ≤ Card(b⊔c) = b + c ;
    sous est_cardinal(b) : Card b = b ⇒ b ≤ b + c.

⚠️ INVARIANT : theorie_ensembles() = 22.  RIEN POSTULÉ : tout DÉRIVE de théorèmes
   CLOS (existe_complement_depuis_inf_egal, inf_egal_somme_gauche,
   inf_egal_transporte_cardinal, _cardinal_est_son_cardinal).  NE MODIFIE AUCUN
   fichier existant.  Gardes HONNÊTES : est_cardinal(a), est_cardinal(b) (l'énoncé
   bourbakiste « a et b cardinaux »).
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (
    Terme, var, egal, et, impl, existe, equiv, tau,
)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite, instancie,
    equivalence_avant,
)
from bourbaki.logique.i_3_quantifies.tactiques_abrege_quantif import existe_elimination
from bourbaki.logique.i_4_egalitaires.tactiques_abrege_egalite import (
    symetrie, composer_egalites,
)

from bourbaki.cardinaux.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    est_cardinal, cardinal, inf_egal_card, est_injection_de, equipotent,
)
from bourbaki.ensembles.familles.ii_4_reunion_intersection_familles.ii_4_recollement_somme.ensembles_somme_disjointe import (
    somme_disjointe, somme_cardinale_binaire,
)

# briques CLOSES réutilisées (cœur combinatoire : on RE-construit le complément en
# conjoignant est_cardinal(Card R) — les _*_t sont les helpers term-safe CLOS)
from bourbaki.cardinaux.iii_3_equipotence_cardinaux.props_restantes.ensembles_prop13_complement import (
    injection_donne_equipotent_image,
    _eq_sym_t, _prop1_direct_t, _cardinal_est_son_cardinal_t as _cesc_t,
    _partie_reunion_complement_t, _partie_disjoint_complement_t,
    _eq_reunion_disjointe_somme_t, _somme_disjointe_cardinal_t,
)
from bourbaki.cardinaux.iii_3_equipotence_cardinaux.somme_produit_bornes.ensembles_cardinaux_bornes_somme import inf_egal_somme_gauche
from bourbaki.cardinaux.arithmetique.iii_3_2_monotonie.ensembles_arith_cardinale_props_exposant_monotone import (
    inf_egal_transporte_cardinal,
)
from bourbaki.cardinaux.iii_3_equipotence_cardinaux.ordre_cardinaux.ensembles_cardinaux_props_restantes_ordre import (
    _cardinal_est_son_cardinal,
)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# ──────────────────────────────────────────────────────────────────────────────
#  helpers term-tolérants (généralise puis instancie : capture-safe)
# ──────────────────────────────────────────────────────────────────────────────
def _inf_egal_somme_gauche_t(tb, tc):
    """⊢ B ≤ B⊔C  pour des TERMES B, C quelconques (capture-safe)."""
    gen = N.generalisation("Bg13", N.generalisation("Cg13",
            inf_egal_somme_gauche("Bg13", "Cg13")))
    return instancie(instancie(gen, _t(tb)), _t(tc))


def _inf_egal_transporte_cardinal_t(tX, tY):
    """⊢ (X ≤ Y) ⇒ (Card X ≤ Card Y)  pour des TERMES X, Y (capture-safe)."""
    gen = N.generalisation("Xt13", N.generalisation("Yt13",
            inf_egal_transporte_cardinal("Xt13", "Yt13")))
    return instancie(instancie(gen, _t(tX)), _t(tY))


def _est_cardinal_card_t(tR, witness="X"):
    """⊢ est_cardinal(Card R)  pour un TERME R (Card R = Card R témoigne (∃X) Card R=Card X)."""
    vR = _t(tR)
    cR = cardinal(vR)
    refl = N.reflexivite(cR)                                   # Card R = Card R
    body = egal(cR, cardinal(var(witness)))                    # Card R = Card X
    return N.modus_ponens(refl, N.s5(body, vR, witness))       # (∃X) Card R = Card X  (témoin X:=R)


# ══════════════════════════════════════════════════════════════════════════════
#  SENS ⇒   :  b ≤ a  ⇒  (∃c)( est_cardinal(c) et a = b + c )
# ══════════════════════════════════════════════════════════════════════════════
def _complement_cardinal_avec_card(b, a, c):
    """⊢ ( est_cardinal(b) et b ≤ a ) ⇒ (∃c)( est_cardinal(c) et Card a = b + c ).

    RE-construit le cœur combinatoire de existe_complement_depuis_inf_egal (témoin
    c := Card R, R = a∖f⟨b⟩) MAIS conjoint est_cardinal(Card R) AVANT le S5, pour
    PRÉSERVER que le témoin est un cardinal (Card R = Card R ⇒ est_cardinal(Card R)).
    Tout DÉRIVE des mêmes briques closes (helpers _*_t importés)."""
    vb, va = _t(b), _t(a)
    cname = c if isinstance(c, str) else c.nom
    inj_F = est_injection_de(var("F"), vb, va)

    ante = et(est_cardinal(vb), inf_egal_card(vb, va))
    h = N.assume(ante)
    h_card_b = conjonction_elim_gauche(h)
    h_le = conjonction_elim_droite(h)

    wit = N.modus_ponens(h_le, N.existe_temoin(inj_F, "F"))        # est_injection_de(τF,b,a)
    Ft = tau("F", inj_F)
    Im = E.image(Ft, vb)
    R = E.difference(va, Im)
    cR = cardinal(R)                                              # c := Card R
    Im_sub_a = conjonction_elim_droite(wit)
    eq_b_Im = N.modus_ponens(wit, injection_donne_equipotent_image(Ft, vb, va))

    eq_Im_b = N.modus_ponens(eq_b_Im, _eq_sym_t(vb, Im))
    cardIm_eq_cardb = N.modus_ponens(eq_Im_b, _prop1_direct_t(Im, vb))
    cardb_eq_b = N.modus_ponens(h_card_b, _cesc_t(vb))
    cardIm_eq_b = composer_egalites(cardIm_eq_cardb, cardb_eq_b)  # Card Im = b

    ImR = E.reunion(Im, R)
    ImsR = somme_disjointe(Im, R)
    ImR_eq_a = N.modus_ponens(Im_sub_a, _partie_reunion_complement_t(va, Im))
    disj = _partie_disjoint_complement_t(va, Im)
    eq_union_somme = N.modus_ponens(disj, _eq_reunion_disjointe_somme_t(Im, R))
    eq_a_somme = N.modus_ponens(eq_union_somme, equivalence_avant(N.modus_ponens(
        ImR_eq_a, N.s6(ImR, va, "w13", equipotent(var("w13"), ImsR)))))
    carda_eq_cardsomme = N.modus_ponens(eq_a_somme, _prop1_direct_t(va, ImsR))

    sdc = _somme_disjointe_cardinal_t(Im, R, vb, cR)
    cardR_refl = N.reflexivite(cR)
    cardsomme_eq = N.modus_ponens(conjonction_intro(cardIm_eq_b, cardR_refl), sdc)

    bcR = somme_cardinale_binaire(vb, cR)                        # b + Card R
    carda_eq_bcR = composer_egalites(carda_eq_cardsomme, cardsomme_eq)   # Card a = b + Card R

    # est_cardinal(Card R)
    card_cR = _est_cardinal_card_t(R)                            # est_cardinal(Card R)
    conj = conjonction_intro(card_cR, carda_eq_bcR)             # est_cardinal(Card R) et Card a = b+Card R

    cible_body = et(est_cardinal(var(cname)),
                    egal(cardinal(va), somme_cardinale_binaire(vb, var(cname))))
    ex = N.modus_ponens(conj, N.s5(cible_body, cR, cname))      # (∃c)(est_cardinal(c) et Card a=b+c)
    return N.loi_deduction(ante, ex)


def prop13_forward_card(b="Bp13", a="Ap13", c="Cp13"):
    """⊢ ( est_cardinal(a) et est_cardinal(b) et b ≤ a )
            ⇒ (∃c)( est_cardinal(c) et a = b + c ).   (CLOS.)

    Cœur combinatoire (_complement_cardinal_avec_card, témoin c := Card R, cardinal)
    donne (∃c)(est_cardinal(c) et Card a = b+c) ; sous est_cardinal(a), Card a = a, on
    réécrit Card a ↦ a SOUS le témoin."""
    vb, va = _t(b), _t(a)
    cname = c if isinstance(c, str) else c.nom
    vc = var(cname)

    ante = et(et(est_cardinal(va), est_cardinal(vb)), inf_egal_card(vb, va))
    h = N.assume(ante)
    h_card_a = conjonction_elim_gauche(conjonction_elim_gauche(h))   # est_cardinal(a)
    h_card_b = conjonction_elim_droite(conjonction_elim_gauche(h))   # est_cardinal(b)
    h_le = conjonction_elim_droite(h)                               # b ≤ a

    comp = N.modus_ponens(conjonction_intro(h_card_b, h_le),
                          _complement_cardinal_avec_card(b, a, c))  # (∃c)(card c et Card a=b+c)

    carda_eq_a = N.modus_ponens(h_card_a, _cesc_t(va))             # Card a = a

    bc = somme_cardinale_binaire(vb, vc)
    body_src = et(est_cardinal(vc), egal(cardinal(va), bc))       # corps de `comp` (Card a)
    body_tgt = et(est_cardinal(vc), egal(va, bc))                 # corps cible (a)

    # per-témoin c : (card c et Card a=b+c) ⇒ (card c et a=b+c) ⇒ (∃c)(...)
    hbody = N.assume(body_src)
    h_card_c = conjonction_elim_gauche(hbody)                     # est_cardinal(c)
    h_carda_bc = conjonction_elim_droite(hbody)                   # Card a = b+c
    a_eq_bc = _reecrire_gauche(h_carda_bc, carda_eq_a, cardinal(va), va, bc, egal)  # a = b+c
    conj = conjonction_intro(h_card_c, a_eq_bc)                   # card c et a = b+c
    ex = N.modus_ponens(conj, N.s5(body_tgt, vc, cname))          # (∃c)(card c et a=b+c)
    imp_body = N.loi_deduction(body_src, ex)

    res = N.modus_ponens(comp, existe_elimination(imp_body, cname))
    out = N.loi_deduction(ante, res)
    assert out.conclusion == prop13_forward_card_enonce(a, b, c), \
        "prop13_forward_card : conclusion ≠ énoncé attendu"
    return out


def prop13_forward_card_enonce(a="Ap13", b="Bp13", c="Cp13"):
    va, vb = _t(a), _t(b)
    cname = c if isinstance(c, str) else c.nom
    vc = var(cname)
    but = existe(cname, et(est_cardinal(vc), egal(va, somme_cardinale_binaire(vb, vc))))
    return impl(et(et(est_cardinal(va), est_cardinal(vb)), inf_egal_card(vb, va)), but)


# ══════════════════════════════════════════════════════════════════════════════
#  SENS ⇐   :  (∃c)( est_cardinal(c) et a = b + c )  ⇒  b ≤ a
# ══════════════════════════════════════════════════════════════════════════════
def _inf_egal_b_plus_c(b, c):
    """⊢ est_cardinal(b) ⇒ ( b ≤ b + c )   pour des TERMES b, c.

    inf_egal_somme_gauche : b ≤ b⊔c ; inf_egal_transporte_cardinal :
    Card b ≤ Card(b⊔c) = somme_cardinale_binaire(b,c) ; sous est_cardinal(b),
    Card b = b ⇒ b ≤ b+c."""
    vb, vc = _t(b), _t(c)
    bsc = somme_disjointe(vb, vc)                  # b ⊔ c
    bc = somme_cardinale_binaire(vb, vc)           # b + c = Card(b⊔c)

    hcard = N.assume(est_cardinal(vb))
    le_set = _inf_egal_somme_gauche_t(vb, vc)                       # b ≤ b⊔c
    le_card = N.modus_ponens(le_set, _inf_egal_transporte_cardinal_t(vb, bsc))  # Card b ≤ Card(b⊔c)=b+c
    cardb_eq_b = N.modus_ponens(hcard, _cesc_t(vb))         # Card b = b
    # réécrire Card b ↦ b dans (Card b ≤ b+c)
    le_b = _reecrire_gauche(le_card, cardb_eq_b, cardinal(vb), vb, bc, inf_egal_card)  # b ≤ b+c
    return N.loi_deduction(est_cardinal(vb), le_b)


def prop13_backward_card(b="Bp13", a="Ap13", c="Cp13"):
    """⊢ ( est_cardinal(b) et (∃c)( est_cardinal(c) et a = b + c ) )  ⇒  b ≤ a.  (CLOS.)

    Per-témoin c : a = b + c et b ≤ b + c (inf_egal_b_plus_c, sous est_cardinal(b))
    ⇒ b ≤ a (réécrire b+c ↦ a)."""
    vb, va = _t(b), _t(a)
    cname = c if isinstance(c, str) else c.nom
    vc = var(cname)
    bc = somme_cardinale_binaire(vb, vc)
    body = et(est_cardinal(vc), egal(va, bc))      # est_cardinal(c) et a = b+c

    ante = et(est_cardinal(vb), existe(cname, body))
    h = N.assume(ante)
    h_card_b = conjonction_elim_gauche(h)          # est_cardinal(b)
    h_ex = conjonction_elim_droite(h)              # (∃c)(est_cardinal(c) et a=b+c)

    # per-témoin : body ⇒ b ≤ a
    hbody = N.assume(body)
    h_a_eq_bc = conjonction_elim_droite(hbody)     # a = b + c
    le_b_bc = N.modus_ponens(h_card_b, _inf_egal_b_plus_c(vb, vc))   # b ≤ b+c
    # réécrire b+c ↦ a : de a=b+c (sym ⇒ b+c=a) dans (b ≤ b+c)
    bc_eq_a = N.modus_ponens(h_a_eq_bc, symetrie(va, bc))            # b + c = a
    le_b_a = _reecrire_droite(le_b_bc, bc_eq_a, bc, va, vb, inf_egal_card)  # b ≤ a
    imp_body = N.loi_deduction(body, le_b_a)                         # body ⇒ b ≤ a

    res = N.modus_ponens(h_ex, existe_elimination(imp_body, cname))  # b ≤ a
    out = N.loi_deduction(ante, res)
    assert out.conclusion == prop13_backward_card_enonce(b, a, c), \
        "prop13_backward_card : conclusion ≠ énoncé attendu"
    return out


def prop13_backward_card_enonce(b="Bp13", a="Ap13", c="Cp13"):
    vb, va = _t(b), _t(a)
    cname = c if isinstance(c, str) else c.nom
    vc = var(cname)
    body = et(est_cardinal(vc), egal(va, somme_cardinale_binaire(vb, vc)))
    return impl(et(est_cardinal(vb), existe(cname, body)), inf_egal_card(vb, va))


# ══════════════════════════════════════════════════════════════════════════════
#  🎯🎯 PROPOSITION 13 §III.3.6 — ÉQUIVALENCE COMPLÈTE
# ══════════════════════════════════════════════════════════════════════════════
def prop13_equivalence_enonce(a="Ap13", b="Bp13", c="Cp13"):
    va, vb = _t(a), _t(b)
    cname = c if isinstance(c, str) else c.nom
    vc = var(cname)
    rhs = existe(cname, et(est_cardinal(vc), egal(va, somme_cardinale_binaire(vb, vc))))
    return impl(et(est_cardinal(va), est_cardinal(vb)),
                equiv(inf_egal_card(vb, va), rhs))


def prop13_equivalence(a="Ap13", b="Bp13", c="Cp13"):
    """🎯🎯 ⊢ ( est_cardinal(a) et est_cardinal(b) )
                ⇒ ( b ≤ a  ⟺  (∃c)( est_cardinal(c) et a = b + c ) ).   (CLOS.)

    PROPOSITION 13 §III.3.6, équivalence bourbakiste EXACTE.  ⇒ = prop13_forward_card,
    ⇐ = prop13_backward_card, packagés sous la garde honnête « a, b cardinaux »."""
    va, vb = _t(a), _t(b)
    cname = c if isinstance(c, str) else c.nom
    vc = var(cname)
    rhs = existe(cname, et(est_cardinal(vc), egal(va, somme_cardinale_binaire(vb, vc))))

    ante = et(est_cardinal(va), est_cardinal(vb))
    h = N.assume(ante)
    h_card_a = conjonction_elim_gauche(h)
    h_card_b = conjonction_elim_droite(h)

    # ⇒ : b≤a ⇒ rhs
    hle = N.assume(inf_egal_card(vb, va))
    fwd_ante = conjonction_intro(conjonction_intro(h_card_a, h_card_b), hle)
    fwd = N.modus_ponens(fwd_ante, prop13_forward_card(b, a, c))     # rhs
    imp_fwd = N.loi_deduction(inf_egal_card(vb, va), fwd)            # b≤a ⇒ rhs

    # ⇐ : rhs ⇒ b≤a
    hrhs = N.assume(rhs)
    bwd_ante = conjonction_intro(h_card_b, hrhs)
    bwd = N.modus_ponens(bwd_ante, prop13_backward_card(b, a, c))    # b≤a
    imp_bwd = N.loi_deduction(rhs, bwd)                             # rhs ⇒ b≤a

    iff = conjonction_intro(imp_fwd, imp_bwd)                       # (b≤a⇒rhs) et (rhs⇒b≤a) = ⟺
    out = N.loi_deduction(ante, iff)
    assert out.conclusion == prop13_equivalence_enonce(a, b, c), \
        "prop13_equivalence : conclusion ≠ énoncé attendu"
    return out


# ──────────────────────────────────────────────────────────────────────────────
#  micro-tactiques Leibniz (réécriture de termes dans une formule à un trou)
# ──────────────────────────────────────────────────────────────────────────────
def _reecrire_gauche(thm, eq_old_new, old, new, rhs_fixe, rel, hole="w13r"):
    """De ⊢ φ[old] et ⊢ old=new, où φ = rel(old, rhs_fixe), produire ⊢ φ[new].
    `rel` ∈ {egal, inf_egal_card} (membre GAUCHE réécrit)."""
    return _reecrire(thm, eq_old_new, old, new, lambda h: rel(h, rhs_fixe), hole)


def _reecrire_droite(thm, eq_old_new, old, new, lhs_fixe, rel, hole="w13r"):
    """idem mais réécrit le membre DROIT : φ = rel(lhs_fixe, old) ↦ rel(lhs_fixe, new)."""
    return _reecrire(thm, eq_old_new, old, new, lambda h: rel(lhs_fixe, h), hole)


def _reecrire(thm, eq_old_new, old, new, build, hole):
    """Leibniz générique : ⊢ φ[old], ⊢ old=new, build(t)=φ[t] ⇒ ⊢ φ[new] via S6."""
    vhole = var(hole)
    schema = build(vhole)                                      # φ[hole]
    equivf = N.modus_ponens(eq_old_new, N.s6(old, new, hole, schema))  # φ[old] ⟺ φ[new]
    return N.modus_ponens(thm, equivalence_avant(equivf))


__all__ = [
    "prop13_forward_card", "prop13_forward_card_enonce",
    "prop13_backward_card", "prop13_backward_card_enonce",
    "prop13_equivalence", "prop13_equivalence_enonce",
]
