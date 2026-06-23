"""§III.3.6 — PROPOSITION 13 (sens DIRECT) : EXISTENCE DU COMPLÉMENT CARDINAL.

🎯 FERME le report `existe_complement_cardinal` (ensembles_cardinaux_props_restantes,
champ `reportes`), seule hypothèse résiduelle du sens DIRECT de la Proposition 13
§III.3.6 « b ≤ a ⇒ (∃c) a = b + c ».  Le cœur combinatoire — « construire le reste
c = a ∖ f⟨b⟩ pour une injection f : b ↪ a » — est ici DÉMONTRÉ :

    existe_complement_depuis_inf_egal(b, a) :
        ⊢ ( est_cardinal(b)  et  inf_egal_card(b, a) )  ⇒  existe_complement_cardinal(b, a)

où  existe_complement_cardinal(b, a) := (∃c) Card(a) = somme_cardinale_binaire(b, c).

────────────────────────────────────────────────────────────────────────────────
PREUVE (témoin c := Card(a ∖ Im), Im := image(F, b) pour une injection F : b ↪ a).

  • inf_egal_card(b,a) = (∃F)est_injection_de(F,b,a) ; existe_temoin fixe F (= τF),
    et le 4ᵉ conjoint de est_injection_de donne  Im = image(F,b) ⊂ a.
  • Eq(b, Im)  (injection_donne_equipotent_image : une injection est une bijection sur
    SON image) ; symétrie ⇒ Eq(Im, b) ⇒ Card Im = Card b (Proposition 1, sens direct).
    Sous est_cardinal(b) : Card b = b (_cardinal_est_son_cardinal), d'où  Card Im = b.
  • R := a ∖ Im.  CŒUR (chirurgie partie/complément, comme eq_retire_ajoute) :
      – Im ⊂ a ⇒ Im ∪ R = a  (partie_reunion_complement) ;
      – Im ∩ R = ∅  (partie_disjoint_complement) ;
      – Eq(Im ∪ R, Im ⊔ R)  (eq_reunion_disjointe_somme, CLOS — Prop. 10 §II.4) ;
      – réécriture Im∪R ↦ a ⇒ Eq(a, Im ⊔ R) ⇒ Card a = Card(Im ⊔ R) (Proposition 1).
  • somme_disjointe_cardinal(Im, R, b, Card R) :
        (Card Im = b et Card R = Card R) ⇒ Card(Im ⊔ R) = somme_cardinale_binaire(b, Card R) ;
    Card Im = b (ci-dessus), Card R = Card R (réflexivité) ⇒
        Card(Im ⊔ R) = somme_cardinale_binaire(b, Card R).
  • composition ⇒  Card a = somme_cardinale_binaire(b, Card R), donc c := Card R témoigne
    (∃c) Card a = somme_cardinale_binaire(b, c) = existe_complement_cardinal(b, a).  S5.

PUIS on DÉCHARGE le report dans prop13_forward_conditionnel :

    prop13_forward_ferme(b, a) :
        ⊢ ( est_cardinal(a)  et  est_cardinal(b)  et  inf_egal_card(b, a) )
                ⇒  (∃c) a = b + c.

(la garde `est_cardinal(a)` provient de prop13_forward_conditionnel — nécessaire pour
identifier Card(a) à a ; `est_cardinal(b)` de notre construction du complément ; les
deux sont HONNÊTES — l'énoncé bourbakiste R{x,y} du Théorème 1 porte déjà « x,y
cardinaux ».)

⚠️ INVARIANT : theorie_ensembles() = 22.  RIEN POSTULÉ : tout DÉRIVE de théorèmes CLOS
   (injection_donne_equipotent_image, eq_reunion_disjointe_somme, somme_disjointe_cardinal,
   Proposition 1) sous les SEULES gardes honnêtes est_cardinal(a/b) + inf_egal_card(b,a).
   NE MODIFIE AUCUN fichier existant.
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (
    Terme, var, egal, et, non, impl, existe, pourtout, appartient, inclus, tau,
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

from bourbaki.cardinaux.ensembles_cardinaux import (
    est_cardinal, equipotent, cardinal, inf_egal_card, est_injection_de,
)
from bourbaki.ensembles.familles.ii_4_reunion_intersection_familles.ii_4_recollement_somme.ensembles_somme_disjointe import (
    somme_disjointe, somme_cardinale_binaire,
)

# ── briques CLOSES réutilisées ───────────────────────────────────────────────
from bourbaki.cardinaux.ensembles_realisation_segment_close import (
    injection_donne_equipotent_image,
)
from bourbaki.cardinaux.arithmetique.ensembles_arith_somme import (
    somme_disjointe_cardinal, _prop1_direct_t,
)
from bourbaki.cardinaux.arithmetique.ensembles_copie_marquee import _eq_sym_t
from bourbaki.cardinaux.ensembles_cardinaux_props_restantes_ordre import (
    _cardinal_est_son_cardinal,
)
from bourbaki.entiers.iii_4_entiers_finis.iii_4_recurrence_c61_existence_n.ensembles_predecesseur_prop2 import eq_reunion_disjointe_somme
from bourbaki.cardinaux.ensembles_cantor_bernstein_fin import (
    partie_reunion_complement, partie_disjoint_complement,
)

# énoncés EXACTS à fermer / décharger
from bourbaki.cardinaux.ensembles_cardinaux_props_restantes import (
    existe_complement_cardinal, prop13_forward_conditionnel,
)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def _cardinal_est_son_cardinal_t(tX):
    """⊢ est_cardinal(X) ⇒ (Card X = X)  pour un TERME X.

    _cardinal_est_son_cardinal accepte déjà un TERME (vx = _t(x)) et bâtit son
    antécédent est_cardinal(X) avec le binder PAR DÉFAUT « X » de est_cardinal ; le
    witness ∃ interne reste « X » aussi (≠ paramètre, lié), donc l'antécédent coïncide
    LITTÉRALEMENT avec est_cardinal(vX)."""
    return _cardinal_est_son_cardinal(_t(tX))


def _partie_reunion_complement_t(ta, tx):
    """⊢ (X ⊂ A) ⇒ (X ∪ (A∖X) = A)  pour des TERMES A, X (généralisé puis instancié).

    Le binder `z` de l'inclusion (défaut de `inclus`) est CONSERVÉ par l'instanciation
    (qui ne touche que les variables LIBRES Ar13/Xr13) ⇒ l'antécédent (X⊂A) coïncide
    avec la forme par défaut produite par est_injection_de (binder « z »)."""
    base = partie_reunion_complement("Ar13", "Xr13")               # CLOS (noms, z par défaut)
    gen = N.generalisation("Ar13", N.generalisation("Xr13", base))
    return instancie(instancie(gen, _t(ta)), _t(tx))


def _partie_disjoint_complement_t(ta, tx):
    """⊢ X ∩ (A∖X) = ∅  pour des TERMES A, X (généralisé puis instancié)."""
    base = partie_disjoint_complement("Ad13", "Xd13")              # CLOS (noms)
    gen = N.generalisation("Ad13", N.generalisation("Xd13", base))
    return instancie(instancie(gen, _t(ta)), _t(tx))


def _somme_disjointe_cardinal_t(tX, tY, ta, tb):
    """⊢ (Card X = a et Card Y = b) ⇒ Card(X⊔Y) = somme_cardinale_binaire(a,b)  pour des
    TERMES X, Y, a, b QUELCONQUES (capture-safe).

    somme_disjointe_cardinal bâtit la bijection-somme via eq_somme_invariant (liants
    internes « k, t, … ») : passer DIRECTEMENT des termes τ-imbriqués (Im, R) capture.
    On la construit en NOMS SYMBOLIQUES, GÉNÉRALISE, puis INSTANCIE aux termes."""
    base = somme_disjointe_cardinal("Xs13", "Ys13", "as13", "bs13")   # CLOS (noms)
    gen = N.generalisation("Xs13", N.generalisation("Ys13",
              N.generalisation("as13", N.generalisation("bs13", base))))
    return instancie(instancie(instancie(instancie(gen, _t(tX)), _t(tY)),
                               _t(ta)), _t(tb))


def _prop1_direct_tt(tU, tV):
    """⊢ Eq(U, V) ⇒ (Card U = Card V)  pour des TERMES U, V QUELCONQUES (capture-safe).

    _prop1_direct_t généralise/instancie DÉJÀ ; on garde la même robustesse pour les
    termes τ-imbriqués."""
    return _prop1_direct_t(_t(tU), _t(tV))


def _eq_sym_tt(tX, tY):
    """⊢ Eq(X, Y) ⇒ Eq(Y, X)  pour des TERMES X, Y QUELCONQUES (capture-safe).

    _eq_sym_t généralise/instancie DÉJÀ (symétrie de Eq, term-tolérante)."""
    return _eq_sym_t(_t(tX), _t(tY))


def _eq_reunion_disjointe_somme_t(ta, tb):
    """⊢ (A∩B=∅) ⇒ Eq(A∪B, A⊔B)  pour des TERMES A, B QUELCONQUES (capture-safe).

    eq_reunion_disjointe_somme bâtit la bijection-recollement W via la machinerie des
    copies marquées (liants internes « e, y, u, v, z, F, … ») : la passer DIRECTEMENT
    des termes τ-imbriqués (Im = image(τF,b), R = a∖Im) déclencherait une capture.  On
    la construit donc en NOMS SYMBOLIQUES, on GÉNÉRALISE, puis on INSTANCIE aux termes
    (renommage déterministe → robuste, comme card_egal_succ_card_diff/aleph0)."""
    base = eq_reunion_disjointe_somme("Ae13", "Be13")              # (A∩B=∅) ⇒ Eq(A∪B,A⊔B)  CLOS
    gen = N.generalisation("Ae13", N.generalisation("Be13", base))
    return instancie(instancie(gen, _t(ta)), _t(tb))


# ══════════════════════════════════════════════════════════════════════════════
#  🎯 EXISTENCE DU COMPLÉMENT CARDINAL — le cœur combinatoire de Prop. 13 direct
# ══════════════════════════════════════════════════════════════════════════════
def existe_complement_depuis_inf_egal(b="Bp13", a="Ap13", c="Cp13"):
    """⊢ ( est_cardinal(b)  et  inf_egal_card(b, a) )  ⇒  existe_complement_cardinal(b, a).

    🎯 LE CŒUR COMBINATOIRE de la Proposition 13 sens DIRECT (E.III.3.6), DÉMONTRÉ :
    construit le complément c = a ∖ f⟨b⟩ et établit Card a = b + c.  Témoin c := Card(R)
    avec R := a ∖ image(F, b), F : b ↪ a (témoin de b≤a).  Conclusion ÉGALE LITTÉRALEMENT
    existe_complement_cardinal(b, a, c).  SEULES gardes honnêtes : est_cardinal(b),
    inf_egal_card(b, a).  theorie=22, NON vacueux."""
    vb, va = _t(b), _t(a)
    cname = c if isinstance(c, str) else c.nom
    inj_F = est_injection_de(var("F"), vb, va)

    ante = et(est_cardinal(vb), inf_egal_card(vb, va))
    h = N.assume(ante)
    h_card_b = conjonction_elim_gauche(h)                          # est_cardinal(b)
    h_le = conjonction_elim_droite(h)                              # b ≤ a

    # ── témoin F de b≤a, Im := image(F,b), Im⊂a, Eq(b,Im) ────────────────────────
    wit = N.modus_ponens(h_le, N.existe_temoin(inj_F, "F"))        # est_injection_de(τF,b,a)
    Ft = tau("F", inj_F)
    Im = E.image(Ft, vb)                                           # Im = F⟨b⟩
    R = E.difference(va, Im)                                       # R = a ∖ Im  (le complément)
    cR = cardinal(R)                                              # c := Card R
    Im_sub_a = conjonction_elim_droite(wit)                        # Im ⊂ a
    eq_b_Im = N.modus_ponens(wit, injection_donne_equipotent_image(Ft, vb, va))  # Eq(b, Im)

    # ── Card Im = b ──────────────────────────────────────────────────────────────
    eq_Im_b = N.modus_ponens(eq_b_Im, _eq_sym_t(vb, Im))          # Eq(Im, b)
    cardIm_eq_cardb = N.modus_ponens(eq_Im_b, _prop1_direct_t(Im, vb))   # Card Im = Card b
    cardb_eq_b = N.modus_ponens(h_card_b, _cardinal_est_son_cardinal_t(vb))   # Card b = b
    cardIm_eq_b = composer_egalites(cardIm_eq_cardb, cardb_eq_b)  # Card Im = b

    # ── Eq(a, Im ⊔ R) ⇒ Card a = Card(Im ⊔ R) ────────────────────────────────────
    ImR = E.reunion(Im, R)                                        # Im ∪ R
    ImsR = somme_disjointe(Im, R)                                 # Im ⊔ R
    # Im ∪ R = a  (partie_reunion_complement sous Im⊂a)
    ImR_eq_a = N.modus_ponens(Im_sub_a, _partie_reunion_complement_t(va, Im))   # Im∪R = a
    # Im ∩ R = ∅
    disj = _partie_disjoint_complement_t(va, Im)                  # Im∩R = ∅
    # Eq(Im∪R, Im⊔R)  (CLOS, Prop. 10 §II.4)
    eq_union_somme = N.modus_ponens(disj, _eq_reunion_disjointe_somme_t(Im, R))  # Eq(Im∪R, Im⊔R)
    # réécrire Im∪R ↦ a  ⇒  Eq(a, Im⊔R)
    eq_a_somme = N.modus_ponens(eq_union_somme, equivalence_avant(N.modus_ponens(
        ImR_eq_a, N.s6(ImR, va, "w13", equipotent(var("w13"), ImsR)))))   # Eq(a, Im⊔R)
    carda_eq_cardsomme = N.modus_ponens(eq_a_somme, _prop1_direct_t(va, ImsR))   # Card a = Card(Im⊔R)

    # ── Card(Im ⊔ R) = somme_cardinale_binaire(b, Card R) ─────────────────────────
    # somme_disjointe_cardinal(Im, R, b, Card R) : (Card Im=b et Card R=Card R) ⇒ Card(Im⊔R)=b+CardR
    sdc = _somme_disjointe_cardinal_t(Im, R, vb, cR)
    cardR_refl = N.reflexivite(cR)                               # Card R = Card R
    cardsomme_eq = N.modus_ponens(conjonction_intro(cardIm_eq_b, cardR_refl), sdc)  # Card(Im⊔R)=b+CardR

    # ── Card a = somme_cardinale_binaire(b, Card R) ───────────────────────────────
    bcR = somme_cardinale_binaire(vb, cR)                        # b + Card R
    carda_eq_bcR = composer_egalites(carda_eq_cardsomme, cardsomme_eq)   # Card a = b + Card R
    assert carda_eq_bcR.conclusion == egal(cardinal(va), bcR), \
        "existe_complement : Card a = b + Card R mal formé"

    # ── (∃c) Card a = somme_cardinale_binaire(b, c) ──────────────────────────────
    cible_body = egal(cardinal(va), somme_cardinale_binaire(vb, var(cname)))
    ex = N.modus_ponens(carda_eq_bcR, N.s5(cible_body, cR, cname))   # (∃c) Card a = b + c
    assert ex.conclusion == existe_complement_cardinal(b, a, c), \
        "existe_complement : conclusion ≠ existe_complement_cardinal(b, a)"
    return N.loi_deduction(ante, ex)   # (est_cardinal(b) et b≤a) ⇒ existe_complement_cardinal(b,a)


def existe_complement_depuis_inf_egal_cible(b="Bp13", a="Ap13", c="Cp13"):
    """ÉNONCÉ-cible (test miroir) de existe_complement_depuis_inf_egal."""
    vb, va = _t(b), _t(a)
    return impl(et(est_cardinal(vb), inf_egal_card(vb, va)),
                existe_complement_cardinal(b, a, c))


# ══════════════════════════════════════════════════════════════════════════════
#  🎯🎯 PROPOSITION 13 sens DIRECT — FERMÉE (report déchargé)
# ══════════════════════════════════════════════════════════════════════════════
def prop13_forward_ferme(b="Bp13", a="Ap13", c="Cp13"):
    """⊢ ( est_cardinal(a)  et  est_cardinal(b)  et  inf_egal_card(b, a) )  ⇒  (∃c) a = b + c.

    🎯🎯 PROPOSITION 13 §III.3.6 sens DIRECT, RÉSIDU `existe_complement_cardinal`
    DÉCHARGÉ.  On DÉRIVE le complément cardinal (existe_complement_depuis_inf_egal,
    sous est_cardinal(b) + b≤a) et on l'INJECTE dans prop13_forward_conditionnel (qui
    montre que ce report SUFFIT, sous est_cardinal(a)).  La SEULE hypothèse survivante
    est la garde HONNÊTE « a, b cardinaux et b ≤ a » (l'antécédent du Théorème 1).

    ⚠ Le conjoint « a est un cardinal » est porté avec le binder « Xa » exigé par
    prop13_forward_conditionnel (qui écrit est_cardinal(a) = (∃Xa) a=Card Xa) ; on aligne
    donc notre antécédent dessus.  theorie=22, NON vacueux."""
    vb, va = _t(b), _t(a)
    est_card_a_Xa = existe("Xa", egal(va, cardinal(var("Xa"))))     # est_cardinal(a) binder « Xa »

    ante = et(et(est_card_a_Xa, est_cardinal(vb)), inf_egal_card(vb, va))
    h = N.assume(ante)
    h_card_a = conjonction_elim_gauche(conjonction_elim_gauche(h))   # est_cardinal(a)  [Xa]
    h_card_b = conjonction_elim_droite(conjonction_elim_gauche(h))   # est_cardinal(b)
    h_le = conjonction_elim_droite(h)                               # b ≤ a

    # complément cardinal (report) DÉRIVÉ
    comp = N.modus_ponens(conjonction_intro(h_card_b, h_le),
                          existe_complement_depuis_inf_egal(b, a, c))   # existe_complement_cardinal(b,a)

    # prop13_forward_conditionnel : (est_cardinal(a) et existe_complement_cardinal(b,a)) ⇒ (∃c)a=b+c
    cond = prop13_forward_conditionnel(b, a, c)
    res = N.modus_ponens(conjonction_intro(h_card_a, comp), cond)   # (∃c) a = b + c
    return N.loi_deduction(ante, res)


def prop13_forward_ferme_cible(b="Bp13", a="Ap13", c="Cp13"):
    """ÉNONCÉ-cible (test miroir) de prop13_forward_ferme."""
    vb, va = _t(b), _t(a)
    cname = c if isinstance(c, str) else c.nom
    est_card_a_Xa = existe("Xa", egal(va, cardinal(var("Xa"))))     # binder « Xa » (prop13_forward_conditionnel)
    but = existe(cname, egal(va, somme_cardinale_binaire(vb, var(cname))))
    return impl(et(et(est_card_a_Xa, est_cardinal(vb)), inf_egal_card(vb, va)), but)


__all__ = [
    "existe_complement_depuis_inf_egal", "existe_complement_depuis_inf_egal_cible",
    "prop13_forward_ferme", "prop13_forward_ferme_cible",
]
