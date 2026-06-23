"""Tests §III.3.4 — Proposition 8, CAS 2 par TRANSPOSITION + COMPOSITION.

On vérifie la route élégante qui RAMÈNE le CAS 2 au CAS 1 (déjà clos) par
composition avec une transposition τ de B⊔{∅} ramenant h(*) sur le marqueur * :
h₂ = τ∘h est une bijection qui FIXE *, donc en CAS 1.  On certifie l'assemblage
COMPLET modulo la SEULE brique concrète d'existence de la transposition HT_glob :

    ⊢ HT_glob(A,B) ⇒ ((successeur(A)=successeur(B)) ⇒ (Card A = Card B)),

où HT_glob(A,B) := (∀h)(∃τ)(bij(τ,B⊔{∅},B⊔{∅}) et τ(h(*))=*).  La construction
concrète de τ (échange ponctuel dans B⊔{∅}) reste à fournir.
"""
from bourbaki.logique.i_1_termes_relations.formule import var, egal, et, impl, appartient, afficher_f
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.cardinaux.ensembles_cardinaux import est_bijection_de, equipotent, cardinal
from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers import ensembles_entiers as Ent
from bourbaki.cardinaux.arithmetique import ensembles_prop8_transposition as T
from bourbaki.cardinaux.arithmetique.ensembles_prop8_assemblage import (
    cas2_hypothese, prop8_successeur_injectif_mod_cas2)


_STAR = E.couple(E.VIDE, T.UN)            # * = (∅, 1)


def _hstar(h="h"):
    return E.valeur(var(h), _STAR)        # h(*)


# ── briques term-tolérantes (composée bijective / CAS 1 sur termes) ────────────
def test_composee_bijection_t_clos():
    """⊢ (bij(h,A⊔{∅},B⊔{∅}) et bij(τ,B⊔{∅},B⊔{∅})) ⇒ bij(τ∘h,A⊔{∅},B⊔{∅}), CLOS."""
    AS, BS = T._AS("A"), T._BS("B")
    t = T._composee_bijection_t("h", "tau", AS, BS, BS)
    comp = E.composee(var("tau"), var("h"))
    expect = impl(et(est_bijection_de(var("h"), AS, BS),
                     est_bijection_de(var("tau"), BS, BS)),
                  est_bijection_de(comp, AS, BS))
    assert t.conclusion == expect
    assert t.est_clos


def test_cas1_t_clos():
    """⊢ bij(τ∘h,A⊔{∅},B⊔{∅}) ⇒ ((τ∘h)(*)=* ⇒ Eq(A,B)), CLOS  (CAS 1, version TERME)."""
    comp = E.composee(var("tau"), var("h"))
    t = T._cas1_t("A", "B", comp)
    AS, BS = T._AS("A"), T._BS("B")
    expect = impl(est_bijection_de(comp, AS, BS),
                  impl(egal(E.valeur(comp, _STAR), _STAR),
                       equipotent(var("A"), var("B"))))
    assert t.conclusion == expect
    assert t.est_clos


def test_eq_implique_eq_copies_gauches_clos():
    """⊢ Eq(A,B) ⇒ Eq(A×{0},B×{0}), CLOS  (sens facile, réciproque du transport)."""
    t = T._eq_implique_eq_copies_gauches("A", "B")
    expect = impl(equipotent(var("A"), var("B")),
                  equipotent(T._A0("A"), T._B0("B")))
    assert t.conclusion == expect
    assert t.est_clos


# ── h₂ = τ∘h fixe le marqueur ──────────────────────────────────────────────────
def test_h2_fixe_le_marqueur():
    """{bij(h,·), bij(τ,·), τ(h(*))=*} ⊢ (τ∘h)(*) = *.

    h₂ = τ∘h ramène * sur lui-même : (τ∘h)(*) = τ(h(*)) = * (composition_valeur + HT)."""
    AS, BS = T._AS("A"), T._BS("B")
    comp = E.composee(var("tau"), var("h"))
    t = T.h2_fixe_le_marqueur("A", "B", "h", "tau")
    assert t.conclusion == egal(E.valeur(comp, _STAR), _STAR)
    expect_hyps = {
        est_bijection_de(var("h"), AS, BS),
        est_bijection_de(var("tau"), BS, BS),
        egal(E.valeur(var("tau"), _hstar()), _STAR),
    }
    assert set(t.hypotheses) == expect_hyps


# ── CŒUR du CAS 2 : Eq(A,B) par réduction au CAS 1 ────────────────────────────
def test_h2_cas1_eq():
    """{bij(h,·), bij(τ,·), τ(h(*))=*} ⊢ Eq(A, B).

    Le CŒUR : composee_bijection donne bij(τ∘h), h2_fixe_le_marqueur donne
    (τ∘h)(*)=*, CAS 1 (clos) conclut Eq(A,B).  CAS 2 RAMENÉ au CAS 1."""
    AS, BS = T._AS("A"), T._BS("B")
    t = T.h2_cas1_eq("A", "B", "h", "tau")
    assert t.conclusion == equipotent(var("A"), var("B"))
    expect_hyps = {
        est_bijection_de(var("h"), AS, BS),
        est_bijection_de(var("tau"), BS, BS),
        egal(E.valeur(var("tau"), _hstar()), _STAR),
    }
    assert set(t.hypotheses) == expect_hyps


# ── CAS 2 sous l'hypothèse existentielle de transposition HT(B,h(*)) ──────────
def test_transposition_hypothese_formule():
    """HT(B,c₀) = (∃τ)(bij(τ,B⊔{∅},B⊔{∅}) et τ(c₀)=*)  (énoncé exact de la brique)."""
    from bourbaki.logique.i_1_termes_relations.formule import existe
    c0 = var("c0")
    BS = T._BS("B")
    f = T.transposition_hypothese("B", c0, "tau")
    expect = existe("tau", et(est_bijection_de(var("tau"), BS, BS),
                              egal(E.valeur(var("tau"), c0), _STAR)))
    assert f == expect


def test_cas2_via_transposition():
    """{HT(B,h(*))} ⊢ (bij(h,A⊔{∅},B⊔{∅}) et h(*)∈B×{0}) ⇒ Eq(A×{0}, B×{0}).

    Le CŒUR du CAS 2 sous la SEULE hypothèse de transposition (forme « copies de
    gauche » exigée par H2)."""
    AS, BS = T._AS("A"), T._BS("B")
    A0, B0 = T._A0("A"), T._B0("B")
    t = T.cas2_via_transposition("A", "B", "h", "tau")
    hstar = _hstar()
    expect_concl = impl(et(est_bijection_de(var("h"), AS, BS), appartient(hstar, B0)),
                        equipotent(A0, B0))
    assert t.conclusion == expect_concl
    assert set(t.hypotheses) == {T.transposition_hypothese("B", hstar, "tau")}


# ── H2 (CAS 2) à partir de l'hypothèse globale de transposition ───────────────
def test_transposition_globale_formule():
    """HT_glob(A,B) = (∀h)(∃τ)(bij(τ,B⊔{∅},B⊔{∅}) et τ(h(*))=*)  (énoncé exact)."""
    from bourbaki.logique.i_1_termes_relations.formule import pourtout
    f = T.transposition_globale("A", "B", "h", "tau")
    expect = pourtout("h", T.transposition_hypothese("B", _hstar(), "tau"))
    assert f == expect


def test_h2_de_transposition_globale():
    """⊢ HT_glob(A,B) ⇒ H2(A,B), CLOS  (la transposition globale fournit le CAS 2)."""
    t = T.h2_de_transposition_globale("A", "B", "h", "tau")
    HTg = T.transposition_globale("A", "B", "h", "tau")
    H2 = cas2_hypothese("A", "B", "h")
    assert t.conclusion == impl(HTg, H2)
    assert t.est_clos


# ── PROPOSITION 8 modulo la SEULE transposition (le JALON conditionnel) ───────
def test_prop8_via_transposition_mod_HT():
    """⊢ HT_glob(A,B) ⇒ ((successeur(A)=successeur(B)) ⇒ (Card A = Card B)), CLOS.

    La PROPOSITION 8 assemblée modulo la SEULE brique concrète de transposition.
    Finir la Proposition 8 inconditionnellement ne demande plus QUE la construction
    d'une transposition τ : B⊔{∅}→B⊔{∅} bijective avec τ(h(*))=* (échange ponctuel)."""
    p = T.prop8_via_transposition_mod_HT("A", "B", "h", "tau")
    HTg = T.transposition_globale("A", "B", "h", "tau")
    inner = impl(egal(Ent.successeur(var("A")), Ent.successeur(var("B"))),
                 egal(cardinal(var("A")), cardinal(var("B"))))
    assert p.conclusion == impl(HTg, inner)
    assert p.est_clos


def test_coherence_avec_mod_cas2():
    """Cohérence : la même conclusion interne (succ=succ ⇒ Card=Card) que la voie
    H2 (prop8_successeur_injectif_mod_cas2), confirmant que la transposition fournit
    bien H2."""
    inner = impl(egal(Ent.successeur(var("A")), Ent.successeur(var("B"))),
                 egal(cardinal(var("A")), cardinal(var("B"))))
    pc2 = prop8_successeur_injectif_mod_cas2("A", "B", "h")
    assert pc2.conclusion == impl(cas2_hypothese("A", "B", "h"), inner)
    # et la voie transposition donne la MÊME conclusion interne (inner) sous HT_glob
    p = T.prop8_via_transposition_mod_HT("A", "B", "h", "tau")
    HTg = T.transposition_globale("A", "B", "h", "tau")
    assert p.conclusion == impl(HTg, inner)
