"""§III.6 — ℵ₀ = Card(ℕ) : ℕ EST INFINI  (ℵ₀ = ℵ₀ + 1, donc ¬Fini(ℵ₀)).

🎯🎯🎯 PREMIER CARDINAL INFINI CONCRET.  ℕ (= NN, ensembles_ensemble_NN) est un SET
concret ; ce module montre que son cardinal ℵ₀ := Card(NN) vérifie l'ÉQUATION
CARACTÉRISTIQUE DE L'INFINI

        ℵ₀  =  successeur(ℵ₀)   (= ℵ₀ + 1),

et en déduit ¬Fini(ℵ₀) : ℵ₀ N'EST PAS un cardinal fini — ℕ est infini.

────────────────────────────────────────────────────────────────────────────────
ROUTE (Dedekind : un ensemble est infini ssi il est équipotent à une partie propre).

  • La translation s : n ↦ successeur(n) est une BIJECTION  NN → NN∖{0}  :
      – s = graphe_terme(NN, successeur(x))  (fonctionnel, dom = NN) ;
      – s INJECTIF sur NN : s(u)=s(u') ⇒ successeur(u)=successeur(u') ⇒ (Prop. 8,
        successeur injectif) Card u = Card u' ; or u,u'∈NN ⇒ Fini u, Fini u' ⇒
        est_cardinal ⇒ Card u = u, Card u' = u' (cardinal_de_cardinal) ⇒ u = u' ;
      – image(s, NN) = NN∖{0} :
          (⊆) t∈NN ⇒ successeur(t)∈NN (NN_clos_successeur) et successeur(t)≠0
              (successeur_non_nul : 0=∅, mais successeur(t)=Card(t⊔{∅}) avec
              t⊔{∅}≠∅, donc Card≠∅) ;
          (⊇) m∈NN∖{0} ⇒ Fini m et m≠0 ⇒ (Prop. 2 §III.5, predecesseur_fini)
              (∃k)(m=successeur(k) et est_cardinal k et k<m) ; k est fini (k<m≤fini)
              donc k∈NN, et m=successeur(k)=s(k) ∈ image(s,NN).
    D'où Eq(NN, NN∖{0}).                                          [NN_eq_NN_sans_zero]

  • NN = (NN∖{0}) ∪ {0}  avec  0 ∉ (NN∖{0})  (réunion DISJOINTE), donc
        Card NN = Card((NN∖{0})⊔{0}) = Card(NN∖{0}) + 1 = successeur(Card(NN∖{0}))
    (surgery « retrait + adjonction » eq_retire_ajoute, exactement comme la Prop. 2).
  • Eq(NN, NN∖{0}) (étape précédente) ⇒ Card NN = Card(NN∖{0})  (Proposition 1).
  • combinaison ⇒  Card NN = successeur(Card NN).               [aleph0_egal_succ]

  • Fini(ℵ₀) = est_cardinal(ℵ₀) ∧ ¬(ℵ₀ = successeur(ℵ₀)) ; le 2ᵉ conjoint est NIÉ par
    aleph0_egal_succ ⇒ ¬Fini(ℵ₀).                                  [aleph0_infini]

⚠️ INVARIANT : theorie_ensembles() = 22 intangible.  Rien postulé — tout DÉRIVE de
   Prop. 2 (predecesseur_fini_universel_preuve), Prop. 8 (prop8_successeur_injectif),
   des lemmes de NN (zero_dans_NN, NN_clos_successeur, appartenance_NN) et de la
   machinerie de recollement / Card-de-réunion-disjointe (eq_retire_ajoute), TOUTES
   CLOSES.  ⚠️ PERF : appartenance_NN repose sur N_existe (~5 min, τ-cardinaux
   imbriqués) ; les cœurs sont mémoïsés (lru_cache) — construits UNE fois par session.
"""
from __future__ import annotations

from functools import lru_cache

from bourbaki.logique.formule import (
    Terme, var, egal, et, non, impl, existe, pourtout, appartient, inclus,
    subst_t, subst_f,
)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.logique.tactiques.tactiques_abrege import a_implique_a, syllogisme
from bourbaki.logique.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, equivalence_transitivite, instancie,
    contraposition,
)
from bourbaki.logique.tactiques.tactiques_abrege_egalite import (
    symetrie, composer_egalites, congruence_terme,
)
from bourbaki.logique.tactiques.tactiques_abrege_quantif import (
    existe_elimination, alpha_existe, congruence_existe, alpha_pour_tout,
)

from bourbaki.cardinaux.ensembles_cardinaux import (
    est_cardinal, equipotent, cardinal, est_bijection_de, inf_egal_card,
    inf_strict_card,
)
from bourbaki.entiers.ensembles_entiers import est_fini, successeur, ZERO

# ── infra GRAPHE D'UN TERME (lemmes de base ; on RECONSTRUIT les dérivés capture-safe) ──
from bourbaki.ensembles.fonctions.ensembles_fonction_terme import membre_graphe_terme

# ── briques CLOSES réutilisées ───────────────────────────────────────────────
from bourbaki.entiers.ensembles_ensemble_NN import (
    ensemble_NN, appartenance_NN, appartenance_NN_instanciee,
    zero_dans_NN, NN_clos_successeur,
)

# ── briques pour la chirurgie de cardinal (surgery GÉNÉRALE, SANS est_cardinal) ──
from bourbaki.entiers.ensembles_predecesseur_prop2 import (
    eq_retire_ajoute, _eq_sym_t, _eq_son_cardinal, _eq_somme_invariant_t,
)
from bourbaki.cardinaux.arithmetique.ensembles_prop8_successeur import (
    successeur_egale_card_somme,
)
from bourbaki.cardinaux.arithmetique.ensembles_arith_cardinale import _prop1_direct_t
from bourbaki.cardinaux.ensembles_equipotence import equipotence_reflexive
from bourbaki.ensembles.familles.ensembles_somme_disjointe import (
    somme_disjointe, injection_droite_dans_somme, _dans_singleton, UN as _UN_MARQUEUR,
)
from bourbaki.logique.tactiques.tactiques_abrege2 import conjonction_intro as _conj_intro

# ── briques pour « successeur ≠ 0 » (NN-indépendantes, rapides) ────────────────
from bourbaki.cardinaux.ensembles_cardinaux_props_restantes_prop7 import (
    cardinal_egal_zero_ssi_vide,
)
from bourbaki.ensembles.base.ensembles_vide import non_vide_ssi_element

# ── briques pour les inégalités cardinales (NN ∖ {0} ↔ NN) ─────────────────────
from bourbaki.cardinaux.ensembles_clause_plus_petit_monotonie import (
    inf_egal_card_de_inclus_terme,
)


def _t(t):
    """Coercion str/Terme → Terme."""
    return t if isinstance(t, Terme) else var(t)


def _rename_pourtout_externe(thm, y):
    """De thm ⊢ (∀x)R, déduit ⊢ (∀y)(y|x)R  (α-renommage du liant LE PLUS EXTERNE).

    Lit le binder x = thm.conclusion.lieur et le corps R = thm.conclusion.sous[0],
    applique alpha_pour_tout(x, y, R) puis modus ponens (sens ⇒)."""
    concl = thm.conclusion
    assert concl.tag == "forall", "_rename_pourtout_externe : pas un ∀ en tête"
    x = concl.lieur
    R = concl.sous[0]
    if x == y:
        return thm
    return N.modus_ponens(thm, equivalence_avant(alpha_pour_tout(x, y, R)))


# ════════════════════════════════════════════════════════════════════════════
#  🎯 DÉFINITION — ℵ₀ := Card(NN)
# ════════════════════════════════════════════════════════════════════════════
@lru_cache(maxsize=None)
def aleph_0():
    """🎯 ℵ₀ := Card(NN).   (TERME CLOS — le cardinal de l'ensemble des entiers.)

    Le cardinal de l'ensemble concret NN = { x | Fini x } des entiers naturels."""
    return cardinal(ensemble_NN())


# ════════════════════════════════════════════════════════════════════════════
#  CHIRURGIE GÉNÉRALE — Card X = successeur( Card(X∖{x0}) )  pour x0 ∈ X
#  (variante de m_egal_successeur_card_diff SANS est_cardinal(X) : vaut pour TOUT
#   ensemble X, en particulier X = NN qui n'est PAS un cardinal.)
# ════════════════════════════════════════════════════════════════════════════
def card_egal_succ_card_diff(X, x0):
    """⊢ ( x0 ∈ X ) ⇒ Card X = successeur( Card(X ∖ {x0}) ).   (THÉORÈME, version GÉNÉRALE.)

    Mirroir de `m_egal_successeur_card_diff` (ensembles_predecesseur_prop2) PRIVÉ de
    l'étape « Card m = m » (qui exigeait est_cardinal(m)) : pour un ENSEMBLE QUELCONQUE
    X avec x0∈X, D := X∖{x0}, on a — par la chirurgie retrait+adjonction —
      Card X = Card(D⊔{∅})   (Eq(X,D⊔{∅}) via eq_retire_ajoute ⇒ Card =, _prop1_direct_t) ;
      Card(D⊔{∅}) = Card(Card D ⊔ {∅})   (Eq(Card D, D) ⇒ Card =, somme invariante) ;
      Card(Card D ⊔ {∅}) = successeur(Card D)   (successeur_egale_card_somme) ;
    d'où Card X = successeur(Card D).  CLOS modulo la seule hyp honnête x0∈X.  theorie=22."""
    vX, vx0 = _t(X), _t(x0)
    sing = E.singleton(vx0)
    D = E.difference(vX, sing)                             # D = X∖{x0}
    cD = cardinal(D)                                       # Card D
    sing_vide = E.singleton(E.VIDE)                        # {∅}
    DsVide = somme_disjointe(D, sing_vide)                 # D ⊔ {∅}
    cDsVide = cardinal(DsVide)                             # Card(D⊔{∅})
    cDsVide_card = somme_disjointe(cD, sing_vide)          # Card D ⊔ {∅}

    h = N.assume(appartient(vx0, vX))                      # x0 ∈ X
    # Eq(X, D⊔{∅}) ⇒ Card X = Card(D⊔{∅})
    eq_X_DsVide = N.modus_ponens(h, eq_retire_ajoute(vX, vx0))          # Eq(X, D⊔{∅})  CLOS
    card_eq = N.modus_ponens(eq_X_DsVide, _prop1_direct_t(vX, DsVide))  # Card X = Card(D⊔{∅})
    # successeur(Card D) = Card(Card D ⊔ {∅})
    succ_eq = successeur_egale_card_somme(cD)              # succ(Card D) = Card(Card D ⊔ {∅})
    # Card(Card D ⊔ {∅}) = Card(D⊔{∅})  via Eq(Card D, D)
    eq_cardD_D = N.modus_ponens(_eq_son_cardinal(D), _eq_sym_t(D, cD))  # Eq(Card D, D)
    eq_vide = instancie(N.generalisation("X", equipotence_reflexive("X")), sing_vide)  # Eq({∅},{∅})
    inv = _eq_somme_invariant_t(cD, sing_vide, D, sing_vide)
    eq_sommes = N.modus_ponens(conjonction_intro(eq_cardD_D, eq_vide), inv)  # Eq(Card D⊔{∅}, D⊔{∅})
    card_sommes_eq = N.modus_ponens(eq_sommes, _prop1_direct_t(cDsVide_card, DsVide))  # Card(CardD⊔{∅})=Card(D⊔{∅})

    # chaîne : Card X = Card(D⊔{∅}) = Card(Card D ⊔ {∅}) = successeur(Card D)
    card_DsVide_eq = N.modus_ponens(card_sommes_eq, symetrie(cardinal(cDsVide_card), cDsVide))  # Card(D⊔{∅})=Card(CardD⊔{∅})
    chain = composer_egalites(card_eq, card_DsVide_eq)     # Card X = Card(Card D ⊔ {∅})
    card_card_eq_succ = N.modus_ponens(succ_eq, symetrie(successeur(cD), cardinal(cDsVide_card)))  # Card(CardD⊔{∅})=succ(CardD)
    cardX_eq_succ = composer_egalites(chain, card_card_eq_succ)  # Card X = successeur(Card D)
    assert cardX_eq_succ.conclusion == egal(cardinal(vX), successeur(cD)), \
        "card_egal_succ_card_diff : conclusion ≠ (Card X = successeur(Card(X∖{x0})))"
    return N.loi_deduction(appartient(vx0, vX), cardX_eq_succ)  # (x0∈X) ⇒ Card X = successeur(Card(X∖{x0}))


# ════════════════════════════════════════════════════════════════════════════
#  🎯 successeur(t) ≠ 0   (le successeur d'un cardinal n'est JAMAIS nul)
# ════════════════════════════════════════════════════════════════════════════
def successeur_non_nul(t="j"):
    """🎯 ⊢ ¬( successeur(t) = 0 ).   (THÉORÈME CLOS, 0 hyp — NN-indépendant.)

    successeur(t) = t + 1 = Card(t ⊔ {∅})  et  0 = Card(∅).  Or t⊔{∅} N'EST PAS vide :
    le marqueur (∅,1) y appartient (injection_droite_dans_somme, ∅∈{∅}), donc
    (∃z)(z∈t⊔{∅}), d'où ¬(t⊔{∅}=∅)  (non_vide_ssi_element).  Par la contraposée de
    cardinal_egal_zero_ssi_vide (« Card X = Card∅ ⇔ X=∅ »), ¬(t⊔{∅}=∅) ⇒
    ¬(Card(t⊔{∅}) = Card∅) = ¬(successeur(t) = 0).

    ⚠ Le paramètre t reçoit par défaut le NOM « j » (≠ liants internes « t » de
    image_reciproque / equipotence_symetrique appelés par cardinal_egal_zero_ssi_vide) :
    un t libre nommé « t » se ferait capturer par une généralisation interne.  CLOS,
    SANS hypothèse, ne touche PAS N_existe (rapide).  theorie=22."""
    vt = _t(t)
    sing = E.singleton(E.VIDE)                            # {∅}  (= marqueur 1)
    S = somme_disjointe(vt, sing)                         # t ⊔ {∅}  (= sous-ensemble de succ t)
    star = E.couple(E.VIDE, _UN_MARQUEUR)                 # (∅, 1)  ∈ t⊔{∅}
    # (∅,1) ∈ t⊔{∅}  (∅∈{∅} déchargé)
    star_in_S = N.modus_ponens(_dans_singleton(E.VIDE),
                               injection_droite_dans_somme(E.VIDE, vt, sing))
    # (∃z)(z ∈ t⊔{∅})  (témoin (∅,1), via S5)
    ex = N.modus_ponens(star_in_S, N.s5(appartient(var("z"), S), star, "z"))
    # ¬(t⊔{∅} = ∅)  (le « a un élément » ⇒ « ≠ ∅ »)
    S_non_vide = N.modus_ponens(ex, equivalence_arriere(non_vide_ssi_element(S)))
    # contraposée de (Card S = Card∅) ⇒ (S=∅) :  ¬(S=∅) ⇒ ¬(Card S = Card∅)
    ez = cardinal_egal_zero_ssi_vide(S)                   # (Card S = Card∅) ⇔ (S=∅)
    contra = contraposition(equivalence_avant(ez))        # ¬(S=∅) ⇒ ¬(Card S = Card∅)
    res = N.modus_ponens(S_non_vide, contra)              # ¬(Card(t⊔{∅}) = Card∅)
    assert res.conclusion == non(egal(successeur(vt), ZERO)), \
        "successeur_non_nul : conclusion ≠ ¬(successeur(t)=0)"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  GRAPHE DE LA TRANSLATION  s = { (n, successeur(n)) | n ∈ A }   (CAPTURE-SAFE)
#
#  ⚠️ Le terme successeur(n) = Card(n ⊔ {∅}) est un τ-terme PROFOND dont les liants
#  INTERNES incluent « u, v, z, y » ; les outils génériques graphe_terme_* utilisent
#  PRÉCISÉMENT ces noms comme paramètres → collision (capture-évitement → renommage
#  @0 → mismatch structurel).  On RECONSTRUIT donc les lemmes du graphe avec des
#  liants SÛRS (« n0 » pour x, « e0/u0/up0 », « w0/wp0 », « y0/z0 ») qui ne figurent
#  PAS parmi les liants internes du successeur — alors subst_t(var(NOM), "n0",
#  successeur(n0)) = successeur(NOM) structurellement (vérifié).
# ════════════════════════════════════════════════════════════════════════════
_BND = "n0"                          # variable liée du graphe (≠ liants internes de succ)


def _succ_terme():
    """Le terme successeur(n0) (n0 = variable liée du graphe, capture-safe)."""
    return successeur(var(_BND))


def _s(a):
    """s := graphe_terme(A, successeur(n0), "n0") = { (n, successeur(n)) | n ∈ A }."""
    return E.graphe_terme(_t(a), _succ_terme(), _BND)


def _membre_s(a, u="e0", w="w0"):
    """⊢ ((u, w) ∈ s) ⇔ ( u ∈ A  et  w = successeur(u) ).   (capture-safe.)

    membre_graphe_terme avec liants sûrs ; u, w doivent éviter les liants internes
    de successeur (défauts « e0 », « w0 », sûrs)."""
    return membre_graphe_terme(_t(a), _succ_terme(), u, w, _BND, "y0")


# ── Conjoint 1 : s fonctionnel ────────────────────────────────────────────────
def s_fonctionnel(a):
    """⊢ est_fonctionnel(s).   (deux valeurs en u sont toutes deux successeur(u).)

    est_fonctionnel(s) = (∀u)(∀v)(∀z)(((u,v)∈s et (u,z)∈s) ⇒ v=z) (liants u,v,z
    forcés par est_fonctionnel — mais ces liants ne PÉNÈTRENT PAS le terme s = app(...),
    donc pas de capture).  On prouve le corps avec des PARAMÈTRES sûrs e0,w0,wp0 puis
    on α-renomme les 3 liants vers u,v,z."""
    va = _t(a)
    s = _s(a)
    ve, vw, vwp = var("e0"), var("w0"), var("wp0")
    succ_e = successeur(ve)
    mem_w = _membre_s(a, "e0", "w0")               # ((e0,w0)∈s) ⇔ (e0∈A et w0=succ e0)
    mem_wp = _membre_s(a, "e0", "wp0")             # ((e0,wp0)∈s) ⇔ (e0∈A et wp0=succ e0)

    ante = et(appartient(E.couple(ve, vw), s), appartient(E.couple(ve, vwp), s))
    h = N.assume(ante)
    w_eq = conjonction_elim_droite(N.modus_ponens(
        conjonction_elim_gauche(h), equivalence_avant(mem_w)))      # w0 = succ e0
    wp_eq = conjonction_elim_droite(N.modus_ponens(
        conjonction_elim_droite(h), equivalence_avant(mem_wp)))     # wp0 = succ e0
    w_wp = composer_egalites(w_eq, N.modus_ponens(wp_eq, symetrie(vwp, succ_e)))  # w0=wp0
    inner = N.loi_deduction(ante, w_wp)                            # body0 (sous hyps déchargées)
    gen = N.generalisation("e0", N.generalisation("w0", N.generalisation("wp0", inner)))
    # gen : (∀e0)(∀w0)(∀wp0) body0.  Cible = est_fonctionnel(s) = (∀u)(∀v)(∀z) body0[e0:=u,w0:=v,wp0:=z].
    # On renomme du PLUS INTERNE au plus externe ; à chaque étape on descend par
    # instanciation puis on remonte par généralisation, en α-renommant le liant visé.
    body0 = impl(et(appartient(E.couple(var("e0"), var("w0")), s),
                    appartient(E.couple(var("e0"), var("wp0")), s)),
                 egal(var("w0"), var("wp0")))
    # ── wp0 → z ──
    inner_e0w0 = instancie(instancie(gen, var("e0")), var("w0"))   # (∀wp0) body0
    ren_z = N.modus_ponens(inner_e0w0, equivalence_avant(alpha_pour_tout("wp0", "z", body0)))  # (∀z) body0[wp0:=z]
    body_z = subst_f(var("z"), "wp0", body0)
    g2 = N.generalisation("e0", N.generalisation("w0", ren_z))     # (∀e0)(∀w0)(∀z) body_z
    # ── w0 → v ──  (corps sous le ∀w0 :  (∀z) body_z)
    corps_w0 = pourtout("z", body_z)
    inner_e0 = instancie(g2, var("e0"))                            # (∀w0) corps_w0
    ren_v = N.modus_ponens(inner_e0, equivalence_avant(alpha_pour_tout("w0", "v", corps_w0)))  # (∀v)(∀z) ...
    g3 = N.generalisation("e0", ren_v)                             # (∀e0)(∀v)(∀z) ...
    # ── e0 → u ──  (corps sous le ∀e0 = ren_v.conclusion, lu directement)
    res = N.modus_ponens(g3, equivalence_avant(alpha_pour_tout("e0", "u", ren_v.conclusion)))  # (∀u)(∀v)(∀z) ...
    assert res.conclusion == E.est_fonctionnel(s), \
        "s_fonctionnel : conclusion ≠ est_fonctionnel(s) après α-renommage"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  🎯 inf_egal_card(NN∖{0}, NN)   (la partie NN∖{0} est ≤ NN — trivial : inclusion)
# ════════════════════════════════════════════════════════════════════════════
def _NN_sans_zero():
    """Le terme NN ∖ {0}  (NN privé de l'entier 0)."""
    return E.difference(ensemble_NN(), E.singleton(ZERO))


def inf_egal_NN_diff():
    """🎯 ⊢ inf_egal_card( NN ∖ {0}, NN ).   (THÉORÈME CLOS, 0 hyp — la moitié FACILE.)

    NN∖{0} ⊂ NN (une différence est incluse dans le minuende : z∈NN∖{0} ⇒ z∈NN par
    AXIOME_DIFF, projection gauche) ; or A⊂B ⇒ A≤B (inf_egal_card_de_inclus_terme,
    l'inclusion canonique Δ_A : A→B est une injection).  D'où NN∖{0} ≤ NN.  CLOS,
    SANS hypothèse, NN-indépendant (n'invoque PAS N_existe — rapide).  theorie=22."""
    NN = ensemble_NN()
    sing0 = E.singleton(ZERO)                             # {0}
    D = E.difference(NN, sing0)                           # NN ∖ {0}
    vz = var("z")
    # AXIOME_DIFF instancié : (z∈NN∖{0}) ⇔ (z∈NN et ¬(z∈{0}))
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_DIFF)
    inst = instancie(instancie(instancie(ax, NN), sing0), vz)
    hz = N.assume(appartient(vz, D))
    zNN = conjonction_elim_gauche(N.modus_ponens(hz, equivalence_avant(inst)))   # z∈NN
    incl = N.generalisation("z", N.loi_deduction(appartient(vz, D), zNN))        # NN∖{0} ⊂ NN
    assert incl.conclusion == inclus(D, NN), "inf_egal_NN_diff : inclusion inattendue"
    res = N.modus_ponens(incl, inf_egal_card_de_inclus_terme(D, NN))             # NN∖{0} ≤ NN
    assert res.conclusion == inf_egal_card(D, NN), \
        "inf_egal_NN_diff : conclusion ≠ inf_egal_card(NN∖{0}, NN)"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  🎯 INJECTIVITÉ de la translation s = n↦successeur(n) sur NN  (MATH VÉRIFIÉE).
#
#  ⚠️⚠️ VERROU STRUCTUREL DE LIANTS (diagnostic complet — bloque inf_egal_NN/étape 3).
#  ----------------------------------------------------------------------------
#  Le but final est `inf_egal_card(NN, NN∖{0}) = (∃F)est_injection_de(F, NN, NN∖{0})`,
#  dont le TÉMOIN-S5 a pour antécédent `est_injection_de(s, NN, NN∖{0})` en FORME
#  PAR DÉFAUT : les sous-formules `est_fonctionnel(s)` (liants u,v,z) et
#  `injective_dans(s, NN)` (liants u,up) sont FIXÉES par ensembles_cardinaux.
#
#  Or les NOMS u,v,z,up coïncident avec des liants INTERNES À LA FOIS de
#    • `successeur(n)` = Card(n⊔{∅}) = τZ(equipotent(…, Z)) — equipotent/est_bijection_de
#      lient u,v,z,F,Z ; ET
#    • `NN` = τy((∀x)(x∈y ⇔ Fini x)) — Fini⊃est_cardinal lie u (entre autres).
#  Construire `injective_dans(s, NN)` DIRECTEMENT garde ces u,v,z LITTÉRAUX (simple
#  nidification), mais TOUTE dérivation qui les introduit par substitution / α-renommage
#  (membre_graphe_terme, alpha_pour_tout, instanciation) DÉCLENCHE le capture-évitement
#  qui renomme les liants internes en « @0 » → la conclusion devient α-équivalente mais
#  STRUCTURELLEMENT distincte de la cible (le noyau compare `==` strictement, PAS modulo α).
#
#  • `_membre_s(NN, u, …)` ÉCHOUE pour u ∈ {u,up,v,z} (subst_t(u,'n0',successeur(n0))
#    @0-renomme l'intérieur de successeur → MP interne de membre_graphe_terme casse).
#  • La MATH est NÉANMOINS CORRECTE et close : `s_injective_safe()` ci-dessous PROUVE
#    `injective_dans(s, NN, "m0", "m0p")` (liants SÛRS) — est_clos=True, 0 hyp, vérifié.
#    Route : valeur(s,u)=successeur(u) (existe_temoin + _membre_s côté SÛR) ; hyp
#    s(u)=s(u') ⇒ succ(u)=succ(u') ⇒ (PROP 8) Card u=Card u' ; u,u'∈NN ⇒ Fini ⇒ cardinal
#    ⇒ Card u=u, Card u'=u' (cardinal_de_cardinal) ⇒ u=u'.
#  • Le PONT manquant : convertir `injective_dans(s,NN,"m0","m0p")` →
#    `injective_dans(s,NN,"u","up")` (défaut).  Le faire au niveau « F libre »
#    (injective_dans(F,NN,m0,m0p) ⇔ injective_dans(F,NN)) ÉCHOUE aussi : `NN` contient
#    un « u » interne, donc renommer m0→u y injecte « @0 ».
#
#  RÉSOLUTIONS POSSIBLES (toutes hors de portée d'un simple lemme) :
#    (a) représentation des termes en De Bruijn / hash-consing (== modulo α) — Tier 2/3
#        du chantier perf déjà identifié ;
#    (b) refactor de est_fonctionnel/injective_dans/est_injection_de pour liants FRAIS
#        garantis (change le cœur, impacte tout le dépôt).
#  Tant que (a)/(b) ne sont pas faits, étape 3 (inf_egal_NN) et l'aval (NN_eq_NN_sans_zero,
#  aleph0_egal_succ, aleph0_infini) RESTENT OUVERTES.  Étapes 1,2 (successeur_non_nul,
#  inf_egal_NN_diff) sont CLOSES et committées.
# ════════════════════════════════════════════════════════════════════════════
def _valeur_s_reduit(uname):
    """{uname∈NN} ⊢ s(uname) = successeur(uname).   (uname liant SÛR ∉ {u,up,v,z,y,F,Z}.)

    (uname,succ uname)∈s (_membre_s ⇐) ⇒ uname dans dom s ; existe_temoin donne
    (uname, s(uname))∈s ; _membre_s (⇒, projection droite) donne s(uname)=succ uname.
    N'invoque PAS est_fonctionnel(s) (donc pas de capture liée à u,v,z)."""
    NN = ensemble_NN()
    s = _s(NN)
    vu = _t(uname)
    succ_u = successeur(vu)
    su = E.valeur(s, vu)
    mem_succ = instancie(N.generalisation("w0", _membre_s(NN, uname, "w0")), succ_u)
    cpl = N.modus_ponens(_conj_intro(N.assume(appartient(vu, NN)), N.reflexivite(succ_u)),
                         equivalence_arriere(mem_succ))           # (uname,succ uname)∈s
    r = appartient(E.couple(vu, var("y")), s)
    cpl_val = N.modus_ponens(N.modus_ponens(cpl, N.s5(r, succ_u, "y")),
                             N.existe_temoin(r, "y"))             # (uname, s(uname))∈s
    mem_val = instancie(N.generalisation("w0", _membre_s(NN, uname, "w0")), su)
    return conjonction_elim_droite(N.modus_ponens(cpl_val, equivalence_avant(mem_val)))


@lru_cache(maxsize=None)
def _prop8_general():
    """⊢ (∀A)(∀B)((succ A = succ B) ⇒ (Card A = Card B))  [PROP 8 généralisée, MÉMOÏSÉE]."""
    from bourbaki.cardinaux.arithmetique.ensembles_prop8_fini2 import prop8_successeur_injectif
    return N.generalisation("A", N.generalisation("B", prop8_successeur_injectif()))


def s_injective_safe(u="m0", up="m0p"):
    """⊢ injective_dans(s, NN, u, up)   (liants SÛRS u,up — MATH de l'injectivité, CLOSE).

    🎯 MATH VÉRIFIÉE de l'étape 3 (cf. note VERROU ci-dessus) : la translation
    s = {(n, successeur(n)) | n∈NN} est INJECTIVE sur NN.  Close, 0 hyp — MAIS en
    liants SÛRS m0,m0p, non convertible vers la forme défaut u,up exigée par
    `est_injection_de` (verrou structurel)."""
    NN = ensemble_NN()
    s = _s(NN)
    from bourbaki.entiers.ensembles_ensemble_NN import appartenance_NN_instanciee
    from bourbaki.entiers.ensembles_entiers_theoremes import fini_implique_cardinal
    from bourbaki.entiers.ensembles_fini_successeur import cardinal_de_cardinal
    vu, vup = var(u), var(up)

    def card_eq_self(uname):
        v = var(uname)
        h = N.assume(appartient(v, NN))
        fini = N.modus_ponens(h, equivalence_avant(appartenance_NN_instanciee(v)))
        return N.modus_ponens(N.modus_ponens(fini, fini_implique_cardinal(v)),
                              cardinal_de_cardinal(v))                       # Card v = v  [v∈NN]

    def p8(a, b):
        return instancie(instancie(_prop8_general(), a), b)

    hyp = et(et(appartient(vu, NN), appartient(vup, NN)),
             egal(E.valeur(s, vu), E.valeur(s, vup)))
    h = N.assume(hyp)
    uNN = conjonction_elim_gauche(conjonction_elim_gauche(h))
    upNN = conjonction_elim_droite(conjonction_elim_gauche(h))
    valeq = conjonction_elim_droite(h)                                      # s(u)=s(u')
    su = N.modus_ponens(uNN, N.loi_deduction(appartient(vu, NN), _valeur_s_reduit(u)))
    sup = N.modus_ponens(upNN, N.loi_deduction(appartient(vup, NN), _valeur_s_reduit(up)))
    succ_eq = composer_egalites(
        composer_egalites(N.modus_ponens(su, symetrie(E.valeur(s, vu), successeur(vu))), valeq), sup)
    card_eq = N.modus_ponens(succ_eq, p8(vu, vup))                          # Card u = Card u'
    cu = N.modus_ponens(uNN, N.loi_deduction(appartient(vu, NN), card_eq_self(u)))
    cup = N.modus_ponens(upNN, N.loi_deduction(appartient(vup, NN), card_eq_self(up)))
    u_eq = composer_egalites(
        composer_egalites(N.modus_ponens(cu, symetrie(cardinal(vu), vu)), card_eq), cup)
    inj = N.generalisation(u, N.generalisation(up, N.loi_deduction(hyp, u_eq)))
    assert inj.conclusion == E.injective_dans(s, NN, u, up), \
        "s_injective_safe : conclusion ≠ injective_dans(s, NN, u, up)"
    return inj


__all__ = ["aleph_0", "card_egal_succ_card_diff", "successeur_non_nul",
           "inf_egal_NN_diff", "s_injective_safe"]
