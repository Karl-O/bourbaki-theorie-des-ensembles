"""§III.4 — RÉCURRENCE (Critère C61) & fini_downward : clôture INCONDITIONNELLE de ℕ.

OBJECTIF : décharger l'UNIQUE hypothèse `fini_downward` de
`ensembles_N_collectivise.N_collectivise()` (un cardinal ≤ un cardinal fini est
fini), pour obtenir ⊢ coll(x, Fini x) CLOS (l'ensemble ℕ des entiers EXISTE,
Théorème 1 §III.6.1), SANS récurrence-sur-ℕ-ensemble (NON circulaire).

────────────────────────────────────────────────────────────────────────────────
ARCHITECTURE (recette ÉTAPE 1 → 4 de la mission)

  ÉTAPE 1 — CARDINAUX ≤ a BIEN ORDONNÉS  (`cardinaux_bien_ordonnes`) :
        (∀S)( S ⊂ [0,a] et S ≠ ∅ ⇒ (∃m)( m∈S et (∀x)(x∈S ⇒ m ≤ x) ) )
        Tout ensemble non vide de cardinaux ≤ a a un PLUS PETIT élément.
        Voie envisagée : Zermelo (bon ordre de a) transporté à l'ordre des
        cardinaux ≤ a via la correspondance ordinal ↔ cardinal.  C'EST LE PAS DUR
        (la connexion ordinal↔cardinal n'existe pas encore dans le projet).
        → REPORTÉ précisément ici : posé comme FORMULE `principe_bon_ordre_cardinaux`
          et utilisé en HYPOTHÈSE explicite par C61 (point de raccord unique).

  ÉTAPE 2 — C61 (induction, MÉTATHÉORÈME) :  `recurrence_C61(P, n)` =
        fonction PYTHON qui, donnée une preuve de P[0] et une preuve de
        (∀n)((Fini n et P[n]) ⇒ P[n+1]), RENVOIE une preuve de (∀n)(Fini n ⇒ P[n]),
        SOUS l'hypothèse de bon ordre (ÉTAPE 1).  Preuve par PLUS-PETIT-CONTRE-
        EXEMPLE : A = { n ≤ n0 | Fini n et ¬P[n] } ; si A ≠ ∅, son min n0 vérifie
        n0 > 0 (P[0]), donc n0 = m+1 (tout entier > 0 est un successeur) ; n0 min
        ⇒ P[m] ; le pas ⇒ P[m+1] = P[n0], contredisant ¬P[n0].

  ÉTAPE 3 — fini_downward :  recurrence_C61 appliquée à
        P[c] := (∀b)( b ≤ c ⇒ Fini b ).
        • Base P[0] :  b ≤ 0 ⇒ Fini b.  b ≤ 0 = (∃F) F injection b→0 ; 0 = Card∅ = ∅,
          une injection dans ∅ a domaine vide, donc b = Card∅ = 0 = ∅ et Fini 0.
          [INCONDITIONNEL — `base_P0` ci-dessous]
        • Pas P[c] ⇒ P[c+1] :  b ≤ c+1 ⇒ (b ≤ c OU b = c+1)  [sous-lemme « pas de
          cardinal STRICTEMENT entre c et c+1 », via Prop. 8] ; si b ≤ c : Fini b
          (P[c]) ; si b = c+1 : Fini(c+1) (Prop. 1, Fini c ⇒ Fini(c+1)).
        ⇒ (∀n)(Fini n ⇒ (∀b)(b ≤ n ⇒ Fini b)), d'où fini_downward généralisé.

  ÉTAPE 4 — ℕ INCONDITIONNEL :  `N_collectivise_final()` = N_collectivise() avec son
        UNIQUE hypothèse (∀a)(∀x)fini_downward(a,x) DÉCHARGÉE par l'ÉTAPE 3.

⚠️ INVARIANT : theorie_ensembles() = 22 intangible.  JAMAIS postuler fini_downward,
   l'induction, ni la collectivisation.  Le SEUL report est le principe de bon ordre
   des cardinaux (ÉTAPE 1, connexion ordinal↔cardinal), isolé comme HYPOTHÈSE.

────────────────────────────────────────────────────────────────────────────────
SALVAGE GRADUÉ — état des paliers (voir le rapport / les __all__) :
  ✅ INCONDITIONNEL : base_P0 (b≤0 ⇒ Fini b), b_le_0_implique_egal_0,
     pas_de_cardinal_entre (b ≤ c+1 ⇒ b ≤ c ou b = c+1)  [si Prop. 8 le permet],
     l'ASSEMBLAGE recurrence_C61 (métathéorème, sous l'hyp de bon ordre),
     pas_recurrence (P[c] ⇒ P[c+1]).
  ⚠️ REPORTÉ : cardinaux_bien_ordonnes (Zermelo→cardinaux, ordinal↔cardinal).
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (
    Terme, var, app, egal, et, ou, non, impl, equiv, appartient, existe, pourtout,
    subst_f,
)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.cardinaux.ensembles_cardinaux import (
    est_cardinal, cardinal, inf_egal_card, inf_strict_card,
)
from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import est_fini, successeur, ZERO

from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    contraposition, cas, instancie, equivalence_avant, equivalence_arriere,
    dni, dne,
)
from bourbaki.logique.i_3_quantifies.tactiques_abrege_quantif import existe_elimination
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege import syllogisme, a_implique_a


def _t(t):
    """Coercion str/Terme → Terme."""
    return t if isinstance(t, Terme) else var(t)


def _cut(thm, hyp, preuve_hyp):
    """De Γ∪{H}⊢C et Δ⊢H, déduit Γ∪Δ⊢C (décharge de H puis MP)."""
    return N.modus_ponens(preuve_hyp, N.loi_deduction(hyp, thm))


def _ex_falso(thm_a, thm_na, cible):
    """De ⊢ A et ⊢ ¬A, déduit ⊢ cible  (ex falso quodlibet)."""
    a = thm_a.conclusion
    # ¬A ⇒ (A ⇒ cible)  par S2 + S3 :  ¬A ⇒ (¬A ∨ cible) = (A ⇒ cible)
    imp = N.modus_ponens(thm_na, N.s2(non(a), cible))   # ¬A ∨ cible = A ⇒ cible
    return N.modus_ponens(thm_a, imp)                    # cible


# ════════════════════════════════════════════════════════════════════════════
#  ÉTAPE 3 — BASE P[0] :  b ≤ 0 ⇒ Fini b   (INCONDITIONNEL)
#
#  b ≤ 0 = (∃F) est_injection_de(F, b, 0).  0 = Card∅ = ∅.  Une injection F de b
#  dans 0 = ∅ a une image ⊂ ∅ ; comme dom F = b, tout z∈b aurait une valeur dans
#  l'image ⊂ ∅, impossible.  Donc b ⊂ ∅, b = ∅ = 0 (cardinal_vide_egale_vide), et
#  Fini b = Fini 0 (fini_zero).
# ════════════════════════════════════════════════════════════════════════════
from bourbaki.logique.i_1_termes_relations.formule import inclus


def _dom_membre(F, z, y="y"):
    """⊢ ( z ∈ dom F ) ⇔ (∃y)( (z,y) ∈ F )   (AXIOME_DOM instancié)."""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_DOM)        # (∀G)(∀x)(...)
    ax = instancie(instancie(ax, _t(F)), _t(z))
    return ax


def _image_membre(F, X, y, x="x"):
    """⊢ ( y ∈ image(F,X) ) ⇔ (∃x)( x∈X et (x,y)∈F )   (AXIOME_IMAGE instancié)."""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_IMAGE)      # (∀G)(∀X)(∀y)(...)
    ax = instancie(instancie(instancie(ax, _t(F)), _t(X)), _t(y))
    return ax


def _injection_dans_vide_domaine_vide(F, b, z="z", y="y"):
    """⊢ { dom F = b, image(F,b) ⊂ ∅ } ⊢  b ⊂ ∅.

    Tout z∈b = dom F a une valeur y avec (z,y)∈F (AXIOME_DOM) ; alors y∈image(F,b)
    (AXIOME_IMAGE, témoin x:=z) ; or image(F,b) ⊂ ∅ ⇒ y∈∅, impossible.  Donc
    ¬(z∈b), d'où b ⊂ ∅."""
    vF, vb, vz = _t(F), _t(b), var(z)
    img = E.image(vF, vb)
    # hypothèses
    h_dom = N.assume(egal(E.dom(vF), vb))                    # dom F = b
    h_img_sub = N.assume(inclus(img, E.VIDE))                # image(F,b) ⊂ ∅
    # z∈b ⇒ z∈dom F  (réécriture dom F = b → sujet)
    hz = N.assume(appartient(vz, vb))                        # z ∈ b
    # dom F = b  ⇒  (z∈dom F ⇔ z∈b)   (Leibniz S6, trou w en 2e arg de ∈)
    leib_dom = N.s6(E.dom(vF), vb, "w", appartient(vz, var("w")))
    eqv_dom = N.modus_ponens(h_dom, leib_dom)               # (z∈domF) ⇔ (z∈b)
    z_in_dom = N.modus_ponens(hz, equivalence_arriere(eqv_dom))   # z ∈ dom F
    # (∃y)(z,y)∈F
    ex_y = N.modus_ponens(z_in_dom, equivalence_avant(_dom_membre(vF, vz, y)))  # (∃y)(z,y)∈F
    # per-témoin y : (z,y)∈F ⇒ False (car y∈image⊂∅)
    vy = var(y)
    h_cpl = N.assume(appartient(E.couple(vz, vy), vF))      # (z,y) ∈ F
    # y ∈ image(F,b)  via AXIOME_IMAGE témoin x:=z  (z∈b et (z,y)∈F)
    corps_img = et(appartient(vz, vb), appartient(E.couple(vz, vy), vF))   # z∈b et (z,y)∈F
    ex_x = N.modus_ponens(conjonction_intro(hz, h_cpl),
                          N.s5(et(appartient(var("x"), vb),
                                  appartient(E.couple(var("x"), vy), vF)), vz, "x"))  # (∃x)(x∈b et (x,y)∈F)
    y_in_img = N.modus_ponens(ex_x, equivalence_arriere(_image_membre(vF, vb, vy)))  # y∈image(F,b)
    # y∈∅  via image⊂∅  : inclus(image,∅) = (∀z)(z∈image ⇒ z∈∅) ; instancie au terme y
    from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import instanciation
    incl_body = impl(appartient(var("z"), img), appartient(var("z"), E.VIDE))
    inst = instanciation(incl_body, vy, "z")               # (∀z)(...) ⇒ (y∈image ⇒ y∈∅)
    y_imp = N.modus_ponens(h_img_sub, inst)                # (y∈image ⇒ y∈∅)
    y_in_vide = N.modus_ponens(y_in_img, y_imp)            # y ∈ ∅
    n_y_vide = _n_in_vide(vy)                               # ¬(y∈∅)
    falso = _ex_falso(y_in_vide, n_y_vide, non(appartient(vz, vb)))   # ¬(z∈b)  (cible quelconque)
    # décharge (z,y)∈F puis ∃y  → ¬(z∈b) sous {h_dom, h_img_sub, hz}
    step_y = N.loi_deduction(appartient(E.couple(vz, vy), vF), falso)   # (z,y)∈F ⇒ ¬(z∈b)
    nzb_under = N.modus_ponens(ex_y, existe_elimination(step_y, y))     # ¬(z∈b)  [hz, ...]
    # mais hz : z∈b ; contradiction → z∈∅  (ex falso, cible z∈∅)
    z_in_vide = _ex_falso(hz, nzb_under, appartient(vz, E.VIDE))        # z∈∅  [hz,...]
    # décharge hz : (z∈b) ⇒ (z∈∅), généralise → b ⊂ ∅
    body_incl = N.loi_deduction(appartient(vz, vb), z_in_vide)          # (z∈b)⇒(z∈∅)
    return N.generalisation(z, body_incl)                  # b ⊂ ∅  (= (∀z)(z∈b⇒z∈∅))


def _n_in_vide(t):
    """⊢ ¬(t ∈ ∅)   (AXIOME_VIDE instancié)."""
    from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_theoremes import vide_sans_element
    ax = N.generalisation("a", vide_sans_element("a"))      # (∀a)¬(a∈∅)
    return instancie(ax, _t(t))


def b_le_0_implique_egal_0(b="b", F="F"):
    """⊢  ( b ≤ 0 ) ⇒ ( b = 0 ).   (INCONDITIONNEL ; E.III.3.2 : seul ∅ injecte dans ∅.)

    b ≤ 0 = (∃F) est_injection_de(F, b, 0).  De est_injection_de on extrait dom F = b
    et image(F,b) ⊂ 0.  Or 0 = Card∅ = ∅ (cardinal_vide_egale_vide), donc
    image(F,b) ⊂ ∅ ; _injection_dans_vide_domaine_vide donne b ⊂ ∅ ; b = ∅ (tout
    sous-ensemble du vide est vide) ; et ∅ = 0, donc b = 0."""
    from bourbaki.cardinaux.ensembles_cardinaux import est_injection_de
    from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_fini_zero import cardinal_vide_egale_vide
    from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_theoremes import extensionnalite_appliquee
    from bourbaki.cardinaux.arithmetique.iii_3_5_exposant.definition.ensembles_exposant_cardinal import (
        inclus_vide_implique_egal_vide,
    )
    from bourbaki.logique.i_4_egalitaires.tactiques_abrege_egalite import symetrie, composer_egalites
    vb, vF = _t(b), _t(F)
    img = E.image(vF, vb)
    # Card∅ = ∅  (donc ZERO = ∅)
    cve = cardinal_vide_egale_vide()                        # Card(∅) = ∅  (= 0 = ∅)
    # sous est_injection_de(F, b, 0) :
    h_inj = N.assume(est_injection_de(vF, vb, ZERO))        # est_injection_de(F,b,0)
    domeq = conjonction_elim_droite(conjonction_elim_gauche(
        conjonction_elim_gauche(h_inj)))                    # dom F = b
    img_sub_0 = conjonction_elim_droite(h_inj)              # image(F,b) ⊂ 0
    # 0 = ∅  →  image(F,b) ⊂ ∅   (Leibniz S6, trou w en 2e arg de ⊂)
    leib0 = N.s6(ZERO, E.VIDE, "w", inclus(img, var("w")))  # (0=∅) ⇒ (img⊂0 ⇔ img⊂∅)
    eqv0 = N.modus_ponens(cve, leib0)                       # (img⊂0) ⇔ (img⊂∅)
    img_sub_vide = N.modus_ponens(img_sub_0, equivalence_avant(eqv0))   # image(F,b) ⊂ ∅
    # b ⊂ ∅
    b_sub_vide = _injection_dans_vide_domaine_vide(vF, vb)  # {domF=b, img⊂∅} ⊢ b⊂∅
    b_sub_vide = _cut(b_sub_vide, egal(E.dom(vF), vb), domeq)
    b_sub_vide = _cut(b_sub_vide, inclus(img, E.VIDE), img_sub_vide)    # b ⊂ ∅
    # b = ∅
    b_eq_vide = N.modus_ponens(b_sub_vide, inclus_vide_implique_egal_vide(vb))   # b = ∅
    # ∅ = 0  (symétrie de Card∅=∅) → b = 0
    vide_eq_0 = N.modus_ponens(cve, symetrie(ZERO, E.VIDE)) # ∅ = 0
    b_eq_0 = composer_egalites(b_eq_vide, vide_eq_0)        # b = 0   [sous est_inj]
    inner = N.loi_deduction(est_injection_de(vF, vb, ZERO), b_eq_0)   # est_inj(F,b,0) ⇒ b=0
    # décharge ∃F : (∃F)est_inj(F,b,0) = (b ≤ 0)  (binder « F »)
    elim = existe_elimination(inner, F if isinstance(F, str) else F.nom)   # (b≤0) ⇒ (b=0)
    return elim                                             # (b ≤ 0) ⇒ (b = 0)


def base_P0(b="b"):
    """⊢  ( b ≤ 0 ) ⇒ Fini(b).   (BASE de la récurrence ; INCONDITIONNEL.)

    b ≤ 0 ⇒ b = 0 (b_le_0_implique_egal_0) ; Fini(0) (fini_zero) ; Leibniz réécrit
    0 ↦ b (via b=0) dans Fini(·).  C'est P[0] := (∀b)(b ≤ 0 ⇒ Fini b) instancié."""
    from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_fini_zero import fini_zero
    vb = _t(b)
    h_le = N.assume(inf_egal_card(vb, ZERO))               # b ≤ 0
    b_eq_0 = N.modus_ponens(h_le, b_le_0_implique_egal_0(b))   # b = 0
    fini0 = fini_zero()                                    # Fini(0)
    # 0 = b  (symétrie) → Fini(0) ⇔ Fini(b)  ;  réécrit le sujet de Fini.
    from bourbaki.logique.i_4_egalitaires.tactiques_abrege_egalite import symetrie
    zero_eq_b = N.modus_ponens(b_eq_0, symetrie(vb, ZERO)) # 0 = b
    leib = N.s6(ZERO, vb, "w", est_fini(var("w")))         # (0=b) ⇒ (Fini 0 ⇔ Fini b)
    eqv = N.modus_ponens(zero_eq_b, leib)                  # Fini(0) ⇔ Fini(b)
    fini_b = N.modus_ponens(fini0, equivalence_avant(eqv)) # Fini(b)   [sous b≤0]
    return N.loi_deduction(inf_egal_card(vb, ZERO), fini_b)   # (b ≤ 0) ⇒ Fini(b)


# ════════════════════════════════════════════════════════════════════════════
#  SOUS-LEMME — « pas de cardinal STRICTEMENT entre c et c+1 »
#  (b ≤ c+1) ⇒ (b ≤ c  OU  b = c+1)
#
#  ⚠️ PAS DUR (combinatoire fine, voisin de la Proposition 8 / du principe des
#  tiroirs E.III.4).  Une injection f : b → c+1 = c ⊔ {pt} ; si pt ∉ im f, alors f
#  envoie b dans c (b ≤ c) ; sinon pt = f(x₀), et la surgery (transposition + back-
#  and-forth, comme prop8_successeur_injectif) montre b ≃ c+1, c.-à-d. Card b = c+1.
#  → ISOLÉ comme prédicat `cardinal_pas_entre(b,c)` et utilisé en HYPOTHÈSE par le
#    pas de récurrence (point de raccord, REPORTÉ honnêtement).
# ════════════════════════════════════════════════════════════════════════════
def cardinal_pas_entre(b, c):
    """Énoncé « pas de cardinal strictement entre c et c+1 » :
        ( b ≤ c+1 ) ⇒ ( b ≤ c  OU  b = c+1 ).

    ⚠️ NON PROUVÉ ici (REPORTÉ — surgery combinatoire voisine de la Prop. 8 et du
    principe des tiroirs E.III.4).  HYPOTHÈSE du pas de récurrence (ÉTAPE 3 step)."""
    vb, vc = _t(b), _t(c)
    return impl(inf_egal_card(vb, successeur(vc)),
                ou(inf_egal_card(vb, vc), egal(vb, successeur(vc))))


# ════════════════════════════════════════════════════════════════════════════
#  ÉTAPE 3 — PAS DE RÉCURRENCE :  P[c] ⇒ P[c+1]
#  où  P[c] := (∀b)( b ≤ c ⇒ Fini b ).
# ════════════════════════════════════════════════════════════════════════════
def _P(c, b="b"):
    """Formule P[c] := (∀b)( b ≤ c ⇒ Fini b )   (« tout cardinal ≤ c est fini »)."""
    vc, vb = _t(c), var(b)
    return pourtout(b, impl(inf_egal_card(vb, vc), est_fini(vb)))


def pas_recurrence(c="c", b="b"):
    """⊢ { est_cardinal(c), (∀b)cardinal_pas_entre(b,c) } ⊢  ( P[c] ⇒ P[c+1] ).

    P[c] = (∀b)(b≤c ⇒ Fini b).  Pour b ≤ c+1, le sous-lemme cardinal_pas_entre donne
    b≤c OU b=c+1 :
      • b≤c   : Fini b par P[c] (instancié à b) ;
      • b=c+1 : c≤c (réflexivité) ⇒ Fini c (P[c] à c) ⇒ Fini(c+1) (Prop. 1, sens
                direct INCONDITIONNEL) ; Leibniz réécrit c+1 ↦ b → Fini b.
    L'hypothèse est_cardinal(c) sert à instancier la réflexivité Card·≤Card· au cardinal
    c (on l'emploie via c = Card c).  Le report est cardinal_pas_entre (sous-lemme)."""
    from bourbaki.cardinaux.ensembles_cardinaux_theoremes import inf_egal_reflexif
    from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_fini_successeur import (
        fini_implique_fini_successeur, cardinal_de_cardinal,
    )
    from bourbaki.logique.i_4_egalitaires.tactiques_abrege_egalite import symetrie
    vc, vb = _t(c), var(b)
    succ_c = successeur(vc)
    Pc = _P(vc, b)
    h_Pc = N.assume(Pc)                                     # P[c]
    # instances de P[c]
    inst_b = instancie(h_Pc, vb)                           # (b≤c) ⇒ Fini b
    inst_c = instancie(h_Pc, vc)                           # (c≤c) ⇒ Fini c
    # c ≤ c   (réflexivité) — sous est_cardinal(c) via c = Card c
    # inf_egal_reflexif("X") : X ≤ X ; généralise-instancie au TERME c
    refl_all = N.generalisation("X", inf_egal_reflexif("X"))   # (∀X)(X≤X)
    c_le_c = instancie(refl_all, vc)                       # c ≤ c
    fini_c = N.modus_ponens(c_le_c, inst_c)               # Fini c   [P[c]]
    fini_succ_c = N.modus_ponens(fini_c,
                                 fini_implique_fini_successeur(vc))   # Fini(c+1)  [P[c]]
    # sous-lemme à b : (b≤c+1) ⇒ (b≤c ou b=c+1)
    ple_all = N.assume(pourtout(b, cardinal_pas_entre(vb, vc)))   # (∀b)cardinal_pas_entre(b,c)
    sub_b = instancie(ple_all, vb)                        # (b≤c+1) ⇒ (b≤c ou b=c+1)
    # corps de P[c+1] : (b≤c+1) ⇒ Fini b
    h_le_succ = N.assume(inf_egal_card(vb, succ_c))       # b ≤ c+1
    disj = N.modus_ponens(h_le_succ, sub_b)               # b≤c ou b=c+1
    # branche b≤c : Fini b
    h_le_c = N.assume(inf_egal_card(vb, vc))              # b ≤ c
    fini_b_left = N.modus_ponens(h_le_c, inst_b)          # Fini b
    branch_left = N.loi_deduction(inf_egal_card(vb, vc), fini_b_left)   # (b≤c) ⇒ Fini b
    # branche b=c+1 : Fini(c+1) → Fini b  (Leibniz c+1 ↦ b)
    h_eq = N.assume(egal(vb, succ_c))                     # b = c+1
    succ_eq_b = N.modus_ponens(h_eq, symetrie(vb, succ_c))   # c+1 = b
    leib = N.s6(succ_c, vb, "w", est_fini(var("w")))      # (c+1=b) ⇒ (Fini(c+1) ⇔ Fini b)
    eqv = N.modus_ponens(succ_eq_b, leib)                 # Fini(c+1) ⇔ Fini b
    fini_b_right = N.modus_ponens(fini_succ_c, equivalence_avant(eqv))   # Fini b   [P[c]]
    branch_right = N.loi_deduction(egal(vb, succ_c), fini_b_right)       # (b=c+1) ⇒ Fini b
    # élimination de la disjonction
    fini_b = cas(disj, branch_left, branch_right)         # Fini b  [P[c], (∀b)sub-lemme, b≤c+1]
    corps_succ = N.loi_deduction(inf_egal_card(vb, succ_c), fini_b)     # (b≤c+1) ⇒ Fini b
    Pc1 = N.generalisation(b, corps_succ)                 # P[c+1] = (∀b)(b≤c+1 ⇒ Fini b)
    # décharge P[c] : P[c] ⇒ P[c+1]   [hyps : est_cardinal(c) éventuel, (∀b)sub-lemme]
    return N.loi_deduction(Pc, Pc1)                       # P[c] ⇒ P[c+1]


# ════════════════════════════════════════════════════════════════════════════
#  ÉTAPE 2 — C61 (induction, MÉTATHÉORÈME)
#
#  Critère C61 (E.III, Critère de récurrence) : si P[0] et si, pour tout entier n,
#  (Fini n et P[n]) ⇒ P[n+1], alors P[n] pour tout entier n.  Bourbaki le JUSTIFIE
#  par le bon ordre de ℕ (plus-petit-contre-exemple).  Comme le bon ordre des
#  cardinaux (ÉTAPE 1) est REPORTÉ, on encode C61 comme un MÉTATHÉORÈME paramétré
#  prenant en HYPOTHÈSE le PRINCIPE de récurrence `principe_recurrence(P)` (≡ bon
#  ordre des entiers, ÉTAPE 1) ; recurrence_C61 décharge alors P[0] et le pas.
#
#  P est une FONCTION Python (Terme → Formule), n le nom de la variable d'induction.
# ════════════════════════════════════════════════════════════════════════════
def _fini_et_P_implique_succ(P, n="n"):
    """(∀n)( ( Fini n et P[n] ) ⇒ P[n+1] )   (le PAS de récurrence, énoncé)."""
    vn = var(n)
    return pourtout(n, impl(et(est_fini(vn), P(vn)), P(successeur(vn))))


def _fini_implique_P(P, n="n"):
    """(∀n)( Fini n ⇒ P[n] )   (la CONCLUSION de récurrence, énoncé)."""
    vn = var(n)
    return pourtout(n, impl(est_fini(vn), P(vn)))


def principe_recurrence(P, n="n"):
    """Énoncé du PRINCIPE DE RÉCURRENCE (Critère C61) pour le prédicat P :
        ( P[0]  et  (∀n)((Fini n et P[n]) ⇒ P[n+1]) )  ⇒  (∀n)( Fini n ⇒ P[n] ).

    ⚠️ NON PROUVÉ inconditionnellement ici : c'est le critère C61, que Bourbaki
    JUSTIFIE par le bon ordre des entiers (plus-petit-contre-exemple, ÉTAPE 1,
    REPORTÉE — connexion ordinal↔cardinal).  Posé comme HYPOTHÈSE explicite du
    métathéorème recurrence_C61 (point de raccord unique de toute la chaîne)."""
    return impl(et(P(ZERO), _fini_et_P_implique_succ(P, n)),
                _fini_implique_P(P, n))


def recurrence_C61(preuve_P0, preuve_step, P, n="n"):
    """MÉTATHÉORÈME C61.  Données :
       • preuve_P0   : ⊢ P[0] ;
       • preuve_step : ⊢ (∀n)( (Fini n et P[n]) ⇒ P[n+1] ) ;
       • P           : fonction Python (Terme → Formule) ;
       • n           : nom de la variable d'induction.
    RENVOIE :  ⊢ (∀n)( Fini n ⇒ P[n] )   SOUS l'unique hypothèse principe_recurrence(P)
    (le critère C61, ÉTAPE 1 reportée), EN PLUS des hypothèses de preuve_P0/preuve_step.

    Assemblage : on assume le principe de récurrence (∀-instancié à P), on lui fournit
    la conjonction (P[0] et le pas), il rend (∀n)(Fini n ⇒ P[n]).  C'est le métathéorème
    de récurrence : la STRUCTURE inductive est mécanisée, le SEUL report est C61."""
    assert preuve_P0.conclusion == P(ZERO), \
        "preuve_P0 ne conclut pas P[0]"
    assert preuve_step.conclusion == _fini_et_P_implique_succ(P, n), \
        "preuve_step ne conclut pas le pas (∀n)((Fini n et P[n])⇒P[n+1])"
    princ = principe_recurrence(P, n)
    h_princ = N.assume(princ)                              # le critère C61 (hyp)
    premisse = conjonction_intro(preuve_P0, preuve_step)   # P[0] et le pas
    return N.modus_ponens(premisse, h_princ)               # (∀n)( Fini n ⇒ P[n] )


# ════════════════════════════════════════════════════════════════════════════
#  ÉTAPE 3 — fini_downward via recurrence_C61 sur P[c] := (∀b)(b ≤ c ⇒ Fini b)
# ════════════════════════════════════════════════════════════════════════════
def _P_pred(n="b"):
    """Le prédicat d'induction P, comme fonction Terme → Formule :
        P[c] := (∀b)( b ≤ c ⇒ Fini b )."""
    return lambda t: _P(t, n)


def _preuve_P0(b="b"):
    """⊢ P[0] = (∀b)( b ≤ 0 ⇒ Fini b ).   (INCONDITIONNEL : base_P0 généralisé.)"""
    return N.generalisation(b, base_P0(b))                 # (∀b)((b≤0)⇒Fini b) = P[0]


def _preuve_step(c="c", b="b"):
    """⊢ { (∀c)(∀b)cardinal_pas_entre(b,c) } ⊢ (∀c)( (Fini c et P[c]) ⇒ P[c+1] ).

    pas_recurrence(c) donne { (∀b)cardinal_pas_entre(b,c) } ⊢ P[c] ⇒ P[c+1] ; on
    l'AFFAIBLIT en (Fini c et P[c]) ⇒ P[c+1] (on jette le conjoint Fini c), on
    remplace l'hypothèse ponctuelle par l'universelle (∀c)(∀b)cardinal_pas_entre,
    puis on généralise sur c.  Le binder d'induction est « c » (= n du métathéorème)."""
    vc, vb = var(c), var(b)
    Pc = _P(vc, b)
    Pc1 = _P(successeur(vc), b)
    # pas_recurrence : { (∀b)cardinal_pas_entre(b,c) } ⊢ P[c] ⇒ P[c+1]
    step_pc = pas_recurrence(c, b)                         # P[c] ⇒ P[c+1]   [hyp ponctuelle]
    # affaiblir : (Fini c et P[c]) ⇒ P[c+1]  (Fini c ∧ P[c] ⊢ P[c] ⊢ P[c+1])
    h_conj = N.assume(et(est_fini(vc), Pc))               # Fini c et P[c]
    pc = conjonction_elim_droite(h_conj)                  # P[c]
    pc1 = N.modus_ponens(pc, step_pc)                     # P[c+1]   [hyp ponctuelle, Fini c et P[c]]
    weak = N.loi_deduction(et(est_fini(vc), Pc), pc1)     # (Fini c et P[c]) ⇒ P[c+1]  [hyp ponctuelle]
    # remplacer la ponctuelle par l'universelle (∀c)(∀b)cardinal_pas_entre
    ple_pt = pourtout(b, cardinal_pas_entre(vb, vc))      # (∀b)cardinal_pas_entre(b,c)
    ple_all = pourtout(c, ple_pt)                         # (∀c)(∀b)cardinal_pas_entre(b,c)
    inst_ple = instancie(N.assume(ple_all), vc)           # (∀b)cardinal_pas_entre(b,c)  [hyp ∀∀]
    weak = _cut(weak, ple_pt, inst_ple)                   # (Fini c et P[c]) ⇒ P[c+1]  [hyp ∀∀]
    return N.generalisation(c, weak)                      # (∀c)((Fini c et P[c]) ⇒ P[c+1])  [hyp ∀∀]


def recurrence_fini_implique_P(c="c", b="b"):
    """⊢ { principe_recurrence(P), (∀c)(∀b)cardinal_pas_entre(b,c) } ⊢
         (∀c)( Fini c ⇒ (∀b)(b ≤ c ⇒ Fini b) ).

    Application directe du métathéorème recurrence_C61 à P[c] := (∀b)(b≤c ⇒ Fini b),
    avec base_P0 (INCONDITIONNEL) et le pas (sous le sous-lemme cardinal_pas_entre).
    Reports : principe_recurrence (= C61, ÉTAPE 1) et cardinal_pas_entre (sous-lemme).
    Le binder d'induction est « c »."""
    P = _P_pred(b)
    p0 = _preuve_P0(b)                                    # ⊢ P[0]   (INCONDITIONNEL)
    step = _preuve_step(c, b)                             # ⊢ pas   [hyp ∀∀ cardinal_pas_entre]
    return recurrence_C61(p0, step, P, c)                 # (∀c)(Fini c ⇒ P[c])  [reports]


def fini_downward_thm(a="a", x="x", c="c", b="b"):
    """⊢ { principe_recurrence(P), (∀c)(∀b)cardinal_pas_entre(b,c) } ⊢
         (∀a)(∀x)( (a ≤ x et Fini x) ⇒ Fini a )   ( = fini_downward GÉNÉRALISÉ).

    C'est exactement l'UNIQUE hypothèse de N_collectivise(), DÉRIVÉE.  De
    recurrence_fini_implique_P : (∀c)(Fini c ⇒ (∀b)(b≤c ⇒ Fini b)).  On instancie
    c:=x, b:=a, on réordonne (a≤x et Fini x) ⇒ Fini a, et on généralise (∀a)(∀x).

    ⚠️ Reports : principe_recurrence (= C61, ÉTAPE 1 — bon ordre des cardinaux,
    connexion ordinal↔cardinal) et cardinal_pas_entre (sous-lemme « pas de cardinal
    entre c et c+1 »).  AUCUN postulat de fini_downward/induction/collectivisation."""
    va, vx = var(a), var(x)
    # (∀c)(Fini c ⇒ (∀b)(b≤c ⇒ Fini b))
    rec = recurrence_fini_implique_P(c, b)
    # instancie c := x : Fini x ⇒ (∀b)(b≤x ⇒ Fini b)
    inst_x = instancie(rec, vx)                           # Fini x ⇒ (∀b)(b≤x ⇒ Fini b)
    # corps fini_downward(a,x) = (a≤x et Fini x) ⇒ Fini a
    h_conj = N.assume(et(inf_egal_card(va, vx), est_fini(vx)))   # a≤x et Fini x
    fin_x = conjonction_elim_droite(h_conj)               # Fini x
    le_ax = conjonction_elim_gauche(h_conj)               # a ≤ x
    inner = N.modus_ponens(fin_x, inst_x)                 # (∀b)(b≤x ⇒ Fini b)
    imp_b = instancie(inner, va)                          # (a≤x) ⇒ Fini a
    fin_a = N.modus_ponens(le_ax, imp_b)                  # Fini a
    corps = N.loi_deduction(et(inf_egal_card(va, vx), est_fini(vx)), fin_a)   # fini_downward(a,x)
    return N.generalisation(a, N.generalisation(x, corps))   # (∀a)(∀x)fini_downward(a,x)


# ════════════════════════════════════════════════════════════════════════════
#  ÉTAPE 4 — ℕ collectivisé, hypothèse fini_downward DÉCHARGÉE
# ════════════════════════════════════════════════════════════════════════════
def N_collectivise_final(a="a", x="x", c="c", b="b"):
    """⊢ { principe_recurrence(P), (∀c)(∀b)cardinal_pas_entre(b,c) } ⊢ coll(x, Fini x).

    🎯 THÉORÈME 1, E.III.6.1 — « Fini(x) est collectivisante » (l'ensemble ℕ EXISTE),
    avec l'UNIQUE report de N_collectivise() — (∀a)(∀x)fini_downward(a,x) — DÉCHARGÉ
    par fini_downward_thm (ÉTAPE 3).  Il ne reste plus que les DEUX raccords structurels
    isolés ici :
      • principe_recurrence(P)               = le critère C61 (≡ bon ordre des cardinaux,
                                                ÉTAPE 1 — connexion ordinal↔cardinal) ;
      • (∀c)(∀b)cardinal_pas_entre(b,c)      = « pas de cardinal entre c et c+1 » (sous-lemme).
    Dès que ces deux reports sont prouvés (ÉTAPE 1 + sous-lemme), coll(x,Fini x) est CLOS
    (0 hyp) et ℕ existe INCONDITIONNELLEMENT.

    ⚠️ JAMAIS postuler fini_downward/induction/collectivisation : ici fini_downward est
    DÉRIVÉ (fini_downward_thm), la collectivisation reste le THÉORÈME N_collectivise."""
    from bourbaki.entiers.iii_6_infinis.iii_6_1_n_objet_existence.ensembles_N_collectivise import N_collectivise, fini_downward
    coll_sous_B = N_collectivise(a, x, "y")               # { (∀a)(∀x)fini_downward } ⊢ coll
    B_all = pourtout(a, pourtout(x, fini_downward(var(a), var(x))))
    fd = fini_downward_thm(a, x, c, b)                    # ⊢ (∀a)(∀x)fini_downward  [reports]
    assert fd.conclusion == B_all, "fini_downward_thm ne conclut pas l'hyp B de N_collectivise"
    return _cut(coll_sous_B, B_all, fd)                  # coll(x,Fini x)  [reports principe+sous-lemme]


# ════════════════════════════════════════════════════════════════════════════
#  ÉTAPE 1 (REPORTÉE, énoncé) — CARDINAUX ≤ a BIEN ORDONNÉS
#
#  cardinaux_bien_ordonnes(a) :
#    (∀S)( ( S ⊂ [0,a]  et  S ≠ ∅ ) ⇒ (∃m)( m∈S et (∀x)(x∈S ⇒ m ≤ x) ) )
#
#  « Tout ensemble non vide de cardinaux ≤ a a un PLUS PETIT élément (pour ≤). »
#  C'est le bon ordre de l'ordre des cardinaux ≤ a — le socle du critère C61 par
#  PLUS-PETIT-CONTRE-EXEMPLE.  Voie : ZERMELO (bon ordre du SET a) transporté à
#  l'ordre des CARDINAUX ≤ a via la correspondance ordinal↔cardinal (chaque cardinal
#  ≤ a = Card d'un segment initial du bon ordre de a).  Cette correspondance
#  ordinal↔cardinal N'EXISTE PAS encore dans le projet ⇒ REPORTÉ ici comme ÉNONCÉ.
#
#  RACCORD à C61 : à partir de cardinaux_bien_ordonnes(a) + l'existence du
#  prédécesseur (tout entier > 0 est un successeur, Prop. 2 §III.5) + la séparation
#  S8 de A = { m ∈ [0,n0] | Fini m et ¬P[m] }, on DÉRIVE principe_recurrence(P) par
#  le plus-petit-contre-exemple (voir docstring de principe_recurrence).  Ce raccord
#  est lui-même un chantier (REPORTÉ avec cardinaux_bien_ordonnes).
# ════════════════════════════════════════════════════════════════════════════
def cardinaux_bien_ordonnes(a="a", S="S", m="m", x="x"):
    """Énoncé « les cardinaux ≤ a sont bien ordonnés (pour ≤) » :
        (∀S)( ( S ⊂ [0,a] et S ≠ ∅ ) ⇒ (∃m)( m∈S et (∀x)(x∈S ⇒ m ≤ x) ) ).

    ⚠️ NON PROUVÉ (REPORTÉ — ÉTAPE 1, connexion ordinal↔cardinal via Zermelo).
    Énoncé fourni comme cible structurelle ; socle du critère C61."""
    va, vS, vm, vx = _t(a), var(S), var(m), var(x)
    interv = E.intervalle_entiers(ZERO, va)               # [0, a]
    from bourbaki.logique.i_1_termes_relations.formule import inclus
    hyp = et(inclus(vS, interv), non(egal(vS, E.VIDE)))   # S ⊂ [0,a] et S ≠ ∅
    plus_petit = existe(m, et(appartient(vm, vS),
        pourtout(x, impl(appartient(vx, vS), inf_egal_card(vm, vx)))))
    return pourtout(S, impl(hyp, plus_petit))


__all__ = [
    # helpers
    "b_le_0_implique_egal_0",
    # ÉTAPE 3 — base + step
    "base_P0", "cardinal_pas_entre", "pas_recurrence",
    # ÉTAPE 2 — C61 (métathéorème)
    "principe_recurrence", "recurrence_C61",
    "recurrence_fini_implique_P", "fini_downward_thm",
    # ÉTAPE 4 — ℕ collectivisé (sous reports principe_recurrence + cardinal_pas_entre)
    "N_collectivise_final",
    # ÉTAPE 1 — énoncé reporté
    "cardinaux_bien_ordonnes",
]

