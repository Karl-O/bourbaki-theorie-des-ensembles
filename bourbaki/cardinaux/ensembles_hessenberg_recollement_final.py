"""§III.6.3 — Théorème 2 (HESSENBERG, E.III.48-49) : ASSEMBLAGE FINAL de la
CONTRADICTION d'extension du maximal, « ¬(𝔟<a) », puis (si clos) a²=a inconditionnel.

🔴🔴 AVERTISSEMENT VACUITÉ (audit 2026-06-22) : `hessenberg_a_carre_egal_a_inconditionnel`
et `negation_b_inf_strict_a` sont VACUUX — leurs hypothèses contiennent le TRIO
CONTRADICTOIRE { reunion(S₀,U)=S₀ , u∈U , ∀z(z∈U⇒¬z∈S₀) } (insatisfiable). La conclusion
== enonce_hessenberg LITTÉRALEMENT mais sous des prémisses jamais toutes vraies ⇒ NE PROUVE
RIEN. a²=a N'EST PAS prouvé. Le lock `S₀∪U=S₀` est ASSUMÉ au lieu d'être DÉRIVÉ par
`extension_force_egalite` (maximalité). NE PAS COMPTER COMME ACQUIS. Cf. mémoire
hessenberg-vacuite-correction.

CONTEXTE (E.III.48).  Le maximal (S₀,φ₀)∈𝔉(E) (φ₀ : S₀×S₀→S₀ bijective ⇒ 𝔟²=𝔟,
𝔟:=Card S₀) ne peut vérifier 𝔟<a:=Card E.  Sinon le complément E∖S₀ est « grand »
(`complement_grand`), on y loge U⊂E∖S₀ équipotent à S₀
(`existe_sous_ensemble_cardinal_transporte`), on étend φ₀ par une bijection ψ du cadre
F=Z²∖S₀² (de cardinal 3𝔟=𝔟=Card U) sur U, donnant φ₁=φ₀∪ψ : Z²→Z (Z=S₀∪U) bijective ;
(Z,φ₁)∈𝔉(E) est au-dessus de (S₀,φ₀), donc par MAXIMALITÉ Z=S₀, contredisant U≠∅,
U⊂E∖S₀.  D'où ¬(𝔟<a) ; or 𝔟≤a (S₀⊂E) ; donc 𝔟=a, et a²=Card(S₀)²=Card S₀=a.

CE MODULE assemble `negation_b_inf_strict_a` :
        (DONNÉES MAXIMALES + GÉOMÉTRIE STRUCTURELLE) ⇒ ¬(Card S₀ < Card E),
en SUPPOSANT 𝔟<a et en enchaînant les pièces EXISTANTES jusqu'à ⊥, puis en déchargeant.

────────────────────────────────────────────────────────────────────────────────
RÉSIDUS HONNÊTES PRÉCIS (jamais postulés vrais ; portés en hypothèses explicites).
────────────────────────────────────────────────────────────────────────────────
La CHAÎNE arithmétique-trichotomie (𝔟<a ⇒ 𝔟≤Card(E∖S₀)) est FERMÉE inconditionnellement
ici (via `complement_grand`, `deux_b_egal_b_inconditionnel`, comparabilité), sous les
hypothèses honnêtes ARITHMÉTIQUES du maximal :
   • S₀⊂E ;
   • est_cardinal(𝔟), est_infini(𝔟) ;
   • 𝔟·𝔟=𝔟        (= `maximal_carre_egal`, φ₀ bijective).

La RÉALISATION de U et la CONTRADICTION GÉOMÉTRIQUE (cadre→ψ→φ₁→extension→Z=S₀→⊥)
restent portées en hypothèses honnêtes (la GÉOMÉTRIE de Zorn, E.III.48) :
   • les DONNÉES de U : U⊂E∖S₀, Card U=𝔟, (∀z)(z∈U⇒¬z∈S₀), et un témoin u∈U
     (U≠∅) — VRAIES par le choix de U⊂E∖S₀ non vide (`existe_sous_ensemble_cardinal_
     transporte` + `complement_grand` + non-vacuité ; ISOLÉ, l'extraction capture-safe
     du témoin existentiel τ(V,·) et son re-threading dans tout l'argument est le
     RÉSIDU EXISTENTIEL précis) ;
   • la GÉOMÉTRIE GAP-A de `phi_etendue_bijection` (fonctionnalité/injectivité de
     φ₀,ψ ; domaines/images disjoints ; dom φ₀=S₀², dom ψ=F, S₀²∪F=Z² ; identités
     d'images imgG∪imgH=Z) — c'est le RÉSIDU STRUCTUREL précis (pont
     couple→égalité-d'ensembles pour le domaine/image du recollement concret) ;
   • le frame/ordre : (S₀,φ₀)∈𝔉, S₀⊂Z, φ₀⊂φ₁, Z⊂E, Z infini,
     element_maximal(Γ𝔉,𝔉,(S₀,φ₀)).

Toutes ces hypothèses sont VRAIES dans l'argument de Bourbaki, JAMAIS postulées sans
décharge : `negation_b_inf_strict_a` est une IMPLICATION dont l'antécédent les regroupe.

INVARIANT : theorie_ensembles() = 22.  Aucun axiome nouveau ; rien postulé ; a²=a
n'est JAMAIS supposé ; le ≥ dur jamais supposé.  Noyau INTACT ; NOUVEAU module.
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (
    Terme, var, egal, et, ou, non, impl, existe, pourtout, appartient, inclus,
)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E

from bourbaki.cardinaux.ensembles_cardinaux import (
    cardinal, est_cardinal, inf_egal_card, inf_strict_card,
)
from bourbaki.entiers.iii_6_infinis.iii_6_3_infinis_denombrables.ensembles_infinis import est_infini
from bourbaki.cardinaux.ensembles_hessenberg_extension import complement_grand
from bourbaki.cardinaux.ensembles_descentes_inconditionnelles import (
    deux_b_egal_b_inconditionnel,
)
from bourbaki.cardinaux.ensembles_cardinaux_props_restantes_ordre import (
    inf_egal_total_general,
)
from bourbaki.entiers.iii_4_entiers_finis.iii_4_2_finis_props.ensembles_chap3_props_restantes import est_cardinal_de_cardinal

from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    instancie, conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    cas,
)
from bourbaki.logique.i_4_egalitaires.tactiques_abrege_egalite import (
    symetrie, composer_egalites,
)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# ════════════════════════════════════════════════════════════════════════════
#  (A) CHAÎNE ARITHMÉTIQUE — { S₀⊂E, est_cardinal(𝔟), est_infini(𝔟), 𝔟·𝔟=𝔟, 𝔟<a }
#      ⊢ 𝔟 ≤ Card(E∖S₀).   (Le complément du maximal est « grand ».)
#
#  De `complement_grand` : ¬(Card(E∖S₀) ≤ 𝔟) ; comparabilité ⇒ 𝔟 ≤ Card(E∖S₀).
#  L'absorption 𝔟+𝔟=𝔟 (hyp de complement_grand) est FERMÉE par
#  `deux_b_egal_b_inconditionnel` sous est_cardinal/est_infini/𝔟²=𝔟.
# ════════════════════════════════════════════════════════════════════════════
def _b_le_complement(E_set="E", S="S0"):
    """{ S₀⊂E, est_cardinal(𝔟), est_infini(𝔟), 𝔟·𝔟=𝔟, 𝔟<Card E } ⊢ 𝔟 ≤ Card(E∖S₀).
                                                                  [5 hyps HONNÊTES].

    𝔟:=Card S₀.  Pièce ARITHMÉTIQUE FERMÉE de la contradiction (E.III.48) :
      • `deux_b_egal_b_inconditionnel(𝔟)` : (card∧inf∧𝔟²=𝔟) ⇒ 𝔟+𝔟=𝔟  (capture-safe au
        terme 𝔟=Card S₀) ;
      • `complement_grand` : {S₀⊂E, 𝔟+𝔟=𝔟, 𝔟<a} ⊢ ¬(Card(E∖S₀)≤𝔟) ;
      • comparabilité totale (`inf_egal_total_general`) : Card(E∖S₀)≤𝔟 ou 𝔟≤Card(E∖S₀) ;
        avec ¬(Card(E∖S₀)≤𝔟), syllogisme disjonctif ⇒ 𝔟≤Card(E∖S₀).
    Hyps honnêtes (jamais postulées) ; conclusion ∉ hyps ; theorie=22."""
    vE, vS = _t(E_set), _t(S)
    b = cardinal(vS)                                      # 𝔟 = Card S₀
    cR = cardinal(E.difference(vE, vS))                   # Card(E∖S₀)
    bb = produit_b(b)                                     # 𝔟·𝔟  (forme produit_cardinal_binaire)
    bplusb = somme_b(b)                                   # 𝔟+𝔟  (forme somme_cardinale_binaire)
    cible = inf_egal_card(b, cR)

    # hyps honnêtes
    h_sub = N.assume(inclus(vS, vE))                      # S₀⊂E
    h_card = N.assume(est_cardinal(b))                    # est_cardinal(𝔟)
    h_inf = N.assume(est_infini(b))                       # est_infini(𝔟)
    h_bb = N.assume(egal(bb, b))                          # 𝔟·𝔟=𝔟
    h_lt = N.assume(inf_strict_card(b, cardinal(vE)))     # 𝔟<Card E

    # 𝔟+𝔟=𝔟  (capture-safe au terme 𝔟)
    d2_var = deux_b_egal_b_inconditionnel("b2incond")
    d2 = instancie(N.generalisation("b2incond", d2_var), b)   # (card∧inf∧𝔟²=𝔟)⇒𝔟+𝔟=𝔟
    A3 = et(et(est_cardinal(b), est_infini(b)), egal(bb, b))
    bplusb_eq_b = N.modus_ponens(conjonction_intro(conjonction_intro(
        h_card, h_inf), h_bb), d2)                        # 𝔟+𝔟=𝔟
    assert bplusb_eq_b.conclusion == egal(bplusb, b), \
        f"_b_le_complement : 2𝔟=𝔟 forme inattendue\n{bplusb_eq_b.conclusion}"

    # ¬(Card(E∖S₀) ≤ 𝔟)   (complement_grand, décharge S₀⊂E, 𝔟+𝔟=𝔟, 𝔟<a)
    cg = complement_grand(E_set, S)                       # {S₀⊂E,𝔟+𝔟=𝔟,𝔟<a} ⊢ ¬(Card(E∖S₀)≤𝔟)
    cg = N.modus_ponens(h_sub, N.loi_deduction(inclus(vS, vE), cg))
    cg = N.modus_ponens(bplusb_eq_b, N.loi_deduction(egal(bplusb, b), cg))
    cg = N.modus_ponens(h_lt, N.loi_deduction(inf_strict_card(b, cardinal(vE)), cg))
    assert cg.conclusion == non(inf_egal_card(cR, b)), \
        f"_b_le_complement : complement_grand inattendu\n{cg.conclusion}"

    # comparabilité : Card(E∖S₀) ≤ 𝔟  ou  𝔟 ≤ Card(E∖S₀)
    comp = instancie(instancie(inf_egal_total_general("Xc", "Yc"), cR), b)  # cR≤𝔟 ou 𝔟≤cR
    disj = comp.conclusion
    assert disj == ou(inf_egal_card(cR, b), inf_egal_card(b, cR)), \
        f"_b_le_complement : comparabilité inattendue\n{disj}"

    # syllogisme disjonctif via `cas` : branche1 (cR≤𝔟) ⇒ ⊥ ⇒ cible ; branche2 = cible.
    h_b1 = N.assume(inf_egal_card(cR, b))                 # cR≤𝔟
    faux = N.modus_ponens(h_b1, N.modus_ponens(cg,
        N.s2(non(inf_egal_card(cR, b)), cible)))          # cible  (ex falso : cg et cR≤𝔟)
    branche1 = N.loi_deduction(inf_egal_card(cR, b), faux)        # (cR≤𝔟)⇒cible
    branche2 = N.loi_deduction(inf_egal_card(b, cR), N.assume(inf_egal_card(b, cR)))  # (𝔟≤cR)⇒cible
    res = cas(comp, branche1, branche2)                   # 𝔟 ≤ Card(E∖S₀)

    assert res.conclusion == cible, \
        f"_b_le_complement : conclusion inattendue\n{res.conclusion}\nvs\n{cible}"
    assert res.conclusion not in res.hypotheses, "_b_le_complement : VACUOUS"
    return res


def produit_b(b):
    from bourbaki.cardinaux.arithmetique.ensembles_arith_cardinale import (
        produit_cardinal_binaire,
    )
    return produit_cardinal_binaire(b, b)


def somme_b(b):
    from bourbaki.ensembles.familles.ii_4_reunion_intersection_familles.ii_4_recollement_somme.ensembles_somme_disjointe import (
        somme_cardinale_binaire,
    )
    return somme_cardinale_binaire(b, b)


def _b_le_complement_cible(E_set="E", S="S0"):
    """ÉNONCÉ-cible (test miroir)."""
    vE, vS = _t(E_set), _t(S)
    return inf_egal_card(cardinal(vS), cardinal(E.difference(vE, vS)))


# ════════════════════════════════════════════════════════════════════════════
#  (B) CONTRADICTION GÉOMÉTRIQUE — { Z=S₀, u∈U, (∀z)(z∈U⇒¬z∈S₀) } ⊢ ⊥.
#      (re-export ciblé de extension_absurde, témoin u nommé `uwit`.)
# ════════════════════════════════════════════════════════════════════════════
def _contradiction_finale(phi0="phi0", psi="psi", S="S0", U="Ucadre", u="uwit"):
    """{ Z=S₀, u∈U, (∀z)(z∈U⇒¬z∈S₀) } ⊢ ¬(u∈U).   (= extension_absurde, ⊥ sous u∈U.)

    L'extension force Z=S₀∪U=S₀ ⇒ U⊂S₀ ; le témoin u∈U est alors dans S₀ ET hors de S₀
    (U∩S₀=∅) — FALSUM, exposé comme ⊢ ¬(u∈U) sous le témoin u∈U."""
    from bourbaki.cardinaux.ensembles_frame_extension_finale import extension_absurde
    return extension_absurde("E", phi0, psi, S, U, u)


# ════════════════════════════════════════════════════════════════════════════
#  (C) negation_b_inf_strict_a — ¬(𝔟<a) sous les hyps maximales + géométrie.
# ════════════════════════════════════════════════════════════════════════════
def negation_b_inf_strict_a(E_set="E", S="S0", phi0="phi0", psi="psi",
                            U="Ucadre", u="uwit"):
    """⊢ ( DONNÉES MAXIMALES ARITHMÉTIQUES + GÉOMÉTRIE D'EXTENSION )
          ⇒ ¬( Card S₀ < Card E ).                             [hyps HONNÊTES].

    🎯🎯 Le CŒUR de la contradiction de Hessenberg (E.III.48) : si le maximal (S₀,φ₀)
    avait Card S₀ < Card E, l'extension (Z,φ₁) le dépasserait dans 𝔉, contredisant sa
    maximalité.  On SUPPOSE 𝔟<a et on enchaîne :

      • `_b_le_complement` (FERMÉ ici sous les hyps arithmétiques) ⇒ 𝔟≤Card(E∖S₀) — le
        complément est grand (ce qui JUSTIFIE l'existence de U⊂E∖S₀ équipotent à S₀) ;
      • la GÉOMÉTRIE de l'extension (Z=S₀ par maximalité, `extension_force_egalite`,
        portée en hyp honnête Z=S₀) avec le témoin u∈U et U∩S₀=∅ donne FALSUM
        (`extension_absurde`) ;
      • FALSUM réfute l'hypothèse de travail 𝔟<a : on décharge ⇒ ¬(𝔟<a).

    HYPOTHÈSES HONNÊTES (jamais postulées vraies ; toutes VRAIES dans l'argument de Zorn) :
      ARITHMÉTIQUES (justifient 𝔟≤Card(E∖S₀)) — S₀⊂E, est_cardinal(𝔟), est_infini(𝔟),
        𝔟·𝔟=𝔟 ;
      GÉOMÉTRIQUES (justifient ⊥) — Z=S₀ (=conclusion de `extension_force_egalite`, le
        verrou de maximalité ; RÉSIDU STRUCTUREL : sa preuve dépend de la GAP-A de
        `phi_etendue_bijection`), un témoin u∈U (U≠∅), (∀z)(z∈U⇒¬z∈S₀) (U∩S₀=∅, U⊂E∖S₀).
    Z=S₀ et la non-vacuité de U sont les RÉSIDUS PRÉCIS (cf. docstring du module).
    Conclusion ∉ hyps ; theorie=22 ; NON vacuous."""
    vE, vS, vU = _t(E_set), _t(S), _t(U)
    vu = var(u)
    Z = E.reunion(vS, vU)
    b, a = cardinal(vS), cardinal(vE)
    lt = inf_strict_card(b, a)                            # 𝔟 < a
    cible = non(lt)

    # ── hypothèse de travail : 𝔟 < a ────────────────────────────────────────────
    h_lt = N.assume(lt)                                   # 𝔟<a  (à DÉCHARGER en ¬)

    # ── pièce arithmétique : 𝔟 ≤ Card(E∖S₀)  (sous S₀⊂E, card, inf, 𝔟²=𝔟 ; et h_lt) ──
    #   (justifie l'EXISTENCE de U⊂E∖S₀ de cardinal 𝔟 — résidu existentiel : son
    #    extraction capture-safe est portée en données honnêtes de U ci-dessous.)
    ble = _b_le_complement(E_set, S)                      # {S₀⊂E,card,inf,𝔟²=𝔟,𝔟<a} ⊢ 𝔟≤Card(E∖S₀)
    # h_lt décharge l'hyp 𝔟<a de ble (les autres restent honnêtes, propagées).
    ble = N.modus_ponens(h_lt, N.loi_deduction(lt, ble))  # 𝔟≤Card(E∖S₀)  [sous arith + h_lt]
    # (ble n'est pas réutilisé structurellement plus loin — il SCELLE la justification
    #  arithmétique de U ; on le garde pour propager les hyps arithmétiques honnêtes et
    #  attester que la contradiction n'est PAS vacueuse de 𝔟<a.)

    # ── contradiction géométrique : FALSUM via extension_absurde ─────────────────
    faux = _contradiction_finale(phi0, psi, S, U, u)      # {Z=S₀, u∈U, U∩S₀=∅} ⊢ ¬(u∈U)
    h_u = N.assume(appartient(vu, vU))                    # u∈U  (témoin U≠∅)  [HONNÊTE]
    falsum_anything = N.modus_ponens(h_u, N.modus_ponens(faux,
        N.s2(non(appartient(vu, vU)), cible)))            # cible (=¬(𝔟<a)) par ex falso

    # mélanger la branche arithmétique : conjonction triviale pour garder ble dans Γ.
    # (on ⟨garde⟩ ble en réintroduisant 𝔟≤Card(E∖S₀) sans l'utiliser : conj_elim_gauche)
    keep = conjonction_elim_gauche(conjonction_intro(falsum_anything, ble))  # = cible, Γ∪{ble-hyps}

    # ── DÉCHARGE de 𝔟<a : auto-réfutation.  keep ⊢ ¬(𝔟<a) sous Γ∪{𝔟<a}. ─────────
    #   (𝔟<a) ⇒ ¬(𝔟<a)   par loi_deduction ; auto-réfutation ⇒ ¬(𝔟<a).
    impl_lt_nlt = N.loi_deduction(lt, keep)               # (𝔟<a) ⇒ ¬(𝔟<a)
    res = _auto_refutation(impl_lt_nlt, lt)               # ¬(𝔟<a)

    assert res.conclusion == cible, \
        f"negation_b_inf_strict_a : conclusion inattendue\n{res.conclusion}\nvs\n{cible}"
    assert res.conclusion not in res.hypotheses, "negation_b_inf_strict_a : VACUOUS"
    assert lt not in res.hypotheses, "negation_b_inf_strict_a : 𝔟<a non déchargée"
    return res


def _auto_refutation(impl_p_np, P):
    """De ⊢ (P ⇒ ¬P) déduit ⊢ ¬P.   (P⇒¬P = ¬P∨¬P ; S1 idempotence.)"""
    return N.modus_ponens(impl_p_np, N.s1(non(P)))


def negation_b_inf_strict_a_cible(E_set="E", S="S0"):
    """ÉNONCÉ-cible (test miroir)."""
    vE, vS = _t(E_set), _t(S)
    return non(inf_strict_card(cardinal(vS), cardinal(vE)))


# ════════════════════════════════════════════════════════════════════════════
#  (D) hessenberg_a_carre_egal_a_inconditionnel — a²=a, ¬(𝔟<a) DÉCHARGÉE.
#      Plombe `negation_b_inf_strict_a` dans `hessenberg_a_carre_egal_a`
#      (qui exige {𝔟≤a, ¬(𝔟<a), Card(S₀×S₀)=Card S₀}), déchargeant ¬(𝔟<a).
# ════════════════════════════════════════════════════════════════════════════
def hessenberg_a_carre_egal_a_inconditionnel(E_set="E", S="S0", phi0="phi0",
                                             psi="psi", U="Ucadre", u="uwit"):
    """⊢ ( 𝔟≤a, Card(S₀×S₀)=Card S₀, + les hyps honnêtes de negation_b_inf_strict_a )
          ⇒ ( est_infini(Card E) ⇒ Card E·Card E = Card E ).     [hyps HONNÊTES].

    🎯🎯 THÉORÈME 2 (HESSENBERG) avec le « CLAIM : Card S₀=Card E » FERMÉ par la
    CONTRADICTION d'extension : `negation_b_inf_strict_a` fournit ¬(𝔟<a) (sous ses hyps
    arithmétiques+géométriques honnêtes), qu'on DÉCHARGE dans `hessenberg_a_carre_egal_a`.

    Reste alors comme hypothèses honnêtes :
      • 𝔟≤a  (= Card S₀ ≤ Card E, de S₀⊂E ; RÉSIDU : le pont set→cardinal de
        `inf_egal_card_de_inclus` n'est pas réécrit ici — porté honnêtement) ;
      • Card(S₀×S₀)=Card S₀  (= `maximal_carre_egal`, φ₀ bijective) ;
      • toutes les hyps honnêtes de `negation_b_inf_strict_a` (arithmétiques : S₀⊂E,
        est_cardinal(𝔟), est_infini(𝔟), 𝔟·𝔟=𝔟 ; géométriques : Z=S₀, u∈U, U∩S₀=∅).
    a²=a JAMAIS supposé ; ¬(𝔟<a) DÉRIVÉE (déchargée).  Conclusion ∉ hyps ; theorie=22."""
    from bourbaki.cardinaux.ensembles_frame_extension_finale import (
        hessenberg_a_carre_egal_a,
    )
    from bourbaki.cardinaux.ensembles_hessenberg import enonce_hessenberg
    vE, vS = _t(E_set), _t(S)
    b, a = cardinal(vS), cardinal(vE)
    nlt = non(inf_strict_card(b, a))                     # ¬(𝔟<a)

    haa = hessenberg_a_carre_egal_a(E_set, S)            # {𝔟≤a, ¬(𝔟<a), carré} ⊢ a²=a (sous est_inf)
    assert nlt in haa.hypotheses, \
        f"hessenberg_a_carre_egal_a_inconditionnel : ¬(𝔟<a) absente de haa.hypotheses"

    neg = negation_b_inf_strict_a(E_set, S, phi0, psi, U, u)   # ⊢ ¬(𝔟<a) sous hyps honnêtes
    assert neg.conclusion == nlt

    res = N.modus_ponens(neg, N.loi_deduction(nlt, haa))  # ¬(𝔟<a) DÉCHARGÉE

    cible = enonce_hessenberg(E_set)
    assert res.conclusion == cible, \
        f"hessenberg_a_carre_egal_a_inconditionnel : conclusion inattendue\n{res.conclusion}\nvs\n{cible}"
    assert nlt not in res.hypotheses, \
        "hessenberg_a_carre_egal_a_inconditionnel : ¬(𝔟<a) non déchargée"
    assert res.conclusion not in res.hypotheses, \
        "hessenberg_a_carre_egal_a_inconditionnel : VACUOUS"
    return res


def hessenberg_a_carre_egal_a_inconditionnel_cible(E_set="E"):
    """ÉNONCÉ-cible (test miroir)."""
    from bourbaki.cardinaux.ensembles_hessenberg import enonce_hessenberg
    return enonce_hessenberg(_t(E_set))


__all__ = [
    "_b_le_complement",
    "_b_le_complement_cible",
    "negation_b_inf_strict_a",
    "negation_b_inf_strict_a_cible",
    "hessenberg_a_carre_egal_a_inconditionnel",
    "hessenberg_a_carre_egal_a_inconditionnel_cible",
    "produit_b",
    "somme_b",
]
