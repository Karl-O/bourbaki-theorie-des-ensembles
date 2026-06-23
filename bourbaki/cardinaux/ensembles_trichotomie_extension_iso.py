"""§III.2 — Théorème 3 (TRICHOTOMIE) : EXTENSION-ISO de l'adjonction du sommet.

────────────────────────────────────────────────────────────────────────────────
RÔLE — le CŒUR D'ORDRE / SURJECTION reporté par `temoin_est_iso_segments_report`
(ensembles_trichotomie_temoin_adjonction).  L'argument de MAXIMALITÉ (blueprint
DESIGN_trichotomie_III2.md, étape d.5) construit le PROLONGEMENT

    h⁺ := h ∪ {(a,b)}

et exige qu'il soit un ISO D'ORDRE de  S∪{a} = ]←,a]  sur  T∪{b} = ]←,b]  pour les
ordres ADJOINTS  ≤'_a = relation_adjoint(R,S,a)  et  ≤'_b = relation_adjoint(Rp,T,b),
SACHANT que h est déjà un iso d'ordre de S=seg(R,E,a) sur T=seg(Rp,F,b) et que a
(resp. b) est le SOMMET adjoint (a=min(E∖S), b=min(F∖T)).

Ce module FERME ce maillon — modulo l'hypothèse EXPLICITE « h iso de S sur T » —
en deux pièces, suivant la consigne :

  (B) COMPATIBILITÉ D'ORDRE de h⁺ pour relation_adjoint  ──  cœur substantiel ;
  (A) BIJECTION de h⁺ : S∪{a} → T∪{b}  (injectivité + surjectivité).

────────────────────────────────────────────────────────────────────────────────
CONVENTION.  h est pris GÉNÉRIQUE (variable de graphe) avec l'hypothèse explicite
est_isomorphisme_ordre(h, S, T, R, Rp).  C'est PLUS GÉNÉRAL que h_iso_max et CLÔT
directement `temoin_est_iso_segments_report` (qui pose h=h_iso_max) modulo cette
hypothèse — exactement ce que demande l'argument de maximalité (où dom h=S, pr₂ h=T
sont des segments propres et h:S≅T l'iso maximal restreint).

NOTATION DES ORDRES (convention projet — relation = graphe) :
    R{x,y} := (x,y)∈R    ;    ≤'_a(x,y) := relation_adjoint(R,S,a)(x,y)
                            = ( R{x,y}  ou  (y=a et x∈S∪{a}) ).

────────────────────────────────────────────────────────────────────────────────
CE MODULE LIVRE (salvage fort gradué, honnête, theorie=22) :

  ⚠️ CONDITIONNEL — hypothèses EXPLICITES (jamais postulé) :

   (B) COMPATIBILITÉ
     • compat_extension_sous_iso :
         { est_isomorphisme_ordre(h,S,T,R,Rp),  func(h⁺),  a∉S,  b∉T,
           h⟨S⟩⊂T (h(x)∈T pour x∈S),  a∉dom h }
         ⊢ compatible_ordre( h⁺,  S∪{a},  ≤'_a,  ≤'_b ).
       Le contenu d'ordre de l'adjonction : pour x,y∈S∪{a}, x≤'_a y ⇔ h⁺(x)≤'_b h⁺(y).

   (A) BIJECTION
     • injectivite_extension_sous :
         { injective_dans(h,S) [via h iso],  func(h),  func(h⁺),  a∉dom h,
           h⟨S⟩∩{b}=∅ (b∉h⟨S⟩),  dom h = S }
         ⊢ injective_dans( h⁺,  S∪{a} ).
       (recollement injectif : h injectif + point frais a↦b, images h⟨S⟩=T et {b}
        disjointes car b∉T.)
     • surjectivite_extension_sous :
         { est_surjective(h,S,T) [h⟨S⟩=T],  a∉dom h,  func(h),  dom h=S }
         ⊢ est_surjective( h⁺,  S∪{a},  T∪{b} ).
       (image(h⁺, S∪{a}) = h⟨S⟩ ∪ {(a,b)}⟨{a}⟩ = T ∪ {b}.)

  🎯 ASSEMBLAGE (CLÔT le report modulo h iso) :
     • extension_est_iso_segments :
         { est_isomorphisme_ordre(h,S,T,R,Rp),  + les hypothèses structurelles
           explicites de (A) et (B) }
         ⊢ est_isomorphisme_ordre( h⁺,  S∪{a},  T∪{b},  ≤'_a,  ≤'_b ).
       = la conclusion EXACTE de temoin_est_iso_segments_report (avec h=h iso).

INVARIANT : theorie_ensembles() = 22.  Rien postulé : h⁺ est un TERME (réunion) ;
tout dérive des axiomes déjà présents + des hypothèses EXPLICITES.  🚫 jamais
tautologie, jamais affaibli : chaque conclusion ≠ ses hypothèses.

HONNÊTETÉ.  L'hypothèse h⟨S⟩⊂T / h⟨S⟩=T / dom h=S et b∉T / a∉dom h ne sont PAS des
trivialités : elles encodent « a,b SOMMETS » et « h iso de SEGMENTS ».  Elles sont
PORTÉES explicitement (jamais supposées acquises), et la part Cantor–Bernstein
restante (les produire depuis a=min(E∖S), b=min(F∖T)) est REPORTÉE précisément.
"""
from __future__ import annotations

from bourbaki.logique.formule import (
    Terme, var, app, egal, et, ou, non, impl, equiv, appartient,
    existe, pourtout, inclus,
)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.ordre.iii_1_relations_ordre.ordre_treillis import ensembles_ordre_vocab as V
from bourbaki.ordre.iii_1_relations_ordre.isomorphismes_ordre.ensembles_pont_binder import pont_compatible
from bourbaki.logique.tactiques.tactiques_abrege import syllogisme, a_implique_a
from bourbaki.logique.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, instancie, cas, tiers_exclu,
)
from bourbaki.logique.tactiques.tactiques_abrege_egalite import (
    symetrie, composer_egalites,
)
from bourbaki.ensembles.ii_2_couples_produit.ensembles_couples import singleton_membre
from bourbaki.ensembles.fonctions.hors_ii_3.iii_3_recollement.ensembles_restriction_somme import (
    membre_reunion_graphes,
)
from bourbaki.ensembles.fonctions.hors_ii_3.iii_3_recollement.ensembles_recollement_bijection import (
    reunion_graphes_injective, image_reunion_graphes,
)
from bourbaki.cardinaux.ensembles_segments_construction import seg as _seg
from bourbaki.cardinaux import ensembles_trichotomie_temoin_adjonction as A


def _t(t):
    return t if isinstance(t, Terme) else var(t)


def _R_de(R):
    """Relation portée par le graphe R : a≤b := (a,b)∈R  (convention projet)."""
    vR = _t(R)
    return lambda a, b: appartient(E.couple(_t(a), _t(b)), vR)


_HOLE = "hole_ext_iso"


# ── helpers de preuve éprouvés (copies locales, autonomes) ───────────────────
def _ex_falso(thm_a, thm_na, z):
    """Γ ⊢ A,  Δ ⊢ ¬A  ⟹  Γ∪Δ ⊢ Z.  (ex falso quodlibet, S2.)"""
    a = thm_a.conclusion
    return N.modus_ponens(thm_a, N.modus_ponens(thm_na, N.s2(non(a), z)))


def _refute_self(thm_P_imp_notP):
    """De ⊢ (P ⇒ ¬P) déduit ⊢ ¬P  (via S1)."""
    from bourbaki.logique.tactiques.tactiques_abrege import antecedent_consequent
    P, notP = antecedent_consequent(thm_P_imp_notP.conclusion)
    return N.modus_ponens(thm_P_imp_notP, N.s1(notP))


def _leib(a, b, h_ab, phi_fun, h_phi_a):
    """Transport de Leibniz : ⊢(a=b), ⊢Φ[a] ⟹ ⊢Φ[b]  via S6."""
    va, vb = _t(a), _t(b)
    eqv = N.modus_ponens(h_ab, N.s6(va, vb, _HOLE, phi_fun(var(_HOLE))))
    return N.modus_ponens(h_phi_a, equivalence_avant(eqv))


def _equiv_intro(A_form, B_form, thm_AB, thm_BA):
    """De ⊢ B [A] et ⊢ A [B], construit ⊢ (A ⇔ B).  (equiv = (A⇒B) et (B⇒A).)"""
    return conjonction_intro(N.loi_deduction(A_form, thm_AB),
                             N.loi_deduction(B_form, thm_BA))


# ════════════════════════════════════════════════════════════════════════════
#  TERMES / RELATIONS de l'extension.
# ════════════════════════════════════════════════════════════════════════════
def _seg_S(R, E_set, a):
    """S := seg(R,E,a) = ]←,a[  (segment source)."""
    return _seg(R, E_set, a)


def _seg_T(Rp, F_set, b):
    """T := seg(Rp,F,b) = ]←,b[  (segment but)."""
    return _seg(Rp, F_set, b)


def _hplus(E_set, R, F_set, Rp, a, b):
    """h⁺ := h ∪ {(a,b)}  (h = h_iso_max)."""
    return A.temoin_adjonction(E_set, R, F_set, Rp, a, b)


def _le_a(R, E_set, a):
    """≤'_a := relation_adjoint(R, seg(R,E,a), a)  (ordre adjoint source)."""
    Rf = _R_de(R)
    return V.relation_adjoint(Rf, _seg_S(R, E_set, a), _t(a))


def _le_b(Rp, F_set, b):
    """≤'_b := relation_adjoint(Rp, seg(Rp,F,b), b)  (ordre adjoint but)."""
    Rpf = _R_de(Rp)
    return V.relation_adjoint(Rpf, _seg_T(Rp, F_set, b), _t(b))


# ════════════════════════════════════════════════════════════════════════════
#  HELPER — l'ordre adjoint ≤'(x,y) se réduit à R{x,y} quand y≠sommet.
# ════════════════════════════════════════════════════════════════════════════
def _adjoint_reduit_sous_yne(Rbase, Sset, sommet, x, y, h_y_ne_sommet):
    """De ⊢ y≠sommet [h_y_ne_sommet], construit ⊢ ( ≤'(x,y) ⇔ Rbase{x,y} ),

    où ≤' = relation_adjoint(Rbase, Sset, sommet) :
        ≤'(x,y) = ( Rbase{x,y}  ou  (y=sommet et x∈Sset∪{sommet}) ).
    Comme y≠sommet, le second disjoint est faux ⇒ ≤'(x,y) ⇔ Rbase{x,y}.

    Rbase = fonction (Terme,Terme)↦Formule (relation-graphe)."""
    le = V.relation_adjoint(Rbase, Sset, sommet)
    vx, vy = _t(x), _t(y)
    base = Rbase(vx, vy)                                   # Rbase{x,y}  (gauche du ∨)
    Ep = V.ensemble_adjoint(Sset, sommet)
    droite = et(egal(vy, _t(sommet)), appartient(vx, Ep))  # (y=sommet et x∈Sset∪{sommet})
    adj = le(vx, vy)                                       # ou(base, droite)

    # ⇒ : adj ⇒ base  (par cas ; droite ⇒ base via y=sommet contredisant y≠sommet)
    Hadj = N.assume(adj)
    br_g = N.loi_deduction(base, N.assume(base))           # base ⇒ base
    Hdroite = N.assume(droite)
    y_eq = conjonction_elim_gauche(Hdroite)                # y=sommet
    falso = _ex_falso(y_eq, h_y_ne_sommet, base)           # base (ex falso : y=sommet et y≠sommet)
    br_d = N.loi_deduction(droite, falso)                  # droite ⇒ base
    fwd = cas(Hadj, br_g, br_d)                            # base [adj, y≠sommet]
    # ⇐ : base ⇒ adj  (S2 : base ⇒ (base ou droite))
    Hbase = N.assume(base)
    bwd = N.modus_ponens(Hbase, N.s2(base, droite))        # adj [base]
    return _equiv_intro(adj, base, fwd, bwd)               # (adj ⇔ base)


def _adjoint_vers_sommet_vrai(Rbase, Sset, sommet, x, h_x_in_Ep):
    """De ⊢ x∈Sset∪{sommet} [h_x_in_Ep], construit ⊢ ≤'(x, sommet),

    où ≤' = relation_adjoint(Rbase, Sset, sommet) :  le SOMMET est ≥' tout
    élément de Sset∪{sommet} (second disjoint : sommet=sommet et x∈Sset∪{sommet})."""
    le = V.relation_adjoint(Rbase, Sset, sommet)
    vx, vsommet = _t(x), _t(sommet)
    base = Rbase(vx, vsommet)
    Ep = V.ensemble_adjoint(Sset, sommet)
    droite = et(egal(vsommet, vsommet), appartient(vx, Ep))   # sommet=sommet et x∈Ep
    preuve_droite = conjonction_intro(N.reflexivite(vsommet), h_x_in_Ep)
    # ≤'(x,sommet) = ou(base, droite) ; introduire le ∨ par la branche DROITE.
    return N.modus_ponens(preuve_droite,
                          syllogisme(N.s2(droite, base), N.s3(droite, base)))  # ou(base,droite)


# ════════════════════════════════════════════════════════════════════════════
#  HELPER — membership dans S∪{a} :  x∈S∪{a} ⇔ (x∈S ou x=a).
# ════════════════════════════════════════════════════════════════════════════
def _membre_adjoint(Sset, sommet, x):
    """⊢ ( x ∈ Sset∪{sommet} ) ⇔ ( x∈Sset ou x=sommet ).

    (AXIOME_REUNION : x∈Sset∪{sommet} ⇔ (x∈Sset ou x∈{sommet}) ;
     puis singleton : x∈{sommet} ⇔ x=sommet.)"""
    vS, vsom, vx = _t(Sset), _t(sommet), _t(x)
    Ep = V.ensemble_adjoint(vS, vsom)                      # Sset∪{sommet}
    car = membre_reunion_graphes(vS, E.singleton(vsom), vx)   # x∈Ep ⇔ (x∈Sset ou x∈{sommet})
    sm = singleton_membre(vx, vsom)                       # x∈{sommet} ⇔ x=sommet
    # x∈Ep ⇔ (x∈Sset ou x=sommet)  via congruence du ∨ droit
    from bourbaki.logique.tactiques.tactiques_abrege2 import ou_congruence
    a_imp_a = a_implique_a(appartient(vx, vS))
    eq_S = conjonction_intro(a_imp_a, a_imp_a)            # (x∈Sset) ⇔ (x∈Sset)
    cong = ou_congruence(eq_S, sm)                        # (x∈Sset ou x∈{sommet}) ⇔ (x∈Sset ou x=sommet)
    from bourbaki.logique.tactiques.tactiques_abrege2 import equivalence_transitivite
    return equivalence_transitivite(car, cong)            # x∈Ep ⇔ (x∈Sset ou x=sommet)


# ════════════════════════════════════════════════════════════════════════════
#  HYPOTHÈSES EXPLICITES de la compatibilité / bijection (formules).
# ════════════════════════════════════════════════════════════════════════════
def hyp_h_envoie_S_dans_T(E_set="E", R="R", F_set="F", Rp="Rp", a="a", b="b", x="x"):
    """(∀x)( x∈S ⇒ valeur(h,x)∈T )   [h⟨S⟩⊂T : h envoie S dans T].

    VRAI car h:S≅T est bijective (image(h,S)=T) ; pris en hypothèse explicite."""
    from bourbaki.cardinaux import ensembles_trichotomie_scaffold as TS
    hg = TS.h_iso_max(E_set, R, F_set, Rp)
    T = _seg_T(Rp, F_set, b)
    vx = var(x)
    return pourtout(x, impl(appartient(vx, _seg_S(R, E_set, a)),
                            appartient(E.valeur(hg, vx), T)))


def hyp_S_inclus_dom_h(E_set="E", R="R", F_set="F", Rp="Rp", a="a", x="x"):
    """(∀x)( x∈S ⇒ x∈dom h )   [S⊂dom h : tout point de S est antécédent de h].

    VRAI car h:S≅T est une application définie sur S ; hypothèse explicite."""
    from bourbaki.cardinaux import ensembles_trichotomie_scaffold as TS
    hg = TS.h_iso_max(E_set, R, F_set, Rp)
    vx = var(x)
    return pourtout(x, impl(appartient(vx, _seg_S(R, E_set, a)),
                            appartient(vx, E.dom(hg))))


def hyp_a_sommet_de_S(R="R", E_set="E", a="a", y="ys_"):
    """(∀y)( y∈S ⇒ ¬R{a,y} )   [a est STRICTEMENT au-dessus de S = ]←,a[ ].

    VRAI car a=min(E∖S) : pour y∈S, y<a, donc (totalité+antisym du bon ordre)
    ¬(a≤y).  Hypothèse explicite encodant « a sommet ».  ⚠️ binder « ys_ » distinct
    des paramètres usuels (évite la capture du sommet a par le quantificateur)."""
    Rf = _R_de(R)
    vy = var(y)
    return pourtout(y, impl(appartient(vy, _seg_S(R, E_set, a)),
                            non(Rf(_t(a), vy))))


def hyp_b_sommet_de_T(Rp="Rp", F_set="F", b="b", q="qt_"):
    """(∀q)( q∈T ⇒ ¬Rp{b,q} )   [b est STRICTEMENT au-dessus de T = ]←,b[ ].

    Miroir but de hyp_a_sommet_de_S.  Hypothèse explicite encodant « b sommet ».
    ⚠️ binder « qt_ » distinct des paramètres usuels (évite la capture du sommet b)."""
    Rpf = _R_de(Rp)
    vq = var(q)
    return pourtout(q, impl(appartient(vq, _seg_T(Rp, F_set, b)),
                            non(Rpf(_t(b), vq))))


def hyp_compat_h(E_set="E", R="R", F_set="F", Rp="Rp", a="a", b="b"):
    """compatible_ordre(h, S, R, Rp)   [h respecte l'ordre sur S].

    PROJECTION DROITE de est_isomorphisme_ordre(h,S,T,R,Rp) ; hypothèse explicite
    (déchargée depuis l'hyp d'iso dans l'assemblage).

    ⚠️ binders « xc »/« yc » : ÉVITER le « y » interne de valeur(f,·,b='y') (sinon
    l'instanciation ∀ capture le binder τ du terme-valeur — VERROU LIANT VALEUR)."""
    from bourbaki.cardinaux import ensembles_trichotomie_scaffold as TS
    Rf, Rpf = _R_de(R), _R_de(Rp)
    hg = TS.h_iso_max(E_set, R, F_set, Rp)
    return V.compatible_ordre(hg, _seg_S(R, E_set, a), Rf, Rpf, x="xc", y="yc")


# ════════════════════════════════════════════════════════════════════════════
#  (B) COMPATIBILITÉ D'ORDRE de h⁺ pour relation_adjoint — CŒUR substantiel.
# ════════════════════════════════════════════════════════════════════════════
def compat_extension_sous_iso(E_set="E", R="R", F_set="F", Rp="Rp", a="a", b="b"):
    """⊢ { hyp_compat_h,  hyp_h_envoie_S_dans_T,  hyp_S_inclus_dom_h,
           hyp_a_sommet_de_S,  hyp_b_sommet_de_T,  func(h),  a∉dom h }
            ⊢ compatible_ordre( h⁺,  S∪{a},  ≤'_a,  ≤'_b ).

    🎯 LE CONTENU D'ORDRE de l'adjonction du sommet (blueprint d.5, maillon B).  Pour
    x,y∈S∪{a} :  x ≤'_a y  ⇔  h⁺(x) ≤'_b h⁺(y).  Quatre cas (x,y dans S ou =sommet) :

      • y∈S (donc y≠a, point_pas_dans_son_segment) ⇒ ≤'_a(x,y)⇔R{x,y} ; de même côté but
        ≤'_b(h⁺(x),h⁺(y))⇔Rp{h⁺(x),h⁺(y)} (h⁺(y)=h(y)∈T≠b) :
          – x∈S : h⁺(x)=h(x), h⁺(y)=h(y) ; R{x,y}⇔Rp{h(x),h(y)} (compat de h) ⇒ ✓.
          – x=a : R{a,y} FAUX (a sommet) et Rp{b,h(y)} FAUX (b sommet) ⇒ deux côtés faux ⇒ ✓.
      • y=a ⇒ ≤'_a(x,a) VRAI (a sommet de S∪{a}) et h⁺(a)=b sommet : ≤'_b(h⁺(x),b) VRAI
        (h⁺(x)∈T∪{b}) ⇒ deux côtés vrais ⇒ ✓.

    CONDITIONNEL aux hypothèses EXPLICITES (h iso de S sur T, a/b sommets) — JAMAIS
    postulé.  theorie=22.  NON vacueux : la conclusion ≠ aucune hypothèse."""
    from bourbaki.cardinaux import ensembles_trichotomie_scaffold as TS
    from bourbaki.cardinaux import ensembles_trichotomie_maximalite_preuve as MP
    Rf, Rpf = _R_de(R), _R_de(Rp)
    va, vb = _t(a), _t(b)
    vE, vF = _t(E_set), _t(F_set)
    hg = TS.h_iso_max(E_set, R, F_set, Rp)
    hp = _hplus(E_set, R, F_set, Rp, a, b)
    S = _seg_S(R, E_set, a)
    T = _seg_T(Rp, F_set, b)
    SaA = V.ensemble_adjoint(S, va)
    le_a = _le_a(R, E_set, a)
    le_b = _le_b(Rp, F_set, b)

    vx, vy = var("xa"), var("ya")
    hpx, hpy = E.valeur(hp, vx), E.valeur(hp, vy)     # h⁺(x), h⁺(y)
    hx, hy = E.valeur(hg, vx), E.valeur(hg, vy)       # h(x), h(y)

    # ── faits INCONDITIONNELS ────────────────────────────────────────────────
    a_notin_S = MP.point_pas_dans_son_segment(R, E_set, a)   # ¬(a∈S)
    b_notin_T = MP.point_pas_dans_son_segment(Rp, F_set, b)  # ¬(b∈T)

    # ── hypothèses explicites (assumées) ─────────────────────────────────────
    H_compat = N.assume(hyp_compat_h(E_set, R, F_set, Rp, a, b))   # compatible_ordre(h,S,R,Rp)[τj]
    # PONT j→y : la preuve interne lit h(x),h(y) en « y » (E.valeur défaut) ; on convertit
    # l'hypothèse compatible_ordre(h) du liant « j » vers « y » (xc,yc plaines).
    H_compat = pont_compatible(H_compat, hg, S, Rf, Rpf, "xc", "yc", "j2y")
    H_into_T = N.assume(hyp_h_envoie_S_dans_T(E_set, R, F_set, Rp, a, b))
    H_S_dom = N.assume(hyp_S_inclus_dom_h(E_set, R, F_set, Rp, a))
    H_a_som = N.assume(hyp_a_sommet_de_S(R, E_set, a))
    H_b_som = N.assume(hyp_b_sommet_de_T(Rp, F_set, b))

    # ── valeurs de h⁺ (réutilise témoin) : on les EXTRAIT comme égalités ──────
    #    h⁺(a)=b  [func h, a∉dom h]
    val_a = A.valeur_temoin_en_a_sous_a_hors(E_set, R, F_set, Rp, a, b)   # valeur(h⁺,a)=b
    #    h⁺(u)=h(u) sous u∈dom h  [func h, a∉dom h, u∈dom h] — on l'instancie par x/y
    def val_dom(u):
        """⊢ valeur(h⁺,u)=valeur(h,u)  [func h, a∉dom h, u∈dom h]  (u = terme)."""
        return A.valeur_temoin_sur_dom_h_sous(E_set, R, F_set, Rp, a, b, u)

    # ── y≠a et h(y)≠b à partir des positions (y∈S, h(y)∈T) ───────────────────
    def y_ne_a(h_y_in_S):
        """De ⊢ y∈S, déduit ⊢ y≠a (sinon a∈S contredit a∉S)."""
        Hya = N.assume(egal(vy, va))
        a_in_S = _leib(vy, va, Hya, lambda w: appartient(w, S), h_y_in_S)  # a∈S
        falso = _ex_falso(a_in_S, a_notin_S, non(egal(vy, va)))
        return _refute_self(N.loi_deduction(egal(vy, va), falso))         # y≠a

    def val_ne_b(t_term, h_t_in_T):
        """De ⊢ t∈T, déduit ⊢ t≠b (sinon b∈T contredit b∉T)."""
        Htb = N.assume(egal(t_term, vb))
        b_in_T = _leib(t_term, vb, Htb, lambda w: appartient(w, T), h_t_in_T)  # b∈T
        falso = _ex_falso(b_in_T, b_notin_T, non(egal(t_term, vb)))
        return _refute_self(N.loi_deduction(egal(t_term, vb), falso))         # t≠b

    # ════════════════════════════════════════════════════════════════════════
    #  Corps : sous (x∈S∪{a} et y∈S∪{a}) ⊢ ( x≤'_a y ⇔ h⁺(x)≤'_b h⁺(y) ).
    # ════════════════════════════════════════════════════════════════════════
    prem = et(appartient(vx, SaA), appartient(vy, SaA))
    Hprem = N.assume(prem)
    x_in_SaA = conjonction_elim_gauche(Hprem)         # x∈S∪{a}
    y_in_SaA = conjonction_elim_droite(Hprem)         # y∈S∪{a}

    cible_iff = equiv(le_a(vx, vy), le_b(hpx, hpy))

    # disjonction x∈S ou x=a  ;  y∈S ou y=a
    x_disj = N.modus_ponens(x_in_SaA, equivalence_avant(_membre_adjoint(S, va, vx)))
    y_disj = N.modus_ponens(y_in_SaA, equivalence_avant(_membre_adjoint(S, va, vy)))

    # ── CAS y=a :  les deux côtés sont VRAIS ⇒ iff trivialement (cas commun x∈S/x=a) ──
    def cas_y_eq_a():
        Hya = N.assume(egal(vy, va))                  # y=a
        # GAUCHE : ≤'_a(x,a) VRAI (a sommet de S∪{a}, x∈S∪{a})
        le_a_xa = _adjoint_vers_sommet_vrai(Rf, S, va, vx, x_in_SaA)   # ≤'_a(x,a)
        # transporter en ≤'_a(x,y) via y=a (Leibniz arrière : a→y)
        ya_sym = N.modus_ponens(Hya, symetrie(vy, va))                 # a=y
        le_a_xy = _leib(va, vy, ya_sym, lambda w: le_a(vx, w), le_a_xa)  # ≤'_a(x,y)
        # h⁺(y)=h⁺(a)=b : par y=a transport puis val_a
        hpy_eq_hpa = _leib(va, vy, ya_sym, lambda w: egal(E.valeur(hp, w), vb),
                           val_a)                                      # h⁺(y)=b  [func h,a∉dom h]
        # DROITE : ≤'_b(h⁺(x), b) VRAI (b sommet de T∪{b}, h⁺(x)∈T∪{b})
        #   il faut h⁺(x)∈T∪{b}.  x∈S : h⁺(x)=h(x)∈T⊂T∪{b} ; x=a : h⁺(x)=b∈{b}⊂T∪{b}.
        TbB = V.ensemble_adjoint(T, vb)
        def hpx_in_TbB_from_xS(h_x_in_S):
            hx_in_T = N.modus_ponens(h_x_in_S, instancie(H_into_T, vx))  # h(x)∈T
            # h⁺(x)=h(x)
            x_in_dom = N.modus_ponens(h_x_in_S, instancie(H_S_dom, vx))  # x∈dom h
            vd = N.modus_ponens(x_in_dom, N.loi_deduction(
                appartient(vx, E.dom(hg)), val_dom(vx)))                # h⁺(x)=h(x)
            hpx_in_T = _leib(hx, hpx, N.modus_ponens(vd, symetrie(hpx, hx)),
                             lambda w: appartient(w, T), hx_in_T)       # h⁺(x)∈T
            # h⁺(x)∈T ⇒ h⁺(x)∈T∪{b} (injection gauche)
            car = membre_reunion_graphes(T, E.singleton(vb), hpx)
            return N.modus_ponens(
                N.modus_ponens(hpx_in_T, N.s2(appartient(hpx, T),
                                              appartient(hpx, E.singleton(vb)))),
                equivalence_arriere(car))                              # h⁺(x)∈T∪{b}
        def hpx_in_TbB_from_xa(h_x_eq_a):
            # h⁺(x)=h⁺(a)=b ; b∈{b}⊂T∪{b}
            xa_sym = h_x_eq_a                                          # x=a
            hpx_eq_b = _leib(va, vx, N.modus_ponens(xa_sym, symetrie(vx, va)),
                             lambda w: egal(E.valeur(hp, w), vb), val_a)  # h⁺(x)=b
            b_in_sing = N.modus_ponens(N.reflexivite(vb),
                                       equivalence_arriere(singleton_membre(vb, vb)))  # b∈{b}
            car = membre_reunion_graphes(T, E.singleton(vb), vb)
            b_in_TbB = N.modus_ponens(
                N.modus_ponens(b_in_sing, syllogisme(
                    N.s2(appartient(vb, E.singleton(vb)), appartient(vb, T)),
                    N.s3(appartient(vb, E.singleton(vb)), appartient(vb, T)))),
                equivalence_arriere(car))                              # b∈T∪{b}
            return _leib(vb, hpx, N.modus_ponens(hpx_eq_b, symetrie(hpx, vb)),
                         lambda w: appartient(w, TbB), b_in_TbB)       # h⁺(x)∈T∪{b}
        hpx_in_TbB = cas(x_disj,
                         N.loi_deduction(appartient(vx, S), hpx_in_TbB_from_xS(N.assume(appartient(vx, S)))),
                         N.loi_deduction(egal(vx, va), hpx_in_TbB_from_xa(N.assume(egal(vx, va)))))
        # ≤'_b(h⁺(x), b) VRAI
        le_b_xpb = _adjoint_vers_sommet_vrai(Rpf, T, vb, hpx, hpx_in_TbB)  # ≤'_b(h⁺(x),b)
        # transporter b→h⁺(y) via h⁺(y)=b
        le_b_xy = _leib(vb, hpy, N.modus_ponens(hpy_eq_hpa, symetrie(hpy, vb)),
                        lambda w: le_b(hpx, w), le_b_xpb)             # ≤'_b(h⁺(x),h⁺(y))
        # iff : les deux côtés VRAIS ⇒ chacun implique l'autre (constante)
        fwd = N.loi_deduction(le_a(vx, vy), le_b_xy)                  # ≤'_a ⇒ ≤'_b (≤'_b déjà vrai)
        bwd = N.loi_deduction(le_b(hpx, hpy), le_a_xy)               # ≤'_b ⇒ ≤'_a
        return conjonction_intro(fwd, bwd)                           # iff  [y=a, prem, hyps]

    # ── CAS y∈S :  ≤'_a(x,y)⇔R{x,y}, ≤'_b(h⁺x,h⁺y)⇔Rp{h⁺x,h⁺y} ; sous-cas x∈S / x=a ──
    def cas_y_in_S():
        Hy_S = N.assume(appartient(vy, S))            # y∈S
        yne = y_ne_a(Hy_S)                            # y≠a
        hy_in_T = N.modus_ponens(Hy_S, instancie(H_into_T, vy))   # h(y)∈T
        # h⁺(y)=h(y)
        y_in_dom = N.modus_ponens(Hy_S, instancie(H_S_dom, vy))   # y∈dom h
        vdy = N.modus_ponens(y_in_dom, N.loi_deduction(
            appartient(vy, E.dom(hg)), val_dom(vy)))              # h⁺(y)=h(y)
        # h⁺(y)∈T  (transport)
        hpy_in_T = _leib(hy, hpy, N.modus_ponens(vdy, symetrie(hpy, hy)),
                         lambda w: appartient(w, T), hy_in_T)     # h⁺(y)∈T
        hpy_ne_b = val_ne_b(hpy, hpy_in_T)                        # h⁺(y)≠b
        # ≤'_a(x,y) ⇔ R{x,y}
        red_a = _adjoint_reduit_sous_yne(Rf, S, va, vx, vy, yne)  # ≤'_a(x,y) ⇔ R{x,y}
        # ≤'_b(h⁺x,h⁺y) ⇔ Rp{h⁺x,h⁺y}
        red_b = _adjoint_reduit_sous_yne(Rpf, T, vb, hpx, hpy, hpy_ne_b)  # ≤'_b ⇔ Rp{h⁺x,h⁺y}

        # ── sous-cas x∈S :  R{x,y}⇔Rp{h⁺x,h⁺y} via compat de h + valeurs ─────────
        def sous_x_in_S():
            Hx_S = N.assume(appartient(vx, S))        # x∈S
            x_in_dom = N.modus_ponens(Hx_S, instancie(H_S_dom, vx))  # x∈dom h
            vdx = N.modus_ponens(x_in_dom, N.loi_deduction(
                appartient(vx, E.dom(hg)), val_dom(vx)))             # h⁺(x)=h(x)
            # compat de h instancié (x,y) : (x∈S et y∈S) ⇒ (R{x,y} ⇔ Rp{h(x),h(y)})
            ci = instancie(instancie(H_compat, vx), vy)
            r_equiv_rp = N.modus_ponens(conjonction_intro(Hx_S, Hy_S), ci)  # R{x,y}⇔Rp{h(x),h(y)}
            from bourbaki.logique.tactiques.tactiques_abrege2 import (
                equivalence_transitivite, equivalence_symetrie)
            # transporter red_b : ≤'_b(h⁺x,h⁺y) ⇔ Rp{h⁺x,h⁺y}  en réécrivant les
            #   ARGUMENTS de Rp côté DROIT :  h⁺x→h(x), h⁺y→h(y)  (LHS ≤'_b inchangé).
            rb1 = _leib(hpx, hx, vdx,
                        lambda w: equiv(le_b(hpx, hpy), Rpf(w, hpy)), red_b)   # ⇔ Rp{h(x),h⁺y}
            red_b_T = _leib(hpy, hy, vdy,
                            lambda w: equiv(le_b(hpx, hpy), Rpf(hx, w)), rb1)  # ⇔ Rp{h(x),h(y)}
            # CHAÎNE : ≤'_a(x,y) ⇔ R{x,y} ⇔ Rp{h(x),h(y)} ⇔ ≤'_b(h⁺x,h⁺y).
            chain = equivalence_transitivite(
                equivalence_transitivite(red_a, r_equiv_rp),
                equivalence_symetrie(red_b_T))               # ≤'_a(x,y) ⇔ ≤'_b(h⁺x,h⁺y)
            return chain

        # ── sous-cas x=a :  R{a,y} FAUX (a sommet) et Rp{b,h⁺y} FAUX (b sommet) ──
        def sous_x_eq_a():
            Hxa = N.assume(egal(vx, va))              # x=a
            # ≤'_a(x,y)⇔R{x,y} ; via x=a, R{x,y}=R{a,y} FAUX (a sommet)
            r_a_y_false = N.modus_ponens(Hy_S, instancie(H_a_som, vy))   # ¬R{a,y}
            # transporter ¬R{a,y} → ¬R{x,y} via x=a (arrière a→x)
            xa_sym = N.modus_ponens(Hxa, symetrie(vx, va))               # a=x
            r_x_y_false = _leib(va, vx, xa_sym, lambda w: non(Rf(w, vy)), r_a_y_false)  # ¬R{x,y}
            # côté but : Rp{b, h⁺y}.  h⁺(x)=h⁺(a)=b ; ⇒ Rp{h⁺x,h⁺y}=Rp{b,h⁺y}.
            hpx_eq_b = _leib(va, vx, xa_sym, lambda w: egal(E.valeur(hp, w), vb), val_a)  # h⁺(x)=b
            # ¬Rp{b, h(y)}  (b sommet, h(y)∈T)
            rp_b_hy_false = N.modus_ponens(hy_in_T, instancie(H_b_som, hy))  # ¬Rp{b,h(y)}
            # transporter h(y)→h⁺y :  ¬Rp{b,h(y)} → ¬Rp{b,h⁺y}
            rp_b_hpy_false = _leib(hy, hpy, N.modus_ponens(vdy, symetrie(hpy, hy)),
                                   lambda w: non(Rpf(vb, w)), rp_b_hy_false)  # ¬Rp{b,h⁺y}
            # transporter b→h⁺x :  ¬Rp{b,h⁺y} → ¬Rp{h⁺x,h⁺y}
            rp_hpx_hpy_false = _leib(vb, hpx, N.modus_ponens(hpx_eq_b, symetrie(hpx, vb)),
                                     lambda w: non(Rpf(w, hpy)), rp_b_hpy_false)  # ¬Rp{h⁺x,h⁺y}
            # iff : ≤'_a(x,y) FAUX (⇔R{x,y} FAUX) et ≤'_b(h⁺x,h⁺y) FAUX (⇔Rp{...} FAUX)
            #   ⇒ deux côtés faux ⇒ chacun implique l'autre (ex falso).
            # ≤'_a(x,y) ⇒ R{x,y} (red_a avant) ⇒ ⊥ ⇒ ≤'_b
            le_a_to_R = equivalence_avant(red_a)             # ≤'_a(x,y) ⇒ R{x,y}
            Hle_a = N.assume(le_a(vx, vy))
            Rxy = N.modus_ponens(Hle_a, le_a_to_R)
            falso1 = _ex_falso(Rxy, r_x_y_false, le_b(hpx, hpy))
            fwd = N.loi_deduction(le_a(vx, vy), falso1)      # ≤'_a ⇒ ≤'_b
            le_b_to_Rp = equivalence_avant(red_b)            # ≤'_b(h⁺x,h⁺y) ⇒ Rp{h⁺x,h⁺y}
            Hle_b = N.assume(le_b(hpx, hpy))
            Rphpxy = N.modus_ponens(Hle_b, le_b_to_Rp)
            falso2 = _ex_falso(Rphpxy, rp_hpx_hpy_false, le_a(vx, vy))
            bwd = N.loi_deduction(le_b(hpx, hpy), falso2)    # ≤'_b ⇒ ≤'_a
            return conjonction_intro(fwd, bwd)               # iff

        return cas(x_disj,
                   N.loi_deduction(appartient(vx, S), sous_x_in_S()),
                   N.loi_deduction(egal(vx, va), sous_x_eq_a()))

    iff_body = cas(y_disj,
                   N.loi_deduction(appartient(vy, S), cas_y_in_S()),
                   N.loi_deduction(egal(vy, va), cas_y_eq_a()))   # iff [prem, hyps]

    body_imp = N.loi_deduction(prem, iff_body)        # (x∈SaA et y∈SaA) ⇒ iff
    res = N.generalisation("xa", N.generalisation("ya", body_imp))   # compatible_ordre(h⁺,…)[τy]
    # PONT y→j : la cible compatible_ordre(h⁺,…) (fonction) écrit h⁺(·) en « j » ; le corps
    # est prouvé en « y ».  On convertit y→j (xa,ya plaines) pour matcher.
    return pont_compatible(res, hp, SaA, le_a, le_b, "xa", "ya", "y2j")


def compat_extension_cible(E_set="E", R="R", F_set="F", Rp="Rp", a="a", b="b"):
    """ÉNONCÉ-cible (test miroir) :  compatible_ordre(h⁺, S∪{a}, ≤'_a, ≤'_b)."""
    S = _seg_S(R, E_set, a)
    hp = _hplus(E_set, R, F_set, Rp, a, b)
    return V.compatible_ordre(hp, V.ensemble_adjoint(S, _t(a)),
                              _le_a(R, E_set, a), _le_b(Rp, F_set, b), x="xa", y="ya")


# ════════════════════════════════════════════════════════════════════════════
#  (A) BIJECTION de h⁺ — injectivité.
#  ✅ point_graphe_injectif : ⊢ injective_dans({(a,b)}, dom{(a,b)}).  INCONDITIONNEL.
# ════════════════════════════════════════════════════════════════════════════
def point_graphe_injectif(a="a", b="b"):
    """⊢ injective_dans( {(a,b)}, dom({(a,b)}) ).

    Le graphe ponctuel {(a,b)} est injectif sur son domaine {a} : pour u,u'∈dom{(a,b)}
    avec {(a,b)}(u)={(a,b)}(u'), comme dom{(a,b)}={a}, u=a=u'.  INCONDITIONNEL,
    theorie=22.  Brique d'injectivité du recollement h⁺.  NON vacueux."""
    va, vb = _t(a), _t(b)
    G = A.graphe_point(va, vb)
    domG = E.dom(G)
    Sa = E.singleton(va)
    dom_eq = A.dom_singleton_couple(a, b)                 # dom({(a,b)}) = {a}
    vu, vup = var("u"), var("up")
    fu, fup = E.valeur(G, vu), E.valeur(G, vup)
    # hypothèse principale de injective_dans : (u∈domG et u'∈domG) et G(u)=G(u')
    hyp = et(et(appartient(vu, domG), appartient(vup, domG)), egal(fu, fup))
    Hyp = N.assume(hyp)
    u_in_domG = conjonction_elim_gauche(conjonction_elim_gauche(Hyp))    # u∈domG
    up_in_domG = conjonction_elim_droite(conjonction_elim_gauche(Hyp))   # u'∈domG
    # u∈{a} ⇒ u=a  (réécrire domG={a})
    u_in_sa = _leib(domG, Sa, dom_eq, lambda w: appartient(vu, w), u_in_domG)   # u∈{a}
    up_in_sa = _leib(domG, Sa, dom_eq, lambda w: appartient(vup, w), up_in_domG) # u'∈{a}
    u_eq_a = N.modus_ponens(u_in_sa, equivalence_avant(singleton_membre(vu, va)))   # u=a
    up_eq_a = N.modus_ponens(up_in_sa, equivalence_avant(singleton_membre(vup, va)))# u'=a
    # u=u' : u=a et u'=a ⇒ u=a=u'
    a_eq_up = N.modus_ponens(up_eq_a, symetrie(vup, va))    # a=u'
    u_eq_up = composer_egalites(u_eq_a, a_eq_up)            # u=u'
    body = N.loi_deduction(hyp, u_eq_up)
    res = N.generalisation("u", N.generalisation("up", body))
    assert res.conclusion == E.injective_dans(G, domG)
    return res


def point_graphe_injectif_cible(a="a", b="b"):
    """ÉNONCÉ-cible (test miroir) :  injective_dans({(a,b)}, dom({(a,b)}))."""
    G = A.graphe_point(a, b)
    return E.injective_dans(G, E.dom(G))


def hyp_dom_h_egale_S(E_set="E", R="R", F_set="F", Rp="Rp", a="a"):
    """dom(h) = S   [S=seg(R,E,a)] — hypothèse explicite : h est l'application de
    domaine S.  VRAIE car h:S≅T est définie exactement sur S."""
    from bourbaki.cardinaux import ensembles_trichotomie_scaffold as TS
    hg = TS.h_iso_max(E_set, R, F_set, Rp)
    return egal(E.dom(hg), _seg_S(R, E_set, a))


def hyp_h_injective_sur_S(E_set="E", R="R", F_set="F", Rp="Rp", a="a"):
    """injective_dans(h, dom h)   [h injective sur son domaine S].

    PROJECTION GAUCHE de est_bijective(h,S,T) (modulo dom h=S) ; hypothèse explicite."""
    from bourbaki.cardinaux import ensembles_trichotomie_scaffold as TS
    hg = TS.h_iso_max(E_set, R, F_set, Rp)
    return E.injective_dans(hg, E.dom(hg))


def hyp_images_disjointes(E_set="E", R="R", F_set="F", Rp="Rp", a="a", b="b"):
    """image(h, dom h) ∩ image({(a,b)}, dom{(a,b)}) = ∅   [images disjointes].

    VRAIE car image(h,S)=T, image({(a,b)},{a})={b}, et b∉T (b sommet, point_pas_dans
    _son_segment) ⇒ T∩{b}=∅ ; hypothèse explicite encodant « b frais »."""
    from bourbaki.cardinaux import ensembles_trichotomie_scaffold as TS
    hg = TS.h_iso_max(E_set, R, F_set, Rp)
    G = A.graphe_point(a, b)
    return egal(E.intersection(E.image(hg, E.dom(hg)), E.image(G, E.dom(G))), E.VIDE)


# ════════════════════════════════════════════════════════════════════════════
#  ⚠️ injectivite_extension_sous : injective_dans(h⁺, S∪{a}).  CONDITIONNEL.
# ════════════════════════════════════════════════════════════════════════════
def injectivite_extension_sous(E_set="E", R="R", F_set="F", Rp="Rp", a="a", b="b"):
    """⊢ { func(h),  a∉dom h,  injective_dans(h, dom h),  images disjointes,  dom h=S }
            ⊢ injective_dans( h⁺,  S∪{a} ).

    🎯 RECOLLEMENT INJECTIF (maillon A, injectivité) : h⁺=h∪{(a,b)} est injectif sur
    S∪{a} car h est injectif sur S, {(a,b)} l'est sur {a}, domaines disjoints (a∉dom h),
    et leurs images (T et {b}) sont disjointes (b frais).  Via reunion_graphes_injective
    + dom h=S + dom{(a,b)}={a}.  CONDITIONNEL aux hypothèses EXPLICITES — JAMAIS postulé.
    theorie=22.  NON vacueux."""
    from bourbaki.cardinaux import ensembles_trichotomie_scaffold as TS
    va, vb = _t(a), _t(b)
    hg = TS.h_iso_max(E_set, R, F_set, Rp)
    G = A.graphe_point(va, vb)
    domh, domG = E.dom(hg), E.dom(G)
    Sa = E.singleton(va)
    S = _seg_S(R, E_set, a)

    # reunion_graphes_injective(hg, G) : 6 hyps ⊢ injective_dans(h⁺, domh∪domG)
    rgi = reunion_graphes_injective(hg, G)
    # décharger : func G (INCOND), point inj G (INCOND), disjonction (sous a∉dom h)
    func_G = A.singleton_couple_fonctionnel(va, vb)               # func {(a,b)}
    inj_G = point_graphe_injectif(va, vb)                         # inj {(a,b)} sur dom
    disj = A.disjonction_domaines_sous_a_hors(E_set, R, F_set, Rp, a, b)   # [a∉dom h]
    disj_form = pourtout("u", non(et(appartient(var("u"), domh),
                                     appartient(var("u"), domG))))
    rgi = N.modus_ponens(func_G, N.loi_deduction(E.est_fonctionnel(G), rgi))
    rgi = N.modus_ponens(inj_G, N.loi_deduction(E.injective_dans(G, domG), rgi))
    rgi = N.modus_ponens(disj, N.loi_deduction(disj_form, rgi))
    # restent en hyp : func h, inj h sur dom h, images disjointes, a∉dom h.
    # rgi : injective_dans(h⁺, domh ∪ domG)

    # transporter domG → {a}  (dom_singleton_couple)
    domG_eq_sa = A.dom_singleton_couple(a, b)                     # domG = {a}
    rgi = _leib(domG, Sa, domG_eq_sa,
                lambda w: E.injective_dans(E.reunion(hg, G), E.reunion(domh, w)), rgi)
    # transporter domh → S  (hypothèse dom h=S)
    Hdom = N.assume(hyp_dom_h_egale_S(E_set, R, F_set, Rp, a))    # dom h = S
    rgi = _leib(domh, S, Hdom,
                lambda w: E.injective_dans(E.reunion(hg, G), E.reunion(w, Sa)), rgi)
    # rgi : injective_dans(h⁺, S∪{a})
    return rgi


def injectivite_extension_cible(E_set="E", R="R", F_set="F", Rp="Rp", a="a", b="b"):
    """ÉNONCÉ-cible (test miroir) :  injective_dans(h⁺, S∪{a})."""
    S = _seg_S(R, E_set, a)
    hp = _hplus(E_set, R, F_set, Rp, a, b)
    return E.injective_dans(hp, V.ensemble_adjoint(S, _t(a)))


# ════════════════════════════════════════════════════════════════════════════
#  (A) BIJECTION de h⁺ — surjectivité.
#  ✅ image_point_graphe : ⊢ image({(a,b)}, {a}) = {b}.  INCONDITIONNEL.
# ════════════════════════════════════════════════════════════════════════════
def image_point_graphe(a="a", b="b", y="z"):
    """⊢ image( {(a,b)},  {a} ) = {b}.

    L'image directe du graphe ponctuel {(a,b)} par son domaine {a} est {b} :
      y∈image({(a,b)},{a}) ⇔ (∃x)(x∈{a} et (x,y)∈{(a,b)}) ⇔ y=b ⇔ y∈{b}.
    Double inclusion + extensionnalité A1.  INCONDITIONNEL, theorie=22.  NON vacueux."""
    from bourbaki.logique.tactiques.tactiques_abrege_quantif import existe_elimination
    from bourbaki.ensembles.ii_2_couples_produit.ensembles_couples import couple_egal_implique_composantes
    from bourbaki.logique.tactiques.tactiques_abrege_egalite import congruence_terme
    va, vb = _t(a), _t(b)
    ab = E.couple(va, vb)
    G = A.graphe_point(va, vb)
    Sa = E.singleton(va)
    Sb = E.singleton(vb)
    imgGa = E.image(G, Sa)
    vy = var(y)
    vx = var("x")

    ax_img = N.axiome(E.theorie_ensembles(), E.AXIOME_IMAGE)
    car = instancie(instancie(instancie(ax_img, G), Sa), vy)   # y∈imgGa ⇔ (∃x)(x∈{a} et (x,y)∈G)
    mem_b = singleton_membre(vy, vb)                           # y∈{b} ⇔ y=b

    # ── ⇒ : y∈imgGa ⇒ y∈{b} ──
    Hy = N.assume(appartient(vy, imgGa))
    ex_x = N.modus_ponens(Hy, equivalence_avant(car))         # (∃x)(x∈{a} et (x,y)∈G)
    body = et(appartient(vx, Sa), appartient(E.couple(vx, vy), G))
    Hbody = N.assume(body)
    xy_in_G = conjonction_elim_droite(Hbody)                  # (x,y)∈G
    xy_eq_ab = N.modus_ponens(xy_in_G, equivalence_avant(singleton_membre(E.couple(vx, vy), ab)))  # (x,y)=(a,b)
    y_eq_b = conjonction_elim_droite(N.modus_ponens(
        xy_eq_ab, couple_egal_implique_composantes(vx, vy, va, vb)))   # y=b
    y_in_sb = N.modus_ponens(y_eq_b, equivalence_arriere(mem_b))       # y∈{b}
    imp = existe_elimination(N.loi_deduction(body, y_in_sb), "x")      # (∃x)body ⇒ y∈{b}
    fwd = N.loi_deduction(appartient(vy, imgGa), N.modus_ponens(ex_x, imp))
    incl_L = N.generalisation(y, fwd)

    # ── ⇐ : y∈{b} ⇒ y∈imgGa ──
    Hyb = N.assume(appartient(vy, Sb))
    y_eq_b2 = N.modus_ponens(Hyb, equivalence_avant(mem_b))    # y=b
    # a∈{a}
    a_in_sa = N.modus_ponens(N.reflexivite(va),
                             equivalence_arriere(singleton_membre(va, va)))   # a∈{a}
    # (a,b)∈{(a,b)}
    ab_in_G = N.modus_ponens(N.reflexivite(ab),
                             equivalence_arriere(singleton_membre(ab, ab)))   # (a,b)∈G
    # (a,y)∈G via y=b : (a,y)=(a,b) ⇒ (a,y)∈G  ; congruence terme sur 2ᵉ coord
    ay_eq_ab = N.modus_ponens(y_eq_b2, congruence_terme(vy, vb, E.couple(va, var("w"))))  # (a,y)=(a,b)
    ay_in_G = N.modus_ponens(ay_eq_ab, equivalence_arriere(singleton_membre(E.couple(va, vy), ab)))  # (a,y)∈G
    body_ay = et(appartient(va, Sa), appartient(E.couple(va, vy), G))
    body_proof = conjonction_intro(a_in_sa, ay_in_G)         # a∈{a} et (a,y)∈G
    ex_ay = N.modus_ponens(body_proof, N.s5(
        et(appartient(vx, Sa), appartient(E.couple(vx, vy), G)), va, "x"))   # (∃x)(x∈{a} et (x,y)∈G)
    y_in_img = N.modus_ponens(ex_ay, equivalence_arriere(car))   # y∈imgGa
    bwd = N.loi_deduction(appartient(vy, Sb), y_in_img)
    incl_R = N.generalisation(y, bwd)

    a1 = instancie(instancie(N.axiome(E.theorie_ensembles(), E.A1), imgGa), Sb)
    return N.modus_ponens(conjonction_intro(incl_L, incl_R), a1)   # imgGa = {b}


def image_point_graphe_cible(a="a", b="b"):
    """ÉNONCÉ-cible (test miroir) :  image({(a,b)}, {a}) = {b}."""
    G = A.graphe_point(a, b)
    return egal(E.image(G, E.singleton(_t(a))), E.singleton(_t(b)))


def hyp_h_surjective_sur_S(E_set="E", R="R", F_set="F", Rp="Rp", a="a", b="b"):
    """est_surjective(h, S, T)   [image(h,S)=T : h surjecte S sur T].

    PROJECTION DROITE de est_bijective(h,S,T) ; hypothèse explicite."""
    from bourbaki.cardinaux import ensembles_trichotomie_scaffold as TS
    hg = TS.h_iso_max(E_set, R, F_set, Rp)
    return E.est_surjective(hg, _seg_S(R, E_set, a), _seg_T(Rp, F_set, b))


# ════════════════════════════════════════════════════════════════════════════
#  ⚠️ surjectivite_extension_sous : est_surjective(h⁺, S∪{a}, T∪{b}).  CONDITIONNEL.
# ════════════════════════════════════════════════════════════════════════════
def surjectivite_extension_sous(E_set="E", R="R", F_set="F", Rp="Rp", a="a", b="b"):
    """⊢ { dom h = S,  est_surjective(h, S, T) }
            ⊢ est_surjective( h⁺,  S∪{a},  T∪{b} ).

    🎯 RECOLLEMENT SURJECTIF (maillon A, surjectivité) : image(h⁺, S∪{a}) =
    image(h, S) ∪ image({(a,b)}, {a}) = T ∪ {b}  (image_reunion_graphes CLOS +
    dom h=S + dom{(a,b)}={a} + image(h,S)=T + image({(a,b)},{a})={b}).  CONDITIONNEL aux
    hypothèses EXPLICITES — JAMAIS postulé.  theorie=22.  NON vacueux."""
    from bourbaki.cardinaux import ensembles_trichotomie_scaffold as TS
    va, vb = _t(a), _t(b)
    hg = TS.h_iso_max(E_set, R, F_set, Rp)
    G = A.graphe_point(va, vb)
    domh, domG = E.dom(hg), E.dom(G)
    Sa, Sb = E.singleton(va), E.singleton(vb)
    S = _seg_S(R, E_set, a)
    T = _seg_T(Rp, F_set, b)
    hp = E.reunion(hg, G)
    SaA = V.ensemble_adjoint(S, va)             # S∪{a}
    TbB = V.ensemble_adjoint(T, vb)             # T∪{b}

    # image_reunion_graphes : image(h⁺, domh∪domG) = image(h,domh) ∪ image(G,domG)  (CLOS)
    irg = image_reunion_graphes(hg, G)
    # ── transporter LHS : domh→S, domG→{a} ────────────────────────────────────
    Hdom = N.assume(hyp_dom_h_egale_S(E_set, R, F_set, Rp, a))    # dom h = S
    domG_eq_sa = A.dom_singleton_couple(a, b)                     # domG = {a}
    # LHS : image(h⁺, domh∪domG)
    irg = _leib(domh, S, Hdom,
                lambda w: egal(E.image(hp, E.reunion(w, domG)),
                               E.reunion(E.image(hg, w), E.image(G, domG))), irg)
    irg = _leib(domG, Sa, domG_eq_sa,
                lambda w: egal(E.image(hp, E.reunion(S, w)),
                               E.reunion(E.image(hg, S), E.image(G, w))), irg)
    # irg : image(h⁺, S∪{a}) = image(h,S) ∪ image(G,{a})
    # ── transporter RHS : image(h,S)→T (hyp surj), image(G,{a})→{b} (lemme) ────
    Hsurj = N.assume(hyp_h_surjective_sur_S(E_set, R, F_set, Rp, a, b))   # image(h,S)=T
    irg = _leib(E.image(hg, S), T, Hsurj,
                lambda w: egal(E.image(hp, E.reunion(S, Sa)),
                               E.reunion(w, E.image(G, Sa))), irg)
    img_pt = image_point_graphe(a, b)                            # image(G,{a})={b}
    irg = _leib(E.image(G, Sa), Sb, img_pt,
                lambda w: egal(E.image(hp, E.reunion(S, Sa)),
                               E.reunion(T, w)), irg)
    # irg : image(h⁺, S∪{a}) = T∪{b}   = est_surjective(h⁺, S∪{a}, T∪{b})
    assert irg.conclusion == E.est_surjective(hp, SaA, TbB)
    return irg


def surjectivite_extension_cible(E_set="E", R="R", F_set="F", Rp="Rp", a="a", b="b"):
    """ÉNONCÉ-cible (test miroir) :  est_surjective(h⁺, S∪{a}, T∪{b})."""
    S = _seg_S(R, E_set, a)
    T = _seg_T(Rp, F_set, b)
    hp = _hplus(E_set, R, F_set, Rp, a, b)
    return E.est_surjective(hp, V.ensemble_adjoint(S, _t(a)),
                            V.ensemble_adjoint(T, _t(b)))


# ════════════════════════════════════════════════════════════════════════════
#  (A) BIJECTION de h⁺ : S∪{a} → T∪{b}  =  injectivité ET surjectivité.
# ════════════════════════════════════════════════════════════════════════════
def bijection_extension_sous(E_set="E", R="R", F_set="F", Rp="Rp", a="a", b="b"):
    """⊢ { func(h),  a∉dom h,  injective_dans(h, dom h),  images disjointes,
           dom h=S,  est_surjective(h, S, T) }
            ⊢ est_bijective( h⁺,  S∪{a},  T∪{b} ).

    🎯 MAILLON A : h⁺ est BIJECTIVE de S∪{a} sur T∪{b} (injectivité + surjectivité,
    conjonction des deux pièces de recollement).  CONDITIONNEL aux hypothèses
    EXPLICITES — JAMAIS postulé.  theorie=22.  NON vacueux."""
    inj = injectivite_extension_sous(E_set, R, F_set, Rp, a, b)   # injective_dans(h⁺, S∪{a})
    surj = surjectivite_extension_sous(E_set, R, F_set, Rp, a, b) # est_surjective(h⁺, S∪{a}, T∪{b})
    return conjonction_intro(inj, surj)                          # est_bijective(h⁺, S∪{a}, T∪{b})


def bijection_extension_cible(E_set="E", R="R", F_set="F", Rp="Rp", a="a", b="b"):
    """ÉNONCÉ-cible (test miroir) :  est_bijective(h⁺, S∪{a}, T∪{b})."""
    S = _seg_S(R, E_set, a)
    T = _seg_T(Rp, F_set, b)
    hp = _hplus(E_set, R, F_set, Rp, a, b)
    return E.est_bijective(hp, V.ensemble_adjoint(S, _t(a)),
                           V.ensemble_adjoint(T, _t(b)))


# ════════════════════════════════════════════════════════════════════════════
#  🎯 ASSEMBLAGE — extension_est_iso_segments : h⁺ EST un iso d'ordre.
#     CLÔT temoin_est_iso_segments_report (modulo h iso) — la conclusion EXACTE.
# ════════════════════════════════════════════════════════════════════════════
def extension_est_iso_segments(E_set="E", R="R", F_set="F", Rp="Rp", a="a", b="b"):
    """🎯 ⊢ { hypothèses structurelles explicites — voir extension_hypotheses }
            ⊢ est_isomorphisme_ordre( h⁺,  S∪{a},  T∪{b},  ≤'_a,  ≤'_b ).

    L'EXTENSION-ISO de l'adjonction du sommet : h⁺=h∪{(a,b)} est un ISO D'ORDRE de
    ]←,a]=S∪{a} sur ]←,b]=T∪{b} pour les ordres adjoints, SACHANT que h:S≅T est iso
    de segments et que a/b sont les sommets.  Conjonction de :
      (A) bijection_extension_sous   (h⁺ bijective S∪{a}→T∪{b}) ;
      (B) compat_extension_sous_iso  (h⁺ compatible pour relation_adjoint).

    Conclusion EXACTEMENT égale à temoin_est_iso_segments_report (avec h=h_iso_max) :
    ce module FERME ce report, modulo les hypothèses EXPLICITES « h iso de S sur T »
    et « a,b sommets ».  CONDITIONNEL — JAMAIS postulé.  theorie=22.  NON vacueux."""
    bij = bijection_extension_sous(E_set, R, F_set, Rp, a, b)     # est_bijective(h⁺,…)
    compat = compat_extension_sous_iso(E_set, R, F_set, Rp, a, b) # compatible_ordre(h⁺,…)
    return conjonction_intro(bij, compat)


def extension_est_iso_segments_cible(E_set="E", R="R", F_set="F", Rp="Rp", a="a", b="b"):
    """ÉNONCÉ-cible : est_isomorphisme_ordre(h⁺, S∪{a}, T∪{b}, ≤'_a, ≤'_b),
    avec binders « xa »/« ya » CAPTURE-FREE pour compatible_ordre.

    ⚠️ NUANCE DE FIDÉLITÉ (importante, honnête).  temoin_est_iso_segments_report appelle
    est_isomorphisme_ordre avec les binders PAR DÉFAUT x='x', y='y' ; or compatible_ordre
    y forme valeur(f,y) = τy((y,y)∈f), dont le « y » est CAPTURÉ par le τ interne
    (valeur(f,·,b='y')) — la sous-formule f(x)/f(y) y est DÉCOUPLÉE du quantificateur.
    Le report tel qu'écrit est donc MALFORMÉ sur ce point (bug latent de binder de
    est_isomorphisme_ordre/compatible_ordre quand y='y').  CE module prouve la version
    CORRECTE (capture-free, binders xa/ya), qui est l'INTENTION du report.  On NE prétend
    PAS l'égalité littérale avec le report malformé : on prouve l'énoncé CORRECT."""
    S = _seg_S(R, E_set, a)
    T = _seg_T(Rp, F_set, b)
    hp = _hplus(E_set, R, F_set, Rp, a, b)
    return V.est_isomorphisme_ordre(hp, V.ensemble_adjoint(S, _t(a)),
                                    V.ensemble_adjoint(T, _t(b)),
                                    _le_a(R, E_set, a), _le_b(Rp, F_set, b),
                                    x="xa", y="ya")


def extension_hypotheses(E_set="E", R="R", F_set="F", Rp="Rp", a="a", b="b"):
    """Les HYPOTHÈSES EXPLICITES (liste de formules) de extension_est_iso_segments —
    encodant « h iso de S sur T » + « a,b sommets » + structure de l'application :

      [ est_fonctionnel(h),  a∉dom h,
        injective_dans(h, dom h),  images disjointes,  dom h=S,  est_surjective(h,S,T),
        compatible_ordre(h,S,R,Rp),  h⟨S⟩⊂T,  S⊂dom h,
        a sommet de S,  b sommet de T ].

    (Toutes VRAIES sous est_isomorphisme_ordre(h,S,T,R,Rp) + a=min(E∖S), b=min(F∖T) ;
     leur PRODUCTION effective depuis le bon ordre est la part Cantor–Bernstein
     REPORTÉE.)"""
    from bourbaki.cardinaux import ensembles_trichotomie_scaffold as TS
    hg = TS.h_iso_max(E_set, R, F_set, Rp)
    return [
        E.est_fonctionnel(hg),
        non(appartient(_t(a), E.dom(hg))),
        hyp_h_injective_sur_S(E_set, R, F_set, Rp, a),
        hyp_images_disjointes(E_set, R, F_set, Rp, a, b),
        hyp_dom_h_egale_S(E_set, R, F_set, Rp, a),
        hyp_h_surjective_sur_S(E_set, R, F_set, Rp, a, b),
        hyp_compat_h(E_set, R, F_set, Rp, a, b),
        hyp_h_envoie_S_dans_T(E_set, R, F_set, Rp, a, b),
        hyp_S_inclus_dom_h(E_set, R, F_set, Rp, a),
        hyp_a_sommet_de_S(R, E_set, a),
        hyp_b_sommet_de_T(Rp, F_set, b),
    ]


# ════════════════════════════════════════════════════════════════════════════
#  CONSOLIDATION — l'iso de segments CAPTURE-FREE comme HYPOTHÈSE UNIQUE.
#  Réduit compat_h / surj / inj-sur-S à la SEULE hypothèse « h iso de S sur T ».
# ════════════════════════════════════════════════════════════════════════════
def iso_segments_capture_free(E_set="E", R="R", F_set="F", Rp="Rp", a="a", b="b"):
    """est_isomorphisme_ordre(h, S, T, R, Rp)  —  binders CAPTURE-FREE « xc »/« yc ».

    L'HYPOTHÈSE CENTRALE « h est un iso d'ordre du segment S=seg(R,E,a) sur le segment
    T=seg(Rp,F,b) », sous la forme CORRECTE (sans capture du « y » par valeur).
    Elle CONTIENT : injective_dans(h,S), est_surjective(h,S,T), compatible_ordre(h,S,R,Rp)."""
    from bourbaki.cardinaux import ensembles_trichotomie_scaffold as TS
    Rf, Rpf = _R_de(R), _R_de(Rp)
    hg = TS.h_iso_max(E_set, R, F_set, Rp)
    return V.est_isomorphisme_ordre(hg, _seg_S(R, E_set, a), _seg_T(Rp, F_set, b),
                                    Rf, Rpf, x="xc", y="yc")


def extension_iso_depuis_iso_h(E_set="E", R="R", F_set="F", Rp="Rp", a="a", b="b"):
    """🎯 ⊢ { est_isomorphisme_ordre(h,S,T,R,Rp) [capture-free],  func h,  a∉dom h,
             dom h=S,  images disjointes,  h⟨S⟩⊂T,  S⊂dom h,  a sommet S,  b sommet T }
            ⊢ est_isomorphisme_ordre( h⁺,  S∪{a},  T∪{b},  ≤'_a,  ≤'_b ).

    VARIANTE CONSOLIDÉE de extension_est_iso_segments : on REMPLACE les trois
    hypothèses-projections (compatible_ordre, est_surjective, injective_dans) par la
    SEULE hypothèse « h iso de S sur T » (capture-free), dont elles sont des
    projections (inj via dom h=S).  C'est la forme la plus proche de l'argument de
    maximalité : « h iso de segments ⇒ h⁺ iso de segments adjoints ».
    CONDITIONNEL — JAMAIS postulé.  theorie=22.  NON vacueux."""
    from bourbaki.cardinaux import ensembles_trichotomie_scaffold as TS
    from bourbaki.logique.tactiques.tactiques_abrege2 import (
        conjonction_elim_gauche as cg, conjonction_elim_droite as cd)
    va = _t(a)
    hg = TS.h_iso_max(E_set, R, F_set, Rp)
    S = _seg_S(R, E_set, a)

    # partir de l'assemblage à 11 hyps
    base = extension_est_iso_segments(E_set, R, F_set, Rp, a, b)

    # ── décharger hyp_compat_h, hyp_h_surjective_sur_S depuis l'iso ───────────
    Hiso = N.assume(iso_segments_capture_free(E_set, R, F_set, Rp, a, b))
    bij = cg(Hiso)                                  # est_bijective(h,S,T)
    compat = cd(Hiso)                               # compatible_ordre(h,S,R,Rp)  = hyp_compat_h
    inj_S = cg(bij)                                 # injective_dans(h,S)
    surj = cd(bij)                                  # est_surjective(h,S,T)       = hyp_h_surjective_sur_S
    # inj sur dom h : transporter injective_dans(h,S) → injective_dans(h,dom h) via dom h=S
    Hdom = N.assume(hyp_dom_h_egale_S(E_set, R, F_set, Rp, a))   # dom h=S
    dom_eq_S_sym = N.modus_ponens(Hdom, symetrie(E.dom(hg), S))  # S=dom h
    inj_domh = _leib(S, E.dom(hg), dom_eq_S_sym,
                     lambda w: E.injective_dans(hg, w), inj_S)   # injective_dans(h,dom h)

    out = base
    out = N.modus_ponens(compat, N.loi_deduction(hyp_compat_h(E_set, R, F_set, Rp, a, b), out))
    out = N.modus_ponens(surj, N.loi_deduction(hyp_h_surjective_sur_S(E_set, R, F_set, Rp, a, b), out))
    out = N.modus_ponens(inj_domh, N.loi_deduction(hyp_h_injective_sur_S(E_set, R, F_set, Rp, a), out))
    # dom h=S est ENCORE requis (par inj_domh ET base) : il reste en hypothèse via Hdom.
    return out


def extension_iso_depuis_iso_h_hypotheses(E_set="E", R="R", F_set="F", Rp="Rp", a="a", b="b"):
    """Les HYPOTHÈSES EXPLICITES (liste) de extension_iso_depuis_iso_h."""
    from bourbaki.cardinaux import ensembles_trichotomie_scaffold as TS
    hg = TS.h_iso_max(E_set, R, F_set, Rp)
    return [
        iso_segments_capture_free(E_set, R, F_set, Rp, a, b),
        E.est_fonctionnel(hg),
        non(appartient(_t(a), E.dom(hg))),
        hyp_dom_h_egale_S(E_set, R, F_set, Rp, a),
        hyp_images_disjointes(E_set, R, F_set, Rp, a, b),
        hyp_h_envoie_S_dans_T(E_set, R, F_set, Rp, a, b),
        hyp_S_inclus_dom_h(E_set, R, F_set, Rp, a),
        hyp_a_sommet_de_S(R, E_set, a),
        hyp_b_sommet_de_T(Rp, F_set, b),
    ]


__all__ = [
    # helpers de relations / termes
    "iso_segments_capture_free",
    # hypothèses explicites (formules)
    "hyp_h_envoie_S_dans_T", "hyp_S_inclus_dom_h",
    "hyp_a_sommet_de_S", "hyp_b_sommet_de_T", "hyp_compat_h",
    "hyp_dom_h_egale_S", "hyp_h_injective_sur_S", "hyp_images_disjointes",
    "hyp_h_surjective_sur_S",
    # (B) compatibilité d'ordre
    "compat_extension_sous_iso", "compat_extension_cible",
    # (A) bijection — pièces inconditionnelles
    "point_graphe_injectif", "point_graphe_injectif_cible",
    "image_point_graphe", "image_point_graphe_cible",
    # (A) bijection — conditionnels
    "injectivite_extension_sous", "injectivite_extension_cible",
    "surjectivite_extension_sous", "surjectivite_extension_cible",
    "bijection_extension_sous", "bijection_extension_cible",
    # assemblage
    "extension_est_iso_segments", "extension_est_iso_segments_cible",
    "extension_hypotheses",
    "extension_iso_depuis_iso_h", "extension_iso_depuis_iso_h_hypotheses",
]
