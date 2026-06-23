"""§III.2 — Théorème 3 (TRICHOTOMIE) : TÉMOIN ISO-DE-SEGMENTS par ADJONCTION.

────────────────────────────────────────────────────────────────────────────────
RÔLE — le maillon (i) du HARD RÉSIDU (cf. memory/n-bien-ordre-route.md, blueprint
DESIGN_trichotomie_III2.md étape d.5).  L'argument de MAXIMALITÉ de l'iso maximal
h (= h_iso_max, union des graphes d'iso de couples de segments isomorphes) suppose :
si dom(h)=seg(R,E,a)=]←,a[ et pr₂(h)=seg(Rp,F,b)=]←,b[ sont des segments PROPRES
(a=min(E∖dom h), b=min(F∖pr₂ h)), alors h SE PROLONGE en un iso d'ordre de
]←,a]=seg∪{a} sur ]←,b]=seg∪{b}, contredisant la maximalité (h contient TOUS les
isos de segments).  Le prolongement est :

    h⁺ := h ∪ {(a,b)}     (recollement de h et du graphe singleton {(a,b)}).

C'est l'ADJONCTION DU PLUS GRAND ÉLÉMENT (relation_adjoint, E.III.1.8) : a au sommet
de S∪{a}, b au sommet de T∪{b}, h⁺ envoie a sur b et coïncide avec h ailleurs.
C'est la MAGNITUDE Cantor–Bernstein ; SALVAGE FORT GRADUÉ : on PROUVE les morceaux
ATTEIGNABLES (a au sommet ; {(a,b)} fonctionnel ; (a,b)∈h⁺ ; h⊂h⁺ ; a∈dom{(a,b)} ;
h⁺ fonctionnel sous a∉dom h ; valeurs de h⁺) et on REPORTE le cœur d'ordre/surjection
avec hypothèses EXPLICITES, JAMAIS postulé.

────────────────────────────────────────────────────────────────────────────────
CE MODULE LIVRE (salvage fort gradué, honnête, theorie=22) :

  ✅ INCONDITIONNEL (theorie=22) :
     • temoin_adjonction(E,R,F,Rp,a,b) := h ∪ {(a,b)} — le TERME de prolongement
       (recollement de h et du graphe singleton {(a,b)}, AUCUN axiome nouveau).
     • a_est_plus_grand_dans_adjoint : ⊢ est_plus_grand_element(≤'_a, S∪{a}, a),
       ≤'_a = relation_adjoint(R,S,a).  a EST le plus grand de l'adjonction S∪{a}.
       (Le CONTENU LITTÉRAL « a au sommet » de l'adjonction du plus grand élément.)
     • singleton_couple_fonctionnel : ⊢ est_fonctionnel({(a,b)}).
       (Le graphe singleton {(a,b)} est fonctionnel : une seule valeur b en a.)
     • couple_dans_temoin           : ⊢ (a,b) ∈ h⁺.        (h⁺ apparie bien a↦b.)
     • h_inclus_temoin              : ⊢ (∀z)( z∈h ⇒ z∈h⁺ ).  (h⁺ PROLONGE h.)
     • a_dans_dom_singleton_couple  : ⊢ a ∈ dom({(a,b)}).   (a antécédent de {(a,b)}.)
     • dom_singleton_couple         : ⊢ dom({(a,b)}) = {a}. (domaine du graphe point.)

  ⚠️ CONDITIONNEL — hypothèse EXPLICITE « a∉dom h » (VRAIE car a=min(E∖dom h)) :
     • disjonction_domaines_sous_a_hors : { a∉dom h } ⊢ (∀u)¬(u∈dom h et u∈dom{(a,b)}).
     • temoin_fonctionnel_sous_a_hors   : { a∉dom h, est_fonctionnel(h) } ⊢ est_fonctionnel(h⁺).
       (h⁺ fonctionnel par recollement à domaines disjoints — reunion_graphes_fonctionnelle.)
     • valeur_temoin_en_a_sous_a_hors   : { a∉dom h, est_fonctionnel(h) } ⊢ valeur(h⁺,a)=b.
       (h⁺(a)=b : a∈dom{(a,b)} ⇒ valeur_reunion_droite.)
     • valeur_temoin_sur_dom_h_sous     : { a∉dom h, est_fonctionnel(h), u∈dom h }
                                          ⊢ valeur(h⁺,u)=valeur(h,u).
       (h⁺ coïncide avec h sur dom h — valeur_reunion_gauche.)

  ⚠️ REPORTÉ — précisément (JAMAIS postulé), le CŒUR D'ORDRE / SURJECTION de
     l'adjonction (ce qui transforme « h⁺ prolonge h, a au sommet » en VRAI iso
     d'ordre de ]←,a] sur ]←,b]) : posé comme ÉNONCÉ conditionnel à hypothèses
     explicites dans `temoin_est_iso_segments_report` (compatibilité d'ordre de h⁺
     + bijectivité S∪{a}→T∪{b}).  C'est la part Cantor–Bernstein/back-and-forth
     restante, alimentée par a au sommet (ci-dessus) + h iso de S sur T.

INVARIANT : theorie_ensembles() = 22.  Rien postulé : h⁺ est un TERME (réunion),
tout DÉRIVE de AXIOME_REUNION/PAIRE/DOM + l'axiome dédié de h (scaffold) + l'infra
recollement déjà certifiée.  🚫 jamais tautologie, jamais affaibli : chaque
conclusion n'est aucune de ses hypothèses.
"""
from __future__ import annotations

from bourbaki.logique.formule import (
    Terme, var, app, egal, et, ou, non, impl, equiv, appartient,
    existe, pourtout, inclus,
)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.ordre.iii_1_relations_ordre.ordre_treillis import ensembles_ordre_vocab as V
from bourbaki.logique.tactiques.tactiques_abrege import syllogisme, a_implique_a
from bourbaki.logique.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, instancie, cas,
)
from bourbaki.cardinaux import ensembles_trichotomie_scaffold as TS
from bourbaki.cardinaux.ensembles_segments_construction import seg as _seg
from bourbaki.ensembles.base.ensembles_couples import (
    singleton_membre, membre_paire_gauche, couple_egal_implique_composantes,
)
from bourbaki.ensembles.fonctions.ensembles_restriction_somme import (
    membre_reunion_graphes, reunion_graphes_fonctionnelle, antecedent_dans_domaine,
)
from bourbaki.ensembles.fonctions.ensembles_recollement_bijection import (
    valeur_reunion_gauche, valeur_reunion_droite,
)


def _t(t):
    return t if isinstance(t, Terme) else var(t)


def _R_de(R):
    """Relation portée par le graphe R : a≤b := (a,b)∈R  (convention projet)."""
    vR = _t(R)
    return lambda a, b: appartient(E.couple(_t(a), _t(b)), vR)


# ── helpers de preuve éprouvés (copies locales, autonomes) ───────────────────
_HOLE = "hole_temoin_adj"


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


# ════════════════════════════════════════════════════════════════════════════
#  LE TERME — h⁺ = h ∪ {(a,b)} : prolongement de l'iso maximal par le point (a,b).
# ════════════════════════════════════════════════════════════════════════════
def graphe_point(a="a", b="b"):
    """{(a,b)} := singleton du couple (a,b) — le graphe ponctuel a↦b."""
    return E.singleton(E.couple(_t(a), _t(b)))


def temoin_adjonction(E_set="E", R="R", F_set="F", Rp="Rp", a="a", b="b"):
    """h⁺ := h ∪ {(a,b)}   (PROLONGEMENT de l'iso maximal h=h_iso_max par le point
    (a,b)).  Le TÉMOIN d'iso-de-segments de l'argument de maximalité (étape d.5) :
    recollement de h (iso de S=dom h sur T=pr₂ h) avec le graphe ponctuel {(a,b)}.
    TERME (réunion), AUCUN axiome nouveau.  theorie_ensembles INCHANGÉE (= 22)."""
    h = TS.h_iso_max(E_set, R, F_set, Rp)
    return E.reunion(h, graphe_point(a, b))


# ════════════════════════════════════════════════════════════════════════════
#  ✅ a_est_plus_grand_dans_adjoint : a EST le plus grand de l'adjonction S∪{a}.
#     LE CONTENU LITTÉRAL de l'adjonction du plus grand élément (relation_adjoint).
# ════════════════════════════════════════════════════════════════════════════
def a_est_plus_grand_dans_adjoint(R="R", E_set="E", a="a", x="x"):
    """⊢ est_plus_grand_element( relation_adjoint(R,E,a),  E∪{a},  a ).

    🎯 a EST LE PLUS GRAND ÉLÉMENT de l'adjonction E∪{a} pour la relation adjointe
    ≤'_a := relation_adjoint(R,E,a) (E.III.1.8) :

        x ≤'_a y  :⟺  (x≤y)  ou  (y=a et x∈E∪{a}).

    PREUVE.  est_plus_grand_element(≤',E∪{a},a) = ( a∈E∪{a} et (∀x)(x∈E∪{a} ⇒ x≤'a) ).
      • a∈E∪{a} : a∈{a} (singleton) ⇒ a∈E∪{a} (injection droite de la réunion).
      • Pour x∈E∪{a} : x≤'a se résout par la BRANCHE DROITE de ≤' (a=a réflexif, et
        x∈E∪{a} l'hypothèse) ; S2 sur la disjonction.
    INCONDITIONNEL, theorie=22.  C'est EXACTEMENT « a au sommet de E∪{a} », le maillon
    d'adjonction qui ALIMENTE la production du témoin iso-de-segments.  NON vacueux :
    est_plus_grand_element(…) n'est aucune hypothèse (il n'y en a pas)."""
    Rf = _R_de(R)
    va, vE = _t(a), _t(E_set)
    Rp_adj = V.relation_adjoint(Rf, vE, va)            # ≤'_a (fonction (x,y)↦Formule)
    Ep = V.ensemble_adjoint(vE, va)                    # E∪{a}
    vx = var(x)

    # ── a ∈ E∪{a} : a∈{a} ⇒ a∈E∪{a} (injection droite) ──
    a_in_sing = singleton_membre(va, va)               # a∈{a} ⇔ a=a
    a_in_singleton = N.modus_ponens(N.reflexivite(va), equivalence_arriere(a_in_sing))  # a∈{a}
    car_a = membre_reunion_graphes(vE, E.singleton(va), va)   # a∈E∪{a} ⇔ (a∈E ou a∈{a})
    a_in_Ep = N.modus_ponens(
        N.modus_ponens(a_in_singleton, N.s2(appartient(va, E.singleton(va)),
                                            appartient(va, vE))),
        syllogisme(N.s3(appartient(va, E.singleton(va)), appartient(va, vE)),
                   equivalence_arriere(car_a)))         # a∈E∪{a}

    # ── (∀x)( x∈E∪{a} ⇒ x≤'a )  via la branche droite (a=a et x∈E∪{a}) ──
    Hx_in_Ep = N.assume(appartient(vx, Ep))            # x∈E∪{a}
    branche_droite = et(egal(va, va), appartient(vx, Ep))     # a=a et x∈E∪{a}  (2ᵉ disjoint de ≤')
    preuve_droite = conjonction_intro(N.reflexivite(va), Hx_in_Ep)
    # relation_adjoint(R,E,a)(x,a) = ou( R(x,a) , et(a=a, x∈E∪{a}) ) : disjoint GAUCHE=R(x,a),
    # disjoint DROIT=branche_droite ; on l'insère par S3 après S2 (introduction du ∨ à droite).
    x_le_a = N.modus_ponens(preuve_droite,
                            syllogisme(N.s2(branche_droite, Rf(vx, va)),
                                       N.s3(branche_droite, Rf(vx, va))))   # R(x,a) ou (a=a et x∈E∪{a})
    assert x_le_a.conclusion == Rp_adj(vx, va), "branche d'adjonction ≠ ≤'_a(x,a)"
    body = N.loi_deduction(appartient(vx, Ep), x_le_a)   # x∈E∪{a} ⇒ x≤'a
    clause = N.generalisation(x, body)                   # (∀x)(x∈E∪{a} ⇒ x≤'a)

    res = conjonction_intro(a_in_Ep, clause)
    assert res.conclusion == E.est_plus_grand_element(Rp_adj, Ep, va, x)
    return res


def a_est_plus_grand_dans_adjoint_cible(R="R", E_set="E", a="a", x="x"):
    """ÉNONCÉ-cible (test miroir) :  est_plus_grand_element(≤'_a, E∪{a}, a)."""
    Rf = _R_de(R)
    va, vE = _t(a), _t(E_set)
    return E.est_plus_grand_element(V.relation_adjoint(Rf, vE, va),
                                    V.ensemble_adjoint(vE, va), va, x)


# ════════════════════════════════════════════════════════════════════════════
#  ✅ singleton_couple_fonctionnel : ⊢ est_fonctionnel({(a,b)}).
# ════════════════════════════════════════════════════════════════════════════
def singleton_couple_fonctionnel(a="a", b="b"):
    """⊢ est_fonctionnel( {(a,b)} ).

    Le graphe PONCTUEL {(a,b)} est fonctionnel : pour (u,v),(u,z)∈{(a,b)}, l'axiome
    du singleton donne (u,v)=(a,b) et (u,z)=(a,b), donc par injectivité des couples
    v=b=z.  INCONDITIONNEL, theorie=22.  NON vacueux : est_fonctionnel({(a,b)})
    n'est aucune hypothèse (il n'y en a pas).  Pièce de fonctionnalité du témoin h⁺."""
    va, vb = _t(a), _t(b)
    G = graphe_point(va, vb)
    ab = E.couple(va, vb)
    vu, vv, vz = var("u"), var("v"), var("z")
    cuv, cuz = E.couple(vu, vv), E.couple(vu, vz)

    # membre du singleton : (u,v)∈{(a,b)} ⇔ (u,v)=(a,b)
    mem_uv = singleton_membre(cuv, ab)                 # (u,v)∈{(a,b)} ⇔ (u,v)=(a,b)
    mem_uz = singleton_membre(cuz, ab)                 # (u,z)∈{(a,b)} ⇔ (u,z)=(a,b)

    Hyp = N.assume(et(appartient(cuv, G), appartient(cuz, G)))
    uv_eq_ab = N.modus_ponens(conjonction_elim_gauche(Hyp), equivalence_avant(mem_uv))  # (u,v)=(a,b)
    uz_eq_ab = N.modus_ponens(conjonction_elim_droite(Hyp), equivalence_avant(mem_uz))  # (u,z)=(a,b)
    # v=b  (2ᵉ composante de (u,v)=(a,b)) ; z=b ; donc v=z
    v_eq_b = conjonction_elim_droite(N.modus_ponens(
        uv_eq_ab, couple_egal_implique_composantes(vu, vv, va, vb)))   # v=b
    z_eq_b = conjonction_elim_droite(N.modus_ponens(
        uz_eq_ab, couple_egal_implique_composantes(vu, vz, va, vb)))   # z=b
    # v=z : de v=b et z=b
    from bourbaki.logique.tactiques.tactiques_abrege_egalite import symetrie, composer_egalites
    b_eq_z = N.modus_ponens(z_eq_b, symetrie(vz, vb))  # b=z
    v_eq_z = composer_egalites(v_eq_b, b_eq_z)         # v=z
    body = N.loi_deduction(et(appartient(cuv, G), appartient(cuz, G)), v_eq_z)
    res = N.generalisation("u", N.generalisation("v", N.generalisation("z", body)))
    assert res.conclusion == E.est_fonctionnel(G)
    return res


def singleton_couple_fonctionnel_cible(a="a", b="b"):
    """ÉNONCÉ-cible (test miroir) :  est_fonctionnel({(a,b)})."""
    return E.est_fonctionnel(graphe_point(a, b))


# ════════════════════════════════════════════════════════════════════════════
#  ✅ couple_dans_temoin : ⊢ (a,b) ∈ h⁺.   h⁺ apparie bien a↦b.
# ════════════════════════════════════════════════════════════════════════════
def couple_dans_temoin(E_set="E", R="R", F_set="F", Rp="Rp", a="a", b="b"):
    """⊢ (a,b) ∈ h⁺  ( = h ∪ {(a,b)} ).

    Le couple adjoint (a,b) appartient au témoin : (a,b)∈{(a,b)} (singleton) ⇒
    (a,b)∈h∪{(a,b)} (injection droite de la réunion).  INCONDITIONNEL, theorie=22.
    NON vacueux.  C'est l'appariement a↦b ajouté au prolongement."""
    va, vb = _t(a), _t(b)
    ab = E.couple(va, vb)
    h = TS.h_iso_max(E_set, R, F_set, Rp)
    G = graphe_point(va, vb)
    # (a,b)∈{(a,b)}
    ab_in_sing = N.modus_ponens(N.reflexivite(ab),
                                equivalence_arriere(singleton_membre(ab, ab)))
    car = membre_reunion_graphes(h, G, ab)             # (a,b)∈h∪{(a,b)} ⇔ ((a,b)∈h ou (a,b)∈{(a,b)})
    return N.modus_ponens(
        N.modus_ponens(ab_in_sing, syllogisme(
            N.s2(appartient(ab, G), appartient(ab, h)),
            N.s3(appartient(ab, G), appartient(ab, h)))),
        equivalence_arriere(car))                      # (a,b)∈h⁺


def couple_dans_temoin_cible(E_set="E", R="R", F_set="F", Rp="Rp", a="a", b="b"):
    """ÉNONCÉ-cible (test miroir) :  (a,b) ∈ h⁺."""
    return appartient(E.couple(_t(a), _t(b)),
                      temoin_adjonction(E_set, R, F_set, Rp, a, b))


# ════════════════════════════════════════════════════════════════════════════
#  ✅ h_inclus_temoin : ⊢ (∀z)( z∈h ⇒ z∈h⁺ ).   h⁺ PROLONGE h.
# ════════════════════════════════════════════════════════════════════════════
def h_inclus_temoin(E_set="E", R="R", F_set="F", Rp="Rp", a="a", b="b", z="z"):
    """⊢ h ⊂ h⁺   ( (∀z)( z∈h ⇒ z∈h∪{(a,b)} ) ).

    Tout couple de h est conservé par le prolongement (injection gauche de la
    réunion).  INCONDITIONNEL, theorie=22.  NON vacueux : l'inclusion n'est aucune
    hypothèse.  Garantit que h⁺ ÉTEND h (le recollement n'efface rien)."""
    va, vb = _t(a), _t(b)
    h = TS.h_iso_max(E_set, R, F_set, Rp)
    G = graphe_point(va, vb)
    vz = var(z)
    Hz = N.assume(appartient(vz, h))                   # z∈h
    car = membre_reunion_graphes(h, G, vz)             # z∈h∪{(a,b)} ⇔ (z∈h ou z∈{(a,b)})
    z_in = N.modus_ponens(
        N.modus_ponens(Hz, N.s2(appartient(vz, h), appartient(vz, G))),
        equivalence_arriere(car))                      # z∈h⁺
    return N.generalisation(z, N.loi_deduction(appartient(vz, h), z_in))


def h_inclus_temoin_cible(E_set="E", R="R", F_set="F", Rp="Rp", a="a", b="b", z="z"):
    """ÉNONCÉ-cible (test miroir) :  (∀z)( z∈h ⇒ z∈h⁺ )."""
    h = TS.h_iso_max(E_set, R, F_set, Rp)
    Gp = temoin_adjonction(E_set, R, F_set, Rp, a, b)
    vz = var(z)
    return pourtout(z, impl(appartient(vz, h), appartient(vz, Gp)))


# ════════════════════════════════════════════════════════════════════════════
#  ✅ a_dans_dom_singleton_couple : ⊢ a ∈ dom({(a,b)}).
#  ✅ dom_singleton_couple        : ⊢ dom({(a,b)}) = {a}.
# ════════════════════════════════════════════════════════════════════════════
def a_dans_dom_singleton_couple(a="a", b="b", y="y"):
    """⊢ a ∈ dom( {(a,b)} ).

    a est l'antécédent du graphe ponctuel {(a,b)} : (a,b)∈{(a,b)} ⇒ a∈dom({(a,b)})
    (antecedent_dans_domaine).  INCONDITIONNEL, theorie=22.  NON vacueux.
    Sert à invoquer valeur_reunion_droite (h⁺(a)=b)."""
    va, vb = _t(a), _t(b)
    ab = E.couple(va, vb)
    G = graphe_point(va, vb)
    ab_in_G = N.modus_ponens(N.reflexivite(ab),
                             equivalence_arriere(singleton_membre(ab, ab)))   # (a,b)∈{(a,b)}
    return N.modus_ponens(ab_in_G, antecedent_dans_domaine(va, vb, G))        # a∈dom({(a,b)})


def a_dans_dom_singleton_couple_cible(a="a", b="b"):
    """ÉNONCÉ-cible (test miroir) :  a ∈ dom({(a,b)})."""
    return appartient(_t(a), E.dom(graphe_point(a, b)))


def dom_singleton_couple(a="a", b="b", u="u", y="y"):
    """⊢ dom( {(a,b)} ) = {a}.

    Le domaine du graphe ponctuel {(a,b)} est le singleton {a} :
      u∈dom{(a,b)} ⇔ (∃y)((u,y)∈{(a,b)}) ⇔ (∃y)((u,y)=(a,b)) ⇔ u=a ⇔ u∈{a}.
    Double inclusion + extensionnalité A1.  INCONDITIONNEL, theorie=22.  NON vacueux.

    ⇒ : (u,y)=(a,b) ⇒ u=a (1ʳᵉ composante) ⇒ u∈{a}.
    ⇐ : u∈{a} ⇒ u=a ⇒ (u,b)=(a,b) ⇒ (u,b)∈{(a,b)} ⇒ u∈dom{(a,b)} (témoin y:=b)."""
    from bourbaki.logique.tactiques.tactiques_abrege_quantif import existe_elimination
    from bourbaki.logique.tactiques.tactiques_abrege_egalite import congruence_terme
    from bourbaki.ensembles.ensembles_theoremes import couple_egal_si_composantes
    va, vb = _t(a), _t(b)
    ab = E.couple(va, vb)
    G = graphe_point(va, vb)
    domG = E.dom(G)
    Sa = E.singleton(va)
    vu = var("z")                                      # liant courant = « z » (apparié à A1)
    vy = var(y)

    ax_dom = N.axiome(E.theorie_ensembles(), E.AXIOME_DOM)
    car_dom = instancie(instancie(ax_dom, G), vu)      # u∈domG ⇔ (∃y)((u,y)∈G)
    mem_sa = singleton_membre(vu, va)                  # u∈{a} ⇔ u=a

    # ── ⇒ : u∈domG ⇒ u∈{a} ──
    Hdom = N.assume(appartient(vu, domG))
    ex_uy = N.modus_ponens(Hdom, equivalence_avant(car_dom))    # (∃y)((u,y)∈G)
    body_uy = appartient(E.couple(vu, vy), G)                   # (u,y)∈G
    Hbody = N.assume(body_uy)
    uy_eq_ab = N.modus_ponens(Hbody, equivalence_avant(singleton_membre(E.couple(vu, vy), ab)))  # (u,y)=(a,b)
    u_eq_a = conjonction_elim_gauche(N.modus_ponens(
        uy_eq_ab, couple_egal_implique_composantes(vu, vy, va, vb)))   # u=a
    u_in_sa = N.modus_ponens(u_eq_a, equivalence_arriere(mem_sa))      # u∈{a}
    imp_body = existe_elimination(N.loi_deduction(body_uy, u_in_sa), y)  # (∃y)((u,y)∈G) ⇒ u∈{a}
    fwd = N.loi_deduction(appartient(vu, domG),
                          N.modus_ponens(ex_uy, imp_body))    # u∈domG ⇒ u∈{a}
    incl_dom_sa = N.generalisation("z", fwd)

    # ── ⇐ : u∈{a} ⇒ u∈domG ──
    Hsa = N.assume(appartient(vu, Sa))
    u_eq_a2 = N.modus_ponens(Hsa, equivalence_avant(mem_sa))    # u=a
    # (u,b)=(a,b) par congruence sur la 1ʳᵉ coordonnée
    ub_eq_ab = N.modus_ponens(u_eq_a2, congruence_terme(vu, va, E.couple(var("w"), vb)))  # (u,b)=(a,b)
    ub_in_G = N.modus_ponens(ub_eq_ab, equivalence_arriere(singleton_membre(E.couple(vu, vb), ab)))  # (u,b)∈G
    # (∃y)((u,y)∈G) témoin y:=b
    ex_ub = N.modus_ponens(ub_in_G, N.s5(body_uy, vb, y))      # (∃y)((u,y)∈G)
    u_in_dom = N.modus_ponens(ex_ub, equivalence_arriere(car_dom))   # u∈domG
    bwd = N.loi_deduction(appartient(vu, Sa), u_in_dom)
    incl_sa_dom = N.generalisation("z", bwd)

    ext = instancie(instancie(N.axiome(E.theorie_ensembles(), E.A1), domG), Sa)
    return N.modus_ponens(conjonction_intro(incl_dom_sa, incl_sa_dom), ext)   # domG = {a}


def dom_singleton_couple_cible(a="a", b="b"):
    """ÉNONCÉ-cible (test miroir) :  dom({(a,b)}) = {a}."""
    return egal(E.dom(graphe_point(a, b)), E.singleton(_t(a)))


# ════════════════════════════════════════════════════════════════════════════
#  ⚠️ disjonction_domaines_sous_a_hors : { a∉dom h } ⊢ domaines disjoints.
# ════════════════════════════════════════════════════════════════════════════
def disjonction_domaines_sous_a_hors(E_set="E", R="R", F_set="F", Rp="Rp",
                                     a="a", b="b", u="u"):
    """⊢ { a∉dom h } ⊢ (∀u)¬( u∈dom h et u∈dom({(a,b)}) ).

    Domaines de h et {(a,b)} DISJOINTS sous l'hypothèse explicite a∉dom h (VRAIE car
    a=min(E∖dom h)).  PREUVE : si u∈dom h et u∈dom{(a,b)}=({a}), alors u=a (via
    dom_singleton_couple + singleton), donc a=u∈dom h — contredit a∉dom h.
    CONDITIONNEL à a∉dom h, theorie=22.  NON vacueux.  C'est la PRÉCONDITION du
    recollement (reunion_graphes_fonctionnelle) appliqué à h⁺."""
    va, vb = _t(a), _t(b)
    h = TS.h_iso_max(E_set, R, F_set, Rp)
    G = graphe_point(va, vb)
    domh, domG = E.dom(h), E.dom(G)
    Sa = E.singleton(va)
    vu = var(u)

    Ha_hors = N.assume(non(appartient(va, domh)))      # a∉dom h
    dom_eq_sa = dom_singleton_couple(a, b)             # dom({(a,b)}) = {a}

    Hpaire = N.assume(et(appartient(vu, domh), appartient(vu, domG)))
    u_in_domh = conjonction_elim_gauche(Hpaire)        # u∈dom h
    u_in_domG = conjonction_elim_droite(Hpaire)        # u∈dom({(a,b)})
    # u∈{a} (réécrire dom({(a,b)}) en {a})
    u_in_sa = _leib(domG, Sa, dom_eq_sa, lambda w: appartient(vu, w), u_in_domG)  # u∈{a}
    u_eq_a = N.modus_ponens(u_in_sa, equivalence_avant(singleton_membre(vu, va))) # u=a
    # a∈dom h (de u∈dom h et u=a) → contredit a∉dom h
    a_in_domh = _leib(vu, va, u_eq_a, lambda w: appartient(w, domh), u_in_domh)   # a∈dom h
    falso = _ex_falso(a_in_domh, Ha_hors,
                      non(et(appartient(vu, domh), appartient(vu, domG))))        # ¬(…)
    neg = _refute_self(N.loi_deduction(
        et(appartient(vu, domh), appartient(vu, domG)), falso))                  # ¬(u∈domh et u∈domG)
    return N.generalisation(u, neg)


def disjonction_domaines_cible(E_set="E", R="R", F_set="F", Rp="Rp", a="a", b="b", u="u"):
    """ÉNONCÉ-cible (test miroir) :  (∀u)¬(u∈dom h et u∈dom({(a,b)}))."""
    h = TS.h_iso_max(E_set, R, F_set, Rp)
    G = graphe_point(a, b)
    vu = var(u)
    return pourtout(u, non(et(appartient(vu, E.dom(h)), appartient(vu, E.dom(G)))))


# ════════════════════════════════════════════════════════════════════════════
#  ⚠️ temoin_fonctionnel_sous_a_hors : { a∉dom h, func h } ⊢ est_fonctionnel(h⁺).
# ════════════════════════════════════════════════════════════════════════════
def temoin_fonctionnel_sous_a_hors(E_set="E", R="R", F_set="F", Rp="Rp", a="a", b="b"):
    """⊢ { a∉dom h, est_fonctionnel(h) } ⊢ est_fonctionnel( h⁺ ).

    h⁺=h∪{(a,b)} est FONCTIONNEL par recollement à domaines disjoints
    (reunion_graphes_fonctionnelle) : h fonctionnel (hyp), {(a,b)} fonctionnel
    (singleton_couple_fonctionnel, INCOND.), domaines disjoints sous a∉dom h
    (disjonction_domaines_sous_a_hors).  CONDITIONNEL aux deux hypothèses EXPLICITES,
    theorie=22.  NON vacueux : est_fonctionnel(h⁺) ≠ hypothèses.

    SENS : le prolongement n'introduit AUCUN conflit de valeur — il étend h en
    gardant une fonction.  Pièce de fonctionnalité du témoin iso-de-segments."""
    va, vb = _t(a), _t(b)
    h = TS.h_iso_max(E_set, R, F_set, Rp)
    G = graphe_point(va, vb)
    # reunion_graphes_fonctionnelle(h, G) : {func h, func G, disj} ⊢ func(h∪G)
    rgf = reunion_graphes_fonctionnelle(h, G)
    # décharger func(G) (PROUVÉ) et disj (PROUVÉ sous a∉dom h) ; garder func(h) et a∉dom h
    func_G = singleton_couple_fonctionnel(va, vb)      # func {(a,b)}   (INCOND.)
    rgf = N.modus_ponens(func_G, N.loi_deduction(E.est_fonctionnel(G), rgf))
    disj = disjonction_domaines_sous_a_hors(E_set, R, F_set, Rp, a, b)   # [a∉dom h]
    disj_form = pourtout("u", non(et(appartient(var("u"), E.dom(h)),
                                     appartient(var("u"), E.dom(G)))))
    rgf = N.modus_ponens(disj, N.loi_deduction(disj_form, rgf))
    # rgf : est_fonctionnel(h∪G)  [func h, a∉dom h]
    return rgf


def temoin_fonctionnel_cible(E_set="E", R="R", F_set="F", Rp="Rp", a="a", b="b"):
    """ÉNONCÉ-cible (test miroir) :  est_fonctionnel(h⁺)."""
    return E.est_fonctionnel(temoin_adjonction(E_set, R, F_set, Rp, a, b))


# ════════════════════════════════════════════════════════════════════════════
#  ⚠️ valeur_temoin_en_a_sous_a_hors : { a∉dom h, func h } ⊢ valeur(h⁺,a)=b.
# ════════════════════════════════════════════════════════════════════════════
def valeur_temoin_en_a_sous_a_hors(E_set="E", R="R", F_set="F", Rp="Rp", a="a", b="b"):
    """⊢ { a∉dom h, est_fonctionnel(h) } ⊢ valeur(h⁺, a) = b.

    h⁺(a)=b : a∈dom({(a,b)}) (a_dans_dom_singleton_couple) donc valeur(h∪{(a,b)},a)=
    valeur({(a,b)},a) (valeur_reunion_droite), et valeur({(a,b)},a)=b.  CONDITIONNEL
    (func h, a∉dom h — pour la fonctionnalité du recollement), theorie=22.  NON vacueux.

    SENS : le point adjoint réalise bien l'appariement a↦b dans h⁺ — c'est φ⁺(a)=b,
    la valeur du sommet, indispensable à « h⁺ envoie ]←,a] sur ]←,b] »."""
    from bourbaki.logique.tactiques.tactiques_abrege_egalite import composer_egalites
    va, vb = _t(a), _t(b)
    h = TS.h_iso_max(E_set, R, F_set, Rp)
    G = graphe_point(va, vb)
    domG = E.dom(G)

    # valeur(h∪G, a) = valeur(G, a)  (valeur_reunion_droite) ; décharger ses 4 hyps.
    vrd = valeur_reunion_droite(h, G, va)              # hyps: func h, func G, disj, a∈domG
    func_G = singleton_couple_fonctionnel(va, vb)
    disj = disjonction_domaines_sous_a_hors(E_set, R, F_set, Rp, a, b)   # [a∉dom h]
    a_in_domG = a_dans_dom_singleton_couple(a, b)      # a∈domG  (INCOND.)
    disj_form = pourtout("u", non(et(appartient(var("u"), E.dom(h)),
                                     appartient(var("u"), domG))))
    vrd = N.modus_ponens(func_G, N.loi_deduction(E.est_fonctionnel(G), vrd))
    vrd = N.modus_ponens(disj, N.loi_deduction(disj_form, vrd))
    vrd = N.modus_ponens(a_in_domG, N.loi_deduction(appartient(va, domG), vrd))
    # vrd : valeur(h∪G,a)=valeur(G,a)  [func h, a∉dom h]

    # valeur(G,a)=b  via valeur_caracterisation du graphe ponctuel
    val_G_a_eq_b = _valeur_graphe_point_en_a(va, vb)   # valeur({(a,b)},a)=b   (INCOND.)
    return composer_egalites(vrd, val_G_a_eq_b)        # valeur(h⁺,a)=b


def _valeur_graphe_point_en_a(a, b):
    """⊢ valeur( {(a,b)}, a ) = b.   ({(a,b)} fonctionnel, (a,a-value)=b par unicité.)"""
    from bourbaki.ensembles.fonctions.ensembles_fonctions import (
        valeur_caracterisation, valeur_dans_graphe)
    from bourbaki.logique.tactiques.tactiques_abrege_egalite import symetrie
    va, vb = _t(a), _t(b)
    ab = E.couple(va, vb)
    G = graphe_point(va, vb)
    func_G = singleton_couple_fonctionnel(va, vb)      # func {(a,b)}
    # (a,b)∈G
    ab_in_G = N.modus_ponens(N.reflexivite(ab),
                             equivalence_arriere(singleton_membre(ab, ab)))
    # (∃y)((a,y)∈G)  témoin b
    ex_ay = N.modus_ponens(ab_in_G, N.s5(appartient(E.couple(va, var("y")), G), vb, "y"))
    # valeur_caracterisation(G,a) : ((a,y)∈G) ⇔ (y=valeur(G,a))  [func G, (∃y)…]
    vc = valeur_caracterisation(G, va)                 # hyps: func G, (∃y)((a,y)∈G)
    vc_b = instancie(N.generalisation("y", vc), vb)    # ((a,b)∈G) ⇔ (b=valeur(G,a))
    b_eq_val = N.modus_ponens(ab_in_G, equivalence_avant(vc_b))   # b=valeur(G,a)
    val_eq_b = N.modus_ponens(b_eq_val, symetrie(vb, E.valeur(G, va)))  # valeur(G,a)=b
    # décharger func G, (∃y)((a,y)∈G)
    val_eq_b = N.modus_ponens(func_G, N.loi_deduction(E.est_fonctionnel(G), val_eq_b))
    val_eq_b = N.modus_ponens(ex_ay, N.loi_deduction(
        existe("y", appartient(E.couple(va, var("y")), G)), val_eq_b))
    return val_eq_b


def valeur_temoin_en_a_cible(E_set="E", R="R", F_set="F", Rp="Rp", a="a", b="b"):
    """ÉNONCÉ-cible (test miroir) :  valeur(h⁺, a) = b."""
    Gp = temoin_adjonction(E_set, R, F_set, Rp, a, b)
    return egal(E.valeur(Gp, _t(a)), _t(b))


# ════════════════════════════════════════════════════════════════════════════
#  ⚠️ valeur_temoin_sur_dom_h_sous : { a∉dom h, func h, u∈dom h } ⊢ h⁺(u)=h(u).
# ════════════════════════════════════════════════════════════════════════════
def valeur_temoin_sur_dom_h_sous(E_set="E", R="R", F_set="F", Rp="Rp",
                                 a="a", b="b", u="u"):
    """⊢ { a∉dom h, est_fonctionnel(h), u∈dom h } ⊢ valeur(h⁺, u) = valeur(h, u).

    h⁺ COÏNCIDE avec h sur dom h : u∈dom h ⇒ valeur(h∪{(a,b)},u)=valeur(h,u)
    (valeur_reunion_gauche).  CONDITIONNEL (func h, a∉dom h pour la fonctionnalité du
    recollement ; u∈dom h pour la branche gauche), theorie=22.  NON vacueux.

    SENS : sur le segment S=dom h, h⁺ EST h (donc h⁺ étend l'iso h:S≅T sans le
    modifier) — l'autre moitié de « h⁺ envoie ]←,a] sur ]←,b] »."""
    va, vb = _t(a), _t(b)
    h = TS.h_iso_max(E_set, R, F_set, Rp)
    G = graphe_point(va, vb)
    domh, domG = E.dom(h), E.dom(G)
    vu = _t(u)

    vrg = valeur_reunion_gauche(h, G, vu)              # hyps: func h, func G, disj, u∈dom h
    func_G = singleton_couple_fonctionnel(va, vb)
    disj = disjonction_domaines_sous_a_hors(E_set, R, F_set, Rp, a, b)   # [a∉dom h]
    disj_form = pourtout("u", non(et(appartient(var("u"), domh),
                                     appartient(var("u"), domG))))
    vrg = N.modus_ponens(func_G, N.loi_deduction(E.est_fonctionnel(G), vrg))
    vrg = N.modus_ponens(disj, N.loi_deduction(disj_form, vrg))
    # u∈dom h reste en HYPOTHÈSE (porté par valeur_reunion_gauche, on le garde)
    return vrg                                          # valeur(h⁺,u)=valeur(h,u)  [func h, a∉dom h, u∈dom h]


def valeur_temoin_sur_dom_h_cible(E_set="E", R="R", F_set="F", Rp="Rp",
                                  a="a", b="b", u="u"):
    """ÉNONCÉ-cible (test miroir) :  valeur(h⁺, u) = valeur(h, u)."""
    h = TS.h_iso_max(E_set, R, F_set, Rp)
    Gp = temoin_adjonction(E_set, R, F_set, Rp, a, b)
    vu = _t(u)
    return egal(E.valeur(Gp, vu), E.valeur(h, vu))


# ════════════════════════════════════════════════════════════════════════════
#  ⚠️ REPORTÉ — le CŒUR D'ORDRE / SURJECTION de l'adjonction (énoncé conditionnel).
#     JAMAIS prouvé ici ; posé avec hypothèses EXPLICITES pour clore la maximalité.
# ════════════════════════════════════════════════════════════════════════════
def temoin_est_iso_segments_report(E_set="E", R="R", F_set="F", Rp="Rp",
                                   a="a", b="b"):
    """ÉNONCÉ (REPORTÉ, NON prouvé) du cœur dur : h⁺ est un ISO D'ORDRE de
    ]←,a]=seg(R,E,a)∪{a} sur ]←,b]=seg(Rp,F,b)∪{b}, pour les ordres ADJOINTS
    ≤'_a = relation_adjoint(R, seg(R,E,a), a)  et  ≤'_b = relation_adjoint(Rp, seg(Rp,F,b), b) :

        est_isomorphisme_ordre( h⁺,  seg(R,E,a)∪{a},  seg(Rp,F,b)∪{b},  ≤'_a,  ≤'_b ).

    ⚠️ CE N'EST PAS UN THÉORÈME PROUVÉ : c'est l'OBJECTIF du maillon (i), reporté.
    Les morceaux DÉJÀ PROUVÉS l'ALIMENTENT (a au sommet — a_est_plus_grand_dans_adjoint ;
    h⁺ fonctionnel — temoin_fonctionnel_sous_a_hors ; h⁺(a)=b et h⁺=h sur S — valeurs ;
    h⊂h⁺ — h_inclus_temoin).  RESTE DUR (Cantor–Bernstein / back-and-forth) :
      • BIJECTIVITÉ de h⁺ : S∪{a}→T∪{b} (h:S≅T bijective + point frais a↦b, a∉S, b∉T).
      • COMPATIBILITÉ D'ORDRE de h⁺ : pour x,y∈S∪{a},  x≤'_a y ⇔ h⁺(x)≤'_b h⁺(y).
        (sur S : compatibilité de h ; avec a au sommet : x≤'_a a tjs vrai et
         h⁺(x)=h(x)∈T≤'_b b=h⁺(a) tjs vrai ; symétrie.)
    Fournir ces deux assemble le témoin et CLÔT la maximalité (via
    adjonction_contredit_segment_propre).  POSÉ comme cible, JAMAIS postulé."""
    Rf, Rpf = _R_de(R), _R_de(Rp)
    va, vb = _t(a), _t(b)
    Sa = _seg(R, E_set, a)                              # seg(R,E,a) = ]←,a[
    Sb = _seg(Rp, F_set, b)                             # seg(Rp,F,b) = ]←,b[
    SaA = V.ensemble_adjoint(Sa, va)                    # ]←,a] = seg∪{a}
    SbB = V.ensemble_adjoint(Sb, vb)                    # ]←,b] = seg∪{b}
    le_a = V.relation_adjoint(Rf, Sa, va)               # ≤'_a
    le_b = V.relation_adjoint(Rpf, Sb, vb)              # ≤'_b
    hplus = temoin_adjonction(E_set, R, F_set, Rp, a, b)
    return V.est_isomorphisme_ordre(hplus, SaA, SbB, le_a, le_b)


__all__ = [
    "graphe_point", "temoin_adjonction",
    "a_est_plus_grand_dans_adjoint", "a_est_plus_grand_dans_adjoint_cible",
    "singleton_couple_fonctionnel", "singleton_couple_fonctionnel_cible",
    "couple_dans_temoin", "couple_dans_temoin_cible",
    "h_inclus_temoin", "h_inclus_temoin_cible",
    "a_dans_dom_singleton_couple", "a_dans_dom_singleton_couple_cible",
    "dom_singleton_couple", "dom_singleton_couple_cible",
    "disjonction_domaines_sous_a_hors", "disjonction_domaines_cible",
    "temoin_fonctionnel_sous_a_hors", "temoin_fonctionnel_cible",
    "valeur_temoin_en_a_sous_a_hors", "valeur_temoin_en_a_cible",
    "valeur_temoin_sur_dom_h_sous", "valeur_temoin_sur_dom_h_cible",
    "temoin_est_iso_segments_report",
]
