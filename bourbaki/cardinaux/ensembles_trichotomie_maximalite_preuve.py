"""§III.2 — Théorème 3 (TRICHOTOMIE) : PREUVE du cœur de la MAXIMALITÉ de h.

────────────────────────────────────────────────────────────────────────────────
RÔLE.  Étape (d.5) du blueprint DESIGN_trichotomie_III2.md — l'argument
« l'un des deux segments est le tout ».  Ce module ATTAQUE le cœur dur posé
(conditionnel) dans ensembles_trichotomie_scaffold_maximalite (h_maximal,
maximalite_donne_trichotomie) et en FERME ce qui est atteignable SANS rien postuler.

PIÈCE AMONT (réutilisée, NON reprouvée) — ensembles_trichotomie_scaffold :
    h = h_iso_max(E,R,F,Rp) = UNION des graphes d'iso de couples de segments
    isomorphes (terme opaque, axiome dédié theorie_h, theorie_ensembles=22) ;
    couple_iso_dans_h : { S seg E, T seg F, φ:S≅T, u∈S, u∈E, v∈F, v=φ(u) } ⊢ (u,v)∈h.

CLÉ STRUCTURELLE.  Tout couple (a,b)∈h donne a∈dom(h) (AXIOME_DOM, déjà dans
theorie_ensembles=22) ET b∈pr₂(h) (AXIOME_IMG).  C'est le levier élémentaire de la
maximalité : un point « nouveau » a∉dom(h) ne peut pas déjà être apparié dans h.

CE MODULE LIVRE (salvage fort gradué, honnête, theorie=22) :

  ✅ INCONDITIONNEL (theorie=22, 0 hypothèse) :
     • couple_dans_h_donne_antecedent : { (a,b)∈h } ⊢ a∈dom(h).        [réutilisable]
     • couple_dans_h_donne_valeur     : { (a,b)∈h } ⊢ b∈pr₂(h).        [réutilisable]
     • point_pas_dans_son_segment     : ⊢ ¬( a ∈ seg(R,E,a) ).         [réutilisable]
       (Aucun point n'appartient à son propre segment initial ]←,a[ : a∈]←,a[
        forcerait a≠a.  Brique de la contradiction de maximalité.)
     • h_maximal_preuve : ⊢ h_maximal(E,R,F,Rp), la FORMULE posée dans le scaffold :
            (∀a)(∀b)( (a∈E et a∉dom h et b∈F et b∉pr₂ h) ⇒ ¬((a,b)∈h) ).
       ⚠️⚠️ AVERTISSEMENT D'HONNÊTETÉ — CE N'EST PAS LA MAXIMALITÉ SUBSTANTIELLE.  La
       formule h_maximal du scaffold encode « (a,b) prolonge h » par `extensible :=
       (a,b)∈h`, si bien que h_maximal se réduit à « a∉dom h ⇒ (a,b)∉h » — VRAI PAR
       DÉFINITION de dom(h) (contraposée : (a,b)∈h ⇒ a∈dom h).  h_maximal_preuve ne fait
       donc que certifier cette TRIVIALITÉ ; elle NE FERME PAS la maximalité qui compte
       pour la trichotomie (= « dom(h)=E ou pr₂(h)=F », càd : on ne peut adjoindre (a,b)
       en gardant un ISO DE SEGMENTS h∪{(a,b)}).  Cette maximalité SUBSTANTIELLE reste
       CONDITIONNELLE (adjonction_contredit_segment_propre, ci-dessous) et REPORTÉE
       (maximalite_donne_trichotomie + témoin effectif).  À ne JAMAIS présenter comme
       « trichotomie maximalité close ».  (Idéalement, le scaffold devrait reposer
       h_maximal avec `extensible := h∪{(a,b)} est un iso de segments`.)

  ⚠️ CONDITIONNEL — hypothèses EXPLICITES (le contenu DUR, REPORTÉ avec précision) :
     • extension_iso_donne_antecedent : sous les 7 hypothèses STRUCTURELLES de
       couple_iso_dans_h (S seg E, T seg F, φ:S≅T, a∈S, a∈E, b∈F, b=φ(a)) ⊢ a∈dom(h).
       (Si (a,b) est un point d'un iso de segments φ:S≅T, alors a est déjà dans dom h :
        on ne peut PAS étendre h par un tel (a,b) « par-dessus » son domaine.)
     • adjonction_contredit_segment_propre : sous les MÊMES 7 hypothèses ⊢
            ¬( dom(h) = seg(R,E,a) ).
       🎯 CŒUR de la maximalité (d.5), honnêtement conditionnel : si a est l'image
       d'un point témoin d'un iso de segments (donc a∈dom h), alors dom(h) ne peut être
       le segment PROPRE ]←,a[ — sinon a∈]←,a[ ⇒ a≠a (point_pas_dans_son_segment).
       C'est EXACTEMENT la contradiction « (a,b) prolonge h ⇒ a∈seg(E,a) ⇒ a<a absurde »
       de l'argument d'extension du blueprint, réduite à ses hypothèses minimales.

  ⚠️ REPORTÉ — précisément (JAMAIS postulé) : reste à fournir, pour CLORE la
     trichotomie inconditionnelle, (i) Prop 1 §III.2 (dom h ≠ E ⇒ dom h = seg(R,E,a)
     avec a=min(E∖dom h), via plus_petit_de_bon_ordre) ; (ii) la production EFFECTIVE
     du témoin iso-de-segments (a,b) qui ALIMENTE les 7 hypothèses structurelles de
     adjonction_contredit_segment_propre — i.e. que ]←,a]≅]←,b] EST un iso (adjonction
     du plus grand élément, relation_adjoint), back-and-forth de magnitude
     Cantor–Bernstein.  Ces deux maillons sont la part dure restante.

INVARIANT : theorie_ensembles() = 22.  Rien postulé : tout dérive de AXIOME_DOM /
AXIOME_IMG / AXIOME_SEGMENT_EXTREMITE (déjà présents) + de l'axiome dédié de h.
🚫 jamais tautologie déguisée, jamais affaibli : chaque conclusion (a∈dom h, b∈pr₂ h,
¬(a∈seg(E,a)), ¬(dom h=seg(E,a)), h_maximal) n'est aucune de ses hypothèses.
"""
from __future__ import annotations

from bourbaki.logique.formule import (
    Terme, var, egal, et, ou, non, impl, equiv, appartient, existe, pourtout, inclus,
)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.ordre import ensembles_ordre_vocab as V
from bourbaki.logique.tactiques.tactiques_abrege import a_implique_a, syllogisme
from bourbaki.logique.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, instancie,
)
from bourbaki.cardinaux import ensembles_trichotomie_scaffold as TS
from bourbaki.cardinaux import ensembles_trichotomie_scaffold_maximalite as M
from bourbaki.cardinaux.ensembles_segments_construction import (
    seg as _seg, membre_segment as _membre_seg,
)


def _t(t):
    return t if isinstance(t, Terme) else var(t)


# ── helpers de preuve éprouvés (copies locales) ──────────────────────────────
def _ex_falso(thm_a, thm_na, z):
    """De ⊢A et ⊢¬A, conclure ⊢Z (n'importe quoi)."""
    a = thm_a.conclusion
    return N.modus_ponens(thm_a, N.modus_ponens(thm_na, N.s2(non(a), z)))


def _refute_self(thm_P_imp_notP):
    """De ⊢(P⇒¬P), conclure ⊢¬P  (via S1 : (¬P∨¬P)⇒¬P)."""
    from bourbaki.logique.tactiques.tactiques_abrege import antecedent_consequent
    P, notP = antecedent_consequent(thm_P_imp_notP.conclusion)
    return N.modus_ponens(thm_P_imp_notP, N.s1(notP))


def _leib(a, b, h_ab, phi_fun, h_phi_a, hole="hole_max"):
    """Transport de Leibniz : ⊢(a=b), ⊢φ(a) ⟹ ⊢φ(b)  via S6."""
    va, vb = _t(a), _t(b)
    eqv = N.modus_ponens(h_ab, N.s6(va, vb, hole, phi_fun(var(hole))))
    return N.modus_ponens(h_phi_a, equivalence_avant(eqv))


def _ex_y_couple(h, a, b, y="y"):
    """De ⊢ (a,b)∈h, conclure ⊢ (∃y)((a,y)∈h)  (témoin b, liant y).

    Le liant « y » COÏNCIDE avec celui de AXIOME_DOM (sinon α-décalage)."""
    return None  # placeholder remplacé inline (cf. couple_dans_h_donne_antecedent)


# ════════════════════════════════════════════════════════════════════════════
#  ✅ couple_dans_h_donne_antecedent : { (a,b)∈h } ⊢ a∈dom(h).   INCONDITIONNEL.
# ════════════════════════════════════════════════════════════════════════════
def couple_dans_h_donne_antecedent(E_set="E", R="R", F_set="F", Rp="Rp",
                                   a="a", b="b", y="y"):
    """⊢ { (a,b)∈h } ⊢ a∈dom(h).

    Un couple de h a son antécédent dans dom(h) : de (a,b)∈h on tire (∃y)((a,y)∈h)
    (témoin b, S5), donc a∈dom(h) (AXIOME_DOM, sens arrière).  INCONDITIONNEL,
    theorie=22 : aucune propriété de bon ordre, juste la définition du domaine.
    Levier élémentaire de la maximalité.  NON vacueux : a∈dom(h) ≠ (a,b)∈h.

    ⚠️ y=« y » par défaut = liant de AXIOME_DOM (sinon les ∃ diffèrent par α-renommage)."""
    va, vb = _t(a), _t(b)
    h = TS.h_iso_max(E_set, R, F_set, Rp)
    ab = E.couple(va, vb)
    Hab = N.assume(appartient(ab, h))                    # (a,b)∈h
    Ry = appartient(E.couple(va, var(y)), h)             # (a,y)∈h  [y libre]
    # S5 : ((b|y)Ry) ⇒ (∃y)Ry ; (b|y)Ry = (a,b)∈h
    ex = N.modus_ponens(Hab, N.s5(Ry, vb, y))            # (∃y)((a,y)∈h)
    axd = N.axiome(E.theorie_ensembles(), E.AXIOME_DOM)
    domeq = instancie(instancie(axd, h), va)             # a∈dom h ⇔ (∃y)((a,y)∈h)
    return N.modus_ponens(ex, equivalence_arriere(domeq))   # a∈dom(h)


def couple_dans_h_donne_antecedent_cible(E_set="E", R="R", F_set="F", Rp="Rp", a="a"):
    """ÉNONCÉ-cible (test miroir) :  a∈dom(h)."""
    h = TS.h_iso_max(E_set, R, F_set, Rp)
    return appartient(_t(a), E.dom(h))


# ════════════════════════════════════════════════════════════════════════════
#  ✅ couple_dans_h_donne_valeur : { (a,b)∈h } ⊢ b∈pr₂(h).   INCONDITIONNEL.
# ════════════════════════════════════════════════════════════════════════════
def couple_dans_h_donne_valeur(E_set="E", R="R", F_set="F", Rp="Rp",
                               a="a", b="b", x="x"):
    """⊢ { (a,b)∈h } ⊢ b∈pr₂(h).

    Miroir de couple_dans_h_donne_antecedent côté image : (a,b)∈h ⇒ (∃x)((x,b)∈h)
    (témoin a, S5), donc b∈pr₂(h) (AXIOME_IMG, sens arrière).  INCONDITIONNEL.

    ⚠️ x=« x » par défaut = liant de AXIOME_IMG (cohérence des ∃)."""
    va, vb = _t(a), _t(b)
    h = TS.h_iso_max(E_set, R, F_set, Rp)
    ab = E.couple(va, vb)
    Hab = N.assume(appartient(ab, h))                    # (a,b)∈h
    Rx = appartient(E.couple(var(x), vb), h)             # (x,b)∈h  [x libre]
    ex = N.modus_ponens(Hab, N.s5(Rx, va, x))            # (∃x)((x,b)∈h)
    axi = N.axiome(E.theorie_ensembles(), E.AXIOME_IMG)
    imgeq = instancie(instancie(axi, h), vb)             # b∈pr₂ h ⇔ (∃x)((x,b)∈h)
    return N.modus_ponens(ex, equivalence_arriere(imgeq))   # b∈pr₂(h)


def couple_dans_h_donne_valeur_cible(E_set="E", R="R", F_set="F", Rp="Rp", b="b"):
    """ÉNONCÉ-cible (test miroir) :  b∈pr₂(h)."""
    h = TS.h_iso_max(E_set, R, F_set, Rp)
    return appartient(_t(b), E.img(h))


# ════════════════════════════════════════════════════════════════════════════
#  ✅ point_pas_dans_son_segment : ⊢ ¬( a ∈ seg(R,E,a) ).   INCONDITIONNEL.
# ════════════════════════════════════════════════════════════════════════════
def point_pas_dans_son_segment(R="R", E_set="E", a="a"):
    """⊢ ¬( a ∈ seg(R,E,a) ).

    Aucun point n'appartient à son propre segment initial ]←,a[ : par AXIOME_SEGMENT_
    EXTREMITE, a∈seg(R,E,a) ⇔ ((a∈E et R{a,a}) et a≠a) ; le conjoint a≠a contredit la
    réflexivité a=a.  INCONDITIONNEL, theorie=22.  Brique de la contradiction de
    maximalité (l'extension d'un segment propre ]←,a[ par a est exclue)."""
    va = _t(a)
    Sa = _seg(R, E_set, a)                                # seg(R,E,a) = ]←,a[
    in_Sa = appartient(va, Sa)
    Hin = N.assume(in_Sa)                                 # a∈]←,a[
    mem = _membre_seg(R, E_set, a, a)                     # a∈Sa ⇔ ((a∈E et R{a,a}) et a≠a)
    body = N.modus_ponens(Hin, equivalence_avant(mem))   # (a∈E et R{a,a}) et a≠a
    a_ne_a = conjonction_elim_droite(body)               # ¬(a=a)
    refl = N.reflexivite(va)                              # a=a
    absurd = _ex_falso(refl, a_ne_a, non(in_Sa))         # ¬(a∈Sa)   [a∈Sa]
    return _refute_self(N.loi_deduction(in_Sa, absurd))  # ¬(a∈Sa)   []


def point_pas_dans_son_segment_cible(R="R", E_set="E", a="a"):
    """ÉNONCÉ-cible (test miroir) :  ¬( a ∈ seg(R,E,a) )."""
    Sa = _seg(R, E_set, a)
    return non(appartient(_t(a), Sa))


# ════════════════════════════════════════════════════════════════════════════
#  🎯 h_maximal_preuve : ⊢ h_maximal(E,R,F,Rp).   INCONDITIONNEL.
#  FERME la FORMULE de maximalité posée (scaffold) — maximalité « par appartenance ».
# ════════════════════════════════════════════════════════════════════════════
def h_maximal_preuve(E_set="E", R="R", F_set="F", Rp="Rp", a="a", b="b"):
    """🎯 ⊢ h_maximal(E,R,F,Rp)  (FORMULE posée dans le scaffold) :

        (∀a)(∀b)( (a∈E et a∉dom h et b∈F et b∉pr₂ h) ⇒ ¬((a,b)∈h) ).

    PREUVE (contraposée).  Si (a,b)∈h alors a∈dom(h) (couple_dans_h_donne_antecedent),
    ce qui contredit la prémisse a∉dom(h) ; donc ¬((a,b)∈h).  INCONDITIONNEL, theorie=22.

    SENS.  C'est la maximalité de h « par appartenance » : h ne contient AUCUN couple
    dont l'antécédent serait HORS de dom(h) — un point nouveau a∉dom(h) ne peut pas
    déjà être apparié dans h.  NON postulée (dérivée de AXIOME_DOM + axiome de h),
    NON tautologique au sens propositionnel.  La part DURE complémentaire (qu'un tel a
    PUISSE étendre h en iso de segments) reste reportée : voir
    adjonction_contredit_segment_propre (conditionnel) et le REPORTÉ du module."""
    va, vb = _t(a), _t(b)
    vE, vF = _t(E_set), _t(F_set)
    h = TS.h_iso_max(E_set, R, F_set, Rp)
    extensible = appartient(E.couple(va, vb), h)          # (a,b)∈h
    premisse = et(et(appartient(va, vE), non(appartient(va, E.dom(h)))),
                  et(appartient(vb, vF), non(appartient(vb, E.img(h)))))
    Hprem = N.assume(premisse)
    a_notin_dom = conjonction_elim_droite(conjonction_elim_gauche(Hprem))   # ¬(a∈dom h)
    # (a,b)∈h ⇒ a∈dom h  :  on monte la preuve sous l'hypothèse extensible
    a_in_dom = couple_dans_h_donne_antecedent(E_set, R, F_set, Rp, a, b)    # {extensible}⊢a∈dom h
    # ex falso : a∈dom h et ¬(a∈dom h) ⇒ ¬extensible
    not_ext_under_ext = _ex_falso(a_in_dom, a_notin_dom, non(extensible))   # ¬ext [extensible, premisse]
    imp = N.loi_deduction(extensible, not_ext_under_ext)                    # ext⇒¬ext [premisse]
    not_ext = _refute_self(imp)                                            # ¬ext     [premisse]
    body = N.loi_deduction(premisse, not_ext)                              # premisse⇒¬ext []
    return N.generalisation(a, N.generalisation(b, body))                  # (∀a)(∀b)(…)


def h_maximal_preuve_cible(E_set="E", R="R", F_set="F", Rp="Rp", a="a", b="b"):
    """ÉNONCÉ-cible (test miroir) = la FORMULE h_maximal du scaffold."""
    return M.h_maximal(E_set, R, F_set, Rp, a, b)


# ════════════════════════════════════════════════════════════════════════════
#  ⚠️ extension_iso_donne_antecedent : sous les 7 hyps STRUCTURELLES ⊢ a∈dom(h).
#     (Si (a,b) est un point d'un iso de segments φ:S≅T, alors a∈dom h.)
# ════════════════════════════════════════════════════════════════════════════
def extension_iso_donne_antecedent(E_set="E", R="R", F_set="F", Rp="Rp",
                                   S="S", T="T", phi="phi", a="a", b="b", y="y"):
    """⊢ { S seg E, T seg F, φ:S≅T iso, a∈S, a∈E, b∈F, b=φ(a) } ⊢ a∈dom(h).

    Si (a,b) est un point (b=φ(a)) d'un iso φ:S≅T de segments, alors (a,b)∈h
    (couple_iso_dans_h) donc a∈dom(h).  CONDITIONNEL aux 7 hypothèses STRUCTURELLES
    de couple_iso_dans_h (les MÊMES, sans en ajouter).  C'est l'étape : « on ne peut
    pas étendre h par un point d'iso de segments par-dessus son domaine » — a y est
    DÉJÀ.  NON vacueux : a∈dom(h) ≠ aucune des 7 hypothèses."""
    va, vb = _t(a), _t(b)
    h = TS.h_iso_max(E_set, R, F_set, Rp)
    cid = TS.couple_iso_dans_h(E_set, R, F_set, Rp, S, T, phi, a, b)        # 7 hyps ⊢ (a,b)∈h
    Ry = appartient(E.couple(va, var(y)), h)
    ex = N.modus_ponens(cid, N.s5(Ry, vb, y))                              # (∃y)((a,y)∈h)
    axd = N.axiome(E.theorie_ensembles(), E.AXIOME_DOM)
    domeq = instancie(instancie(axd, h), va)
    return N.modus_ponens(ex, equivalence_arriere(domeq))                  # a∈dom(h)


def extension_iso_donne_antecedent_cible(E_set="E", R="R", F_set="F", Rp="Rp", a="a"):
    """ÉNONCÉ-cible (test miroir) :  a∈dom(h)."""
    h = TS.h_iso_max(E_set, R, F_set, Rp)
    return appartient(_t(a), E.dom(h))


def extension_iso_hypotheses(E_set="E", R="R", F_set="F", Rp="Rp",
                             S="S", T="T", phi="phi", a="a", b="b"):
    """Les 7 HYPOTHÈSES STRUCTURELLES (liste de formules) — celles de couple_iso_dans_h,
    partagées par extension_iso_donne_antecedent et adjonction_contredit_segment_propre.
    Pour documentation / tests miroir."""
    Rf = TS._R_de(R)
    Rpf = TS._R_de(Rp)
    vE, vF = _t(E_set), _t(F_set)
    vS, vT, vphi, va, vb = _t(S), _t(T), _t(phi), _t(a), _t(b)
    return [
        E.est_segment(vS, Rf, vE),
        E.est_segment(vT, Rpf, vF),
        V.est_isomorphisme_ordre(vphi, vS, vT, Rf, Rpf),
        appartient(va, vS),
        appartient(va, vE),
        appartient(vb, vF),
        egal(vb, E.valeur(vphi, va)),
    ]


# ════════════════════════════════════════════════════════════════════════════
#  ⚠️🎯 adjonction_contredit_segment_propre : sous les MÊMES 7 hyps ⊢
#       ¬( dom(h) = seg(R,E,a) ).  CŒUR de la maximalité (d.5), conditionnel.
# ════════════════════════════════════════════════════════════════════════════
def adjonction_contredit_segment_propre(E_set="E", R="R", F_set="F", Rp="Rp",
                                        S="S", T="T", phi="phi", a="a", b="b", y="y"):
    """🎯 ⊢ { S seg E, T seg F, φ:S≅T, a∈S, a∈E, b∈F, b=φ(a) } ⊢ ¬( dom(h) = seg(R,E,a) ).

    CŒUR de la maximalité (blueprint d.5), honnêtement CONDITIONNEL aux 7 hypothèses
    structurelles (production d'un point témoin (a,b) d'un iso de segments).

    PREUVE.  De ces hypothèses, a∈dom(h) (extension_iso_donne_antecedent).  Si l'on
    avait dom(h)=seg(R,E,a), Leibniz donnerait a∈seg(R,E,a) — IMPOSSIBLE
    (point_pas_dans_son_segment).  Donc dom(h) ≠ seg(R,E,a).

    SENS.  C'est EXACTEMENT la contradiction « (a,b) prolonge h ⇒ a∈dom h ⇒ (si dom h
    était le segment propre ]←,a[) a∈]←,a[ ⇒ a<a absurde » de l'argument d'extension
    du blueprint, réduite à ses hypothèses MINIMALES.  Donc le domaine de h ne peut
    être un segment propre ]←,a[ DÈS QU'on dispose d'un point témoin (a,b) au-dessus —
    la pierre angulaire « dom(h)=E ou pr₂(h)=F ».  NON vacueux, NON postulé.

    ⚠️ REPORTÉ (ce qui ALIMENTE ces 7 hypothèses, JAMAIS supposé ici comme acquis) :
    que ]←,a]≅]←,b] SOIT un iso de segments (adjonction du plus grand élément,
    relation_adjoint) — back-and-forth de magnitude Cantor–Bernstein."""
    va = _t(a)
    h = TS.h_iso_max(E_set, R, F_set, Rp)
    Sa = _seg(R, E_set, a)                                                  # seg(R,E,a)=]←,a[
    dom_eq_Sa = egal(E.dom(h), Sa)

    a_in_dom = extension_iso_donne_antecedent(E_set, R, F_set, Rp,
                                              S, T, phi, a, b, y)           # 7 hyps ⊢ a∈dom h
    Hdom_eq = N.assume(dom_eq_Sa)                                           # dom h = Sa
    # Leibniz : a∈dom h  +  dom h = Sa  ⇒  a∈Sa
    a_in_Sa = _leib(E.dom(h), Sa, Hdom_eq, lambda w: appartient(va, w), a_in_dom)
    # mais a∉Sa (point_pas_dans_son_segment)
    a_notin_Sa = point_pas_dans_son_segment(R, E_set, a)                    # ¬(a∈Sa)
    # contradiction ⇒ ¬(dom h = Sa)
    neg_dom = _ex_falso(a_in_Sa, a_notin_Sa, non(dom_eq_Sa))               # ¬(dom h=Sa) [7 hyps, dom_eq]
    return _refute_self(N.loi_deduction(dom_eq_Sa, neg_dom))               # ¬(dom h=Sa) [7 hyps]


def adjonction_contredit_segment_propre_cible(E_set="E", R="R", F_set="F", Rp="Rp", a="a"):
    """ÉNONCÉ-cible (test miroir) :  ¬( dom(h) = seg(R,E,a) )."""
    h = TS.h_iso_max(E_set, R, F_set, Rp)
    Sa = _seg(R, E_set, a)
    return non(egal(E.dom(h), Sa))


__all__ = [
    "couple_dans_h_donne_antecedent", "couple_dans_h_donne_antecedent_cible",
    "couple_dans_h_donne_valeur", "couple_dans_h_donne_valeur_cible",
    "point_pas_dans_son_segment", "point_pas_dans_son_segment_cible",
    "h_maximal_preuve", "h_maximal_preuve_cible",
    "extension_iso_donne_antecedent", "extension_iso_donne_antecedent_cible",
    "extension_iso_hypotheses",
    "adjonction_contredit_segment_propre", "adjonction_contredit_segment_propre_cible",
]
