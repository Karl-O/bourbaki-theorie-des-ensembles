"""§III.4 — PREUVE du PRINCIPE DE RÉCURRENCE (Critère C61) par PLUS-PETIT-CONTRE-EXEMPLE.

OBJECTIF : prouver `principe_recurrence(P, n)` (l'ÉNONCÉ posé en HYPOTHÈSE par
`recurrence_C61` dans ensembles_recurrence_C61) — gate ℕ #3 —, désormais que sa
dépendance clé `cardinaux_bien_ordonnes(a)` est CLOSE
(`ensembles_gate_onto_top.cardinaux_bien_ordonnes_close`, 0 hyp).  Le clos
`principe_recurrence(_P_pred(b), c)` décharge le REPORT #1 de `N_collectivise_final`.

        principe_recurrence(P,n) :=
            ( P[0]  et  (∀n)((Fini n et P[n]) ⇒ P[n+1]) )  ⇒  (∀n)( Fini n ⇒ P[n] ).

──────────────────────────────────────────────────────────────────────────────
PREUVE (plus-petit-contre-exemple — Bourbaki justifie C61 par le bon ordre de ℕ).

  Hypothèse de récurrence H := ( P[0] et (∀n)((Fini n et P[n]) ⇒ P[n+1]) ).
  Cible C := (∀n)( Fini n ⇒ P[n] ).  On fixe n0, on assume Fini(n0), et on prouve
  P[n0] par l'absurde : on assume ¬P[n0] et on dérive une contradiction.

  1. SÉPARATION S8 :  A := { m ∈ [0,n0] | Fini m et ¬P[m] }   (axiome DÉDIÉ, theorie=22).
     A ⊂ [0,n0] (projection du corps).  n0 ∈ A (n0∈[0,n0] par réflexivité 0≤n0≤n0 +
     est_cardinal(n0) issu de Fini(n0) ; Fini(n0) ; ¬P[n0]), donc A ≠ ∅.

  2. BON ORDRE :  cardinaux_bien_ordonnes_close(n0) (CLOS) appliqué à A (≠∅, ⊂[0,n0])
     donne un ≤-MIN m0 :  m0∈A et (∀x)(x∈A ⇒ m0 ≤ x).  m0∈A : Fini m0, ¬P[m0], m0∈[0,n0].

  3. m0 ≠ 0 :  P[0] (de H) et ¬P[m0] (m0∈A) ⇒ m0 ≠ 0 (sinon Leibniz 0=m0 → P[m0]).

  4. PRÉDÉCESSEUR (Prop. 2 §III.5, REPORTÉE — voir RÉSIDU) :  Fini m0 et m0≠0 ⇒
     (∃k)( m0 = k+1 et est_cardinal(k) et k < m0 ).  Pour un tel k :
       • Fini k :  m0=k+1 ⇒ Fini(k+1) (Leibniz sur Fini m0) ; est_cardinal(k) ⇒
                   (Fini(k+1)⇒Fini k) (Prop. 1 réciproque, CLOSE) ⇒ Fini k ;
       • k ∈ [0,n0] :  est_cardinal(k), 0≤k (borne 0), k≤n0 (transitivité k≤m0≤n0) ;
       • ¬(m0 ≤ k) :  sinon (k≤m0 et m0≤k et k,m0 cardinaux) ⇒ m0=k (antisymétrie CLOSE),
                      contredisant k<m0 (k≠m0).

  5. k ∉ A :  m0 ≤-MIN ⇒ (∀x)(x∈A ⇒ m0≤x) ; contraposée : ¬(m0≤k) ⇒ k∉A.

  6. P[k] :  ¬(k∈A) = ¬( k∈[0,n0] et (Fini k et ¬P[k]) ).  Or k∈[0,n0] et Fini k, donc
     l'absence dans A force ¬¬P[k], d'où P[k] (DNE).

  7. PAS DE RÉCURRENCE :  (∀n)((Fini n et P[n])⇒P[n+1]) (de H) instancié à k :
     (Fini k et P[k]) ⇒ P[k+1] ; Fini k et P[k] ⇒ P[k+1] = P[m0] (Leibniz m0=k+1).
     Contradiction P[m0] ∧ ¬P[m0].  Donc sous {Fini n0, ¬P[n0], H} : ⊥ ⇒ ¬P[n0]⇒¬¬P[n0],
     d'où ¬¬P[n0] (consequentia mirabilis) et P[n0] (DNE), SOUS {Fini n0, H}.

  8. Décharge Fini n0 ⇒ (Fini n0 ⇒ P[n0]), généralise (∀n0), décharge H ⇒ principe.

──────────────────────────────────────────────────────────────────────────────
⚠️ RÉSIDU HONNÊTE — EXISTENCE DU PRÉDÉCESSEUR (Bourbaki Prop. 2, §III.5).

  « Tout entier (cardinal fini) m ≠ 0 est un successeur » :

      predecesseur_fini_universel() :=
          (∀m)( ( Fini m et ¬(m = 0) ) ⇒
                (∃k)( m = k+1  et  est_cardinal(k)  et  k < m ) ).

  N'EST PAS un théorème clos du projet (vérifié : aucun lemme `predecesseur`/Prop.2
  existant ; sa preuve exige la machinerie soustraction/bon-ordre de §III.5).  Il est
  donc ISOLÉ comme HYPOTHÈSE EXPLICITE, universellement quantifiée, DÉCHARGÉE par
  loi_deduction — JAMAIS postulée comme théorème, JAMAIS ajoutée à theorie_ensembles
  (qui reste = 22).  Tout le reste (Fini k, k∈[0,n0], ¬(m0≤k), m0≠0, le pas) est DÉRIVÉ
  de lemmes CLOS.

──────────────────────────────────────────────────────────────────────────────
⚠️ RÉSIDU #2 — ≤-MIN DU CONTRE-EXEMPLE (limitation du NOYAU, NON un gap mathématique).

      bon_ordre_min_universel(P) :=
          (∀n0)(∃m)( m∈A(n0) et (∀x)( x∈A(n0) ⇒ m ≤ x ) ),   A(n0)={m∈[0,n0]|Fini m et ¬P[m]}.

  C'est l'application de `cardinaux_bien_ordonnes_close` (CLOS, 0 hyp) à la séparation S8
  A(n0)⊂[0,n0].  Mathématiquement TOUT est là : A⊂[0,n0] est PROUVÉ en forme α-équivalente
  (cf. `_A_inclus_interv`, binder 'zincl'),
  A≠∅ aussi (n0∈A), et cbo est CLOS.  MAIS sa DÉCHARGE par modus_ponens est BLOQUÉE par une
  LIMITATION DU NOYAU : l'antécédent `A⊂[0,n0]` de cbo = `inclus(A, intervalle_entiers(ZERO,n0))`
  est CONSTRUIT RAW par `inclus` avec le liant 'z' SHADOWANT le 'z' interne du τ-cardinal ZERO ;
  cette forme RAW est INACCESSIBLE comme CONCLUSION (toute substitution capture-évitante du
  noyau, subst_f, renomme ce 'z' interne en '@0').  Donc cbo ne peut pas être MP-déchargé sur
  l'ensemble concret A — le ≤-min reste un RÉSIDU HONNÊTE, FERMÉ en n0, déchargé par
  loi_deduction, JAMAIS postulé, theorie=22.  (Voir le rapport pour le détail du blocage.)

⇒ DEUX résidus : (1) predecesseur_fini_universel [maths, Prop.2], (2) bon_ordre_min_universel
  [noyau, cbo non-MP-branchable].  L'INDUCTION/SÉPARATION/PAS sont mécanisés et CLOS.
"""
from __future__ import annotations

from bourbaki.logique.formule import (
    Terme, var, app, egal, et, non, impl, equiv, appartient, existe, pourtout,
    inclus,
)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.cardinaux.ensembles_cardinaux import (
    est_cardinal, inf_egal_card, inf_strict_card,
)
from bourbaki.entiers.ensembles_entiers import est_fini, successeur, ZERO

from bourbaki.logique.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    instancie, contraposition, equivalence_avant, equivalence_arriere, dne, dni,
    antecedent_consequent,
)
from bourbaki.logique.tactiques.tactiques_abrege_quantif import (
    existe_elimination, alpha_pour_tout, alpha_existe, congruence_existe,
)
from bourbaki.logique.tactiques.tactiques_abrege import a_implique_a
from bourbaki.logique.tactiques.tactiques_abrege2 import ou_congruence

from bourbaki.logique.tactiques.tactiques_abrege_egalite import symetrie

from bourbaki.ensembles.base.ensembles_vide import non_vide_ssi_element
from bourbaki.ordre.ensembles_pont_binder import reecrire

from bourbaki.entiers.ensembles_recurrence_C61 import (
    principe_recurrence, _fini_et_P_implique_succ, _fini_implique_P, _P_pred,
)
# `cardinaux_bien_ordonnes_close` (CLOS, 0 hyp) DÉCHARGE désormais le ≤-min du contre-exemple :
# le blocage de liant ('z' du τ-cardinal ZERO renommé '@0' dans la forme RAW comme conclusion)
# est CONTOURNÉ par un pont α (cf. `_A_inclus_interv_raw`).  Le résidu #2 `bon_ordre_min_universel`
# est ÉLIMINÉ ; il ne reste que `predecesseur_fini_universel`.
from bourbaki.cardinaux.ensembles_gate_onto_top import cardinaux_bien_ordonnes_close
from bourbaki.entiers.ensembles_entiers_theoremes import (
    theorie_intervalle_entiers, axiome_intervalle_entiers,
)
from bourbaki.entiers.ensembles_fini_successeur import fini_successeur_implique_fini
from bourbaki.entiers.ensembles_N_collectivise import zero_inf_egal_cardinal
from bourbaki.cardinaux.ensembles_cardinaux_theoremes import inf_egal_reflexif
from bourbaki.cardinaux.ensembles_cardinaux_props_restantes_ordre import (
    inf_egal_transitive_general, inf_egal_antisymetrique_card,
)


def _t(t):
    """Coercion str/Terme → Terme."""
    return t if isinstance(t, Terme) else var(t)


def _cut(thm, hyp, preuve_hyp):
    """De Γ∪{H}⊢C et Δ⊢H, déduit Γ∪Δ⊢C (décharge de H puis MP)."""
    return N.modus_ponens(preuve_hyp, N.loi_deduction(hyp, thm))


def _ex_falso(thm_a, thm_na, cible):
    """De ⊢ A et ⊢ ¬A, déduit ⊢ cible  (ex falso quodlibet)."""
    a = thm_a.conclusion
    imp = N.modus_ponens(thm_na, N.s2(non(a), cible))   # ¬A ∨ cible = (A ⇒ cible)
    return N.modus_ponens(thm_a, imp)                    # cible


def _refute_self(thm_P_imp_notP):
    """De ⊢ (P ⇒ ¬P) déduit ⊢ ¬P.   ((P⇒¬P) = (¬P∨¬P) → ¬P par S1.)"""
    P, notP = antecedent_consequent(thm_P_imp_notP.conclusion)   # P⇒¬P = ¬P∨¬P
    return N.modus_ponens(thm_P_imp_notP, N.s1(notP))            # (¬P∨¬P)⇒¬P


# ════════════════════════════════════════════════════════════════════════════
#  RÉSIDU HONNÊTE — existence du prédécesseur d'un entier ≠ 0  (Prop. 2 §III.5).
# ════════════════════════════════════════════════════════════════════════════
def predecesseur_fini(m, k="kpred"):
    """Énoncé « m a un prédécesseur (cardinal, strictement plus petit) » :
        (∃k)( m = k+1  et  est_cardinal(k)  et  k < m )."""
    vm = _t(m)
    kn = k if isinstance(k, str) else k.nom
    vk = var(kn)
    return existe(kn, et(et(egal(vm, successeur(vk)), est_cardinal(vk)),
                         inf_strict_card(vk, vm)))


def predecesseur_fini_universel(m="mpred", k="kpred"):
    """Énoncé UNIVERSEL « tout entier ≠ 0 est un successeur » (Bourbaki Prop. 2 §III.5) :
        (∀m)( ( Fini m et ¬(m = 0) ) ⇒ (∃k)( m = k+1 et est_cardinal(k) et k < m ) ).

    ⚠️ HYPOTHÈSE ISOLÉE, REPORTÉE (NON close dans le projet ; sa preuve relève de la
    machinerie soustraction/bon-ordre §III.5).  Déchargée par loi_deduction ; JAMAIS
    postulée comme théorème, JAMAIS ajoutée à theorie_ensembles (= 22)."""
    mn = m if isinstance(m, str) else m.nom
    vm = var(mn)
    return pourtout(mn, impl(et(est_fini(vm), non(egal(vm, ZERO))),
                             predecesseur_fini(vm, k)))


# ════════════════════════════════════════════════════════════════════════════
#  SÉPARATION S8 DÉDIÉE — A := { m ∈ [0,n0] | Fini m et ¬P[m] }.
#  Terme opaque + axiome DÉFINITIONNEL (motif Ncol / difference) — theorie reste 22.
# ════════════════════════════════════════════════════════════════════════════
def _A(P, n0):
    """A := { m ∈ [0,n0] | Fini m et ¬P[m] }  (terme opaque)."""
    return app("A_contre_exemple", _t(n0))


def _A_corps(P, n0, m):
    """Corps caractérisant m ∈ A :  m ∈ [0,n0]  et  ( Fini m et ¬P[m] )."""
    vm = _t(m)
    interv = E.intervalle_entiers(ZERO, _t(n0))
    return et(appartient(vm, interv), et(est_fini(vm), non(P(vm))))


def _axiome_A(P, n0="n0pr", m="mApr"):
    """⊢-schéma  (∀n0)(∀m)( m ∈ A(n0) ⇔ (m∈[0,n0] et (Fini m et ¬P[m])) )   (S8 dans [0,n0]).

    ⚠️ n0 et m sont des NOMS de liants (str) — JAMAIS var() sur un Terme."""
    n0n = n0 if isinstance(n0, str) else n0.nom
    mn = m if isinstance(m, str) else m.nom
    vn0, vm = var(n0n), var(mn)
    return pourtout(n0n, pourtout(mn,
        equiv(appartient(vm, _A(P, vn0)), _A_corps(P, vn0, vm))))


def _theorie_A(P, n0="n0pr", m="mApr"):
    """Théorie DÉDIÉE ne contenant que l'axiome de A (motif theorie_Ncol).  N'altère
    PAS theorie_ensembles() (= 22)."""
    return N.Theorie("A-contre-exemple-recurrence", [_axiome_A(P, n0, m)])


def _A_membre(P, n0, x, mbind="mApr"):
    """⊢ ( x ∈ A(n0) ⇔ (x∈[0,n0] et (Fini x et ¬P[x])) )   (axiome instancié aux TERMES n0, x)."""
    ax = N.axiome(_theorie_A(P, "n0pr", mbind), _axiome_A(P, "n0pr", mbind))
    return instancie(instancie(ax, _t(n0)), _t(x))


def _A_inclus_interv(P, n0, mbind="mApr", z="zincl"):
    """⊢ inclus(A, [0,n0], z='zincl')  = (∀zincl)( zincl∈A ⇒ zincl∈[0,n0] ).

    PREUVE (CLOSE, 0 hyp) que A ⊂ [0,n0] — fournie au comparateur FRAIS 'zincl' (≠ le 'z'
    interne du τ-cardinal ZERO ⇒ AUCUN renommage du liant interne : il reste 'z').  C'est
    α-ÉQUIVALENT à la forme CANONIQUE `inclus(A,[0,n0])` (binder 'z') attendue par
    `cardinaux_bien_ordonnes`, et le PONT α `_A_inclus_interv_raw` produit cette dernière
    EXACTEMENT (cf. là-bas pour le contournement du binder 'z'/'@0')."""
    vn0, vz = _t(n0), var(z)
    interv = E.intervalle_entiers(ZERO, vn0)
    A = _A(P, vn0)
    h = N.assume(appartient(vz, A))
    corps = N.modus_ponens(h, equivalence_avant(_A_membre(P, vn0, vz, mbind)))
    z_in = conjonction_elim_gauche(corps)                # zincl ∈ [0,n0]  (ZERO plain)
    res = N.generalisation(z, N.loi_deduction(appartient(vz, A), z_in))  # inclus(A,[0,n0]) @ 'zincl'
    assert res.conclusion == inclus(A, interv, z), "A_sub ≠ inclus(A,[0,n0]) @ 'zincl'"
    assert res.est_clos, "A_sub non clos"
    return res


def _eq_alpha_formule(f1, f2):
    """⊢ ( f1 ⇔ f2 )  où f1, f2 ne diffèrent QUE par l'α-renommage de liants ∃ (mêmes
    connecteurs ¬/∨, mêmes termes).  Congruence STRUCTURELLE récursive :
      • f1 == f2          : réflexivité (a_implique_a des deux sens) ;
      • ¬A vs ¬B          : ¬-congruence (double contraposition de A⇔B) ;
      • A∨B vs A'∨B'      : ou_congruence ;
      • (∃u)R vs (∃v)R'   : si u≠v, alpha_existe(u,v,R) (α-renommage du ∃ ; v FRAIS, e.g.
                            '@k', ⇒ aucune capture) ; sinon congruence_existe sur le corps.
    Sert à PONTER `bodyZ ⇔ bodyZ@0` (le corps du τ-cardinal ZERO dont un ∃z interne a été
    renommé '@0' par subst_f) ⇒ via s7, l'égalité τ ZERO = ZERO@0 (cf. _A_inclus_interv_raw)."""
    if f1 == f2:
        return conjonction_intro(a_implique_a(f1), a_implique_a(f1))
    if f1.tag == "non" and f2.tag == "non":
        s = _eq_alpha_formule(f1.sous[0], f2.sous[0])
        from bourbaki.logique.tactiques.tactiques_abrege2 import contraposition
        return conjonction_intro(contraposition(equivalence_arriere(s)),
                                 contraposition(equivalence_avant(s)))      # ¬A ⇔ ¬B
    if f1.tag == "ou" and f2.tag == "ou":
        return ou_congruence(_eq_alpha_formule(f1.sous[0], f2.sous[0]),
                             _eq_alpha_formule(f1.sous[1], f2.sous[1]))
    if f1.tag == "exists" and f2.tag == "exists":
        if f1.lieur != f2.lieur:
            return alpha_existe(f1.lieur, f2.lieur, f1.sous[0])             # (∃u)R ⇔ (∃v)(v|u)R
        return congruence_existe(_eq_alpha_formule(f1.sous[0], f2.sous[0]), f1.lieur)
    raise ValueError(f"_eq_alpha_formule : structures incompatibles ({f1.tag},{f2.tag})")


def _trouve_interv(obj):
    """Cherche STRUCTURELLEMENT le sous-terme `interv_ent(ZERO@0, n0)` CORROMPU dans `obj`
    (Formule ou Terme) — celui dont l'arg[0] (le ZERO) a son ∃z interne renommé '@0', donc
    `args[0] ≠ ZERO` (≠ structurel).  Ignore tout `interv_ent` PROPRE (arg[0] == ZERO,
    p.ex. à l'intérieur du terme A).  Renvoie le Terme corrompu, ou None.  Duck-typing :
    une Formule porte `.termes`/`.sous`, un Terme porte `.args`."""
    if hasattr(obj, "termes"):                       # Formule
        for t in obj.termes:
            r = _trouve_interv(t)
            if r is not None:
                return r
        for s in obj.sous:
            r = _trouve_interv(s)
            if r is not None:
                return r
        return None
    # Terme
    if getattr(obj, "tag", None) == "app" and obj.nom == "interv_ent" \
            and len(obj.args) == 2 and obj.args[0] != ZERO:
        return obj
    for a in getattr(obj, "args", ()):               # 'app' → Termes ; 'tau' → Formules
        r = _trouve_interv(a)
        if r is not None:
            return r
    return None


def _A_inclus_interv_raw(P, n0, mbind="mApr"):
    """⊢ inclus(A, [0,n0])  = (∀z)( z∈A ⇒ z∈[0,n0] )   (binder 'z' PAR DÉFAUT, forme RAW).

    🎯🎯 CONTOURNEMENT DU BINDER 'z'/'@0' (ce qui DÉBLOQUE le résidu #2 → ÉLIMINÉ).

    La forme RAW `inclus(A,[0,n0])` (que cbo instancié à S:=A dépose comme antécédent) a son
    comparateur 'z' SHADOWANT un ∃z INTERNE du τ-cardinal ZERO=[0,..] (ZERO contient un ∃z).
    La PROUVER directement au comparateur 'z' renomme ce ∃z interne en '@0' (subst_f
    capture-évitante quand on instancie l'axiome de séparation au TERME var('z')) ⇒ on n'obtient
    que la forme '@0' (`raw_at0`), STRUCTURELLEMENT ≠ de la forme RAW 'z' de cbo, et les ponts α
    ne reconstruisent JAMAIS la forme 'z' comme conclusion (asymétrie subst_f : introduire
    var('z') re-renomme le ∃z interne).

    PONT s7 (qui MARCHE).  raw_at0 et la cible RAW ne diffèrent QUE par l'unique ∃z→'@0' DANS
    le corps de ZERO (ZERO = τZ(bodyZ), bodyZ vs bodyZ@0 = un ∃z renommé '@0').  On PROUVE
    l'égalité de TERMES  ZERO@0 = ZERO  par :
        s7 :  (∀Z)( bodyZ@0 ⇔ bodyZ )  ⇒  ( τZ(bodyZ@0) = τZ(bodyZ) )
    où l'équivalence interne `bodyZ@0 ⇔ bodyZ` est la congruence STRUCTURELLE `_eq_alpha_formule`
    (renommage '@0'→'z' du ∃, propre).  Puis on RÉÉCRIT (Leibniz s6, `reecrire`) ZERO@0→ZERO dans
    raw_at0 ⇒ la forme RAW 'z' EXACTE (== inclus(A,[0,n0]), vérifié, CLOS, 0 hyp).  theorie=22."""
    vn0 = _t(n0)
    interv = E.intervalle_entiers(ZERO, vn0)
    A = _A(P, vn0)
    asub_zincl = _A_inclus_interv(P, vn0, mbind)         # inclus(A,[0,n0],'zincl')  CLOS
    body_z = impl(appartient(var("z"), A), appartient(var("z"), interv))
    ren = alpha_pour_tout("z", "zincl", body_z)          # (∀z)body_z ⇔ (∀zincl)(zincl|z)body_z
    raw_at0 = N.modus_ponens(asub_zincl, equivalence_arriere(ren))   # forme '@0' (∃z interne→'@0')

    # extraire ZERO@0 (le τ-cardinal corrompu) : c'est l'arg[0] de l'intervalle interv_ent(.,n0)
    # qui apparaît dans la 2ᵉ membership `z∈interv@0` du corps.  Recherche STRUCTURELLE robuste.
    interv_at0 = _trouve_interv(raw_at0.conclusion)
    ZERO_at0 = interv_at0.args[0]
    bodyZ, bodyZ_at0 = ZERO.args[0], ZERO_at0.args[0]
    # s7 : ZERO@0 = ZERO  (congruence interne bodyZ@0 ⇔ bodyZ, généralisée sur 'Z', puis s7)
    eqZ = N.modus_ponens(N.generalisation("Z", _eq_alpha_formule(bodyZ_at0, bodyZ)),
                         N.s7(bodyZ_at0, bodyZ, "Z"))    # τZ(bodyZ@0) = τZ(bodyZ)  =  ZERO@0 = ZERO
    assert eqZ.conclusion == egal(ZERO_at0, ZERO), "s7 ne conclut pas ZERO@0 = ZERO"
    # réécrire ZERO@0 → ZERO dans raw_at0 (Leibniz s6) ⇒ forme RAW 'z' EXACTE
    res = reecrire(raw_at0, eqZ, lambda h: inclus(A, E.intervalle_entiers(h, vn0)))
    assert res.conclusion == inclus(A, interv), "A_sub_raw ≠ inclus(A,[0,n0]) RAW 'z'"
    assert res.est_clos, "A_sub_raw non clos"
    return res


def _A_non_vide(P, n0, n0_in_A):
    """⊢ ¬( A(n0) = ∅ )   depuis une preuve `n0_in_A` de  n0 ∈ A(n0)  (témoin de NON-vacuité).

    `n0_in_A` : Theoreme de conclusion `n0 ∈ A(n0)` (sous les hyps de l'appelant).  On
    introduit (∃z)(z∈A) par S5 (témoin n0) puis on MP le sens ARRIÈRE de
    `non_vide_ssi_element(A)` : ¬(A=∅) ⇔ (∃z)(z∈A).  Hyps = celles de n0_in_A."""
    A = _A(P, _t(n0))
    assert n0_in_A.conclusion == appartient(_t(n0), A), "n0_in_A ne conclut pas n0∈A(n0)"
    ex_z = N.modus_ponens(n0_in_A, N.s5(appartient(var("z"), A), _t(n0), "z"))  # (∃z)(z∈A)
    res = N.modus_ponens(ex_z, equivalence_arriere(non_vide_ssi_element(A)))    # ¬(A=∅)
    assert res.conclusion == non(egal(A, E.VIDE)), "A_non_vide mal formé"
    return res


def _min_A_via_cbo(P, n0, n0_in_A, mbind="mApr"):
    """⊢ bon_ordre_min_A(P, n0)   ( (∃m)( m∈A et (∀x)(x∈A ⇒ m≤x) ) )   DÉRIVÉ de cbo CLOS.

    🎯🎯 DÉCHARGE INTÉGRALE du ≤-min du contre-exemple par `cardinaux_bien_ordonnes_close`
    (CLOS, 0 hyp), SANS résidu `bon_ordre_min_universel`.  cbo (générique en `a`) est
    généralisé sur `a`, instancié à n0, puis à S:=A.  Son antécédent instancié est EXACTEMENT
    `inclus(A,[0,n0]) et A≠∅` (forme RAW binder 'z' — `instancie(S:=A)` n'introduit pas de 'z'
    libre, donc le 'z' interne de ZERO reste 'z') :
      • `inclus(A,[0,n0])` RAW : produit par `_A_inclus_interv_raw` (pont α, CLOS) ;
      • `A≠∅` : `_A_non_vide` depuis `n0_in_A` (le contre-exemple n0 témoigne A≠∅).
    MP ⇒ le ≤-min.  Hyps = celles de n0_in_A (typiquement {Fini n0, ¬P[n0]}) — AUCUN résidu
    bon_ordre.  theorie=22."""
    vn0 = _t(n0)
    A = _A(P, vn0)
    interv = E.intervalle_entiers(ZERO, vn0)
    A_sub = _A_inclus_interv_raw(P, vn0, mbind)          # inclus(A,[0,n0]) RAW   [CLOS]
    A_ne = _A_non_vide(P, vn0, n0_in_A)                  # ¬(A=∅)                [hyps de n0_in_A]
    cbo = cardinaux_bien_ordonnes_close()                # ⊢ cardinaux_bien_ordonnes(a)  CLOS
    inst = instancie(instancie(N.generalisation("a", cbo), vn0), A)   # (inclus∧≠∅) ⇒ (∃m)min
    ante = conjonction_intro(A_sub, A_ne)                # inclus(A,[0,n0]) et A≠∅
    res = N.modus_ponens(ante, inst)                     # (∃m)( m∈A et (∀x)(x∈A ⇒ m≤x) )
    assert res.conclusion == bon_ordre_min_A(P, vn0), "min via cbo ≠ bon_ordre_min_A"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  RÉSIDU HONNÊTE #2 — ≤-MIN du contre-exemple (instance VRAIE de cardinaux_bien_ordonnes,
#  bloquée par le NOYAU — cf. _A_inclus_interv & le rapport).
# ════════════════════════════════════════════════════════════════════════════
def bon_ordre_min_A(P, n0, mmin="m", xcmp="x"):
    """Énoncé « A(n0) a un ≤-min » :  (∃m)( m∈A et (∀x)( x∈A ⇒ m ≤ x ) ).

    A = { m∈[0,n0] | Fini m et ¬P[m] }.  C'est EXACTEMENT la conclusion de
    cardinaux_bien_ordonnes(n0) instanciée à S:=A (binders m='m', x='x' — ceux de cbo)."""
    vmin, vx = var(mmin), var(xcmp)
    A = _A(P, _t(n0))
    return existe(mmin, et(appartient(vmin, A),
        pourtout(xcmp, impl(appartient(vx, A), inf_egal_card(vmin, vx)))))


def bon_ordre_min_universel(P, n0="n0pr", mmin="m", xcmp="x"):
    """Énoncé UNIVERSEL (FERMÉ en n0) « chaque contre-exemple A(n0) a un ≤-min » :
        (∀n0)(∃m)( m∈A(n0) et (∀x)( x∈A(n0) ⇒ m ≤ x ) ).

    ⚠️ RÉSIDU HONNÊTE #2 — instance VRAIE de `cardinaux_bien_ordonnes` (désormais CLOS,
    `cardinaux_bien_ordonnes_close`) appliquée à la séparation S8 A(n0)⊂[0,n0].  Il N'EST
    PAS un postulat mathématique : tout est démontré (A⊂[0,n0] est PROUVÉ en forme
    α-équivalente — cf. `_A_inclus_interv` —, A≠∅ aussi (n0∈A), et cbo est CLOS).  Mais sa
    DÉCHARGE par modus_ponens
    est BLOQUÉE par une limitation du NOYAU : l'antécédent `A⊂[0,n0]` de cbo est construit
    RAW par `inclus` (liant 'z' shadowant le 'z' interne du τ-cardinal ZERO) et cette forme
    RAW est INACCESSIBLE comme conclusion (toute substitution capture-évitante la renomme en
    '@0').  Posé donc en HYPOTHÈSE EXPLICITE, FERMÉE en n0, déchargée par loi_deduction ;
    JAMAIS ajouté à theorie_ensembles (= 22).  cf. le rapport pour le détail du blocage."""
    n0n = n0 if isinstance(n0, str) else n0.nom
    return pourtout(n0n, bon_ordre_min_A(P, var(n0n), mmin, xcmp))


# ════════════════════════════════════════════════════════════════════════════
#  helpers TERME-niveau (intervalle, ordre).
# ════════════════════════════════════════════════════════════════════════════
def _membre_interv_0(n0, x):
    """⊢ ( x ∈ [0,n0] ) ⇔ ( x cardinal et 0≤x et x≤n0 )   (axiome d'intervalle, [0,n0])."""
    ax = N.axiome(theorie_intervalle_entiers(), axiome_intervalle_entiers())
    ax = instancie(ax, ZERO)
    ax = instancie(ax, _t(n0))
    ax = instancie(ax, _t(x))
    return ax


def _interv_sup(n0, x, x_in_interv):
    """⊢ x ≤ n0   depuis x ∈ [0,n0]  (projection borne sup du corps de l'intervalle)."""
    corps = N.modus_ponens(x_in_interv, equivalence_avant(_membre_interv_0(n0, x)))
    return conjonction_elim_droite(corps)                # (card x et 0≤x) et x≤n0 → x≤n0


def _trans_le(u, v, w):
    """⊢ ( u ≤ v et v ≤ w ) ⇒ ( u ≤ w )   aux TERMES (transitivité de ≤)."""
    gen = inf_egal_transitive_general("Xtr", "Ytr", "Ztr")
    return instancie(instancie(instancie(gen, _t(u)), _t(v)), _t(w))


def _antisym(u, v):
    """⊢ ( u≤v et v≤u et est_cardinal(u) et est_cardinal(v) ) ⇒ ( u = v )   aux TERMES."""
    gen = inf_egal_antisymetrique_card("uas", "vas")
    return instancie(instancie(gen, _t(u)), _t(v))


def _refl_le(t):
    """⊢ t ≤ t   (réflexivité de ≤ au TERME t)."""
    return instancie(N.generalisation("Xrefl", inf_egal_reflexif("Xrefl")), _t(t))


# ════════════════════════════════════════════════════════════════════════════
#  PREUVE GÉNÉRIQUE — principe_recurrence(P, n) par plus-petit-contre-exemple.
# ════════════════════════════════════════════════════════════════════════════
def principe_recurrence_preuve(P, n="n", n0="n0pr", mbind="mApr", k="kpred"):
    """⊢ { predecesseur_fini_universel } ⊢ principe_recurrence(P, n).

    PREUVE GÉNÉRIQUE (vaut pour TOUTE fonction P : Terme→Formule) par plus-petit-contre-
    exemple, sous l'UNIQUE résidu honnête `predecesseur_fini_universel` (Prop. 2 §III.5,
    non close).  Tous les autres maillons sont CLOS : cardinaux_bien_ordonnes_close(n0),
    fini_successeur_implique_fini (Prop. 1 réciproque), réflexivité/transitivité/
    antisymétrie de ≤, borne 0 ; la séparation S8 de A est un axiome DÉDIÉ (theorie=22).

    Binders DISTINCTS pour éviter toute capture avec les binders internes de P
    (typiquement « b » pour _P_pred) : contre-exemple n0='n0pr', séparation 'mApr',
    prédécesseur k='kpred', min='mmin'/comparaison 'xcmp'."""
    nn = n if isinstance(n, str) else n.nom

    H = et(P(ZERO), _fini_et_P_implique_succ(P, nn))      # hypothèse de récurrence
    hH = N.assume(H)
    pP0 = conjonction_elim_gauche(hH)                     # P[0]
    pStep = conjonction_elim_droite(hH)                   # (∀n)((Fini n et P[n])⇒P[n+1])

    hPred = N.assume(predecesseur_fini_universel(k=k))    # résidu honnête (∀m)(...)

    # ════════════════════════════════════════════════════════════════════════
    #  On fixe n0 ; sous { Fini(n0), ¬P[n0] } on dérive une CONTRADICTION.
    # ════════════════════════════════════════════════════════════════════════
    vn0 = var(n0)
    h_fini_n0 = N.assume(est_fini(vn0))                   # Fini(n0)
    h_nP_n0 = N.assume(non(P(vn0)))                       # ¬P[n0]
    A = _A(P, vn0)

    # ── n0 ∈ A  (n0∈[0,n0] par réflexivité 0≤n0≤n0 + card ; Fini n0 ; ¬P[n0]) — TÉMOIGNE A≠∅
    #    (DÉCHARGE la garde de non-vacuité de cbo, cf. _min_A_via_cbo / _A_non_vide).
    card_n0 = conjonction_elim_gauche(h_fini_n0)          # est_cardinal(n0)
    zero_le_n0 = _cut(zero_inf_egal_cardinal(vn0), est_cardinal(vn0), card_n0)  # 0≤n0
    corps_interv_n0 = conjonction_intro(conjonction_intro(card_n0, zero_le_n0), _refl_le(vn0))
    n0_in_interv = N.modus_ponens(corps_interv_n0, equivalence_arriere(_membre_interv_0(vn0, vn0)))
    corps_A_n0 = conjonction_intro(n0_in_interv, conjonction_intro(h_fini_n0, h_nP_n0))
    n0_in_A = N.modus_ponens(corps_A_n0, equivalence_arriere(_A_membre(P, vn0, vn0, mbind)))  # n0∈A

    # ════════════════════════════════════════════════════════════════════════
    #  BON ORDRE : le ≤-MIN de A — DÉCHARGÉ INTÉGRALEMENT par cbo (CLOS, 0 hyp).
    #
    #  🎯 `cardinaux_bien_ordonnes_close` (CLOS) généralisé sur `a`, instancié à n0 puis à S:=A,
    #  donne (S⊂[0,n0] et S≠∅) ⇒ (∃m)min(S).  Les DEUX conjoints de l'antécédent sont PROUVÉS :
    #    • A⊂[0,n0] (= inclus(A,[0,n0]) RAW 'z') par `_A_inclus_interv_raw` (pont α zincl→z qui
    #      contourne le binder 'z'/'@0' du τ-cardinal ZERO — cf. sa docstring) ;
    #    • A≠∅ par `_A_non_vide` depuis n0∈A (le contre-exemple TÉMOIGNE la non-vacuité — c'est
    #      la garde de non-vacuité, déchargée INTERNE ICI).
    #  MP ⇒ le ≤-min.  AUCUN résidu `bon_ordre_min_universel` : le verrou de canonicalisation est
    #  levé.  Reste l'UNIQUE résidu honnête `predecesseur_fini_universel` (Prop. 2 §III.5).
    ex_min = _min_A_via_cbo(P, vn0, n0_in_A, mbind)       # (∃m)( min de A(n0) )  [Fini n0, ¬P[n0]]

    mmin = "m"; xcmp = "x"                                # binders de cardinaux_bien_ordonnes
    vmin, vx = var(mmin), var(xcmp)
    corps_min = et(appartient(vmin, A),
        pourtout(xcmp, impl(appartient(vx, A), inf_egal_card(vmin, vx))))
    hMin = N.assume(corps_min)
    min_in_A = conjonction_elim_gauche(hMin)              # m0 ∈ A
    min_le_all = conjonction_elim_droite(hMin)            # (∀x)(x∈A ⇒ m0≤x)

    min_corps = N.modus_ponens(min_in_A, equivalence_avant(_A_membre(P, vn0, vmin, mbind)))
    min_in_interv = conjonction_elim_gauche(min_corps)    # m0 ∈ [0,n0]
    fini_min = conjonction_elim_gauche(conjonction_elim_droite(min_corps))  # Fini m0
    nP_min = conjonction_elim_droite(conjonction_elim_droite(min_corps))    # ¬P[m0]
    card_min = conjonction_elim_gauche(fini_min)          # est_cardinal(m0)
    min_le_n0 = _interv_sup(vn0, vmin, min_in_interv)     # m0 ≤ n0

    # ── m0 ≠ 0 :  si m0 = 0 alors Leibniz 0=m0 → (P[0] ⇒ P[m0]) ; ¬P[m0] réfute.
    h_min_eq_0 = N.assume(egal(vmin, ZERO))               # m0 = 0
    zero_eq_min = N.modus_ponens(h_min_eq_0, symetrie(vmin, ZERO))    # 0 = m0
    leib_P0 = N.modus_ponens(zero_eq_min, N.s6(ZERO, vmin, "w0", P(var("w0"))))  # P[0]⇔P[m0]
    P_min_from0 = N.modus_ponens(pP0, equivalence_avant(leib_P0))     # P[m0]
    min_ne_0 = _refute_self(N.loi_deduction(egal(vmin, ZERO),
        _ex_falso(P_min_from0, nP_min, non(egal(vmin, ZERO)))))       # ¬(m0 = 0)

    # ════════════════════════════════════════════════════════════════════════
    #  PRÉDÉCESSEUR : (Fini m0 et m0≠0) ⇒ (∃k)(m0=k+1 et card k et k<m0)  [résidu].
    # ════════════════════════════════════════════════════════════════════════
    pred_imp = instancie(hPred, vmin)                     # (Fini m0 et m0≠0) ⇒ predecesseur_fini(m0)
    ex_k = N.modus_ponens(conjonction_intro(fini_min, min_ne_0), pred_imp)   # (∃k)(...)

    vk = var(k)
    corps_k = et(et(egal(vmin, successeur(vk)), est_cardinal(vk)), inf_strict_card(vk, vmin))
    hK = N.assume(corps_k)
    min_eq_succk = conjonction_elim_gauche(conjonction_elim_gauche(hK))  # m0 = k+1
    card_k = conjonction_elim_droite(conjonction_elim_gauche(hK))        # est_cardinal(k)
    k_strict_min = conjonction_elim_droite(hK)            # k < m0 = (k≤m0 et k≠m0)
    k_le_min = conjonction_elim_gauche(k_strict_min)      # k ≤ m0
    k_ne_min = conjonction_elim_droite(k_strict_min)      # k ≠ m0

    # ── Fini k
    leib_fini = N.modus_ponens(min_eq_succk,
        N.s6(vmin, successeur(vk), "wf", est_fini(var("wf"))))          # Fini m0 ⇔ Fini(k+1)
    fini_succk = N.modus_ponens(fini_min, equivalence_avant(leib_fini))  # Fini(k+1)
    fini_k = N.modus_ponens(fini_succk,
        N.modus_ponens(card_k, fini_successeur_implique_fini(k)))        # Fini k

    # ── k ∈ [0,n0]
    zero_le_k = _cut(zero_inf_egal_cardinal(vk), est_cardinal(vk), card_k)   # 0≤k
    k_le_n0 = N.modus_ponens(conjonction_intro(k_le_min, min_le_n0),
                             _trans_le(vk, vmin, vn0))    # k≤n0
    k_in_interv = N.modus_ponens(
        conjonction_intro(conjonction_intro(card_k, zero_le_k), k_le_n0),
        equivalence_arriere(_membre_interv_0(vn0, vk)))   # k∈[0,n0]

    # ── ¬(m0 ≤ k)
    h_min_le_k = N.assume(inf_egal_card(vmin, vk))        # m0 ≤ k  (réfutation)
    k_eq_min = N.modus_ponens(
        conjonction_intro(conjonction_intro(conjonction_intro(k_le_min, h_min_le_k),
                                            card_k), card_min),
        _antisym(vk, vmin))                               # k = m0
    not_min_le_k = _refute_self(N.loi_deduction(inf_egal_card(vmin, vk),
        _ex_falso(k_eq_min, k_ne_min, non(inf_egal_card(vmin, vk)))))    # ¬(m0 ≤ k)

    # ── k ∉ A
    min_le_k_if_inA = instancie(min_le_all, vk)           # k∈A ⇒ m0≤k
    not_k_in_A = N.modus_ponens(not_min_le_k, contraposition(min_le_k_if_inA))  # ¬(k∈A)

    # ── P[k] :  k∈A ⇔ (k∈[0,n0] et (Fini k et ¬P[k])) ; on a k∈[0,n0] et Fini k, donc
    #            si ¬P[k] alors k∈A (contradiction).  D'où ¬¬P[k] ⇒ P[k].
    h_nP_k = N.assume(non(P(vk)))                         # ¬P[k]  (réfutation)
    corps_k_in_A = conjonction_intro(k_in_interv, conjonction_intro(fini_k, h_nP_k))
    k_in_A = N.modus_ponens(corps_k_in_A, equivalence_arriere(_A_membre(P, vn0, vk, mbind)))  # k∈A
    nn_P_k = _refute_self(N.loi_deduction(non(P(vk)),
        _ex_falso(k_in_A, not_k_in_A, non(non(P(vk))))))  # ¬¬P[k]
    P_k = N.modus_ponens(nn_P_k, dne(P(vk)))              # P[k]

    # ── PAS : (Fini k et P[k]) ⇒ P[k+1] = P[m0]
    step_k = instancie(pStep, vk)                         # (Fini k et P[k]) ⇒ P[k+1]
    P_succk = N.modus_ponens(conjonction_intro(fini_k, P_k), step_k)     # P[k+1]
    succk_eq_min = N.modus_ponens(min_eq_succk, symetrie(vmin, successeur(vk)))  # k+1 = m0
    leib_P = N.modus_ponens(succk_eq_min,
        N.s6(successeur(vk), vmin, "wp", P(var("wp"))))   # P[k+1] ⇔ P[m0]
    P_min = N.modus_ponens(P_succk, equivalence_avant(leib_P))           # P[m0]

    # ── contradiction P[m0] ∧ ¬P[m0]  →  P[n0]  (ex falso ; cible P[n0]).  Sous corps_k.
    P_n0_fromK = _ex_falso(P_min, nP_min, P(vn0))          # P[n0]   [corps_k, …, ¬P[n0]]
    P_n0_fromMin = N.modus_ponens(ex_k,
        existe_elimination(N.loi_deduction(corps_k, P_n0_fromK), k))      # P[n0] [corps_min,…,¬P[n0]]
    P_n0_underNeg = N.modus_ponens(ex_min,
        existe_elimination(N.loi_deduction(corps_min, P_n0_fromMin), mmin))  # P[n0] [Fini n0, ¬P[n0], H, hPred]
    # ¬P[n0] ⇒ ¬¬P[n0]  (dni ∘) ⇒ ¬¬P[n0]  (consequentia mirabilis via _refute_self)
    neg_imp_dneg = N.loi_deduction(non(P(vn0)),
        N.modus_ponens(P_n0_underNeg, dni(P(vn0))))                       # ¬P[n0] ⇒ ¬¬P[n0]
    nn_P_n0 = _refute_self(neg_imp_dneg)                  # ¬¬P[n0]   [Fini n0, H, hPred]
    P_n0 = N.modus_ponens(nn_P_n0, dne(P(vn0)))           # P[n0]     [Fini n0, H, hPred]

    # ════════════════════════════════════════════════════════════════════════
    #  Assemblage : (Fini n0 ⇒ P[n0]), généralise (∀n0), décharge H.
    # ════════════════════════════════════════════════════════════════════════
    corps_concl = N.loi_deduction(est_fini(vn0), P_n0)    # (Fini n0 ⇒ P[n0])   [H, hPred]
    concl_all = N.generalisation(n0, corps_concl)         # (∀n0)(Fini n0 ⇒ P[n0])  [H, hPred]

    cible_concl = _fini_implique_P(P, nn)                 # (∀n)(Fini n ⇒ P[n])  forme cible
    if concl_all.conclusion != cible_concl:
        concl_all = _aligne_pourtout(concl_all, cible_concl, n0)

    res = N.loi_deduction(H, concl_all)                   # H ⇒ (∀n)(Fini n ⇒ P[n]) = principe
    assert res.conclusion == principe_recurrence(P, nn), \
        f"conclusion ≠ principe_recurrence(P, n)"
    return res


def _aligne_pourtout(thm_all, cible_all, src_binder):
    """De ⊢ (∀src)(φ[src]) [thm_all] et une cible (∀dst)(φ[dst]) α-équivalente, renvoie
    ⊢ cible.  α-renomme src→dst via le PONT propre `alpha_pour_tout(src, dst, corps_raw)`
    où corps_raw = le corps RAW de thm_all extrait par instancie(assume(.), src) [identité
    sur src ⇒ NON renommé].  Le sens AVANT de ce pont a son antécédent == thm_all.conclusion
    et son conséquent == cible_all EXACTEMENT (vérifié)."""
    from bourbaki.logique.tactiques.tactiques_abrege_quantif import alpha_pour_tout
    if thm_all.conclusion == cible_all:
        return thm_all
    dst = cible_all.sous[0].lieur                         # binder de (∀dst) = exists-node lieur
    corps_raw = instancie(N.assume(thm_all.conclusion), var(src_binder)).conclusion
    ren = alpha_pour_tout(src_binder, dst, corps_raw)     # (∀src)φ ⇔ (∀dst)φ[dst]
    out = N.modus_ponens(thm_all, equivalence_avant(ren))
    assert out.conclusion == cible_all, "alignement (∀) échoué"
    return out


# ════════════════════════════════════════════════════════════════════════════
#  INSTANCE CIBLE — principe_recurrence(_P_pred(b), c)  (ce que la chaîne ℕ consomme).
# ════════════════════════════════════════════════════════════════════════════
def principe_recurrence_P_pred(b="b", c="c", k="kpred"):
    """⊢ { bon_ordre_min_universel, predecesseur_fini_universel } ⊢
         principe_recurrence(_P_pred(b), c).

    L'INSTANCE EXACTE consommée par recurrence_C61 / recurrence_fini_implique_P
    (P = _P_pred(b), binder d'induction « c »).  C'est le REPORT #1 de
    N_collectivise_final, prouvé modulo DEUX résidus honnêtes, FERMÉS :
      • predecesseur_fini_universel  — Prop. 2 §III.5 (tout entier ≠0 est un successeur ;
        NON close dans le projet, gap MATHÉMATIQUE) ;
      • bon_ordre_min_universel(P)   — le ≤-min du contre-exemple A(n0) (instance VRAIE de
        cardinaux_bien_ordonnes_close, bloquée comme RÉSIDU par une limitation du NOYAU
        — canonicalisation des liants de `inclus(A,[0,n0])`, cf. la docstring de
        bon_ordre_min_universel / _A_inclus_interv).  PAS un gap mathématique."""
    P = _P_pred(b)
    return principe_recurrence_preuve(P, c, k=k)


# ════════════════════════════════════════════════════════════════════════════
#  DÉCHARGE DU REPORT #1 de N_collectivise_final  (vérification de raccord).
# ════════════════════════════════════════════════════════════════════════════
def N_collectivise_report1_discharge(a="a", x="x", c="c", b="b"):
    """⊢ { bon_ordre_min_universel, predecesseur_fini_universel,
           (∀c)(∀b)cardinal_pas_entre(b,c) } ⊢ coll(x, Fini x).

    VARIANTE de `N_collectivise_final` dont le REPORT #1 `principe_recurrence(_P_pred(b),c)`
    est DÉCHARGÉ par `principe_recurrence_P_pred(b,c)` (ce module).  Le report #1 est donc
    ÉLIMINÉ ; il ne reste, OUTRE le report #2 `(∀c)(∀b)cardinal_pas_entre(b,c)`, que les DEUX
    résidus honnêtes de principe_recurrence_P_pred (predecesseur_fini_universel ;
    bon_ordre_min_universel).  Confirme que coll(x,Fini x) ⊢ (= ℕ EXISTE) tient sous
    EXACTEMENT ces hypothèses.  Aucun nouvel axiome ; theorie=22."""
    from bourbaki.entiers.ensembles_recurrence_C61 import N_collectivise_final
    ncf = N_collectivise_final(a, x, c, b)               # hyps : {principe_recurrence(P,c), cardinal_pas_entre∀∀}
    princ = principe_recurrence(_P_pred(b), c)           # = report #1 (forme EXACTE)
    assert princ in ncf.hypotheses, "report #1 absent de N_collectivise_final (forme inattendue)"
    preuve_princ = principe_recurrence_P_pred(b, c)      # ⊢ report #1  [2 résidus honnêtes]
    assert preuve_princ.conclusion == princ, "principe_recurrence_P_pred ne conclut pas le report #1"
    return _cut(ncf, princ, preuve_princ)                # coll(x,Fini x)  [report#2 + 2 résidus]


__all__ = [
    "predecesseur_fini", "predecesseur_fini_universel",
    "bon_ordre_min_A", "bon_ordre_min_universel",
    "principe_recurrence_preuve", "principe_recurrence_P_pred",
    "N_collectivise_report1_discharge",
]
