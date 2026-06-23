"""§II.4 / §III.3.3 — PROP. 10 (binaire) :  A ∩ B = ∅  ⇒  Eq(A ∪ B, A ⊔ B).

« La réunion (disjointe) de deux ensembles est équipotente à leur somme disjointe. »
Ferme le dernier mille laissé « à un round dédié » par
ensembles_recollement_props.reunion_equipotente_somme_si_bijection : la BIJECTIVITÉ
INCONDITIONNELLE (sous A∩B=∅) du recollement canonique

    W := Δ₀(A) ∪ Δ₁(B),   Δ₀(A) = {(a,(a,0)) | a∈A},  Δ₁(B) = {(b,(b,1)) | b∈B},

de A∪B sur A⊔B = (A×{0}) ∪ (B×{1}).

────────────────────────────────────────────────────────────────────────────────
On RÉUTILISE les copies marquées CLOSES (ensembles_copie_marquee, binder « e ») —
Δ_m = graphe_terme(A,(e,m)) — et l'infra recollement CLOSE (reunion_graphes_*).
Les 4 conjoints de est_bijection_de(W, A∪B, A⊔B) :

  • func W      : reunion_graphes_fonctionnelle(Δ₀,Δ₁) sous {func Δ₀, func Δ₁, dom disjoints} ;
  • dom W = A∪B : dom_reunion_graphes(Δ₀,Δ₁) = dom Δ₀ ∪ dom Δ₁ = A∪B  (copie_graphe_domaine) ;
  • inj W       : reunion_graphes_injective sous {inj Δ₀, inj Δ₁, image∩image=∅} ;
  • image W = A⊔B : image_reunion_graphes = image(Δ₀,A)∪image(Δ₁,B) = (A×{0})∪(B×{1}) = A⊔B.

⚠️ INVARIANT : theorie_ensembles() = 22.  Rien postulé ; tout DÉRIVE des copies
   marquées + de l'infra recollement, toutes closes.
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (Terme, var, egal, et, non, appartient,
                                       existe, pourtout, inclus)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege import a_implique_a
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, instancie,
)
from bourbaki.logique.i_4_egalitaires.tactiques_abrege_egalite import (
    symetrie, composer_egalites,
)

from bourbaki.ensembles.familles.ii_4_reunion_intersection_familles.ii_4_recollement_somme.ensembles_somme_disjointe import (
    somme_disjointe, ZERO, UN,
)
from bourbaki.cardinaux.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import est_bijection_de, equipotent
from bourbaki.cardinaux.arithmetique.iii_3_4_prop8_successeur.ensembles_copie_marquee import (
    _copie_graphe, copie_graphe_fonctionnel, copie_graphe_domaine,
    copie_graphe_injective, copie_graphe_image,
)
from bourbaki.ensembles.fonctions.hors_ii_3.iii_3_recollement.ensembles_restriction_somme import (
    reunion_graphes_fonctionnelle, dom_reunion_graphes,
)
from bourbaki.ensembles.fonctions.hors_ii_3.iii_3_recollement.ensembles_recollement_bijection import (
    image_reunion_graphes, reunion_graphes_injective,
)
from bourbaki.ensembles.familles.ii_4_reunion_intersection_familles.ii_4_recollement_somme.ensembles_recollement_props import (
    reunion_disjointe_binaire_disjoints,
)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def _subst_terme(term, old_t, new_v):
    """Substitution STRUCTURELLE de old_t (terme) par new_v (terme) dans `term`
    (descente récursive sur les 'app' ; les autres termes sont opaques)."""
    if term == old_t:
        return new_v
    if getattr(term, "tag", None) == "app":
        from bourbaki.logique.i_1_termes_relations.formule import app as _app
        return _app(term.nom, *[_subst_terme(arg, old_t, new_v) for arg in term.args])
    return term


def _rewrite_egalite(eq_thm, old_t, new_t, eq_old_new, w="wr"):
    """De `eq_thm` (⊢ L = R) et `eq_old_new` (⊢ old_t = new_t), réécrit old_t↦new_t
    SIMULTANÉMENT dans les DEUX membres L, R (Leibniz S6 sur la formule paramétrée)."""
    concl = eq_thm.conclusion                              # L = R
    L, Rr = concl.termes
    L_w = _subst_terme(L, old_t, var(w))
    R_w = _subst_terme(Rr, old_t, var(w))
    leib = N.modus_ponens(eq_old_new, N.s6(old_t, new_t, w, egal(L_w, R_w)))
    return N.modus_ponens(eq_thm, equivalence_avant(leib))


def _gA(a):
    """Δ₀(A) = copie marquée gauche {(a,(a,0)) | a∈A}  (binder « e »)."""
    return _copie_graphe(_t(a), ZERO)


def _gB(b):
    """Δ₁(B) = copie marquée droite {(b,(b,1)) | b∈B}  (binder « e »)."""
    return _copie_graphe(_t(b), UN)


def _W(a, b):
    """W := Δ₀(A) ∪ Δ₁(B)  (recollement canonique des copies marquées)."""
    return E.reunion(_gA(a), _gB(b))


# ════════════════════════════════════════════════════════════════════════════
#  Disjonction des domaines de Δ₀, Δ₁  sous A∩B=∅
# ════════════════════════════════════════════════════════════════════════════
def _domaines_disjoints(a, b):
    """⊢ ( A ∩ B = ∅ ) ⇒ (∀u)¬( u ∈ dom Δ₀  et  u ∈ dom Δ₁ ).

    dom Δ₀ = A, dom Δ₁ = B (copie_graphe_domaine) ; sous A∩B=∅, si u∈A et u∈B alors
    u∈A∩B=∅, contradiction (AXIOME_VIDE).  Forme exactement attendue par
    reunion_graphes_fonctionnelle (liant « u »)."""
    va, vb = _t(a), _t(b)
    gA, gB = _gA(a), _gB(b)
    domA = E.dom(gA)                                       # dom Δ₀
    domB = E.dom(gB)                                       # dom Δ₁
    vu = var("u")
    domA_eq = copie_graphe_domaine(va, ZERO)              # dom Δ₀ = A
    domB_eq = copie_graphe_domaine(vb, UN)                # dom Δ₁ = B

    disj = egal(E.intersection(va, vb), E.VIDE)
    h_disj = N.assume(disj)
    # u∈domΔ₀ et u∈domΔ₁  ⇒  u∈A et u∈B  (réécriture dom=A, dom=B)
    body = et(appartient(vu, domA), appartient(vu, domB))
    hb = N.assume(body)
    u_inA = N.modus_ponens(conjonction_elim_gauche(hb), equivalence_avant(N.modus_ponens(
        domA_eq, N.s6(domA, va, "w", appartient(vu, var("w"))))))   # u∈A
    u_inB = N.modus_ponens(conjonction_elim_droite(hb), equivalence_avant(N.modus_ponens(
        domB_eq, N.s6(domB, vb, "w", appartient(vu, var("w"))))))   # u∈B
    # u∈A∩B
    car_inter = instancie(instancie(instancie(
        N.axiome(E.theorie_ensembles(), E.AXIOME_INTER), va), vb), vu)  # u∈A∩B ⇔ (u∈A et u∈B)
    u_inter = N.modus_ponens(conjonction_intro(u_inA, u_inB), equivalence_arriere(car_inter))  # u∈A∩B
    # u∈∅  (réécriture A∩B=∅)
    u_vide = N.modus_ponens(u_inter, equivalence_avant(N.modus_ponens(
        h_disj, N.s6(E.intersection(va, vb), E.VIDE, "w", appartient(vu, var("w"))))))  # u∈∅
    n_vide = instancie(N.axiome(E.theorie_ensembles(), E.AXIOME_VIDE), vu)   # ¬(u∈∅)
    contra = N.modus_ponens(u_vide, N.modus_ponens(n_vide,
        N.s2(non(appartient(vu, E.VIDE)), non(body))))    # ¬body
    n_body = N.modus_ponens(N.loi_deduction(body, contra), N.s1(non(body)))  # ¬(u∈domΔ₀ et u∈domΔ₁)
    gen = N.generalisation("u", n_body)                   # (∀u)¬(…)
    return N.loi_deduction(disj, gen)                     # (A∩B=∅) ⇒ (∀u)¬(…)


# ════════════════════════════════════════════════════════════════════════════
#  CONJOINT 1 — func W  (sous A∩B=∅)
# ════════════════════════════════════════════════════════════════════════════
def W_fonctionnel(a, b):
    """⊢ ( A ∩ B = ∅ ) ⇒ est_fonctionnel( W ).

    reunion_graphes_fonctionnelle(Δ₀,Δ₁) sous {func Δ₀, func Δ₁, dom disjoints} :
    func Δ₀, func Δ₁ INCONDITIONNELS (copie_graphe_fonctionnel) ; dom disjoints depuis
    A∩B=∅ (_domaines_disjoints)."""
    va, vb = _t(a), _t(b)
    gA, gB = _gA(a), _gB(b)
    funcA = copie_graphe_fonctionnel(va, ZERO)            # func Δ₀
    funcB = copie_graphe_fonctionnel(vb, UN)              # func Δ₁
    rgf = reunion_graphes_fonctionnelle(gA, gB)           # {func Δ₀, func Δ₁, disj} ⊢ func(W)
    disj_formule = pourtout("u", non(et(appartient(var("u"), E.dom(gA)),
                                        appartient(var("u"), E.dom(gB)))))
    disj = egal(E.intersection(va, vb), E.VIDE)
    h_disj = N.assume(disj)
    disj_proof = N.modus_ponens(h_disj, _domaines_disjoints(a, b))   # (∀u)¬(…)  [A∩B=∅]
    # décharge les 3 hypothèses de rgf
    res = N.modus_ponens(funcA, N.loi_deduction(E.est_fonctionnel(gA), rgf))
    res = N.modus_ponens(funcB, N.loi_deduction(E.est_fonctionnel(gB), res))
    res = N.modus_ponens(disj_proof, N.loi_deduction(disj_formule, res))   # func(W)  [A∩B=∅]
    return N.loi_deduction(disj, res)                     # (A∩B=∅) ⇒ func(W)


# ════════════════════════════════════════════════════════════════════════════
#  CONJOINT 2 — dom W = A ∪ B  (INCONDITIONNEL)
# ════════════════════════════════════════════════════════════════════════════
def W_domaine(a, b):
    """⊢ dom( W ) = ( A ∪ B ).   (INCONDITIONNEL.)

    dom_reunion_graphes(Δ₀,Δ₁) ⊢ dom(W) = dom Δ₀ ∪ dom Δ₁ ; copie_graphe_domaine ⊢
    dom Δ₀=A, dom Δ₁=B ; réécritures ⇒ dom(W) = A∪B."""
    va, vb = _t(a), _t(b)
    gA, gB = _gA(a), _gB(b)
    domA, domB = E.dom(gA), E.dom(gB)
    W = _W(a, b)
    dom_eq = dom_reunion_graphes(gA, gB)                  # dom(W) = dom Δ₀ ∪ dom Δ₁
    domA_eq = copie_graphe_domaine(va, ZERO)             # dom Δ₀ = A
    domB_eq = copie_graphe_domaine(vb, UN)               # dom Δ₁ = B
    # réécrire dom Δ₀ ↦ A  dans  dom(W) = dom Δ₀ ∪ dom Δ₁
    step1 = N.modus_ponens(domA_eq, N.s6(domA, va, "w",
        egal(E.dom(W), E.reunion(var("w"), domB))))       # (domΔ₀=A) ⇒ ((dom W=domΔ₀∪domΔ₁) ⇔ (dom W=A∪domΔ₁))
    e1 = N.modus_ponens(dom_eq, equivalence_avant(step1)) # dom(W) = A ∪ dom Δ₁
    step2 = N.modus_ponens(domB_eq, N.s6(domB, vb, "w",
        egal(E.dom(W), E.reunion(va, var("w")))))         # (domΔ₁=B) ⇒ ((dom W=A∪domΔ₁) ⇔ (dom W=A∪B))
    return N.modus_ponens(e1, equivalence_avant(step2))   # dom(W) = A ∪ B


# ════════════════════════════════════════════════════════════════════════════
#  CONJOINT 4 — image W = A ⊔ B  (INCONDITIONNEL)
# ════════════════════════════════════════════════════════════════════════════
def W_image(a, b):
    """⊢ image( W,  A ∪ B ) = ( A ⊔ B ).   (INCONDITIONNEL.)

    image_reunion_graphes ⊢ image(W, domΔ₀∪domΔ₁) = image(Δ₀,domΔ₀) ∪ image(Δ₁,domΔ₁) ;
    réécritures domΔ₀=A, domΔ₁=B (les DEUX occurrences : codomaine de gauche ET argument
    de chaque image) ; copie_graphe_image ⊢ image(Δ₀,A)=A×{0}, image(Δ₁,B)=B×{1} ;
    A⊔B = (A×{0})∪(B×{1}) littéralement (déf. somme_disjointe)."""
    va, vb = _t(a), _t(b)
    gA, gB = _gA(a), _gB(b)
    domA, domB = E.dom(gA), E.dom(gB)
    W = _W(a, b)
    A0 = E.produit(va, E.singleton(ZERO))                 # A×{0}
    B1 = E.produit(vb, E.singleton(UN))                   # B×{1}
    domA_eq = copie_graphe_domaine(va, ZERO)             # dom Δ₀ = A
    domB_eq = copie_graphe_domaine(vb, UN)               # dom Δ₁ = B

    img_eq = image_reunion_graphes(gA, gB)               # image(W, domΔ₀∪domΔ₁) = image(Δ₀,domΔ₀)∪image(Δ₁,domΔ₁)
    # réécriture domΔ₀↦A puis domΔ₁↦B SIMULTANÉMENT dans les 2 membres (les 2 côtés
    # contiennent ces termes).
    e1 = _rewrite_egalite(img_eq, domA, va, domA_eq)      # image(W, A∪domΔ₁) = image(Δ₀,A)∪image(Δ₁,domΔ₁)
    e2 = _rewrite_egalite(e1, domB, vb, domB_eq)          # image(W, A∪B) = image(Δ₀,A)∪image(Δ₁,B)
    # image(Δ₀,A)=A×{0}, image(Δ₁,B)=B×{1}
    imgA_eq = copie_graphe_image(va, ZERO)               # image(Δ₀,A) = A×{0}
    imgB_eq = copie_graphe_image(vb, UN)                 # image(Δ₁,B) = B×{1}
    # réécrire image(Δ₀,A)↦A×{0} puis image(Δ₁,B)↦B×{1} dans le membre DROIT
    imgA, imgB = E.image(gA, va), E.image(gB, vb)
    s1 = N.modus_ponens(imgA_eq, N.s6(imgA, A0, "w",
        egal(E.image(W, E.reunion(va, vb)), E.reunion(var("w"), imgB))))
    e3 = N.modus_ponens(e2, equivalence_avant(s1))        # image(W,A∪B) = (A×{0})∪image(Δ₁,B)
    s2 = N.modus_ponens(imgB_eq, N.s6(imgB, B1, "w",
        egal(E.image(W, E.reunion(va, vb)), E.reunion(A0, var("w")))))
    e4 = N.modus_ponens(e3, equivalence_avant(s2))        # image(W,A∪B) = (A×{0})∪(B×{1}) = A⊔B
    assert e4.conclusion == egal(E.image(W, E.reunion(va, vb)), somme_disjointe(va, vb)), \
        "W_image : conclusion ≠ image(W, A∪B) = A⊔B"
    return e4


# ════════════════════════════════════════════════════════════════════════════
#  CONJOINT 3 — injective_dans(W, A∪B)  (sous A∩B=∅)
# ════════════════════════════════════════════════════════════════════════════
def _images_disjointes(a, b):
    """⊢ ( image(Δ₀, dom Δ₀) ∩ image(Δ₁, dom Δ₁) ) = ∅.   (INCONDITIONNEL.)

    image(Δ₀,domΔ₀)=image(Δ₀,A)=A×{0}, image(Δ₁,domΔ₁)=image(Δ₁,B)=B×{1}
    (copie_graphe_domaine + copie_graphe_image) ; (A×{0})∩(B×{1})=∅
    (reunion_disjointe_binaire_disjoints).  On REMONTE par réécriture inverse pour
    obtenir la forme image(Δ₀,domΔ₀)∩image(Δ₁,domΔ₁) attendue par
    reunion_graphes_injective."""
    va, vb = _t(a), _t(b)
    gA, gB = _gA(a), _gB(b)
    domA, domB = E.dom(gA), E.dom(gB)
    A0 = E.produit(va, E.singleton(ZERO))
    B1 = E.produit(vb, E.singleton(UN))
    base = reunion_disjointe_binaire_disjoints(va, vb)    # (A×{0})∩(B×{1}) = ∅
    imgAdom = E.image(gA, domA)                            # image(Δ₀, dom Δ₀)
    imgBdom = E.image(gB, domB)                            # image(Δ₁, dom Δ₁)
    imgA_eq = copie_graphe_image(va, ZERO)               # image(Δ₀,A) = A×{0}
    imgB_eq = copie_graphe_image(vb, UN)                 # image(Δ₁,B) = B×{1}
    domA_eq = copie_graphe_domaine(va, ZERO)             # dom Δ₀ = A
    domB_eq = copie_graphe_domaine(vb, UN)               # dom Δ₁ = B
    from bourbaki.logique.i_4_egalitaires.tactiques_abrege_egalite import congruence_terme
    # image(Δ₀, dom Δ₀) = A×{0} :  domΔ₀↦A (congruence dans le 2e arg de image, SAFE car
    # gA ne contient pas dom(gA)) donne image(Δ₀,domΔ₀)=image(Δ₀,A) ; puis =A×{0}.
    imgAdom_eq_imgAA = N.modus_ponens(domA_eq,
        congruence_terme(domA, va, E.image(gA, var("w")), "w"))   # image(Δ₀,domΔ₀) = image(Δ₀,A)
    imgAdom_eq_A0 = composer_egalites(imgAdom_eq_imgAA, imgA_eq)   # image(Δ₀,domΔ₀) = A×{0}
    imgBdom_eq_imgBB = N.modus_ponens(domB_eq,
        congruence_terme(domB, vb, E.image(gB, var("w")), "w"))   # image(Δ₁,domΔ₁) = image(Δ₁,B)
    imgBdom_eq_B1 = composer_egalites(imgBdom_eq_imgBB, imgB_eq)   # image(Δ₁,domΔ₁) = B×{1}
    # base = ((A×{0})∩(B×{1})=∅) → réécrire A×{0}↦image(Δ₀,domΔ₀), B×{1}↦image(Δ₁,domΔ₁)
    e1 = _rewrite_egalite(base, A0, imgAdom, N.modus_ponens(imgAdom_eq_A0, symetrie(imgAdom, A0)))
    e2 = _rewrite_egalite(e1, B1, imgBdom, N.modus_ponens(imgBdom_eq_B1, symetrie(imgBdom, B1)))
    assert e2.conclusion == egal(E.intersection(imgAdom, imgBdom), E.VIDE), \
        "_images_disjointes : forme ≠ image(Δ₀,domΔ₀)∩image(Δ₁,domΔ₁)=∅"
    return e2


def W_injective(a, b):
    """⊢ ( A ∩ B = ∅ ) ⇒ injective_dans( W, A ∪ B ).

    reunion_graphes_injective(Δ₀,Δ₁) ⊢ injective_dans(W, domΔ₀∪domΔ₁) sous
    {func Δ₀, func Δ₁, disj, inj Δ₀ sur domΔ₀, inj Δ₁ sur domΔ₁, images disjointes} ;
    on décharge chaque hypothèse (closes sauf disj qui vient de A∩B=∅) et on réécrit
    domΔ₀↦A, domΔ₁↦B pour obtenir injective_dans(W, A∪B)."""
    va, vb = _t(a), _t(b)
    gA, gB = _gA(a), _gB(b)
    domA, domB = E.dom(gA), E.dom(gB)
    W = _W(a, b)
    rgi = reunion_graphes_injective(gA, gB)              # injective_dans(W, domΔ₀∪domΔ₁)  [6 hyps]
    # proofs des 6 hypothèses
    funcA = copie_graphe_fonctionnel(va, ZERO)
    funcB = copie_graphe_fonctionnel(vb, UN)
    domA_eq = copie_graphe_domaine(va, ZERO)             # dom Δ₀ = A
    domB_eq = copie_graphe_domaine(vb, UN)               # dom Δ₁ = B
    # inj Δ₀ sur dom Δ₀ : copie_graphe_injective donne inj(Δ₀, A) ; réécrire A↦domΔ₀
    injA_A = copie_graphe_injective(va, ZERO)            # injective_dans(Δ₀, A)
    injA = N.modus_ponens(injA_A, equivalence_avant(N.modus_ponens(
        N.modus_ponens(domA_eq, symetrie(domA, va)),
        N.s6(va, domA, "w", E.injective_dans(gA, var("w"))))))   # injective_dans(Δ₀, dom Δ₀)
    injB_B = copie_graphe_injective(vb, UN)              # injective_dans(Δ₁, B)
    injB = N.modus_ponens(injB_B, equivalence_avant(N.modus_ponens(
        N.modus_ponens(domB_eq, symetrie(domB, vb)),
        N.s6(vb, domB, "w", E.injective_dans(gB, var("w"))))))   # injective_dans(Δ₁, dom Δ₁)
    img_disj = _images_disjointes(a, b)                  # image(Δ₀,domΔ₀)∩image(Δ₁,domΔ₁)=∅
    disj_formule = pourtout("u", non(et(appartient(var("u"), domA),
                                        appartient(var("u"), domB))))
    disj = egal(E.intersection(va, vb), E.VIDE)
    h_disj = N.assume(disj)
    disj_proof = N.modus_ponens(h_disj, _domaines_disjoints(a, b))   # (∀u)¬(…)  [A∩B=∅]

    # décharge les 6 hypothèses de rgi (toutes par leur preuve respective)
    res = rgi
    for formule, preuve in [
        (E.est_fonctionnel(gA), funcA),
        (E.est_fonctionnel(gB), funcB),
        (disj_formule, disj_proof),
        (E.injective_dans(gA, domA), injA),
        (E.injective_dans(gB, domB), injB),
        (egal(E.intersection(E.image(gA, domA), E.image(gB, domB)), E.VIDE), img_disj),
    ]:
        res = N.modus_ponens(preuve, N.loi_deduction(formule, res))   # décharge  [+ A∩B=∅ via disj_proof]
    # res : injective_dans(W, domΔ₀∪domΔ₁)   [A∩B=∅]  ; réécrire domΔ₀↦A, domΔ₁↦B
    inj_W = res
    # injective_dans(W, domΔ₀∪domΔ₁) ↦ injective_dans(W, A∪domΔ₁) ↦ injective_dans(W, A∪B)
    s1 = N.modus_ponens(domA_eq, N.s6(domA, va, "w",
        E.injective_dans(W, E.reunion(var("w"), domB))))
    inj1 = N.modus_ponens(inj_W, equivalence_avant(s1))   # injective_dans(W, A∪domΔ₁)
    s2 = N.modus_ponens(domB_eq, N.s6(domB, vb, "w",
        E.injective_dans(W, E.reunion(va, var("w")))))
    inj2 = N.modus_ponens(inj1, equivalence_avant(s2))    # injective_dans(W, A∪B)  [A∩B=∅]
    return N.loi_deduction(disj, inj2)                    # (A∩B=∅) ⇒ injective_dans(W, A∪B)


# ════════════════════════════════════════════════════════════════════════════
#  🎯 ASSEMBLAGE — est_bijection_de(W, A∪B, A⊔B)  puis  Eq(A∪B, A⊔B)
# ════════════════════════════════════════════════════════════════════════════
def W_est_bijection(a, b):
    """⊢ ( A ∩ B = ∅ ) ⇒ est_bijection_de( W, A∪B, A⊔B ).

    Les 4 conjoints : func W (W_fonctionnel, sous A∩B=∅), dom W=A∪B (W_domaine, clos),
    inj W (W_injective, sous A∩B=∅), image W=A⊔B (W_image, clos).
    est_bijection_de = ((func ∧ dom) ∧ (inj ∧ image))."""
    va, vb = _t(a), _t(b)
    W = _W(a, b)
    src = E.reunion(va, vb)
    dst = somme_disjointe(va, vb)
    disj = egal(E.intersection(va, vb), E.VIDE)
    h = N.assume(disj)
    c1 = N.modus_ponens(h, W_fonctionnel(a, b))           # func W
    c2 = W_domaine(a, b)                                  # dom W = A∪B   (clos)
    c3 = N.modus_ponens(h, W_injective(a, b))             # inj W
    c4 = W_image(a, b)                                    # image W = A⊔B (clos)
    bij = conjonction_intro(conjonction_intro(c1, c2), conjonction_intro(c3, c4))
    assert bij.conclusion == est_bijection_de(W, src, dst), \
        "W_est_bijection : conjonction ≠ est_bijection_de(W, A∪B, A⊔B)"
    return N.loi_deduction(disj, bij)                     # (A∩B=∅) ⇒ est_bijection_de(W, A∪B, A⊔B)


def eq_reunion_somme(a, b):
    """⊢ ( A ∩ B = ∅ ) ⇒ Eq( A ∪ B, A ⊔ B ).   (THÉORÈME CLOS, 0 hyp — Prop. 10 §II.4.)

    🎯🎯 La réunion disjointe ≃ somme : S5 (témoin W) sur est_bijection_de(F, A∪B, A⊔B)
    donne (∃F)bij = Eq(A∪B, A⊔B), sous A∩B=∅."""
    va, vb = _t(a), _t(b)
    W = _W(a, b)
    src = E.reunion(va, vb)
    dst = somme_disjointe(va, vb)
    disj = egal(E.intersection(va, vb), E.VIDE)
    h = N.assume(disj)
    bij = N.modus_ponens(h, W_est_bijection(a, b))        # est_bijection_de(W, A∪B, A⊔B)
    eq = N.modus_ponens(bij, N.s5(est_bijection_de(var("F"), src, dst), W, "F"))  # Eq(A∪B, A⊔B)
    assert eq.conclusion == equipotent(src, dst), "eq_reunion_somme : conclusion ≠ Eq(A∪B, A⊔B)"
    return N.loi_deduction(disj, eq)                      # (A∩B=∅) ⇒ Eq(A∪B, A⊔B)


__all__ = ["_gA", "_gB", "_W", "_domaines_disjoints", "W_fonctionnel",
           "W_domaine", "W_image", "_images_disjointes", "W_injective",
           "W_est_bijection", "eq_reunion_somme"]
