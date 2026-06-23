"""§III.2 — Lemme 1 : RÉCONCILIATION DU CODOMAINE.

────────────────────────────────────────────────────────────────────────────────
RÔLE.  La fusion de deux isos de segments emboîtés (Lemme 1 §III.2) produit
φ1 : S1 ≅ T1  et  φ2 : S2 ≅ T2  (S1 ⊂ S2) avec des codomaines T1, T2 a priori
DIFFÉRENTS.  Or `coincidence_close` / `coincidence_univ` exigent que φ1 et φ2|S1
partagent UN codomaine.  Ce module FRANCHIT ce raccord en prouvant :

        T1 = image(φ2, S1).

C.-à-d. : l'iso φ1 : S1 ≅ T1 et la restriction φ2|S1 : S1 ≅ φ2⟨S1⟩ ont LA MÊME
IMAGE (le même codomaine effectif).

────────────────────────────────────────────────────────────────────────────────
STRATÉGIE (fidèle à la note de l'énoncé).

  (1) φ2|S1 = restriction(φ2,S1) est un iso  S1 ≅ image(φ2,S1)  (`iso_restriction_image`) :
      • fonctionnel / dom=S1 / injectif / compatible-ordre : les QUATRE briques de
        `ensembles_restriction_iso_pieces` ;
      • surjectif sur image(φ2,S1) : `restriction_image_egale_image` (CLOS) donne
        image(φ2|S1, S1) = image(φ2, S1) = `est_surjective(φ2|S1, S1, image(φ2,S1))`.
      On RECOLLE est_isomorphisme_ordre(φ2|S1, S1, image(φ2,S1), R, R').

  (2) ψ := (φ2|S1) ∘ (φ1⁻¹) : T1 ≅ image(φ2,S1)  (`iso_T1_vers_image`) :
      φ1⁻¹ : T1 ≅ S1  (`reciproque_isomorphisme_ordre`) puis composée avec (1)
      (`composee_isomorphisme_ordre`).  C'est un iso d'ordre de (T1,R') sur (I,R').

  (3) T1 et I=image(φ2,S1) sont DEUX SEGMENTS d'un bon ordre (F,R') donc COMPARABLES
      (`segments_abstraits_comparables`) :  T1 ⊂ I  ou  I ⊂ T1.

  (4) Chaque inclusion stricte est RÉFUTÉE par Cor 1 (`cor1_pas_dans_segment` /
      `lemme_4`) appliqué à un iso entre segments emboîtés d'un même bon ordre, dont
      la stricte croissance vient de `strict_croissante_depuis_iso`.  L'antisymétrie
      de ⊂ (`inclusion_antisymetrique`) conclut T1 = I.

────────────────────────────────────────────────────────────────────────────────
INVARIANT : theorie_ensembles() = 22.  RÉUTILISE des théorèmes déjà certifiés ;
rien postulé ; non vacueux.  Construction GRADUÉE — chaque sous-lemme est testé et
SAUVEGARDÉ avant le suivant.
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (
    Terme, var, egal, et, ou, non, impl, appartient, inclus, pourtout,
)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.ordre.iii_1_relations_ordre.ordre_treillis import ensembles_ordre_vocab as V
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    instancie, equivalence_avant, equivalence_arriere,
)
from bourbaki.logique.i_4_egalitaires.tactiques_abrege_egalite import symetrie, composer_egalites


def _t(x):
    """var(x) sur un NOM ; coercition sûre si x est déjà un Terme (bug var(Terme))."""
    return x if isinstance(x, Terme) else var(x)


def _R_de(R):
    """Relation-graphe R{a,b} := (a,b) ∈ R  (convention iso / segment / bon ordre)."""
    vR = _t(R)
    return lambda a, b: appartient(E.couple(_t(a), _t(b)), vR)


# ════════════════════════════════════════════════════════════════════════════
#  SOUS-LEMME (1) — φ2|S1 est un isomorphisme d'ordre de S1 sur image(φ2, S1).
# ════════════════════════════════════════════════════════════════════════════
def iso_restriction_image(phi2="phi2", S1="S1", S2="S2", R="R", Rp="Rp",
                          x="a", y="b"):
    """⊢ { compatible_ordre(φ2, S2, R, R'),  injective_dans(φ2, S2),
            inclus(S1, S2),  est_fonctionnel(φ2),  inclus(S1, dom φ2) }
          ⊢ est_isomorphisme_ordre(φ2|S1, S1, image(φ2,S1), R, R')  [liants x, y].

    La RESTRICTION φ2|S1 = restriction(φ2,S1) est un iso d'ordre de S1 sur son image
    φ2⟨S1⟩.  Les CINQ hypothèses sont les données NESTÉES de la fusion (φ2 vit sur le
    grand segment S2 ⊇ S1, compatible/injective sur S2).  Assemblage :
      • injective_dans(φ2|S1, S1)        ← restriction_injective_piece ;
      • compatible_ordre(φ2|S1, S1, R, R') ← restriction_compatible_ordre_piece ;
      • est_surjective(φ2|S1, S1, image(φ2,S1))  =  image(φ2|S1,S1)=image(φ2,S1)
                                            ← restriction_image_egale_image (CLOS).
    On RECOLLE est_bijective = et(injective, surjective) puis
    est_isomorphisme_ordre = et(est_bijective, compatible_ordre).

    Binders d'ordre x, y par défaut (forme canonique de est_isomorphisme_ordre).
    L'injectivité / la compatibilité utilisent les liants c,d / a,b en INTERNE.
    """
    from bourbaki.cardinaux.ensembles_restriction_iso_pieces import (
        restriction_injective_piece, restriction_compatible_ordre_piece,
    )
    from bourbaki.cardinaux.ensembles_cantor_bernstein_bij import (
        restriction_image_egale_image,
    )
    Rf, Rpf = _R_de(R), _R_de(Rp)
    vphi2, vS1 = _t(phi2), _t(S1)
    fX = E.restriction(vphi2, vS1)
    img = E.image(vphi2, vS1)                       # I = image(φ2, S1)

    # ── injectivité de φ2|S1 sur S1 ───────────────────────────────────────────
    inj = restriction_injective_piece(phi2, S1, S2)            # injective_dans(φ2|S1, S1)[c,d]
    #     hyps : injective_dans(φ2,S2)[c,d], inclus(S1,S2), est_fonctionnel(φ2), inclus(S1,dom φ2)
    # α-renomme les liants c,d ↦ u,up (forme canonique de injective_dans dans est_bijective)
    inj = instancie(instancie(inj, var("u")), var("up"))
    inj = N.generalisation("u", N.generalisation("up", inj))   # injective_dans(φ2|S1, S1)[u,up]
    assert inj.conclusion == E.injective_dans(fX, vS1)

    # ── surjectivité de φ2|S1 sur image(φ2,S1) ────────────────────────────────
    #   est_surjective(φ2|S1, S1, I) = egal(image(φ2|S1,S1), I) = restriction_image_egale_image.
    surj = restriction_image_egale_image(phi2, S1)            # ⊢ image(φ2|S1,S1)=image(φ2,S1)  [CLOS]
    assert surj.conclusion == E.est_surjective(fX, vS1, img), \
        "restriction_image_egale_image n'est pas est_surjective(φ2|S1,S1,image(φ2,S1))"

    # ── bijectivité = injective ET surjective ─────────────────────────────────
    bij = conjonction_intro(inj, surj)                         # est_bijective(φ2|S1, S1, I)
    assert bij.conclusion == E.est_bijective(fX, vS1, img)

    # ── compatibilité d'ordre de φ2|S1 sur S1 (liants x, y attendus par l'iso) ─
    compat = restriction_compatible_ordre_piece(phi2, S1, S2, R, Rp, x=x, y=y)
    #     compatible_ordre(φ2|S1, S1, R, R')[x,y]
    assert compat.conclusion == V.compatible_ordre(fX, vS1, Rf, Rpf, x, y)

    # ── est_isomorphisme_ordre = et(bijective, compatible) ────────────────────
    iso = conjonction_intro(bij, compat)
    assert iso.conclusion == V.est_isomorphisme_ordre(fX, vS1, img, Rf, Rpf, x, y), \
        "recollement iso(φ2|S1,S1,image) ≠ forme canonique"
    return iso


def iso_restriction_image_cible(phi2="phi2", S1="S1", S2="S2", R="R", Rp="Rp",
                                x="a", y="b"):
    """ÉNONCÉ-cible (test miroir) : est_isomorphisme_ordre(φ2|S1, S1, image(φ2,S1), R, R')."""
    Rf, Rpf = _R_de(R), _R_de(Rp)
    vphi2, vS1 = _t(phi2), _t(S1)
    fX = E.restriction(vphi2, vS1)
    return V.est_isomorphisme_ordre(fX, vS1, E.image(vphi2, vS1), Rf, Rpf, x, y)


def iso_restriction_vers_T1(phi2="phi2", S1="S1", T1="T1", S2="S2", F="F",
                            R="R", Rp="Rp", x="a", y="b", phi1="phi1"):
    """⊢ { hyps de iso_restriction_image  ∪  hyps de codomaine_egal_image }
          ⊢ est_isomorphisme_ordre(φ2|S1, S1, T1, R, R')  [liants x, y].

    🎯 RACCORD DE CODOMAINE APPLIQUÉ : `iso_restriction_image` donne
    iso(φ2|S1, S1, image(φ2,S1)) ; `codomaine_egal_image` donne T1 = image(φ2,S1) ;
    on RÉÉCRIT (Leibniz S6) le codomaine image(φ2,S1) ↦ T1 dans l'iso → iso(φ2|S1, S1, T1).
    C'est EXACTEMENT l'hypothèse iso(φ2|S1, S1, T1) consommée par coincidence_close_isos
    (versant nesté) : la restriction de φ2 à S1 est un iso de S1 sur le MÊME codomaine T1
    que φ1.  Le codomaine n'apparaît qu'au conjoint surjectif (egal(image(φ2|S1,S1), ·)),
    d'où une réécriture S6 propre (un seul site)."""
    Rf, Rpf = _R_de(R), _R_de(Rp)
    vphi2, vS1, vT1 = _t(phi2), _t(S1), _t(T1)
    fX, img = E.restriction(vphi2, vS1), E.image(vphi2, vS1)
    iso_img = iso_restriction_image(phi2, S1, S2, R, Rp, x, y)        # iso(φ2|S1,S1,image)[x,y]
    ceq = codomaine_egal_image(phi1, phi2, S1, T1, S2, F, R, Rp)      # ⊢ T1 = image(φ2,S1)
    img_eq_T1 = N.modus_ponens(ceq, symetrie(vT1, img))              # ⊢ image(φ2,S1) = T1
    hole = V.est_isomorphisme_ordre(fX, vS1, var("w"), Rf, Rpf, x, y)  # iso(φ2|S1,S1, w )
    equiv = N.modus_ponens(img_eq_T1, N.s6(img, vT1, "w", hole))      # iso[image] ⇔ iso[T1]
    return N.modus_ponens(iso_img, equivalence_avant(equiv))          # iso(φ2|S1, S1, T1)[x,y]


def iso_restriction_vers_T1_cible(phi2="phi2", S1="S1", T1="T1", R="R", Rp="Rp", x="a", y="b"):
    """ÉNONCÉ-cible (test miroir) : est_isomorphisme_ordre(φ2|S1, S1, T1, R, R')."""
    Rf, Rpf = _R_de(R), _R_de(Rp)
    vphi2, vS1, vT1 = _t(phi2), _t(S1), _t(T1)
    return V.est_isomorphisme_ordre(E.restriction(vphi2, vS1), vS1, vT1, Rf, Rpf, x, y)


# ════════════════════════════════════════════════════════════════════════════
#  Helpers de pont de liants d'ordre (idiome _rename_iso_y, partagé).
# ════════════════════════════════════════════════════════════════════════════
def _rename_iso_order_binders(iso_thm, b1, b2):
    """α-renomme les DEUX liants de quantification d'ORDRE d'un théorème iso
    (et(bijective, compatible_ordre[·,·])) vers (b1, b2), SANS toucher au conjoint
    bijective (dont les liants u,up sont fixés par la définition).

    iso_thm.conclusion = et(est_bijective(φ,S,T), (∀p)(∀q) compatible) ; on instancie
    le corps compatible à (b1,b2) puis on regénéralise.  Hypothèses PRÉSERVÉES.
    (Généralisation de `_rename_iso_y` de ensembles_coincidence_geometrie : ici on
    renomme LES DEUX liants, utile pour aligner a,b ↦ x,x2 ou w ↦ x2.)"""
    bij = conjonction_elim_gauche(iso_thm)                  # est_bijective(φ,S,T)
    compat = conjonction_elim_droite(iso_thm)               # (∀·)(∀·) compatible
    body = instancie(instancie(compat, var(b1)), var(b2))   # corps[b1, b2]
    compat2 = N.generalisation(b1, N.generalisation(b2, body))
    return conjonction_intro(bij, compat2)


# ════════════════════════════════════════════════════════════════════════════
#  SOUS-LEMME (2) — ψ := (φ2|S1) ∘ (φ1⁻¹) est un iso d'ordre de T1 sur image(φ2,S1).
# ════════════════════════════════════════════════════════════════════════════
def iso_T1_vers_image(phi1="phi1", phi2="phi2", S1="S1", T1="T1", S2="S2",
                      R="R", Rp="Rp"):
    """⊢ { iso(φ1,S1,T1,R,R'), func φ1, dom φ1=S1,
            compatible_ordre(φ2,S2,R,R'), injective_dans(φ2,S2),
            inclus(S1,S2), func φ2, inclus(S1,dom φ2) }
          ⊢ est_isomorphisme_ordre( (φ2|S1)∘(φ1⁻¹), T1, image(φ2,S1), R', R' )  [x,x2].

    ψ := composee(φ2|S1, φ1⁻¹) : T1 ≅ image(φ2,S1).
      • φ1⁻¹ : T1 ≅ S1 (R'→R)         ← reciproque_isomorphisme_ordre(φ1) ;
      • φ2|S1 : S1 ≅ image(φ2,S1) (R→R') ← iso_restriction_image (SOUS-LEMME 1) ;
      • composée                       ← composee_isomorphisme_ordre.
    Les six hyps internes de la composée sont DÉCHARGÉES vers les données honnêtes ;
    les ponts de liants (a,b / w ↦ x,x2) sont franchis par _rename_iso_order_binders.
    """
    from bourbaki.cardinaux.ensembles_iso_ordre_composee import composee_isomorphisme_ordre
    from bourbaki.cardinaux.ensembles_iso_ordre_reciproque import reciproque_isomorphisme_ordre
    from bourbaki.cardinaux.ensembles_bijection import (
        reciproque_fonctionnelle, reciproque_domaine,
    )
    from bourbaki.cardinaux.ensembles_restriction_iso_pieces import (
        restriction_fonctionnelle_piece, restriction_domaine_piece,
    )
    Rf, Rpf = _R_de(R), _R_de(Rp)
    vphi1, vphi2, vS1, vT1, vS2 = _t(phi1), _t(phi2), _t(S1), _t(T1), _t(S2)
    finv = E.reciproque(vphi1)                              # φ1⁻¹
    fX = E.restriction(vphi2, vS1)                          # φ2|S1
    img = E.image(vphi2, vS1)                               # I = image(φ2,S1)

    # ── base : la composée (φ2|S1)∘(φ1⁻¹), 6 hyps internes, binders x,x2 ──────────
    base = composee_isomorphisme_ordre(
        f=finv, g=fX, S=vT1, T=vS1, U=img, R=Rpf, Rp=Rf, Rpp=Rpf)
    #   conclusion : iso(ψ, T1, image(φ2,S1), R', R')  [x,x2]

    # formes EXACTES des 6 hypothèses internes (relues de composee_isomorphisme_ordre)
    h_func_finv = E.est_fonctionnel(finv)
    h_iso_finv  = V.est_isomorphisme_ordre(finv, vT1, vS1, Rpf, Rf, "x", "x2")
    h_iso_fX    = V.est_isomorphisme_ordre(fX, vS1, img, Rf, Rpf, "x", "x2")
    h_func_fX   = E.est_fonctionnel(fX)
    h_dom_fX    = egal(E.dom(fX), vS1)
    h_dom_finv  = egal(E.dom(finv), vT1)
    for hh in (h_func_finv, h_iso_finv, h_iso_fX, h_func_fX, h_dom_fX, h_dom_finv):
        assert hh in set(base.hypotheses), "hyp interne composée introuvable: " + str(hh)[:60]

    # ── (3) iso(φ2|S1, S1, image, R, R')[x,x2] ← SOUS-LEMME 1 (binders a,b → x,x2) ──
    iso_fX_ab = iso_restriction_image(phi2, S1, S2, R, Rp, x="a", y="b")
    iso_fX = _rename_iso_order_binders(iso_fX_ab, "x", "x2")    # iso(φ2|S1,S1,I,R,R')[x,x2]
    assert iso_fX.conclusion == h_iso_fX, "renommage iso(φ2|S1) ≠ forme attendue par composée"
    base = N.modus_ponens(iso_fX, N.loi_deduction(h_iso_fX, base))   # décharge (3)

    # ── pré-requis bijectivité de φ1 (extrait de iso(φ1,S1,T1)) ───────────────────
    iso_phi1 = V.est_isomorphisme_ordre(vphi1, vS1, vT1, Rf, Rpf, "x", "w")
    H_iso_phi1 = N.assume(iso_phi1)
    bij_phi1 = conjonction_elim_gauche(H_iso_phi1)             # est_bijective(φ1,S1,T1)
    inj_phi1 = conjonction_elim_gauche(bij_phi1)              # injective_dans(φ1,S1)
    img_phi1 = conjonction_elim_droite(bij_phi1)             # image(φ1,S1)=T1

    # ── (2) iso(φ1⁻¹, T1, S1, R', R)[x,x2] ← reciproque_isomorphisme_ordre(φ1) (w→x2) ──
    rio = reciproque_isomorphisme_ordre(phi1, S1, T1, Rf, Rpf)   # iso(φ1⁻¹,T1,S1,R',R)[x,w]
    rio = _rename_iso_order_binders(rio, "x", "x2")              # → [x,x2]
    assert rio.conclusion == h_iso_finv, "renommage iso(φ1⁻¹) ≠ forme attendue par composée"
    #   hyps de rio : iso(φ1,S1,T1)[x,w], func φ1, dom φ1=S1 ; on décharge iso(φ1) par H_iso_phi1
    rio = N.modus_ponens(H_iso_phi1, N.loi_deduction(iso_phi1, rio))
    base = N.modus_ponens(rio, N.loi_deduction(h_iso_finv, base))   # décharge (2)

    # ── (1) func(φ1⁻¹) ← reciproque_fonctionnelle {inj(φ1,S1), func φ1, dom φ1=S1} ──
    rf = reciproque_fonctionnelle(phi1, S1)                      # func(φ1⁻¹)
    rf = N.modus_ponens(inj_phi1, N.loi_deduction(E.injective_dans(vphi1, vS1), rf))
    base = N.modus_ponens(rf, N.loi_deduction(h_func_finv, base))   # décharge (1)

    # ── (6) dom(φ1⁻¹)=T1 ← reciproque_domaine {dom φ1=S1, image(φ1,S1)=T1} ─────────
    rd = reciproque_domaine(phi1, S1, T1)                       # dom(φ1⁻¹)=T1
    rd = N.modus_ponens(img_phi1, N.loi_deduction(egal(E.image(vphi1, vS1), vT1), rd))
    base = N.modus_ponens(rd, N.loi_deduction(h_dom_finv, base))    # décharge (6)

    # ── (4) func(φ2|S1) ← restriction_fonctionnelle_piece {func φ2} ───────────────
    rfX = restriction_fonctionnelle_piece(phi2, S1)             # func(φ2|S1) {func φ2}
    base = N.modus_ponens(rfX, N.loi_deduction(h_func_fX, base))    # décharge (4)

    # ── (5) dom(φ2|S1)=S1 ← restriction_domaine_piece {inclus(S1,dom φ2)} ─────────
    rdX = restriction_domaine_piece(phi2, S1)                   # dom(φ2|S1)=S1 {S1⊂dom φ2}
    base = N.modus_ponens(rdX, N.loi_deduction(h_dom_fX, base))     # décharge (5)

    return base                  # iso(ψ, T1, image(φ2,S1), R', R')[x,x2]


def iso_T1_vers_image_cible(phi1="phi1", phi2="phi2", S1="S1", T1="T1",
                            R="R", Rp="Rp"):
    """ÉNONCÉ-cible : est_isomorphisme_ordre((φ2|S1)∘(φ1⁻¹), T1, image(φ2,S1), R', R')."""
    Rf, Rpf = _R_de(R), _R_de(Rp)
    vphi1, vphi2, vS1, vT1 = _t(phi1), _t(phi2), _t(S1), _t(T1)
    psi = E.composee(E.restriction(vphi2, vS1), E.reciproque(vphi1))
    return V.est_isomorphisme_ordre(psi, vT1, E.image(vphi2, vS1), Rpf, Rpf, "x", "x2")


# ════════════════════════════════════════════════════════════════════════════
#  SOUS-LEMME (3) — χ:B→A iso (A⊂B segments d'un bon ordre) ⟹ B⊂A (donc B=A).
#  CŒUR : χ vu comme self-map de B (A⊂B) STRICTEMENT CROISSANT ; lemme_4 donne
#  x ≤ χ(x), et la propriété de SEGMENT de A (χ(x)∈A, x∈F, x≤χ(x) ⟹ x∈A) tire B⊂A.
# ════════════════════════════════════════════════════════════════════════════
def _chi_dans_B(chi, B, A, j_hole_unused=None):
    """⊢ { dom χ=B, image(χ,B)=A, inclus(A,B) } ⊢ (∀t)( t∈B ⇒ valeur(χ,t,b="j")∈B ).

    χ : B→A ; comme A⊂B, χ envoie B DANS B (forme self-map τ_j attendue par lemme_4).
    χ(t)[y]∈A (valeur_dans_but_surjectif, surjectivité image=A) ; A⊂B ⇒ χ(t)[y]∈B ;
    pont y→j (valeur_j_egal_y) ⇒ χ(t)[j]∈B."""
    from bourbaki.cardinaux.ensembles_iso_ordre_composee import valeur_dans_but_surjectif
    from bourbaki.ordre.iii_1_relations_ordre.isomorphismes_ordre.ensembles_valeur_bridge import valeur_j_egal_y
    vchi, vB, vA = _t(chi), _t(B), _t(A)
    vt = var("t")
    ct_y = E.valeur(vchi, vt)               # χ(t)[y]
    ct_j = E.valeur(vchi, vt, b="j")        # χ(t)[j]
    Ht = N.assume(appartient(vt, vB))       # t∈B

    ct_in_A = valeur_dans_but_surjectif(vchi, vB, vA, vt)        # χ(t)[y]∈A  {image=A,dom=B,t∈B}
    ct_in_A = N.modus_ponens(Ht, N.loi_deduction(appartient(vt, vB), ct_in_A))
    # A⊂B ⇒ χ(t)[y]∈B
    Hsub = N.assume(inclus(vA, vB))
    ct_y_in_B = N.modus_ponens(ct_in_A, instancie(Hsub, ct_y))  # χ(t)[y]∈B
    # pont y→j : χ(t)[j]=χ(t)[y] ⇒ χ(t)[j]∈B
    eq_jy = valeur_j_egal_y(vchi, vt)                           # χ(t)[j]=χ(t)[y]
    eqv = N.modus_ponens(eq_jy, N.s6(ct_j, ct_y, "hcdb", appartient(var("hcdb"), vB)))
    ct_j_in_B = N.modus_ponens(ct_y_in_B, equivalence_arriere(eqv))   # χ(t)[j]∈B
    body = N.loi_deduction(appartient(vt, vB), ct_j_in_B)
    return N.generalisation("t", body)      # (∀t)(t∈B ⇒ χ(t)[j]∈B)


def _strict_croissante_depuis_iso_into(chi, B, A, Rp):
    """⊢ { iso(χ, B, A, R', R')[a,b] }  ⊢ est_strictement_croissante(R',R',χ,B,B).

    Comme `strict_croissante_depuis_iso` MAIS l'iso a un BUT A ⊃ image (χ:B→A) au lieu
    du self-map B→B : seuls compatible_ordre(χ,B,R',R') et injective_dans(χ,B) sont
    consommés (la part surjective image=A n'intervient pas), via les deux ponts
    (compat_y_vers_jv / inj_y_vers_jv) + iso_donne_strict_croissant (CLOS).
    χ est un TERME (composée/réciproque) ; relations R' des deux côtés."""
    from bourbaki.cardinaux.ensembles_coincidence_pont import (
        compat_y_vers_jv, inj_y_vers_jv,
    )
    from bourbaki.cardinaux.ensembles_iso_unicite_finale import (
        _compat_yv, _inj_hyp, iso_donne_strict_croissant,
    )
    from bourbaki.ordre.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_vocab import compatible_ordre
    Rpf = _R_de(Rp)
    vchi, vB, vA = _t(chi), _t(B), _t(A)
    iso = V.est_isomorphisme_ordre(vchi, vB, vA, Rpf, Rpf, "a", "b")   # 1 hyp (binders a,b)
    Hiso = N.assume(iso)
    bij = conjonction_elim_gauche(Hiso)                              # est_bijective(χ,B,A)
    co = conjonction_elim_droite(Hiso)                              # compatible_ordre(χ,B,R',R')[a,b]
    inj = conjonction_elim_gauche(bij)                              # injective_dans(χ,B)

    # ponts compat τ_y→τ_j et inj τ_y→τ_j (réutilise coincidence_pont, χ TERME)
    compat_jv = N.modus_ponens(
        co, N.loi_deduction(compatible_ordre(vchi, vB, Rpf, Rpf, x="a", y="b"),
                            compat_y_vers_jv(vchi, vB, Rp, "a", "b")))   # _compat_yv(χ,B,R')
    inj_jv = N.modus_ponens(
        inj, N.loi_deduction(E.injective_dans(vchi, vB),
                             inj_y_vers_jv(vchi, vB)))                   # _inj_hyp(χ,B)

    idsc = iso_donne_strict_croissant(Rp, vB, vchi)   # consomme _compat_yv + _inj_hyp
    out = N.modus_ponens(compat_jv, N.loi_deduction(_compat_yv(vchi, vB, Rpf), idsc))
    out = N.modus_ponens(inj_jv, N.loi_deduction(_inj_hyp(vchi, vB), out))
    return out                                        # est_strictement_croissante(R',R',χ,B,B)


def segment_inclus_par_iso(chi, A, B, Rp, F, a="a", t="t"):
    """⊢ { est_bien_ordonne(R',F), est_segment(A,R',F),
            inclus(A,B), inclus(B,F),
            iso(χ, B, A, R', R')[a,b], dom χ=B, image(χ,B)=A }
          ⊢ inclus(B, A).

    🎯 CŒUR de la réconciliation : un iso χ : B ≅ A entre DEUX SEGMENTS EMBOÎTÉS A⊂B
    d'un bon ordre (F,R') force B⊂A (donc, avec A⊂B, l'ÉGALITÉ).

    🔑 BON ORDRE AMBIANT.  lemme_4 est appliqué via `lemme_4_sous_domaine` sur le bon
    ordre AMBIANT (F,R') + inclus(B,F), JAMAIS bo(R',B) (FAUSSE pour un segment PROPRE
    B⊊F : la composante réflexive R'{x,x}⇔x∈B échoue pour x∈F∖B).  C'est le fix du REPORT
    historique « reste hyp bo(R',B) mais on a bo(R',F) » : les DEUX hyps bo(R',F) et
    inclus(B,F) sont DÉJÀ dans le séquent de segment_inclus_par_iso, donc le résidu se
    discharge sans rien ajouter.

    PREUVE.  χ:B→A, A⊂B, donc χ envoie B DANS B (`_chi_dans_B`) ; χ est strictement
    croissant (`_strict_croissante_depuis_iso_into`).  lemme_4_sous_domaine sur (F,R')|B :
    ∀x∈B, R'{x, χ(x)}.  Pour a∈B : χ(a)∈A et a≤χ(a) ; A étant un SEGMENT de F, de
    χ(a)∈A, a∈F (a∈B⊂F) et a≤χ(a) on conclut a∈A.  D'où B⊂A.

    χ est un TERME (ψ ou ψ⁻¹).  Binder de point « a », élément courant « t »."""
    from bourbaki.cardinaux.ensembles_lemme4_sous_domaine import lemme_4_sous_domaine
    from bourbaki.cardinaux.ensembles_lemme4_croissante import _val
    Rpf = _R_de(Rp)
    vchi, vA, vB, vF = _t(chi), _t(A), _t(B), _t(F)
    vt = var(t)
    chit = _val(vchi, vt)                   # χ(t)[j]

    # χ:B→B (forme τ_j) et stricte croissance
    fdans = _chi_dans_B(vchi, vB, vA)       # {dom χ=B, image(χ,B)=A, A⊂B} ⊢ (∀t)(t∈B⇒χ(t)[j]∈B)
    scr = _strict_croissante_depuis_iso_into(vchi, vB, vA, Rp)   # {iso(χ,B,A,R',R')} ⊢ strict crois χ B→B

    # lemme_4_sous_domaine sur (F,R')|B : (∀x)(x∈B ⇒ R'{x, χ(x)})  [bo AMBIANT bo(R',F)+inclus(B,F)]
    l4 = lemme_4_sous_domaine(Rp, vF, vB, vchi)  # hyps : bo(R',F), inclus(B,F), map, strict crois
    #   décharge la map self χ:B→B et la stricte croissance  (bo(R',F)+inclus(B,F) restent)
    from bourbaki.cardinaux.ensembles_lemme4_croissante import _f_dans_E
    from bourbaki.ordre.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_monotone import est_strictement_croissante
    l4 = N.modus_ponens(fdans, N.loi_deduction(_f_dans_E(vchi, vB), l4))
    l4 = N.modus_ponens(scr, N.loi_deduction(
        est_strictement_croissante(var(Rp), var(Rp), vchi, vB, vB), l4))
    #   reste hyps : bo(R',F), inclus(B,F)  — TOUTES DEUX dans le séquent de cette fonction.

    # corps : t∈B ⇒ t∈A
    Ht = N.assume(appartient(vt, vB))
    Rt_chit = N.modus_ponens(Ht, instancie(l4, vt))            # R'{t, χ(t)}  i.e. (t,χ(t))∈R'
    # χ(t)∈A (de _chi_dans_B on a χ(t)∈B ; il faut χ(t)∈A : valeur_dans_but_surjectif + pont)
    chit_in_A = _chi_t_in_A(vchi, vB, vA, vt, Ht)              # χ(t)[j]∈A
    # t∈F (de t∈B et B⊂F)
    HBF = N.assume(inclus(vB, vF))
    t_in_F = N.modus_ponens(Ht, instancie(HBF, vt))           # t∈F
    # SEGMENT de A : (χ(t)∈A et t∈F et R'{t,χ(t)}) ⇒ t∈A
    Hseg = N.assume(E.est_segment(vA, Rpf, vF))
    seg_clause = conjonction_elim_droite(Hseg)                # (∀x)(∀y)((x∈A et y∈F et R'{y,x})⇒y∈A)
    seg_inst = instancie(instancie(seg_clause, chit), vt)     # (χ(t)∈A et t∈F et R'{t,χ(t)})⇒t∈A
    t_in_A = N.modus_ponens(
        conjonction_intro(conjonction_intro(chit_in_A, t_in_F), Rt_chit), seg_inst)
    body = N.loi_deduction(appartient(vt, vB), t_in_A)
    return N.generalisation(t, body)        # (∀t)(t∈B ⇒ t∈A) = inclus(B,A)


def _chi_t_in_A(vchi, vB, vA, vt, Ht):
    """sous {dom χ=B, image(χ,B)=A, t∈B} ⊢ χ(t)[j]∈A  (valeur_dans_but_surjectif + pont y→j)."""
    from bourbaki.cardinaux.ensembles_iso_ordre_composee import valeur_dans_but_surjectif
    from bourbaki.ordre.iii_1_relations_ordre.isomorphismes_ordre.ensembles_valeur_bridge import valeur_j_egal_y
    ct_y = E.valeur(vchi, vt)
    ct_j = E.valeur(vchi, vt, b="j")
    ct_in_A = valeur_dans_but_surjectif(vchi, vB, vA, vt)       # χ(t)[y]∈A
    ct_in_A = N.modus_ponens(Ht, N.loi_deduction(appartient(vt, vB), ct_in_A))
    eq_jy = valeur_j_egal_y(vchi, vt)                          # χ(t)[j]=χ(t)[y]
    eqv = N.modus_ponens(eq_jy, N.s6(ct_j, ct_y, "hcta", appartient(var("hcta"), vA)))
    return N.modus_ponens(ct_in_A, equivalence_arriere(eqv))   # χ(t)[j]∈A


# ════════════════════════════════════════════════════════════════════════════
#  THÉORÈME — RÉCONCILIATION DU CODOMAINE :  T1 = image(φ2, S1).
# ════════════════════════════════════════════════════════════════════════════
def codomaine_egal_image(phi1="phi1", phi2="phi2", S1="S1", T1="T1", S2="S2",
                         F="F", R="R", Rp="Rp"):
    """⊢ {  est_isomorphisme_ordre(φ1, S1, T1, R, R'),  est_fonctionnel(φ1),  dom φ1=S1,
            est_isomorphisme_ordre(φ2, S2, T2, R, R'),  est_fonctionnel(φ2),  dom φ2=S2,
            inclus(S1, S2),
            est_segment(T1, R', F),  est_segment(image(φ2,S1), R', F),
            est_bien_ordonne(R', F) }                          [BON ORDRE AMBIANT seul]
          ⊢ egal(T1, image(φ2, S1)).

    🎯 RÉCONCILIATION DU CODOMAINE (Lemme 1 §III.2).  φ1 : S1 ≅ T1 et φ2|S1 : S1 ≅ φ2⟨S1⟩
    ont LA MÊME IMAGE.  Nécessaire car coincidence_close exige que φ1 et φ2|S1 partagent
    un codomaine, alors que la fusion livre φ1:S1≅T1, φ2:S2≅T2 (codomaines a priori
    distincts).

    PREUVE.
      (1) φ2|S1 : S1 ≅ I:=image(φ2,S1)  (iso_restriction_image, SOUS-LEMME 1) ;
      (2) ψ := (φ2|S1)∘(φ1⁻¹) : T1 ≅ I   (iso_T1_vers_image, SOUS-LEMME 2) ;
      (3) T1 et I sont DEUX SEGMENTS du bon ordre (F,R') donc COMPARABLES
          (segments_abstraits_comparables) :  T1 ⊂ I  ou  I ⊂ T1 ;
      (4) chaque inclusion entraîne l'inclusion RÉCIPROQUE par segment_inclus_par_iso
          (SOUS-LEMME 3, via lemme_4 + propriété de segment) :
            • I ⊂ T1  ⟹  ψ : T1 ≅ I, self-map de T1 ⟹ T1 ⊂ I ;
            • T1 ⊂ I  ⟹  ψ⁻¹ : I ≅ T1, self-map de I ⟹ I ⊂ T1 ;
          d'où la DOUBLE INCLUSION puis l'ÉGALITÉ (inclusion_antisymetrique).

    🔑 BON ORDRE AMBIANT (fix du REPORT historique).  est_bien_ordonne(R',T1) et
    est_bien_ordonne(R',I) NE SONT PLUS portées : le cœur segment_inclus_par_iso route
    désormais par lemme_4_sous_domaine, qui consomme le bon ordre AMBIANT bo(R',F) +
    inclus(B,F) (B = T1 ou I) au lieu de la formule LITTÉRALE bo(R',B) (FAUSSE sur un
    segment PROPRE : R'{x,x}⇔x∈B échoue pour x∈F∖B).  Les inclus(T1,F)/inclus(I,F)
    nécessaires sont DÉRIVÉS du conjoint gauche de est_segment (non portés).  Le séquent
    ne porte donc QUE bo(R',F).  theorie=22 ; conclusion non vacueuse."""
    from bourbaki.cardinaux.ensembles_iso_ordre_reciproque import reciproque_isomorphisme_ordre
    from bourbaki.cardinaux.ensembles_bijection import (
        reciproque_fonctionnelle, reciproque_domaine, image_reciproque,
        composee_domaine,
    )
    from bourbaki.cardinaux.ensembles_restriction_iso_pieces import (
        restriction_fonctionnelle_piece, restriction_domaine_piece,
    )
    from bourbaki.ensembles.fonctions.ii_3_7_composee_fonctions.ensembles_fonctions_composee import composee_fonctionnelle
    from bourbaki.cardinaux.ensembles_segment_comparabilite_abstrait import (
        segments_abstraits_comparables,
    )
    from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import cas
    from bourbaki.ordre.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_relation import inclusion_antisymetrique

    Rf, Rpf = _R_de(R), _R_de(Rp)
    vphi1, vphi2, vS1, vT1, vS2, vF = _t(phi1), _t(phi2), _t(S1), _t(T1), _t(S2), _t(F)
    finv1 = E.reciproque(vphi1)                     # φ1⁻¹
    fX = E.restriction(vphi2, vS1)                  # φ2|S1
    psi = E.composee(fX, finv1)                     # ψ = (φ2|S1)∘(φ1⁻¹)
    I = E.image(vphi2, vS1)                         # I = image(φ2, S1)

    # ── pré-requis : injectivité / image de φ1 (de iso(φ1,S1,T1)) ────────────────
    iso_phi1 = V.est_isomorphisme_ordre(vphi1, vS1, vT1, Rf, Rpf, "x", "w")
    H_iso_phi1 = N.assume(iso_phi1)
    bij_phi1 = conjonction_elim_gauche(H_iso_phi1)
    inj_phi1 = conjonction_elim_gauche(bij_phi1)            # injective_dans(φ1,S1)
    img_phi1 = conjonction_elim_droite(bij_phi1)           # image(φ1,S1)=T1

    # ── (2) iso ψ : T1 ≅ I  (SOUS-LEMME 2), aligné en binders a,b pour le sous-lemme 3 ──
    iso_psi_x = iso_T1_vers_image(phi1, phi2, S1, T1, S2, R, Rp)   # iso(ψ,T1,I,R',R')[x,x2]
    iso_psi_ab = _rename_iso_order_binders(iso_psi_x, "a", "b")    # iso(ψ,T1,I,R',R')[a,b]

    # ── structurelles de ψ : dom ψ=T1, image(ψ,T1)=I, func ψ ──────────────────────
    img_psi = conjonction_elim_droite(conjonction_elim_gauche(iso_psi_x))  # image(ψ,T1)=I
    #   dom φ1⁻¹=T1, image(φ1⁻¹,T1)=S1, func φ1⁻¹  (pièces réciproque, déchargées vers honnêtes)
    rd1 = reciproque_domaine(phi1, S1, T1)                  # dom(φ1⁻¹)=T1  {dom φ1=S1, image(φ1,S1)=T1}
    rd1 = N.modus_ponens(img_phi1, N.loi_deduction(egal(E.image(vphi1, vS1), vT1), rd1))
    ir1 = image_reciproque(phi1, S1, T1)                   # image(φ1⁻¹,T1)=S1  {dom φ1=S1, image(φ1,S1)=T1}
    ir1 = N.modus_ponens(img_phi1, N.loi_deduction(egal(E.image(vphi1, vS1), vT1), ir1))
    rf1 = reciproque_fonctionnelle(phi1, S1)               # func(φ1⁻¹)  {inj(φ1,S1), func φ1, dom φ1=S1}
    rf1 = N.modus_ponens(inj_phi1, N.loi_deduction(E.injective_dans(vphi1, vS1), rf1))
    #   dom(φ2|S1)=S1, func(φ2|S1)  (pièces restriction, déchargées vers honnêtes)
    rdX = restriction_domaine_piece(phi2, S1)              # dom(φ2|S1)=S1  {S1⊂dom φ2}
    rfX = restriction_fonctionnelle_piece(phi2, S1)        # func(φ2|S1)    {func φ2}
    #   dom ψ=T1  (composee_domaine : g=φ2|S1, f=φ1⁻¹, X=T1, Y=S1)
    dom_psi = composee_domaine(fX, finv1, vT1, vS1)        # dom(ψ)=T1  {dom(φ2|S1)=S1, dom(φ1⁻¹)=T1, image(φ1⁻¹,T1)=S1}
    dom_psi = N.modus_ponens(rdX, N.loi_deduction(egal(E.dom(fX), vS1), dom_psi))
    dom_psi = N.modus_ponens(rd1, N.loi_deduction(egal(E.dom(finv1), vT1), dom_psi))
    dom_psi = N.modus_ponens(ir1, N.loi_deduction(egal(E.image(finv1, vT1), vS1), dom_psi))
    #   func ψ  (composee_fonctionnelle, CLOS : (func(φ1⁻¹) et func(φ2|S1)) ⇒ func ψ)
    #   ⚠ ordre du conjoint = (func F=φ1⁻¹) puis (func G=φ2|S1), cf. signature (g, f).
    func_psi_impl = composee_fonctionnelle(fX, finv1)
    func_psi = N.modus_ponens(conjonction_intro(rf1, rfX), func_psi_impl)   # func(ψ)

    # ── conjoints gauches de est_segment : inclus(T1,F), inclus(I,F) ──────────────
    H_seg_T1 = N.assume(E.est_segment(vT1, Rpf, vF))
    H_seg_I  = N.assume(E.est_segment(I, Rpf, vF))
    incl_T1_F = conjonction_elim_gauche(H_seg_T1)          # inclus(T1,F)
    incl_I_F  = conjonction_elim_gauche(H_seg_I)           # inclus(I,F)

    # ════════════════════════════════════════════════════════════════════════════
    #  BRANCHE B :  inclus(I, T1)  ⟹  T1 = I.   (ψ : T1≅I self-map de T1.)
    # ════════════════════════════════════════════════════════════════════════════
    #   segment_inclus_par_iso(χ=ψ, A=I, B=T1) ⊢ inclus(T1,I)
    #     hyps : bo(R',T1), est_segment(I,R',F), inclus(I,T1), inclus(T1,F),
    #            iso(ψ,T1,I,R',R')[a,b], dom ψ=T1, image(ψ,T1)=I
    sB = segment_inclus_par_iso(psi, I, vT1, Rp, vF, t="z")  # ⊢ inclus(T1,I)  (binder z = celui de inclus)
    sB = N.modus_ponens(iso_psi_ab, N.loi_deduction(
        V.est_isomorphisme_ordre(psi, vT1, I, Rpf, Rpf, "a", "b"), sB))
    sB = N.modus_ponens(dom_psi, N.loi_deduction(egal(E.dom(psi), vT1), sB))
    sB = N.modus_ponens(img_psi, N.loi_deduction(egal(E.image(psi, vT1), I), sB))
    sB = N.modus_ponens(H_seg_I, N.loi_deduction(E.est_segment(I, Rpf, vF), sB))
    sB = N.modus_ponens(incl_T1_F, N.loi_deduction(inclus(vT1, vF), sB))
    #   reste hyps : bo(R',T1), inclus(I,T1)
    H_inc_I_T1 = N.assume(inclus(I, vT1))
    sB = N.modus_ponens(H_inc_I_T1, N.loi_deduction(inclus(I, vT1), sB))   # ⊢ inclus(T1,I)  {bo(R',T1), inclus(I,T1)}
    #   double inclusion → T1=I
    ia = inclusion_antisymetrique(vT1, I)                  # (T1⊂I et I⊂T1) ⇒ T1=I
    eqB = N.modus_ponens(conjonction_intro(sB, H_inc_I_T1), ia)   # T1=I  {bo(R',T1), inclus(I,T1)}
    brB = N.loi_deduction(inclus(I, vT1), eqB)             # inclus(I,T1) ⇒ T1=I

    # ════════════════════════════════════════════════════════════════════════════
    #  BRANCHE A :  inclus(T1, I)  ⟹  T1 = I.   (ψ⁻¹ : I≅T1 self-map de I.)
    # ════════════════════════════════════════════════════════════════════════════
    psi_inv = E.reciproque(psi)                            # ψ⁻¹
    #   iso(ψ⁻¹, I, T1, R', R')  via reciproque_isomorphisme_ordre(ψ, T1, I, R', R')
    rio = reciproque_isomorphisme_ordre(psi, vT1, I, Rpf, Rpf)   # iso(ψ⁻¹,I,T1,R',R')[x,w]
    iso_psi_xw = V.est_isomorphisme_ordre(psi, vT1, I, Rpf, Rpf, "x", "w")
    iso_psi_xw_proof = _rename_iso_order_binders(iso_psi_x, "x", "w")    # iso(ψ,T1,I)[x,w]
    rio = N.modus_ponens(iso_psi_xw_proof, N.loi_deduction(iso_psi_xw, rio))
    rio = N.modus_ponens(func_psi, N.loi_deduction(E.est_fonctionnel(psi), rio))
    rio = N.modus_ponens(dom_psi, N.loi_deduction(egal(E.dom(psi), vT1), rio))   # iso(ψ⁻¹,I,T1,R',R')[x,w]
    iso_psiinv_ab = _rename_iso_order_binders(rio, "a", "b")             # iso(ψ⁻¹,I,T1)[a,b]
    #   dom ψ⁻¹=I, image(ψ⁻¹,I)=T1
    rd_inv = reciproque_domaine(psi, vT1, I)               # dom(ψ⁻¹)=I  {dom ψ=T1, image(ψ,T1)=I}
    rd_inv = N.modus_ponens(dom_psi, N.loi_deduction(egal(E.dom(psi), vT1), rd_inv))
    rd_inv = N.modus_ponens(img_psi, N.loi_deduction(egal(E.image(psi, vT1), I), rd_inv))
    ir_inv = image_reciproque(psi, vT1, I)                 # image(ψ⁻¹,I)=T1  {dom ψ=T1, image(ψ,T1)=I}
    ir_inv = N.modus_ponens(dom_psi, N.loi_deduction(egal(E.dom(psi), vT1), ir_inv))
    ir_inv = N.modus_ponens(img_psi, N.loi_deduction(egal(E.image(psi, vT1), I), ir_inv))
    #   segment_inclus_par_iso(χ=ψ⁻¹, A=T1, B=I) ⊢ inclus(I,T1)
    #     hyps : bo(R',I), est_segment(T1,R',F), inclus(T1,I), inclus(I,F),
    #            iso(ψ⁻¹,I,T1,R',R')[a,b], dom ψ⁻¹=I, image(ψ⁻¹,I)=T1
    sA = segment_inclus_par_iso(psi_inv, vT1, I, Rp, vF, t="z")  # ⊢ inclus(I,T1)  (binder z)
    sA = N.modus_ponens(iso_psiinv_ab, N.loi_deduction(
        V.est_isomorphisme_ordre(psi_inv, I, vT1, Rpf, Rpf, "a", "b"), sA))
    sA = N.modus_ponens(rd_inv, N.loi_deduction(egal(E.dom(psi_inv), I), sA))
    sA = N.modus_ponens(ir_inv, N.loi_deduction(egal(E.image(psi_inv, I), vT1), sA))
    sA = N.modus_ponens(H_seg_T1, N.loi_deduction(E.est_segment(vT1, Rpf, vF), sA))
    sA = N.modus_ponens(incl_I_F, N.loi_deduction(inclus(I, vF), sA))
    #   reste hyps : bo(R',I), inclus(T1,I)
    H_inc_T1_I = N.assume(inclus(vT1, I))
    sA = N.modus_ponens(H_inc_T1_I, N.loi_deduction(inclus(vT1, I), sA))   # ⊢ inclus(I,T1)  {bo(R',I), inclus(T1,I)}
    eqA = N.modus_ponens(conjonction_intro(H_inc_T1_I, sA), ia)           # T1=I
    brA = N.loi_deduction(inclus(vT1, I), eqA)            # inclus(T1,I) ⇒ T1=I

    # ── comparabilité des deux segments T1, I de (F,R') ───────────────────────────
    comp = segments_abstraits_comparables(Rp, F, T1, I)   # inclus(T1,I) ou inclus(I,T1)

    # ── preuve par cas : T1 = I ───────────────────────────────────────────────────
    out = cas(comp, brA, brB)                             # egal(T1, image(φ2,S1))

    # ════════════════════════════════════════════════════════════════════════════
    #  RÉCONCILIATION des hyps φ2 vers la forme NESTÉE de la fusion (target signature).
    #  Les sous-lemmes consomment compat(φ2,S2), inj(φ2,S2), inclus(S1,dom φ2) — STRICTEMENT
    #  PLUS FAIBLES que les données honnêtes iso(φ2,S2,T2), dom φ2=S2 fournies par la fusion.
    #  On les DÉRIVE pour que le séquent porte EXACTEMENT iso(φ2,S2,T2)+func φ2+dom φ2=S2.
    # ════════════════════════════════════════════════════════════════════════════
    vT2 = var("T2")
    #   (i) compat(φ2,S2)[a,b] et inj(φ2,S2)[c,d] ← iso(φ2,S2,T2,R,R')[a,b]
    iso_phi2 = V.est_isomorphisme_ordre(vphi2, vS2, vT2, Rf, Rpf, "a", "b")
    H_iso_phi2 = N.assume(iso_phi2)
    bij_phi2 = conjonction_elim_gauche(H_iso_phi2)         # est_bijective(φ2,S2,T2)
    compat_phi2 = conjonction_elim_droite(H_iso_phi2)      # compatible_ordre(φ2,S2,R,R')[a,b]
    inj_phi2_uup = conjonction_elim_gauche(bij_phi2)       # injective_dans(φ2,S2)[u,up]
    #   α-renomme injective u,up ↦ c,d (forme consommée par restriction_injective_piece)
    inj_phi2_cd = N.generalisation("c", N.generalisation("d",
        instancie(instancie(inj_phi2_uup, var("c")), var("d"))))   # injective_dans(φ2,S2)[c,d]
    compat_form = V.compatible_ordre(vphi2, vS2, Rf, Rpf, "a", "b")
    inj_form_cd = E.injective_dans(vphi2, vS2, "c", "d")
    if compat_form in set(out.hypotheses):
        out = N.modus_ponens(compat_phi2, N.loi_deduction(compat_form, out))
    if inj_form_cd in set(out.hypotheses):
        out = N.modus_ponens(inj_phi2_cd, N.loi_deduction(inj_form_cd, out))
    #   (ii) inclus(S1, dom φ2) ← inclus(S1,S2) et dom φ2=S2  (Leibniz S2→dom φ2)
    incl_dom_form = inclus(vS1, E.dom(vphi2))
    if incl_dom_form in set(out.hypotheses):
        H_inc12 = N.assume(inclus(vS1, vS2))
        H_dom2 = N.assume(egal(E.dom(vphi2), vS2))         # dom φ2 = S2 (donnée fusion)
        S2_eq_dom = N.modus_ponens(H_dom2, symetrie(E.dom(vphi2), vS2))   # S2 = dom φ2
        # inclus(S1,S2) ⇒ inclus(S1,dom φ2)  par Leibniz (S2 → dom φ2)
        eqv = N.modus_ponens(S2_eq_dom,
            N.s6(vS2, E.dom(vphi2), "hdom2", inclus(vS1, var("hdom2"))))
        incl_dom = N.modus_ponens(H_inc12, equivalence_avant(eqv))        # inclus(S1, dom φ2)
        out = N.modus_ponens(incl_dom, N.loi_deduction(incl_dom_form, out))
    return out                                            # egal(T1, image(φ2,S1))


def codomaine_egal_image_cible(phi1="phi1", phi2="phi2", S1="S1", T1="T1"):
    """ÉNONCÉ-cible (test miroir) : egal(T1, image(φ2, S1))."""
    vphi2, vS1, vT1 = _t(phi2), _t(S1), _t(T1)
    return egal(vT1, E.image(vphi2, vS1))


__all__ = [
    "iso_restriction_image", "iso_restriction_image_cible",
    "iso_restriction_vers_T1", "iso_restriction_vers_T1_cible",
    "iso_T1_vers_image", "iso_T1_vers_image_cible",
    "segment_inclus_par_iso",
    "codomaine_egal_image", "codomaine_egal_image_cible",
]
