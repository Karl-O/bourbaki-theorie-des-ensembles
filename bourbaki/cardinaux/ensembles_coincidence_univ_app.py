"""§III.2 — Lemme 1 : RÉDUCTION de la coïncidence universelle à une PRÉMISSE PROPRE.

────────────────────────────────────────────────────────────────────────────────
RÔLE.  `coincidence_univ_close_isos(φ1,φ2,S1,T1)` (ensembles_coincidence_geometrie)
prouve  (∀u)(u∈S1 ⇒ φ1(u)=φ2(u))  mais sous 15 hypothèses BRUTES (graphes ⊂ produits
de termes RÉCIPROQUE/RESTRICTION, fonctionnalités de composées/réciproques/restrictions,
isos déjà renommés en x,x2, domaines de restrictions, etc.).  Ce module REGROUPE ces
15 hyps brutes en une PRÉMISSE PROPRE, fidèle aux DONNÉES de la fusion (Lemme 1 §III.2) :

  • est_isomorphisme_ordre(φ1, S1, T1, R, R')[x,y],  est_fonctionnel(φ1),  dom φ1 = S1
  • est_isomorphisme_ordre(φ2, S2, T2, R, R')[a,b],  est_fonctionnel(φ2),  dom φ2 = S2
  • inclus(S1, S2)
  • est_segment(T1, R', F),   est_segment(image(φ2,S1), R', F)
  • est_bien_ordonne(R',F)            ← BON ORDRE AMBIANT F-side (seul)
  • est_bien_ordonne(R, S2)           ← BON ORDRE AMBIANT R-side (S2 ⊇ S1 ; inclus(S1,S2) ci-dessus)
  • [STRUCTURELLES de graphe — honnêtes, voir NOTE] :
      inclus(φ1, produit(S1,T1)),   inclus(restriction(φ2,S1), produit(S1,T1))

Conclusion :  (∀u)( u∈S1 ⇒ φ1(u) = φ2(u) )   (liant-valeur « j », comme
coincidence_univ_close_isos).

────────────────────────────────────────────────────────────────────────────────
MÉTHODE.  base := coincidence_univ_close_isos(φ1,φ2,S1,T1) (15 hyps brutes).  On
DÉCHARGE chaque hyp brute DÉRIVÉE depuis la prémisse propre, par modus_ponens :
  • func(φ2|S1), dom(φ2|S1)=S1   ← restriction_fonctionnelle_piece / _domaine_piece ;
  • func(c)  (c=(φ2|S1)⁻¹∘φ1),
    func(k)  (k=φ1⁻¹∘(φ2|S1))    ← composee_fonctionnelle, factorisée par
                                    func(φ1)/func(φ2|S1)/func(φ1⁻¹)/func((φ2|S1)⁻¹)
                                    (reciproque_fonctionnelle, inj depuis les isos) ;
  • iso(φ1,S1,T1)[x,x2], [x,w]   ← prémisse iso(φ1)[x,y] (α-rename des liants d'ordre) ;
  • iso(φ2|S1,S1,T1)[x,x2]       ← iso_restriction_vers_T1 (inj/compat de φ2 déchargés
                                    depuis prémisse iso(φ2,S2,T2)[a,b]) ;
  • inclus(S1, dom φ2)           ← inclus(S1,S2) + dom φ2=S2 (Leibniz S2→dom φ2) ;
  • recip(φ1) ⊂ T1×S1,
    recip(φ2|S1) ⊂ T1×S1         ← graphe forward ⊂ S1×T1 (prémisse) via
                                    `reciproque_inclusion_monotone` + reciproque_produit.
Les hyps restantes sont EXACTEMENT la prémisse propre ci-dessus (15 formules).

────────────────────────────────────────────────────────────────────────────────
NOTE D'HONNÊTETÉ (hyps structurelles).  `est_isomorphisme_ordre` / `est_bijective`
NE CONTIENNENT PAS la clause de graphe φ ⊂ S×T (vérifié : la définition n'a que
injective + image=T + compatible_ordre).  L'inclusion de graphe φ1 ⊂ S1×T1 (« φ1 est
un graphe S1→T1 ») est donc GENUINEMENT INDÉPENDANTE des données d'iso/func/dom, et
non dérivable d'elles.  On la PORTE en hypothèse explicite — convention déjà adoptée
par coincidence_close (qui porte φ ⊂ S×T comme hyp structurelle).  De même pour la
restriction φ2|S1 ⊂ S1×T1 (le codomaine effectif de la restriction est T1=image(φ2,S1)
par codomaine_egal_image — porter S1×T1 directement évite de reconstruire ce raccord
ici).  Les DEUX inclusions RÉCIPROQUES (recip φ1, recip φ2|S1) sont, elles, DÉRIVÉES
de ces deux forward-inclusions (pas portées).

────────────────────────────────────────────────────────────────────────────────
RE-BASE BON ORDRE AMBIANT (branche coincidence-ambient-bo).  La prémisse ne consomme
QUE des bons ordres AMBIANTS : bo(R,S2) (côté E, via coincidence_univ_close_isos avec
E:=S2 et inclus(S1,S2) ; le cœur auto_iso_est_identite_sous_domaine route par
bo(R,S2)+inclus(S1,S2)) et bo(R',F) (côté F, via lemme_4_sous_domaine ; inclus(T1,F),
inclus(image(φ2,S1),F) dérivées de est_segment).  Les TROIS bons ordres SUR DES SEGMENTS
— bo(R,S1), bo(R',T1), bo(R',image(φ2,S1)) — ont DISPARU.  C'est crucial pour la fusion :
ces formules LITTÉRALES sont FAUSSES sur un segment PROPRE (R{x,x}⇔x∈S échoue pour
x hors S) et NE pouvaient se discharger dans le contexte de fusion.  Prémisse : 13 conjoints.

INVARIANT : theorie_ensembles() = 22.  Rien postulé.  NON vacueux (conclusion ≠ hyp).
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (
    Terme, var, egal, et, impl, appartient, inclus, pourtout, existe, subst_f,
)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.ordre.iii_1_relations_ordre.ordre_treillis import ensembles_ordre_vocab as V
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    instancie, equivalence_avant, equivalence_arriere,
)
from bourbaki.logique.i_3_quantifies.tactiques_abrege_quantif import existe_elimination
from bourbaki.logique.i_4_egalitaires.tactiques_abrege_egalite import symetrie


def _t(x):
    """var(x) sur un NOM ; coercition sûre si x est déjà un Terme (bug var(Terme))."""
    return x if isinstance(x, Terme) else var(x)


def _R_de(R):
    """Relation-graphe R{a,b} := (a,b) ∈ R."""
    vR = _t(R)
    return lambda a, b: appartient(E.couple(_t(a), _t(b)), vR)


# ════════════════════════════════════════════════════════════════════════════
#  Briques structurelles RÉUTILISABLES : monotonie de la réciproque + inclusion
#  de graphe réciproque dans le produit miroir.
# ════════════════════════════════════════════════════════════════════════════
def reciproque_inclusion_monotone(g="G", h="H"):
    """⊢ (G ⊂ H) ⇒ (reciproque(G) ⊂ reciproque(H)).   (monotonie de la réciproque.)

    z∈G⁻¹ ⇔ (∃p,q)(z=(p,q) et (q,p)∈G)  [AXIOME_RECIP] ; de (q,p)∈G et G⊂H on tire
    (q,p)∈H, donc z∈H⁻¹.  INCONDITIONNEL.  CLOSE (forme implicative)."""
    from bourbaki.ensembles.fonctions.ii_3_2_reciproque.ensembles_reciproque import _inst_recip_z
    vG, vH = _t(g), _t(h)
    vz, vp, vq = var("z"), var("p"), var("q")
    Hsub = N.assume(inclus(vG, vH))                                # G ⊂ H
    instG, instH = _inst_recip_z(vG, vz), _inst_recip_z(vH, vz)
    bodyG = et(egal(vz, E.couple(vp, vq)), appartient(E.couple(vq, vp), vG))
    bodyH = et(egal(vz, E.couple(vp, vq)), appartient(E.couple(vq, vp), vH))
    hb = N.assume(bodyG)
    body_to_H = conjonction_intro(
        conjonction_elim_gauche(hb),
        N.modus_ponens(conjonction_elim_droite(hb), instancie(Hsub, E.couple(vq, vp))))
    gbody = subst_f(vp, "p", bodyH)
    ex_H = N.modus_ponens(N.modus_ponens(body_to_H, N.s5(gbody, vq, "q")),
                          N.s5(existe("q", bodyH), vp, "p"))         # (∃p)(∃q)bodyH
    z_in_Hrec = N.modus_ponens(ex_H, equivalence_arriere(instH))    # z∈H⁻¹
    avant = existe_elimination(existe_elimination(
        N.loi_deduction(bodyG, z_in_Hrec), "q"), "p")               # (∃p)(∃q)bodyG ⇒ z∈H⁻¹
    z_in_Grec = N.assume(appartient(vz, E.reciproque(vG)))
    z_to = N.modus_ponens(N.modus_ponens(z_in_Grec, equivalence_avant(instG)), avant)
    incl_imp = N.generalisation("z", N.loi_deduction(appartient(vz, E.reciproque(vG)), z_to))
    return N.loi_deduction(inclus(vG, vH), incl_imp)


def reciproque_inclus_produit_miroir(g, A, B):
    """⊢ { G ⊂ A×B }  ⊢  reciproque(G) ⊂ B×A.

    G⊂A×B ⇒ G⁻¹⊂(A×B)⁻¹ (reciproque_inclusion_monotone) ; (A×B)⁻¹=B×A
    (reciproque_produit, E.II.41) ; Leibniz S6 réécrit le codomaine.  CONDITIONNEL
    à la seule inclusion forward G⊂A×B."""
    from bourbaki.ensembles.fonctions.ii_3_2_reciproque.ensembles_reciproque import reciproque_produit
    vG, vA, vB = _t(g), _t(A), _t(B)
    Hsub = N.assume(inclus(vG, E.produit(vA, vB)))                  # G ⊂ A×B
    mono = reciproque_inclusion_monotone(vG, E.produit(vA, vB))     # (G⊂A×B)⇒(G⁻¹⊂(A×B)⁻¹)
    rec_incl = N.modus_ponens(Hsub, mono)                          # G⁻¹ ⊂ (A×B)⁻¹
    rp = reciproque_produit(vA, vB)                                # (A×B)⁻¹ = B×A
    eqv = N.modus_ponens(rp, N.s6(E.reciproque(E.produit(vA, vB)), E.produit(vB, vA),
                                  "hrp", inclus(E.reciproque(vG), var("hrp"))))
    return N.modus_ponens(rec_incl, equivalence_avant(eqv))         # G⁻¹ ⊂ B×A


# ════════════════════════════════════════════════════════════════════════════
#  THÉORÈME — COÏNCIDENCE UNIVERSELLE par PRÉMISSE PROPRE (per-witness).
# ════════════════════════════════════════════════════════════════════════════
def coincidence_univ_app_point(phi1="phi1", phi2="phi2", S1="S1", T1="T1",
                               S2="S2", T2="T2", F="F", R="R", Rp="Rp", Eamb="E"):
    """⊢ {  PRÉMISSE PROPRE (voir docstring module)  }
          ⊢ (∀u)( u∈S1 ⇒ φ1(u) = φ2(u) ).

    🎯 Réduction de coincidence_univ_close_isos à une PRÉMISSE PROPRE : les 15
    hypothèses BRUTES (graphes réciproque/restriction ⊂ produits, func des composées
    c,k, isos déjà renommés, domaines de restriction) sont DÉRIVÉES de la prémisse
    propre (isos/func/dom de φ1,φ2 + segments + bons ordres + inclus(S1,S2) + DEUX
    inclusions de graphe honnêtes).  Méthode = modus_ponens brique par brique.
    theorie=22 ; non vacueux."""
    from bourbaki.cardinaux.ensembles_coincidence_geometrie import (
        coincidence_univ_close_isos,
    )
    from bourbaki.cardinaux.ensembles_codomaine_reconciliation import (
        iso_restriction_vers_T1, _rename_iso_order_binders,
    )
    from bourbaki.cardinaux.ensembles_restriction_iso_pieces import (
        restriction_fonctionnelle_piece, restriction_domaine_piece,
    )
    from bourbaki.cardinaux.ensembles_bijection import reciproque_fonctionnelle
    from bourbaki.ensembles.fonctions.ii_3_7_composee_fonctions.ensembles_fonctions_composee import (
        composee_fonctionnelle,
    )

    Rf, Rpf = _R_de(R), _R_de(Rp)
    vphi1, vphi2 = _t(phi1), _t(phi2)
    vS1, vT1, vS2, vT2 = _t(S1), _t(T1), _t(S2), _t(T2)
    phi2S1 = E.restriction(vphi2, vS1)                            # φ2|S1
    recip_phi1 = E.reciproque(vphi1)                              # φ1⁻¹
    recip_phi2S1 = E.reciproque(phi2S1)                           # (φ2|S1)⁻¹
    c_term = E.composee(recip_phi2S1, vphi1)                      # c = (φ2|S1)⁻¹∘φ1
    k_term = E.composee(recip_phi1, phi2S1)                       # k = φ1⁻¹∘(φ2|S1)

    def cut(thm, formule, preuve):
        """Décharge une hyp `formule` de `thm` par la preuve `preuve` (assert présence)."""
        assert formule in thm.hypotheses, "cut: formule absente des hyps"
        return N.modus_ponens(preuve, N.loi_deduction(formule, thm))

    def discharge(base, proof):
        """Décharge proof.conclusion de base.hypotheses (assert présence)."""
        assert proof.conclusion in base.hypotheses, "discharge: conclusion absente des hyps"
        return N.modus_ponens(proof, N.loi_deduction(proof.conclusion, base))

    # ── prémisse : isos en formules (binders canoniques) + extractions ─────────
    iso_phi1_xy = V.est_isomorphisme_ordre(vphi1, vS1, vT1, Rf, Rpf, "x", "y")
    inj_phi1 = conjonction_elim_gauche(conjonction_elim_gauche(N.assume(iso_phi1_xy)))
    iso_phi2_ab = V.est_isomorphisme_ordre(vphi2, vS2, vT2, Rf, Rpf, "a", "b")
    H_iso_phi2 = N.assume(iso_phi2_ab)
    bij_phi2 = conjonction_elim_gauche(H_iso_phi2)
    compat_phi2_ab = conjonction_elim_droite(H_iso_phi2)          # compatible_ordre(φ2,S2)[a,b]
    inj_phi2_uup = conjonction_elim_gauche(bij_phi2)              # inj(φ2,S2)[u,up]
    inj_phi2_cd = N.generalisation("c", N.generalisation("d",     # → inj(φ2,S2)[c,d]
        instancie(instancie(inj_phi2_uup, var("c")), var("d"))))

    # ── pièces de restriction (réduites aux hyps de prémisse) ──────────────────
    p_func_phi2S1 = restriction_fonctionnelle_piece(phi2, S1)     # {func φ2} ⊢ func(φ2|S1)
    p_dom_phi2S1 = restriction_domaine_piece(phi2, S1)            # {S1⊂dom φ2} ⊢ dom(φ2|S1)=S1

    # inj(φ2|S1,S1) extrait de iso(φ2|S1,S1,T1)[x,x2] (présent dans base) ───────
    iso_phi2S1_xx2 = V.est_isomorphisme_ordre(phi2S1, vS1, vT1, Rf, Rpf, "x", "x2")
    inj_phi2S1 = conjonction_elim_gauche(conjonction_elim_gauche(N.assume(iso_phi2S1_xx2)))

    # ── func(φ1⁻¹), func((φ2|S1)⁻¹) ────────────────────────────────────────────
    rf_phi1 = cut(reciproque_fonctionnelle(phi1, S1),
                  E.injective_dans(vphi1, vS1), inj_phi1)          # func(φ1⁻¹)
    rf_phi2S1 = reciproque_fonctionnelle(phi2S1, vS1)
    rf_phi2S1 = cut(rf_phi2S1, E.injective_dans(phi2S1, vS1), inj_phi2S1)
    rf_phi2S1 = cut(rf_phi2S1, E.est_fonctionnel(phi2S1), p_func_phi2S1)
    rf_phi2S1 = cut(rf_phi2S1, egal(E.dom(phi2S1), vS1), p_dom_phi2S1)   # func((φ2|S1)⁻¹)

    # ── func(c) = func((φ2|S1)⁻¹ ∘ φ1), func(k) = func(φ1⁻¹ ∘ (φ2|S1)) ─────────
    func_c = N.modus_ponens(
        conjonction_intro(N.assume(E.est_fonctionnel(vphi1)), rf_phi2S1),
        composee_fonctionnelle(recip_phi2S1, vphi1))
    func_k = N.modus_ponens(
        conjonction_intro(p_func_phi2S1, rf_phi1),
        composee_fonctionnelle(recip_phi1, phi2S1))

    # ── iso(φ1)[x,x2] et iso(φ1)[x,w] depuis prémisse iso(φ1)[x,y] ─────────────
    p_iso_phi1_xx2 = _rename_iso_order_binders(N.assume(iso_phi1_xy), "x", "x2")
    p_iso_phi1_xw = _rename_iso_order_binders(N.assume(iso_phi1_xy), "x", "w")

    # ── iso(φ2|S1,S1,T1)[x,x2] depuis iso_restriction_vers_T1 (inj/compat de φ2
    #    déchargés depuis prémisse iso(φ2,S2,T2)[a,b]) ─────────────────────────
    ivt1 = iso_restriction_vers_T1(phi2, S1, T1, S2, F, R, Rp, x="a", y="b", phi1=phi1)
    ivt1 = cut(ivt1, E.injective_dans(vphi2, vS2, "c", "d"), inj_phi2_cd)
    ivt1 = cut(ivt1, V.compatible_ordre(vphi2, vS2, Rf, Rpf, "a", "b"), compat_phi2_ab)
    p_iso_phi2S1 = _rename_iso_order_binders(ivt1, "x", "x2")

    # ── inclus(S1, dom φ2) ← inclus(S1,S2) + dom φ2=S2 (Leibniz S2→dom φ2) ──────
    H_inc12 = N.assume(inclus(vS1, vS2))
    H_dom2 = N.assume(egal(E.dom(vphi2), vS2))
    S2_eq_dom = N.modus_ponens(H_dom2, symetrie(E.dom(vphi2), vS2))
    eqv_dom = N.modus_ponens(S2_eq_dom,
                             N.s6(vS2, E.dom(vphi2), "hd2", inclus(vS1, var("hd2"))))
    p_inc_dom = N.modus_ponens(H_inc12, equivalence_avant(eqv_dom))  # inclus(S1,dom φ2)

    # ── inclusions réciproques de graphe (DÉRIVÉES des forward portées) ────────
    p_recip_phi1 = reciproque_inclus_produit_miroir(vphi1, vS1, vT1)     # φ1⁻¹⊂T1×S1 {φ1⊂S1×T1}
    p_recip_phi2S1 = reciproque_inclus_produit_miroir(phi2S1, vS1, vT1)  # (φ2|S1)⁻¹⊂T1×S1

    # ── ASSEMBLAGE : décharge des 11 hyps DÉRIVÉES ─────────────────────────────
    base = coincidence_univ_close_isos(phi1, phi2, S1, T1, E_set=Eamb)  # bo AMBIANT VRAI E (pas S2)
    base = discharge(base, p_func_phi2S1)        # func(φ2|S1)
    base = discharge(base, p_dom_phi2S1)         # dom(φ2|S1)=S1
    base = discharge(base, func_c)               # func(c)
    base = discharge(base, func_k)               # func(k)
    base = discharge(base, p_iso_phi1_xx2)       # iso(φ1)[x,x2]
    base = discharge(base, p_iso_phi2S1)         # iso(φ2|S1)[x,x2]
    base = discharge(base, p_inc_dom)            # inclus(S1,dom φ2)
    base = discharge(base, p_recip_phi1)         # φ1⁻¹⊂T1×S1
    base = discharge(base, p_recip_phi2S1)       # (φ2|S1)⁻¹⊂T1×S1
    base = discharge(base, p_iso_phi1_xw)        # iso(φ1)[x,w] (variante binder)
    return base


def coincidence_univ_app_point_cible(phi1="phi1", phi2="phi2", S1="S1", T1="T1"):
    """ÉNONCÉ-cible (test miroir) : (∀u)(u∈S1 ⇒ φ1(u)=φ2(u))  (liant « j »)."""
    vphi1, vphi2, vS1 = _t(phi1), _t(phi2), _t(S1)
    return pourtout("u", impl(appartient(var("u"), vS1),
                              egal(E.valeur(vphi1, var("u"), b="j"),
                                   E.valeur(vphi2, var("u"), b="j"))))


def coincidence_univ_app_point_premisse(phi1="phi1", phi2="phi2", S1="S1", T1="T1",
                                        S2="S2", T2="T2", F="F", R="R", Rp="Rp", Eamb="E"):
    """La PRÉMISSE PROPRE attendue (14 formules), pour vérifier que le séquent ne
    porte QUE ces hypothèses-là (test de propreté).  Délègue à `_premisse_liste`.

    🔑 BON ORDRE AMBIANT VRAI : bo(R,E) [R-side, E = ambiant ⊇ S1] et bo(R',F) [F-side]
    SEULS ; les bons ordres sur des SEGMENTS PROPRES (bo(R,S1), bo(R,S2), bo(R',T1),
    bo(R',image)) ont disparu (faux sur segment propre).  inclus(S1,E) fournie par
    est_segment(S1,R,E) dans la fusion."""
    return set(_premisse_liste(phi1, phi2, S1, T1, S2, T2, F, R, Rp, Eamb))


def _premisse_liste(phi1, phi2, S1, T1, S2, T2, F, R, Rp, Eamb="E"):
    """La prémisse propre, en LISTE ORDONNÉE (source de vérité pour la conjonction).

    🔑 BON ORDRE AMBIANT VRAI (re-base R-side, branche rside-ambient-E).  Les bons ordres
    consommés sont les bons ordres AMBIANTS des ENSEMBLES SOUS-JACENTS : bo(R,E) (R-side,
    E = le bon ordre ambiant ⊇ S1, via coincidence_univ_close_isos E_set:=E ; inclus(S1,E)
    fournie par est_segment(S1,R,E) dans la fusion) et bo(R',F) (F-side, via
    lemme_4_sous_domaine).  Les bons ordres SUR DES SEGMENTS PROPRES — bo(R,S1), bo(R,S2),
    bo(R',T1), bo(R',image(φ2,S1)) — ont TOUS DISPARU : FAUX sur un segment propre
    (réflexivité R{x,x}⇔x∈S échoue hors S), donc INDÉCHARGEABLES dans la fusion.  Seuls
    subsistent les bons ordres des ENSEMBLES AMBIANTS E, F — tous deux fournis par la fusion."""
    Rf, Rpf = _R_de(R), _R_de(Rp)
    v1, v2 = _t(phi1), _t(phi2)
    s1, t1, s2, t2, eamb = _t(S1), _t(T1), _t(S2), _t(T2), _t(Eamb)
    phi2S1, img = E.restriction(v2, s1), E.image(v2, s1)
    return [
        V.est_isomorphisme_ordre(v1, s1, t1, Rf, Rpf, "x", "y"),
        V.est_isomorphisme_ordre(v2, s2, t2, Rf, Rpf, "a", "b"),
        E.est_fonctionnel(v1), E.est_fonctionnel(v2),
        egal(E.dom(v1), s1), egal(E.dom(v2), s2), inclus(s1, s2),
        E.est_segment(t1, Rpf, _t(F)), E.est_segment(img, Rpf, _t(F)),
        E.est_bien_ordonne(Rpf, _t(F)),       # BON ORDRE AMBIANT F-side
        E.est_bien_ordonne(Rf, eamb),         # BON ORDRE AMBIANT R-side VRAI (E ⊇ S1)
        inclus(s1, eamb),                     # inclus(S1,E) — fournie par est_segment(S1,R,E)
        inclus(v1, E.produit(s1, t1)), inclus(phi2S1, E.produit(s1, t1)),
    ]


def _conjoindre(formules):
    """Conjonction left-nested et(et(...et(p0,p1),p2)...,pn)."""
    acc = formules[0]
    for f in formules[1:]:
        acc = et(acc, f)
    return acc


def _elim_conjoint(HH, i, n):
    """De HH ⊢ conjonction left-nested de n formules, extrait la i-ème (0-indexée)."""
    t = HH
    for _ in range(n - 1 - i):
        t = conjonction_elim_gauche(t)
    if i > 0:
        t = conjonction_elim_droite(t)
    return t


def coincidence_univ_app(phi1="phi1", phi2="phi2", S1="S1", T1="T1",
                         S2="S2", T2="T2", F="F", R="R", Rp="Rp", Eamb="E"):
    """⊢ (∀S1)(∀T1)(∀φ1)(∀S2)(∀T2)(∀φ2)( PRÉMISSE_APPLICATIONS ⇒ (∀w)(w∈S1 ⇒ φ1(w)=φ2(w)) ).

    🎯🎯🎯 COÏNCIDENCE UNIVERSELLE (Lemme 1 §III.2), forme APPLICATIONS — **THÉORÈME CLOS**.
    Généralise `coincidence_univ_app_point` sur les 6 témoins (S1,T1,φ1,S2,T2,φ2) après
    avoir replié sa prémisse propre (13 formules) en une seule conjonction antécédente.
    La PRÉMISSE renforce `coincidence_univ` (postulée) en témoignant φ1,φ2 comme
    APPLICATIONS (iso + func + dom) + bons ordres AMBIANTS + inclusions de graphe — toutes
    des données HONNÊTES fournies par le contexte de fusion.  `.est_clos == True`
    (0 hypothèse) : le contenu géométrique de Lemme 1 est ENTIÈREMENT PROUVÉ (schéma sur
    F, R, R').

    🔑 BON ORDRE AMBIANT : les bons ordres consommés sont bo(R,S2) [R-side, S2 = grand
    segment ⊇ S1] et bo(R',F) [F-side] — JAMAIS bo sur un segment PROPRE (bo(R,S1),
    bo(R',T1), bo(R',image(φ2,S1)) ont DISPARU : faux sur segment propre, donc indéchargeable
    dans la fusion).  C'est le re-base de la branche coincidence-ambient-bo.

    RESTE pour brancher fusion : renforcer `axiome_h`/témoin₁ pour témoigner func/dom
    (l'architecture « φ application »), afin que fusion fournisse cette prémisse."""
    thm = coincidence_univ_app_point(phi1, phi2, S1, T1, S2, T2, F, R, Rp, Eamb)
    prem = _premisse_liste(phi1, phi2, S1, T1, S2, T2, F, R, Rp, Eamb)
    assert set(thm.hypotheses) == set(prem), "prémisse ≠ hypothèses du séquent point"
    H = _conjoindre(prem)
    HH = N.assume(H)
    for i, pi in enumerate(prem):                       # décharge chaque conjoint → hyp unique H
        thm = N.modus_ponens(_elim_conjoint(HH, i, len(prem)), N.loi_deduction(pi, thm))
    imp = N.loi_deduction(H, thm)                       # ⊢ H ⇒ C  (CLOS)
    for w in [phi2, T2, S2, phi1, T1, S1]:              # ∀ sur les 6 témoins (F,R,R' restent libres)
        imp = N.generalisation(w, imp)
    return imp


def coincidence_univ_app_cible(phi1="phi1", phi2="phi2", S1="S1", T1="T1",
                               S2="S2", T2="T2", F="F", R="R", Rp="Rp", Eamb="E"):
    """ÉNONCÉ-cible (test miroir) : (∀6 témoins)(prémisse ⇒ coïncidence sur S1)."""
    prem = _premisse_liste(phi1, phi2, S1, T1, S2, T2, F, R, Rp, Eamb)
    concl = coincidence_univ_app_point_cible(phi1, phi2, S1, T1)
    imp = impl(_conjoindre(prem), concl)
    for w in [phi2, T2, S2, phi1, T1, S1]:
        imp = pourtout(w, imp)
    return imp


__all__ = [
    "coincidence_univ_app_point", "coincidence_univ_app_point_cible",
    "coincidence_univ_app_point_premisse",
    "coincidence_univ_app", "coincidence_univ_app_cible",
    "reciproque_inclusion_monotone", "reciproque_inclus_produit_miroir",
]
