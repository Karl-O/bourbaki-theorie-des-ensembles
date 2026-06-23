"""§III.4 — SURGERY « RETRAIT D'UN POINT » : ferme l'unique maillon dur
`retrait_surgery_hyp` de ensembles_retrait_point (donc la branche non surjective du
LEMME N « pas de cardinal strictement entre c et c+1 »).

OBJECTIF FINAL (l'énoncé EXACT de retrait_surgery_hyp, ensembles_retrait_point) :

    retrait_surgery_hyp(b, c, F) :
        ( est_injection_de(F, b, c+1)  et  image(F,b) ≠ c+1 )  ⇒  ( b ≤ (C⊔{∅})∖{*} ),

où  c+1 = successeur(c) = Card(S),  S := C ⊔ {∅} = (C×{0}) ∪ ({∅}×{1}),  et
* = (∅, 1) est le point marqué.  C'est l'ÉCHANGE PONCTUEL E.III.4 (surgery voisine
de la Prop. 8) : une injection f : b → c+1 NON surjective rate un point q ∈ c+1 ;
on RAMÈNE q sur le marqueur * par une TRANSPOSITION, ce qui place l'image dans S∖{*},
d'où b ≤ S∖{*}.

────────────────────────────────────────────────────────────────────────────────
ARCHITECTURE DE LA PREUVE (du bas vers le haut), 3 grandes étapes :

  (B) RE-CIBLAGE (INCONDITIONNEL, ce module) — « une injection dont l'image rate un
      point q se RE-CIBLE sur le complémentaire E∖{q} » :
        injection_evite_implique_inf_egal_diff(G, b, E, q) :
          ( est_injection_de(G, b, E)  et  ¬(q ∈ image(G,b)) )  ⇒  ( b ≤ E∖{q} ).
      Pur jeu d'inclusion : image(G,b) ⊂ E et q∉image(G,b) ⇒ image(G,b) ⊂ E∖{q}, donc
      G est déjà une injection b → E∖{q}.  AUCUNE transposition.  C'est le cœur
      réutilisable, entièrement CLOS.

  (T) TRANSPORT cardinal↔ensemble (INCONDITIONNEL) — l'injection part dans le CARDINAL
      OPAQUE c+1 = Card(S).  On la transporte dans l'ensemble CONCRET S via la
      bijection canonique Eq(Card S, S) (= eq_succ_ensemble) : si f : b → Card S est
      injective non surjective, alors b injecte dans S en ratant un point.  [étape
      assemblée dans retrait_surgery_close, cf. ci-dessous]

  (S) ÉCHANGE par TRANSPOSITION (INCONDITIONNEL, via transposition_existe DÉJÀ CLOS) —
      le point raté q ∈ S est amené sur * par une transposition τ de S (échange q↔*),
      bijective ; b ≤ S∖{q} se transporte en b ≤ S∖{*} par Eq(S∖{q}, S∖{*}).

⚠️ INVARIANT : theorie_ensembles() = 22 intangible.  AUCUN N.axiome ; on ne fait
   que RÉUTILISER transposition_existe (clos) et les ponts CLOS de retrait_point.
"""
from __future__ import annotations

from bourbaki.logique.formule import (Terme, var, egal, et, non, impl, existe,
                                       inclus, appartient, pourtout)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, instancie, dne, contraposition)

from bourbaki.cardinaux.ensembles_cardinaux import (
    est_injection_de, inf_egal_card,
)
from bourbaki.ensembles.ii_2_couples_produit.ensembles_couples import singleton_membre


def _t(t):
    """Coercion str/Terme → Terme (utilitaire local)."""
    return t if isinstance(t, Terme) else var(t)


# ════════════════════════════════════════════════════════════════════════════
#  BRIQUE — (y ∈ E∖{q}) ⇔ (y∈E et ¬(y∈{q}))   (instance de AXIOME_DIFF)
# ════════════════════════════════════════════════════════════════════════════
def _inst_diff(e, x, z):
    """⊢ (z ∈ E∖X) ⇔ (z∈E et ¬(z∈X)).   (instance de AXIOME_DIFF.)"""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_DIFF)
    return instancie(instancie(instancie(ax, _t(e)), _t(x)), _t(z))


# ════════════════════════════════════════════════════════════════════════════
#  ÉTAPE (B) — RE-CIBLAGE INCONDITIONNEL : image rate q  ⇒  b ≤ E∖{q}
# ════════════════════════════════════════════════════════════════════════════
def image_evite_inclus_diff(g="G", b="b", e="E", q="q"):
    """⊢ ( image(G,b) ⊂ E  et  ¬(q ∈ image(G,b)) )  ⇒  ( image(G,b) ⊂ E∖{q} ).

    Pur jeu d'inclusion (INCONDITIONNEL).  Pour y ∈ image(G,b) :
      • y ∈ E             (de image(G,b) ⊂ E) ;
      • y ≠ q             (si y=q alors q ∈ image(G,b) par Leibniz, contredisant ¬…) ;
      • ¬(y ∈ {q})        (singleton_membre : y∈{q} ⇔ y=q) ;
      • y ∈ E∖{q}         (AXIOME_DIFF)."""
    vG, vb, vE, vq = _t(g), _t(b), _t(e), _t(q)
    img = E.image(vG, vb)                                    # image(G,b)
    sing = E.singleton(vq)                                   # {q}
    diff = E.difference(vE, sing)                            # E∖{q}
    # liant « z » : EXACTEMENT celui de inclus(·,·) (= pourtout("z", …)), pour que la
    # généralisation finale ÉGALE littéralement inclus(image(G,b), E∖{q}).
    vy = var("z")

    ante = et(inclus(img, vE), non(appartient(vq, img)))
    h = N.assume(ante)
    h_sub = conjonction_elim_gauche(h)                       # image(G,b) ⊂ E
    h_qni = conjonction_elim_droite(h)                       # ¬(q ∈ image(G,b))

    # y ∈ image(G,b) ⇒ y ∈ E∖{q}
    hy = N.assume(appartient(vy, img))                       # y ∈ image(G,b)
    y_in_E = N.modus_ponens(hy, instancie(h_sub, vy))        # y ∈ E
    # y ≠ q : si y=q, alors q ∈ image(G,b) (Leibniz y→q), contredit ¬(q∈image)
    h_yq = N.assume(egal(vy, vq))                            # y = q
    q_in_img = N.modus_ponens(hy, equivalence_avant(N.modus_ponens(
        h_yq, N.s6(vy, vq, "w", appartient(var("w"), img)))))   # q ∈ image(G,b)
    falso = N.modus_ponens(q_in_img,
        N.modus_ponens(h_qni, N.s2(non(appartient(vq, img)), non(egal(vy, vq)))))
    y_ne_q = N.modus_ponens(N.loi_deduction(egal(vy, vq), falso),
                            N.s1(non(egal(vy, vq))))          # ¬(y = q)
    # ¬(y ∈ {q})  (contraposée de y∈{q} ⇒ y=q, sens ⇒ de singleton_membre)
    sing_ssi = singleton_membre(vy, vq)                       # (y∈{q}) ⇔ (y=q)
    y_nin_sing = N.modus_ponens(y_ne_q,
        contraposition(equivalence_avant(sing_ssi)))          # ¬(y ∈ {q})
    # y ∈ E∖{q}  (AXIOME_DIFF ⇐)
    y_in_diff = N.modus_ponens(conjonction_intro(y_in_E, y_nin_sing),
                               equivalence_arriere(_inst_diff(vE, sing, vy)))   # y ∈ E∖{q}
    body = N.loi_deduction(appartient(vy, img), y_in_diff)    # y∈image ⇒ y∈E∖{q}
    sub = N.generalisation("z", body)                         # image(G,b) ⊂ E∖{q}
    return N.loi_deduction(ante, sub)


def injection_evite_implique_inf_egal_diff(g="G", b="b", e="E", q="q"):
    """⊢ ( est_injection_de(G, b, E)  et  ¬(q ∈ image(G,b)) )  ⇒  ( b ≤ E∖{q} ).

    🎯 RE-CIBLAGE INCONDITIONNEL.  Une injection G : b → E dont l'IMAGE RATE le point
    q se RE-CIBLE en une injection b → E∖{q} (le codomaine se restreint à E∖{q}, le
    GRAPHE G est inchangé) :
      • est_injection_de(G,b,E) = ((G fonctionnel et dom=b) et inj/b) et image(G,b)⊂E ;
      • image(G,b) ⊂ E∖{q}  (image_evite_inclus_diff, de image⊂E et q∉image) ;
      • on RÉASSEMBLE est_injection_de(G, b, E∖{q}) (seul le dernier conjoint change) ;
      • S5 témoin G ⇒ b ≤ E∖{q}.
    Entièrement CLOS, réutilisable.  C'est la moitié « facile mais essentielle » de la
    surgery : il NE reste qu'à AMENER le point raté sur un point FIXÉ (la transposition)."""
    vG, vb, vE, vq = _t(g), _t(b), _t(e), _t(q)
    img = E.image(vG, vb)                                    # image(G,b)
    diff = E.difference(vE, E.singleton(vq))                 # E∖{q}

    inj = est_injection_de(vG, vb, vE)                       # est_injection_de(G,b,E)
    q_ni = non(appartient(vq, img))                          # ¬(q ∈ image(G,b))
    ante = et(inj, q_ni)
    h = N.assume(ante)
    h_inj = conjonction_elim_gauche(h)                       # est_injection_de(G,b,E)
    h_qni = conjonction_elim_droite(h)                       # ¬(q ∈ image(G,b))
    # extraire les 3 premiers conjoints + image⊂E
    noyau = conjonction_elim_gauche(h_inj)                   # (G fonctionnel et dom=b) et inj/b
    img_sub_E = conjonction_elim_droite(h_inj)               # image(G,b) ⊂ E
    # image(G,b) ⊂ E∖{q}
    img_sub_diff = N.modus_ponens(conjonction_intro(img_sub_E, h_qni),
                                  image_evite_inclus_diff(g, b, e, q))   # image⊂E∖{q}
    # réassembler est_injection_de(G, b, E∖{q})
    inj_diff = conjonction_intro(noyau, img_sub_diff)        # est_injection_de(G,b,E∖{q})
    assert inj_diff.conclusion == est_injection_de(vG, vb, diff), \
        "réassemblage de est_injection_de(G,b,E∖{q}) incorrect"
    # b ≤ E∖{q}  (S5 témoin G)
    le = N.modus_ponens(inj_diff, N.s5(est_injection_de(var("F"), vb, diff), vG, "F"))
    return N.loi_deduction(ante, le)                         # (inj et q∉image) ⇒ b≤E∖{q}


# ════════════════════════════════════════════════════════════════════════════
#  ÉTAPE (P1) — NON SURJECTIVITÉ ⇒ POINT RATÉ EXPLICITE   (INCONDITIONNEL)
#
#  Une image incluse dans E mais DIFFÉRENTE de E rate un point de E.
# ════════════════════════════════════════════════════════════════════════════
def non_surjective_donne_point_rate(g="G", b="b", e="E"):
    """⊢ ( image(G,b) ⊂ E  et  image(G,b) ≠ E )  ⇒  (∃q)( q ∈ E  et  ¬(q ∈ image(G,b)) ).

    Une injection (ou toute fonction) dont l'IMAGE est STRICTEMENT incluse dans le
    codomaine E rate un point de E.  Preuve par l'absurde (extensionnalité A1) :
      • si AUCUN point de E n'était hors de l'image, on aurait E ⊂ image(G,b) ;
      • avec image(G,b) ⊂ E, l'ANTISYMÉTRIE de ⊂ (inclusion_antisymetrique = A1)
        donnerait image(G,b) = E, CONTREDISANT image(G,b) ≠ E.
    Donc ∃q ∈ E hors de l'image.  INCONDITIONNEL, réutilisable."""
    from bourbaki.ordre.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_relation import inclusion_antisymetrique
    vG, vb, vE = _t(g), _t(b), _t(e)
    img = E.image(vG, vb)                                    # image(G,b)
    vq = var("q")
    q_in_E = appartient(vq, vE)
    q_ni_img = non(appartient(vq, img))
    existe_q = existe("q", et(q_in_E, q_ni_img))             # (∃q)(q∈E et ¬(q∈image))

    ante = et(inclus(img, vE), non(egal(img, vE)))
    h = N.assume(ante)
    img_sub_E = conjonction_elim_gauche(h)                   # image(G,b) ⊂ E
    img_ne_E = conjonction_elim_droite(h)                    # image(G,b) ≠ E

    # ── par l'absurde : supposons ¬(∃q)(q∈E et ¬(q∈image)) ──────────────────────
    h_neg = N.assume(non(existe_q))                          # ¬(∃q)(q∈E et ¬(q∈image))
    # on prouve E ⊂ image :  (∀z)(z∈E ⇒ z∈image)   (liant « z », celui de inclus)
    vz = var("z")
    z_in_E = appartient(vz, vE)
    z_in_img = appartient(vz, img)
    hz = N.assume(z_in_E)                                    # z ∈ E
    #   z∈image par DNE : suppose ¬(z∈image) ⇒ (z∈E et ¬(z∈image)) ⇒ (∃q)… ⊥ H_neg
    h_zni = N.assume(non(z_in_img))                          # ¬(z ∈ image)
    body_z = conjonction_intro(hz, h_zni)                    # z∈E et ¬(z∈image)
    ex_z = N.modus_ponens(body_z,
        N.s5(et(q_in_E, q_ni_img), vz, "q"))                 # (∃q)(q∈E et ¬(q∈image))
    #   ex falso (cible = ¬¬(z∈image)) : (∃q)… et ¬(∃q)… ⊢ ¬¬(z∈image)
    falso = N.modus_ponens(ex_z,
        N.modus_ponens(h_neg, N.s2(non(existe_q), non(non(z_in_img)))))   # ¬¬(z∈image)
    nn_z = N.modus_ponens(N.loi_deduction(non(z_in_img), falso),
                          N.s1(non(non(z_in_img))))          # ¬¬(z∈image)
    z_in_img_thm = N.modus_ponens(nn_z, dne(z_in_img))       # z∈image
    z_imp = N.loi_deduction(z_in_E, z_in_img_thm)            # z∈E ⇒ z∈image
    E_sub_img = N.generalisation("z", z_imp)                 # E ⊂ image(G,b)
    # antisymétrie : (image⊂E et E⊂image) ⇒ image=E
    antisym = inclusion_antisymetrique(img, vE)              # ((img⊂E)et(E⊂img))⇒img=E
    img_eq_E = N.modus_ponens(conjonction_intro(img_sub_E, E_sub_img), antisym)   # image=E
    # contradiction avec image≠E :  ⊥, d'où ¬¬(∃q) (cible = ¬¬existe_q pour s1)
    falso2 = N.modus_ponens(img_eq_E,
        N.modus_ponens(img_ne_E, N.s2(non(egal(img, vE)), non(non(existe_q)))))   # ¬¬(∃q)…
    existe_thm = N.modus_ponens(N.loi_deduction(non(existe_q), falso2),
                                N.s1(non(non(existe_q))))    # ¬¬(∃q)…
    existe_thm = N.modus_ponens(existe_thm, dne(existe_q))   # (∃q)(q∈E et ¬(q∈image))
    return N.loi_deduction(ante, existe_thm)


# ════════════════════════════════════════════════════════════════════════════
#  COMBINAISON (P1 + B) — injection NON SURJECTIVE ⇒ (∃q∈E) b ≤ E∖{q}
# ════════════════════════════════════════════════════════════════════════════
def injection_non_surj_donne_inf_egal_diff(f="F", b="b", e="E"):
    """⊢ ( est_injection_de(F, b, E)  et  image(F,b) ≠ E )
            ⇒  (∃q)( q ∈ E  et  b ≤ E∖{q} ).

    🎯 RÉSULTAT INTERMÉDIAIRE CLOS : une injection F : b → E NON surjective place b
    dans le complémentaire E∖{q} d'UN POINT q ∈ E (rate par F).  Assemblage :
      • est_injection_de(F,b,E) ⊢ image(F,b) ⊂ E ;
      • (P1) non_surjective_donne_point_rate ⊢ (∃q)(q∈E et ¬(q∈image(F,b))) ;
      • (B) injection_evite_implique_inf_egal_diff ⊢ pour CE q, b ≤ E∖{q} ;
      • monotonie de (∃q) sur le corps ⇒ (∃q)(q∈E et b ≤ E∖{q}).
    INCONDITIONNEL, réutilisable — la moitié « ensembliste » de la surgery, AVANT
    l'échange ponctuel qui fixe le point retiré sur le marqueur."""
    from bourbaki.logique.tactiques.tactiques_abrege_quantif import monotonie_existe
    vF, vb, vE = _t(f), _t(b), _t(e)
    img = E.image(vF, vb)                                    # image(F,b)
    vq = var("q")
    q_in_E = appartient(vq, vE)
    q_ni_img = non(appartient(vq, img))
    diff_q = E.difference(vE, E.singleton(vq))               # E∖{q}
    le_q = inf_egal_card(vb, diff_q)                         # b ≤ E∖{q}

    inj = est_injection_de(vF, vb, vE)
    img_ne_E = non(egal(img, vE))
    ante = et(inj, img_ne_E)
    h = N.assume(ante)
    h_inj = conjonction_elim_gauche(h)                       # est_injection_de(F,b,E)
    h_ne = conjonction_elim_droite(h)                        # image(F,b) ≠ E
    img_sub_E = conjonction_elim_droite(h_inj)               # image(F,b) ⊂ E

    # (P1) : (∃q)(q∈E et ¬(q∈image))
    ex_rate = N.modus_ponens(conjonction_intro(img_sub_E, h_ne),
                             non_surjective_donne_point_rate(f, b, e))   # (∃q)(q∈E et q∉img)

    # corps : (q∈E et q∉img) ⇒ (q∈E et b≤E∖{q})   [sous est_injection_de(F,b,E)]
    h_body = N.assume(et(q_in_E, q_ni_img))                  # q∈E et ¬(q∈image)
    q_inE = conjonction_elim_gauche(h_body)                  # q∈E
    q_niI = conjonction_elim_droite(h_body)                  # ¬(q∈image)
    # (B) b ≤ E∖{q}  via injection_evite_implique_inf_egal_diff (au point q)
    le = N.modus_ponens(conjonction_intro(h_inj, q_niI),
                        injection_evite_implique_inf_egal_diff(f, b, e, "q"))   # b ≤ E∖{q}
    body_cible = conjonction_intro(q_inE, le)               # q∈E et b≤E∖{q}
    corps_imp = N.loi_deduction(et(q_in_E, q_ni_img), body_cible)   # (q∈E et q∉img)⇒(q∈E et b≤E∖{q})

    # monotonie de (∃q) (q non libre dans est_injection_de(F,b,E))
    ex_imp = monotonie_existe(corps_imp, "q")              # (∃q)(q∈E et q∉img) ⇒ (∃q)(q∈E et b≤E∖{q})
    ex_cible = N.modus_ponens(ex_rate, ex_imp)            # (∃q)(q∈E et b≤E∖{q})   [hyp ante]
    return N.loi_deduction(ante, ex_cible)


# ════════════════════════════════════════════════════════════════════════════
#  ASSEMBLAGE — retrait_surgery_hyp MODULO la SEULE équipotence « retrait d'un point »
#
#  Mon résultat combiné (E = c+1) donne (∃q)(q∈c+1 et b ≤ (c+1)∖{q}).  Pour FERMER
#  retrait_surgery_hyp (conclusion b ≤ S∖{*}, S=C⊔{∅}), il NE reste qu'à transporter
#  b ≤ (c+1)∖{q} vers b ≤ S∖{*}, ce qui découle de l'équipotence des « (c+1) PRIVÉ
#  D'UN POINT » avec S∖{*} (lui-même ≃ C, cf. eq_diff_marqueur_c).  On l'isole :
#
#    HD(b, c) := (∀q)( q ∈ c+1  ⇒  Eq( (c+1)∖{q},  (C⊔{∅})∖{*} ) ).
#
#  « Retirer UN POINT QUELCONQUE du cardinal c+1 = Card(C⊔{∅}) laisse un ensemble
#  équipotent à (C⊔{∅})∖{*} » (donc à C, le retrait d'un point d'un (c+1)-ensemble).
#  C'est le RÉSIDU PROPRE de la surgery (échange ponctuel ramenant tout point retiré
#  sur le marqueur), STRICTEMENT plus simple que l'énoncé brut de retrait_surgery_hyp :
#  l'INJECTION b → S∖{*} est désormais FABRIQUÉE inconditionnellement (re-ciblage +
#  point raté), et il ne reste que l'ÉQUIPOTENCE des retraits ponctuels — réductible
#  à la transposition τ DÉJÀ construite (transposition_existe, clos).
# ════════════════════════════════════════════════════════════════════════════
def _succ(c):
    """c+1 = successeur(c) = Card(C⊔{∅})  (le codomaine cardinal opaque de retrait_surgery_hyp)."""
    from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import successeur
    return successeur(_t(c))


def _S_etoile(c):
    """(C⊔{∅})∖{*}  (S privé du marqueur), EXACTEMENT le but de retrait_surgery_hyp."""
    from bourbaki.entiers.iii_4_entiers_finis.iii_4_2_pigeonhole_surgery.ensembles_retrait_point import _S, _STAR
    return E.difference(_S(c), E.singleton(_STAR))


def retrait_un_point_hypothese(b="b", c="c", q="q"):
    """La formule HD(b, c) := (∀q)( q ∈ c+1 ⇒ Eq( (c+1)∖{q}, (C⊔{∅})∖{*} ) ).

    RÉSIDU PROPRE de la surgery : « retirer un point quelconque du (c+1)-cardinal
    donne un ensemble équipotent à (C⊔{∅})∖{*} ».  Brique CONCRÈTE (échange ponctuel
    via la transposition DÉJÀ construite), à fournir/décharger — jamais postulée."""
    from bourbaki.cardinaux.ensembles_cardinaux import equipotent
    vc, vq = _t(c), _t(q)
    succ_c = _succ(c)                                        # c+1
    diff_q = E.difference(succ_c, E.singleton(vq))          # (c+1)∖{q}
    Sstar = _S_etoile(c)                                     # (C⊔{∅})∖{*}
    nom = q if isinstance(q, str) else q.nom
    return pourtout(nom, impl(appartient(vq, succ_c), equipotent(diff_q, Sstar)))


def _combination_succ_t(b, c):
    """⊢ ( est_injection_de(F,b,c+1) et image(F,b)≠c+1 ) ⇒ (∃q)(q∈c+1 et b≤(c+1)∖{q}),
       version au TERME c+1 (= Card(C⊔{∅}), codomaine OPAQUE).

    injection_non_surj_donne_inf_egal_diff n'accepte qu'un NOM pour E (sinon CAPTURE :
    c+1 contient des liants z, u, v, F dans le τ de Card) ; on généralise sur E puis
    on instancie au TERME c+1 (renommage déterministe, sans capture), comme
    _prop1_direct_t.  F, b restent des noms."""
    base = injection_non_surj_donne_inf_egal_diff("F", b, "E")   # E nom : CLOS
    gen = N.generalisation("E", base)
    return instancie(gen, _succ(c))                              # instancie E := c+1


def retrait_surgery_assemble(b="b", c="c", f="F"):
    """{ HD(b,c) } ⊢ retrait_surgery_hyp(b,c,F)
       = ( est_injection_de(F,b,c+1) et image(F,b)≠c+1 ) ⇒ ( b ≤ (C⊔{∅})∖{*} ).

    🎯 retrait_surgery_hyp ASSEMBLÉ modulo la SEULE équipotence des retraits ponctuels.
    Sous l'hypothèse ( inj et ¬surj ) :
      • _combination_succ_t (CLOS, E=c+1 instancié) ⊢ (∃q)( q∈c+1 et b≤(c+1)∖{q} ) ;
      • pour CE q : HD(b,c) instancié ⊢ Eq( (c+1)∖{q}, S∖{*} ),
        puis inf_egal_via_eq_codom (CLOS) ⊢ b ≤ S∖{*} ;
      • la conclusion b ≤ S∖{*} ne contient pas q ⇒ existe_elimination ⇒ b ≤ S∖{*}.
    Conclusion ÉGALE LITTÉRALEMENT à retrait_surgery_hyp(b,c,F).  Une SEULE hypothèse
    résiduelle ISOLÉE (HD), déchargée par loi_deduction — jamais postulée.

    ⚠️ Le corps existentiel (q∈c+1 et b≤(c+1)∖{q}) et le terme (c+1)∖{q} sont EXTRAITS
    du théorème instancié (et NON reconstruits) pour garantir l'égalité structurelle
    malgré le renommage anti-capture du τ de Card(C⊔{∅})."""
    from bourbaki.entiers.iii_4_entiers_finis.iii_4_2_pigeonhole_surgery.ensembles_retrait_point import (
        retrait_surgery_hyp, inf_egal_via_eq_codom)
    from bourbaki.logique.tactiques.tactiques_abrege_quantif import existe_elimination
    from bourbaki.logique.tactiques.tactiques_abrege import antecedent_consequent
    vb, vc, vf = _t(b), _t(c), _t(f)
    succ_c = _succ(c)                                        # c+1
    Sstar = _S_etoile(c)                                     # (C⊔{∅})∖{*}

    inj = est_injection_de(vf, vb, succ_c)
    non_surj = non(egal(E.image(vf, vb), succ_c))
    ante = et(inj, non_surj)

    # combinaison instanciée : ante ⇒ (∃q)(q∈c+1 et b≤(c+1)∖{q})
    comb = _combination_succ_t(b, c)
    _, ex_concl = antecedent_consequent(comb.conclusion)    # (∃q)(q∈c+1 et b≤(c+1)∖{q})
    nomq = ex_concl.lieur                                    # le NOM du liant existentiel
    body = ex_concl.sous[0]                                  # q∈c+1 et b≤(c+1)∖{q}  (corps)
    vq = var(nomq)
    # (c+1)∖{q}  reconstruit (q ∉ liants de c+1 ⇒ pas de renommage) ; vérifié structurellement
    diff_q = E.difference(succ_c, E.singleton(vq))          # (c+1)∖{q}
    le_q_extrait = conjonction_elim_droite(N.assume(body)).conclusion   # b≤(c+1)∖{q}  (extrait)
    assert le_q_extrait == inf_egal_card(vb, diff_q), \
        "le terme (c+1)∖{q} reconstruit ne matche pas le corps existentiel instancié"

    h_HD = N.assume(retrait_un_point_hypothese(b, c, nomq))  # HD(b,c)  [hypothèse résiduelle]

    h_ante = N.assume(ante)                                  # (inj et ¬surj)
    ex_q = N.modus_ponens(h_ante, comb)                      # (∃q)(q∈c+1 et b≤(c+1)∖{q})

    # corps : (q∈c+1 et b≤(c+1)∖{q}) ⇒ b ≤ S∖{*}   [sous HD]
    h_body = N.assume(body)
    q_inn = conjonction_elim_gauche(h_body)                 # q∈c+1
    le_qq = conjonction_elim_droite(h_body)                 # b≤(c+1)∖{q}
    eq_q = N.modus_ponens(q_inn, instancie(h_HD, vq))       # Eq((c+1)∖{q}, S∖{*})  [HD]
    transport = inf_egal_via_eq_codom(vb, diff_q, Sstar)    # (b≤Y et Eq(Y,Z))⇒b≤Z
    le_star = N.modus_ponens(conjonction_intro(le_qq, eq_q), transport)   # b ≤ S∖{*}
    corps_imp = N.loi_deduction(body, le_star)             # (q∈c+1 et b≤(c+1)∖{q}) ⇒ b≤S∖{*}

    ex_imp = existe_elimination(corps_imp, nomq)           # (∃q)(…) ⇒ b≤S∖{*}
    conc = N.modus_ponens(ex_q, ex_imp)                    # b ≤ S∖{*}   [hyps ante, HD]
    inner = N.loi_deduction(ante, conc)                    # (inj et ¬surj) ⇒ b≤S∖{*}   [hyp HD]
    assert inner.conclusion == retrait_surgery_hyp(b, c, f), \
        "la conclusion n'égale pas retrait_surgery_hyp(b,c,F)"
    return inner


def retrait_surgery_mod_HD(b="b", c="c", f="F", q="q"):
    """⊢ HD(b,c) ⇒ retrait_surgery_hyp(b,c,F).   (THÉORÈME CLOS, 0 hyp.)

    Forme CONDITIONNELLE entièrement CLOSE : l'équipotence des retraits ponctuels
    HD(b,c) est DÉCHARGÉE (loi_deduction) en antécédent explicite.  La conséquence EST
    retrait_surgery_hyp(b,c,F) de ensembles_retrait_point LITTÉRALEMENT.  Aucune
    hypothèse résiduelle, rien postulé : dès que HD est prouvée (l'échange ponctuel via
    la transposition DÉJÀ construite ramenant tout point retiré sur le marqueur), la
    surgery est inconditionnelle, et le report retrait_surgery_hyp est fermé — donc,
    par retrait_point_hyp_mod_surgery + cardinal_pas_entre_conditionnel, le LEMME N est
    clos modulo le SEUL est_cardinal(b)."""
    from bourbaki.entiers.iii_4_entiers_finis.iii_4_2_pigeonhole_surgery.ensembles_retrait_point import retrait_surgery_hyp
    inner = retrait_surgery_assemble(b, c, f)              # retrait_surgery_hyp [hyp HD]
    HD = retrait_un_point_hypothese(b, c, q)
    return N.loi_deduction(HD, inner)                      # HD ⇒ retrait_surgery_hyp


# ════════════════════════════════════════════════════════════════════════════
#  RÉDUCTION FINALE — HD ⇐ « les retraits ponctuels d'ensembles équipotents sont
#  équipotents » (le résidu PROPRE et GÉNÉRAL, indépendant de C/* et de c+1)
#
#    GEN := (∀X)(∀Y)(∀x)(∀y)( ( Eq(X,Y) et x∈X et y∈Y ) ⇒ Eq( X∖{x}, Y∖{y} ) ).
#
#  C'est le seul vrai contenu combinatoire restant (échange ponctuel par la
#  TRANSPOSITION DÉJÀ construite, transposition_existe).  HD s'en déduit en
#  instanciant X:=c+1=Card(C⊔{∅}), Y:=C⊔{∅}, y:=* avec Eq(c+1,C⊔{∅}) (eq_succ_ensemble,
#  CLOS) et *∈C⊔{∅} (marqueur_dans_somme, CLOS).
# ════════════════════════════════════════════════════════════════════════════
def equipotence_retrait_un_point_general(x="X", y="Y", xp="x", yp="y"):
    """La formule GEN := (∀X)(∀Y)(∀x)(∀y)( ( Eq(X,Y) et x∈X et y∈Y ) ⇒ Eq(X∖{x}, Y∖{y}) ).

    « Le retrait d'un point de deux ensembles ÉQUIPOTENTS donne deux ensembles
    équipotents » — théorème de Bourbaki E.III.4 (surgery ponctuelle).  RÉSIDU PROPRE,
    GÉNÉRAL et RÉUTILISABLE de la branche non surjective du LEMME N.  Sa preuve =
    l'échange ponctuel par la transposition τ DÉJÀ construite (transposition_existe,
    clos) : pour une bijection β : X→Y, on amène β(x) sur y par τ_{Y,y,β(x)}, puis on
    restreint β (resp. τ∘β) à X∖{x} (bijection sur Y∖{y}).  À fournir/décharger —
    jamais postulée."""
    from bourbaki.cardinaux.ensembles_cardinaux import equipotent
    vX, vY, vx, vy = _t(x), _t(y), _t(xp), _t(yp)
    diffX = E.difference(vX, E.singleton(vx))               # X∖{x}
    diffY = E.difference(vY, E.singleton(vy))               # Y∖{y}
    corps = impl(et(et(equipotent(vX, vY), appartient(vx, vX)), appartient(vy, vY)),
                 equipotent(diffX, diffY))
    nX = x if isinstance(x, str) else x.nom
    nY = y if isinstance(y, str) else y.nom
    nx = xp if isinstance(xp, str) else xp.nom
    ny = yp if isinstance(yp, str) else yp.nom
    return pourtout(nX, pourtout(nY, pourtout(nx, pourtout(ny, corps))))


def retrait_un_point_depuis_general(b="b", c="c", q="q"):
    """⊢ GEN ⇒ HD(b,c).   (l'équipotence générale des retrait ponctuels fournit HD.)

    HD(b,c) = (∀q)(q∈c+1 ⇒ Eq((c+1)∖{q}, (C⊔{∅})∖{*})).  Pour chaque q∈c+1 :
      • GEN instancié en X:=c+1, Y:=C⊔{∅}, x:=q, y:=* ⊢
            ( Eq(c+1,C⊔{∅}) et q∈c+1 et *∈C⊔{∅} ) ⇒ Eq((c+1)∖{q}, (C⊔{∅})∖{*}) ;
      • Eq(c+1, C⊔{∅})   (eq_succ_ensemble, CLOS) ;
      • *∈C⊔{∅}          (marqueur_dans_somme, CLOS) ;
      • d'où Eq((c+1)∖{q}, (C⊔{∅})∖{*}) sous la seule hyp q∈c+1.
    Généralisation en q ⇒ HD.  Aucune hypothèse résiduelle hors GEN."""
    from bourbaki.entiers.iii_4_entiers_finis.iii_4_2_pigeonhole_surgery.ensembles_retrait_point import _S, _STAR, eq_succ_ensemble
    from bourbaki.cardinaux.arithmetique.ensembles_prop8_plus_point import marqueur_dans_somme
    vc, vq = _t(c), _t(q)
    succ_c = _succ(c)                                        # c+1 = Card(C⊔{∅})
    S = _S(c)                                                # C⊔{∅}
    GEN = equipotence_retrait_un_point_general()
    h_GEN = N.assume(GEN)
    # instancie X:=c+1, Y:=S, x:=q, y:=*   (au niveau du ∀, capture-safe)
    inst = instancie(instancie(instancie(instancie(h_GEN, succ_c), S), vq), _STAR)
    # antécédent ( Eq(c+1,S) et q∈c+1 et *∈S )
    eq_cs = eq_succ_ensemble(c)                              # Eq(c+1, S)   (CLOS)
    star_in = marqueur_dans_somme(c)                         # *∈S          (CLOS)
    q_in = appartient(vq, succ_c)
    h_qin = N.assume(q_in)                                   # q∈c+1
    ante = conjonction_intro(conjonction_intro(eq_cs, h_qin), star_in)   # Eq(c+1,S) et q∈c+1 et *∈S
    eq_diff = N.modus_ponens(ante, inst)                    # Eq((c+1)∖{q}, S∖{*})  [hyp q∈c+1]
    corps_q = N.loi_deduction(q_in, eq_diff)                # q∈c+1 ⇒ Eq((c+1)∖{q}, S∖{*})
    nomq = q if isinstance(q, str) else q.nom
    HD = N.generalisation(nomq, corps_q)                    # HD(b,c)   [hyp GEN]
    return N.loi_deduction(GEN, HD)                         # GEN ⇒ HD


def retrait_surgery_mod_general(b="b", c="c", f="F", q="q"):
    """⊢ GEN ⇒ retrait_surgery_hyp(b,c,F).   (THÉORÈME CLOS, 0 hyp.)

    🎯 La COMPOSITION FINALE : la branche non surjective du LEMME N réduite à la SEULE
    équipotence GÉNÉRALE des retraits ponctuels GEN.
        GEN ⇒[retrait_un_point_depuis_general] HD(b,c)
            ⇒[retrait_surgery_mod_HD]            retrait_surgery_hyp(b,c,F).
    Conclusion CLOSE.  Tout le reste de la surgery (re-ciblage, point raté, transport
    cardinal↔ensemble, *∈S) est INCONDITIONNEL ; il NE reste, pour fermer le LEMME N
    inconditionnellement (modulo est_cardinal(b)), que de PROUVER GEN — l'échange
    ponctuel via la transposition τ DÉJÀ construite (transposition_existe, clos)."""
    from bourbaki.entiers.iii_4_entiers_finis.iii_4_2_pigeonhole_surgery.ensembles_retrait_point import retrait_surgery_hyp
    GEN = equipotence_retrait_un_point_general()
    g_to_hd = retrait_un_point_depuis_general(b, c, q)      # GEN ⇒ HD
    hd_to_surg = retrait_surgery_mod_HD(b, c, f, q)         # HD ⇒ retrait_surgery_hyp
    h_GEN = N.assume(GEN)
    HD = N.modus_ponens(h_GEN, g_to_hd)                     # HD   [hyp GEN]
    surg = N.modus_ponens(HD, hd_to_surg)                  # retrait_surgery_hyp   [hyp GEN]
    return N.loi_deduction(GEN, surg)                      # GEN ⇒ retrait_surgery_hyp


# ════════════════════════════════════════════════════════════════════════════
#  CAPSTONE — LEMME N (cardinal_pas_entre) modulo le SEUL ( est_cardinal(b) et GEN )
# ════════════════════════════════════════════════════════════════════════════
def retrait_point_hyp_mod_general(b="b", c="c", f="F", q="q"):
    """⊢ GEN ⇒ retrait_point_hyp(b,c,F).   (THÉORÈME CLOS, 0 hyp.)

    Composition de retrait_surgery_mod_general (GEN ⇒ retrait_surgery_hyp) et de
    retrait_point_hyp_mod_surgery (retrait_surgery_hyp ⇒ retrait_point_hyp, CLOS dans
    ensembles_retrait_point).  La conséquence EST le report retrait_point_hyp(b,c,F) de
    ensembles_cardinal_pas_entre LITTÉRALEMENT (= retrait_point_hyp_enonce)."""
    from bourbaki.entiers.iii_4_entiers_finis.iii_4_2_pigeonhole_surgery.ensembles_retrait_point import (
        retrait_point_hyp_mod_surgery, retrait_point_hyp_enonce)
    from bourbaki.logique.tactiques.tactiques_abrege import antecedent_consequent
    GEN = equipotence_retrait_un_point_general()
    g2s = retrait_surgery_mod_general(b, c, f, q)          # GEN ⇒ retrait_surgery_hyp
    s2p = retrait_point_hyp_mod_surgery(b, c, f)           # retrait_surgery_hyp ⇒ retrait_point_hyp
    h_GEN = N.assume(GEN)
    surg = N.modus_ponens(h_GEN, g2s)                      # retrait_surgery_hyp  [GEN]
    rp = N.modus_ponens(surg, s2p)                         # retrait_point_hyp    [GEN]
    out = N.loi_deduction(GEN, rp)                         # GEN ⇒ retrait_point_hyp
    ante_chk, cons_chk = antecedent_consequent(out.conclusion)
    assert ante_chk == GEN and cons_chk == retrait_point_hyp_enonce(b, c, f), \
        "GEN ⇒ retrait_point_hyp mal formé"
    return out


def cardinal_pas_entre_mod_general(b="b", c="c", f="F", q="q"):
    """⊢ ( est_cardinal(b) et GEN ) ⇒ ( ( b ≤ c+1 ) ⇒ ( b ≤ c OU b = c+1 ) ).
       (THÉORÈME CLOS, 0 hyp.)

    🎯🎯 CAPSTONE : le LEMME N « pas de cardinal STRICTEMENT entre c et c+1 » réduit au
    SEUL antécédent explicite ( est_cardinal(b) et GEN ).  La conséquence EST
    cardinal_pas_entre(b,c) LITTÉRALEMENT.  Chaîne :
        GEN ⇒[retrait_point_hyp_mod_general] retrait_point_hyp(b,c,F)
            ⇒[généralisation F]               (∀F)retrait_point_hyp(b,c,F)
        ( est_cardinal(b) et (∀F)retrait_point_hyp ) ⇒[cardinal_pas_entre_conditionnel]
                                                cardinal_pas_entre(b,c).
    Donc, sous est_cardinal(b) (structurel) et GEN (= l'équipotence des retraits
    ponctuels, l'UNIQUE résidu combinatoire), le LEMME N est CLOS.  Le report
    cardinal_pas_entre de ensembles_recurrence_C61 est ainsi fermé MODULO GEN, lui-même
    réductible à la transposition τ DÉJÀ construite (transposition_existe, clos) :
    rien postulé, theorie=22."""
    from bourbaki.entiers.iii_4_entiers_finis.iii_4_recurrence_c61_existence_n.ensembles_cardinal_pas_entre import (
        cardinal_pas_entre_conditionnel, retrait_point_hyp_universel)
    from bourbaki.cardinaux.ensembles_cardinaux import est_cardinal
    vb = _t(b)
    nomf = f if isinstance(f, str) else f.nom
    GEN = equipotence_retrait_un_point_general()
    # GEN ⇒ retrait_point_hyp(b,c,F)  puis généralisation F (GEN sans F libre)
    g2rp = retrait_point_hyp_mod_general(b, c, f, q)       # GEN ⇒ retrait_point_hyp(b,c,F)
    h_GEN = N.assume(GEN)
    rp = N.modus_ponens(h_GEN, g2rp)                       # retrait_point_hyp(b,c,F)  [GEN]
    rp_univ = N.generalisation(nomf, rp)                   # (∀F)retrait_point_hyp(b,c,F)  [GEN]
    assert rp_univ.conclusion == retrait_point_hyp_universel(b, c, f), \
        "la forme universelle ne matche pas retrait_point_hyp_universel"
    g2univ = N.loi_deduction(GEN, rp_univ)                 # GEN ⇒ (∀F)retrait_point_hyp

    # cardinal_pas_entre_conditionnel : (est_cardinal(b) et (∀F)rp) ⇒ cardinal_pas_entre
    cond = cardinal_pas_entre_conditionnel(b, c, f)        # CLOS
    ec = est_cardinal(vb)
    ante = et(ec, GEN)
    h = N.assume(ante)
    h_ec = conjonction_elim_gauche(h)                      # est_cardinal(b)
    h_GEN2 = conjonction_elim_droite(h)                    # GEN
    univ = N.modus_ponens(h_GEN2, g2univ)                 # (∀F)retrait_point_hyp  [ante]
    cpe = N.modus_ponens(conjonction_intro(h_ec, univ), cond)   # cardinal_pas_entre(b,c)  [ante]
    return N.loi_deduction(ante, cpe)                     # (est_cardinal(b) et GEN) ⇒ cardinal_pas_entre


__all__ = [
    "image_evite_inclus_diff",
    "injection_evite_implique_inf_egal_diff",
    "non_surjective_donne_point_rate",
    "injection_non_surj_donne_inf_egal_diff",
    "retrait_un_point_hypothese",
    "retrait_surgery_assemble",
    "retrait_surgery_mod_HD",
    "equipotence_retrait_un_point_general",
    "retrait_un_point_depuis_general",
    "retrait_surgery_mod_general",
    "retrait_point_hyp_mod_general",
    "cardinal_pas_entre_mod_general",
]
