"""§III.4 — LEMME N : « pas de cardinal STRICTEMENT entre c et c+1 ».

OBJECTIF (ferme l'un des deux reports de ℕ INCONDITIONNEL, cf.
ensembles_recurrence_C61.cardinal_pas_entre — qui n'y est qu'un ÉNONCÉ non prouvé) :

        cardinal_pas_entre(b, c) :   ( b ≤ c+1 )  ⇒  ( b ≤ c  OU  b = c+1 ).

C'est le pas de récurrence de fini_downward : un cardinal ≤ c+1 est, soit ≤ c, soit
ÉGAL à c+1 — il n'y a RIEN entre c et c+1.

──────────────────────────────────────────────────────────────────────────────
PREUVE (Bourbaki, principe des tiroirs E.III.4 ; surgery voisine de la Prop. 8) :

  b ≤ c+1  =  (∃f) est_injection_de(f, b, c+1),  où  c+1 = successeur(c) =
  Card(c ⊔ {∅}) = Card(C ⊔ {pt})  est le successeur cardinal fidèle.  Posons, pour un
  témoin f : b → c+1 injective :
      • c+1 (= le terme ensembliste successeur(c)) joue le rôle du codomaine ;
      • « f surjective sur c+1 »  :⇔  image(f, b) = c+1.

  TIERS EXCLU sur « image(f,b) = c+1 » :

   (A) image(f,b) = c+1  (f surjective).   Alors f, déjà injective de domaine b à
       valeurs dans c+1, devient BIJECTIVE de b sur c+1 (est_bijective = injective_dans
       ∧ image = c+1).  D'où Eq(b, c+1) (témoin f), puis Card b = Card(c+1) (Prop. 1
       sens direct).  Or c+1 = successeur(c) est TOUJOURS un cardinal, donc
       Card(c+1) = c+1 ; et sous est_cardinal(b), Card b = b.  Réécritures ⇒ b = c+1.
       [INCONDITIONNEL ici, modulo est_cardinal(b) — entièrement PROUVÉ ci-dessous.]

   (B) image(f,b) ≠ c+1  (f NON surjective).   Alors il existe un point q ∈ c+1 hors
       de l'image ; f envoie b dans (c+1) ∖ {q}.  Or retirer UN point d'un ensemble à
       c+1 éléments laisse un ensemble à c éléments : (c+1) ∖ {q} ≃ c (retrait d'un
       point d'un (c+1)-ensemble, principe des tiroirs).  Donc b injecte dans c, i.e.
       b ≤ c.
       [HARD — surgery « retrait d'un point » au niveau du GRAPHE, de la catégorie de
        difficulté de la Prop. 8 ; REPORTÉ comme HYPOTHÈSE ISOLÉE retrait_point_hyp.]

  cas(tiers_exclu(surj), branche_A, branche_B) ⇒ (b ≤ c OU b = c+1).

──────────────────────────────────────────────────────────────────────────────
SALVAGE GRADUÉ — ce qui est PROUVÉ vs REPORTÉ :

  ✅ INCONDITIONNEL (rien postulé, theorie=22) :
     • injection_surjective_est_bijection(f,X,Y) — est_injection_de(f,X,Y) ∧
       image(f,X)=Y ⇒ est_bijection_de(f,X,Y) ;
     • bijection_implique_equipotent(f,X,Y)      — est_bijection_de(f,X,Y) ⇒ Eq(X,Y) ;
     • card_succ_egale_succ(c)                    — Card(c+1) = c+1 (c+1 cardinal) ;
     • branche_surjective(b,c)                    — { est_cardinal(b) } ⊢ pour le témoin f,
       ( est_injection_de(f,b,c+1) ∧ image(f,b)=c+1 ) ⇒ b = c+1 ;
     • cardinal_pas_entre_assemble(b,c)           — l'ASSEMBLAGE par tiers-exclu, CLOS
       modulo les DEUX hypothèses explicites est_cardinal(b) et retrait_point_hyp.

  ⚠️ REPORTÉ (honnêtement, hypothèse ISOLÉE, jamais postulée comme théorème) :
     • retrait_point_hyp(b,c,f) = ( est_injection_de(f,b,c+1) ∧ image(f,b)≠c+1 ) ⇒ b ≤ c
       — la surgery « retrait d'un point » (c+1)∖{q} ≃ c.  C'est le SEUL maillon dur,
       point de raccord unique pour finir le lemme inconditionnellement.

⚠️ INVARIANT : theorie_ensembles() = 22 intangible.  AUCUN N.axiome dans theorie ;
   les seuls « givens » sont des HYPOTHÈSES explicites (est_cardinal(b), retrait_point_hyp),
   déchargées par loi_deduction — jamais postulées.
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (Terme, var, egal, et, ou, non, impl, existe,
                                       inclus)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    instancie, cas, tiers_exclu, equivalence_avant, equivalence_arriere,
)
from bourbaki.logique.i_4_egalitaires.tactiques_abrege_egalite import symetrie, composer_egalites
from bourbaki.logique.i_3_quantifies.tactiques_abrege_quantif import existe_elimination

from bourbaki.cardinaux.ensembles_cardinaux import (
    est_cardinal, cardinal, inf_egal_card, est_injection_de, est_bijection_de,
    equipotent,
)
from bourbaki.cardinaux.arithmetique.iii_3_3_produit.ensembles_arith_cardinale import _prop1_direct_t
from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import successeur
from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_fini_successeur import (
    successeur_est_un_cardinal, cardinal_de_cardinal,
)


def _t(t):
    """Coercion str/Terme → Terme."""
    return t if isinstance(t, Terme) else var(t)


# ════════════════════════════════════════════════════════════════════════════
#  LEMME UNCONDITIONNEL 1 — injection + surjection  ⇒  bijection
#
#  est_injection_de(F,X,Y) = ((fonctionnel ∧ dom=X) ∧ injective_dans(F,X)) ∧ image⊂Y.
#  est_bijection_de(F,X,Y) = (fonctionnel ∧ dom=X) ∧ (injective_dans(F,X) ∧ image=Y).
#  Si en outre image(F,X) = Y, on RECOMPOSE est_bijection_de à partir des conjoints
#  de est_injection_de (on remplace « image⊂Y » par « image=Y », plus fort).
# ════════════════════════════════════════════════════════════════════════════
def injection_surjective_est_bijection(f="F", X="X", Y="Y"):
    """⊢ ( est_injection_de(F,X,Y) et image(F,X)=Y ) ⇒ est_bijection_de(F,X,Y).

    Une injection f : X → Y dont l'image directe est Y TOUT ENTIER est bijective.
    Re-projection des conjoints : est_injection_de fournit (fonctionnel ∧ dom=X),
    injective_dans(F,X) et image⊂Y ; l'hypothèse image=Y donne le conjoint surjectif
    de est_bijective ; on réassemble est_bijection_de = (fonct ∧ dom=X) ∧ (inj ∧ image=Y).
    INCONDITIONNEL."""
    vf, vX, vY = _t(f), _t(X), _t(Y)
    inj = est_injection_de(vf, vX, vY)                       # injection
    surj = egal(E.image(vf, vX), vY)                         # image(F,X) = Y
    h = N.assume(et(inj, surj))                              # injection et image=Y
    h_inj = conjonction_elim_gauche(h)                       # est_injection_de(F,X,Y)
    h_surj = conjonction_elim_droite(h)                      # image(F,X) = Y
    # est_injection_de = ((fonct ∧ dom=X) ∧ injective_dans) ∧ image⊂Y
    fonc_dom = conjonction_elim_gauche(conjonction_elim_gauche(h_inj))   # fonctionnel ∧ dom=X
    inj_dans = conjonction_elim_droite(conjonction_elim_gauche(h_inj))   # injective_dans(F,X)
    # est_bijective(F,X,Y) = injective_dans(F,X) ∧ image=Y
    bijective = conjonction_intro(inj_dans, h_surj)          # est_bijective(F,X,Y)
    # est_bijection_de = (fonct ∧ dom=X) ∧ est_bijective
    bij = conjonction_intro(fonc_dom, bijective)             # est_bijection_de(F,X,Y)
    assert bij.conclusion == est_bijection_de(vf, vX, vY), \
        "recomposition de est_bijection_de incorrecte"
    return N.loi_deduction(et(inj, surj), bij)


# ════════════════════════════════════════════════════════════════════════════
#  LEMME UNCONDITIONNEL 2 — bijection  ⇒  équipotence  (témoin)
# ════════════════════════════════════════════════════════════════════════════
def bijection_implique_equipotent(f="F", X="X", Y="Y"):
    """⊢ est_bijection_de(F,X,Y) ⇒ Eq(X,Y).

    Eq(X,Y) := (∃F)est_bijection_de(F,X,Y) ; le témoin est F (S5).  INCONDITIONNEL."""
    vf, vX, vY = _t(f), _t(X), _t(Y)
    bij = est_bijection_de(vf, vX, vY)
    h = N.assume(bij)
    # (∃F) est_bijection_de(F,X,Y) = Eq(X,Y)   via S5 témoin F
    ex = N.modus_ponens(h, N.s5(est_bijection_de(var("F"), vX, vY), vf, "F"))
    assert ex.conclusion == equipotent(vX, vY), "S5 ne produit pas Eq(X,Y)"
    return N.loi_deduction(bij, ex)


# ════════════════════════════════════════════════════════════════════════════
#  LEMME UNCONDITIONNEL 3 — Card(c+1) = c+1   (le successeur est un cardinal)
# ════════════════════════════════════════════════════════════════════════════
def card_succ_egale_succ(c="c"):
    """⊢ Card(c+1) = c+1.   (le successeur cardinal est son propre cardinal ; INCONDITIONNEL.)

    c+1 = successeur(c) est TOUJOURS un cardinal (successeur_est_un_cardinal) ; un
    cardinal coïncide avec son cardinal (cardinal_de_cardinal)."""
    vc = _t(c)
    succ_c = successeur(vc)                                  # c+1
    is_card = successeur_est_un_cardinal(c)                  # est_cardinal(c+1)
    return N.modus_ponens(is_card, cardinal_de_cardinal(succ_c))   # Card(c+1) = c+1


# ════════════════════════════════════════════════════════════════════════════
#  BRANCHE (A) — f SURJECTIVE  ⇒  b = c+1   (INCONDITIONNEL modulo est_cardinal(b))
#
#  Pour le témoin f : b → c+1 injective ET surjective (image=c+1) :
#    • injection_surjective_est_bijection : f est BIJECTIVE de b sur c+1 ;
#    • bijection_implique_equipotent       : Eq(b, c+1) ;
#    • Prop. 1 sens direct (_prop1_direct_t) : Card b = Card(c+1) ;
#    • Card(c+1) = c+1 (card_succ_egale_succ)  et, sous est_cardinal(b), Card b = b
#      (cardinal_de_cardinal) ⇒ réécritures ⇒ b = c+1.
# ════════════════════════════════════════════════════════════════════════════
def branche_surjective(b="b", c="c", f="F"):
    """⊢ { est_cardinal(b) } ⊢
         ( est_injection_de(f, b, c+1) et image(f,b)=c+1 ) ⇒ ( b = c+1 ).

    La BRANCHE SURJECTIVE du tiers-exclu : si f : b → c+1 est injective ET d'image
    pleine (= c+1), alors b = c+1.  Entièrement PROUVÉE (modulo l'hypothèse
    est_cardinal(b), indispensable pour identifier Card b à b).  INCONDITIONNEL au
    sens où aucune surgery n'est requise — uniquement bijection ⇒ Eq ⇒ Card= + Prop. 8/1."""
    vb, vc, vf = _t(b), _t(c), _t(f)
    succ_c = successeur(vc)                                  # c+1
    inj = est_injection_de(vf, vb, succ_c)                   # injection f : b → c+1
    surj = egal(E.image(vf, vb), succ_c)                     # image(f,b) = c+1
    ante = et(inj, surj)
    h = N.assume(ante)                                       # injection et surjection

    # f bijective ⇒ Eq(b, c+1)
    bij = N.modus_ponens(h, injection_surjective_est_bijection(f, b, succ_c))   # bijection
    eq_b_succ = N.modus_ponens(bij, bijection_implique_equipotent(f, b, succ_c))   # Eq(b, c+1)
    # Card b = Card(c+1)   (Prop. 1 sens direct)
    card_eq = N.modus_ponens(eq_b_succ, _prop1_direct_t(vb, succ_c))   # Card b = Card(c+1)
    # Card(c+1) = c+1   (INCONDITIONNEL)
    card_succ = card_succ_egale_succ(c)                      # Card(c+1) = c+1
    # Card b = c+1   (composition)
    cardb_eq_succ = composer_egalites(card_eq, card_succ)    # Card b = c+1
    # b = Card b   sous est_cardinal(b)
    h_card_b = N.assume(est_cardinal(vb))                    # est_cardinal(b)
    cardb_eq_b = N.modus_ponens(h_card_b, cardinal_de_cardinal(vb))   # Card b = b
    b_eq_cardb = N.modus_ponens(cardb_eq_b, symetrie(cardinal(vb), vb))   # b = Card b
    # b = c+1
    b_eq_succ = composer_egalites(b_eq_cardb, cardb_eq_succ)   # b = c+1   [hyps ante, est_cardinal(b)]
    return N.loi_deduction(ante, b_eq_succ)                  # (inj et surj) ⇒ b=c+1  [est_cardinal(b)]


# ════════════════════════════════════════════════════════════════════════════
#  BRANCHE (B) — f NON surjective  ⇒  b ≤ c   (HARD : surgery « retrait d'un point »)
#
#  REPORTÉ honnêtement comme HYPOTHÈSE ISOLÉE.  Énoncé exact (pour le témoin f) :
#      ( est_injection_de(f, b, c+1) et image(f,b) ≠ c+1 )  ⇒  b ≤ c.
#  Justification mathématique : un point q ∈ c+1 ∖ image(f,b) existe ; f envoie b dans
#  (c+1)∖{q} ≃ c (retrait d'un point d'un (c+1)-ensemble), d'où une injection b → c.
#  La construction de la bijection (c+1)∖{q} ≃ c (au niveau du graphe, avec sélecteur
#  τ du point retiré + recollement) est de la catégorie de difficulté de la Prop. 8.
# ════════════════════════════════════════════════════════════════════════════
def retrait_point_hyp(b, c, f="F"):
    """Énoncé de la BRANCHE NON SURJECTIVE (HYPOTHÈSE isolée, REPORTÉE) :
        ( est_injection_de(f, b, c+1) et image(f,b) ≠ c+1 )  ⇒  ( b ≤ c ).

    ⚠️ NON PROUVÉ ici : surgery « retrait d'un point » (c+1)∖{q} ≃ c (principe des
    tiroirs E.III.4, voisine de la Prop. 8).  Posé comme hypothèse explicite du pas,
    déchargée par loi_deduction dans cardinal_pas_entre_assemble — jamais postulée."""
    vb, vc, vf = _t(b), _t(c), _t(f)
    succ_c = successeur(vc)
    inj = est_injection_de(vf, vb, succ_c)
    non_surj = non(egal(E.image(vf, vb), succ_c))
    return impl(et(inj, non_surj), inf_egal_card(vb, vc))


def retrait_point_hyp_universel(b, c, f="F"):
    """Énoncé UNIVERSEL de la branche non surjective (HYPOTHÈSE isolée, REPORTÉE) :
        (∀F)( ( est_injection_de(F, b, c+1) et image(F,b) ≠ c+1 ) ⇒ ( b ≤ c ) ).

    Forme close en F (la surgery « retrait d'un point » vaut pour TOUT témoin f de
    b ≤ c+1) : c'est la version requise par l'ASSEMBLAGE, car la décharge du ∃f
    (existe_elimination) exige que l'hypothèse restante ne contienne pas F libre.
    On l'instancie au témoin f à l'intérieur du corps.  ⚠️ NON PROUVÉE (REPORTÉE)."""
    from bourbaki.logique.i_1_termes_relations.formule import pourtout
    nom = f if isinstance(f, str) else f.nom
    return pourtout(nom, retrait_point_hyp(b, c, f))


# ════════════════════════════════════════════════════════════════════════════
#  ASSEMBLAGE — cardinal_pas_entre par TIERS-EXCLU (CLOS modulo 2 hyps isolées)
# ════════════════════════════════════════════════════════════════════════════
def cardinal_pas_entre_assemble(b="b", c="c", f="F"):
    """⊢ { est_cardinal(b),  (pour le témoin f) retrait_point_hyp(b,c,f) } ⊢
         ( b ≤ c+1 )  ⇒  ( b ≤ c  OU  b = c+1 ).

    🎯 LEMME N « pas de cardinal strictement entre c et c+1 », ASSEMBLÉ par tiers-exclu
    sur « image(f,b) = c+1 » :
       • b ≤ c+1 = (∃f) est_injection_de(f, b, c+1) — on travaille SOUS un témoin f ;
       • tiers_exclu(image(f,b)=c+1) :
           – branche SURJ  : branche_surjective ⇒ b = c+1  ⇒ (b≤c OU b=c+1)  (droite) ;
           – branche ¬SURJ : retrait_point_hyp ⇒ b ≤ c     ⇒ (b≤c OU b=c+1)  (gauche).
       • le ∃f se décharge par existe_elimination (la conclusion b≤c OU b=c+1 ne
         contient pas f).

    DEUX hypothèses explicites, ISOLÉES, déchargées par loi_deduction (jamais postulées
    comme théorèmes) :
       • est_cardinal(b)        — b est un cardinal (vrai dans la récurrence où b parcourt
                                  les cardinaux ; sans elle « b=c+1 » n'a pas de sens) ;
       • retrait_point_hyp_universel(b,c) = (∀F)retrait_point_hyp(b,c,F) — la surgery
         « retrait d'un point » (forme UNIVERSELLE, close en F ; SEUL maillon dur).
    Dès que retrait_point_hyp est prouvée (sous est_cardinal(b)), le lemme est CLOS et
    le report cardinal_pas_entre de ensembles_recurrence_C61 est fermé."""
    vb, vc, vf = _t(b), _t(c), _t(f)
    succ_c = successeur(vc)                                  # c+1
    inj = est_injection_de(vf, vb, succ_c)                   # est_injection_de(f, b, c+1)
    img_eq = egal(E.image(vf, vb), succ_c)                   # image(f,b) = c+1
    cible = ou(inf_egal_card(vb, vc), egal(vb, succ_c))      # b ≤ c OU b = c+1

    # SOUS un témoin f de b ≤ c+1 :  est_injection_de(f, b, c+1)
    h_inj = N.assume(inj)

    le_c = inf_egal_card(vb, vc)                            # b ≤ c
    eq_succ = egal(vb, succ_c)                              # b = c+1

    # — branche SURJECTIVE (image=c+1)  ⇒ b=c+1 ⇒ cible = (b≤c ∨ b=c+1)  (introduction à DROITE)
    h_surj = N.assume(img_eq)                              # image(f,b)=c+1
    b_eq_succ = N.modus_ponens(conjonction_intro(h_inj, h_surj),
                               branche_surjective(b, c, f))  # b = c+1   [est_cardinal(b), inj, surj]
    # (b=c+1) ⇒ ((b=c+1) ∨ (b≤c))  [S2]  puis  ⇒ ((b≤c) ∨ (b=c+1))  [S3, commutation]
    or_rev = N.modus_ponens(b_eq_succ, N.s2(eq_succ, le_c))   # (b=c+1) ∨ (b≤c)
    cible_surj = N.modus_ponens(or_rev, N.s3(eq_succ, le_c))  # (b≤c) ∨ (b=c+1) = cible
    branche_droite = N.loi_deduction(img_eq, cible_surj)   # (image=c+1) ⇒ cible   [est_cardinal(b), inj]

    # — branche NON SURJECTIVE (image≠c+1) ⇒ b≤c ⇒ cible  (introduction à GAUCHE, S2 direct)
    #   l'hypothèse est la forme UNIVERSELLE (∀F) (close en F, pour décharger le ∃f),
    #   instanciée au témoin f courant.
    h_retrait = N.assume(retrait_point_hyp_universel(b, c, f))   # (∀F)( (inj et ¬surj) ⇒ b≤c )
    retrait_f = instancie(h_retrait, vf)                   # (inj et ¬surj) ⇒ b≤c   [au témoin f]
    h_nsurj = N.assume(non(img_eq))                        # image(f,b)≠c+1
    b_le_c = N.modus_ponens(conjonction_intro(h_inj, h_nsurj), retrait_f)   # b ≤ c   [retrait univ, inj]
    cible_nsurj = N.modus_ponens(b_le_c, N.s2(le_c, eq_succ))   # (b≤c) ∨ (b=c+1) = cible
    branche_gauche = N.loi_deduction(non(img_eq), cible_nsurj)   # (image≠c+1) ⇒ cible

    # — tiers exclu : (image=c+1) OU (image≠c+1)
    te = tiers_exclu(img_eq)                                # (image=c+1) ∨ ¬(image=c+1)
    cible_sous_temoin = cas(te, branche_droite, branche_gauche)   # cible  [est_cardinal(b), retrait, inj]

    # — décharge l'injection (corps du ∃f) puis le ∃f
    corps = N.loi_deduction(inj, cible_sous_temoin)        # est_injection_de(f,b,c+1) ⇒ cible
    ex_imp = existe_elimination(corps, f if isinstance(f, str) else f.nom)   # (∃f)inj ⇒ cible = (b≤c+1) ⇒ cible
    assert ex_imp.conclusion == impl(inf_egal_card(vb, succ_c), cible), \
        "l'assemblage ne conclut pas (b≤c+1) ⇒ (b≤c ou b=c+1)"
    return ex_imp


# ════════════════════════════════════════════════════════════════════════════
#  FORME CONDITIONNELLE CLOSE — les deux reports DÉCHARGÉS en antécédent explicite
# ════════════════════════════════════════════════════════════════════════════
def cardinal_pas_entre_conditionnel(b="b", c="c", f="F"):
    """⊢ ( est_cardinal(b) et (∀F) retrait_point_hyp(b,c,F) )
            ⇒ ( ( b ≤ c+1 ) ⇒ ( b ≤ c OU b = c+1 ) ).   (THÉORÈME CLOS, 0 hyp.)

    Forme CONDITIONNELLE entièrement CLOSE de cardinal_pas_entre : les deux maillons
    isolés — est_cardinal(b) et la surgery universelle retrait_point_hyp_universel —
    sont DÉCHARGÉS (loi_deduction) en un unique antécédent explicite.  La conséquence
    EST cardinal_pas_entre(b,c) LITTÉRALEMENT.  Aucune hypothèse résiduelle, rien
    postulé : dès que l'antécédent est prouvé (la surgery « retrait d'un point »), le
    lemme N est inconditionnel et le report de ensembles_recurrence_C61 est fermé."""
    vb = _t(b)
    inner = cardinal_pas_entre_assemble(b, c, f)            # cardinal_pas_entre(b,c) [est_card(b), retrait]
    ec = est_cardinal(vb)                                   # est_cardinal(b)
    rp = retrait_point_hyp_universel(b, c, f)               # (∀F) retrait_point_hyp(b,c,F)
    ante = et(ec, rp)
    h = N.assume(ante)
    sous = N.modus_ponens(conjonction_elim_droite(h),
                          N.loi_deduction(rp, N.modus_ponens(
                              conjonction_elim_gauche(h),
                              N.loi_deduction(ec, inner))))   # cardinal_pas_entre(b,c) [hyp ante]
    return N.loi_deduction(ante, sous)                     # (est_card(b) et retrait) ⇒ cardinal_pas_entre(b,c)


__all__ = [
    "injection_surjective_est_bijection",
    "bijection_implique_equipotent",
    "card_succ_egale_succ",
    "branche_surjective",
    "retrait_point_hyp",
    "retrait_point_hyp_universel",
    "cardinal_pas_entre_assemble",
    "cardinal_pas_entre_conditionnel",
]
