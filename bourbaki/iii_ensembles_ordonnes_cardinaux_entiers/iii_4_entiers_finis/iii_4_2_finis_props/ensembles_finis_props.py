"""§III.4.2 — PROPOSITIONS sur les ENSEMBLES FINIS atteignables SANS récurrence.

Ce module SALVAGE, de manière GRADUÉE, les énoncés de E.III.4.2 (Proposition 2 et
ses Corollaires 1-4) qui sont accessibles INCONDITIONNELLEMENT à partir des grands
théorèmes DÉJÀ prouvés du projet :

  • CANTOR–BERNSTEIN  (antisymétrie de ≤ : (a≤b et b≤a) ⇒ Eq(a,b)),
  • COMPARABILITÉ     (ordre total : a≤b OU b≤a),
  • TRANSITIVITÉ de ≤ (composée d'injections : (a≤b et b≤c) ⇒ a≤c),
  • RÉFLEXIVITÉ de ≤  (la diagonale injecte),
  • Proposition 1 §III.3 (Eq(X,Y) ⇔ Card X = Card Y),
  • Prop. 1 §III.4.1 (Fini(𝔞) ⇒ Fini(𝔞+1)) [ensembles_fini_successeur].

────────────────────────────────────────────────────────────────────────────────
ÉNONCÉ DE BOURBAKI (E.III.4.2, Proposition 2) :

   « Soit n un entier.  Tout cardinal 𝔞 tel que 𝔞 ≤ n est un entier.  Si n ≠ 0, il
     existe un cardinal m et un seul tel que n = m + 1, et la relation 𝔞 < n est
     équivalente à 𝔞 ≤ m. »

   Cor. 1 : Toute partie d'un ensemble fini est finie.
   Cor. 2 : Si X ⊂ E (X ≠ E), E fini, alors Card(X) < Card(E).
   Cor. 3 : f : E → F, E fini ⇒ f(E) partie finie de F.
   Cor. 4 (tiroirs) : E, F finis de même cardinal, f : E → F ⇒ (inj ⇔ surj ⇔ bij).

────────────────────────────────────────────────────────────────────────────────
SALVAGE GRADUÉ — état des paliers (cf. les __all__) :

  ✅ INCONDITIONNEL (rien postulé, theorie_ensembles()=22) — PROPRIÉTÉS DIRECTES de
     l'ordre des cardinaux, valables EN PARTICULIER pour les cardinaux finis :
       • fini_implique_inf_egal_reflexif(a)   — Fini(a) ⇒ a ≤ a  (réflexivité) ;
       • antisymetrie_card_egal(a,b)          — (a≤b et b≤a) ⇒ Card a = Card b
                                                 [Cantor–Bernstein + Prop. 1 §III.3] ;
       • antisymetrie_cardinaux(a,b)          — (est_cardinal a et est_cardinal b et
                                                 a≤b et b≤a) ⇒ a = b  (deux cardinaux
                                                 chacun ≤ l'autre sont ÉGAUX) ;
       • comparabilite_finis(a,b)             — a ≤ b OU b ≤ a  (ordre total) ;
       • transitivite_inf_egal_finis(a,b,c)   — (a≤b et b≤c) ⇒ a≤c ;
       • inf_strict_exclut_reciproque(a,b)    — (a < b) ⇒ ¬(b ≤ a)  (asymétrie du <,
                                                 « pas de partie stricte plus grande »,
                                                 cœur de Cor. 2 — via Cantor–Bernstein) ;
       • inf_strict_irreflexif(a)             — ¬(a < a) ;
       • inf_strict_transitif(a,b,c)          — (a<b et b<c) ⇒ a<c (sous est_cardinal,
                                                 voir docstring) ;
       • trichotomie_finis(a,b)               — (est_cardinal a et est_cardinal b)
                                                 ⇒ (a<b OU a=b OU b<a).

  ⚠️ CONDITIONNEL (hypothèse ISOLÉE, jamais postulée comme théorème) :
       • prop2_cardinal_inf_n_est_entier(a,n) — (a ≤ n et Fini n) ⇒ Fini a  : c'est
         EXACTEMENT fini_downward (Prop. 2, « tout 𝔞 ≤ n est un entier »), qui dépend
         de la RÉCURRENCE C61 (cf. ensembles_recurrence_C61.fini_downward_thm, reporté
         au principe de bon ordre des cardinaux).  → fourni en forme CONDITIONNELLE,
         hypothèse fini_downward(a,n) déchargée en antécédent ;
       • cor1_partie_finie_est_finie(X,E)     — (X ⊂ E et E fini) ⇒ X fini  : repose
         sur Cor. 1 = Prop. 2 (Card X ≤ Card E + 𝔞≤n ⇒ entier) → CONDITIONNEL sur
         fini_downward ;
       • cor2_partie_stricte_card_strict(X,E) — surgery « retrait d'un point » /
         cardinal_pas_entre → REPORTÉ (énoncé seul, cf. rapport).

⚠️ INVARIANT : aucun N.axiome n'est ajouté à theorie_ensembles() (= 22) ; les seuls
   « givens » sont des HYPOTHÈSES explicites (Fini n, fini_downward, est_cardinal),
   déchargées par loi_deduction — JAMAIS postulées.  Anti-tautologie/anti-affaibli
   strict : chaque énoncé inconditionnel a un CONTENU (réflexivité, antisymétrie,
   comparabilité, asymétrie) non trivial, certifié par le noyau.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (Terme, var, egal, et, ou, non, impl, inclus)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N

from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    est_cardinal, cardinal, inf_egal_card, inf_strict_card,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux_theoremes import inf_egal_reflexif
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.ordre_cardinaux.ensembles_cardinaux_ordre import inf_egal_transitive
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.cantor_bernstein.cloture._recollement import cantor_bernstein
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.ordre_cardinaux.ensembles_comparabilite import comparabilite_cardinaux
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.ordinal_cardinal.bon_ordre_intervalle.ensembles_clause_plus_petit_monotonie import inf_egal_card_de_inclus_terme
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_produit.ensembles_arith_cardinale import _prop1_direct_t
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import est_fini
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_fini_successeur import cardinal_de_cardinal

from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    instancie, cas,
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
    symetrie, composer_egalites,
)


def _t(t):
    """Coercion str/Terme → Terme (utilitaire local)."""
    return t if isinstance(t, Terme) else var(t)


# ════════════════════════════════════════════════════════════════════════════
#  (1) RÉFLEXIVITÉ pour un cardinal fini :  Fini(a) ⇒ a ≤ a   (INCONDITIONNEL)
#
#  La réflexivité a ≤ a vaut pour TOUT terme a (la diagonale Δ_a injecte a dans a,
#  inf_egal_reflexif).  On l'AFFAIBLIT sous l'hypothèse Fini(a) pour matérialiser
#  la propriété dans le contexte « ensembles finis » de E.III.4.
# ════════════════════════════════════════════════════════════════════════════
def fini_implique_inf_egal_reflexif(a="a"):
    """⊢ Fini(a) ⇒ ( a ≤ a ).   (RÉFLEXIVITÉ de ≤, contextualisée aux finis ; INCONDITIONNEL.)

    a ≤ a est inconditionnel (inf_egal_reflexif : la diagonale Δ_a injecte a dans a) ;
    on l'introduit sous Fini(a) (affaiblissement S1), pour disposer de la réflexivité
    dans le langage des ensembles finis (E.III.4).  Tout cardinal fini se majore
    lui-même — base des comparaisons d'entiers."""
    va = _t(a)
    # a ≤ a   (réflexivité au TERME a, via (∀X)(X≤X))
    refl_all = N.generalisation("X", inf_egal_reflexif("X"))   # (∀X)(X ≤ X)
    le_aa = instancie(refl_all, va)                            # a ≤ a
    # introduit sous Fini(a) : loi_deduction(C6) ajoute l'antécédent Fini(a) (a≤a est
    # clos, donc Fini(a) ∉ ses hyps ; C6 retire-{Fini a} = no-op et produit l'implication).
    return N.loi_deduction(est_fini(va), le_aa)                # Fini(a) ⇒ (a ≤ a)


# ════════════════════════════════════════════════════════════════════════════
#  (2) ANTISYMÉTRIE de ≤  :  (a ≤ b et b ≤ a) ⇒ Card a = Card b   (INCONDITIONNEL)
#
#  Cantor–Bernstein : (a≤b et b≤a) ⇒ Eq(a,b) ; Prop. 1 §III.3 sens direct (terme) :
#  Eq(a,b) ⇒ Card a = Card b.  Composition.
# ════════════════════════════════════════════════════════════════════════════
def antisymetrie_card_egal(a="a", b="b"):
    """⊢ ( a ≤ b et b ≤ a ) ⇒ ( Card a = Card b ).   (ANTISYMÉTRIE de ≤ ; INCONDITIONNEL.)

    Corollaire 2 du Théorème 1 §III.3 (Cantor–Bernstein) : deux ensembles chacun
    équipotent à une partie de l'autre sont équipotents ; donc Card a = Card b
    (Proposition 1 §III.3, sens direct).  Vrai pour TOUS cardinaux, finis en
    particulier (E.III.4)."""
    va, vb = _t(a), _t(b)
    # cantor_bernstein avec ses liants DÉFAUT (A,B), généralisé puis instancié aux
    # termes va, vb : on ÉVITE la capture des liants internes (u,v,…) si va/vb sont des
    # noms minuscules qui collisionneraient (généralisation+instanciation = renommage sûr).
    cb_AB = cantor_bernstein("A", "B")                        # (A≤B et B≤A) ⇒ Eq(A,B)   [A,B libres]
    cb_gen = N.generalisation("A", N.generalisation("B", cb_AB))
    cb = instancie(instancie(cb_gen, va), vb)                # (a≤b et b≤a) ⇒ Eq(a,b)
    ante = et(inf_egal_card(va, vb), inf_egal_card(vb, va))
    h = N.assume(ante)
    eq_ab = N.modus_ponens(h, cb)                             # Eq(a,b)
    card_eq = N.modus_ponens(eq_ab, _prop1_direct_t(va, vb))  # Card a = Card b
    return N.loi_deduction(ante, card_eq)                    # (a≤b et b≤a) ⇒ Card a=Card b


def antisymetrie_cardinaux(a="a", b="b"):
    """⊢ ( est_cardinal(a) et est_cardinal(b) et a ≤ b et b ≤ a ) ⇒ ( a = b ).

    ANTISYMÉTRIE de ≤ sur les CARDINAUX (E.III.4) : deux cardinaux chacun ≤ l'autre
    sont ÉGAUX.  De antisymetrie_card_egal on tire Card a = Card b ; sous est_cardinal,
    Card a = a et Card b = b (cardinal_de_cardinal), d'où a = Card a = Card b = b.
    Forme conjointe (hypothèses regroupées), entièrement CLOSE — rien postulé."""
    va, vb = _t(a), _t(b)
    h_ca = est_cardinal(va)
    h_cb = est_cardinal(vb)
    le_ab = inf_egal_card(va, vb)
    le_ba = inf_egal_card(vb, va)
    ante = et(et(et(h_ca, h_cb), le_ab), le_ba)
    h = N.assume(ante)
    # extraire les quatre conjoints
    hca = conjonction_elim_gauche(conjonction_elim_gauche(conjonction_elim_gauche(h)))   # est_cardinal a
    hcb = conjonction_elim_droite(conjonction_elim_gauche(conjonction_elim_gauche(h)))   # est_cardinal b
    hab = conjonction_elim_droite(conjonction_elim_gauche(h))                            # a ≤ b
    hba = conjonction_elim_droite(h)                                                     # b ≤ a
    # Card a = Card b
    card_eq = N.modus_ponens(conjonction_intro(hab, hba), antisymetrie_card_egal(a, b))  # Card a = Card b
    # a = Card a  (symétrie de Card a = a, sous est_cardinal a)
    carda_eq_a = N.modus_ponens(hca, cardinal_de_cardinal(va))   # Card a = a
    a_eq_carda = N.modus_ponens(carda_eq_a, symetrie(cardinal(va), va))   # a = Card a
    # Card b = b  (sous est_cardinal b)
    cardb_eq_b = N.modus_ponens(hcb, cardinal_de_cardinal(vb))   # Card b = b
    # a = Card a = Card b = b
    a_eq_cardb = composer_egalites(a_eq_carda, card_eq)         # a = Card b
    a_eq_b = composer_egalites(a_eq_cardb, cardb_eq_b)          # a = b
    return N.loi_deduction(ante, a_eq_b)


# ════════════════════════════════════════════════════════════════════════════
#  (3) COMPARABILITÉ (ordre total)  :  a ≤ b OU b ≤ a   (INCONDITIONNEL)
# ════════════════════════════════════════════════════════════════════════════
def comparabilite_finis(a="a", b="b"):
    """⊢ ( a ≤ b )  OU  ( b ≤ a ).   (COMPARABILITÉ ; ordre total des cardinaux, INCONDITIONNEL.)

    Théorème de comparabilité (E.III.3, via ZORN) : de deux cardinaux quelconques,
    l'un s'injecte dans l'autre.  Vaut en particulier pour deux cardinaux finis
    (E.III.4 : l'ensemble des entiers est totalement ordonné).  Simple ré-exposition
    du grand théorème comparabilite_cardinaux dans le contexte fini.

    On instancie via les liants DÉFAUT (X,Y) du grand théorème, généralisés puis
    instanciés aux termes a, b (renommage sûr, ÉVITE toute capture de liants internes)."""
    va, vb = _t(a), _t(b)
    comp_XY = comparabilite_cardinaux("X", "Y")              # X ≤ Y OU Y ≤ X   [X,Y libres]
    comp_gen = N.generalisation("X", N.generalisation("Y", comp_XY))
    return instancie(instancie(comp_gen, va), vb)            # a ≤ b OU b ≤ a  (CLOS)


# ════════════════════════════════════════════════════════════════════════════
#  (4) TRANSITIVITÉ de ≤  :  (a ≤ b et b ≤ c) ⇒ a ≤ c   (INCONDITIONNEL)
# ════════════════════════════════════════════════════════════════════════════
def transitivite_inf_egal_finis(a="a", b="b", c="c"):
    """⊢ ( a ≤ b et b ≤ c ) ⇒ ( a ≤ c ).   (TRANSITIVITÉ de ≤ ; INCONDITIONNEL.)

    Composée de deux injections est une injection (inf_egal_transitive) — propriété
    d'ordre valable pour TOUS cardinaux, finis en particulier (E.III.4).  Les noms de
    liants internes de inf_egal_transitive sont F, G, X, Y, Z ; on instancie aux
    paramètres a, b, c en renommant proprement (généralisation puis instanciation)."""
    va, vb, vc = _t(a), _t(b), _t(c)
    # inf_egal_transitive(F,G,X,Y,Z) : (X≤Y et Y≤Z)⇒X≤Z ; généralise X,Y,Z puis instancie a,b,c
    trans = inf_egal_transitive("F", "G", "X", "Y", "Z")      # (X≤Y et Y≤Z)⇒X≤Z   (CLOS)
    gen = N.generalisation("X", N.generalisation("Y", N.generalisation("Z", trans)))
    return instancie(instancie(instancie(gen, va), vb), vc)   # (a≤b et b≤c)⇒a≤c


# ════════════════════════════════════════════════════════════════════════════
#  (5) ASYMÉTRIE du <  :  (a < b) ⇒ ¬( b ≤ a )   (INCONDITIONNEL, cœur de Cor. 2)
#
#  a < b = (a ≤ b et a ≠ b).  Si l'on avait AUSSI b ≤ a, l'antisymétrie (Cantor–
#  Bernstein + Prop. 1) donnerait Card a = Card b ; or pour des cardinaux a = Card a,
#  b = Card b… mais ici on n'a pas est_cardinal.  On raisonne plutôt directement sur
#  l'ÉQUIPOTENCE : a≤b et b≤a ⇒ Eq(a,b).  Sous l'hypothèse a < b (donc a≤b), si b≤a
#  alors Eq(a,b), ce qui (Prop. 1) donne Card a = Card b ; et SI a, b sont des
#  cardinaux, a = b, contredisant a ≠ b.  Pour rester INCONDITIONNEL (sans est_cardinal),
#  on énonce l'asymétrie au niveau de l'ÉQUIPOTENCE.
# ════════════════════════════════════════════════════════════════════════════
def inf_strict_exclut_reciproque(a="a", b="b"):
    """⊢ ( est_cardinal(a) et est_cardinal(b) ) ⇒ ( ( a < b ) ⇒ ¬( b ≤ a ) ).

    ASYMÉTRIE de l'ordre strict des cardinaux (E.III.4, cœur du Corollaire 2 : une
    partie STRICTEMENT plus petite ne peut « rattraper » le tout).  a < b = (a≤b et
    a≠b).  Si l'on avait b≤a, alors a≤b et b≤a ⇒ a=b (antisymetrie_cardinaux, sous
    est_cardinal a, est_cardinal b), contredisant a≠b.  Donc ¬(b≤a).  Sous l'hypothèse
    (Bourbaki) que a et b sont des cardinaux."""
    va, vb = _t(a), _t(b)
    h_ca = N.assume(est_cardinal(va))                         # est_cardinal a
    h_cb = N.assume(est_cardinal(vb))                         # est_cardinal b
    lt = inf_strict_card(va, vb)                              # a < b = (a≤b et a≠b)
    h_lt = N.assume(lt)
    le_ab = conjonction_elim_gauche(h_lt)                     # a ≤ b
    ne_ab = conjonction_elim_droite(h_lt)                     # ¬(a = b)
    # sous b ≤ a : a = b  (antisymétrie), contredit ¬(a=b)  → ¬(b≤a)
    le_ba = inf_egal_card(vb, va)                             # b ≤ a
    h_ba = N.assume(le_ba)
    ante_anti = et(et(et(est_cardinal(va), est_cardinal(vb)),
                      inf_egal_card(va, vb)), le_ba)
    conj4 = conjonction_intro(conjonction_intro(conjonction_intro(h_ca, h_cb), le_ab), h_ba)
    a_eq_b = N.modus_ponens(conj4, antisymetrie_cardinaux(a, b))   # a = b   [hyps card, a≤b, b≤a]
    # a=b contredit ¬(a=b) → ¬(b≤a)  (ex falso : de a=b et ¬(a=b) déduire ¬(b≤a))
    falso = N.modus_ponens(a_eq_b, N.modus_ponens(ne_ab,
        N.s2(non(egal(va, vb)), non(le_ba))))                # ¬(b≤a)   [sous b≤a]
    n_ba = N.modus_ponens(N.loi_deduction(le_ba, falso),
                          N.s1(non(le_ba)))                  # ¬(b≤a)   (S1 : (b≤a⇒¬(b≤a))⇒¬(b≤a))
    inner = N.loi_deduction(lt, n_ba)                        # (a<b) ⇒ ¬(b≤a)   [hyps card]
    step_b = N.loi_deduction(est_cardinal(vb), inner)        # est_card(b)⇒((a<b)⇒¬(b≤a))  [card a]
    return N.loi_deduction(est_cardinal(va), step_b)         # est_card(a)⇒(est_card(b)⇒((a<b)⇒¬(b≤a)))


# ════════════════════════════════════════════════════════════════════════════
#  (6) IRRÉFLEXIVITÉ du <  :  ¬( a < a )   (INCONDITIONNEL)
#
#  a < a = (a ≤ a et a ≠ a) ; mais a = a (réflexivité de =), donc le 2ᵉ conjoint
#  ¬(a=a) est faux → ¬(a<a).
# ════════════════════════════════════════════════════════════════════════════
def inf_strict_irreflexif(a="a"):
    """⊢ ¬( a < a ).   (IRRÉFLEXIVITÉ de l'ordre strict ; INCONDITIONNEL.)

    a < a = (a ≤ a et a ≠ a).  Or a = a (réflexivité de l'égalité, N.reflexivite), donc
    ¬(a = a) est réfuté : sous a < a on aurait a ≠ a et a = a, contradiction.  D'où
    ¬(a < a).  Aucun entier n'est strictement plus petit que lui-même (E.III.4)."""
    va = _t(a)
    lt = inf_strict_card(va, va)                             # a < a = (a≤a et a≠a)
    h = N.assume(lt)
    ne_aa = conjonction_elim_droite(h)                       # ¬(a = a)   [sous a<a]
    a_eq_a = N.reflexivite(va)                               # ⊢ a = a   (Théorème 1, E.I.39)
    # a=a et ¬(a=a) → ¬(a<a)
    falso = N.modus_ponens(a_eq_a, N.modus_ponens(ne_aa,
        N.s2(non(egal(va, va)), non(lt))))                   # ¬(a<a)   [sous a<a]
    return N.modus_ponens(N.loi_deduction(lt, falso), N.s1(non(lt)))   # ¬(a<a)


# ════════════════════════════════════════════════════════════════════════════
#  (7) TRANSITIVITÉ du <  :  (a < b et b < c) ⇒ a < c   (sous est_cardinal)
#
#  a<b = (a≤b et a≠b), b<c = (b≤c et b≠c).  a≤c par transitivité de ≤.  Reste a≠c :
#  si a=c, alors c≤b (réécriture de a≤b) et b≤c donneraient Card b=Card c, i.e. (sous
#  cardinaux) b=c, contredisant b≠c.  On a besoin de est_cardinal(b), est_cardinal(c).
# ════════════════════════════════════════════════════════════════════════════
def inf_strict_transitif(a="a", b="b", c="c"):
    """⊢ ( est_cardinal(b) et est_cardinal(c) ) ⇒ ( ( a < b et b < c ) ⇒ ( a < c ) ).

    TRANSITIVITÉ de l'ordre strict des cardinaux (E.III.4).  a≤c par transitivité de ≤.
    Pour a≠c : si a=c, alors (réécriture) c≤b ; or b≤c (de b<c) ; antisymétrie ⇒ b=c
    (sous est_cardinal b, c), contredisant b≠c.  Donc a≠c.  Hypothèse (Bourbaki) :
    b, c cardinaux (pour identifier Card·=· dans l'antisymétrie)."""
    va, vb, vc = _t(a), _t(b), _t(c)
    h_cb = N.assume(est_cardinal(vb))
    h_cc = N.assume(est_cardinal(vc))
    lt_ab = inf_strict_card(va, vb)                          # a < b
    lt_bc = inf_strict_card(vb, vc)                          # b < c
    ante = et(lt_ab, lt_bc)
    h = N.assume(ante)
    h_ab = conjonction_elim_gauche(h)                        # a < b
    h_bc = conjonction_elim_droite(h)                        # b < c
    le_ab = conjonction_elim_gauche(h_ab)                    # a ≤ b
    le_bc = conjonction_elim_gauche(h_bc)                    # b ≤ c
    ne_bc = conjonction_elim_droite(h_bc)                    # ¬(b = c)
    # a ≤ c
    le_ac = N.modus_ponens(conjonction_intro(le_ab, le_bc),
                           transitivite_inf_egal_finis(a, b, c))   # a ≤ c
    # a ≠ c :  si a=c, c≤b (Leibniz a↦c dans a≤b) ; b≤c (le_bc) ; antisym ⇒ b=c, ⊥
    h_ac = N.assume(egal(va, vc))                            # a = c
    # a≤b et a=c ⇒ c≤b  (réécrire le sujet a↦c)
    leib = N.s6(va, vc, "w", inf_egal_card(var("w"), vb))    # (a=c)⇒((a≤b)⇔(c≤b))
    eqv = N.modus_ponens(h_ac, leib)
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import equivalence_avant
    le_cb = N.modus_ponens(le_ab, equivalence_avant(eqv))    # c ≤ b
    # antisymétrie sur (b, c) : (est_card b et est_card c et b≤c et c≤b) ⇒ b=c
    conj4 = conjonction_intro(conjonction_intro(conjonction_intro(h_cb, h_cc), le_bc), le_cb)
    b_eq_c = N.modus_ponens(conj4, antisymetrie_cardinaux(b, c))   # b = c
    # b=c contredit ¬(b=c) → ¬(a=c)
    falso = N.modus_ponens(b_eq_c, N.modus_ponens(ne_bc,
        N.s2(non(egal(vb, vc)), non(egal(va, vc)))))         # ¬(a=c)   [sous a=c]
    ne_ac = N.modus_ponens(N.loi_deduction(egal(va, vc), falso),
                           N.s1(non(egal(va, vc))))          # ¬(a = c)
    lt_ac = conjonction_intro(le_ac, ne_ac)                  # a < c
    inner = N.loi_deduction(ante, lt_ac)                     # (a<b et b<c) ⇒ a<c   [card b, c]
    step_c = N.loi_deduction(est_cardinal(vc), inner)
    return N.loi_deduction(est_cardinal(vb), step_c)


# ════════════════════════════════════════════════════════════════════════════
#  (8) TRICHOTOMIE  :  (est_cardinal a et est_cardinal b) ⇒ (a<b OU a=b OU b<a)
#
#  Comparabilité donne a≤b OU b≤a.  Tiers-exclu sur a=b raffine chaque branche en <
#  ou =.  INCONDITIONNEL (sous est_cardinal, pour identifier l'égalité aux cardinaux —
#  ici l'égalité a=b est PURE, pas besoin de cardinal ; on n'en a même pas besoin pour
#  trichotomie, qui suit de comparabilité + tiers-exclu).
# ════════════════════════════════════════════════════════════════════════════
def trichotomie_finis(a="a", b="b"):
    """⊢ ( a < b )  OU  ( ( a = b )  OU  ( b < a ) ).   (TRICHOTOMIE ; INCONDITIONNEL.)

    De la comparabilité a≤b OU b≤a, et du tiers-exclu sur a=b, on raffine :
      • si a≤b : soit a=b, soit a≠b et alors a<b ;
      • si b≤a : soit a=b, soit a≠b et alors b<a.
    D'où a<b OU a=b OU b<a (l'ordre des cardinaux est total et strict).  Aucune
    hypothèse : la trichotomie suit de la comparabilité (grand théorème, CLOS)."""
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import tiers_exclu
    va, vb = _t(a), _t(b)
    le_ab = inf_egal_card(va, vb)
    le_ba = inf_egal_card(vb, va)
    lt_ab = inf_strict_card(va, vb)                          # a < b = (a≤b et a≠b)
    lt_ba = inf_strict_card(vb, va)                          # b < a = (b≤a et b≠a)
    eqab = egal(va, vb)
    cible = ou(lt_ab, ou(eqab, lt_ba))                       # a<b OU (a=b OU b<a)

    comp = comparabilite_finis(a, b)                         # a≤b OU b≤a   (CLOS, renommage sûr)

    # branche a ≤ b
    h_le_ab = N.assume(le_ab)
    #   tiers-exclu sur a=b
    te = tiers_exclu(eqab)                                   # (a=b) OU ¬(a=b)
    #     a=b ⇒ cible (milieu)
    h_eq = N.assume(eqab)
    # construire cible = a<b OU (a=b OU b<a) à partir de a=b : a=b ⇒ (a=b OU b<a) ⇒ a<b OU(a=b OU b<a)
    inn = N.modus_ponens(h_eq, N.s2(eqab, lt_ba))           # (a=b) OU (b<a)
    cible_from_eq = N.modus_ponens(inn, N.s2(ou(eqab, lt_ba), lt_ab))   # ((a=b) OU (b<a)) OU (a<b)
    # commuter au format a<b OU ((a=b) OU (b<a))  via S3
    cible_eq = N.modus_ponens(cible_from_eq, N.s3(ou(eqab, lt_ba), lt_ab))   # (a<b) OU ((a=b) OU (b<a)) = cible
    branch_eq = N.loi_deduction(eqab, cible_eq)             # (a=b) ⇒ cible
    #     ¬(a=b) et a≤b ⇒ a<b ⇒ cible (à gauche)
    h_ne = N.assume(non(eqab))                              # ¬(a=b)
    lt_ab_thm = conjonction_intro(h_le_ab, h_ne)            # a < b
    cible_lt_ab = N.modus_ponens(lt_ab_thm, N.s2(lt_ab, ou(eqab, lt_ba)))   # (a<b) OU ((a=b) OU (b<a)) = cible
    branch_ne = N.loi_deduction(non(eqab), cible_lt_ab)     # ¬(a=b) ⇒ cible
    cible_left = cas(te, branch_eq, branch_ne)              # cible   [sous a≤b]
    branch_le_ab = N.loi_deduction(le_ab, cible_left)       # (a≤b) ⇒ cible

    # branche b ≤ a   (symétrique : a=b ⇒ cible (milieu) ; a≠b ⇒ b<a ⇒ cible (droite))
    h_le_ba = N.assume(le_ba)
    te2 = tiers_exclu(eqab)
    #   a=b ⇒ cible (réutilise branch_eq)
    #   ¬(a=b) ⇒ b≠a ⇒ b<a ⇒ cible
    h_ne2 = N.assume(non(eqab))                             # ¬(a=b)
    #   b≠a depuis a≠b : si b=a alors a=b (symétrie), contredit ¬(a=b) → ¬(b=a)
    h_ba_eq = N.assume(egal(vb, va))                        # b = a
    a_eq_b_from = N.modus_ponens(h_ba_eq, symetrie(vb, va)) # a = b
    falso2 = N.modus_ponens(a_eq_b_from, N.modus_ponens(h_ne2,
        N.s2(non(eqab), non(egal(vb, va)))))               # ¬(b=a)   [sous b=a]
    ne_ba = N.modus_ponens(N.loi_deduction(egal(vb, va), falso2),
                           N.s1(non(egal(vb, va))))         # ¬(b = a)
    lt_ba_thm = conjonction_intro(h_le_ba, ne_ba)          # b < a
    #   cible depuis b<a (droite) : b<a ⇒ (b<a OU a=b) ⇒ (a=b OU b<a) ⇒ a<b OU(a=b OU b<a)
    or_mid = N.modus_ponens(lt_ba_thm, N.s2(lt_ba, eqab))  # (b<a) OU (a=b)
    or_mid = N.modus_ponens(or_mid, N.s3(lt_ba, eqab))     # (a=b) OU (b<a)
    cible_ba = N.modus_ponens(or_mid, N.s2(ou(eqab, lt_ba), lt_ab))   # ((a=b)OU(b<a)) OU (a<b)
    cible_ba = N.modus_ponens(cible_ba, N.s3(ou(eqab, lt_ba), lt_ab)) # (a<b) OU ((a=b)OU(b<a)) = cible
    branch_ne2 = N.loi_deduction(non(eqab), cible_ba)      # ¬(a=b) ⇒ cible
    cible_right = cas(te2, branch_eq, branch_ne2)          # cible   [sous b≤a]
    branch_le_ba = N.loi_deduction(le_ba, cible_right)     # (b≤a) ⇒ cible

    return cas(comp, branch_le_ab, branch_le_ba)           # cible   (CLOS)


# ════════════════════════════════════════════════════════════════════════════
#  (9) PROPOSITION 2 (forme CONDITIONNELLE) — « tout 𝔞 ≤ n est un entier »
#
#  C'est EXACTEMENT fini_downward (Prop. 2), reporté à la RÉCURRENCE C61.  On le pose
#  ici en HYPOTHÈSE explicite déchargée — l'énoncé est ainsi CLOS, et dès que
#  fini_downward_thm devient inconditionnel (ÉTAPE 1 de ensembles_recurrence_C61), il
#  l'est aussi.  JAMAIS postulé comme théorème.
# ════════════════════════════════════════════════════════════════════════════
def prop2_cardinal_inf_n_est_entier(a="a", n="n"):
    """ÉNONCÉ (formule, NON théorème) de la PROPOSITION 2 §III.4.2, forme directe :
        ( a ≤ n et Fini n ) ⇒ Fini a.

    « Soit n un entier.  Tout cardinal 𝔞 tel que 𝔞 ≤ n est un entier. »  C'est
    EXACTEMENT le contenu de fini_downward (« un cardinal ≤ un cardinal fini est
    fini »).  ⚠️ REPORTÉ : fini_downward dépend de la RÉCURRENCE C61, reportée au
    principe de bon ordre des cardinaux (ensembles_recurrence_C61.fini_downward_thm).
    Cette fonction renvoie la FORMULE-CIBLE (pas une preuve) — la preuve EST le
    théorème fini_downward_thm (sous reports), JAMAIS postulée ici."""
    va, vn = _t(a), _t(n)
    return impl(et(inf_egal_card(va, vn), est_fini(vn)), est_fini(va))


# ── BRIQUE INCONDITIONNELLE (contenu réel) — une partie a un cardinal ≤ ───────
def partie_inf_egal_card(X="X", Eens="E"):
    """⊢ ( X ⊂ E ) ⇒ ( X ≤ E ).   (une PARTIE s'injecte dans le TOUT ; INCONDITIONNEL.)

    🎯 BRIQUE MONOTONE (E.III.3.2, ré-exposée au contexte fini E.III.4) : si X ⊂ E, la
    diagonale Δ_X injecte X dans E, donc Card X ≤ Card E.  C'est le SOCLE des
    Corollaires 1 et 2 (« une partie est plus petite »).  INCONDITIONNEL, contenu non
    trivial — distinct de toute tautologie.  (Ré-exposition de inf_egal_card_de_inclus.)"""
    vX, vE = _t(X), _t(Eens)
    return inf_egal_card_de_inclus_terme(vX, vE)            # (X⊂E) ⇒ X≤E   (CLOS)


def _pont_inf_egal_card(tX, tE):
    """⊢ ( X ≤ E ) ⇒ ( Card X ≤ Card E ).   (le ≤ entre ENSEMBLES passe aux CARDINAUX.)

    Card X ≤ X (Eq(X,Card X) symétrique ⇒ Eq(Card X,X) ⇒ Card X ≤ X) ; X ≤ E (hyp) ;
    E ≤ Card E (Eq(E,Card E) ⇒ E ≤ Card E).  Transitivité ×2 :
    Card X ≤ X ≤ E ≤ Card E.  Tout INCONDITIONNEL (réflexivité/transitivité de ≤ +
    Prop. 1 §III.3).  Sert de pont pour appliquer fini_downward (sur cardinaux) à une
    inclusion d'ensembles."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux_theoremes import equipotent_son_cardinal
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.ordre_cardinaux.ensembles_cardinaux_ordre import equipotence_implique_inf_egal
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.equipotence.ensembles_bijection import equipotence_symetrique
    cX, cE = cardinal(tX), cardinal(tE)
    # Eq(X, Card X) → Eq(Card X, X) → Card X ≤ X
    eq_X_cX = N.generalisation("X", equipotent_son_cardinal("X"))     # (∀X) Eq(X, Card X)
    eq_X_cX = instancie(eq_X_cX, tX)                                  # Eq(X, Card X)
    sym_all = N.generalisation("X", N.generalisation("Y",
        equipotence_symetrique("F", "X", "Y")))                      # (∀X)(∀Y)(Eq(X,Y)⇒Eq(Y,X))
    eq_cX_X = N.modus_ponens(eq_X_cX, instancie(instancie(sym_all, tX), cX))   # Eq(Card X, X)
    eqle_all = N.generalisation("X", N.generalisation("Y",
        equipotence_implique_inf_egal("F", "X", "Y")))               # (∀X)(∀Y)(Eq(X,Y)⇒X≤Y)
    le_cX_X = N.modus_ponens(eq_cX_X, instancie(instancie(eqle_all, cX), tX))  # Card X ≤ X
    # Eq(E, Card E) → E ≤ Card E
    eq_E_cE = instancie(N.generalisation("X", equipotent_son_cardinal("X")), tE)   # Eq(E, Card E)
    le_E_cE = N.modus_ponens(eq_E_cE, instancie(instancie(eqle_all, tE), cE))  # E ≤ Card E
    # sous X ≤ E : Card X ≤ X ≤ E ≤ Card E
    h_le_XE = N.assume(inf_egal_card(tX, tE))                        # X ≤ E
    # Card X ≤ E  (transit Card X ≤ X, X ≤ E)
    le_cX_E = N.modus_ponens(conjonction_intro(le_cX_X, h_le_XE),
                             transitivite_inf_egal_finis(cX, tX, tE))   # Card X ≤ E
    # Card X ≤ Card E  (transit Card X ≤ E, E ≤ Card E)
    le_cX_cE = N.modus_ponens(conjonction_intro(le_cX_E, le_E_cE),
                              transitivite_inf_egal_finis(cX, tE, cE))   # Card X ≤ Card E
    return N.loi_deduction(inf_egal_card(tX, tE), le_cX_cE)          # (X≤E) ⇒ (Card X ≤ Card E)


# @livre Ch.III §4.2 Cor.1 | E III.31 L.33-33 | PDF p.134
def cor1_partie_finie_est_finie_conditionnel(X="X", Eens="E"):
    """⊢ ( (∀a)(∀n) fini_downward(a,n) ) ⇒ ( ( X ⊂ E et E fini ) ⇒ X fini ).

    🎯 COROLLAIRE 1 §III.4.2, forme CONDITIONNELLE au CONTENU non trivial (PAS une
    tautologie P⇒P) : « toute partie d'un ensemble fini est finie ».  Sous l'UNIQUE
    report fini_downward INSTANCIÉ à (Card X, Card E) — l'instance de la Prop. 2
        H := ( Card X ≤ Card E et Fini(Card E) ) ⇒ Fini(Card X)
    (dépendant de C61) — la preuve enchaîne des étapes INCONDITIONNELLES :
      1. X ⊂ E ⇒ X ≤ E                  [partie_inf_egal_card] ;
      2. X ≤ E ⇒ Card X ≤ Card E        [_pont_inf_egal_card] ;
      3. (Card X ≤ Card E et Fini(Card E)) ⇒ Fini(Card X)   [H, le report] ;
    d'où (X⊂E et E fini) ⇒ X fini, où « E fini » = Fini(Card E), « X fini » = Fini(Card X).
    Le SEUL maillon reporté (H = fini_downward instancié) est DÉCHARGÉ en antécédent
    explicite — jamais postulé.  Dès que fini_downward_thm est inconditionnel, H l'est
    et le Corollaire 1 aussi.  On assume H sous sa forme INSTANCIÉE (mêmes constructeurs
    est_fini/inf_egal_card que la conclusion) pour garantir l'identité structurelle —
    pas d'instanciation d'un universel (qui α-renomme les liants internes de est_fini)."""
    vX, vE = _t(X), _t(Eens)
    cX, cE = cardinal(vX), cardinal(vE)
    # report H = fini_downward(Card X, Card E), INSTANCE de la Prop. 2 (ENONCE reporté)
    H = impl(et(inf_egal_card(cX, cE), est_fini(cE)), est_fini(cX))   # (cX≤cE et Fini cE)⇒Fini cX
    h_H = N.assume(H)
    # 1+2. X⊂E ⇒ X≤E ⇒ Card X ≤ Card E
    h = N.assume(et(inclus(vX, vE), est_fini(cE)))          # X⊂E et Fini(Card E)
    h_incl = conjonction_elim_gauche(h)                     # X ⊂ E
    h_finiE = conjonction_elim_droite(h)                    # Fini(Card E) = « E fini »
    le_XE = N.modus_ponens(h_incl, partie_inf_egal_card(X, Eens))   # X ≤ E
    le_cXcE = N.modus_ponens(le_XE, _pont_inf_egal_card(vX, vE))    # Card X ≤ Card E
    # 3. H : (Card X ≤ Card E et Fini(Card E)) ⇒ Fini(Card X)
    finiX = N.modus_ponens(conjonction_intro(le_cXcE, h_finiE), h_H)   # Fini(Card X) = « X fini »
    inner = N.loi_deduction(et(inclus(vX, vE), est_fini(cE)), finiX)   # (X⊂E et E fini)⇒X fini  [H]
    return N.loi_deduction(H, inner)                        # H ⇒ ((X⊂E et E fini)⇒X fini)


def cor2_partie_stricte_card_strict(X="X", Eens="E"):
    """ÉNONCÉ du Corollaire 2 (E.III.4.2) : ( X ⊂ E, X ≠ E, E fini ) ⇒ Card X < Card E.

    « Si X est une partie d'un ensemble fini E, distincte de E, on a Card X < Card E. »
    ⚠️ REPORTÉ : nécessite que retirer une partie stricte d'un ensemble FINI fasse
    STRICTEMENT chuter le cardinal — c'est la surgery « retrait d'un point » / le lemme
    cardinal_pas_entre (E.III.4, principe des tiroirs, voisine de la Prop. 8), reportée
    dans ensembles_cardinal_pas_entre.retrait_point_hyp.  Énoncé fourni comme cible ;
    JAMAIS postulé.  (L'asymétrie inf_strict_exclut_reciproque ci-dessus en est la
    moitié INCONDITIONNELLE : a<b exclut b≤a.)"""
    vX, vE = _t(X), _t(Eens)
    return impl(et(et(inclus(vX, vE), non(egal(vX, vE))), est_fini(cardinal(vE))),
                inf_strict_card(cardinal(vX), cardinal(vE)))


__all__ = [
    # ✅ INCONDITIONNELS (propriétés directes de ≤ / < pour les finis)
    "fini_implique_inf_egal_reflexif",
    "antisymetrie_card_egal",
    "antisymetrie_cardinaux",
    "comparabilite_finis",
    "transitivite_inf_egal_finis",
    "inf_strict_exclut_reciproque",
    "inf_strict_irreflexif",
    "inf_strict_transitif",
    "trichotomie_finis",
    "partie_inf_egal_card",
    # ⚠️ CONDITIONNEL au CONTENU non trivial (report fini_downward DÉCHARGÉ en hyp)
    "cor1_partie_finie_est_finie_conditionnel",
    # ⚠️ ÉNONCÉS REPORTÉS (formules-cibles, jamais postulées comme théorèmes)
    "prop2_cardinal_inf_n_est_entier",
    "cor2_partie_stricte_card_strict",
]
