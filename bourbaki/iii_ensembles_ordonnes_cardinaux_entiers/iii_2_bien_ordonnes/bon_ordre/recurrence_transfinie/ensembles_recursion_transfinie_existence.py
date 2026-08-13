"""§III.2 — DÉFINITION PAR RÉCURRENCE TRANSFINIE (Critère C60) : la moitié EXISTENCE.

Suite directe de `ensembles_recurrence_transfinie` (C59 induction transfinie CLOS +
C60 UNICITÉ sous 2 hypothèses honnêtes).  Ici on attaque la moitié DURE de C60 :
l'EXISTENCE d'une solution de l'équation de récursion.

────────────────────────────────────────────────────────────────────────────────
LE CADRE (faithful à Bourbaki E.III.2, Critère C60).

Soit (E,R) bien ordonné et une « RÈGLE » h qui, à chaque x∈E et à chaque fonction
partielle p définie sur le segment seg(R,E,x), associe une valeur h(x,p).  C60
affirme l'existence d'une UNIQUE fonction f sur E vérifiant l'ÉQUATION DE RÉCURSION

        (∀x∈E)  f(x) = h( x, f|seg(R,E,x) ).

Construction classique : f = ⋃ des fonctions partielles « essais » sur les segments
initiaux ; chaque essai est unique (C60-unicité), les essais COÏNCIDENT sur les
recouvrements (⇐ C60-unicité), donc leur réunion est FONCTIONNELLE, et tout x∈E est
couvert (⇐ C59-induction).

────────────────────────────────────────────────────────────────────────────────
REPRÉSENTATION CHOISIE (méta-théorème, motif C59/C60-unicité).

On représente :
  • la RÈGLE par une fonction Python `vh : (Terme x) → (Terme)` qui, appliquée à un
    point x, RÉIFIE la valeur-règle h(x, ·) sous forme d'un terme `vh(x)` dépendant
    (symboliquement, via la fonction-valeur ambiante) de la solution.  Plus
    précisément, on travaille au niveau des FONCTIONS-VALEUR  vf : Terme→Terme  (où
    vf(x) = la valeur de la candidate f en x, p.ex. E.valeur(graphe_de(f),x)), comme
    dans recursion_transfinie_unicite.
  • une « SOLUTION (de la règle vh sur E) » par le prédicat
        est_solution(vf, vh, R, E) :=
            (∀x)( x∈E ⇒ vf(x) = vh(x) )                       [équation de récursion]
    où vh(x) est la valeur-règle (qui, sémantiquement, ne dépend de la solution que
    via sa restriction au segment seg(R,E,x) — c'est la LOCALITÉ de la règle).

  • la LOCALITÉ de la règle (que h(x,·) ne lit la solution que sur seg(R,E,x)) est
    capturée par l'hypothèse honnête `regle_locale` : si deux fonctions-valeur
    coïncident sur seg(R,E,x), leurs valeurs-règle en x sont égales :
        (∀x)( x∈E ⇒ ( (∀y)(y∈seg(R,E,x) ⇒ vf(y)=vg(y)) ⇒ vh_f(x)=vh_g(x) ) ).

CE QUI EST CLOS ICI (sous hypothèses HONNÊTES, jamais postulées, theorie=22) :

  (a) COHÉRENCE DES SOLUTIONS — `solutions_coincident` :
        deux solutions de la MÊME règle locale sur E coïncident PONCTUELLEMENT.
        DÉRIVÉ : les deux équations de récursion + la localité ⇒ l'hypothèse
        `regle_coherente_sur_segments` de C60-unicité, puis C60-unicité (⇐ C59).

  (b) FONCTIONNALITÉ DE LA RÉUNION DE DEUX ESSAIS — `reunion_essais_fonctionnelle` :
        si deux graphes-essais G, H sont fonctionnels et leurs domaines DISJOINTS,
        leur réunion G∪H est fonctionnelle (⇐ reunion_graphes_fonctionnelle, infra
        recollement).  [brique de la réunion-des-essais]

LA FRONTIÈRE (REPORTÉE, honnêtement) — voir le rapport en bas du fichier et le test :
  (c) COUVERTURE : « tout x∈E appartient au domaine d'un essai » par C59-induction —
      nécessite de CONSTRUIRE, pour chaque x, l'essai sur seg(R,E,x+) (extension d'un
      pas), ce qui exige la collectivisation de l'ensemble des essais (S8 sur 𝔓(E×V))
      et le recollement d'une FAMILLE (non binaire) de graphes — gros chantier.
  (d) ÉQUATION pour la réunion f=⋃essais : f(x)=h(x,f|seg) — nécessite (c) + le
      transfert de valeur le long de la réunion d'une famille.

INVARIANT : theorie_ensembles() = 22 intangible.  Tout est DÉRIVÉ ; rien n'est
postulé.  Les hypothèses (équations de récursion, localité, disjonction) sont
HONNÊTES et déchargées par loi_deduction — ce sont les données mêmes du Critère C60.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, et, non, impl, appartient, pourtout,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E

from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    instancie, equivalence_avant, equivalence_arriere,
)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
    symetrie, composer_egalites,
)

from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_recurrence_transfinie import (
    heredite_transfinie, conclusion_transfinie,
    regle_coherente_sur_segments, coincidence_solutions,
    recursion_transfinie_unicite, recurrence_transfinie_preuve,
    _graphe_R, _P_egal_valeurs,
)


def _t(t):
    """Coercion str/Terme → Terme."""
    return t if isinstance(t, Terme) else var(t)


# ════════════════════════════════════════════════════════════════════════════
#  ÉNONCÉS — équation de récursion C60 + localité de la règle.
# ════════════════════════════════════════════════════════════════════════════
def equation_recursion(vf, vh, e, x="x"):
    """L'ÉQUATION DE RÉCURSION C60 pour la solution vf et la règle-valeur vh :

        (∀x)( x∈E ⇒ vf(x) = vh(x) ).

    « vf est une solution de la règle vh sur E » : en tout point x de E, la valeur
    de la candidate coïncide avec la valeur-règle vh(x) = h(x, vf|seg(R,E,x)).
    vf, vh : fonctions Python Terme→Terme."""
    vx = var(x)
    return pourtout(x, impl(appartient(vx, _t(e)), egal(vf(vx), vh(vx))))


def regle_locale(vf, vg, vhf, vhg, G, e, x="x", y="y"):
    """LOCALITÉ de la règle (la règle ne lit la solution que sur le segment) :

        (∀x)( x∈E ⇒ ( (∀y)(y∈seg(R,E,x) ⇒ vf(y)=vg(y))  ⇒  vhf(x)=vhg(x) ) ).

    « Si deux candidates vf, vg coïncident sur seg(R,E,x), alors la même règle h(x,·),
    qui ne lit la candidate que via sa restriction au segment, rend la même valeur :
    vhf(x)=vhg(x). »  C'est la traduction fidèle de « h(x,p) ne dépend de p que par sa
    restriction à seg(R,E,x) ».  HYPOTHÈSE HONNÊTE (la donnée même de C60).

    vhf = valeur-règle évaluée le long de vf ; vhg = idem le long de vg."""
    P = _P_egal_valeurs(vf, vg)                 # P[y] := vf(y)=vg(y)
    vx = var(x)
    seg_x = E.segment_extremite(_t(G), _t(e), vx)
    devant = pourtout(y, impl(appartient(var(y), seg_x), P(var(y))))
    return pourtout(x, impl(appartient(vx, _t(e)),
                            impl(devant, egal(vhf(vx), vhg(vx)))))


# ════════════════════════════════════════════════════════════════════════════
#  LEMME (a) — COHÉRENCE DES SOLUTIONS  (le résultat CLOS le plus profond).
#  Deux solutions de la MÊME règle locale coïncident ponctuellement.
# ════════════════════════════════════════════════════════════════════════════
# @livre Ch.III §2.2 Demo.60 | E III.18 L.27-33 | PDF p.121  (démonstration de C60, unicité : deux solutions coïncident — f=f', U'=U)
def solutions_coincident(vf, vg, vhf, vhg, e="E", G="G", x0="x0tf", y="ytf",
                         ebind="Eax", xbind="xAax"):
    """⊢ { est_bien_ordonne(R,E),
           equation_recursion(vf, vhf, E),     [ vf solution :  vf(x)=vhf(x) ]
           equation_recursion(vg, vhg, E),     [ vg solution :  vg(x)=vhg(x) ]
           regle_locale(vf, vg, vhf, vhg, R, E) }
         ⊢ (∀x)( x∈E ⇒ vf(x)=vg(x) )                       [ COHÉRENCE / UNICITÉ C60 ].

    DÉRIVATION (le pont entre les ÉQUATIONS de récursion et C60-unicité) :
    on PROUVE l'hypothèse `regle_coherente_sur_segments(vf,vg,R,E)` de C60-unicité —
    c.-à-d. (∀x∈E)( (∀y∈seg)(vf(y)=vg(y)) ⇒ vf(x)=vg(x) ) — à partir des deux
    équations de récursion et de la localité :
        soit x∈E, et supposons vf(y)=vg(y) pour tout y∈seg(R,E,x).
        • localité ⇒ vhf(x)=vhg(x) ;
        • équation vf : vf(x)=vhf(x) ;
        • équation vg : vg(x)=vhg(x) ;
        • chaîne :  vf(x)=vhf(x)=vhg(x)=vhg... soit vf(x)=vg(x).   ✓
    puis recursion_transfinie_unicite (⇐ C59) décharge le reste.

    ⚠️ QUATRE hypothèses HONNÊTES (jamais postulées ; theorie=22), déchargées par
    loi_deduction : le bon ordre, les DEUX équations de récursion, la localité de la
    règle.  Ce sont EXACTEMENT les données du Critère C60 (deux solutions d'une même
    règle).  La conclusion (coïncidence) ∉ hypothèses (non vacuous)."""
    ve = _t(e)
    R = _graphe_R(G)
    P = _P_egal_valeurs(vf, vg)                          # P[x] := vf(x)=vg(x)

    # ── On PROUVE l'hérédité `regle_coherente_sur_segments(vf,vg,R,E)`. ──────────
    #    Soit x0, assume x0∈E, assume (∀y)(y∈seg(R,E,x0) ⇒ vf(y)=vg(y)), prouve vf(x0)=vg(x0).
    vx0 = var(x0)
    h_x0_in_E = N.assume(appartient(vx0, ve))           # x0 ∈ E

    seg_x0 = E.segment_extremite(_t(G), ve, vx0)
    devant = pourtout(y, impl(appartient(var(y), seg_x0), P(var(y))))
    h_devant = N.assume(devant)                         # (∀y)(y∈seg(R,E,x0) ⇒ vf(y)=vg(y))

    # localité instanciée à x0 :  x0∈E ⇒ ( devant ⇒ vhf(x0)=vhg(x0) )
    loc = regle_locale(vf, vg, vhf, vhg, G, ve, x0, y)
    h_loc = N.assume(loc)
    loc_x0 = instancie(h_loc, vx0)                      # x0∈E ⇒ (devant ⇒ vhf(x0)=vhg(x0))
    loc_x0_dev = N.modus_ponens(h_x0_in_E, loc_x0)      # devant ⇒ vhf(x0)=vhg(x0)
    vhf_eq_vhg = N.modus_ponens(h_devant, loc_x0_dev)   # vhf(x0)=vhg(x0)

    # équation vf instanciée à x0 :  vf(x0)=vhf(x0)
    eq_vf = equation_recursion(vf, vhf, ve, x0)
    h_eq_vf = N.assume(eq_vf)
    vf_eq_vhf = N.modus_ponens(h_x0_in_E, instancie(h_eq_vf, vx0))   # vf(x0)=vhf(x0)

    # équation vg instanciée à x0 :  vg(x0)=vhg(x0)
    eq_vg = equation_recursion(vg, vhg, ve, x0)
    h_eq_vg = N.assume(eq_vg)
    vg_eq_vhg = N.modus_ponens(h_x0_in_E, instancie(h_eq_vg, vx0))   # vg(x0)=vhg(x0)

    # chaîne :  vf(x0) = vhf(x0) = vhg(x0) = vg(x0)
    #   vf(x0)=vhf(x0)  et  vhf(x0)=vhg(x0)  ⇒  vf(x0)=vhg(x0)
    vf_eq_vhg = composer_egalites(vf_eq_vhf, vhf_eq_vhg)   # vf(x0)=vhg(x0)
    #   vg(x0)=vhg(x0)  ⇒  vhg(x0)=vg(x0)  (symétrie) ; puis vf(x0)=vhg(x0) → vf(x0)=vg(x0)
    vhg_eq_vg = N.modus_ponens(vg_eq_vhg, symetrie(vg(vx0), vhg(vx0)))   # vhg(x0)=vg(x0)
    vf_eq_vg = composer_egalites(vf_eq_vhg, vhg_eq_vg)     # vf(x0)=vg(x0)

    assert vf_eq_vg.conclusion == P(vx0), "lemme (a) : conclusion locale ≠ vf(x0)=vg(x0)"

    # ── assemblage : x0∈E ⇒ ( devant ⇒ vf(x0)=vg(x0) ), généralise (∀x0). ──────
    inner = N.loi_deduction(devant, vf_eq_vg)           # devant ⇒ vf(x0)=vg(x0)
    body = N.loi_deduction(appartient(vx0, ve), inner)  # x0∈E ⇒ (devant ⇒ vf(x0)=vg(x0))
    heredite = N.generalisation(x0, body)               # = regle_coherente_sur_segments(vf,vg,R,E)

    cible_her = regle_coherente_sur_segments(vf, vg, G, ve, x0, y)
    assert heredite.conclusion == cible_her, "hérédité prouvée ≠ regle_coherente_sur_segments"

    # ── C60-unicité (⇐ C59) : { bo, heredite } ⊢ coincidence_solutions. ─────────
    unic = recursion_transfinie_unicite(vf, vg, e, G, x0, y, ebind, xbind)  # [bo, heredite]
    W = E.est_bien_ordonne(R, ve)
    # décharge l'hypothèse `heredite` de `unic` par la preuve `heredite` ci-dessus.
    res = N.modus_ponens(heredite, N.loi_deduction(cible_her, unic))        # [bo, eqs, loc]

    cible = coincidence_solutions(vf, vg, ve, x0)
    assert res.conclusion == cible, "solutions_coincident : conclusion ≠ coincidence_solutions"
    assert res.conclusion not in res.hypotheses, "solutions_coincident : VACUOUS (concl∈hyps)"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  LEMME (b) — FONCTIONNALITÉ DE LA RÉUNION DE DEUX ESSAIS  (brique recollement).
# ════════════════════════════════════════════════════════════════════════════
def reunion_essais_fonctionnelle(g="G", h="H"):
    """{ est_fonctionnel(G), est_fonctionnel(H), (∀u)¬(u∈dom G et u∈dom H) }
        ⊢ est_fonctionnel(G∪H).

    BRIQUE de la réunion-des-essais : deux fonctions partielles (graphes-essais)
    fonctionnelles à domaines DISJOINTS se RECOLLENT en un graphe fonctionnel G∪H.
    Délègue directement à `reunion_graphes_fonctionnelle` (infra recollement R25).
    Utile pour la moitié EXISTENCE (la réunion ⋃essais est fonctionnelle car les
    essais coïncident sur les recouvrements — lemme (a) — donc, après réindexation à
    domaines disjoints, ce pivot s'applique)."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.recollement.ensembles_restriction_somme import (
        reunion_graphes_fonctionnelle,
    )
    return reunion_graphes_fonctionnelle(_t(g), _t(h))


# ════════════════════════════════════════════════════════════════════════════
#  LEMME (c) — COUVERTURE TRANSFINIE  (le squelette C59 de l'existence).
#
#  Dans la construction de Bourbaki, f = ⋃essais ; pour que f soit définie PARTOUT
#  il faut que TOUT x∈E soit COUVERT (= appartienne au domaine d'un essai vérifiant
#  l'équation de récursion).  La couverture se prouve par C59-INDUCTION : si tout
#  y<x est couvert, alors x est couvert (on prolonge l'essai d'un pas, en posant
#  f(x) = h(x, f|seg(R,E,x)) — c'est l'UNIQUE valeur possible).
#
#  CE LEMME EST LE SQUELETTE C59 de cette étape : il est PLEINEMENT GÉNÉRIQUE sur le
#  prédicat `couvert : Terme → Formule`.  C'EST une instance CLOSE du méta-théorème
#  C59 (recurrence_transfinie_preuve) appliqué à P := couvert.  La SEULE obligation
#  restante (le PROLONGEMENT D'UN PAS = l'hérédité de la couverture) est exposée
#  comme HYPOTHÈSE HONNÊTE — c'est EXACTEMENT le point dur reporté (cf. frontière).
# ════════════════════════════════════════════════════════════════════════════
def heredite_couverture(couvert, G, e, x="x", y="y"):
    """L'HÉRÉDITÉ de la couverture (= prolongement d'un pas) :

        (∀x)( x∈E ⇒ ( (∀y)(y∈seg(R,E,x) ⇒ couvert[y])  ⇒  couvert[x] ) ).

    « Si tout y<x est couvert (un essai est défini sur seg(R,E,x)), alors x est
    couvert (on prolonge l'essai en x). »  C'est `heredite_transfinie(couvert,R,E)`.
    HYPOTHÈSE HONNÊTE : son contenu EST le prolongement-d'un-pas, qui exige le
    recollement/la collectivisation des essais (point dur reporté de C60-existence)."""
    return heredite_transfinie(couvert, G, e, x, y)


def couverture_totale(couvert, e, x="x"):
    """CONCLUSION de couverture :  (∀x)( x∈E ⇒ couvert[x] )  (tout point est couvert)."""
    return conclusion_transfinie(couvert, e, x)


# @livre Ch.III §2.2 Demo.60 | E III.18 L.34-39 | PDF p.121  (démonstration de C60, existence : squelette de couverture des segments par essais)
def couverture_transfinie(couvert, e="E", G="G", x0="x0tf", y="ytf",
                          ebind="Eax", xbind="xAax"):
    """⊢ { est_bien_ordonne(R,E),  heredite_couverture(couvert,R,E) }
         ⊢ (∀x)( x∈E ⇒ couvert[x] )                       [ COUVERTURE TOTALE ].

    SQUELETTE C59 de l'EXISTENCE : si la couverture est héréditaire (prolongement
    d'un pas), alors tout point de E est couvert.  DÉRIVÉ du méta-théorème C59
    `recurrence_transfinie_preuve` appliqué à P := couvert.

    ⚠️ DEUX HYPOTHÈSES HONNÊTES (jamais postulées ; theorie=22), déchargées par
    loi_deduction :
      • est_bien_ordonne(R,E)            — (E,R) bien ordonné (donnée de C60) ;
      • heredite_couverture(couvert,…)   — le PROLONGEMENT D'UN PAS (point dur :
        construction de l'essai sur seg(R,E,x) — REPORTÉ, cf. frontière).
    La conclusion (couverture totale) ∉ hypothèses (non vacuous).

    couvert : fonction Python Terme→Formule (« x est couvert par un essai »).
    R = relation portée par le graphe G (a≤b := (a,b)∈G)."""
    ve = _t(e)
    R = _graphe_R(G)

    c59 = recurrence_transfinie_preuve(couvert, e, G, x0, y, ebind, xbind)  # W⇒(héréd⇒concl) [CLOS]

    W = E.est_bien_ordonne(R, ve)
    her = heredite_couverture(couvert, G, ve, x0, y)
    inner = N.modus_ponens(N.assume(W), c59)             # héréd ⇒ concl   [W]
    concl = N.modus_ponens(N.assume(her), inner)         # concl  [W, héréd]

    cible = couverture_totale(couvert, ve, x0)
    assert concl.conclusion == cible, "couverture_transfinie : conclusion ≠ couverture_totale"
    assert W in concl.hypotheses and her in concl.hypotheses, "hyps inattendues"
    assert len(concl.hypotheses) == 2, "hypothèses résiduelles inattendues (≠ 2)"
    assert concl.conclusion not in concl.hypotheses, "couverture_transfinie : VACUOUS"
    return concl


# ════════════════════════════════════════════════════════════════════════════
#  LEMME (d) — ÉQUATION pour la réunion (transfert de VALEUR) au niveau BINAIRE.
#
#  La réunion f=⋃essais doit, en tout point u où elle est définie par l'essai G,
#  RENDRE la valeur de cet essai : f(u)=G(u).  Au niveau BINAIRE (réunion de 2
#  essais G, H), c'est `valeur_reunion_gauche` : valeur(G∪H,u)=valeur(G,u) sur
#  dom G.  C'est le pas (d) — l'équation de la réunion hérite de celle de l'essai.
#  (La version FAMILLE — ⋃ d'une famille quelconque d'essais — est la frontière.)
# ════════════════════════════════════════════════════════════════════════════
def valeur_essai_reunion(g="G", h="H", u="u"):
    """{ est_fonctionnel(G), est_fonctionnel(H), (∀u)¬(u∈dom G et u∈dom H), u∈dom G }
        ⊢ valeur(G∪H, u) = valeur(G, u).

    TRANSFERT DE VALEUR (d) au niveau binaire : la réunion de deux essais COÏNCIDE,
    sur le domaine de G, avec G.  Donc si G(u)=h(u,G|seg) (équation de l'essai G),
    alors (G∪H)(u)=h(u,…) aussi — l'équation de récursion PASSE À LA RÉUNION.
    Délègue à `valeur_reunion_gauche` (infra recollement).  4 hyps honnêtes."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.recollement.ensembles_recollement_bijection import (
        valeur_reunion_gauche,
    )
    return valeur_reunion_gauche(_t(g), _t(h), _t(u))


__all__ = [
    # énoncés
    "equation_recursion", "regle_locale",
    # (a) cohérence des solutions (CLOS sous 4 hyps honnêtes)
    "solutions_coincident",
    # (b) fonctionnalité de la réunion de deux essais (brique recollement)
    "reunion_essais_fonctionnelle",
    # (c) couverture transfinie (squelette C59 de l'existence, 2 hyps honnêtes)
    "heredite_couverture", "couverture_totale", "couverture_transfinie",
    # (d) transfert de valeur de la réunion au niveau binaire (4 hyps honnêtes)
    "valeur_essai_reunion",
]
