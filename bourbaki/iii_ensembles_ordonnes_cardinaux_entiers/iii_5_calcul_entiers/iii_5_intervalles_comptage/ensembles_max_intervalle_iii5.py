"""§III.5.3 — LE PLUS GRAND ÉLÉMENT DE L'INTERVALLE D'ENTIERS [0,n] EST n.

  🎯 `plus_grand_element_intervalle`  : { est_cardinal n } ⊢ est_plus_grand_element(≤, [0,n], n)
  🎯🎯 `max_intervalle_vaut_n`        : { est_cardinal n } ⊢ M( [0,n] ) = n
  🎯🎯 `max_intervalle_vaut_n_entier` : { est_entier n }   ⊢ M( [0,n] ) = n   ← forme du LIVRE
  ✅ `antisymetrie_ordre_sur_intervalle` : ⊢ antisymetrie_sur( ≤, [0,n] )   [CLOS, 0 hyp]

L'INSTANCE ARITHMÉTIQUE de la brique générique
`iii_1_7_plus_grand_plus_petit/ensembles_terme_plus_grand.py` (le τ-terme M(·) de
Bourbaki E III.46, note 2).  C'est la pièce qui manquait pour écrire « le plus
grand élément du domaine » dans une règle de récursion.

────────────────────────────────────────────────────────────────────────────────
POURQUOI CET ÉNONCÉ-LÀ.  [0,n] := intervalle_entiers(0,n) = { x | x cardinal et
0≤x et x≤n } (E III.37 L.22-26).  Le majorant n en est le PLUS GRAND ÉLÉMENT :
  • n ∈ [0,n]  — demande n cardinal (0≤n par zero_inf_egal_cardinal, n≤n par
    inf_egal_reflexif) ;  c'est l'UNIQUE endroit où l'hypothèse sert ;
  • n majore [0,n] — GRATUIT : c'est le 3ᵉ conjoint de la caractérisation de
    l'intervalle (`intervalle_implique_borne_sup`, CLOS), ∀-clôturé sur « x ».

L'hypothèse `est_cardinal(n)` n'est PAS un affaiblissement gratuit : sans elle
n ∉ [0,n] (l'intervalle ne contient que des cardinaux) et l'énoncé est FAUX.
Statut : CLOS MODULO `est_cardinal(n)`.

ANTISYMÉTRIE.  `antisymetrie_sur(≤,[0,n])` est DÉMONTRÉE ici, CLOSE (0 hyp) :
u,v ∈ [0,n] sont des cardinaux (`intervalle_implique_cardinal`), et l'antisymétrie
de ≤ sur les cardinaux (`inf_egal_antisymetrique_card`, CLOSE) conclut.  Le
théorème générique n'a donc PLUS QUE l'hypothèse de cardinalité à sa sortie.

────────────────────────────────────────────────────────────────────────────────
⚠️ CE QUE CE MODULE NE DIT PAS (à lire avant de recâbler `regle_factorielle`).
C63 (E III.46) applique M au domaine D(u) de la RESTRICTION f⁽ⁿ⁾ = f|[0,n[, qui
est l'intervalle SEMI-OUVERT [0,n[ = [0,n−1] en notation fermée.  Le présent
théorème donne M([0,n]) = n ; utilisé avec le domaine de f⁽ⁿ⁾ il donnera donc
M(D(f⁽ⁿ⁾)) = n−1, c'est-à-dire exactement le « f(n−1) » du livre.  Le pont
« dom(f|seg n) = [0, n−1] » N'EST PAS établi ici : c'est la pièce suivante.

⚠️ LIANTS (piège payé pendant la construction).  `inf_egal_card` lie EN INTERNE
{F, u, up, v, y, z} : les liants d'antisymétrie DOIVENT éviter « u » et « v »
(sinon `modus ponens : mineure ≠ antécédent`, capture silencieuse à l'instanciation).
D'où les liants « u1 »/« v1 ».  Le garde-fou `verifie_liants_frais` du module
générique refuse désormais explicitement ce cas.

INVARIANT : theorie_ensembles() = 22.  Noyau et subst INTOUCHÉS.  Rien postulé.

⚠️ THÉORIES AUXILIAIRES — « 1 hypothèse » ≠ « aucune prémisse libre ».  `N.axiome`
rend un théorème à hypothèses VIDES : les théories DÉDIÉES sont des prémisses
invisibles à la fois du compte d'hypothèses ET de l'invariant 22 (qui ne certifie
que `theorie_ensembles()`).  MESURÉ sur `max_intervalle_vaut_n_entier()` — les
théories effectivement sollicitées sont exactement TROIS, toutes PRÉEXISTANTES :
    Ensembles (= theorie_ensembles(), 22 ax.) ·  Intervalle-entiers (1 ax., §III.5.3)
    ·  D-Knaster-Tarski (1 ax., via Cantor–Bernstein dans l'antisymétrie).
Aucune théorie nouvelle n'est créée ici.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, et, impl, appartient,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_arriere, instancie,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_1_relations_ordre.iii_1_7_plus_grand_plus_petit.ensembles_terme_plus_grand import (
    terme_plus_grand, antisymetrie_sur, terme_plus_grand_vaut,
    cible_terme_plus_grand_vaut,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    inf_egal_card, est_cardinal,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux_theoremes import (
    inf_egal_reflexif,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.ordre_cardinaux.ensembles_cardinaux_props_restantes_ordre import (
    inf_egal_antisymetrique_card,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (
    ZERO, est_entier,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers_theoremes import (
    axiome_intervalle_entiers, theorie_intervalle_entiers,
    intervalle_implique_borne_sup, intervalle_implique_cardinal,
    fini_implique_cardinal,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_1_n_objet_existence.ensembles_N_collectivise import (
    zero_inf_egal_cardinal,
)

#: Liants FRAIS pour l'antisymétrie — « u »/« v » sont liés dans `inf_egal_card`.
LIANTS_ANTISYM = ("u1", "v1")
#: Liant du ∀ de `est_plus_grand_element`, et liant du τ de `terme_plus_grand`.
LIANT_MAJORE, LIANT_TAU = "x", "m"


def _t(t):
    return t if isinstance(t, Terme) else var(t)


def ordre_entiers(a, b):
    """≤ : l'ordre des cardinaux (E.III.3.2), celui qui définit [0,n] (E.III.5.3)."""
    return inf_egal_card(_t(a), _t(b))


def intervalle_zero(n):
    """[0, n] := intervalle_entiers(0, n)  (E.III.5.3)."""
    return E.intervalle_entiers(ZERO, _t(n))


# ── Briques génériques instanciées à des TERMES (patron ensembles_n_bien_ordonne) ──
def _membre_intervalle(b, x):
    """⊢ ( x ∈ [0,b] ) ⇔ ( (est_cardinal x et 0≤x) et x≤b )  pour des TERMES b, x."""
    ax = N.axiome(theorie_intervalle_entiers(), axiome_intervalle_entiers())
    return instancie(instancie(instancie(ax, ZERO), _t(b)), _t(x))


def _reflexivite(t):
    """⊢ t ≤ t  (inf_egal_reflexif généralisé-instancié ; inconditionnel)."""
    return instancie(N.generalisation("X", inf_egal_reflexif("X")), _t(t))


def _zero_minore(t):
    """⊢ est_cardinal t ⇒ 0 ≤ t  pour un TERME t."""
    base = zero_inf_egal_cardinal("zlt")                      # {card zlt} ⊢ 0≤zlt
    imp = N.loi_deduction(est_cardinal(var("zlt")), base)
    return instancie(N.generalisation("zlt", imp), _t(t))


def _projection_intervalle(theoreme_abc, b, x):
    """Généralise un théorème (a,b,x) de §III.5.3 puis l'instancie en (0, b, x)."""
    g = N.generalisation("ia", N.generalisation("ib", N.generalisation("ix",
        theoreme_abc("ia", "ib", "ix"))))
    return instancie(instancie(instancie(g, ZERO), _t(b)), _t(x))


# ══════════════════════════════════════════════════════════════════════════════
#  (1) ANTISYMÉTRIE DE ≤ SUR [0,n]  —  CLOS, 0 hypothèse
# ══════════════════════════════════════════════════════════════════════════════
# @livre Ch.III §5.3 Rem.- | E III.37 L.22-26 | PDF p.140  (« Tout ensemble d'entiers, étant un ensemble de cardinaux, est bien ordonné … l'ensemble des x vérifiant cette relation … que l'on peut donc noter [0, a] » — c'est parce que [0,a] est un ensemble de CARDINAUX que l'antisymétrie de ≤ y vaut)
def antisymetrie_ordre_sur_intervalle(n="n", u=LIANTS_ANTISYM[0], v=LIANTS_ANTISYM[1]):
    """✅ ⊢ antisymetrie_sur( ≤ , [0,n] ).                          [CLOS, 0 hyp]

    (∀u)(∀v)( ((u∈[0,n] et v∈[0,n]) et (u≤v et v≤u)) ⇒ u=v ).

    Les éléments de [0,n] sont des CARDINAUX (`intervalle_implique_cardinal`), et
    ≤ est antisymétrique sur les cardinaux (`inf_egal_antisymetrique_card`, CLOSE,
    via Cantor–Bernstein).  Aucune hypothèse ne subsiste : la cardinalité de u et
    de v est LUE dans l'appartenance à l'intervalle, pas supposée."""
    vn, vu, vv = _t(n), var(u), var(v)
    A = intervalle_zero(vn)
    antecedent = et(et(appartient(vu, A), appartient(vv, A)),
                    et(ordre_entiers(vu, vv), ordre_entiers(vv, vu)))
    H = N.assume(antecedent)
    u_in = conjonction_elim_gauche(conjonction_elim_gauche(H))    # u ∈ [0,n]
    v_in = conjonction_elim_droite(conjonction_elim_gauche(H))    # v ∈ [0,n]
    le_uv = conjonction_elim_gauche(conjonction_elim_droite(H))   # u ≤ v
    le_vu = conjonction_elim_droite(conjonction_elim_droite(H))   # v ≤ u
    card_u = N.modus_ponens(u_in, _projection_intervalle(intervalle_implique_cardinal, vn, vu))
    card_v = N.modus_ponens(v_in, _projection_intervalle(intervalle_implique_cardinal, vn, vv))
    anti = instancie(instancie(inf_egal_antisymetrique_card(), vu), vv)
    premisse = conjonction_intro(
        conjonction_intro(conjonction_intro(le_uv, le_vu), card_u), card_v)
    res = N.generalisation(u, N.generalisation(
        v, N.loi_deduction(antecedent, N.modus_ponens(premisse, anti))))
    assert res.conclusion == antisymetrie_sur(ordre_entiers, A, u, v), \
        "antisymetrie_ordre_sur_intervalle : conclusion ≠ antisymetrie_sur(≤,[0,n])"
    assert res.est_clos, "antisymetrie_ordre_sur_intervalle : hypothèses résiduelles"
    return res


# ══════════════════════════════════════════════════════════════════════════════
#  (2) n EST LE PLUS GRAND ÉLÉMENT DE [0,n]
# ══════════════════════════════════════════════════════════════════════════════
def cible_plus_grand_intervalle(n="n", x=LIANT_MAJORE):
    """ÉNONCÉ-cible (test miroir) :  est_plus_grand_element( ≤ , [0,n] , n )."""
    vn = _t(n)
    return E.est_plus_grand_element(ordre_entiers, intervalle_zero(vn), vn, x)


# @livre Ch.III §1.7 Def.4 | E III.8 L.26-27 | PDF p.111   (L.30-32 était FAUX, recompté le 27 juil.)
# @livre Ch.III §5.3 Rem.- | E III.37 L.22-26 | PDF p.140  (l'intervalle [0,a] des entiers x ⩽ a : son majorant a lui appartient, donc en est le plus grand élément)
def plus_grand_element_intervalle(n="n", x=LIANT_MAJORE):
    """🎯 { est_cardinal n } ⊢ est_plus_grand_element( ≤ , [0,n] , n ).   [1 hyp]

    « n est le plus grand élément de l'intervalle d'entiers [0,n]. »

      • n ∈ [0,n] : n est un cardinal (hypothèse), 0≤n (zero_inf_egal_cardinal) et
        n≤n (inf_egal_reflexif) ; le sens ⇐ de la caractérisation de [0,n] conclut.
      • n majore [0,n] : `intervalle_implique_borne_sup` est CLOS, on le ∀-clôture
        sur le liant « x » imposé par `est_plus_grand_element`.

    HONNÊTETÉ : la conclusion n'est pas parmi les hypothèses ; l'unique hypothèse
    `est_cardinal(n)` est NÉCESSAIRE (sans elle n ∉ [0,n])."""
    vn = _t(n)
    card_n = N.assume(est_cardinal(vn))
    corps = conjonction_intro(
        conjonction_intro(card_n, N.modus_ponens(card_n, _zero_minore(vn))),
        _reflexivite(vn))                                    # ((card n et 0≤n) et n≤n)
    n_dedans = N.modus_ponens(corps, equivalence_arriere(_membre_intervalle(vn, vn)))
    n_majore = N.generalisation(
        x, _projection_intervalle(intervalle_implique_borne_sup, vn, var(x)))
    res = conjonction_intro(n_dedans, n_majore)
    assert res.conclusion == cible_plus_grand_intervalle(vn, x), \
        "plus_grand_element_intervalle : conclusion ≠ est_plus_grand_element(≤,[0,n],n)"
    assert res.hypotheses == frozenset({est_cardinal(vn)}), \
        "plus_grand_element_intervalle : hypothèses ≠ { est_cardinal(n) }"
    return res


# ══════════════════════════════════════════════════════════════════════════════
#  (3) 🎯🎯 LE CAPSTONE :  M( [0,n] ) = n
# ══════════════════════════════════════════════════════════════════════════════
def cible_max_intervalle(n="n"):
    """ÉNONCÉ-cible (test miroir) :  M( [0,n] ) = n."""
    vn = _t(n)
    return cible_terme_plus_grand_vaut(ordre_entiers, intervalle_zero(vn), vn,
                                       LIANT_TAU, LIANT_MAJORE)


def terme_max_intervalle(n="n"):
    """Le TERME  M([0,n]) := τ_m( m est le plus grand élément de [0,n] )."""
    return terme_plus_grand(ordre_entiers, intervalle_zero(_t(n)),
                            LIANT_TAU, LIANT_MAJORE)


# @livre Ch.III §6.2 Demo.C63 | E III.46 L.28-29 | PDF p.149  (« Soit M(u) la borne supérieure de D(u) dans N » — l'instance de M sur un intervalle d'entiers, seul cas dont C63 se sert ; citation FINE dans le L.25-33 déjà posé par ensembles_recursion_hygienic)
def max_intervalle_vaut_n(n="n"):
    """🎯🎯 { est_cardinal n } ⊢ M( [0,n] ) = n.                       [1 hyp]

    LE TERME « plus grand élément de [0,n] » DÉNOTE n.  Assemblage :
      • `terme_plus_grand_vaut` (générique, §III.1.7) : 2 hypothèses ;
      • l'antisymétrie sur [0,n] est DÉCHARGÉE par `antisymetrie_ordre_sur_intervalle`
        (CLOSE) ;
      • « n plus grand élément » est DÉCHARGÉE par `plus_grand_element_intervalle`,
        qui ne laisse que `est_cardinal(n)`.
    Reste donc exactement { est_cardinal n } — statut : CLOS MODULO est_cardinal(n).

    ⚠️ NE PAS lire « M(D u) est enfin disponible pour `regle_factorielle` » : il
    manque encore le pont dom(f|seg n) = [0,n−1] (cf. en-tête du module)."""
    vn = _t(n)
    A = intervalle_zero(vn)
    generique = terme_plus_grand_vaut(ordre_entiers, A, vn, LIANT_TAU, LIANT_MAJORE,
                                      *LIANTS_ANTISYM)
    sans_antisym = N.modus_ponens(
        antisymetrie_ordre_sur_intervalle(vn, *LIANTS_ANTISYM),
        N.loi_deduction(antisymetrie_sur(ordre_entiers, A, *LIANTS_ANTISYM), generique))
    res = N.modus_ponens(
        plus_grand_element_intervalle(vn, LIANT_MAJORE),
        N.loi_deduction(cible_plus_grand_intervalle(vn, LIANT_MAJORE), sans_antisym))
    assert res.conclusion == cible_max_intervalle(vn), \
        "max_intervalle_vaut_n : conclusion ≠ M([0,n]) = n"
    assert res.hypotheses == frozenset({est_cardinal(vn)}), \
        "max_intervalle_vaut_n : hypothèses ≠ { est_cardinal(n) }"
    return res


# ══════════════════════════════════════════════════════════════════════════════
#  (4) COROLLAIRE À L'HYPOTHÈSE DU LIVRE : « n ENTIER » (et non « n cardinal »)
# ══════════════════════════════════════════════════════════════════════════════
# @livre Ch.III §5.3 Rem.- | E III.37 L.22-26 | PDF p.140  (« pour tout entier a … l'ensemble des x vérifiant cette relation … que l'on peut donc noter [0, a] » — l'hypothèse du livre est « a ENTIER », c'est celle-ci)
def max_intervalle_vaut_n_entier(n="n"):
    """🎯 { est_entier n } ⊢ M( [0,n] ) = n.                           [1 hyp]

    LA FORME DU LIVRE.  Bourbaki écrit « pour tout ENTIER a » (E III.37 L.22-26),
    pas « pour tout cardinal » ; un entier EST un cardinal fini (E.III.4.1, Déf. 1),
    et `fini_implique_cardinal` (CLOS) fait le pont.  C'est la forme directement
    consommable en aval : un indice de récursion arrive sous « n entier », jamais
    sous « n cardinal ».

    Aucune hypothèse gratuite : `est_entier(n)` = `est_fini(n)` est STRICTEMENT
    plus forte que `est_cardinal(n)`, mais c'est celle du livre et celle dont
    disposent les appelants.  La forme faible reste disponible
    (`max_intervalle_vaut_n`) pour qui n'a que la cardinalité."""
    vn = _t(n)
    faible = max_intervalle_vaut_n(vn)                   # { card n } ⊢ M([0,n]) = n
    pont = instancie(N.generalisation("afic", fini_implique_cardinal("afic")), vn)
    res = N.modus_ponens(N.modus_ponens(N.assume(est_entier(vn)), pont),
                         N.loi_deduction(est_cardinal(vn), faible))
    assert res.conclusion == cible_max_intervalle(vn), \
        "max_intervalle_vaut_n_entier : conclusion ≠ M([0,n]) = n"
    assert res.hypotheses == frozenset({est_entier(vn)}), \
        "max_intervalle_vaut_n_entier : hypothèses ≠ { est_entier(n) }"
    return res


__all__ = ["LIANTS_ANTISYM", "LIANT_MAJORE", "LIANT_TAU",
           "ordre_entiers", "intervalle_zero",
           "antisymetrie_ordre_sur_intervalle",
           "cible_plus_grand_intervalle", "plus_grand_element_intervalle",
           "cible_max_intervalle", "terme_max_intervalle", "max_intervalle_vaut_n",
           "max_intervalle_vaut_n_entier"]
