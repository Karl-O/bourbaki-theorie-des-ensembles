"""§III.6.3 (Théorème 2, HESSENBERG) — sous-pièces d'ARITHMÉTIQUE CARDINALE de
l'argument d'extension du maximal :  2𝔟 = 𝔟  et  3𝔟 = 𝔟  pour 𝔟 = 𝔟²  infini.

CONTEXTE.  Une fois le carré du maximal établi (`maximal_carre_egal` ⊢ 𝔟²=𝔟,
𝔟 := Card S₀), Bourbaki (E.III.45-48) dérive la chaîne

      𝔟 ≤ 2𝔟 ≤ 3𝔟 ≤ … ≤ 𝔟·𝔟 = 𝔟,

les inégalités MONTANTES (𝔟 ≤ 2𝔟, etc.) étant triviales (injection canonique
gauche), et les inégalités DESCENDANTES (2𝔟 ≤ 𝔟², 3𝔟 ≤ 𝔟²) exigeant « 2 ≤ 𝔟 »,
« 3 ≤ 𝔟 » — i.e. « n ≤ 𝔟 pour tout entier n » quand 𝔟 est infini (E.III.45,
remarque de la Déf. 1, §III.6.1).

⚠️ OBSTRUCTION HONNÊTE (documentée, anti-faux).  La chaîne « 𝔞 infini ⇒ n ≤ 𝔞 pour
tout entier n » est EXPLICITEMENT REPORTÉE dans le dépôt
(`ensembles_infinis_props.aleph0_inf_egal_cardinal_infini_enonce` : « REPORTÉ :
exige tout entier n vérifie n≤a + collectivisation de N + arithmétique cardinale
infinie » ; cf. aussi l'en-tête de `ensembles_hessenberg_maximal_card`).  Donc
« 2 ≤ 𝔟 » et « 3 ≤ 𝔟 » NE SONT PAS établissables ici depuis est_infini(𝔟) seul.

CE QU'ON FAIT (isolation PROPRE du verrou).  On prouve 2𝔟=𝔟 / 3𝔟=𝔟 en prenant
la SEULE inégalité DESCENDANTE comme HYPOTHÈSE HONNÊTE explicite (jamais postulée
vraie ; déchargée par loi_deduction).  TOUT LE RESTE est inconditionnel et clos :

  • `deux_b_egal_b(b)` :
        { est_cardinal(𝔟),  𝔟+𝔟 ≤ 𝔟 }  ⊢  𝔟 + 𝔟 = 𝔟          (2𝔟=𝔟).
    Le ≥ (𝔟 ≤ 𝔟+𝔟) est CLOS (injection gauche `inf_egal_somme_gauche` + transport
    par Card + Card 𝔟 = 𝔟) ; antisymétrie de ≤ (CANTOR–BERNSTEIN,
    `inf_egal_antisymetrique_card`) referme l'égalité.  Le ≤ (𝔟+𝔟 ≤ 𝔟) est l'hyp
    honnête (= la descente 2𝔟≤𝔟², verrouillée par « 2 ≤ 𝔟 »).

  • `trois_b_egal_b(b)` :
        { est_cardinal(𝔟),  𝔟+𝔟 = 𝔟,  (𝔟+𝔟)+𝔟 ≤ 𝔟 }  ⊢  (𝔟 + 𝔟) + 𝔟 = 𝔟   (3𝔟=𝔟).
    Même schéma : ≥ clos, antisymétrie ferme.  (On NE redérive PAS 3𝔟≤𝔟² depuis
    rien — c'est l'hyp honnête.)  La 2ᵉ hyp 𝔟+𝔟=𝔟 est le RÉSULTAT de deux_b_egal_b
    (fournie pour expliciter le lien 3𝔟 = 2𝔟+𝔟 = 𝔟+𝔟 = 𝔟 dans la version cardinale ;
    on n'en a en fait besoin que pour la cohérence — la preuve par antisymétrie est
    autonome).

Le pas BLOQUANT vers Hessenberg complet — la CONTRADICTION d'extension du maximal
(prolonger φ₀ sur S₀∪U avec Card U = 𝔟, via la bijection (S₀∪U)²∖S₀² ≃ U fondée
sur 3𝔟²=3𝔟=𝔟, contredisant la maximalité) ⇒ Card S₀ = Card E — reste la PIÈCE
RESTANTE (cf. REPORT en fin de module), elle aussi sous le même verrou « n ≤ 𝔟 ».

INVARIANT : theorie_ensembles() = 22.  Aucun axiome nouveau ; rien postulé ; les
inégalités descendantes (le verrou « 2 ≤ 𝔟 ») ne sont JAMAIS supposées vraies, mais
isolées en hypothèses honnêtes.  Noyau INTACT.
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import Terme, var, egal, et
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E

from bourbaki.cardinaux.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    cardinal, inf_egal_card, est_cardinal,
)
from bourbaki.ensembles.familles.ii_4_reunion_intersection_familles.ii_4_recollement_somme.ensembles_somme_disjointe import (
    somme_disjointe, somme_cardinale_binaire,
)
from bourbaki.cardinaux.iii_3_equipotence_cardinaux.somme_produit_bornes.ensembles_cardinaux_bornes_somme import inf_egal_somme_gauche
from bourbaki.cardinaux.arithmetique.iii_3_2_monotonie.ensembles_arith_cardinale_props_exposant_monotone import (
    inf_egal_transporte_cardinal,
)
from bourbaki.cardinaux.iii_3_equipotence_cardinaux.ordre_cardinaux.ensembles_cardinaux_props_restantes_ordre import (
    inf_egal_antisymetrique_card, _cardinal_est_son_cardinal,
)
from bourbaki.entiers.iii_4_entiers_finis.iii_4_2_finis_props.ensembles_chap3_props_restantes import est_cardinal_de_cardinal
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    instancie, conjonction_intro,
)
from bourbaki.logique.i_4_egalitaires.tactiques_abrege_egalite import symetrie, composer_egalites


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# ════════════════════════════════════════════════════════════════════════════
#  Brique : 𝔟 ≤ 𝔟+𝔟   (inconditionnel SOUS est_cardinal(𝔟)).
#  inf_egal_somme_gauche(𝔟,𝔟) ⊢ 𝔟 ≤ 𝔟⊔𝔟 (ENSEMBLISTE) ;  transport par Card :
#  Card 𝔟 ≤ Card(𝔟⊔𝔟) = 𝔟+𝔟 ; puis Card 𝔟 = 𝔟 (𝔟 cardinal) réécrit le LHS.
# ════════════════════════════════════════════════════════════════════════════
def _b_inf_egal_somme_gauche(vb, vsecond):
    """{ est_cardinal(𝔟) } ⊢ 𝔟 ≤ Card(𝔟⊔S) = somme_cardinale_binaire(𝔟,S),  où S=vsecond.

    Injection canonique GAUCHE de 𝔟 dans 𝔟⊔S (inf_egal_somme_gauche, AUCUNE
    transitivité — donc capture-safe même pour S = 𝔟⊔𝔟 imbriqué) + transport par
    Card + Card 𝔟 = 𝔟.  SEULE hyp ouverte : est_cardinal(𝔟)."""
    cb = cardinal(vb)
    bS = somme_disjointe(vb, vsecond)                # 𝔟⊔S
    cbS = cardinal(bS)                               # = somme_cardinale_binaire(𝔟,S)

    # 𝔟 ≤ 𝔟⊔S  (ENSEMBLISTE, injection gauche — pas de transitivité)
    le_ens = inf_egal_somme_gauche(vb, vsecond)      # 𝔟 ≤ 𝔟⊔S
    assert le_ens.conclusion == inf_egal_card(vb, bS)

    # transport : (𝔟 ≤ 𝔟⊔S) ⇒ (Card 𝔟 ≤ Card(𝔟⊔S))   (généralisé/instancié aux termes)
    transp_gen = N.generalisation("X", N.generalisation("Y",
        inf_egal_transporte_cardinal("X", "Y")))
    transp = instancie(instancie(transp_gen, vb), bS)
    le_card = N.modus_ponens(le_ens, transp)         # Card 𝔟 ≤ Card(𝔟⊔S)
    assert le_card.conclusion == inf_egal_card(cb, cbS)

    # Card 𝔟 = 𝔟  (𝔟 est un cardinal) ; réécrit le LHS Card 𝔟 → 𝔟 via S6.
    cb_eq_b = N.modus_ponens(N.assume(est_cardinal(vb)), _cardinal_est_son_cardinal(vb))  # Card 𝔟 = 𝔟
    assert cb_eq_b.conclusion == egal(cb, vb)
    from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import equivalence_avant
    s6 = N.s6(cb, vb, "w", inf_egal_card(var("w"), cbS))
    res = N.modus_ponens(le_card, equivalence_avant(N.modus_ponens(cb_eq_b, s6)))  # 𝔟 ≤ Card(𝔟⊔S)
    assert res.conclusion == inf_egal_card(vb, cbS)
    return res


def _b_inf_egal_b_plus_b(vb):
    """{ est_cardinal(𝔟) } ⊢ 𝔟 ≤ Card(𝔟⊔𝔟) = somme_cardinale_binaire(𝔟,𝔟)."""
    return _b_inf_egal_somme_gauche(vb, vb)


# ════════════════════════════════════════════════════════════════════════════
#  Brique : antisymétrie close au TERME — (x ≤ y et y ≤ x et card x et card y) ⇒ x=y.
# ════════════════════════════════════════════════════════════════════════════
def _antisym_t(tx, ty):
    """⊢ (x≤y et y≤x et est_cardinal(x) et est_cardinal(y)) ⇒ x=y, pour TERMES x,y
    (inf_egal_antisymetrique_card généralisé/instancié, capture-safe)."""
    vx, vy = _t(tx), _t(ty)
    gen = inf_egal_antisymetrique_card("a", "b")     # (∀a∀b)(… ⇒ a=b)
    return instancie(instancie(gen, vx), vy)


# ════════════════════════════════════════════════════════════════════════════
#  (1)  deux_b_egal_b :  { est_cardinal(𝔟), 𝔟+𝔟 ≤ 𝔟 } ⊢ 𝔟 + 𝔟 = 𝔟.
# ════════════════════════════════════════════════════════════════════════════
def deux_b_egal_b(b="b"):
    """{ est_cardinal(𝔟),  𝔟+𝔟 ≤ 𝔟 }  ⊢  somme_cardinale_binaire(𝔟,𝔟) = 𝔟.   (2𝔟=𝔟.)

    🎯 2𝔟 = 𝔟 pour 𝔟 = 𝔟² infini (E.III.45).  Route ANTISYMÉTRIE :
      • 𝔟 ≤ 𝔟+𝔟   — CLOS sous est_cardinal(𝔟) (_b_inf_egal_b_plus_b : injection
        canonique gauche + transport par Card + Card 𝔟 = 𝔟) ;
      • 𝔟+𝔟 ≤ 𝔟   — HYP HONNÊTE (la descente 2𝔟 ≤ 𝔟², verrouillée par « 2 ≤ 𝔟 »
        = « n ≤ 𝔟 pour 𝔟 infini », REPORTÉE) ;
      • antisymétrie (CANTOR–BERNSTEIN, `inf_egal_antisymetrique_card`), avec
        est_cardinal(𝔟+𝔟) (=Card(𝔟⊔𝔟), `est_cardinal_de_cardinal`) et
        est_cardinal(𝔟) (hyp) ⇒ 𝔟+𝔟 = 𝔟.

    Hyps HONNÊTES (jamais postulées vraies) : est_cardinal(𝔟), 𝔟+𝔟 ≤ 𝔟.
    Conclusion ∉ hyps ; theorie=22."""
    vb = _t(b)
    bb = somme_disjointe(vb, vb)
    bplusb = somme_cardinale_binaire(vb, vb)          # = cardinal(𝔟⊔𝔟)
    assert bplusb == cardinal(bb)
    cible = egal(bplusb, vb)

    # ≥ : 𝔟 ≤ 𝔟+𝔟   (clos sous est_cardinal(𝔟))
    ge = _b_inf_egal_b_plus_b(vb)                     # 𝔟 ≤ 𝔟+𝔟   [hyp est_cardinal(𝔟)]
    assert ge.conclusion == inf_egal_card(vb, bplusb)

    # ≤ : 𝔟+𝔟 ≤ 𝔟   (HYP HONNÊTE)
    le = N.assume(inf_egal_card(bplusb, vb))          # 𝔟+𝔟 ≤ 𝔟

    # est_cardinal(𝔟+𝔟) = est_cardinal(Card(𝔟⊔𝔟))   (clos)
    card_bb = est_cardinal_de_cardinal(bb)            # est_cardinal(Card(𝔟⊔𝔟))
    assert card_bb.conclusion == est_cardinal(bplusb)
    # est_cardinal(𝔟)   (HYP HONNÊTE)
    card_b = N.assume(est_cardinal(vb))

    # antisymétrie aux termes (𝔟+𝔟, 𝔟) : (𝔟+𝔟≤𝔟 et 𝔟≤𝔟+𝔟 et card(𝔟+𝔟) et card 𝔟) ⇒ 𝔟+𝔟=𝔟
    anti = _antisym_t(bplusb, vb)
    ante = et(et(et(inf_egal_card(bplusb, vb), inf_egal_card(vb, bplusb)),
                 est_cardinal(bplusb)), est_cardinal(vb))
    minor = conjonction_intro(conjonction_intro(conjonction_intro(le, ge), card_bb), card_b)
    assert minor.conclusion == ante, \
        f"deux_b_egal_b : antécédent inattendu\n{minor.conclusion}\nvs\n{ante}"
    res = N.modus_ponens(minor, anti)                 # 𝔟+𝔟 = 𝔟

    assert res.conclusion == cible, \
        f"deux_b_egal_b : conclusion inattendue\n{res.conclusion}\nvs\n{cible}"
    assert est_cardinal(vb) in res.hypotheses, "deux_b_egal_b : hyp est_cardinal(𝔟) absente"
    assert inf_egal_card(bplusb, vb) in res.hypotheses, "deux_b_egal_b : hyp 𝔟+𝔟≤𝔟 absente"
    assert res.conclusion not in res.hypotheses, "deux_b_egal_b : VACUOUS"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  (2)  trois_b_egal_b :  { est_cardinal(𝔟), (𝔟+𝔟)+𝔟 ≤ 𝔟 } ⊢ (𝔟+𝔟)+𝔟 = 𝔟.
# ════════════════════════════════════════════════════════════════════════════
def trois_b_egal_b(b="b"):
    """{ est_cardinal(𝔟),  𝔟+(𝔟+𝔟) ≤ 𝔟 }  ⊢  somme_cardinale_binaire(𝔟, 𝔟+𝔟) = 𝔟.  (3𝔟=𝔟.)

    🎯 3𝔟 = 𝔟 pour 𝔟 = 𝔟² infini (E.III.45).  Même route ANTISYMÉTRIE, avec
    3𝔟 := somme_cardinale_binaire(𝔟, 𝔟+𝔟) (= Card(𝔟⊔(𝔟⊔𝔟))) — somme RIGHT-associée
    pour que 𝔟 soit le SOMMANT GAUCHE de la somme externe (injection directe, SANS
    transitivité ⇒ capture-safe sur le terme imbriqué) :
      • 𝔟 ≤ 3𝔟   — CLOS sous est_cardinal(𝔟) (_b_inf_egal_somme_gauche(𝔟, 𝔟⊔𝔟) :
        injection canonique gauche de 𝔟 dans 𝔟⊔(𝔟⊔𝔟) + transport par Card + Card 𝔟 = 𝔟) ;
      • 3𝔟 ≤ 𝔟   — HYP HONNÊTE (descente 3𝔟 ≤ 𝔟², verrouillée par « 3 ≤ 𝔟 »
        = « n ≤ 𝔟 pour 𝔟 infini », REPORTÉE) ;
      • antisymétrie (CANTOR–BERNSTEIN) ⇒ 3𝔟 = 𝔟.

    (3𝔟 = 𝔟+(𝔟+𝔟) ; par associativité/commutativité de la somme cardinale,
    Card(𝔟⊔(𝔟⊔𝔟)) = Card((𝔟⊔𝔟)⊔𝔟) = « (𝔟+𝔟)+𝔟 », déjà closes ailleurs.)

    Hyps HONNÊTES : est_cardinal(𝔟), 𝔟+(𝔟+𝔟) ≤ 𝔟.  Conclusion ∉ hyps ; theorie=22."""
    vb = _t(b)
    bb = somme_disjointe(vb, vb)                       # 𝔟⊔𝔟
    bbb = somme_disjointe(vb, bb)                      # 𝔟⊔(𝔟⊔𝔟)   (RIGHT-associé)
    threeb = somme_cardinale_binaire(vb, bb)           # = cardinal(𝔟⊔(𝔟⊔𝔟)) = 3𝔟
    assert threeb == cardinal(bbb)
    cible = egal(threeb, vb)

    # ≥ : 𝔟 ≤ 3𝔟   (injection gauche directe, pas de transitivité)
    ge = _b_inf_egal_somme_gauche(vb, bb)             # 𝔟 ≤ Card(𝔟⊔(𝔟⊔𝔟)) = 3𝔟
    assert ge.conclusion == inf_egal_card(vb, threeb)

    # ≤ : 3𝔟 ≤ 𝔟   (HYP HONNÊTE)
    le = N.assume(inf_egal_card(threeb, vb))

    # est_cardinal(3𝔟) (clos) ; est_cardinal(𝔟) (hyp)
    card_3b = est_cardinal_de_cardinal(bbb)           # est_cardinal(Card((𝔟⊔𝔟)⊔𝔟))
    assert card_3b.conclusion == est_cardinal(threeb)
    card_b = N.assume(est_cardinal(vb))

    # antisymétrie (3𝔟, 𝔟)
    anti = _antisym_t(threeb, vb)
    ante = et(et(et(inf_egal_card(threeb, vb), inf_egal_card(vb, threeb)),
                 est_cardinal(threeb)), est_cardinal(vb))
    minor = conjonction_intro(conjonction_intro(conjonction_intro(le, ge), card_3b), card_b)
    assert minor.conclusion == ante, \
        f"trois_b_egal_b : antécédent inattendu\n{minor.conclusion}\nvs\n{ante}"
    res = N.modus_ponens(minor, anti)                 # 3𝔟 = 𝔟

    assert res.conclusion == cible, \
        f"trois_b_egal_b : conclusion inattendue\n{res.conclusion}\nvs\n{cible}"
    assert est_cardinal(vb) in res.hypotheses, "trois_b_egal_b : hyp est_cardinal(𝔟) absente"
    assert inf_egal_card(threeb, vb) in res.hypotheses, "trois_b_egal_b : hyp 3𝔟≤𝔟 absente"
    assert res.conclusion not in res.hypotheses, "trois_b_egal_b : VACUOUS"
    return res


__all__ = ["deux_b_egal_b", "trois_b_egal_b"]
