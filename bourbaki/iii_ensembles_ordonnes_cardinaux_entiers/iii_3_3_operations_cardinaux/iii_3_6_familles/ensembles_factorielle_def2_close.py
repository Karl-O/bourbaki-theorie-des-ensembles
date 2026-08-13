"""§III.5.8 Déf.2 — LA RÉCURSION DÉCHARGÉE :  { n∈ℕ, HW, HN } ⊢ (n+1)! = n!·(n+1).

H2/H3 (« les membres des produits ∏_{I∪{j}} / ∏_I sont des GRAPHES ») étaient
portées comme hypothèses honnêtes depuis T1b-2 — et, sous l'ANCIEN axiome produit,
elles étaient même RÉFUTABLES pour I=∅.  L'axiome RÉPARÉ (26 juil. 2026) les
DÉMONTRE : `produit_graphe` [CLOS, 0 hyp] (ii_5_definitions), instancié ici aux
deux produits de la récursion, au liant « G » directement via son paramètre `ff`
(zéro re-liant — le liant est un PARAMÈTRE exposé, leçon ev. 101 sans son coût).

  🎯 `factorielle_def2_dechargee(n)` :
        { n∈ℕ, HW, HN } ⊢ factorielle_def2(succ n) = factorielle_def2(n)·(succ n)

Restent EXACTEMENT les ponts fam↔valeur HW/HN, INDÉPENDANTS des 22 (mesuré —
l'exemplaire X_ι = f(ι) de l'article) : leur résolution est la phase 2 (extension-δ
ou décision d'encodage valeur_famille := valeur).
INVARIANT : theorie_ensembles() = 22.  Noyau et subst INTOUCHÉS.  Rien postulé.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, appartient,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E

from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import instancie
from bourbaki.ii_theorie_des_ensembles.ii_5_produit_famille.ii_5_definitions.ensembles_produit_famille import produit_graphe
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import successeur
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_1_n_objet_existence.ensembles_ensemble_NN import ensemble_NN
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_6_familles.ensembles_produit_adjonction import produit_total
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_6_familles.ensembles_produit_recursion import (
    hypotheses_graphes_recursion, _seg_NN,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_6_familles.ensembles_famille_successeurs import famille_successeurs
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_6_familles.ensembles_factorielle_def2_rec import (
    factorielle_def2_recursion, factorielle_def2_recursion_enonce,
    hypothese_valuation_large, hypothese_valuation_etroite, _HB,
)


def _t(t):
    """Coercion str/Terme → Terme."""
    return t if isinstance(t, Terme) else var(t)


def _dech(thm, hyp, preuve_hyp):
    """De Γ∪{H}⊢C et Δ⊢H, déduit Γ∪Δ⊢C (loi_deduction puis modus_ponens)."""
    return N.modus_ponens(preuve_hyp, N.loi_deduction(hyp, thm))


def _instance_graphes(u, idx):
    """⊢ (∀G)( G ∈ ∏_{idx} u ⇒ est_un_graphe(G) )   [CLOS] — produit_graphe instancié.

    Noms de ∀-clôture EXOTIQUES fpg/Ipg (u et idx sont des termes à liants) ; le
    liant du ∀ interne est « G » directement (paramètre ff de produit_graphe)."""
    g = N.generalisation("fpg", N.generalisation("Ipg",
        produit_graphe("fpg", "Ipg", ff="G")))
    return instancie(instancie(g, _t(u)), _t(idx))


# ══════════════════════════════════════════════════════════════════════════════
#  🎯 { n∈ℕ, HW, HN } ⊢ (succ n)!_déf2 = (n!_déf2)·(succ n)   — H2/H3 DÉCHARGÉES.
# ══════════════════════════════════════════════════════════════════════════════
# @livre Ch.III §5.8 Def.2 | E III.41 L.28-29 | PDF p.144  (n! = ∏_{i<n}(i+1) — la récursion de la forme-produit, H2/H3 désormais THÉORÈMES par l'axiome produit réparé)
# @livre Ch.III §5.8 Rem.- | E III.41 L.30-32 | PDF p.144  (« (n+1)! = n!(n+1) » — la même relation, côté Déf.2)
def factorielle_def2_dechargee(n="nfr", iota="ifs"):
    """🎯 { n∈ℕ, HW, HN } ⊢ factorielle_def2(succ n) = pcb(factorielle_def2(n), succ n).

    `factorielle_def2_recursion` (5 hyps) dont H2/H3 sont COUPÉES par les instances
    closes de `produit_graphe` — miroir `==` asserté sur chacune avant la coupe.
    Restent les ponts fam↔valeur HW/HN (indépendants, phase 2) et n∈ℕ."""
    vn = var(n)
    base = factorielle_def2_recursion(n, iota)               # 5 hyps
    W = famille_successeurs(successeur(vn), iota)
    I = _seg_NN(vn)
    h2, h3 = hypotheses_graphes_recursion(W, vn)

    th2 = _instance_graphes(W, produit_total(W, I, vn).args[1])   # ∏_{I∪{n}} W
    assert th2.conclusion == h2, \
        "factorielle_def2_dechargee : instance produit_graphe ≠ H2 (index ∪ ?)"
    th3 = _instance_graphes(W, I)                                 # ∏_I W
    assert th3.conclusion == h3, \
        "factorielle_def2_dechargee : instance produit_graphe ≠ H3"
    assert th2.est_clos and th3.est_clos, "factorielle_def2_dechargee : instances non closes"

    res = _dech(_dech(base, h2, th2), h3, th3)

    assert res.conclusion == factorielle_def2_recursion_enonce(n, iota), \
        "factorielle_def2_dechargee : conclusion altérée par les coupes"
    assert res.hypotheses == frozenset({
        appartient(vn, ensemble_NN()),
        hypothese_valuation_large(n, iota), hypothese_valuation_etroite(n, iota)}), \
        "factorielle_def2_dechargee : hypothèses ≠ { n∈ℕ, HW, HN }"
    assert len(res.hypotheses) == 3, "factorielle_def2_dechargee : hyps ≠ 3"
    assert res.conclusion not in res.hypotheses, "factorielle_def2_dechargee : VACUOUS"
    return res


# ══════════════════════════════════════════════════════════════════════════════
#  🎯🎯 { n∈ℕ } ⊢ (succ n)!_déf2 = (n!_déf2)·(succ n)  — HW/HN par RÉFLEXIVITÉ.
# ══════════════════════════════════════════════════════════════════════════════
def _pont_reflexif(antecedent, t, binder):
    """⊢ (∀i)( antecedent ⇒ t = t )   [CLOS] — le pont fam↔valeur post-migration."""
    imp = N.loi_deduction(antecedent, N.reflexivite(t))
    return N.generalisation(binder, imp)


# @livre Ch.III §5.8 Def.2 | E III.41 L.28-29 | PDF p.144  (n! = ∏_{i<n}(i+1) — la récursion Déf.2 au SEUL paramètre n∈ℕ : les ponts fam↔valeur sont morts avec la migration d'encodage du 2 août)
def factorielle_def2_ultime(n="nfr", iota="ifs"):
    """🎯🎯 { n∈ℕ } ⊢ factorielle_def2(succ n) = pcb(factorielle_def2(n), succ n).

    LE PAS DE RÉCURRENCE DE LA DÉF.2, AU SEUL PARAMÈTRE.  Depuis la migration
    valeur_famille := valeur (2 août 2026), les ponts HW/HN sont des égalités t=t :
    la réflexivité + ∀-clôture les DÉRIVE closes, et la coupe les efface.  Ce qui
    était mesuré INDÉPENDANT des 22 (l'exemplaire X_ι de l'article) est résolu par
    l'ENCODAGE FIDÈLE — le coup de la figure 3, sans axiome ni 23e entrée."""
    vn = var(n)
    base = factorielle_def2_dechargee(n, iota)               # 3 hyps
    W = famille_successeurs(successeur(vn), iota)
    Nw = famille_successeurs(vn, iota)
    vi = var(_HB)

    hw = hypothese_valuation_large(n, iota)
    thw = _pont_reflexif(appartient(vi, _seg_NN(successeur(vn))),
                         E.valeur(W, vi), _HB)
    assert thw.conclusion == hw, \
        "factorielle_def2_ultime : pont réflexif ≠ HW (migration incomplète ?)"
    hn = hypothese_valuation_etroite(n, iota)
    thn = _pont_reflexif(appartient(vi, _seg_NN(vn)), E.valeur(Nw, vi), _HB)
    assert thn.conclusion == hn, \
        "factorielle_def2_ultime : pont réflexif ≠ HN (migration incomplète ?)"
    assert thw.est_clos and thn.est_clos, "factorielle_def2_ultime : ponts non clos"

    res = _dech(_dech(base, hw, thw), hn, thn)

    assert res.conclusion == factorielle_def2_recursion_enonce(n, iota), \
        "factorielle_def2_ultime : conclusion altérée"
    assert res.hypotheses == frozenset({appartient(vn, ensemble_NN())}), \
        "factorielle_def2_ultime : hypothèses ≠ { n∈ℕ }"
    assert res.conclusion not in res.hypotheses, "factorielle_def2_ultime : VACUOUS"
    return res


__all__ = ["factorielle_def2_dechargee", "factorielle_def2_ultime"]
