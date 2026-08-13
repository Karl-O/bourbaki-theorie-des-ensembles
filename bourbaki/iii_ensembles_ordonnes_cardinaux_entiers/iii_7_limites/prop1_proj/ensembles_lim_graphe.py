"""§III.7.1 — « tout point d'une limite projective est un graphe ».

────────────────────────────────────────────────────────────────────────────────
La définition de lim←_{α∈I}(E_α, f_{αβ}) en fait une PARTIE du produit ∏_α E_α
(E III.52, formule (1)).  Or « les points du produit sont des graphes » est,
depuis la réparation de l'axiome du produit (26 juil. 2026), un théorème CLOS du
dépôt : `produit_graphe` (ii_5_definitions/ensembles_produit_famille).  Les deux
faits se composent immédiatement :

    x ∈ lim←   ⟹   x ∈ ∏_α E_α   ⟹   est_un_graphe(x).

L'intérêt n'est pas la profondeur — la preuve tient en un modus ponens — mais
l'ÉCONOMIE D'HYPOTHÈSES chez les consommateurs.  `extensionnalite_produit`
réclame `est_un_graphe` de ses deux points ; jusqu'ici les modules de §7.2
portaient ces conditions comme hypothèses honnêtes, ce qui faisait apparaître
dans la prémisse de l'injectivité universelle deux conjoints qui n'ont rien à
y faire (`prop3_g_injective` : 9 hypothèses au lieu de 7).  Avec ce lemme la
condition de graphe est DÉDUITE de l'appartenance à la limite, déjà présente.

⚠️ Ce lemme est le seul endroit où le passage lim← → ∏ sert à autre chose qu'à
   l'extensionnalité : `_lim_dans_produit` (ensembles_cone_unicite) fait le
   premier pas, `produit_graphe` le second.  Ne pas ré-dériver l'un des deux.
⚠️ PIÈGE DE LIANT, mesuré ici.  `E.est_un_graphe(g)` est l'abréviation
   (∀z)(z∈g ⇒ z est un couple) : elle LIE « z ».  Un point NOMMÉ « z » est donc
   capturé — `est_un_graphe(var("z"))` dit (∀z)(z∈z ⇒ …), qui n'est pas
   l'énoncé voulu.  D'où le nom par défaut « p » ci-dessous ; les assertions de
   conclusion détectent la capture si un appelant repasse « z ».
INVARIANT : theorie_ensembles()=22 ; rien postulé, tout déduit.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, appartient, impl, pourtout,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    instancie,
)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import (
    ensembles_abrege as E,
)
from bourbaki.ii_theorie_des_ensembles.ii_5_produit_famille.ii_5_definitions.ensembles_produit_famille import (
    produit_graphe,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites import (
    ensembles_limites as L,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites.ensembles_cone_unicite import (
    _lim_dans_produit, _gleq,
)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# @livre Ch.III §7.1 Lem.- | E III.52 L.4-11 | PDF p.155  (lim← est une PARTIE du produit : ses points sont donc des graphes)
def point_limite_est_graphe(Efam="E", f="f", leq=None, i="I", terme=None,
                            preuve_in_lim=None):
    """{ hyps de preuve_in_lim } ⊢ est_un_graphe(terme).

    Deux pas, tous deux déjà dans le dépôt :
      1. `_lim_dans_produit` : terme ∈ lim←  ⟹  terme ∈ ∏_α E_α  (conjoint de
         tête de la caractérisation (1)) ;
      2. `produit_graphe` : (∀F)(F ∈ ∏ ⇒ est_un_graphe F), CLOS depuis la
         réparation de l'axiome du produit — on l'instancie au terme.

    `preuve_in_lim` est une preuve de « terme ∈ lim← » (typiquement un
    `N.assume`) ; les hypothèses du résultat sont EXACTEMENT les siennes : le
    lemme n'en ajoute aucune."""
    if leq is None:
        leq = _gleq()
    if terme is None:
        terme = var("p")
    terme = _t(terme)
    if preuve_in_lim is None:
        preuve_in_lim = N.assume(appartient(terme, L.lim_proj(_t(Efam), _t(f))))
    en_prod = _lim_dans_produit(Efam, f, leq, i, terme, preuve_in_lim)
    res = N.modus_ponens(en_prod, instancie(
        produit_graphe(Efam, i, "F"), terme))
    assert res.conclusion == E.est_un_graphe(terme), \
        "point_limite_est_graphe : conclusion ≠ est_un_graphe(terme)"
    assert res.hypotheses == preuve_in_lim.hypotheses, \
        "point_limite_est_graphe : hypothèses ≠ celles de la prémisse"
    return res


# @livre Ch.III §7.1 Lem.- | E III.52 L.4-11 | PDF p.155  (forme universelle CLOSE : (∀z)(z ∈ lim← ⇒ est_un_graphe z))
def limite_points_graphes(Efam="E", f="f", leq=None, i="I", z="p"):
    """⊢ (∀p)( p ∈ lim←_{α∈I}(E_α, f_{αβ})  ⇒  est_un_graphe(p) ).  [CLOS].

    La forme réutilisable : aucune hypothèse, un seul liant.  Les sites qui en
    ont besoin l'instancient au point voulu — c'est ainsi que
    `prop3_g_injective` se débarrasse de ses deux conditions de graphe.

    Le liant vaut « p » et non « z » : voir le piège de capture en tête de
    module."""
    if leq is None:
        leq = _gleq()
    vz = _t(z)
    h = N.assume(appartient(vz, L.lim_proj(_t(Efam), _t(f))))
    ponctuel = point_limite_est_graphe(Efam, f, leq, i, vz, h)
    nom = z if isinstance(z, str) else vz.nom
    res = N.generalisation(nom, N.loi_deduction(
        appartient(vz, L.lim_proj(_t(Efam), _t(f))), ponctuel))
    assert res.conclusion == pourtout(nom, impl(
        appartient(vz, L.lim_proj(_t(Efam), _t(f))), E.est_un_graphe(vz))), \
        "limite_points_graphes : conclusion ≠ (∀z)(z∈lim← ⇒ graphe z)"
    assert res.est_clos, "limite_points_graphes : non clos"
    return res


__all__ = ["point_limite_est_graphe", "limite_points_graphes"]
