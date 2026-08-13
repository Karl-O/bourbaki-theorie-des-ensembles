"""§II.4.6 Déf. 5 — le PONT « recouvrement ⇒ lecture ponctuelle », CLOS (0 hypothèse).

Bourbaki (E II.27, §4 n°6, Déf. 5, VÉRIFIÉ AU PDF p.78 L.34-38) : « On dit qu'une
famille d'ensembles (X_ι)_{ι∈I} est un recouvrement d'un ensemble E si E ⊂ ⋃_{ι∈I} X_ι. »
C'est la définition ENSEMBLISTE (une inclusion).  Tout consommateur en a en fait
besoin sous sa forme PONCTUELLE : « tout point de E est dans un X_ι ».  Ce fichier
certifie que les deux coïncident — sans aucune hypothèse honnête :

    ⊢  ( E ⊂ ⋃_{ι∈I} X_ι )  ⇒  (∀x)( x∈E ⇒ (∃i)(i∈I et x∈X_i) )

⚠️ CORRECTION D'UNE CARTE PÉRIMÉE.  La docstring de
`ii_6_relations_equivalence/ensembles_egalite_equivalence.py` affirme que ce pont
« exige la caractérisation d'appartenance z∈⋃_{ι∈I}X_ι ⇔ (∃ι)(ι∈I et z∈X_ι),
ABSENTE (reunion_famille est un app opaque, chantier ⋃-famille) », et porte donc
H_rec en HYPOTHÈSE honnête.  C'est FAUX depuis que `membre_reunion_famille` existe
(ii_4_1/ensembles_familles.py) : c'est une instance DIRECTE d'AXIOME_REUNION_FAM,
close, 0 hypothèse.  Le maillon prétendu manquant est là ; le pont ci-dessous se
démontre en cinq lignes.  ⇒ H_rec de `relation_partition_reflexive_dans` est
DÉCHARGEABLE : il suffit de lui fournir est_recouvrement à la place.

DIRECTION DES DÉPENDANCES.  Le résultat vit ici (§II.4, sa section du livre) et
NON dans ii_6 : `bourbaki/ii_4_*` ne doit pas importer `bourbaki/ii_6_*`.  La
formule H_rec est donc redéfinie ici (`recouvrement_points`) ; le test miroir
importe ii_6 et vérifie qu'elle est VERBATIM identique à celle qu'y attend
`relation_partition_reflexive_dans` — c'est là que se ferme la boucle.

Liants : « x » et « i » sont IMPOSÉS (ce sont ceux de l'énoncé H_rec côté ii_6 :
`recouvrement_points(f, i_set, e, x="x", i="i")`) — pas des choix libres ; les
changer casserait la décharge.  « z » est le liant par défaut de outil_formule.inclus.
theorie_ensembles() == 22 ; rien postulé.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, et, impl, appartient, existe, pourtout)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    equivalence_avant, instancie)
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_1_definitions_algebre.ensembles_familles import (
    membre_reunion_famille)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# @livre Ch.II §4.6 Def.5 | E II.27 L.34-38 | PDF p.78  (recouvrement : E ⊂ ⋃_{ι∈I} X_ι)
def recouvrement_points(f="f", i_set="I", e="E", x="x", i="i"):
    """H_rec := (∀x)( x∈E ⇒ (∃i)(i∈I et x∈X_i) )   — lecture PONCTUELLE du recouvrement.

    Formule VERBATIM de `ensembles_egalite_equivalence.recouvrement_points` (ii_6) ;
    redéfinie ici pour ne pas inverser la direction des dépendances (test miroir)."""
    vf, viset, ve = _t(f), _t(i_set), _t(e)
    vx, vi = var(x), var(i)
    return pourtout(x, impl(appartient(vx, ve),
                            existe(i, et(appartient(vi, viset),
                                         appartient(vx, E.valeur_famille(vf, vi))))))


def enonce_recouvrement_donne_points(f="f", i_set="I", e="E", x="x", i="i"):
    return impl(E.est_recouvrement(_t(f), _t(i_set), _t(e)),
                recouvrement_points(f, i_set, e, x, i))


# @livre Ch.II §4.6 Def.5 | E II.27 L.34-38 | PDF p.78  (le recouvrement, lu point par point)
def recouvrement_donne_points(f="f", i_set="I", e="E", x="x", i="i"):
    """⊢ ( E ⊂ ⋃_{ι∈I}X_ι ) ⇒ (∀x)( x∈E ⇒ (∃i)(i∈I et x∈X_i) ).   CLOS — 0 hypothèse.

    Déplié : le recouvrement EST l'inclusion E ⊂ ⋃X_ι, i.e. (∀z)(z∈E ⇒ z∈⋃X_ι) ;
    on l'instancie en x, puis membre_reunion_famille (instance close d'AXIOME_
    REUNION_FAM) convertit x∈⋃X_ι en (∃i)(i∈I et x∈X_i)."""
    vf, viset, ve, vx = _t(f), _t(i_set), _t(e), var(x)
    rec = E.est_recouvrement(vf, viset, ve)                 # E ⊂ ⋃_{ι∈I} X_ι

    h = N.assume(rec)
    hx = N.assume(appartient(vx, ve))                       # x∈E
    x_in_reu = N.modus_ponens(hx, instancie(h, vx))         # x ∈ ⋃_{ι∈I} X_ι
    ex = N.modus_ponens(x_in_reu,                           # (∃i)(i∈I et x∈X_i)
                        equivalence_avant(membre_reunion_famille(f, i_set, x)))
    gen = N.generalisation(x, N.loi_deduction(appartient(vx, ve), ex))
    res = N.loi_deduction(rec, gen)

    assert res.conclusion == enonce_recouvrement_donne_points(f, i_set, e, x, i), \
        "recouvrement_donne_points : conclusion ≠ énoncé attendu"
    assert res.hypotheses == frozenset(), \
        "recouvrement_donne_points : le théorème doit être CLOS (0 hypothèse)"
    assert res.est_clos, "recouvrement_donne_points : est_clos attendu True"
    return res


__all__ = ["recouvrement_points", "enonce_recouvrement_donne_points",
           "recouvrement_donne_points"]
