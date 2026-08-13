"""Le premier énoncé OUVERT que l'instrumentation puisse mesurer.

Ces tests ne disent rien sur la vérité de Goldbach. Ils figent deux choses :
que l'énoncé est CLOS et bâti sur un vocabulaire AXIOMATISÉ, et que la
trichotomie répond « inconnu » plutôt que de tirer un « indépendante » gratuit.
"""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Formule, libres_f, var, egal,
)
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from outils_ia.conjectures.goldbach import goldbach, est_premier, un, deux
from outils_ia.verite import classer_residu as CR


def test_enonce_clos_et_sans_symbole_libre():
    """👑 LE point. Sur les termes opaques `plus_ent`/`prod_ent`, l'énoncé porte
    des symboles qu'aucun axiome ne contraint et la trichotomie tire un
    « indépendante » gratuit. Sur l'arithmétique construite, il n'en porte
    aucun — c'est ce qui rend le verdict signifiant."""
    G = goldbach()
    assert isinstance(G, Formule)
    assert libres_f(G) == set(), "l'énoncé doit être clos"
    assert CR.symboles_libres(G, E.theorie_ensembles()) == frozenset(), \
        "aucun symbole ne doit échapper aux 22 axiomes"


def test_le_vocabulaire_est_celui_de_la_theorie_de_reference():
    """Les symboles employés sont ceux que les 22 axiomes contraignent."""
    G = goldbach()
    T0 = E.theorie_ensembles()
    assert CR.symboles(G) <= CR.symboles_theorie(T0)


def test_la_trichotomie_dit_inconnu_et_non_independante():
    """Le quatrième état épistémique : une DETTE DE MESURE, pas un mur.

    Sans prouveur injecté, le classifieur ne peut ni décharger ni réfuter ; le
    seul risque est qu'il sur-affirme par le critère syntaxique. Il ne le fait
    pas, parce qu'il n'y a plus de symbole libre à quoi l'accrocher."""
    verdict = CR.classer(goldbach(), E.theorie_ensembles())
    assert verdict == "inconnu", f"attendu « inconnu », mesuré « {verdict} »"


def test_les_termes_opaques_donneraient_un_verdict_gratuit():
    """🔴 RÉGRESSION — la mesure qui a motivé tout ce module.

    `plus_ent`, `prod_ent`, `un_ent` ne sont contraints par aucun axiome. Ce test
    fige ce fait : si l'un d'eux recevait un jour son axiome, il tomberait, et
    c'est alors qu'il faudrait rouvrir la question de `divise`."""
    T0 = E.theorie_ensembles()
    voc = CR.symboles_theorie(T0)
    for opaque in ("plus_ent", "prod_ent", "un_ent"):
        assert opaque not in voc, \
            f"{opaque} est désormais contraint : reconsidérer `divise` et les opaques"


def test_aucun_theoreme_n_est_construit():
    """L'invariant du dépôt : poser une conjecture ne touche pas la théorie."""
    assert len(E.theorie_ensembles().axiomes) == 22
    assert isinstance(goldbach(), Formule)
    assert isinstance(est_premier(un()), Formule)


def test_un_et_deux_sont_construits_et_distincts():
    """1 et 2 sont Card{∅} et 1+1, pas des symboles postulés."""
    assert not egal(un(), deux()) == egal(un(), un())
    assert libres_f(egal(un(), deux())) == set()


# ── le prouveur branché : sans lui, aucun verdict n'informe ──────────────────
def test_sans_prouveur_le_verdict_n_informe_pas():
    """🔴 LA MESURE QUI A MOTIVÉ L'ADAPTATEUR (5 août 2026).

    Sans prouveur injecté, `classer` rend « inconnu » pour Goldbach — mais aussi
    pour `z = z`, qui est clos par la primitive de réflexivité du noyau. Le
    verdict ne distinguait donc pas l'ouvert du trivialement vrai : il ne portait
    aucune information. Un verdict n'informe que si l'outil peut en rendre un
    autre."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
        var, egal,
    )
    T0 = E.theorie_ensembles()
    assert CR.classer(egal(var("z"), var("z")), T0) == "inconnu"
    assert CR.classer(goldbach(), T0) == "inconnu"


def test_avec_prouveur_le_classifieur_discrimine():
    """👑 Le prouveur branché sépare le trivialement clos de l'ouvert.

    C'est ce qui donne son sens au « inconnu » de Goldbach : le classifieur
    vient de fermer trois autres cibles et n'a pas pu entamer celle-là."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
        var, egal,
    )
    from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_recollement_somme.ensembles_somme_disjointe import (
        somme_cardinale_binaire,
    )
    from outils_ia.conjectures.prouveur_branche import prouveur
    T0 = E.theorie_ensembles()
    quatre = somme_cardinale_binaire(deux(), deux())

    assert CR.classer(egal(var("z"), var("z")), T0, prouveur=prouveur,
                      timeout=25) == "dechargeable"
    assert CR.classer(egal(quatre, quatre), T0, prouveur=prouveur,
                      timeout=25) == "dechargeable"
    assert CR.classer(T0.axiomes[0], T0, prouveur=prouveur,
                      timeout=25) == "dechargeable"
    assert CR.classer(goldbach(), T0, prouveur=prouveur,
                      timeout=25) == "inconnu"


def test_l_adaptateur_ne_peut_pas_fabriquer_de_faux_theoreme():
    """La soundness ne dépend pas de l'adaptateur : `classer` re-vérifie type,
    clôture et conclusion. Un adaptateur qui mentirait ferait perdre une preuve,
    jamais gagner un théorème."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
        var, appartient,
    )
    from outils_ia.conjectures.prouveur_branche import prouveur
    T0 = E.theorie_ensembles()
    faux = appartient(var("aaa"), var("bbb"))
    assert prouveur(faux, T0) is None
    assert len(E.theorie_ensembles().axiomes) == 22


def test_le_quantificateur_de_primalite_est_garde():
    """🔴 RÉGRESSION — le défaut trouvé par la recherche du 5 août 2026.

    Sans garde, le (∀d) de `est_premier` parcourt TOUS LES ENSEMBLES et non les
    entiers. Or `divise_propre(d, p)` ne regarde que `Card(d)` : elle a un sens
    pour un `d` qui n'est pas un cardinal. L'énoncé non gardé affirmait donc que
    tout ensemble à deux éléments EST le τ-terme du cardinal 1 ou celui du 2 —
    ce qui n'est pas de l'arithmétique, et rendait `est_premier(2)` indémontrable
    pour une raison étrangère à la primalité.

    Ce test fige la présence de la garde dans la formule elle-même."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (
        est_fini,
    )
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
        var,
    )

    def _contient(f, cible):
        return f == cible or any(_contient(s, cible) for s in getattr(f, "sous", ()))

    formule = est_premier(deux(), d="dgb")
    assert _contient(formule, est_fini(var("dgb"))), \
        "le (∀d) de est_premier doit être gardé par est_fini(d)"
