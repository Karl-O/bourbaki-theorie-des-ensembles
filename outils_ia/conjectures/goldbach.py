"""GOLDBACH — l'énoncé, sur l'arithmétique CONSTRUITE.

────────────────────────────────────────────────────────────────────────────────
CE QUE CE MODULE EST, ET CE QU'IL N'EST PAS.  Il écrit une conjecture ouverte
depuis 1742 dans le langage du noyau.  Il ne la démontre pas, ne prétend rien sur
sa vérité, et ne produit aucun `Theoreme`.  Son intérêt est ailleurs : c'est le
premier énoncé OUVERT que l'instrumentation du corpus peut mesurer sans que la
mesure soit vide.

────────────────────────────────────────────────────────────────────────────────
POURQUOI « ARITHMÉTIQUE CONSTRUITE », ET POURQUOI C'EST LE POINT.

Une première tentative posait Goldbach sur les termes arithmétiques OPAQUES du
corpus, `plus_ent` et `prod_ent`.  La trichotomie a répondu **« indépendante »**.
Le verdict était juste et sans valeur : mesuré, `plus_ent`, `prod_ent` et
`un_ent` ne sont contraints par AUCUN axiome — ni par les 22 de la théorie de
référence, ni par aucune des 60 théories dédiées du dépôt.  L'énoncé ne parlait
donc pas d'addition ; il parlait de symboles de fonction non interprétés, et
n'importe quoi écrit avec eux est indépendant pour rien.

Écrit ici sur `somme_cardinale_binaire` et `divise_propre` — des τ bâtis sur
`Card`, le produit et la somme disjointe — l'énoncé n'a **plus aucun symbole
libre** au sens de la théorie de référence (mesuré : `symboles_libres` = ∅).  Le
critère syntaxique ne peut donc plus tirer d'« indépendante » gratuit, et le
classifieur rend **« inconnu »** : le quatrième état épistémique, celui que le
projet tient pour une DETTE DE MESURE et non pour un mur.

⚠️ LA LEÇON, qui vaut au-delà de Goldbach : **un verdict d'indépendance ne vaut
que relativement à un vocabulaire AXIOMATISÉ.**  Sur des symboles libres, il est
gratuit.  C'est la première limite de la trichotomie que le corpus ait mesurée
sur un problème réellement ouvert.

INVARIANT : aucun `Theoreme` construit ici ; `theorie_ensembles()` reste à 22.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, egal, non, et, impl, pourtout, existe,
)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import (
    ensembles_abrege as E,
)
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_recollement_somme.ensembles_somme_disjointe import (
    somme_cardinale_binaire,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    cardinal,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.props_restantes.ensembles_divisibilite_propre import (
    divise_propre,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (
    est_fini,
)


def zero():
    """Le cardinal 0, CONSTRUIT : Card ∅."""
    return cardinal(E.VIDE)


def un():
    """Le cardinal 1, CONSTRUIT : Card{∅}."""
    return cardinal(E.singleton(E.VIDE))


def deux():
    """Le cardinal 2, CONSTRUIT : 1 + 1 par la somme cardinale binaire."""
    return somme_cardinale_binaire(un(), un())


def _ou(a, b):
    """A ∨ B au niveau abrégé (¬(¬A ∧ ¬B) : le « ou » n'est pas primitif ici)."""
    return non(et(non(a), non(b)))


def est_premier(p, d="dgb", q="qgb"):
    """« p est premier » := p ≠ 1  et  (∀d)( (d fini et d | p) ⇒ (d = 1 ou d = p) ).

    La divisibilité est `divise_propre` — (∃q)(q fini et p = Card(d × q)) — et non
    la forme opaque `divise` : c'est elle qui porte le contenu arithmétique.

    🔴 LA GARDE `est_fini(d)` N'EST PAS COSMÉTIQUE — défaut mesuré le 5 août 2026.
    Sans elle, le (∀d) parcourt TOUS LES ENSEMBLES, et non les entiers.  Or
    `divise_propre(d, p)` ne regarde que `Card(d)` : elle a un sens pour un `d`
    qui n'est pas un cardinal.  L'énoncé non gardé affirmait donc que *tout
    ensemble à deux éléments EST le τ-terme du cardinal 1 ou celui du cardinal 2*
    — ce qui n'est pas de l'arithmétique, et rendait `est_premier(2)`
    indémontrable pour une raison qui n'a rien à voir avec la primalité.
    Mesuré : `⊢ est_premier(2) ⇒ (∀S)( Card S = 2 ⇒ (S = 1 ou S = 2) )`, clos.

    ⚠️ Le liant `q` de la divisibilité doit rester FRAIS d'un appel à l'autre :
    deux primalités imbriquées sur le même liant entreraient en collision (piège
    récurrent du projet, cf. le playbook des collisions de liants)."""
    vd, vp = var(d), p
    return et(non(egal(vp, un())),
              pourtout(d, impl(et(est_fini(vd), divise_propre(vd, vp, q=q)),
                               _ou(egal(vd, un()), egal(vd, vp)))))


def goldbach(n="ngb", k="kgb", p="pgb", pp="qgb"):
    """(∀n)( (n fini et n pair et n ≠ 0 et n ≠ 2) ⇒ (∃p)(∃p')( p,p' premiers
    et n = p+p' ) ).

    « n pair » s'écrit (∃k)(n = k + k), sans avoir besoin de la division : c'est
    la forme la plus économique sur la somme cardinale.

    ────────────────────────────────────────────────────────────────────────────
    🔴 DEUX CONJOINTS AJOUTÉS LE 6 AOÛT 2026.  Sans eux l'énoncé était **FAUX** —
    deux fois, et pour deux raisons différentes.  Ce n'étaient pas des difficultés
    de preuve : c'était une conjecture qui disait autre chose que la conjecture.

    (1) `n ≠ 0` — DÉFAUT DÉMONTRÉ DANS LE NOYAU, clos et sans hypothèse :

            ⊢ pair( N(0) )       (témoin k := 0, car ⊢ 0 + 0 = 0)
            ⊢ ¬( N(0) = 2 )      (par ⊢ 1 + 1 = N(2) et ⊢ ¬( N(0) = N(2) ))

        L'antécédent était donc satisfait en 0, et l'énoncé affirmait que **0 est
        somme de deux nombres premiers**.  Le test de régression le redémontre.

    (2) `est_fini(n)` — DÉFAUT ÉGALEMENT DÉMONTRÉ, clos et sans hypothèse, dans
        `outils_ia/conjectures/defaut_infini.py`.  `pair(n)` force n à être un
        CARDINAL — n = Card(k⊔k) — mais nullement un ENTIER.  En posant
        n := ℕ + ℕ, qui est infini :

            ⊢ pair( ℕ+ℕ )     (témoin ℕ : réflexivité, puis S5)
            ⊢ ¬( ℕ+ℕ = 0 )    (sinon ℵ₀ ≤ 0 donc ℵ₀ = 0, qui est fini)
            ⊢ ¬( ℕ+ℕ = 2 )    (sinon ℵ₀ ≤ 2, et `enum` ne laisse que des finis)

        et cette conjonction EST l'ancien antécédent instancié en n — l'égalité de
        formules est vérifiée, pas supposée.  L'énoncé affirmait donc aussi que
        **ℕ+ℕ est somme de deux nombres premiers**.
        ⚠️ Il n'a fallu ni Hessenberg ni a + a = a : en posant n := a+a la parité
        est vraie par construction.  Chercher le bon TÉMOIN avant le lemme général.
        ⚠️ C'est EXACTEMENT la faute déjà corrigée le 5 août sur `est_premier`
        (garde `est_fini(d)`) : un (∀) posé sur les ensembles quand on croyait le
        poser sur les entiers.  Faite deux fois — donc à chercher SYSTÉMATIQUEMENT
        sur tout quantificateur d'un énoncé arithmétique.

    ────────────────────────────────────────────────────────────────────────────
    ⚠️ ET CE N'EST PAS « ADAPTER L'ÉNONCÉ À LA PREUVE ».  La conjecture classique
    porte sur les ENTIERS pairs **strictement supérieurs à 2** ; pour un entier
    pair, cet ensemble est exactement le complémentaire de {0, 2}.  Les anciennes
    rédactions admettaient 0 et les cardinaux infinis par accident de
    transcription.  On restaure le domaine visé — on ne rétrécit pas un énoncé
    pour le rendre démontrable.  Le critère est la DIRECTION de la justification :
    vers la preuve (interdit), vers la source (obligatoire).

    ⚠️ La forme par exclusion (n ≠ 0 et n ≠ 2) est préférée à « 2 < n » pour ne pas
    faire entrer la relation d'ordre dans un module qui ne porte QUE l'énoncé.

    Rend une `Formule`, jamais un `Theoreme` : cet énoncé n'est pas démontré."""
    vn, vk, vp, vpp = var(n), var(k), var(p), var(pp)
    pair = existe(k, egal(vn, somme_cardinale_binaire(vk, vk)))
    decomposable = existe(p, existe(pp,
        et(et(est_premier(vp, d="d1", q="q1"), est_premier(vpp, d="d2", q="q2")),
           egal(vn, somme_cardinale_binaire(vp, vpp)))))
    ante = et(et(et(est_fini(vn), pair), non(egal(vn, zero()))),
              non(egal(vn, deux())))
    return pourtout(n, impl(ante, decomposable))


__all__ = ["zero", "un", "deux", "est_premier", "goldbach"]
