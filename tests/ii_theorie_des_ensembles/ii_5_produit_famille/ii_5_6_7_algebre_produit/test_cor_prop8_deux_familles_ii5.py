"""§II.5 — COROLLAIRE de la PROPOSITION 8, première formule (1), E II.36 :
    (∃i)(i∈I) ⇒ ( (∃i)(i∈K) ⇒
        ( ⋂_{ι∈I} X_ι ) ∪ ( ⋂_{κ∈K} Y_κ )  =  ⋂_{(ι,κ)∈I×K} ( X_ι ∪ Y_κ ) ).

ÉGALITÉ PLEINE (deux sens), SANS choix (cas L={1,2}).  Le test APPELLE le théorème
et vérifie : conclusion == cible reconstruite INDÉPENDAMMENT avec les constructeurs
E.* (réunion binaire ∪, intersections de familles, produit cartésien I×K, famille Z),
clôture (0 hyp), et theorie_ensembles() == 22 axiomes.

MISE À JOUR (2026-07-26) — MIGRATION « ⋂ = sélection dans ⋃ ».  Ces tests encodaient
l'égalité SANS hypothèse (`egal(gauche, droite)` nu, et `c.tag == "="`).  Cet énoncé
n'était démontrable que via l'ANCIEN AXIOME_INTER_FAM, qui était CONTRADICTOIRE (il
peuplait ⋂ sur un ensemble d'indices vide de tout objet).  Avec l'axiome réparé
l'égalité est FAUSSE dès qu'un des deux ensembles d'indices est vide — contre-exemple
I = ∅, K ≠ ∅ : ⋂_{ι∈∅}X_ι = ∅ donc le membre gauche vaut ⋂_{κ∈K}Y_κ, qui n'a aucune
raison d'être vide, tandis que I×K = ∅ rend le membre droit ⋂_{p∈∅}Z_p = ∅.  L'énoncé
porte donc désormais les deux antécédents « ensembles d'indices non vides », que le
corollaire écrit noir sur blanc à sa première ligne (E II.36 L.15).  C'est un
RENFORCEMENT D'ÉNONCÉ, donc un GAIN de fidélité au livre : le test suit l'énoncé,
pas l'inverse.  RIEN n'a été retiré du verrou — les deux membres de l'égalité sont
toujours comparés terme à terme, on PÈLE simplement les antécédents avant.
"""
from bourbaki.ii_theorie_des_ensembles.ii_5_produit_famille.ii_5_6_7_algebre_produit import (
    ensembles_cor_prop8_deux_familles_ii5 as M)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_intersection_fondation.ensembles_inter_migration_ii4 import (
    indices_non_vides, inter_famille_vide_egale_vide)
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, egal, impl


def _membres_independants():
    """(gauche, droite) reconstruits à la main avec les MÊMES constructeurs E.* que
    la fonction (Z = famille externe sur I×K définie par `theorie_cor_distrib`)."""
    vXX, vYY, vZ, vI, vK = var("XX"), var("YY"), var("Z"), var("I"), var("K")
    gauche = E.reunion(E.inter_famille(vXX, vI), E.inter_famille(vYY, vK))
    droite = E.inter_famille(vZ, E.produit(vI, vK))
    return gauche, droite


def _cible_independante():
    """(∃i)(i∈I) ⇒ ( (∃i)(i∈K) ⇒ ( ⋂_{ι∈I}X_ι )∪( ⋂_{κ∈K}Y_κ ) = ⋂_{(ι,κ)∈I×K}( X_ι∪Y_κ ) ).

    Les deux antécédents sont l'hypothèse « ensembles d'indices non vides » du
    corollaire (cf. docstring du module) : sans eux l'égalité est fausse."""
    gauche, droite = _membres_independants()
    return impl(indices_non_vides(var("I")),
                impl(indices_non_vides(var("K")), egal(gauche, droite)))


def test_cor_distributivite_deux_familles_close():
    th = M.cor_distributivite_inter_reunion_deux_familles()
    # clôture : 0 hypothèse pendante — les deux hypothèses d'indices sont DÉCHARGÉES
    # en antécédents (loi de déduction), elles ne restent pas au compteur.
    assert th.est_clos is True
    assert th.hypotheses == frozenset()
    # conclusion == cible (construction indépendante avec E.*)
    assert th.conclusion == _cible_independante()
    assert th.conclusion == M._cible()
    # invariant : théorie des ensembles inchangée (22 axiomes)
    assert len(E.theorie_ensembles().axiomes) == 22


def test_cible_est_une_egalite():
    """Sous les deux antécédents, la cible est bien l'égalité gauche = droite.

    VERROU D'ORIGINE (pré-migration) : `th.conclusion.tag == "="` et les deux membres.
    L'égalité vit maintenant sous deux antécédents — on les pèle (impl(P,Q) = ou(¬P,Q),
    le conséquent est le 2e sous-terme du « ou ») et on vérifie le MÊME verrou."""
    th = M.cor_distributivite_inter_reunion_deux_familles()
    sous_hyp_I = th.conclusion.sous[1]              # (∃i)(i∈K) ⇒ (gauche = droite)
    c = sous_hyp_I.sous[1]                          # gauche = droite
    assert c.tag == "="
    g, d = c.termes
    assert g == M._membre_gauche()
    assert d == M._membre_droit()


def test_hypotheses_indices_non_vides_sont_les_antecedents():
    """Les hypothèses ajoutées par la migration sont EXACTEMENT (∃i)(i∈I) et (∃i)(i∈K).

    Test neuf : il rend visible, et donc auditable, le RENFORCEMENT d'énoncé — le
    conséquent, lui, est verbatim l'ancienne cible (l'égalité nue)."""
    hyp_I, hyp_K = M._hyp_indices()
    assert hyp_I == indices_non_vides(var("I"))
    assert hyp_K == indices_non_vides(var("K"))
    th = M.cor_distributivite_inter_reunion_deux_familles()
    # impl(P,Q) = ou(¬P, Q) : l'antécédent est sous le ¬, le conséquent à droite
    assert th.conclusion.sous[0].sous[0] == hyp_I
    assert th.conclusion.sous[1].sous[0].sous[0] == hyp_K
    gauche, droite = _membres_independants()
    assert th.conclusion.sous[1].sous[1] == egal(gauche, droite)   # ancienne cible


def test_contre_exemple_indice_vide_est_certifie():
    """L'ingrédient MACHINE du contre-exemple : ⊢ ⋂_{ι∈∅} X_ι = ∅.

    C'est ce théorème (`inter_famille_vide_egale_vide`, II.4.1 Déf. 2 réparée) qui
    rend l'ancienne forme SANS hypothèse réfutable : pour I=∅ il vide le premier
    terme du membre gauche — qui se réduit à ⋂_{κ∈K}Y_κ — pendant que I×K=∅ (Prop. 3,
    E II.8) vide le membre droit.  Sous l'ANCIEN axiome ce même ⋂ contenait TOUT
    objet ; le test verrouille donc la mort de la pathologie qui portait la preuve."""
    th = inter_famille_vide_egale_vide("XX")
    assert th.est_clos is True
    assert th.conclusion == egal(E.inter_famille(var("XX"), E.VIDE), E.VIDE)


def test_theorie_locale_close_et_hors_22():
    """La théorie locale `theorie_cor_distrib` porte l'axiome-schéma C54 de Z et n'entre
    PAS dans theorie_ensembles() ; N.axiome(theorie_locale, AX_Z) reste légitime."""
    th_loc = M.theorie_cor_distrib()
    # un seul axiome-schéma (déf. de Z par son terme sur les couples)
    assert len(th_loc.axiomes) == 1
    # theorie_ensembles() inchangée
    assert len(E.theorie_ensembles().axiomes) == 22
