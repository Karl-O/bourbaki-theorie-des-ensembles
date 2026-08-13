"""§II.5.3 Déf.1 — TÉMOINS SUR {∅} pour le conjoint « graphe » du produit.

Ce module porte les petits lemmes clos sur le témoin S := {∅} qui ont servi à
DIAGNOSTIQUER, puis qui servent à MESURER, le conjoint « F ⊂ I × ⋃X_ι » de la
Définition 1 (E II.32).

────────────────────────────────────────────────────────────────────────────────
HISTOIRE (à conserver — c'est le « pourquoi » du chantier).

Jusqu'au 2026-07-26, `AXIOME_PRODUIT_FAM` encodait la Déf. 1 par ses seuls TROIS
derniers conjoints :

      F ∈ ∏(f,I)  ⇔  ( est_fonctionnel(F)  ∧  dom F = I  ∧  (∀ι)(ι∈I ⇒ F(ι) ∈ X_ι) )

Le conjoint de TÊTE du livre — « F ∈ 𝔓(I × A) », c.-à-d. F est un GRAPHE inclus
dans I × ⋃_{ι∈I} X_ι — avait été perdu à la transcription, alors que l'axiome
frère `axiome_exposant` (F^E, E II.5.2) avait, lui, correctement gardé son
« G ⊂ E×F ».  Or `est_fonctionnel` n'est QUE l'univocité —
(∀u)(∀v)(∀z)( (u,v)∈F ∧ (u,z)∈F ⇒ v=z ) — et ne dit RIEN des éléments de F qui ne
sont pas des couples.

Le témoin de bruit était S := {∅} :
  • S ne contient aucun couple — un couple (a,b) = { {a}, {a,b} } contient {a},
    donc n'est jamais vide — donc `est_fonctionnel(S)` était VRAIE, vacuement
    (`singleton_vide_est_fonctionnel`, toujours démontrée ci-dessous) ;
  • `dom S = ∅` pour la même raison (`dom_singleton_vide_est_vide`) ;
  • la 3ᵉ condition est vide puisque I = ∅.
Le corpus démontrait donc ⊢ {∅} ∈ ∏(u,∅), et de là ⊢ ¬( ∏(u,∅) = {∅} ) — ce qui
CONTREDIT E II.32 : « Si I = ∅, l'ensemble ∏_{ι∈I} X_ι ne possède qu'un seul
élément, savoir l'ensemble vide ».  Défaut de FIDÉLITÉ, pas de soundness.

RÉPARATION (2026-07-26, même journée que celle de `AXIOME_INTER_FAM`).  Le
conjoint du livre a été RÉTABLI EN TÊTE de `AXIOME_PRODUIT_FAM` :

      F ∈ ∏(f,I)  ⇔  ( F ⊂ I × ⋃_{ι∈I} X_ι  ∧  est_fonctionnel(F)
                       ∧  dom F = I  ∧  (∀ι)(ι∈I ⇒ F(ι) ∈ X_ι) )

C'est un REMPLACEMENT, pas un ajout : `theorie_ensembles()` vaut 22 avant comme
après.  Les deux axiomes frères sont désormais littéralement homomorphes.

CE QUI A ÉTÉ SUPPRIMÉ DE CE MODULE, ET POURQUOI C'ÉTAIT OBLIGATOIRE.
`singleton_vide_dans_produit_vide` (⊢ {∅} ∈ ∏(u,∅)) et sa suite
`produit_vide_n_est_pas_singleton` (⊢ ¬(∏(u,∅)={∅})) étaient des théorèmes du
DÉFAUT : ils ne sont plus démontrables et n'ont plus lieu d'être.  Surtout,
`hypothese_graphes_produit_vide_refutee` — qui montrait { H-graphe } ⊢ ∅∈∅ — a dû
DISPARAÎTRE : après réparation H-graphe := (∀F)(F ∈ ∏(u,∅) ⇒ est_un_graphe(F))
est DÉMONTRABLE (cf. `produit_graphe`, ensembles_produit_famille), et coexister
avec sa réfutation rendrait la théorie INCOHÉRENTE.  Leur mort n'est pas un
dommage collatéral : c'est la condition de cohérence de la réparation.

CE QUI REMPLACE LE CONTRE-THÉORÈME.  `singleton_vide_hors_produit_vide` :
      ⊢ ¬( {∅} ∈ ∏(u, ∅) )                                    [CLOS, 0 hyp]
Le bruit est EXCLU : c'est la mesure, dans le formalisme, que le conjoint rétabli
fait son travail — et le corpus cesse de contredire E II.32.

INVARIANT : theorie_ensembles() = 22 avant et après.  Noyau et subst intouchés.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, et, non, appartient,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege import (
    a_implique_a, syllogisme,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, contraposition, instancie,
    equivalence_avant, equivalence_arriere,
)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import (
    existe_elimination,
)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_theoremes import (
    egalite_par_extension, vide_sans_element,
)
from bourbaki.ii_theorie_des_ensembles.ii_2_couples.ii_2_1_definition_couples.ensembles_couples import (
    singleton_membre, membre_paire_gauche,
)

#: Trou EXOTIQUE des congruences de Leibniz de ce module (≠ « w »/« z »/« wpv »).
_TROU = "wpfg"


def _t(t):
    """Coercion str/Terme → Terme."""
    return t if isinstance(t, Terme) else var(t)


def _n_in_vide(t):
    """⊢ ¬(t ∈ ∅)   pour un TERME t quelconque   (instance de AXIOME_VIDE)."""
    return instancie(N.axiome(E.theorie_ensembles(), E.AXIOME_VIDE), t)


def _ex_falso(thm_a, thm_na, cible):
    """Γ⊢A, Δ⊢¬A ⟹ Γ∪Δ⊢Z.   (ex falso : ¬A ⇒ (A ⇒ Z), S2.)"""
    return N.modus_ponens(thm_a, N.modus_ponens(thm_na, N.s2(non(thm_a.conclusion), cible)))


def singleton_vide():
    """S := {∅}  — le témoin : fonctionnel et de domaine ∅, mais PAS un graphe."""
    return E.singleton(E.VIDE)


# @livre Ch.II §2.1 Def.- | E II.7 L.14-14 | PDF p.58  (couple de Kuratowski (a,b) = {{a},{a,b}} : son premier terme {a} en est un élément — d'où « un couple n'est jamais vide »)
def singleton_gauche_dans_couple(a="a", b="b"):
    """⊢ {a} ∈ (a, b).   (1ᵉʳ terme de la paire de Kuratowski ; d'où (a,b) ≠ ∅.)"""
    va, vb = _t(a), _t(b)
    return membre_paire_gauche(E.paire(va, va), E.paire(va, vb))


def _absurde_si_couple_egal_vide(thm_eq, va, vb, cible):
    """{ (a,b) = ∅ } ⊢ cible.   ({a} ∈ (a,b) ; si (a,b)=∅ alors {a} ∈ ∅ : ex falso.)"""
    memb = singleton_gauche_dans_couple(va, vb)
    leib = N.s6(E.couple(va, vb), E.VIDE, _TROU, appartient(E.paire(va, va), var(_TROU)))
    in_vide = N.modus_ponens(memb, equivalence_avant(N.modus_ponens(thm_eq, leib)))
    return _ex_falso(in_vide, _n_in_vide(E.paire(va, va)), cible)


def _absurde_si_couple_dans_S(thm_in, va, vb, cible):
    """{ (a,b) ∈ {∅} } ⊢ cible.   ((a,b)∈{∅} ⇒ (a,b)=∅, puis ci-dessus.)"""
    eq = N.modus_ponens(thm_in, equivalence_avant(singleton_membre(E.couple(va, vb), E.VIDE)))
    return _absurde_si_couple_egal_vide(eq, va, vb, cible)


# @livre Ch.II §5.3 Def.1 | E II.32 L.16-23 | PDF p.83  (pourquoi `est_fonctionnel` seule ne suffit PAS à rendre la Déf. 1 : elle est vacuement vraie sur {∅}, qui ne contient aucun couple)
def singleton_vide_est_fonctionnel():
    """⊢ est_fonctionnel({∅}).   [CLOS, 0 hyp]

    Vacuement : (u,v) ∈ {∅} forcerait (u,v) = ∅, or {u} ∈ (u,v) donc (u,v) ≠ ∅.
    Les liants sont ceux de est_fonctionnel : u, v, z (généralisés z, v, u)."""
    S = singleton_vide()
    vu, vv, vz = var("u"), var("v"), var("z")
    corps = et(appartient(E.couple(vu, vv), S), appartient(E.couple(vu, vz), S))
    h = N.assume(corps)
    v_eq_z = _absurde_si_couple_dans_S(conjonction_elim_gauche(h), vu, vv, egal(vv, vz))
    res = N.generalisation("u", N.generalisation("v", N.generalisation(
        "z", N.loi_deduction(corps, v_eq_z))))
    assert res.conclusion == E.est_fonctionnel(S), \
        "singleton_vide_est_fonctionnel : conclusion ≠ est_fonctionnel({∅})"
    assert res.est_clos, "singleton_vide_est_fonctionnel : non clos"
    return res


# @livre Ch.II §5.3 Def.1 | E II.32 L.16-23 | PDF p.83  (le conjoint « dom F = I » de la Déf. 1 : lui non plus ne contraint pas les éléments non-couples de F)
def dom_singleton_vide_est_vide():
    """⊢ dom({∅}) = ∅.   [CLOS, 0 hyp]

    AXIOME_DOM : z ∈ dom G ⇔ (∃y)((z,y) ∈ G).  Ici (z,y) ∈ {∅} est absurde
    (couple non vide) ; réciproque par ex falso ; extensionnalité (A1)."""
    S = singleton_vide()
    vz, vy = var("z"), var("y")
    inst = instancie(instancie(N.axiome(E.theorie_ensembles(), E.AXIOME_DOM), S), vz)
    corps = appartient(E.couple(vz, vy), S)
    h = N.assume(corps)
    z_in_vide = _absurde_si_couple_dans_S(h, vz, vy, appartient(vz, E.VIDE))
    fwd = syllogisme(equivalence_avant(inst),
                     existe_elimination(N.loi_deduction(corps, z_in_vide), "y"))
    hz = N.assume(appartient(vz, E.VIDE))
    bwd = N.loi_deduction(appartient(vz, E.VIDE),
                          _ex_falso(hz, vide_sans_element("z"), appartient(vz, E.dom(S))))
    char = N.generalisation("z", conjonction_intro(fwd, bwd))
    self_vide = N.generalisation("z", conjonction_intro(
        a_implique_a(appartient(vz, E.VIDE)), a_implique_a(appartient(vz, E.VIDE))))
    res = egalite_par_extension(char, self_vide, E.dom(S), E.VIDE, "z")
    assert res.conclusion == egal(E.dom(S), E.VIDE), \
        "dom_singleton_vide_est_vide : conclusion ≠ dom({∅})=∅"
    assert res.est_clos, "dom_singleton_vide_est_vide : non clos"
    return res


def singleton_vide_different_du_vide():
    """⊢ ¬( {∅} = ∅ ).   ({∅} contient ∅, or ∅ ne contient rien.)"""
    S = singleton_vide()
    vide_in_S = N.modus_ponens(N.reflexivite(E.VIDE),
                               equivalence_arriere(singleton_membre(E.VIDE, E.VIDE)))
    h = N.assume(egal(S, E.VIDE))
    leib = N.s6(S, E.VIDE, _TROU, appartient(E.VIDE, var(_TROU)))
    in_vv = N.modus_ponens(vide_in_S, equivalence_avant(N.modus_ponens(h, leib)))
    imp = N.loi_deduction(egal(S, E.VIDE), in_vv)              # ({∅}=∅) ⇒ (∅∈∅)
    return N.modus_ponens(_n_in_vide(E.VIDE), contraposition(imp))


# @livre Ch.II §5.3 Def.1 | E II.32 L.22-23 | PDF p.83  (« Si I = ∅, l'ensemble ∏_{ι∈I} X_ι ne possède qu'un seul élément, savoir l'ensemble vide » — le bruit {∅} est désormais EXCLU du produit, comme le livre l'exige)
#   ⚠️ CE MARQUEUR A DIT « L.30-33 » : corrigé le 27 juil. 2026 après recomptage des lignes
#   sur la page rendue en PNG (pymupdf, PDF p.83, en-tête « E II.32 » confirmé). La phrase est
#   aux lignes 22-23. `ensembles_produit_famille_vide.py` cite la MÊME phrase et la calait
#   déjà correctement : les deux marqueurs concordent désormais.
def singleton_vide_hors_produit_vide(u="upfg"):
    """🎯 ⊢ ¬( {∅} ∈ ∏_{ι∈∅} X_ι ).   [CLOS, 0 hyp, pour u QUELCONQUE]

    LE MIROIR de l'ancien contre-théorème, et la MESURE que la réparation de
    `AXIOME_PRODUIT_FAM` fait son travail.  {∅} vérifie toujours les trois
    conjoints conservés (fonctionnel, dom = ∅, valeurs vacuement) — c'est
    précisément pourquoi l'ancien encodage l'admettait ; il échoue sur le conjoint
    de TÊTE, car {∅} ⊂ ∅ × ⋃ entraînerait que {∅} est un graphe, donc que ∅ est
    un couple, ce qui est absurde ({a} ∈ (a,b) donc un couple n'est jamais vide).

    PREUVE.  Supposons {∅} ∈ ∏(u,∅).  Le conjoint de tête donne {∅} ⊂ ∅ × ⋃X_ι,
    puis `inclus_produit_est_graphe` (B1) donne est_un_graphe({∅}).  Or ∅ ∈ {∅},
    donc ∅ est un couple ; les témoins éliminés, on obtient ∅ ∈ ∅, réfuté par
    AXIOME_VIDE.  Contraposition."""
    from bourbaki.ii_theorie_des_ensembles.ii_5_produit_famille.ii_5_definitions.ensembles_produit_ecriture import (
        composants_membre, graphe_du_point)
    from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
        symetrie)

    vu, S = _t(u), singleton_vide()
    membre = appartient(S, E.produit_famille(vu, E.VIDE))

    h = N.assume(membre)
    incl = composants_membre(h, vu, E.VIDE, S)[0]                    # {∅} ⊂ ∅×⋃X_ι
    graphe_S = graphe_du_point(incl, S, E.VIDE, vu)                  # est_un_graphe({∅})
    vide_in_S = N.modus_ponens(N.reflexivite(E.VIDE),
                               equivalence_arriere(singleton_membre(E.VIDE, E.VIDE)))
    est_c = N.modus_ponens(vide_in_S, instancie(graphe_S, E.VIDE))   # « ∅ est un couple »

    va, vb = var("x"), var("y")                     # liants de est_un_couple (E.II.31)
    corps = egal(E.VIDE, E.couple(va, vb))
    hc = N.assume(corps)
    eq = N.modus_ponens(hc, symetrie(E.VIDE, E.couple(va, vb)))      # (x,y) = ∅
    faux = _absurde_si_couple_egal_vide(eq, va, vb, appartient(E.VIDE, E.VIDE))
    absurde = N.modus_ponens(est_c, existe_elimination(
        existe_elimination(N.loi_deduction(corps, faux), "y"), "x"))  # {membre} ⊢ ∅∈∅

    res = N.modus_ponens(_n_in_vide(E.VIDE),
                         contraposition(N.loi_deduction(membre, absurde)))
    assert res.conclusion == non(membre), \
        "singleton_vide_hors_produit_vide : conclusion ≠ ¬({∅} ∈ ∏(u,∅))"
    assert res.est_clos, "singleton_vide_hors_produit_vide : non clos"
    return res


__all__ = [
    "singleton_vide", "singleton_gauche_dans_couple", "singleton_vide_est_fonctionnel",
    "dom_singleton_vide_est_vide", "singleton_vide_different_du_vide",
    "singleton_vide_hors_produit_vide",
]
