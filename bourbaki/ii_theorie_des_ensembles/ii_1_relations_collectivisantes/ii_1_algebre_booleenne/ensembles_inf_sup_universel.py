"""§II.1 — PROPRIÉTÉS UNIVERSELLES de ∩ (borne inf) et ∪ (borne sup) BINAIRES.

Bourbaki, Résumé des résultats, E.R.5 nº14 i) (lecture ordinale de l'algèbre des
parties, Chap II.1 ; treillis (∪, ∩) des parties) :

    « Z ⊂ X et Z ⊂ Y » est équivalente à  Z ⊂ X∩Y ;
    « X ⊂ Z et Y ⊂ Z » est équivalente à  X∪Y ⊂ Z.

Autrement dit : dans le treillis des parties ordonné par ⊂,
  • X∩Y est la BORNE INFÉRIEURE de {X, Y} : Z minore X et Y  ⟺  Z ⊂ X∩Y ;
  • X∪Y est la BORNE SUPÉRIEURE de {X, Y} : X et Y majorés par Z  ⟺  X∪Y ⊂ Z.
Ce sont les propriétés UNIVERSELLES (caractérisation du inf / du sup) de ∩ / ∪.

DEUX théorèmes CLOS (0 hypothèse) : les implications internes sont déchargées par
loi_deduction (les inclusions « ⊂ » sont des relations, PAS des hypothèses), donc
est_clos == True pour les deux.  Algèbre des parties PURE : aucun schéma S8, aucune
théorie dédiée ; les seuls axiomes ensemblistes utilisés sont AXIOME_INTER /
AXIOME_REUNION (membres des 22 axiomes de theorie_ensembles()), réinjectés via les
caractérisations d'appartenance EXISTANTES `_instance_intersection` /
`_instance_reunion` (ensembles_theoremes) — non re-dérivées ici.

STRATÉGIE (les deux sont des équivalences ⇔ = conjonction des deux implications) :
  • inf (∩) : ⇒ assume (Z⊂X et Z⊂Y) ; pour z∈Z : z∈X et z∈Y, recoller via
      equivalence_arriere(_instance_intersection) ⟹ z∈X∩Y ; generalisation ⟹
      Z⊂X∩Y ; décharger ⟹ implication.  ⇐ assume Z⊂X∩Y ; pour z∈Z : z∈X∩Y ⟹
      (z∈X et z∈Y) (equivalence_avant), projeter ⟹ Z⊂X et Z⊂Y.
  • sup (∪) : ⇒ assume (X⊂Z et Y⊂Z) ; pour z∈X∪Y : (z∈X ou z∈Y) (equivalence_avant
      _instance_reunion), `cas` z∈X→z∈Z / z∈Y→z∈Z ⟹ z∈Z ; generalisation ⟹ X∪Y⊂Z.
      ⇐ assume X∪Y⊂Z ; pour z∈X : z∈X ⟹ z∈X∪Y (s2 + equivalence_arriere) ⟹ z∈Z
      (X∪Y⊂Z) ⟹ X⊂Z ; idem Y⊂Z (injection à droite via s2/s3).

INVARIANTS : est_clos == True (les DEUX, 0 hypothèse) ; conclusion == cible (==
structurelle, l'équivalence Bourbaki) ; PAS de tautologie déguisée (contenu réel :
caractérisation via ∩ / ∪) ; theorie_ensembles() INCHANGÉE = 22 ; aucun axiome
ajouté, aucune théorie dédiée / S8.

NB — une version FAMILLES (inf/sup universel d'une famille (X_ι)) existe déjà dans
ii_4 : ensembles_inter_inf_univ_ii4.py / ensembles_reunion_sup_univ_ii4.py.  On ne
spécialise PAS celle-ci (famille à 2 éléments = plus lourde) ; on prouve DIRECTEMENT
au niveau binaire, comme dans le Résumé E.R.5.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, appartient, et, ou, equiv, inclus)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_theoremes import (
    _instance_intersection, _instance_reunion)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege import syllogisme
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, instancie, cas,
)


def _t(x):
    return x if isinstance(x, Terme) else var(x)


def _oui_g(a, b):
    """⊢ A ⇒ (A∨B)   (injection à gauche dans la disjonction)."""
    return N.s2(a, b)


def _oui_d(a, b):
    """⊢ B ⇒ (A∨B)   (injection à droite : B⇒(B∨A)⇒(A∨B))."""
    return syllogisme(N.s2(b, a), N.s3(b, a))


def cible_inf_universel_binaire(x="X", y="Y", z="Z"):
    """L'énoncé Bourbaki visé : (Z⊂X et Z⊂Y) ⇔ Z⊂X∩Y   (E.R.5 nº14 i, 1er membre)."""
    vX, vY, vZ = _t(x), _t(y), _t(z)
    return equiv(et(inclus(vZ, vX), inclus(vZ, vY)),
                 inclus(vZ, E.intersection(vX, vY)))


def cible_sup_universel_binaire(x="X", y="Y", z="Z"):
    """L'énoncé Bourbaki visé : (X⊂Z et Y⊂Z) ⇔ X∪Y⊂Z   (E.R.5 nº14 i, 2nd membre)."""
    vX, vY, vZ = _t(x), _t(y), _t(z)
    return equiv(et(inclus(vX, vZ), inclus(vY, vZ)),
                 inclus(E.reunion(vX, vY), vZ))


# @livre Ch.R §1 Prop.14i | E.R.5 L.11-11 | PDF p.308
def inf_universel_binaire(x="X", y="Y", z="Z"):
    """⊢ ( (Z⊂X et Z⊂Y) ⇔ Z⊂X∩Y ).   (E.R.5 nº14 i ; ∩ = borne inférieure.)

    Théorème CLOS (0 hypothèse) : Z minore X et Y  ⟺  Z ⊂ X∩Y.  C'est la propriété
    universelle de l'intersection binaire (plus grand minorant) dans le treillis ⊂."""
    vX, vY, vZ, vz = _t(x), _t(y), _t(z), var("z")
    zX, zY, zZ = appartient(vz, vX), appartient(vz, vY), appartient(vz, vZ)
    inter = E.intersection(vX, vY)
    gauche = et(inclus(vZ, vX), inclus(vZ, vY))           # Z⊂X et Z⊂Y
    droite = inclus(vZ, inter)                            # Z ⊂ X∩Y

    # ── sens ⇒ : (Z⊂X et Z⊂Y) ⇒ Z⊂X∩Y ───────────────────────────────────────
    hG = N.assume(gauche)
    zZ_zX = instancie(conjonction_elim_gauche(hG), vz)    # {G} ⊢ z∈Z ⇒ z∈X
    zZ_zY = instancie(conjonction_elim_droite(hG), vz)    # {G} ⊢ z∈Z ⇒ z∈Y
    hzZ = N.assume(zZ)                                    # z∈Z
    membre = conjonction_intro(N.modus_ponens(hzZ, zZ_zX),  # z∈X
                               N.modus_ponens(hzZ, zZ_zY))  # z∈Y  ⟹ (z∈X et z∈Y)
    z_inter = N.modus_ponens(membre,
                             equivalence_arriere(_instance_intersection(vX, vY, vz)))  # z∈X∩Y
    incl_G = N.generalisation("z", N.loi_deduction(zZ, z_inter))   # {G} ⊢ Z⊂X∩Y
    sens_avant = N.loi_deduction(gauche, incl_G)          # ⊢ (Z⊂X et Z⊂Y) ⇒ Z⊂X∩Y

    # ── sens ⇐ : Z⊂X∩Y ⇒ (Z⊂X et Z⊂Y) ───────────────────────────────────────
    hD = N.assume(droite)                                 # Z⊂X∩Y
    hzZ2 = N.assume(zZ)                                   # z∈Z
    z_dans_inter = N.modus_ponens(hzZ2, instancie(hD, vz))  # {D,z∈Z} ⊢ z∈X∩Y
    et_xy = N.modus_ponens(z_dans_inter,
                           equivalence_avant(_instance_intersection(vX, vY, vz)))  # (z∈X et z∈Y)
    inclZX = N.generalisation("z", N.loi_deduction(
        zZ, conjonction_elim_gauche(et_xy)))              # {D} ⊢ Z⊂X
    inclZY = N.generalisation("z", N.loi_deduction(
        zZ, conjonction_elim_droite(et_xy)))              # {D} ⊢ Z⊂Y
    sens_arriere = N.loi_deduction(droite,
                                   conjonction_intro(inclZX, inclZY))   # ⊢ Z⊂X∩Y ⇒ (Z⊂X et Z⊂Y)

    return conjonction_intro(sens_avant, sens_arriere)    # ⊢ (Z⊂X et Z⊂Y) ⇔ Z⊂X∩Y


# @livre Ch.R §1 Prop.14i | E.R.5 L.12-12 | PDF p.308
def sup_universel_binaire(x="X", y="Y", z="Z"):
    """⊢ ( (X⊂Z et Y⊂Z) ⇔ X∪Y⊂Z ).   (E.R.5 nº14 i ; ∪ = borne supérieure.)

    Théorème CLOS (0 hypothèse) : X et Y majorés par Z  ⟺  X∪Y ⊂ Z.  C'est la
    propriété universelle de la réunion binaire (plus petit majorant) dans (⊂)."""
    vX, vY, vZ, vz = _t(x), _t(y), _t(z), var("z")
    zX, zY, zZ = appartient(vz, vX), appartient(vz, vY), appartient(vz, vZ)
    reun = E.reunion(vX, vY)
    gauche = et(inclus(vX, vZ), inclus(vY, vZ))           # X⊂Z et Y⊂Z
    droite = inclus(reun, vZ)                             # X∪Y ⊂ Z

    # ── sens ⇒ : (X⊂Z et Y⊂Z) ⇒ X∪Y⊂Z ───────────────────────────────────────
    hG = N.assume(gauche)
    zX_zZ = instancie(conjonction_elim_gauche(hG), vz)    # {G} ⊢ z∈X ⇒ z∈Z
    zY_zZ = instancie(conjonction_elim_droite(hG), vz)    # {G} ⊢ z∈Y ⇒ z∈Z
    membre_Z = cas(N.assume(ou(zX, zY)), zX_zZ, zY_zZ)    # {z∈X∨z∈Y} ⊢ z∈Z
    z_reun_to_zZ = syllogisme(
        equivalence_avant(_instance_reunion(vX, vY, vz)),  # z∈X∪Y ⇒ (z∈X∨z∈Y)
        N.loi_deduction(ou(zX, zY), membre_Z))            # (z∈X∨z∈Y) ⇒ z∈Z
    incl_G = N.generalisation("z", z_reun_to_zZ)          # {G} ⊢ X∪Y⊂Z
    sens_avant = N.loi_deduction(gauche, incl_G)          # ⊢ (X⊂Z et Y⊂Z) ⇒ X∪Y⊂Z

    # ── sens ⇐ : X∪Y⊂Z ⇒ (X⊂Z et Y⊂Z) ───────────────────────────────────────
    hD = N.assume(droite)                                 # X∪Y⊂Z
    z_reun_zZ = instancie(hD, vz)                         # {D} ⊢ z∈X∪Y ⇒ z∈Z
    inj_X = syllogisme(_oui_g(zX, zY),                    # z∈X ⇒ (z∈X∨z∈Y)
                       equivalence_arriere(_instance_reunion(vX, vY, vz)))  # ⇒ z∈X∪Y
    inj_Y = syllogisme(_oui_d(zX, zY),                    # z∈Y ⇒ (z∈X∨z∈Y)
                       equivalence_arriere(_instance_reunion(vX, vY, vz)))  # ⇒ z∈X∪Y
    inclXZ = N.generalisation("z", syllogisme(inj_X, z_reun_zZ))   # {D} ⊢ X⊂Z
    inclYZ = N.generalisation("z", syllogisme(inj_Y, z_reun_zZ))   # {D} ⊢ Y⊂Z
    sens_arriere = N.loi_deduction(droite,
                                   conjonction_intro(inclXZ, inclYZ))  # ⊢ X∪Y⊂Z ⇒ (X⊂Z et Y⊂Z)

    return conjonction_intro(sens_avant, sens_arriere)    # ⊢ (X⊂Z et Y⊂Z) ⇔ X∪Y⊂Z


__all__ = ["inf_universel_binaire", "sup_universel_binaire",
           "cible_inf_universel_binaire", "cible_sup_universel_binaire"]
