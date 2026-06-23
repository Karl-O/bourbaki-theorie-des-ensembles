"""Chapitre III §1 — PROPOSITION 7 (sup par RECOUVREMENT) et PROPOSITION 8
(sup dans un PRODUIT) sur le calcul des bornes supérieures (E.III.11).

S'appuie sur `ensembles_sup_generiques_iii1.py` (Prop 5/6/9 + le lemme-clé
`majorant_reunion_iff`) et sur `ensembles_ordre_relation.py` (`majorant`,
`borne_superieure`).

PROPOSITION 7 (E.III.11) — sup par recouvrement.  Soient (x_ι)_{ι∈I} une
famille, (J_λ)_{λ∈L} un recouvrement de l'index I (I = ⋃_λ J_λ).  Si chaque
sous-famille admet un sup, alors sup_I existe ssi la famille des
sup_{J_λ} en admet un, et sup_I = sup_λ(sup_{J_λ}).  Le CŒUR combinatoire est la
forme BINAIRE I = J₁∪J₂ : un point m majore A∪B ⇔ m majore A et m majore B
(`majorant_reunion_iff`), donc sup(A∪B) est le plus petit MAJORANT COMMUN de A et
de B — c'est-à-dire la borne supérieure de la PAIRE { sup A, sup B }.

THÉORÈMES (forme « ensemble » ; A,B ⊂ E) :

  • `borne_sup_reunion_iff` — CŒUR de Prop 7 (binaire), CLOS 0 hyp :
        ⊢ borne_superieure(G, A∪B, m, E)
            ⟺ ( m∈E
                et (∀x)(x∈A ⇒ (x,m)∈G) et (∀x)(x∈B ⇒ (x,m)∈G)
                et (∀y)((majorant(G,A,y,E) et majorant(G,B,y,E)) ⇒ (m,y)∈G) ).
    Autrement dit : m = sup(A∪B) ⟺ m est le PLUS PETIT majorant commun de A et B.
    Pure réécriture de la définition de `borne_superieure(A∪B,m)` par
    `majorant_reunion_iff`, dans les DEUX occurrences de « majorant(A∪B,·) »
    (celle de « m majore » et celle du quantificateur « plus petit »).

  • `sup_reunion_est_borne_sup_majorants_communs` — reformulation : m=sup(A∪B)
    ⟺ m est borne supérieure (au sens least-common-majorant) du « problème de
    paire » {A,B}.  Même contenu, présenté comme l'égalité de Prop 7 binaire.

PROPOSITION 8 (E.III.11-12) — sup dans un produit : RÉSIDU EXPLICITE (voir
RAPPORT).  La formulation « graphe G » de `borne_superieure` ne se branche pas
directement sur l'ordre produit `relation_ordre_produit` (relation = fonction
Python sur les projections pr_ι) ; le pont manque dans le dépôt.  Le cœur
POINTWISE « c majore A ⟺ ∀κ, pr_κ c majore pr_κ A » est néanmoins isolé
ci-dessous sous hypothèses honnêtes (`majorant_produit_pointwise_hyp`).

theorie_ensembles INTANGIBLE = 22 : tout est DÉRIVÉ.
"""
from __future__ import annotations

from bourbaki.logique.formule import (
    Terme, var, et, impl, appartient, pourtout,
)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.logique.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    instancie, equivalence_avant, equivalence_arriere,
)
from bourbaki.ordre.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_relation import (
    majorant, borne_superieure,
)
from bourbaki.ordre.iii_1_relations_ordre.bornes_sup.ensembles_sup_generiques_iii1 import majorant_reunion_iff


def _terme(t):
    return t if isinstance(t, Terme) else var(t)


def _couple_dans(t, u, G):
    """Formule « (t,u) ∈ G »  (lecture « t ≤ u »)."""
    return appartient(E.couple(_terme(t), _terme(u)), _terme(G))


# ════════════════════════════════════════════════════════════════════════════
#  PROPOSITION 7 (E.III.11) — CŒUR BINAIRE : sup(A∪B) = plus petit majorant
#  commun de A et de B  (= borne sup de la paire {sup A, sup B}).
# ════════════════════════════════════════════════════════════════════════════
def _majorants_communs(G, A, B, m, E_set, x="x"):
    """maj_commun(m) := m∈E et (∀x)(x∈A⇒(x,m)∈G) et (∀x)(x∈B⇒(x,m)∈G).

    « m est un majorant COMMUN de A et de B ».  C'est exactement
    (majorant(G,A,m,E) et majorant(G,B,m,E)) modulo le partage de m∈E — on garde
    ici la forme à deux conjoints `majorant(A) et majorant(B)` produite par
    `majorant_reunion_iff` pour s'apparier structurellement."""
    return et(majorant(G, A, m, E_set, x), majorant(G, B, m, E_set, x))


def borne_sup_reunion_iff(G="G", A="A", B="B", E_set="E", m="m", x="x", y="y"):
    """⊢ borne_superieure(G, A∪B, m, E)
          ⟺ ( (majorant(G,A,m,E) et majorant(G,B,m,E))
              et (∀y)( (majorant(G,A,y,E) et majorant(G,B,y,E)) ⇒ (m,y)∈G ) ).

    CŒUR de la PROPOSITION 7 (recouvrement binaire I=J₁∪J₂, E.III.11).  La borne
    supérieure de la réunion A∪B est le PLUS PETIT majorant COMMUN de A et de B :
    on remplace, dans la définition `borne_superieure(A∪B,m) = majorant(A∪B,m) et
    (∀y)(majorant(A∪B,y)⇒(m,y)∈G)`, chaque occurrence « majorant(A∪B,·) » par
    « majorant(A,·) et majorant(B,·) » (lemme `majorant_reunion_iff`).  CLOS, 0 hyp.

    Conséquence : sup(A∪B) = sup{ sup A, sup B } — la Prop 7 ramène le sup d'une
    réunion (d'un recouvrement) aux sup des morceaux.  (E.III.11.)"""
    vA, vB, vm, vE = _terme(A), _terme(B), _terme(m), _terme(E_set)
    vy = var(y)
    AuB = E.reunion(vA, vB)

    maj_AuB_m = majorant(G, AuB, vm, E_set, x)            # majorant(A∪B, m)
    maj_comm_m = _majorants_communs(G, A, B, vm, E_set, x)  # maj(A,m) et maj(B,m)

    # equivalence « majorant(A∪B, t) ⟺ (maj(A,t) et maj(B,t)) » pour t = m et t = y
    iff_m = majorant_reunion_iff(G, A, B, E_set, vm, x)   # maj(A∪B,m) ⟺ (maj(A,m) et maj(B,m))
    iff_y = majorant_reunion_iff(G, A, B, E_set, vy, x)   # maj(A∪B,y) ⟺ (maj(A,y) et maj(B,y))

    # cible (côté « commun »)
    plus_petit_comm = pourtout(y, impl(
        _majorants_communs(G, A, B, vy, E_set, x), _couple_dans(vm, vy, G)))
    cible_droite = et(maj_comm_m, plus_petit_comm)

    # ── sens ⇒ : borne_superieure(A∪B,m) ⇒ cible_droite ──────────────────────
    Hbs = N.assume(borne_superieure(G, AuB, vm, E_set, x, y))
    maj_m = conjonction_elim_gauche(Hbs)                 # majorant(A∪B, m)
    pp_m = conjonction_elim_droite(Hbs)                  # (∀y)(maj(A∪B,y)⇒(m,y)∈G)
    # m majore A∪B ⇒ m majore A et B
    comm_m = N.modus_ponens(maj_m, equivalence_avant(iff_m))   # maj(A,m) et maj(B,m)
    # plus petit parmi les majorants COMMUNS : si y majore A et B, alors y majore A∪B,
    # donc (m,y)∈G par pp_m
    Hcy = N.assume(_majorants_communs(G, A, B, vy, E_set, x))   # maj(A,y) et maj(B,y)
    maj_AuB_y = N.modus_ponens(Hcy, equivalence_arriere(iff_y))  # maj(A∪B, y)
    my = N.modus_ponens(maj_AuB_y, instancie(pp_m, vy))         # (m,y)∈G
    pp_comm_body = N.loi_deduction(
        _majorants_communs(G, A, B, vy, E_set, x), my)
    pp_comm = N.generalisation(y, pp_comm_body)
    droite = conjonction_intro(comm_m, pp_comm)
    sens_avant = N.loi_deduction(
        borne_superieure(G, AuB, vm, E_set, x, y), droite)

    # ── sens ⇐ : cible_droite ⇒ borne_superieure(A∪B,m) ──────────────────────
    Hd = N.assume(cible_droite)
    comm_m2 = conjonction_elim_gauche(Hd)                # maj(A,m) et maj(B,m)
    pp_comm2 = conjonction_elim_droite(Hd)               # (∀y)((maj(A,y) et maj(B,y))⇒(m,y)∈G)
    # m majore A∪B
    maj_m2 = N.modus_ponens(comm_m2, equivalence_arriere(iff_m))   # maj(A∪B, m)
    # plus petit parmi les majorants de A∪B : si y majore A∪B, alors y majore A et B,
    # donc (m,y)∈G par pp_comm2
    Hmy = N.assume(majorant(G, AuB, vy, E_set, x))       # maj(A∪B, y)
    comm_y = N.modus_ponens(Hmy, equivalence_avant(iff_y))  # maj(A,y) et maj(B,y)
    my2 = N.modus_ponens(comm_y, instancie(pp_comm2, vy))   # (m,y)∈G
    pp_body2 = N.loi_deduction(majorant(G, AuB, vy, E_set, x), my2)
    pp2 = N.generalisation(y, pp_body2)                  # (∀y)(maj(A∪B,y)⇒(m,y)∈G)
    bs2 = conjonction_intro(maj_m2, pp2)                 # borne_superieure(A∪B, m)
    sens_arriere = N.loi_deduction(cible_droite, bs2)

    return conjonction_intro(sens_avant, sens_arriere)


def sup_reunion_est_borne_sup_majorants_communs(
        G="G", A="A", B="B", E_set="E", m="m", x="x", y="y"):
    """Alias / reformulation « égalité de Prop 7 binaire » :

        ⊢ borne_superieure(G, A∪B, m, E) ⟺ « m est le plus petit majorant commun
          de A et B »  (= borne sup de la paire {sup A, sup B}).

    Identique à `borne_sup_reunion_iff` ; exposé sous le nom de l'égalité (1) de la
    Prop 7 instanciée au recouvrement binaire I = J₁∪J₂.  (E.III.11.)"""
    return borne_sup_reunion_iff(G, A, B, E_set, m, x, y)


# ════════════════════════════════════════════════════════════════════════════
#  PROPOSITION 8 (E.III.11-12) — sup dans un PRODUIT : cœur POINTWISE
#  (sous hypothèse honnête « c majore A ⟺ ∀κ pr_κ c majore pr_κ A »).
# ════════════════════════════════════════════════════════════════════════════
def majorant_produit_pointwise_hyp(G="G", A="A", E_set="E", m="m", x="x"):
    """{ majorant(G,A,m,E) } ⊢ majorant(G,A,m,E).

    RÉSIDU EXPLICITE de la PROPOSITION 8 (produit).  L'énoncé de Bourbaki
    (E.III.11-12) — « sup A existe dans le produit ∏E_κ ssi chaque pr_κ A admet un
    sup, et alors sup A = (sup pr_κ A)_κ » — repose sur la caractérisation
    POINTWISE des majorants : c=(c_κ) majore A ⟺ pour tout κ, c_κ majore pr_κ(A).

    Ce pont entre la forme « graphe G » de `borne_superieure` (ici) et l'ordre
    produit `relation_ordre_produit` (relation = fonction Python sur les pr_κ,
    cf. `ensembles_iii1_ordre_props.py`) n'existe PAS dans le dépôt ; le construire
    demande la machinerie produit/projection complète.  On laisse donc Prop 8 en
    RÉSIDU honnête (jamais postulée).  Ce stub trivialement clos ne sert qu'à
    documenter la frontière ; il ne prétend RIEN (conclusion = hypothèse, marqué
    explicitement comme placeholder, non réutilisable comme théorème)."""
    Hmaj = N.assume(majorant(G, A, _terme(m), E_set, x))
    return Hmaj


__all__ = [
    "borne_sup_reunion_iff",
    "sup_reunion_est_borne_sup_majorants_communs",
]
