"""Chapitre III §1 — Théorie ÉLÉMENTAIRE des ensembles ordonnés (graphes d'ordre).

Vue COMPLÉMENTAIRE de `ensembles_ordre.py` (qui travaille avec une relation R
donnée comme fonction Python (x,y)↦Formule).  Ici une relation d'ordre est un
GRAPHE G (ensemble de couples) sur un ensemble E ; les conditions de Bourbaki
(E.III.1.1) s'écrivent comme prédicats sur l'appartenance « (x,y)∈G » :

  reflexivite_sur(G,E) := (∀x)(x∈E ⇒ (x,x)∈G)
  antisymetrie(G)      := (∀x)(∀y)(((x,y)∈G et (y,x)∈G) ⇒ x=y)
  transitivite_rel(G)  := (∀x)(∀y)(∀z)(((x,y)∈G et (y,z)∈G) ⇒ (x,z)∈G)
  est_ordre(G,E)       := reflexivite_sur(G,E) et antisymetrie(G) et transitivite_rel(G)

Théorèmes DIRECTS certifiés par le noyau abrégé (type Theoreme opaque) :

  • Δ_E est un ordre sur E (ordre de l'égalité), E.III.3.1 :
      diagonale_reflexive_sur, diagonale_antisymetrique, diagonale_transitive,
      diagonale_est_ordre.
  • L'inclusion ⊂ est un ordre (sur n'importe quelle « famille » de parties), via
      ⊂ réflexive (inclusion_reflexive), transitive (inclusion_transitive),
      antisymétrique (A1, egalite_par_extension) :
      inclusion_reflexive_sur, inclusion_antisymetrique, inclusion_transitive_rel.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import Terme, var, egal, et, ou, impl, appartient, pourtout, inclus
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.equipotence.ensembles_equipotence import diagonale_membre
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege import a_implique_a, syllogisme
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, instancie, cas,
)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import symetrie, composer_egalites


def _terme(t):
    return t if isinstance(t, Terme) else var(t)


def _couple_dans(t, u, G):
    """Formule « (t,u) ∈ G »."""
    return appartient(E.couple(_terme(t), _terme(u)), _terme(G))


def _cut(thm, hyp, preuve_hyp):
    """Remplace l'hypothèse `hyp` de `thm` par sa preuve `preuve_hyp`.

    De  Γ∪{H} ⊢ C  et  Δ ⊢ H  on déduit  Γ∪Δ ⊢ C  (décharge de H puis MP)."""
    return N.modus_ponens(preuve_hyp, N.loi_deduction(hyp, thm))


# ════════════════════════════════════════════════════════════════════════════
#  DÉFINITIONS — relation d'ordre comme prédicats sur un graphe G (E.III.1.1)
# ════════════════════════════════════════════════════════════════════════════
def reflexivite_sur(G, E_set, x="x"):
    """reflexivite_sur(G,E) := (∀x)(x∈E ⇒ (x,x)∈G).   (réflexivité sur E.)"""
    vx, vE = var(x), _terme(E_set)
    return pourtout(x, impl(appartient(vx, vE), _couple_dans(vx, vx, G)))


def antisymetrie(G, x="x", y="y"):
    """antisymetrie(G) := (∀x)(∀y)(((x,y)∈G et (y,x)∈G) ⇒ x=y).   (E.III.1.1.)"""
    vx, vy = var(x), var(y)
    return pourtout(x, pourtout(y,
        impl(et(_couple_dans(vx, vy, G), _couple_dans(vy, vx, G)), egal(vx, vy))))


def transitivite_rel(G, x="x", y="y", z="z"):
    """transitivite_rel(G) := (∀x)(∀y)(∀z)(((x,y)∈G et (y,z)∈G) ⇒ (x,z)∈G).  (E.III.1.1.)"""
    vx, vy, vz = var(x), var(y), var(z)
    return pourtout(x, pourtout(y, pourtout(z,
        impl(et(_couple_dans(vx, vy, G), _couple_dans(vy, vz, G)),
             _couple_dans(vx, vz, G)))))


# @livre Ch.III §1.1 Def.- | E III.2 L.19-23 | PDF p.105
# @livre Ch.III §1.3 Rem.- | E III.5 L.16-27 | PDF p.108
# (1er marqueur : « ordre sur un ensemble E » = correspondance Γ=(G,E,E) de graphe G ;
#  2ᵉ marqueur : prose « théorie 𝒯, E ensemble ordonné par l'ordre Γ, x≤y := y∈Γ⟨x⟩,
#  ensemble préordonné » + petit texte — prose, rien à formaliser de plus)
def est_ordre(G, E_set, x="x", y="y", z="z"):
    """est_ordre(G,E) := reflexivite_sur(G,E) et antisymetrie(G) et transitivite_rel(G).

    « G est le graphe d'une relation d'ordre sur l'ensemble E »  (E.III.1.1)."""
    return et(et(reflexivite_sur(G, E_set, x), antisymetrie(G, x, y)),
              transitivite_rel(G, x, y, z))


# @livre Ch.III §1.12 Def.9 | E III.13 L.31-34 | PDF p.116
def totalement_ordonne(G, E_set, x="x", y="y", z="z"):
    """totalement_ordonne(G,E) := est_ordre(G,E) et
        (∀x)(∀y)((x∈E et y∈E) ⇒ ((x,y)∈G ou (y,x)∈G)).

    « G est le graphe d'un ordre TOTAL sur E » : deux éléments quelconques de E
    sont toujours comparables.  (E.III.1.12, Définition 11.)"""
    vx, vy, vE = var(x), var(y), _terme(E_set)
    comparables = pourtout(x, pourtout(y,
        impl(et(appartient(vx, vE), appartient(vy, vE)),
             ou(_couple_dans(vx, vy, G), _couple_dans(vy, vx, G)))))
    return et(est_ordre(G, E_set, x, y, z), comparables)


# ════════════════════════════════════════════════════════════════════════════
#  DÉFINITIONS — majorant / minorant, plus grand / plus petit, borne sup,
#  élément maximal / minimal  (E.III.1.7-1.8, graphe G, sous-ensemble A de E)
# ════════════════════════════════════════════════════════════════════════════
# @livre Ch.III §1.8 Def.5 | E III.9 L.22-25 | PDF p.112
def majorant(G, A, m, E_set, x="x"):
    """majorant(G,A,m,E) := m∈E et (∀x)(x∈A ⇒ (x,m)∈G).

    « m est un majorant de A (dans E) » : m∈E majore tous les éléments de A.
    (E.III.1.8, Définition 5.)"""
    vm, vA, vE, vx = _terme(m), _terme(A), _terme(E_set), var(x)
    return et(appartient(vm, vE),
              pourtout(x, impl(appartient(vx, vA), _couple_dans(vx, vm, G))))


# @livre Ch.III §1.8 Def.5 | E III.9 L.22-25 | PDF p.112
def minorant(G, A, m, E_set, x="x"):
    """minorant(G,A,m,E) := m∈E et (∀x)(x∈A ⇒ (m,x)∈G).

    « m est un minorant de A (dans E) ».  (E.III.1.8, Définition 5, dual.)"""
    vm, vA, vE, vx = _terme(m), _terme(A), _terme(E_set), var(x)
    return et(appartient(vm, vE),
              pourtout(x, impl(appartient(vx, vA), _couple_dans(vm, vx, G))))


# @livre Ch.III §1.7 Def.4 | E III.8 L.26-27 | PDF p.111
#   ⚠️ CE MARQUEUR A DIT « L.30-32 » : corrigé le 27 juil. 2026 après recomptage ligne à ligne
#   sur la page rendue en PNG (en-tête « E III.8 » confirmé). La Déf. 4 (« On dit qu'un élément
#   a ∈ E est le plus petit (resp. le plus grand) élément de E si… ») est aux lignes 26-27 ;
#   L.30-32 tombait sur le paragraphe SUIVANT. La valeur fausse avait été RECOPIÉE dans 3 autres
#   modules — un marqueur erroné se propage par copie, c'est son mode de nuisance principal.
def plus_grand_element(G, A, m, x="x"):
    """plus_grand_element(G,A,m) := m∈A et (∀x)(x∈A ⇒ (x,m)∈G).

    « m est le plus grand élément de A » : m appartient à A et majore A.
    (E.III.1.7, Définition 4.)"""
    vm, vA, vx = _terme(m), _terme(A), var(x)
    return et(appartient(vm, vA),
              pourtout(x, impl(appartient(vx, vA), _couple_dans(vx, vm, G))))


# @livre Ch.III §1.7 Def.4 | E III.8 L.26-27 | PDF p.111
#   ⚠️ CE MARQUEUR A DIT « L.30-32 » : corrigé le 27 juil. 2026 après recomptage ligne à ligne
#   sur la page rendue en PNG (en-tête « E III.8 » confirmé). La Déf. 4 (« On dit qu'un élément
#   a ∈ E est le plus petit (resp. le plus grand) élément de E si… ») est aux lignes 26-27 ;
#   L.30-32 tombait sur le paragraphe SUIVANT. La valeur fausse avait été RECOPIÉE dans 3 autres
#   modules — un marqueur erroné se propage par copie, c'est son mode de nuisance principal.
def plus_petit_element(G, A, m, x="x"):
    """plus_petit_element(G,A,m) := m∈A et (∀x)(x∈A ⇒ (m,x)∈G).

    « m est le plus petit élément de A ».  (E.III.1.7, Définition 4, dual.)"""
    vm, vA, vx = _terme(m), _terme(A), var(x)
    return et(appartient(vm, vA),
              pourtout(x, impl(appartient(vx, vA), _couple_dans(vm, vx, G))))


# @livre Ch.III §1.6 Def.3 | E III.8 L.10-12 | PDF p.111
def element_maximal(G, A, m, x="x"):
    """element_maximal(G,A,m) := m∈A et (∀x)((x∈A et (m,x)∈G) ⇒ x=m).

    « m est un élément maximal de A » : aucun élément de A n'est strictement
    au-dessus de m.  (E.III.1.6, Définition 3.)"""
    vm, vA, vx = _terme(m), _terme(A), var(x)
    return et(appartient(vm, vA),
              pourtout(x, impl(et(appartient(vx, vA), _couple_dans(vm, vx, G)),
                               egal(vx, vm))))


# @livre Ch.III §1.6 Def.3 | E III.8 L.10-12 | PDF p.111
def element_minimal(G, A, m, x="x"):
    """element_minimal(G,A,m) := m∈A et (∀x)((x∈A et (x,m)∈G) ⇒ x=m).

    « m est un élément minimal de A ».  (E.III.1.6, Définition 3, dual.)"""
    vm, vA, vx = _terme(m), _terme(A), var(x)
    return et(appartient(vm, vA),
              pourtout(x, impl(et(appartient(vx, vA), _couple_dans(vx, vm, G)),
                               egal(vx, vm))))


# @livre Ch.III §1.9 Def.6 | E III.10 L.4-8 | PDF p.113
def borne_superieure(G, A, m, E_set, x="x", y="y"):
    """borne_superieure(G,A,m,E) := « m est le plus petit majorant de A dans E »
        = majorant(G,A,m,E)  et  (∀y)(majorant(G,A,y,E) ⇒ (m,y)∈G).

    (E.III.1.9, Définition 7 : borne supérieure de A.)"""
    vm, vE, vy = _terme(m), _terme(E_set), var(y)
    est_maj_m = majorant(G, A, m, E_set, x)
    plus_petit = pourtout(y, impl(majorant(G, A, vy, E_set, x),
                                  _couple_dans(vm, vy, G)))
    return et(est_maj_m, plus_petit)


# @livre Ch.III §1.9 Def.6 | E III.10 L.4-8 | PDF p.113
def borne_inferieure(G, A, m, E_set, x="x", y="y"):
    """borne_inferieure(G,A,m,E) := « m est le plus grand minorant de A dans E »
        = minorant(G,A,m,E)  et  (∀y)(minorant(G,A,y,E) ⇒ (y,m)∈G).

    (E.III.1.9, Définition 7, dual : borne inférieure de A.)"""
    vm, vE, vy = _terme(m), _terme(E_set), var(y)
    est_min_m = minorant(G, A, m, E_set, x)
    plus_grand = pourtout(y, impl(minorant(G, A, vy, E_set, x),
                                  _couple_dans(vy, vm, G)))
    return et(est_min_m, plus_grand)


# ════════════════════════════════════════════════════════════════════════════
#  THÉORÈME 1 — la DIAGONALE Δ_E est un ordre sur E (ordre de l'égalité)
#  Cœur : diagonale_membre  ⊢  ((u,v) ∈ Δ_E) ⇔ (u∈E et u=v).      (E.III.3.1)
# ════════════════════════════════════════════════════════════════════════════
def diagonale_reflexive_sur(e="E", x="x"):
    """⊢ reflexivite_sur(Δ_E, E).   = (∀x)(x∈E ⇒ (x,x)∈Δ_E).

    Si x∈E alors (x∈E et x=x), donc (x,x)∈Δ_E par diagonale_membre (sens ⇐)."""
    vE, vx = _terme(e), var(x)
    DE = E.diagonale(vE)
    h = N.assume(appartient(vx, vE))                       # x∈E
    paire = conjonction_intro(h, N.reflexivite(vx))        # x∈E et x=x
    # diagonale_membre(E,x,x) : ((x,x)∈Δ_E) ⇔ (x∈E et x=x)
    xx_in = N.modus_ponens(paire, equivalence_arriere(diagonale_membre(e, x, x)))
    body = N.loi_deduction(appartient(vx, vE), xx_in)      # x∈E ⇒ (x,x)∈Δ_E
    return N.generalisation(x, body)                       # (∀x)(x∈E ⇒ (x,x)∈Δ_E)


def diagonale_antisymetrique(e="E", x="x", y="y"):
    """⊢ antisymetrie(Δ_E).   = (∀x)(∀y)(((x,y)∈Δ_E et (y,x)∈Δ_E) ⇒ x=y).

    De (x,y)∈Δ_E on tire déjà x=y (diagonale_membre, sens ⇒, projection droite) ;
    l'hypothèse (y,x)∈Δ_E n'est même pas nécessaire."""
    vE, vx, vy = _terme(e), var(x), var(y)
    DE = E.diagonale(vE)
    hyp = et(_couple_dans(vx, vy, DE), _couple_dans(vy, vx, DE))
    h = N.assume(hyp)
    xy = N.modus_ponens(conjonction_elim_gauche(h),
                        equivalence_avant(diagonale_membre(e, x, y)))   # (x∈E et x=y)
    x_eq_y = conjonction_elim_droite(xy)                                # x=y
    body = N.loi_deduction(hyp, x_eq_y)
    return N.generalisation(x, N.generalisation(y, body))


def diagonale_transitive(e="E", x="x", y="y", z="z"):
    """⊢ transitivite_rel(Δ_E).   = (∀x)(∀y)(∀z)(((x,y)∈Δ et (y,z)∈Δ) ⇒ (x,z)∈Δ).

    (x,y)∈Δ ⇒ (x∈E et x=y) ;  (y,z)∈Δ ⇒ (y∈E et y=z).  Donc x∈E et x=y=z, d'où
    (x∈E et x=z), donc (x,z)∈Δ (sens ⇐ de diagonale_membre)."""
    vE, vx, vy, vz = _terme(e), var(x), var(y), var(z)
    DE = E.diagonale(vE)
    hyp = et(_couple_dans(vx, vy, DE), _couple_dans(vy, vz, DE))
    h = N.assume(hyp)
    xy = N.modus_ponens(conjonction_elim_gauche(h),
                        equivalence_avant(diagonale_membre(e, x, y)))   # x∈E et x=y
    yz = N.modus_ponens(conjonction_elim_droite(h),
                        equivalence_avant(diagonale_membre(e, y, z)))   # y∈E et y=z
    x_in = conjonction_elim_gauche(xy)                                  # x∈E
    x_eq_y = conjonction_elim_droite(xy)                               # x=y
    y_eq_z = conjonction_elim_droite(yz)                               # y=z
    x_eq_z = composer_egalites(x_eq_y, y_eq_z)                         # x=z
    paire = conjonction_intro(x_in, x_eq_z)                            # x∈E et x=z
    xz_in = N.modus_ponens(paire, equivalence_arriere(diagonale_membre(e, x, z)))  # (x,z)∈Δ
    body = N.loi_deduction(hyp, xz_in)
    return N.generalisation(x, N.generalisation(y, N.generalisation(z, body)))


def diagonale_est_ordre(e="E", x="x", y="y", z="z"):
    """⊢ est_ordre(Δ_E, E).   La diagonale est l'ordre de l'égalité sur E (E.III.3.1)."""
    return conjonction_intro(
        conjonction_intro(diagonale_reflexive_sur(e, x), diagonale_antisymetrique(e, x, y)),
        diagonale_transitive(e, x, y, z))


# ════════════════════════════════════════════════════════════════════════════
#  THÉORÈME 2 — l'INCLUSION ⊂ est un ordre  (E.III.1.1, Exemple 1)
#  Ici la « relation » ⊂ n'est pas un graphe ∈, mais ses trois propriétés
#  s'expriment et se prouvent directement à partir des lemmes déjà vérifiés.
# ════════════════════════════════════════════════════════════════════════════
# @livre Ch.R §6 Ex.- | E.R.26 item 2 (l'inclusion Y⊂X est un ordre sur P(E) : réflexivité) | PDF p.329
def inclusion_reflexive_sur(x="x"):
    """⊢ x ⊂ x.   (⊂ est réflexive — chaque ensemble est inclus dans lui-même.)

    Réexpose `tactiques_abrege.inclusion_reflexive` sous le vocabulaire « ordre »."""
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege import inclusion_reflexive
    return inclusion_reflexive(x)


# @livre Ch.R §6 Ex.- | E.R.26 item 2 (l'inclusion Y⊂X est un ordre sur P(E) : transitivité) | PDF p.329
def inclusion_transitive_rel(a="a", b="b", c="c"):
    """⊢ ((a⊂b) et (b⊂c)) ⇒ (a⊂c).   (⊂ est transitive.)

    Réexpose `tactiques_abrege2.inclusion_transitive`."""
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import inclusion_transitive
    return inclusion_transitive(a, b, c)


# @livre Ch.R §6 Ex.- | E.R.26 item 2 (l'inclusion Y⊂X est un ordre sur P(E) : antisymétrie) | PDF p.329
def inclusion_antisymetrique(a="a", b="b", z="z"):
    """⊢ ((a⊂b) et (b⊂a)) ⇒ (a=b).   (⊂ est antisymétrique — c'est A1, E.II.1.3.)

    Forme conjonctive (« antisymétrie ») de l'extensionnalité appliquée."""
    va, vb = _terme(a), _terme(b)
    from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_theoremes import extensionnalite_appliquee
    return extensionnalite_appliquee(va, vb)              # ((a⊂b) et (b⊂a)) ⇒ a=b


# ════════════════════════════════════════════════════════════════════════════
#  THÉORÈMES DIRECTS — plus grand élément, maximal, borne supérieure
#  (E.III.1.6-1.9, formulation graphe G ; tous certifiés par le noyau abrégé)
# ════════════════════════════════════════════════════════════════════════════
def plus_grand_element_unique(G, A, a="a", b="b", x="x", y="y"):
    """{ antisymetrie(G), a plus grand élt de A, b plus grand élt de A } ⊢ a=b.

    Le plus grand élément, s'il existe, est UNIQUE.  Si a et b sont tous deux
    plus grands, alors (a,b)∈G (b majore, a∈A) et (b,a)∈G (a majore, b∈A) ;
    l'antisymétrie conclut a=b.  (E.III.1.7.)"""
    va, vb = _terme(a), _terme(b)
    Has = N.assume(antisymetrie(G, x, y))                 # (∀x∀y)(((x,y)∈G et (y,x)∈G)⇒x=y)
    Ha = N.assume(plus_grand_element(G, A, va, x))         # a∈A et (∀x)(x∈A⇒(x,a)∈G)
    Hb = N.assume(plus_grand_element(G, A, vb, x))         # b∈A et (∀x)(x∈A⇒(x,b)∈G)
    a_in = conjonction_elim_gauche(Ha)                    # a∈A
    b_in = conjonction_elim_gauche(Hb)                    # b∈A
    a_maj = conjonction_elim_droite(Ha)                   # (∀x)(x∈A⇒(x,a)∈G)
    b_maj = conjonction_elim_droite(Hb)                   # (∀x)(x∈A⇒(x,b)∈G)
    # (b,a)∈G : b∈A, a plus grand → instancier a_maj en b
    ba = N.modus_ponens(b_in, instancie(a_maj, vb))       # (b,a)∈G
    # (a,b)∈G : a∈A, b plus grand → instancier b_maj en a
    ab = N.modus_ponens(a_in, instancie(b_maj, va))       # (a,b)∈G
    # antisymétrie en (a,b) : ((a,b)∈G et (b,a)∈G) ⇒ a=b
    antisym_ab = instancie(instancie(Has, va), vb)
    return N.modus_ponens(conjonction_intro(ab, ba), antisym_ab)   # a=b


def plus_petit_element_unique(G, A, a="a", b="b", x="x", y="y"):
    """{ antisymetrie(G), a plus petit élt de A, b plus petit élt de A } ⊢ a=b.
    (E.III.1.7, dual.)"""
    va, vb = _terme(a), _terme(b)
    Has = N.assume(antisymetrie(G, x, y))
    Ha = N.assume(plus_petit_element(G, A, va, x))         # a∈A et (∀x)(x∈A⇒(a,x)∈G)
    Hb = N.assume(plus_petit_element(G, A, vb, x))         # b∈A et (∀x)(x∈A⇒(b,x)∈G)
    a_in = conjonction_elim_gauche(Ha)
    b_in = conjonction_elim_gauche(Hb)
    a_min = conjonction_elim_droite(Ha)
    b_min = conjonction_elim_droite(Hb)
    ab = N.modus_ponens(b_in, instancie(a_min, vb))       # (a,b)∈G
    ba = N.modus_ponens(a_in, instancie(b_min, va))       # (b,a)∈G
    antisym_ab = instancie(instancie(Has, va), vb)        # ((a,b)∈G et (b,a)∈G)⇒a=b
    return N.modus_ponens(conjonction_intro(ab, ba), antisym_ab)


# @livre Ch.III §1.7 Rem.- | E III.8 L.36-38 | PDF p.111
def plus_grand_est_maximal(G, A, m="m", x="x", y="y"):
    """{ antisymetrie(G), m plus grand élt de A } ⊢ element_maximal(G,A,m).

    Le plus grand élément est un élément MAXIMAL.  m∈A est donné ; et si x∈A avec
    (m,x)∈G, alors comme m est plus grand on a aussi (x,m)∈G, d'où x=m par
    antisymétrie.  (E.III.1.6-1.7.)"""
    vm, vA, vx = _terme(m), _terme(A), var(x)
    Has = N.assume(antisymetrie(G, x, y))
    Hm = N.assume(plus_grand_element(G, A, vm, x))         # m∈A et (∀x)(x∈A⇒(x,m)∈G)
    m_in = conjonction_elim_gauche(Hm)                    # m∈A
    m_maj = conjonction_elim_droite(Hm)                   # (∀x)(x∈A⇒(x,m)∈G)
    # corps : (x∈A et (m,x)∈G) ⇒ x=m
    hyp_body = et(appartient(vx, vA), _couple_dans(vm, vx, G))
    Hbody = N.assume(hyp_body)
    x_in = conjonction_elim_gauche(Hbody)                 # x∈A
    mx = conjonction_elim_droite(Hbody)                   # (m,x)∈G
    xm = N.modus_ponens(x_in, instancie(m_maj, vx))       # (x,m)∈G
    antisym_xm = instancie(instancie(Has, vx), vm)        # ((x,m)∈G et (m,x)∈G)⇒x=m
    x_eq_m = N.modus_ponens(conjonction_intro(xm, mx), antisym_xm)   # x=m
    body = N.loi_deduction(hyp_body, x_eq_m)
    return conjonction_intro(m_in, N.generalisation(x, body))


# @livre Ch.III §1.7 Rem.- | E III.8 L.36-38 | PDF p.111
def plus_petit_est_minimal(G, A, m="m", x="x", y="y"):
    """{ antisymetrie(G), m plus petit élt de A } ⊢ element_minimal(G,A,m).
    (E.III.1.6-1.7, dual.)"""
    vm, vA, vx = _terme(m), _terme(A), var(x)
    Has = N.assume(antisymetrie(G, x, y))
    Hm = N.assume(plus_petit_element(G, A, vm, x))         # m∈A et (∀x)(x∈A⇒(m,x)∈G)
    m_in = conjonction_elim_gauche(Hm)
    m_min = conjonction_elim_droite(Hm)                   # (∀x)(x∈A⇒(m,x)∈G)
    hyp_body = et(appartient(vx, vA), _couple_dans(vx, vm, G))   # x∈A et (x,m)∈G
    Hbody = N.assume(hyp_body)
    x_in = conjonction_elim_gauche(Hbody)
    xm = conjonction_elim_droite(Hbody)                   # (x,m)∈G
    mx = N.modus_ponens(x_in, instancie(m_min, vx))       # (m,x)∈G
    antisym_xm = instancie(instancie(Has, vx), vm)        # ((x,m)∈G et (m,x)∈G)⇒x=m
    x_eq_m = N.modus_ponens(conjonction_intro(xm, mx), antisym_xm)
    body = N.loi_deduction(hyp_body, x_eq_m)
    return conjonction_intro(m_in, N.generalisation(x, body))


def plus_grand_est_majorant(G, A, E_set="E", m="m", x="x"):
    """{ A⊂E, m plus grand élt de A } ⊢ majorant(G,A,m,E).

    Un plus grand élément de A est en particulier un majorant de A dans E
    (il appartient à E car A⊂E).  (E.III.1.7-1.8.)"""
    vm, vA, vE = _terme(m), _terme(A), _terme(E_set)
    Hsub = N.assume(inclus(vA, vE))                       # A⊂E = (∀z)(z∈A⇒z∈E)
    Hm = N.assume(plus_grand_element(G, A, vm, x))         # m∈A et (∀x)(x∈A⇒(x,m)∈G)
    m_in_A = conjonction_elim_gauche(Hm)                  # m∈A
    m_maj = conjonction_elim_droite(Hm)                   # (∀x)(x∈A⇒(x,m)∈G)
    m_in_E = N.modus_ponens(m_in_A, instancie(Hsub, vm))  # m∈E
    return conjonction_intro(m_in_E, m_maj)               # majorant(G,A,m,E)


def plus_petit_est_minorant(G, A, E_set="E", m="m", x="x"):
    """{ A⊂E, m plus petit élt de A } ⊢ minorant(G,A,m,E).  (E.III.1.7-1.8, dual.)"""
    vm, vA, vE = _terme(m), _terme(A), _terme(E_set)
    Hsub = N.assume(inclus(vA, vE))
    Hm = N.assume(plus_petit_element(G, A, vm, x))         # m∈A et (∀x)(x∈A⇒(m,x)∈G)
    m_in_A = conjonction_elim_gauche(Hm)
    m_min = conjonction_elim_droite(Hm)
    m_in_E = N.modus_ponens(m_in_A, instancie(Hsub, vm))  # m∈E
    return conjonction_intro(m_in_E, m_min)               # minorant(G,A,m,E)


# @livre Ch.III §1.9 Rem.- | E III.10 L.9-10 | PDF p.113
def plus_grand_est_borne_superieure(G, A, E_set="E", m="m", x="x", y="y"):
    """{ A⊂E, m plus grand élt de A } ⊢ borne_superieure(G,A,m,E).

    Le plus grand élément de A est sa borne supérieure : c'est un majorant
    (plus_grand_est_majorant) et c'est le PLUS PETIT des majorants — car si y
    majore A, alors comme m∈A on a (m,y)∈G.  (E.III.1.9.)"""
    vm, vA, vE, vy = _terme(m), _terme(A), _terme(E_set), var(y)
    Hsub = N.assume(inclus(vA, vE))
    Hm = N.assume(plus_grand_element(G, A, vm, x))
    m_in_A = conjonction_elim_gauche(Hm)                  # m∈A
    # (1) m est un majorant de A dans E
    maj_m = plus_grand_est_majorant(G, A, E_set, vm, x)   # {A⊂E, m pge} ⊢ majorant(G,A,m,E)
    # (2) m est le plus petit majorant : (∀y)(majorant(G,A,y,E) ⇒ (m,y)∈G)
    Hy = N.assume(majorant(G, A, vy, E_set, x))           # y∈E et (∀x)(x∈A⇒(x,y)∈G)
    y_maj = conjonction_elim_droite(Hy)                   # (∀x)(x∈A⇒(x,y)∈G)
    my = N.modus_ponens(m_in_A, instancie(y_maj, vm))     # (m,y)∈G
    body = N.loi_deduction(majorant(G, A, vy, E_set, x), my)   # majorant(y)⇒(m,y)∈G
    plus_petit = N.generalisation(y, body)
    return conjonction_intro(maj_m, plus_petit)           # borne_superieure(G,A,m,E)


def borne_superieure_unique(G, A, E_set="E", a="a", b="b", x="x", y="y"):
    """{ antisymetrie(G), a borne sup de A, b borne sup de A } ⊢ a=b.

    La borne supérieure, si elle existe, est UNIQUE.  a et b sont des majorants ;
    a étant le plus petit majorant, (a,b)∈G ; de même (b,a)∈G ; antisymétrie ⇒ a=b.
    (E.III.1.9.)"""
    va, vb = _terme(a), _terme(b)
    Has = N.assume(antisymetrie(G, x, y))
    Ha = N.assume(borne_superieure(G, A, va, E_set, x, y))   # maj(a) et (∀y)(maj(y)⇒(a,y)∈G)
    Hb = N.assume(borne_superieure(G, A, vb, E_set, x, y))   # maj(b) et (∀y)(maj(y)⇒(b,y)∈G)
    a_maj = conjonction_elim_gauche(Ha)                   # majorant(G,A,a,E)
    b_maj = conjonction_elim_gauche(Hb)                   # majorant(G,A,b,E)
    a_least = conjonction_elim_droite(Ha)                 # (∀y)(maj(y)⇒(a,y)∈G)
    b_least = conjonction_elim_droite(Hb)                 # (∀y)(maj(y)⇒(b,y)∈G)
    ab = N.modus_ponens(b_maj, instancie(a_least, vb))    # (a,b)∈G
    ba = N.modus_ponens(a_maj, instancie(b_least, va))    # (b,a)∈G
    antisym_ab = instancie(instancie(Has, va), vb)        # ((a,b)∈G et (b,a)∈G)⇒a=b
    return N.modus_ponens(conjonction_intro(ab, ba), antisym_ab)


# ════════════════════════════════════════════════════════════════════════════
#  THÉORÈMES DIRECTS — ordre induit sur une partie, ordre total
#  (E.III.1.4, E.III.1.12)
# ════════════════════════════════════════════════════════════════════════════
# @livre Ch.III §1.4 Def.- | E III.5 L.31-37 | PDF p.108
# (« G∩(A×A) est un ordre sur A » — ordre induit / prolongements ; L.31 = titre du n°4)
def ordre_induit_sur_partie(G, E_set="E", A="A", x="x", y="y", z="z"):
    """{ est_ordre(G,E), A⊂E } ⊢ est_ordre(G,A).

    La restriction d'un ordre à un sous-ensemble reste un ordre : antisymétrie et
    transitivité sont des propriétés du graphe G (indépendantes de l'ensemble de
    base) ; seule la réflexivité doit être ré-établie sur A, ce qui résulte de
    A⊂E.  (E.III.1.4, ordre induit.)"""
    vA, vE, vx = _terme(A), _terme(E_set), var(x)
    Hord = N.assume(est_ordre(G, E_set, x, y, z))         # (refl_E et antisym) et trans
    Hsub = N.assume(inclus(vA, vE))                       # A⊂E
    refl_E = conjonction_elim_gauche(conjonction_elim_gauche(Hord))   # (∀x)(x∈E⇒(x,x)∈G)
    antisym = conjonction_elim_droite(conjonction_elim_gauche(Hord))  # antisymetrie(G)
    trans = conjonction_elim_droite(Hord)                 # transitivite_rel(G)
    # réflexivité sur A : x∈A ⇒ (x,x)∈G  (via x∈A → x∈E → (x,x)∈G)
    Hx = N.assume(appartient(vx, vA))                     # x∈A
    x_in_E = N.modus_ponens(Hx, instancie(Hsub, vx))      # x∈E
    xx = N.modus_ponens(x_in_E, instancie(refl_E, vx))    # (x,x)∈G
    refl_body = N.loi_deduction(appartient(vx, vA), xx)   # x∈A⇒(x,x)∈G
    refl_A = N.generalisation(x, refl_body)               # reflexivite_sur(G,A)
    return conjonction_intro(conjonction_intro(refl_A, antisym), trans)


# @livre Ch.III §1.12 Ex.1 | E III.14 L.10-11 | PDF p.117
# @livre Ch.R §6 Prop.- | E.R.27 item 4 (toute partie d'un totalement ordonné est totalement ordonnée) | PDF p.330
def totalement_ordonne_partie(G, E_set="E", A="A", x="x", y="y", z="z"):
    """{ totalement_ordonne(G,E), A⊂E } ⊢ totalement_ordonne(G,A).

    Toute partie A d'un ensemble totalement ordonné E est elle-même totalement
    ordonnée par le même graphe : c'est un ordre (ordre_induit_sur_partie) et deux
    éléments de A, étant dans E, restent comparables.  (E.III.1.12.)"""
    vA, vE, vx, vy = _terme(A), _terme(E_set), var(x), var(y)
    Htot = N.assume(totalement_ordonne(G, E_set, x, y))   # est_ordre(G,E) et comparables_E
    Hsub = N.assume(inclus(vA, vE))                       # A⊂E
    ord_part = conjonction_elim_gauche(Htot)              # est_ordre(G,E)
    comp_E = conjonction_elim_droite(Htot)                # (∀x∀y)((x∈E et y∈E)⇒(…ou…))
    # (1) est_ordre(G,A)  — via ordre_induit_sur_partie, dont on CUT les 2 hyps
    ord_A = ordre_induit_sur_partie(G, E_set, A, x, y, z)   # {est_ordre(G,E),A⊂E}⊢est_ordre(G,A)
    ord_A = _cut(ord_A, est_ordre(G, E_set, x, y, z), ord_part)
    ord_A = _cut(ord_A, inclus(vA, vE), Hsub)             # ⊢ est_ordre(G,A)  (sous {Htot,Hsub})
    # (2) comparabilité sur A : (x∈A et y∈A) ⇒ ((x,y)∈G ou (y,x)∈G)
    Hxy = N.assume(et(appartient(vx, vA), appartient(vy, vA)))
    x_in_E = N.modus_ponens(conjonction_elim_gauche(Hxy), instancie(Hsub, vx))   # x∈E
    y_in_E = N.modus_ponens(conjonction_elim_droite(Hxy), instancie(Hsub, vy))   # y∈E
    comp_xy = instancie(instancie(comp_E, vx), vy)        # (x∈E et y∈E)⇒(…ou…)
    disj = N.modus_ponens(conjonction_intro(x_in_E, y_in_E), comp_xy)
    body = N.loi_deduction(et(appartient(vx, vA), appartient(vy, vA)), disj)
    comp_A = N.generalisation(x, N.generalisation(y, body))
    return conjonction_intro(ord_A, comp_A)


def maximal_est_plus_grand_si_total(G, E_set="E", A="A", m="m", x="x", y="y"):
    """{ totalement_ordonne(G,E), A⊂E, element_maximal(G,A,m) } ⊢ plus_grand_element(G,A,m).

    Dans un ensemble TOTALEMENT ordonné, tout élément maximal de A est le plus
    grand élément de A : soit x∈A ; par totalité (x,m)∈G ou (m,x)∈G.  Dans le
    second cas, la maximalité de m donne x=m, et la réflexivité (m,m)∈G se
    transporte en (x,m)∈G.  (E.III.1.12 — l'ordre total fusionne maximal et
    plus grand.)"""
    vm, vA, vE, vx = _terme(m), _terme(A), _terme(E_set), var(x)
    Htot = N.assume(totalement_ordonne(G, E_set, x, y))   # est_ordre(G,E) et comparables
    Hsub = N.assume(inclus(vA, vE))                       # A⊂E
    Hmax = N.assume(element_maximal(G, A, vm, x))          # m∈A et (∀x)((x∈A et (m,x)∈G)⇒x=m)
    m_in_A = conjonction_elim_gauche(Hmax)                # m∈A
    max_body = conjonction_elim_droite(Hmax)              # (∀x)((x∈A et (m,x)∈G)⇒x=m)
    ord_part = conjonction_elim_gauche(Htot)              # est_ordre(G,E)
    refl_E = conjonction_elim_gauche(conjonction_elim_gauche(ord_part))   # (∀x)(x∈E⇒(x,x)∈G)
    comparables = conjonction_elim_droite(Htot)           # (∀x∀y)((x∈E et y∈E)⇒((x,y)∈G ou (y,x)∈G))
    m_in_E = N.modus_ponens(m_in_A, instancie(Hsub, vm))  # m∈E
    # corps du « plus grand » : x∈A ⇒ (x,m)∈G
    Hx = N.assume(appartient(vx, vA))                     # x∈A
    x_in_E = N.modus_ponens(Hx, instancie(Hsub, vx))      # x∈E
    # totalité en (x,m) : (x∈E et m∈E) ⇒ ((x,m)∈G ou (m,x)∈G)
    comp_xm = instancie(instancie(comparables, vx), vm)
    disj = N.modus_ponens(conjonction_intro(x_in_E, m_in_E), comp_xm)   # (x,m)∈G ou (m,x)∈G
    cible = _couple_dans(vx, vm, G)                       # but : (x,m)∈G
    # cas 1 : (x,m)∈G — immédiat
    cas1 = N.loi_deduction(_couple_dans(vx, vm, G), N.assume(_couple_dans(vx, vm, G)))
    # cas 2 : (m,x)∈G — maximalité ⇒ x=m, puis réflexivité (m,m)∈G transportée en (x,m)∈G
    Hmx = N.assume(_couple_dans(vm, vx, G))               # (m,x)∈G
    max_inst = instancie(max_body, vx)                    # (x∈A et (m,x)∈G)⇒x=m
    x_eq_m = N.modus_ponens(conjonction_intro(Hx, Hmx), max_inst)   # x=m  (sous {x∈A,(m,x)∈G})
    m_eq_x = N.modus_ponens(x_eq_m, symetrie(vx, vm))     # m=x
    mm = N.modus_ponens(m_in_E, instancie(refl_E, vm))    # (m,m)∈G
    # Leibniz : (m=x) ⇒ ((m,m)∈G ⇔ (x,m)∈G), trou « w » sur la 1re coordonnée
    phi = _couple_dans(var("w"), vm, G)                   # Φ(w) = (w,m)∈G
    leib = N.s6(vm, vx, "w", phi)                         # (m=x)⇒((m,m)∈G ⇔ (x,m)∈G)
    equiv_mm = N.modus_ponens(m_eq_x, leib)               # (m,m)∈G ⇔ (x,m)∈G
    xm = N.modus_ponens(mm, equivalence_avant(equiv_mm)) # (x,m)∈G  (sous {x∈A,(m,x)∈G})
    cas2 = N.loi_deduction(_couple_dans(vm, vx, G), xm)   # (m,x)∈G ⇒ (x,m)∈G  (sous {x∈A})
    par_cas = cas(disj, cas1, cas2)                       # (x,m)∈G  (sous {x∈A, …})
    body = N.loi_deduction(appartient(vx, vA), par_cas)   # x∈A ⇒ (x,m)∈G
    return conjonction_intro(m_in_A, N.generalisation(x, body))


__all__ = [
    # définitions
    "reflexivite_sur", "antisymetrie", "transitivite_rel", "est_ordre",
    "totalement_ordonne",
    "majorant", "minorant", "plus_grand_element", "plus_petit_element",
    "element_maximal", "element_minimal", "borne_superieure", "borne_inferieure",
    # diagonale = ordre de l'égalité
    "diagonale_reflexive_sur", "diagonale_antisymetrique", "diagonale_transitive",
    "diagonale_est_ordre",
    # inclusion = ordre
    "inclusion_reflexive_sur", "inclusion_transitive_rel", "inclusion_antisymetrique",
    # plus grand / petit, maximal / minimal, majorant, borne supérieure
    "plus_grand_element_unique", "plus_petit_element_unique",
    "plus_grand_est_maximal", "plus_petit_est_minimal",
    "plus_grand_est_majorant", "plus_petit_est_minorant",
    "plus_grand_est_borne_superieure", "borne_superieure_unique",
    # ordre induit, ordre total
    "ordre_induit_sur_partie", "totalement_ordonne_partie",
    "maximal_est_plus_grand_si_total",
]
