"""§III.4 — SURGERY « RETRAIT D'UN POINT » : ferme le report retrait_point_hyp du
LEMME N (« pas de cardinal strictement entre c et c+1 »).

OBJECTIF (ferme l'unique maillon dur de ensembles_cardinal_pas_entre, la BRANCHE
NON SURJECTIVE) :

    retrait_point_hyp(b, c, F) :
        ( est_injection_de(F, b, c+1)  et  image(F,b) ≠ c+1 )  ⇒  ( b ≤ c ),

où  c+1 = successeur(c) = Card(C ⊔ {∅})  est le successeur cardinal fidèle, et
C ⊔ {∅} = (C×{0}) ∪ ({∅}×{1})  est l'ensemble augmenté CONCRET (somme disjointe
binaire).  La preuve est le PRINCIPE DES TIROIRS E.III.4 (surgery voisine de la
Prop. 8) : une injection f : b → c+1 NON surjective rate un point q de c+1, donc
injecte b dans (c+1) ∖ {q} ≃ c, d'où b ≤ c.

────────────────────────────────────────────────────────────────────────────────
DÉCOMPOSITION — où passe la frontière du SALVAGE (anti-faux, rien postulé) :

Le codomaine de f est la CARDINAL OPAQUE  c+1 = Card(S)  avec  S := C ⊔ {∅}.  On
travaille donc en DEUX temps :

  (I) PONTS INCONDITIONNELS (rien postulé, theorie=22) — toute la plomberie qui
      ramène la non-surjectivité au niveau de l'ensemble concret S, puis qui
      identifie « S privé du point marqué * = (∅,1) » à c :

      • eq_succ_ensemble(c)        — ⊢ Eq(c+1, S)            (S = C⊔{∅}, son cardinal) ;
      • inf_egal_via_eq_codom(b,Y,Z) — ⊢ (b ≤ Y et Eq(Y,Z)) ⇒ b ≤ Z   (glue de transport) ;
      • diff_marqueur_egal_copie(c) — ⊢ (C⊔{∅})∖{*} = C×{0}   (retrait du point marqué) ;
      • eq_diff_marqueur_c(c)      — ⊢ Eq((C⊔{∅})∖{*}, C)    (S∖{*} ≃ C, copie de gauche) ;
      • inf_egal_diff_marqueur_implique(b,c) —
            ⊢ ( b ≤ (C⊔{∅})∖{*} ) ⇒ ( b ≤ c )    [le pont FINAL, INCONDITIONNEL].

  (II) SURGERY ISOLÉE (le SEUL maillon dur, REPORTÉE honnêtement, hypothèse
       explicite jamais postulée) — la fabrication EFFECTIVE de l'injection
       b → S∖{*} à partir d'une injection f : b → Card(S) non surjective.  C'est
       l'échange ponctuel « ramener le point raté sur le marqueur * » (type Prop. 8,
       transposition DÉJÀ outillée ensembles_prop8_transposition) :

       • retrait_surgery_hyp(b,c,F) =
            ( est_injection_de(F, b, c+1) et image(F,b)≠c+1 )  ⇒  ( b ≤ (C⊔{∅})∖{*} ).

ASSEMBLAGE :  retrait_surgery_hyp  ∘  inf_egal_diff_marqueur_implique  ⇒
              retrait_point_hyp.  Le report rétrécit donc de « b ≤ c » (cardinal
              opaque) à « b ≤ S∖{*} » (ensemble CONCRET, point retiré FIXÉ = le
              marqueur) : tout le transport cardinal↔ensemble et S∖{*}≃c est CLOS.

  • retrait_point_hyp_mod_surgery(b,c)  — ⊢ retrait_surgery_hyp(b,c,F) ⇒ retrait_point_hyp(b,c,F)
        (CLOS, 0 hyp : la surgery isolée est en antécédent explicite) ;
  • retrait_point_hyp_assemble(b,c,F)   — { retrait_surgery_hyp } ⊢ retrait_point_hyp(b,c,F)
        (conclusion ÉGALE LITTÉRALEMENT au report de ensembles_cardinal_pas_entre).

⚠️ INVARIANT : theorie_ensembles() = 22 intangible.  AUCUN N.axiome ; le seul
   « given » est l'HYPOTHÈSE explicite retrait_surgery_hyp, déchargée par
   loi_deduction — jamais postulée comme théorème.
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (Terme, var, egal, et, non, impl, existe,
                                       inclus, appartient)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege import syllogisme
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, instancie)
from bourbaki.logique.i_4_egalitaires.tactiques_abrege_egalite import symetrie, composer_egalites

from bourbaki.cardinaux.ensembles_cardinaux import (
    est_injection_de, equipotent, cardinal, inf_egal_card,
)
from bourbaki.cardinaux.ensembles_cardinaux_theoremes import equipotent_son_cardinal
from bourbaki.cardinaux.ensembles_cardinaux_ordre import equipotence_implique_inf_egal
from bourbaki.cardinaux.ensembles_cardinaux_props_restantes import (
    _inf_egal_transitive_t, _eq_implique_inf_egal_t, _eq_son_cardinal_t)
from bourbaki.cardinaux.arithmetique.ensembles_copie_marquee import (
    eq_copie_gauche, _eq_sym_t, _eq_trans_t)
from bourbaki.cardinaux.arithmetique.ensembles_prop8_plus_point import somme_un_plus_point
from bourbaki.ensembles.familles.ii_4_reunion_intersection_familles.ii_4_recollement_somme.ensembles_somme_disjointe import somme_disjointe, ZERO, UN
from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_theoremes import egalite_par_extension
from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import successeur


def _t(t):
    """Coercion str/Terme → Terme (utilitaire local)."""
    return t if isinstance(t, Terme) else var(t)


# Le point marqué * = (∅, 1)  (l'unique élément « en plus » de C⊔{∅} par rapport à C×{0}).
_STAR = E.couple(E.VIDE, UN)


def _S(c):
    """S := C ⊔ {∅} = (C×{0}) ∪ ({∅}×{1})   (l'ensemble augmenté CONCRET, dont
    c+1 = successeur(c) = Card(S))."""
    return somme_disjointe(_t(c), E.singleton(E.VIDE))


def _C0(c):
    """C×{0}   (la copie de gauche de C dans l'ensemble augmenté)."""
    return E.produit(_t(c), E.singleton(ZERO))


# ════════════════════════════════════════════════════════════════════════════
#  PONT 1 (INCONDITIONNEL) — ⊢ Eq(c+1, C⊔{∅})   (le successeur cardinal ≃ l'ensemble)
# ════════════════════════════════════════════════════════════════════════════
def eq_succ_ensemble(c="c"):
    """⊢ Eq(c+1, C⊔{∅}).   (le successeur cardinal est équipotent à l'ensemble augmenté.)

    c+1 = successeur(c) = Card(C⊔{∅}) LITTÉRALEMENT (def. du successeur fidèle).
    equipotent_son_cardinal(S) donne Eq(S, Card S) ; symétrie ⇒ Eq(Card S, S) =
    Eq(c+1, S).  INCONDITIONNEL (Card S est de la forme Card(·))."""
    vc = _t(c)
    S = _S(c)                                             # C ⊔ {∅}
    cardS = cardinal(S)                                   # Card(C⊔{∅}) = c+1 (def.)
    eq_S_card = _eq_son_cardinal_t(S)                     # Eq(S, Card S)
    return N.modus_ponens(eq_S_card, _eq_sym_t(S, cardS)) # Eq(Card S, S) = Eq(c+1, S)


# ════════════════════════════════════════════════════════════════════════════
#  GLUE (INCONDITIONNEL) — ⊢ (b ≤ Y et Eq(Y,Z)) ⇒ b ≤ Z   (transport de ≤ par Eq)
# ════════════════════════════════════════════════════════════════════════════
def inf_egal_via_eq_codom(b="b", y="Y", z="Z"):
    """⊢ ( b ≤ Y  et  Eq(Y, Z) )  ⇒  ( b ≤ Z ).   (on transporte b ≤ Y par Eq(Y,Z).)

    Eq(Y,Z) ⇒ Y ≤ Z (equipotence_implique_inf_egal) ; transitivité de ≤ :
    (b ≤ Y et Y ≤ Z) ⇒ b ≤ Z.  INCONDITIONNEL, réutilisable."""
    vb, vy, vz = _t(b), _t(y), _t(z)
    ante = et(inf_egal_card(vb, vy), equipotent(vy, vz))
    h = N.assume(ante)
    le_bY = conjonction_elim_gauche(h)                    # b ≤ Y
    eq_YZ = conjonction_elim_droite(h)                    # Eq(Y, Z)
    le_YZ = N.modus_ponens(eq_YZ, _eq_implique_inf_egal_t(vy, vz))   # Y ≤ Z
    trans = _inf_egal_transitive_t(vb, vy, vz)            # (b≤Y et Y≤Z) ⇒ b≤Z
    le_bZ = N.modus_ponens(conjonction_intro(le_bY, le_YZ), trans)   # b ≤ Z
    return N.loi_deduction(ante, le_bZ)


# ════════════════════════════════════════════════════════════════════════════
#  PONT 2 (INCONDITIONNEL) — ⊢ (C⊔{∅}) ∖ {*} = C×{0}   (retrait du point marqué)
#
#  z ∈ (C⊔{∅})∖{*} ⇔ (z∈C⊔{∅} et z≠*) ⇔ ((z∈C×{0} ou z=*) et z≠*) ⇔ z∈C×{0}.
#  (somme_un_plus_point donne la décomposition ; z≠* élimine la branche z=*.)
# ════════════════════════════════════════════════════════════════════════════
def _inst_diff(e, x, z):
    """⊢ (z ∈ E∖X) ⇔ (z∈E et ¬(z∈X))   (instance de AXIOME_DIFF)."""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_DIFF)
    return instancie(instancie(instancie(ax, _t(e)), _t(x)), _t(z))


def _dans_singleton_star_ssi(z):
    """⊢ (z ∈ {*}) ⇔ (z = *).   (* = (∅,1) ; AXIOME_PAIRE sur le singleton {*,*}.)"""
    vz = _t(z)
    ax_p = N.axiome(E.theorie_ensembles(), E.AXIOME_PAIRE)
    car = instancie(instancie(instancie(ax_p, _STAR), _STAR), vz)   # z∈{*,*} ⇔ (z=* ou z=*)
    # (z=* ou z=*) ⇔ z=*   (idempotence du « ou »)
    from bourbaki.ensembles.familles.ii_4_reunion_intersection_familles.ii_4_recollement_somme.ensembles_somme_disjointe import _ou_idem
    from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege import a_implique_a
    from bourbaki.logique.i_1_termes_relations.formule import ou
    h_or = N.assume(ou(egal(vz, _STAR), egal(vz, _STAR)))
    fwd = N.loi_deduction(ou(egal(vz, _STAR), egal(vz, _STAR)),
                          _ou_idem(h_or, egal(vz, _STAR)))           # (z=* ou z=*) ⇒ z=*
    bwd = N.loi_deduction(egal(vz, _STAR),
                          N.modus_ponens(N.assume(egal(vz, _STAR)),
                                         N.s2(egal(vz, _STAR), egal(vz, _STAR))))  # z=* ⇒ (z=* ou z=*)
    idem = conjonction_intro(fwd, bwd)                              # (z=* ou z=*) ⇔ z=*
    from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import equivalence_transitivite
    return equivalence_transitivite(car, idem)                      # z∈{*} ⇔ z=*


def diff_marqueur_egal_copie(c="c"):
    """⊢ (C⊔{∅}) ∖ {*} = C×{0}.   (retirer le point marqué * = (∅,1) rend la copie gauche.)

    Par extensionnalité (egalite_par_extension) sur le corps « z∈… » :
      z ∈ (C⊔{∅})∖{*}  ⇔  (z∈C⊔{∅} et ¬(z∈{*}))            [AXIOME_DIFF]
                       ⇔  ((z∈C×{0} ou z=*) et ¬(z=*))      [somme_un_plus_point, z∈{*}⇔z=*]
                       ⇔  z∈C×{0}.
    Le « et ¬(z=*) » ÉLIMINE la branche z=* de la disjonction (un « ou » dont une
    branche est niée se réduit à l'autre).  INCONDITIONNEL."""
    from bourbaki.logique.i_1_termes_relations.formule import ou
    from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege import a_implique_a
    vc = _t(c)
    S = _S(c)                                             # C⊔{∅}
    C0 = _C0(c)                                            # C×{0}
    sing = E.singleton(_STAR)                              # {*}
    diff = E.difference(S, sing)                           # (C⊔{∅})∖{*}
    vz = var("z")
    z_in_C0 = appartient(vz, C0)
    z_eq_star = egal(vz, _STAR)

    # z ∈ diff ⇔ (z∈S et ¬(z∈{*}))
    ax_diff = _inst_diff(S, sing, vz)                     # z∈diff ⇔ (z∈S et ¬(z∈{*}))
    # z∈{*} ⇔ z=*  ⇒  ¬(z∈{*}) ⇔ ¬(z=*)
    sing_ssi = _dans_singleton_star_ssi(vz)               # z∈{*} ⇔ z=*
    # z∈S ⇔ (z∈C×{0} ou z=*)
    sup = somme_un_plus_point(c, vz)                      # z∈C⊔{∅} ⇔ (z∈C×{0} ou z=*)

    # ── On prouve directement l'équivalence cible  z∈diff ⇔ z∈C×{0}  par double sens. ──
    # ⇒ : z∈diff ⇒ z∈C×{0}
    h_diff = N.assume(appartient(vz, diff))
    z_in_S_and = N.modus_ponens(h_diff, equivalence_avant(ax_diff))   # z∈S et ¬(z∈{*})
    z_in_S = conjonction_elim_gauche(z_in_S_and)                      # z∈S
    nz_sing = conjonction_elim_droite(z_in_S_and)                     # ¬(z∈{*})
    # ¬(z∈{*}) ⇒ ¬(z=*)   (contraposée de z=* ⇒ z∈{*}, i.e. ⇐ de sing_ssi)
    from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import contraposition
    nz_star = N.modus_ponens(nz_sing,
        contraposition(equivalence_arriere(sing_ssi)))               # ¬(z=*)
    disj = N.modus_ponens(z_in_S, equivalence_avant(sup))            # z∈C×{0} ou z=*
    # (z∈C×{0} ou z=*) et ¬(z=*) ⇒ z∈C×{0}   (cas : branche z=* contredit ¬(z=*))
    from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import cas
    br_left = N.loi_deduction(z_in_C0, N.assume(z_in_C0))             # z∈C×{0} ⇒ z∈C×{0}
    # branche z=* : z=* et ¬(z=*) ⊢ z∈C×{0}  (ex falso quodlibet : ¬P ⇒ (P ⇒ Z))
    h_star = N.assume(z_eq_star)
    falso = N.modus_ponens(h_star,
        N.modus_ponens(nz_star, N.s2(non(z_eq_star), z_in_C0)))      # z∈C×{0}
    br_right = N.loi_deduction(z_eq_star, falso)                     # z=* ⇒ z∈C×{0}
    z_in_C0_thm = cas(disj, br_left, br_right)                       # z∈C×{0}
    fwd = N.loi_deduction(appartient(vz, diff), z_in_C0_thm)         # z∈diff ⇒ z∈C×{0}

    # ⇐ : z∈C×{0} ⇒ z∈diff
    h_c0 = N.assume(z_in_C0)
    # z∈S  (injection gauche : z∈C×{0} ⇒ (z∈C×{0} ou z=*) ⇒ z∈S)
    in_disj = N.modus_ponens(h_c0, N.s2(z_in_C0, z_eq_star))         # z∈C×{0} ou z=*
    z_in_S2 = N.modus_ponens(in_disj, equivalence_arriere(sup))     # z∈S
    # ¬(z=*)  : si z=*, alors *=z∈C×{0} ; or ¬(*∈C×{0}) (marqueur_hors_copie_gauche)
    from bourbaki.cardinaux.arithmetique.ensembles_prop8_plus_point import marqueur_hors_copie_gauche
    n_star_in_C0 = marqueur_hors_copie_gauche(c)                     # ¬(*∈C×{0})
    h_zstar = N.assume(z_eq_star)
    star_in_C0 = N.modus_ponens(h_c0, equivalence_avant(N.modus_ponens(
        h_zstar, N.s6(vz, _STAR, "w", appartient(var("w"), C0)))))   # *∈C×{0}
    falso2 = N.modus_ponens(star_in_C0,
        N.modus_ponens(n_star_in_C0, N.s2(non(appartient(_STAR, C0)), non(z_eq_star))))
    nz_star2 = N.modus_ponens(N.loi_deduction(z_eq_star, falso2), N.s1(non(z_eq_star)))  # ¬(z=*)
    # ¬(z∈{*})  (de ¬(z=*) via contraposée de z∈{*} ⇒ z=*, i.e. ⇒ de sing_ssi)
    nz_sing2 = N.modus_ponens(nz_star2,
        contraposition(equivalence_avant(sing_ssi)))                 # ¬(z∈{*})
    z_in_diff = N.modus_ponens(conjonction_intro(z_in_S2, nz_sing2),
                               equivalence_arriere(ax_diff))          # z∈diff
    bwd = N.loi_deduction(z_in_C0, z_in_diff)                        # z∈C×{0} ⇒ z∈diff

    equiv_z = conjonction_intro(fwd, bwd)                            # z∈diff ⇔ z∈C×{0}
    char_diff = N.generalisation("z", equiv_z)
    char_C0 = N.generalisation("z", conjonction_intro(
        a_implique_a(z_in_C0), a_implique_a(z_in_C0)))
    return egalite_par_extension(char_diff, char_C0, diff, C0, "z")  # (C⊔{∅})∖{*} = C×{0}


# ════════════════════════════════════════════════════════════════════════════
#  PONT 3 (INCONDITIONNEL) — ⊢ Eq((C⊔{∅})∖{*}, C)   (S privé du marqueur ≃ C)
# ════════════════════════════════════════════════════════════════════════════
def eq_diff_marqueur_c(c="c"):
    """⊢ Eq((C⊔{∅}) ∖ {*}, C).   (retirer le point marqué d'un (c+1)-ensemble rend C.)

    (C⊔{∅})∖{*} = C×{0} (diff_marqueur_egal_copie) ; Eq(C, C×{0}) (eq_copie_gauche)
    ⇒ Eq(C×{0}, C) (symétrie) ; réécriture C×{0} ↦ (C⊔{∅})∖{*} (Leibniz S6) donne
    Eq((C⊔{∅})∖{*}, C).  INCONDITIONNEL — c'est le « retrait d'un point d'un
    (c+1)-ensemble laisse un c-ensemble », au point retiré FIXÉ = le marqueur."""
    vc = _t(c)
    C0 = _C0(c)                                           # C×{0}
    diff = E.difference(_S(c), E.singleton(_STAR))        # (C⊔{∅})∖{*}
    eq_diff_C0 = diff_marqueur_egal_copie(c)              # (C⊔{∅})∖{*} = C×{0}
    eq_C_C0 = eq_copie_gauche(c)                          # Eq(C, C×{0})
    eq_C0_C = N.modus_ponens(eq_C_C0, _eq_sym_t(vc, C0))  # Eq(C×{0}, C)
    # réécris le 1er argument C×{0} ↦ (C⊔{∅})∖{*} via (C⊔{∅})∖{*} = C×{0}
    # S6(diff, C0) : (diff = C0) ⇒ (Eq(diff,c) ⇔ Eq(C0,c))
    eq_diff_iff_C0 = N.modus_ponens(eq_diff_C0,
        N.s6(diff, C0, "w", equipotent(var("w"), vc)))   # Eq((C⊔{∅})∖{*},C) ⇔ Eq(C×{0},C)
    return N.modus_ponens(eq_C0_C, equivalence_arriere(eq_diff_iff_C0))  # Eq((C⊔{∅})∖{*}, C)


# ════════════════════════════════════════════════════════════════════════════
#  PONT FINAL (INCONDITIONNEL) — ⊢ ( b ≤ (C⊔{∅})∖{*} ) ⇒ ( b ≤ c )
# ════════════════════════════════════════════════════════════════════════════
def inf_egal_diff_marqueur_implique(b="b", c="c"):
    """⊢ ( b ≤ (C⊔{∅})∖{*} )  ⇒  ( b ≤ c ).   (transport final, INCONDITIONNEL.)

    b ≤ (C⊔{∅})∖{*} et Eq((C⊔{∅})∖{*}, C) (eq_diff_marqueur_c) ⇒ b ≤ c
    (inf_egal_via_eq_codom).  C'est le PONT qui ferme la branche non surjective une
    fois la surgery faite : il NE reste plus qu'à fabriquer l'injection b → S∖{*}."""
    vb, vc = _t(b), _t(c)
    diff = E.difference(_S(c), E.singleton(_STAR))        # (C⊔{∅})∖{*}
    le_b_diff = N.assume(inf_egal_card(vb, diff))         # b ≤ (C⊔{∅})∖{*}   [hyp]
    eq_diff_c = eq_diff_marqueur_c(c)                     # Eq((C⊔{∅})∖{*}, C)
    transport = inf_egal_via_eq_codom(vb, diff, vc)       # (b≤diff et Eq(diff,C)) ⇒ b≤c
    le_b_c = N.modus_ponens(conjonction_intro(le_b_diff, eq_diff_c), transport)   # b ≤ c
    return N.loi_deduction(inf_egal_card(vb, diff), le_b_c)


# ════════════════════════════════════════════════════════════════════════════
#  SURGERY ISOLÉE (REPORTÉE, hypothèse explicite) — l'unique maillon dur restant
# ════════════════════════════════════════════════════════════════════════════
def retrait_surgery_hyp(b, c, f="F"):
    """Énoncé de la SURGERY ISOLÉE (HYPOTHÈSE explicite, REPORTÉE) :
        ( est_injection_de(F, b, c+1)  et  image(F,b) ≠ c+1 )  ⇒  ( b ≤ (C⊔{∅})∖{*} ).

    ⚠️ NON PROUVÉ ici : la FABRICATION EFFECTIVE de l'injection b → (C⊔{∅})∖{*} à
    partir d'une injection f : b → Card(C⊔{∅}) non surjective.  Concrètement :
    f rate un point q ∈ c+1 ; on ramène q sur le marqueur * (échange ponctuel,
    transposition type Prop. 8, déjà outillée ensembles_prop8_transposition), ce qui
    place l'image de f dans S∖{*}.  C'est le SEUL maillon dur, et il est RÉDUIT au
    point retiré FIXÉ = le marqueur (tout le reste — transport cardinal↔ensemble et
    S∖{*} ≃ C — est CLOS dans ce module).  Posé en hypothèse explicite, déchargé par
    loi_deduction — jamais postulé."""
    vb, vc, vf = _t(b), _t(c), _t(f)
    succ_c = successeur(vc)                               # c+1
    diff = E.difference(_S(c), E.singleton(_STAR))        # (C⊔{∅})∖{*}
    inj = est_injection_de(vf, vb, succ_c)
    non_surj = non(egal(E.image(vf, vb), succ_c))
    return impl(et(inj, non_surj), inf_egal_card(vb, diff))


# ════════════════════════════════════════════════════════════════════════════
#  ASSEMBLAGE — retrait_point_hyp MODULO la surgery isolée
# ════════════════════════════════════════════════════════════════════════════
def retrait_point_hyp_enonce(b, c, f="F"):
    """L'ÉNONCÉ EXACT du report fermé (identique à ensembles_cardinal_pas_entre) :
        ( est_injection_de(F, b, c+1)  et  image(F,b) ≠ c+1 )  ⇒  ( b ≤ c )."""
    vb, vc, vf = _t(b), _t(c), _t(f)
    succ_c = successeur(vc)
    inj = est_injection_de(vf, vb, succ_c)
    non_surj = non(egal(E.image(vf, vb), succ_c))
    return impl(et(inj, non_surj), inf_egal_card(vb, vc))


def retrait_point_hyp_assemble(b="b", c="c", f="F"):
    """{ retrait_surgery_hyp(b,c,F) } ⊢ retrait_point_hyp(b,c,F)
       = ( est_injection_de(F,b,c+1) et image(F,b)≠c+1 ) ⇒ ( b ≤ c ).

    🎯 La BRANCHE NON SURJECTIVE du LEMME N, ASSEMBLÉE modulo la SEULE surgery
    isolée.  Sous l'hypothèse  ( inj et ¬surj ) :
       • retrait_surgery_hyp ⇒ b ≤ (C⊔{∅})∖{*}    (le SEUL maillon dur, REPORTÉ) ;
       • inf_egal_diff_marqueur_implique ⇒ b ≤ c   (PONT FINAL, INCONDITIONNEL).
    Conclusion ÉGALE LITTÉRALEMENT au report retrait_point_hyp de
    ensembles_cardinal_pas_entre.  Une hypothèse résiduelle ISOLÉE
    (retrait_surgery_hyp), déchargée par loi_deduction — jamais postulée."""
    vb, vc, vf = _t(b), _t(c), _t(f)
    succ_c = successeur(vc)                               # c+1
    diff = E.difference(_S(c), E.singleton(_STAR))        # (C⊔{∅})∖{*}
    inj = est_injection_de(vf, vb, succ_c)
    non_surj = non(egal(E.image(vf, vb), succ_c))
    ante = et(inj, non_surj)

    h_ante = N.assume(ante)                               # (inj et ¬surj)
    # SURGERY (isolée) : (inj et ¬surj) ⇒ b ≤ (C⊔{∅})∖{*}
    h_surgery = N.assume(retrait_surgery_hyp(b, c, f))   # l'hypothèse explicite
    le_b_diff = N.modus_ponens(h_ante, h_surgery)        # b ≤ (C⊔{∅})∖{*}
    # PONT FINAL (clos) : b ≤ (C⊔{∅})∖{*} ⇒ b ≤ c
    pont = inf_egal_diff_marqueur_implique(b, c)         # (b≤diff) ⇒ (b≤c)
    le_b_c = N.modus_ponens(le_b_diff, pont)             # b ≤ c
    return N.loi_deduction(ante, le_b_c)                 # (inj et ¬surj) ⇒ b≤c   [hyp surgery]


def retrait_point_hyp_mod_surgery(b="b", c="c", f="F"):
    """⊢ retrait_surgery_hyp(b,c,F) ⇒ retrait_point_hyp(b,c,F).   (THÉORÈME CLOS, 0 hyp.)

    Forme CONDITIONNELLE entièrement CLOSE : la surgery isolée est DÉCHARGÉE
    (loi_deduction) en antécédent explicite.  La conséquence EST le report
    retrait_point_hyp(b,c,F) de ensembles_cardinal_pas_entre LITTÉRALEMENT.  Aucune
    hypothèse résiduelle, rien postulé : dès que retrait_surgery_hyp est prouvée
    (l'échange ponctuel ramenant le point raté sur le marqueur), la branche non
    surjective du LEMME N est inconditionnelle, et le LEMME N tout entier est clos
    (modulo est_cardinal(b), cf. cardinal_pas_entre_conditionnel)."""
    vb, vc, vf = _t(b), _t(c), _t(f)
    inner = retrait_point_hyp_assemble(b, c, f)          # retrait_point_hyp [hyp surgery]
    surgery = retrait_surgery_hyp(b, c, f)
    return N.loi_deduction(surgery, inner)               # surgery ⇒ retrait_point_hyp


__all__ = [
    "eq_succ_ensemble",
    "inf_egal_via_eq_codom",
    "diff_marqueur_egal_copie",
    "eq_diff_marqueur_c",
    "inf_egal_diff_marqueur_implique",
    "retrait_surgery_hyp",
    "retrait_point_hyp_enonce",
    "retrait_point_hyp_assemble",
    "retrait_point_hyp_mod_surgery",
]
