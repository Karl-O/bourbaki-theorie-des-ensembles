"""Chapitre III §1.11 — REMARQUE (E.III.13, après Déf. 8) : un ensemble ordonné
RÉTICULÉ est FILTRANT à droite ET à gauche.

Convention « graphe G » de `ensembles_ordre_relation.py` : x≤y := (x,y)∈G.  Un
ensemble réticulé (treillis) est un ensemble ordonné dans lequel toute paire
{x,y} admet une borne supérieure ET une borne inférieure (E.III.1.11, Déf. 8) :

    est_reticule(G,E) := est_ordre(G,E) et
        (∀x)(∀y)((x∈E et y∈E) ⇒
            (∃s)(∃i)(borne_superieure(G,{x,y},s,E) et borne_inferieure(G,{x,y},i,E))).

Filtrant à droite / à gauche pour l'ordre de graphe G (E.III.1.10, Déf. 7) :

    R_G(u,v) := (u,v)∈G   (la relation ≤ portée par le graphe G)
    filtrant_droite_G(G,E) := est_filtrant_droite(R_G, E)
        = (∀x)(∀y)((x∈E et y∈E) ⇒ (∃z)(z∈E et (x,z)∈G et (y,z)∈G))
    filtrant_gauche_G(G,E) := est_filtrant_gauche(R_G, E)
        = (∀x)(∀y)((x∈E et y∈E) ⇒ (∃z)(z∈E et (z,x)∈G et (z,y)∈G)).

THÉORÈME (forme « graphe », CLOS) — `reticule_implique_filtrant_droite_gauche` :

  { est_reticule(G,E) } ⊢ ( filtrant_droite_G(G,E) et filtrant_gauche_G(G,E) ).

  « Un ensemble ordonné réticulé est évidemment filtrant à droite et à gauche. »
  (E.III.13, Remarque après la Définition 8.)

  PREUVE.  Soient x,y ∈ E.  Le réticulé fournit une borne supérieure s et une
  borne inférieure i de la paire {x,y}.  La borne supérieure s est un MAJORANT de
  {x,y} : s∈E, (x,s)∈G et (y,s)∈G (instanciation du majorant en x∈{x,y} puis
  y∈{x,y}, lemmes membre_paire_gauche/droite).  Donc s est un majorant commun de
  x et y : E est filtrant à DROITE.  Dualement, la borne inférieure i est un
  MINORANT de {x,y} : i∈E, (i,x)∈G et (i,y)∈G ; i est un minorant commun : E est
  filtrant à GAUCHE.  Les témoins existentiels s puis i sont déchargés par
  `existe_elimination` (s,i ne figurent pas dans les corps filtrants).

  theorie_ensembles INTANGIBLE = 22 : tout est DÉRIVÉ (primitives N.* du noyau
  LCF), aucun axiome nouveau.  (E.III.13, Remarque.)
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, et, impl, appartient, existe,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.ii_theorie_des_ensembles.ii_2_couples.ii_2_1_definition_couples.ensembles_couples import (
    membre_paire_gauche, membre_paire_droite,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    instancie,
)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import existe_elimination
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_relation import (
    _couple_dans,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_monotone import (
    est_reticule, admet_borne_sup_inf,
)


def _t(t):
    return t if isinstance(t, Terme) else var(t)


# liants des bornes sup/inf dans est_reticule / admet_borne_sup_inf (défauts du
# projet) : la paire {x,y} y est notée par le liant interne « u », le « plus petit
# majorant » / « plus grand minorant » par « y ».  On les fixe ici pour reconstruire
# EXACTEMENT les formules manipulées.
_S, _I, _U = "s", "i", "u"
# liant du témoin existentiel des prédicats filtrants (défaut de est_filtrant_*).
_Z = "z"


def _R_G(G):
    """Relation d'ordre portée par le graphe G : R_G(u,v) := (u,v)∈G.

    C'est l'encodage commun aux modules §III.1 (cf. `_filtrant_droite_G` de la
    Proposition 10) : la relation ≤ est lue sur l'appartenance au graphe."""
    return lambda u, v: _couple_dans(u, v, G)


def _filtrant_droite_G(G, E_set):
    """filtrant_droite_G(G,E) := est_filtrant_droite(R_G, E)  (E.III.1.10, Déf. 7)."""
    return E.est_filtrant_droite(_R_G(G), _t(E_set))


def _filtrant_gauche_G(G, E_set):
    """filtrant_gauche_G(G,E) := est_filtrant_gauche(R_G, E)  (E.III.1.10, Déf. 7)."""
    return E.est_filtrant_gauche(_R_G(G), _t(E_set))


def cible_reticule_implique_filtrant(G="G", E_set="E"):
    """Conclusion attendue de `reticule_implique_filtrant_droite_gauche` :

        filtrant_droite_G(G,E) et filtrant_gauche_G(G,E).

    (Reconstruite à l'identique pour le test : égalité structurelle des liants.)"""
    return et(_filtrant_droite_G(G, E_set), _filtrant_gauche_G(G, E_set))


def hypothese_reticule(G="G", E_set="E"):
    """L'unique hypothèse honnête : est_reticule(G,E)  (E.III.1.11, Déf. 8)."""
    return est_reticule(G, E_set)


# ════════════════════════════════════════════════════════════════════════════
#  REMARQUE (E.III.13) — réticulé ⇒ filtrant à droite et à gauche
# ════════════════════════════════════════════════════════════════════════════
# @livre Ch.III §1.11 Rem.- | E III.13 L.19-21 | PDF p.116
def reticule_implique_filtrant_droite_gauche(G="G", E_set="E", x="x", y="y"):
    """🎯 { est_reticule(G,E) } ⊢ ( filtrant_droite_G(G,E) et filtrant_gauche_G(G,E) ).

    REMARQUE (E.III.13, après la Définition 8) : « Un ensemble ordonné réticulé est
    évidemment filtrant à droite et à gauche. »  Pour x,y∈E, le réticulé donne une
    borne supérieure s (majorant commun ⇒ filtrant à droite) et une borne
    inférieure i (minorant commun ⇒ filtrant à gauche) de la paire {x,y}.  Les
    coordonnées (x,s)∈G, (y,s)∈G, (i,x)∈G, (i,y)∈G s'obtiennent en instanciant le
    majorant/minorant aux deux membres x∈{x,y}, y∈{x,y} (lemmes
    membre_paire_gauche/droite).  (E.III.13, Remarque.)
    """
    vG, vE = _t(G), _t(E_set)
    vx, vy = var(x), var(y)
    paire_xy = E.paire(vx, vy)

    # ── l'UNIQUE hypothèse honnête ────────────────────────────────────────────
    Hret = N.assume(est_reticule(G, E_set))               # est_ordre(G,E) et (∀x∀y)(…)
    # clause « toute paire admet bornes sup & inf » : (∀x)(∀y)((x∈E et y∈E)⇒…)
    toute_paire = conjonction_elim_droite(Hret)

    # ── corps filtrant : (x∈E et y∈E) ⇒ (∃z)(…)  pour les deux côtés ───────────
    Hxy = N.assume(et(appartient(vx, vE), appartient(vy, vE)))   # x∈E et y∈E
    # réticulé en (x,y) : (x∈E et y∈E) ⇒ (∃s)(∃i)(BS et BI)
    inst_xy = instancie(instancie(toute_paire, vx), vy)
    ex_si = N.modus_ponens(Hxy, inst_xy)                  # admet_borne_sup_inf(G,x,y,E)

    # corps du ∃s∃i : BS(s) et BI(i), avec témoins s,i FIXÉS (liants par défaut)
    vs, vi = var(_S), var(_I)
    bs = _bs(G, paire_xy, vs, E_set)                      # borne_superieure(G,{x,y},s,E)
    bi = _bi(G, paire_xy, vi, E_set)                      # borne_inferieure(G,{x,y},i,E)
    Hbody = N.assume(et(bs, bi))                          # BS(s) et BI(i)
    bs_thm = conjonction_elim_gauche(Hbody)              # borne_superieure(…)
    bi_thm = conjonction_elim_droite(Hbody)              # borne_inferieure(…)

    # ── DROITE : la borne sup s est un majorant commun ⇒ témoin z:=s ───────────
    droite_ex = _cote_filtrant(
        G, E_set, vx, vy, paire_xy, bs_thm, vs,
        gauche=False)                                     # (∃z)(z∈E et (x,z)∈G et (y,z)∈G)
    # décharge des témoins existentiels s puis i (absents de droite_ex)
    imp_d = N.loi_deduction(et(bs, bi), droite_ex)        # (BS et BI) ⇒ droite_ex
    imp_d = existe_elimination(imp_d, _I)                 # (∃i)(BS et BI) ⇒ droite_ex
    imp_d = existe_elimination(imp_d, _S)                 # (∃s)(∃i)(…) ⇒ droite_ex
    droite = N.modus_ponens(ex_si, imp_d)                 # droite_ex  (sous {Hret,Hxy})
    droite_corps = N.loi_deduction(
        et(appartient(vx, vE), appartient(vy, vE)), droite)
    filt_d = N.generalisation(x, N.generalisation(y, droite_corps))

    # ── GAUCHE : la borne inf i est un minorant commun ⇒ témoin z:=i ───────────
    gauche_ex = _cote_filtrant(
        G, E_set, vx, vy, paire_xy, bi_thm, vi,
        gauche=True)                                      # (∃z)(z∈E et (z,x)∈G et (z,y)∈G)
    imp_g = N.loi_deduction(et(bs, bi), gauche_ex)        # (BS et BI) ⇒ gauche_ex
    imp_g = existe_elimination(imp_g, _I)                 # (∃i)(BS et BI) ⇒ gauche_ex
    imp_g = existe_elimination(imp_g, _S)                 # (∃s)(∃i)(…) ⇒ gauche_ex
    gauche = N.modus_ponens(ex_si, imp_g)                 # gauche_ex  (sous {Hret,Hxy})
    gauche_corps = N.loi_deduction(
        et(appartient(vx, vE), appartient(vy, vE)), gauche)
    filt_g = N.generalisation(x, N.generalisation(y, gauche_corps))

    res = conjonction_intro(filt_d, filt_g)
    assert res.conclusion == cible_reticule_implique_filtrant(G, E_set), \
        "conclusion ≠ cible (filtrant droite et gauche)"
    return res


# ── helpers locaux — bornes sup/inf aux liants par défaut, et un côté filtrant ──
def _bs(G, A, m, E_set):
    """borne_superieure(G,A,m,E) aux MÊMES liants que admet_borne_sup_inf : majorant
    sur "u", « plus petit majorant » sur le liant frais "mbs" (cf. ANOMALIES capture)."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_relation import (
        borne_superieure,
    )
    return borne_superieure(G, A, m, E_set, _U, "mbs")


def _bi(G, A, m, E_set):
    """borne_inferieure(G,A,m,E) aux MÊMES liants que admet_borne_sup_inf : minorant
    sur "u", « plus grand minorant » sur le liant frais "mbi" (cf. ANOMALIES capture)."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_relation import (
        borne_inferieure,
    )
    return borne_inferieure(G, A, m, E_set, _U, "mbi")


def _cote_filtrant(G, E_set, vx, vy, paire_xy, borne_thm, temoin, gauche):
    """De la borne (sup si gauche=False, inf si gauche=True) construit le témoin
    filtrant et réintroduit l'existentielle (∃z)(…) attendue par est_filtrant_*.

    DROITE  (sup s) : majorant ⇒ (x,s)∈G, (y,s)∈G ;  corps z∈E et (x,z)∈G et (y,z)∈G.
    GAUCHE (inf i) : minorant ⇒ (i,x)∈G, (i,y)∈G ;  corps z∈E et (z,x)∈G et (z,y)∈G."""
    vE = _t(E_set)
    # majorant(sup) / minorant(inf) = projection gauche de la borne ; structure
    # commune : (m∈E et (∀u)(u∈{x,y} ⇒ (·)∈G)), seul le sens du couple diffère.
    extremal = conjonction_elim_gauche(borne_thm)         # majorant / minorant
    m_in_E = conjonction_elim_gauche(extremal)            # m∈E (m = sup ou inf)
    quant = conjonction_elim_droite(extremal)             # (∀u)(u∈{x,y} ⇒ (·)∈G)
    # u∈{x,y} ⇒ (·)∈G, instancié aux deux membres de la paire {x,y}
    cx = N.modus_ponens(membre_paire_gauche(vx, vy), instancie(quant, vx))  # (x,m)∈G ou (m,x)∈G
    cy = N.modus_ponens(membre_paire_droite(vx, vy), instancie(quant, vy))  # (y,m)∈G ou (m,y)∈G
    # corps du témoin filtrant : z∈E et (… selon le côté …)
    R = _R_G(G)
    if gauche:
        # est_filtrant_gauche : (z,x)∈G et (z,y)∈G  → réintroduit sur le liant z
        corps_z = et(et(appartient(var(_Z), vE), R(var(_Z), vx)), R(var(_Z), vy))
        corps_temoin = conjonction_intro(conjonction_intro(m_in_E, cx), cy)
    else:
        # est_filtrant_droite : (x,z)∈G et (y,z)∈G
        corps_z = et(et(appartient(var(_Z), vE), R(vx, var(_Z))), R(vy, var(_Z)))
        corps_temoin = conjonction_intro(conjonction_intro(m_in_E, cx), cy)
    # S5 : (témoin|z)corps_z ⇒ (∃z)corps_z ; corps_temoin EST (témoin|z)corps_z
    return N.modus_ponens(corps_temoin, N.s5(corps_z, temoin, _Z))


__all__ = [
    "reticule_implique_filtrant_droite_gauche",
    "cible_reticule_implique_filtrant",
    "hypothese_reticule",
]
