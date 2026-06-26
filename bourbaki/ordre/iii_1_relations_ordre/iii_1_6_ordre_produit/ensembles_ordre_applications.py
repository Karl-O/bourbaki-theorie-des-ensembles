"""Chapitre III §1.6 — Ordre « point par point » sur les applications (E III.6).

Bourbaki (E III.6, à propos de l'ordre PRODUIT) :  l'ensemble 𝓕(E;F) des
applications d'un ensemble E dans un ensemble ORDONNÉ F est muni de l'ordre
défini par la relation

    « f ≤ g  ⟺  quel que soit x∈E, f(x) ≤ g(x) »                       (E III.6)

(c'est, via l'isomorphisme canonique F^E ≅ 𝓕(E;F), la restriction de l'ordre
produit des ordres de F).  On formalise ici cette relation « point par point »
et l'HÉRITAGE par F→𝓕(E;F) de deux des trois axiomes de l'ordre : la
RÉFLEXIVITÉ et la TRANSITIVITÉ.

Conventions (fidèles au codage du projet, cf. ensembles_ordre_monotone) :
  • l'ordre sur l'ensemble but F est donné par un graphe GF ; « u ≤ v » s'écrit
    (u,v) ∈ GF,  soit _couple_dans(u,v,GF) ;
  • f est une application E → F ; la valeur f(x) au sens Bourbaki est la valeur
    du graphe, E.valeur(f, x, b="j")  (liant interne « j », lettre simple fraîche
    jamais utilisée comme liant de quantification — cf. _val de ensembles_ordre_
    monotone : on garde EXACTEMENT le même binder pour que les valeurs f(x)
    construites dans la définition et dans les preuves coïncident structurellement).

PÉRIMÈTRE HONNÊTE.  On formalise la définition et DEUX héritages :
  • RÉFLEXIVITÉ : sous { est_ordre(GF,F) }, toute application f : E→F vérifie
    f ≤ f  (point par point) ;
  • TRANSITIVITÉ : sous { est_ordre(GF,F) }, (f ≤ g et g ≤ h) ⇒ f ≤ h.
On NE prétend PAS l'antisymétrie « globale » f ≤ g et g ≤ f ⇒ f = g : elle exige
l'extensionnalité des applications (égalité des graphes fonctionnels), plus lourde
et HORS du périmètre de cette sous-section.

Les preuves sont CLOSES sous l'unique hypothèse honnête { est_ordre(GF,F) }
(est_clos == False), certifiées par le noyau abrégé (primitives N.* + tactiques).
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (
    Terme, var, et, impl, appartient, pourtout,
)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.ordre.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_relation import (
    est_ordre, reflexivite_sur,
)
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    conjonction_elim_gauche, conjonction_elim_droite, instancie,
)


def _terme(t):
    return t if isinstance(t, Terme) else var(t)


def _nom(t):
    """Nom (str) de la variable t, qu'on reçoive un Terme var('f') ou la chaîne 'f'.

    Sert à `generalisation`, qui exige le NOM du liant (str), alors que f est passé
    comme application (Terme ou chaîne)."""
    return t.nom if isinstance(t, Terme) else t


def _couple_dans(t, u, G):
    """Formule « (t,u) ∈ G »  (lecture « t ≤ u » pour l'ordre de graphe G)."""
    return appartient(E.couple(_terme(t), _terme(u)), _terme(G))


def _val(f, x):
    """f(x) au sens Bourbaki = valeur du graphe f en x.

    Liant interne forcé à « j », EXACTEMENT comme _val de ensembles_ordre_monotone :
    lettre simple fraîche jamais employée comme liant de quantification (donc pas de
    capture, et α-τ-compatible).  Garder ce binder identique entre la définition et
    les preuves est INDISPENSABLE pour que les valeurs f(x) coïncident
    structurellement (==)."""
    return E.valeur(_terme(f), _terme(x), b="j")


def _envoie_dans(f, E_set, F_set, x="x"):
    """Hypothèse « f est une application E→F » sous la forme suffisante pour les
    preuves : (∀x)(x∈E ⇒ f(x)∈F)  (f(x) au sens du graphe).

    Sert d'antécédent au théorème de réflexivité : f ≤ f n'a de sens que si f a
    bien ses valeurs dans F (où vit l'ordre GF)."""
    vx, vE, vF = var(x), _terme(E_set), _terme(F_set)
    return pourtout(x, impl(appartient(vx, vE), appartient(_val(f, vx), vF)))


# ════════════════════════════════════════════════════════════════════════════
#  DÉFINITION — ordre « point par point » sur les applications  (E III.6)
# ════════════════════════════════════════════════════════════════════════════
# @livre Ch.III §1.6 Rem.- | E III.6 L.41-49 | PDF p.109
def ordre_pointwise(GF, F, f, g, E_set, x="x"):
    """ordre_pointwise(GF,F,f,g,E) := (∀x)( x∈E ⇒ (f(x), g(x)) ∈ GF ).

    « f ≤ g pour l'ordre point par point sur E » : en chaque point x∈E, la valeur
    f(x) est inférieure (au sens du graphe GF d'ordre sur le but F) à g(x).  C'est
    la relation d'ordre que Bourbaki met sur 𝓕(E;F) lorsque F est ordonné par GF
    (E III.6, Remarque ; restriction de l'ordre produit).  Le 2e argument F n'entre
    pas dans la formule (il documente l'ensemble but où vit l'ordre) ; le liant x
    est frais.  f(x), g(x) = _val(f,x), _val(g,x)."""
    vx, vE = var(x), _terme(E_set)
    return pourtout(x, impl(appartient(vx, vE),
                            _couple_dans(_val(f, vx), _val(g, vx), GF)))


# ════════════════════════════════════════════════════════════════════════════
#  HÉRITAGE 1 — RÉFLEXIVITÉ : sous est_ordre(GF,F), toute f : E→F vérifie f ≤ f
# ════════════════════════════════════════════════════════════════════════════
# @livre Ch.III §1.6 Rem.- | E III.6 L.31-33 | PDF p.109
def pointwise_reflexif(GF="GF", F="F", E_set="E", f="f", x="x", y="y", z="z"):
    """{ est_ordre(GF,F) } ⊢
        (∀f)( (∀x)(x∈E ⇒ f(x)∈F) ⇒ ordre_pointwise(GF,F,f,f,E) ).

    RÉFLEXIVITÉ héritée de l'ordre de F (E III.6 : l'ordre point par point est un
    ordre « comme on le vérifie aisément »).  Si f envoie E dans F, alors pour
    chaque x∈E on a f(x)∈F, donc (f(x),f(x))∈GF par la réflexivité de l'ordre GF ;
    en généralisant sur x on obtient f ≤ f, puis en déchargeant l'hypothèse
    « f : E→F » et en généralisant sur f on conclut.

    L'antisymétrie de GF n'est PAS utilisée : on n'extrait que la réflexivité."""
    vE, vF, vx = _terme(E_set), _terme(F), var(x)
    Hord = N.assume(est_ordre(GF, F, x, y, z))                   # ordre sur F
    # réflexivité sur F : (∀x)(x∈F ⇒ (x,x)∈GF)  (conj_elim gauche∘gauche)
    refl_F = conjonction_elim_gauche(conjonction_elim_gauche(Hord))
    # corps : (∀x)(x∈E ⇒ f(x)∈F) ⇒ ordre_pointwise(GF,F,f,f,E)
    Hbut = N.assume(_envoie_dans(f, E_set, F, x))               # (∀x)(x∈E ⇒ f(x)∈F)
    Hx = N.assume(appartient(vx, vE))                           # x∈E
    fx_in = N.modus_ponens(Hx, instancie(Hbut, vx))            # f(x)∈F
    # réflexivité de GF en f(x) : f(x)∈F ⇒ (f(x),f(x))∈GF
    fxfx = N.modus_ponens(fx_in, instancie(refl_F, _val(f, vx)))  # (f(x),f(x))∈GF
    body = N.loi_deduction(appartient(vx, vE), fxfx)           # x∈E ⇒ (f(x),f(x))∈GF
    pw = N.generalisation(x, body)                             # ordre_pointwise(GF,F,f,f,E)
    impl_f = N.loi_deduction(_envoie_dans(f, E_set, F, x), pw)  # (∀x…) ⇒ f≤f
    return N.generalisation(_nom(f), impl_f)                   # (∀f)( … ⇒ f≤f )


# ════════════════════════════════════════════════════════════════════════════
#  HÉRITAGE 2 — TRANSITIVITÉ : sous est_ordre(GF,F), (f≤g et g≤h) ⇒ f≤h
# ════════════════════════════════════════════════════════════════════════════
def cible_transitif(GF, F, f, g, h, E_set, x="x"):
    """Conclusion visée du théorème de transitivité (pour comparaison == en test) :
        ( ordre_pointwise(GF,F,f,g,E) et ordre_pointwise(GF,F,g,h,E) )
            ⇒ ordre_pointwise(GF,F,f,h,E)."""
    return impl(et(ordre_pointwise(GF, F, f, g, E_set, x),
                   ordre_pointwise(GF, F, g, h, E_set, x)),
                ordre_pointwise(GF, F, f, h, E_set, x))


# @livre Ch.III §1.6 Rem.- | E III.6 L.31-33 | PDF p.109
def pointwise_transitif(GF="GF", F="F", f="f", g="g", h="h",
                        E_set="E", x="x", y="y", z="z"):
    """{ est_ordre(GF,F) } ⊢
        ( ordre_pointwise(GF,F,f,g,E) et ordre_pointwise(GF,F,g,h,E) )
            ⇒ ordre_pointwise(GF,F,f,h,E).

    TRANSITIVITÉ héritée de l'ordre de F (E III.6).  Soit x∈E : de f ≤ g on tire
    (f(x),g(x))∈GF, de g ≤ h on tire (g(x),h(x))∈GF ; la transitivité de l'ordre
    GF, instanciée en (f(x), g(x), h(x)), donne (f(x),h(x))∈GF.  En généralisant
    sur x on obtient f ≤ h, puis on décharge la conjonction des deux hypothèses
    point par point.

    L'antisymétrie de GF n'est PAS utilisée : on n'extrait que la transitivité."""
    from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import conjonction_intro
    vE, vx = _terme(E_set), var(x)
    Hord = N.assume(est_ordre(GF, F, x, y, z))                  # ordre sur F
    trans_F = conjonction_elim_droite(Hord)                    # transitivite_rel(GF)
    # hypothèse UNIQUE point par point : la conjonction (f≤g et g≤h), pour pouvoir
    # la décharger d'un seul coup (loi_deduction retire littéralement cette formule).
    hyp_conj = et(ordre_pointwise(GF, F, f, g, E_set, x),
                  ordre_pointwise(GF, F, g, h, E_set, x))
    Hconj = N.assume(hyp_conj)                                 # f≤g et g≤h
    Hfg = conjonction_elim_gauche(Hconj)                       # f ≤ g
    Hgh = conjonction_elim_droite(Hconj)                       # g ≤ h
    # corps : x∈E ⇒ (f(x),h(x))∈GF
    Hx = N.assume(appartient(vx, vE))                          # x∈E
    fg_x = N.modus_ponens(Hx, instancie(Hfg, vx))             # (f(x),g(x))∈GF
    gh_x = N.modus_ponens(Hx, instancie(Hgh, vx))             # (g(x),h(x))∈GF
    # transitivité de GF en (f(x),g(x),h(x)) :
    #   ((f(x),g(x))∈GF et (g(x),h(x))∈GF) ⇒ (f(x),h(x))∈GF
    fx, gx, hx = _val(f, vx), _val(g, vx), _val(h, vx)
    trans_inst = instancie(instancie(instancie(trans_F, fx), gx), hx)
    fh_x = N.modus_ponens(conjonction_intro(fg_x, gh_x), trans_inst)   # (f(x),h(x))∈GF
    body = N.loi_deduction(appartient(vx, vE), fh_x)          # x∈E ⇒ (f(x),h(x))∈GF
    pw_fh = N.generalisation(x, body)                         # ordre_pointwise(GF,F,f,h,E)
    return N.loi_deduction(hyp_conj, pw_fh)                   # (f≤g et g≤h) ⇒ f≤h


__all__ = [
    "ordre_pointwise",
    "pointwise_reflexif",
    "pointwise_transitif",
    "cible_transitif",
]
