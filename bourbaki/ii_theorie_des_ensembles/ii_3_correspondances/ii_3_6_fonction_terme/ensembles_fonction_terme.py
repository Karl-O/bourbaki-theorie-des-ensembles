"""§II.3.6 — Définition d'une fonction par un terme (Critère C54, E.II.46).

La fonction x↦T (x∈A, T∈C) a pour graphe
    F := {w | (∃x)(∃y)(w=(x,y) et x∈A et y=T)}.
Critère C54 : R := « x∈A et y=T » admet F pour graphe par rapport à x,y ;
ce graphe est FONCTIONNEL ; sa première projection est A, sa seconde est
B = {T | x∈A} (II, p.6).

On certifie ici (toolbox abrégée) :
  - `membre_graphe_terme`  ⊢ ((u,v)∈F) ⇔ (u∈A et v=T[u])   (réduction du graphe,
        via Prop. 1 et l'élimination des témoins x,y) ;
  - `graphe_terme_fonctionnel`  ⊢ F est fonctionnel   (le cœur de C54 :
        (u,v)∈F et (u,v')∈F entraîne v=v', par unicité de la valeur T[u]).

NB : x, y sont les liants du corps (donc l'assemblage de F ne contient ni x ni y,
fidèle à C54). u, v, v' sont des lettres-paramètres distinctes de x, y, w.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, egal, et, impl, appartient, existe, pourtout, subst_t, libres_t, libres_f, _fraiche
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege import syllogisme
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (conjonction_intro, conjonction_elim_gauche,
                               conjonction_elim_droite, equivalence_avant,
                               equivalence_arriere, equivalence_transitivite,
                               instancie, instanciation_en_x)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import symetrie, composer_egalites, congruence_terme
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import existe_elimination
from bourbaki.ii_theorie_des_ensembles.ii_2_couples.ii_2_1_definition_couples.ensembles_couples import couple_egal_implique_composantes


def _inst_axiome(a, t, w, x="x", y="y"):
    """⊢ (W∈F) ⇔ (∃x)(∃y)(W=(x,y) et (x∈A et y=T)).   (instance de l'axiome C54.)"""
    th = E.theorie_graphe_terme(a, t, x, y, "w")
    ax = N.axiome(th, E.axiome_graphe_terme(a, t, x, y, "w"))   # (∀w)(...)
    return instancie(ax, w)


# @livre Ch.II §3.6 Crit.54 | E II.15 L.31-35 | PDF p.66
def membre_graphe_terme(a="A", t=None, u="u", v="v", x="x", y="y"):
    """⊢ ((u,v) ∈ F) ⇔ (u∈A et v=T[u]),   F = graphe_terme(A,T).

    T[u] = (u|x)T.  Réduit l'appartenance au graphe (∃-définie) à la condition
    explicite « u∈A et v=valeur du terme en u »  (via Prop. 1 + élim. des témoins).
    """
    vA = var(a) if isinstance(a, str) else a
    vu, vv, vx, vy = var(u), var(v), var(x), var(y)
    if t is None:
        t = E.valeur(var("F"), vx)        # défaut sans intérêt ; appels réels passent T
    Tu = subst_t(vu, x, t)                # T[u]
    cuv = E.couple(vu, vv)
    inst = _inst_axiome(vA, t, cuv, x, y)            # ((u,v)∈F) ⇔ (∃x)(∃y) body
    body = et(et(egal(cuv, E.couple(vx, vy)), appartient(vx, vA)), egal(vy, t))

    # ── ⇒ : (∃x)(∃y) body  ⇒  (u∈A et v=T[u]) ──────────────────────────────────
    hb = N.assume(body)
    eqcpl = conjonction_elim_gauche(conjonction_elim_gauche(hb))   # (u,v)=(x,y)
    xA = conjonction_elim_droite(conjonction_elim_gauche(hb))      # x∈A
    yT = conjonction_elim_droite(hb)                               # y=T
    comps = N.modus_ponens(eqcpl, couple_egal_implique_composantes(u, v, x, y))  # u=x et v=y
    ux = conjonction_elim_gauche(comps)                            # u=x
    vy_eq = conjonction_elim_droite(comps)                         # v=y
    # u∈A : de x∈A et u=x (Leibniz)
    uA = N.modus_ponens(xA, equivalence_arriere(N.modus_ponens(
        ux, N.s6(vu, vx, "w", appartient(var("w"), vA)))))         # u∈A
    # v=T[u] : v=y, y=T(=t), et t=T[u] par CONGRUENCE DIRECTE (trou = x lui-même, licite car
    # x est LIBRE dans t) ⇒ T[u] = subst_t(vu,x,t) = Tu (IDENTIQUE au sens ⇐ ; correctif verrou-τ
    # 2026-07-24 : l'ancien détour par un trou frais `hole` produisait un T[u] α-divergent de Tu
    # quand t est binder-riche, cassant l'équivalence ⇒ division_successeur/distributivite_cardinale).
    xu = N.modus_ponens(ux, symetrie(vu, vx))                      # x=u
    Tx_Tu = N.modus_ponens(xu, congruence_terme(vx, vu, t, x))     # (x=u) ⇒ (t = T[u])
    v_eq_Tu = composer_egalites(vy_eq, composer_egalites(yT, Tx_Tu))   # v=y=t=T[u]
    conc_av = conjonction_intro(uA, v_eq_Tu)                       # u∈A et v=T[u]
    avant = existe_elimination(existe_elimination(
        N.loi_deduction(body, conc_av), y), x)                     # (∃x)(∃y)body ⇒ conc

    # ── ⇐ : (u∈A et v=T[u])  ⇒  (∃x)(∃y) body ──────────────────────────────────
    hc = N.assume(et(appartient(vu, vA), egal(vv, Tu)))
    # témoins x:=u, y:=v.  (u|x)(v|y)body = ((u,v)=(u,v) et (u∈A et v=T[u]))
    refl = N.reflexivite(cuv)                                      # (u,v)=(u,v)
    wit = conjonction_intro(conjonction_intro(refl, conjonction_elim_gauche(hc)),
                            conjonction_elim_droite(hc))           # = (u|x)(v|y)body
    # (v|y)body, puis (∃y), puis (u|x), puis (∃x)
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import subst_f
    body_uy = subst_f(vu, x, body)            # (u|x)body
    ex_y = N.modus_ponens(wit, N.s5(body_uy, vv, y))              # (∃y)(u|x)body
    ex_xy = N.modus_ponens(ex_y, N.s5(existe(y, body), vu, x))    # (∃x)(∃y)body
    arriere = N.loi_deduction(et(appartient(vu, vA), egal(vv, Tu)), ex_xy)

    eq_ex = conjonction_intro(avant, arriere)                     # (∃x)(∃y)body ⇔ conc
    return equivalence_transitivite(inst, eq_ex)                  # ((u,v)∈F) ⇔ (u∈A et v=T[u])


def _lies_t(t):
    """Ensemble des noms LIÉS (liants τ / ∃) apparaissant dans le terme t."""
    if t.tag == "var":
        return set()
    if t.tag == "tau":
        return {t.lieur} | _lies_f(t.args[0])
    s = set()
    for a in t.args:
        s |= _lies_t(a)
    return s


def _lies_f(f):
    s = set()
    if f.lieur:
        s.add(f.lieur)
    for tt in f.termes:
        s |= _lies_t(tt)
    for g in f.sous:
        s |= _lies_f(g)
    return s


def _noms_t(t):
    """Tous les noms (libres ET liés) apparaissant dans t — pour choisir des liants frais."""
    if t.tag == "var":
        return {t.nom}
    if t.tag == "tau":
        return {t.lieur} | _noms_f(t.args[0])
    s = set()
    for a in t.args:
        s |= _noms_t(a)
    return s


def _noms_f(f):
    s = set()
    if f.lieur:
        s.add(f.lieur)
    for tt in f.termes:
        s |= _noms_t(tt)
    for g in f.sous:
        s |= _noms_f(g)
    return s


def _gtf_preuve(vA, t, x, un, vn, vpn, yn):
    """⊢ (∀un)(∀vn)(∀vpn)(((un,vn)∈F et (un,vpn)∈F) ⇒ vn=vpn),  F=graphe_terme(A,t).

    Cœur factorisé : paramétré par les liants (un = antécédent, subst dans t ; yn = liant
    interne d'axiome) pour permettre le chemin à LIANTS FRAIS (verrou-τ)."""
    vu, vv, vvp = var(un), var(vn), var(vpn)
    Tu = subst_t(vu, x, t)                       # T[un]
    F = E.graphe_terme(vA, t, x)
    lem_v = membre_graphe_terme(vA, t, un, vn, x, yn)
    lem_vp = membre_graphe_terme(vA, t, un, vpn, x, yn)
    ante = et(appartient(E.couple(vu, vv), F), appartient(E.couple(vu, vvp), F))
    h = N.assume(ante)
    v_Tu = conjonction_elim_droite(N.modus_ponens(conjonction_elim_gauche(h),
                                                  equivalence_avant(lem_v)))
    vp_Tu = conjonction_elim_droite(N.modus_ponens(conjonction_elim_droite(h),
                                                   equivalence_avant(lem_vp)))
    v_vp = composer_egalites(v_Tu, N.modus_ponens(vp_Tu, symetrie(vvp, Tu)))
    inner = N.loi_deduction(ante, v_vp)
    return N.generalisation(un, N.generalisation(vn, N.generalisation(vpn, inner)))


# @livre Ch.II §3.6 Crit.54 | E II.15 L.31-35 | PDF p.66
def graphe_terme_fonctionnel(a="A", t=None, x="x", y="y"):
    """⊢ F est fonctionnel,   F = graphe_terme(A,T).   (Critère C54, cœur.)

    Forme : ⊢ (∀u)(∀v)(∀v')(((u,v)∈F et (u,v')∈F) ⇒ v=v').
    Preuve : (u,v)∈F ⇒ v=T[u] et (u,v')∈F ⇒ v'=T[u] (lemme), donc v=v'.

    ✅ VERROU-τ RÉSOLU À LA RACINE (2026-07-24, fix subst) : l'ancien échec « modus
    ponens : mineure ≠ antécédent » sur les t liant u/v/z (τ Card-valués) venait d'un
    renommage GRATUIT de la substitution (elle renommait un liant homonyme même quand la
    variable substituée n'était PAS libre dessous ⇒ les deux chemins internes divergeaient
    en α).  Depuis le court-circuit CS de subst_t/subst_f ((T|x)t = t si x ∉ libres(t),
    outil_formule.py), les renommages restants sont tous NÉCESSAIRES et déterministes,
    identiques sur les deux chemins — les liants codés en dur u/v/z fonctionnent pour
    TOUT t, y compris Card-valué (repro : somme_cardinale_commutative(diff, b) VERT)."""
    vA = var(a) if isinstance(a, str) else a
    vx = var(x)
    if t is None:
        t = E.valeur(var("F"), vx)
    return _gtf_preuve(vA, t, x, "u", "v", "z", y)


# @livre Ch.II §3.6 Crit.54 | E II.15 L.31-35 | PDF p.66  (le graphe de x↦T est un GRAPHE : tout membre est un couple — lecture directe de la forme-z de l'axiome C54)
def graphe_terme_est_graphe(a, t, x="x", y="y"):
    """⊢ est_un_graphe( graphe_terme(A,T) ).                          [CLOS, 0 hyp].

    La forme-z de l'axiome C54 (∀w)(w∈F ⇔ (∃x)(∃y)(w=(x,y) ∧ …)) donne, par
    affaiblissement du corps sous les deux ∃ (monotonie), (∀z)(z∈F ⇒ z couple).
    ⚠️ t ne doit pas contenir « z » libre (liant canonique d'est_un_graphe)."""
    vA = var(a) if isinstance(a, str) else a
    assert "z" not in libres_t(t if not isinstance(t, str) else var(t)),         "graphe_terme_est_graphe : t contient z libre"
    vz, vx, vy = var("z"), var(x), var(y)
    F = E.graphe_terme(vA, t, x)
    inst = _inst_axiome(vA, t, vz, x, y)          # z∈F ⇔ (∃x)(∃y)(corps)
    corps = et(et(egal(vz, E.couple(vx, vy)), appartient(vx, vA)), egal(vy, t))
    hb = N.assume(corps)
    eq = conjonction_elim_gauche(conjonction_elim_gauche(hb))       # z=(x_param,y_param)
    # ré-introduire les ∃ CANONIQUES x,y d'est_un_couple (témoins x_param,y_param)
    j1 = N.modus_ponens(eq, N.s5(egal(vz, E.couple(vx, var("y"))), vy, "y"))
    j2 = N.modus_ponens(j1, N.s5(
        existe("y", egal(vz, E.couple(var("x"), var("y")))), vx, "x"))
    imp = N.loi_deduction(corps, j2)
    m = existe_elimination(existe_elimination(imp, y), x)  # ∃∃corps ⇒ est_un_couple(z)
    zimp = syllogisme(equivalence_avant(inst), m)      # z∈F ⇒ est_un_couple(z)
    res = N.generalisation("z", zimp)
    cible = E.est_un_graphe(F)
    assert res.conclusion == cible, "graphe_terme_est_graphe : conclusion ≠"
    assert not res.hypotheses, "graphe_terme_est_graphe : NON clos"
    return res


__all__ = ["membre_graphe_terme", "graphe_terme_fonctionnel",
           "graphe_terme_est_graphe"]
