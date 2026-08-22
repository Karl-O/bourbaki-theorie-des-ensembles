# -*- coding: utf-8 -*-
"""§III.6.2 — R8' (étape 1) : L'ITÉRATION SUR ℕ PAR LE CRITÈRE C60-VRAI.

🎯 CIBLES :

    regle_iteration_vraie(S, a) :
        T{u} := τ_y( (u=∅ ∧ y=a)  ∨  (u≠∅ ∧ y=S{u(M(D u))}) )
        — LA règle de C63 (Bourbaki, note E III.46), avec le max RÉEL
        M = terme_plus_grand (§III.1.7), PAS le fallback dom.

    t_iter_en_vide(S, a)  :  ⊢ T(∅) = a                        [CLOS, 0 hyp]
    iteration_N_vrai      :  { regle_dans_V(T) }
                             ⊢ (∃g)( est_solution_rec(g, T, G_≤, ℕ) )

Le critère C60-VRAI (R7') instancié à (ℕ, ≤) : le bon ordre se DÉCHARGE par
bo_graphe_NN (CLOS) — il ne reste qu'UNE hypothèse honnête, la règle bornée.
Les ticks suivants évaluent l'équation en 0 (f(0)=a) et en succ n
(f(succ n)=S(f(n))) : la forme C63 du livre.

theorie_ensembles() INCHANGÉE (22).  Noyau INTACT.  S OPAQUE (callable).
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, et, ou, non, tau, existe,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E

from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
    composer_egalites,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_1_relations_ordre.iii_1_7_plus_grand_plus_petit.ensembles_terme_plus_grand import (
    terme_plus_grand,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    inf_egal_card,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_somme.ensembles_somme_equipotence import (
    _garde_disjonction,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_8_factorielle.ensembles_factorielle_zero import (
    _nn, _et_parts,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_1_n_objet_existence.ensembles_ensemble_NN import (
    ensemble_NN,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_1_n_objet_existence.ensembles_ordre_NN_graphe import (
    G_ordre_NN, bo_graphe_NN,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_recurrence_transfinie import (
    _graphe_R,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.couverture_rec.ensembles_heredite_rec import (
    regle_dans_V,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.couverture_rec.capstone.ensembles_unicite_globale import (
    est_solution_rec,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.couverture_rec.capstone.ensembles_critere_c60_vrai import (
    existence_solution,
)


def _t(t):
    """Coercion str/Terme → Terme."""
    return t if isinstance(t, Terme) else var(t)


def _cut(preuve, formule, thm):
    """Décharge l'hypothèse `formule` de `thm` par la preuve `preuve` (coupure)."""
    return N.modus_ponens(preuve, N.loi_deduction(formule, thm))


# @livre Ch.III §6.2 Crit.C63 | E III.46 L.21-24 | PDF p.149  (la règle de la note 2 :
#   T{u} = « a si u=∅, sinon S de la dernière valeur » — le M(D u) de Bourbaki)
def regle_iteration_vraie(S, a, yname="yitv"):
    """LA règle d'itération, max RÉEL (patron regle_factorielle, S-générique).

    S : Terme→Terme (le pas) ; a : Terme (la valeur initiale).  Callable OPAQUE
    consommable par le critère C60-vrai.  Liants m/x du τ-max HORS des liants
    cardinaux (piège du 27 juil.)."""
    va = _t(a)

    def T(u):
        vu = _t(u)
        Du = E.dom(vu)
        prev = E.valeur(vu, terme_plus_grand(inf_egal_card, Du, "m", "x"))
        vy = var(yname)
        cas_zero = et(egal(vu, E.VIDE), egal(vy, va))
        cas_succ = et(non(egal(vu, E.VIDE)), egal(vy, S(prev)))
        return tau(yname, ou(cas_zero, cas_succ))

    return T


def t_iter_en_vide(S, a, yname="yitv"):
    """⊢ T_{S,a}(∅) = a                                        [CLOS, 0 hyp].

    Patron t_fac_en_vide : la garde gauche (∅=∅) est vraie par réflexivité, la
    droite réfutée (¬¬(∅=∅)) ; _garde_disjonction réduit la disjonction, S7
    puis S5+existe_temoin évaluent le τ à a."""
    va = _t(a)
    T = regle_iteration_vraie(S, a, yname)
    Tv = T(E.VIDE)
    cond = Tv.args[0]
    gauche, droite = cond.sous[0], cond.sous[1]
    P, R = _et_parts(gauche)                                # ∅=∅ ; y=a
    Q, S_part = _et_parts(droite)                           # ¬(∅=∅) ; y=S(…)
    assert P == egal(E.VIDE, E.VIDE), "t_iter_en_vide : garde gauche ≠ ∅=∅"
    vy = var(Tv.lieur)
    assert R == egal(vy, va), "t_iter_en_vide : sortie gauche ≠ y=a"

    refl = N.reflexivite(E.VIDE)
    gd = _garde_disjonction(refl, _nn(refl), R, S_part)     # cond ⇔ (y=a)
    gen = N.generalisation(Tv.lieur, gd)
    tau_eq = N.modus_ponens(gen, N.s7(cond, R, Tv.lieur))   # τ(cond)=τ(y=a)
    tau_val = N.modus_ponens(
        N.modus_ponens(N.reflexivite(va), N.s5(egal(vy, va), va, Tv.lieur)),
        N.existe_temoin(egal(vy, va), Tv.lieur))            # τ(y=a)=a
    res = composer_egalites(tau_eq, tau_val)

    assert res.conclusion == egal(Tv, va), "t_iter_en_vide : ≠ T(∅)=a"
    assert res.est_clos, "t_iter_en_vide : non clos"
    return res


def iteration_N_vrai(S, a, V="Vitv", yname="yitv"):
    """🎯 R8'-étape 1 : { regle_dans_V(T_{S,a}, V) }
       ⊢ (∃gcap)( est_solution_rec(gcap, T_{S,a}, G_≤, ℕ) )   [1 hyp honnête].

    Le critère C60-vrai sur (ℕ, ≤) : le bon ordre est DÉCHARGÉ par
    bo_graphe_NN (CLOS) — la seule hypothèse restante est la règle bornée."""
    T = regle_iteration_vraie(S, a, yname)
    GNN = G_ordre_NN()
    NN = ensemble_NN()
    ex = existence_solution(T, GNN, NN, V)                  # {bo, règle}
    bo = E.est_bien_ordonne(_graphe_R(GNN), NN)
    res = _cut(bo_graphe_NN(), bo, ex)                      # {règle} seule
    assert res.conclusion == existe("gcap", est_solution_rec(var("gcap"), T, GNN, NN)), \
        "iteration_N_vrai : forme"
    assert list(res.hypotheses) == [regle_dans_V(T, V)], \
        "iteration_N_vrai : hyps ≠ {règle bornée}"
    return res


__all__ = ["regle_iteration_vraie", "t_iter_en_vide", "iteration_N_vrai"]
