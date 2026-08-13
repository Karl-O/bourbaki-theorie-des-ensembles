"""§III.5.8 — L'ÉQUATION DE BASE :  f(0) = 1   (0! = 1, E III.41 L.30).

Depuis la forme du livre f(n)=T_fac(f|seg(n)) (pont restriction), le cas n=0 :
seg(0)=∅ (rien avant zéro — donnée d'ordre de (ℕ,≤,0), hypothèse honnête sur la
variable Enat) ⇒ f|seg(0)=∅ ⇒ f(0)=T_fac(∅)=1 (le τ de la règle s'évalue par
GARDE-DISJONCTION : la garde u=∅ est vraie par réflexivité, l'autre tuée par ¬¬).

  • `t_fac_en_vide`             ⊢ T_fac(∅) = 1                        [CLOS, 0 hyp]
  • `restriction_vide_est_vide` ⊢ F|∅ = ∅   (F terme)                 [CLOS, 0 hyp]
  • 🎯🎯 `factorielle_zero`     { bo, ebf, rc, essais_restriction,
        ZERO∈E, seg(≤,E,ZERO)=∅ } ⊢ valeur(f, ZERO) = UN              [6 hyps].

INVARIANT : theorie_ensembles() = 22.  Rien postulé ; les 2 hypothèses ajoutées
(ZERO∈E, seg(ZERO)=∅) sont les données de position de 0 dans (Enat,≤G) — sur la
variable Enat elles ne sont pas dérivables (Enat ≡ ℕ seulement par lecture).
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, et, non, appartient, pourtout,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E

from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege import a_implique_a
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, instancie,
)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import existe_elimination
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
    composer_egalites, congruence_terme,
)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_vide import (
    vide_ssi_sans_element, sous_ensemble_vide_ssi_egal,
)
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_5_restrictions_prolongements.ensembles_restrictions import _inst_restriction
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_somme.ensembles_somme_equipotence import _garde_disjonction
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.recollement.ensembles_restriction_somme import _ex_falso
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_recurrence_transfinie import _graphe_R
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import ZERO, UN
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_8_factorielle.ensembles_factorielle_existence import regle_factorielle
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_8_factorielle.ensembles_factorielle_fonction import factorielle_equation_restriction
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_2_recursion_c62.ensembles_c62_fonction_globale import fonction_globale
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_2_recursion_c62.ensembles_c62_equation_restriction import (
    _congruence_T, essais_restriction,
)


def _t(t):
    """Coercion str/Terme → Terme."""
    return t if isinstance(t, Terme) else var(t)


def _nn(thm):
    """⊢ A → ⊢ ¬¬A.   (a_implique_a(¬A) = ¬¬A∨¬A ; S3 la retourne en A⇒¬¬A ; MP.)"""
    a = thm.conclusion
    imp = N.modus_ponens(a_implique_a(non(a)), N.s3(non(non(a)), non(a)))
    return N.modus_ponens(thm, imp)


def _et_parts(f):
    """Décompose un `et` ENCODÉ  et(x,y)=¬(¬x∨¬y)  →  (x, y)."""
    return f.sous[0].sous[0].sous[0], f.sous[0].sous[1].sous[0]


# ════════════════════════════════════════════════════════════════════════════
#  ⊢ T_fac(∅) = 1  — le τ de la règle s'évalue au cas base (garde-disjonction).
# ════════════════════════════════════════════════════════════════════════════
# @livre Ch.III §5.8 Rem.- | E III.41 L.30-32 | PDF p.144  (« On a 0!=1 » — la règle au segment vide rend a=1)
def t_fac_en_vide(zcard="Zfac62"):
    """⊢ T_fac(∅) = 1                                                  [CLOS, 0 hyp].

    T_fac(∅) = τy( (∅=∅ ∧ y=1) ∨ (∅≠∅ ∧ y=…) ).  La garde gauche est VRAIE
    (réflexivité), la droite FAUSSE (¬¬(∅=∅)) : `_garde_disjonction` donne
    cond ⇔ (y=1) ; S7 puis S5+existe_temoin évaluent le τ à 1.

    `zcard` = le liant du `cardinal` interne de la règle.  Défaut "Zfac62"
    (byte-identique à l'historique) ; "Z" = le liant CANONIQUE de `cardinal`, requis
    pour parler de la MÊME règle que le cas successeur (cf. `factorielle_zero`)."""
    T = regle_factorielle(zcard=zcard)
    Tv = T(E.VIDE)                                               # τyfac62(cond)
    cond = Tv.args[0]
    gauche, droite = cond.sous[0], cond.sous[1]
    P, R = _et_parts(gauche)                                     # ∅=∅ ; y=1
    Q, S = _et_parts(droite)                                     # ¬(∅=∅) ; y=(…)·(…)
    assert P == egal(E.VIDE, E.VIDE), "t_fac_en_vide : garde gauche ≠ ∅=∅"
    vy = var(Tv.lieur)
    assert R == egal(vy, UN), "t_fac_en_vide : sortie gauche ≠ y=1"

    refl = N.reflexivite(E.VIDE)
    gd = _garde_disjonction(refl, _nn(refl), R, S)               # cond ⇔ (y=1)
    gen = N.generalisation(Tv.lieur, gd)
    tau_eq = N.modus_ponens(gen, N.s7(cond, R, Tv.lieur))        # τ(cond)=τ(y=1)
    tau_val = N.modus_ponens(
        N.modus_ponens(N.reflexivite(UN), N.s5(egal(vy, UN), UN, Tv.lieur)),
        N.existe_temoin(egal(vy, UN), Tv.lieur))                 # τ(y=1)=1
    res = composer_egalites(tau_eq, tau_val)

    assert res.conclusion == egal(Tv, UN), "t_fac_en_vide : ≠ T_fac(∅)=1"
    assert res.est_clos, "t_fac_en_vide : non clos"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  ⊢ F|∅ = ∅  — la restriction au vide est vide (F terme quelconque).
# ════════════════════════════════════════════════════════════════════════════
def restriction_vide_est_vide(F):
    """⊢ restriction(F, ∅) = ∅                                         [CLOS, 0 hyp].

    w∈F|∅ décompose en (∃p)(∃q)(… ∧ p∈∅ ∧ …) ; or ¬(p∈∅) (caractérisation du
    vide) : ex falso donne w∈∅ ; donc F|∅ ⊂ ∅, et X⊂∅ ⇔ X=∅ conclut."""
    F = _t(F)
    RV = E.restriction(F, E.VIDE)
    vz = var("z")

    # ¬(p∈∅) : (∅=∅) ⇔ (∀z)¬(z∈∅), sens avant sur la réflexivité, instancié à p
    vide_car = instancie(N.generalisation("A", vide_ssi_sans_element("A")), E.VIDE)
    sans_elem = N.modus_ponens(N.reflexivite(E.VIDE), equivalence_avant(vide_car))
    non_p_vide = instancie(sans_elem, var("p"))                  # ¬(p∈∅)

    h_z = N.assume(appartient(vz, RV))                           # z∈F|∅
    dec = N.modus_ponens(h_z, equivalence_avant(_inst_restriction(F, E.VIDE, vz)))
    vp, vq = var("p"), var("q")
    cpq = E.couple(vp, vq)
    corps = et(et(egal(vz, cpq), appartient(vp, E.VIDE)), appartient(cpq, F))
    h_c = N.assume(corps)
    p_vide = conjonction_elim_droite(conjonction_elim_gauche(h_c))   # p∈∅
    z_vide = _ex_falso(p_vide, non_p_vide, appartient(vz, E.VIDE))   # z∈∅ (ex falso)
    imp_q = existe_elimination(N.loi_deduction(corps, z_vide), "q")
    imp_pq = existe_elimination(imp_q, "p")
    z_vide = N.modus_ponens(dec, imp_pq)                         # z∈∅   [z∈F|∅]

    sub = N.generalisation("z", N.loi_deduction(appartient(vz, RV), z_vide))  # F|∅⊂∅
    car = instancie(N.generalisation("X", sous_ensemble_vide_ssi_egal("X")), RV)
    res = N.modus_ponens(sub, equivalence_avant(car))            # F|∅ = ∅

    assert res.conclusion == egal(RV, E.VIDE), "restriction_vide_est_vide : ≠ F|∅=∅"
    assert res.est_clos, "restriction_vide_est_vide : non clos"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  🎯🎯 f(0) = 1  — l'équation de base de la factorielle.
# ════════════════════════════════════════════════════════════════════════════
# @livre Ch.III §5.8 Rem.- | E III.41 L.30-32 | PDF p.144  (« On a 0! = 1 » — dérivé de la forme du livre au point 0)
def factorielle_zero(e="Enat", G="Gle", V="Vfac62", zcard="Zfac62"):
    """🎯🎯 { bo, essais_bien_formes, rule_codomain, essais_restriction,
             ZERO∈E, seg(≤,E,ZERO)=∅ } ⊢ valeur(f, ZERO) = UN          [6 hyps].

    0! = 1 : la forme du livre en 0 donne f(0)=T_fac(f|seg(0)) ; seg(0)=∅ (donnée
    de position de 0) ⇒ f|seg(0)=f|∅=∅ ⇒ T_fac(∅)=1 (garde-disjonction).  Les 2
    hypothèses de position (ZERO∈E, seg(ZERO)=∅) s'ajoutent aux 4 de la forme du
    livre — toutes honnêtes, rien postulé, theorie==22.

    ⚠️ `zcard` EST LOAD-BEARING pour tout RECOLLEMENT.  Il fixe le liant du `cardinal`
    interne de la règle, donc l'IDENTITÉ (au sens `==` du noyau) des trois hypothèses
    règle-dépendantes (essais_bien_formes, rule_codomain, essais_restriction).  Le
    défaut historique "Zfac62" diffère du "Z" (liant canonique de `cardinal`) qu'impose
    le cas successeur pour se raccorder à `prop5_intervalle_zero`.  Les deux jeux sont
    α-ÉQUIVALENTS (MESURÉ) mais pas `==`, et le noyau n'identifie pas les α-variants :
    conjuguer les deux moitiés à leurs défauts donne 13 hypothèses (2 partagées) au
    lieu de 10 — trois résidus C62 comptés deux fois sous deux noms de liant.
    Appeler avec zcard="Z" pour joindre — cf. `factorielle_caracterisation`."""
    R = _graphe_R(G)
    ve = _t(e)
    T = regle_factorielle(zcard=zcard)
    f = fonction_globale(e, V)
    seg0 = E.segment_extremite(_t(G), ve, ZERO)

    eqres = factorielle_equation_restriction(e, G, V, zcard=zcard)   # (∀z∈E) f(z)=T(f|seg z)
    h_0E = N.assume(appartient(ZERO, ve))                        # ZERO∈E   [HONNÊTE]
    eq0 = N.modus_ponens(h_0E, instancie(eqres, ZERO))           # f(0)=T(f|seg(0))

    h_seg = N.assume(egal(seg0, E.VIDE))                         # seg(0)=∅ [HONNÊTE]
    cong = congruence_terme(var("wr0"), E.VIDE, E.restriction(f, var("wr0")), "wr0")
    cong = instancie(N.generalisation("wr0", cong), seg0)        # (seg0=∅)⇒(f|seg0=f|∅)
    eq_rs = N.modus_ponens(h_seg, cong)                          # f|seg0 = f|∅
    eq_r = composer_egalites(eq_rs, restriction_vide_est_vide(f))   # f|seg0 = ∅

    Teq = N.modus_ponens(eq_r, _congruence_T(T, E.restriction(f, seg0), E.VIDE))
    res = composer_egalites(composer_egalites(eq0, Teq), t_fac_en_vide(zcard))

    assert res.conclusion == egal(E.valeur(f, ZERO), UN), "factorielle_zero : ≠ f(0)=1"
    assert appartient(ZERO, ve) in res.hypotheses, "factorielle_zero : ZERO∈E absente"
    assert egal(seg0, E.VIDE) in res.hypotheses, "factorielle_zero : seg(0)=∅ absente"
    assert essais_restriction(T, T, e, G) in res.hypotheses, \
        "factorielle_zero : essais_restriction absente"
    assert len(res.hypotheses) == 6, "factorielle_zero : hyps ≠ 6"
    assert res.conclusion not in res.hypotheses, "factorielle_zero : VACUOUS"
    return res


__all__ = ["t_fac_en_vide", "restriction_vide_est_vide", "factorielle_zero"]
