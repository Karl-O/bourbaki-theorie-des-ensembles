"""Tests de ensembles_bourbaki_witt_chaine.py — LE VERROU DE BOURBAKI–WITT LEVÉ.

On vérifie, ÉTAPE par ÉTAPE (preuve de Witt, deux tours emboîtés) :
  • ÉTAPE 1 : M_c = {x∈M | x≤c OU p(c)≤x} est un TOUR (sous est_extreme(c)).
  • ÉTAPE 2 : M_c = M ⇒ (∀x∈M) x≤c OU c≤x (c comparable à tout x).
  • ÉTAPE 3 : Cext = {c∈M | est_extreme(c)} est un TOUR (incl. s_est_extreme, cœur dur).
  • ÉTAPE 4 : Cext = M ⇒ tout c∈M est extrême.
  • ÉTAPE 5 : 🎯 M_est_une_chaine = totalement_ordonne(G,M) — LE THÉORÈME VISÉ.
  • ÉTAPE 6 : 🎯 bourbaki_witt = point fixe (∃s) p(s)=s — CLOS (== énoncé du module).
  • ÉTAPE 7 : bw_strict_contradiction = cœur logique de Zorn ⇐ Bourbaki–Witt — CLOS.

INVARIANT : theorie_ensembles() reste = 22 (axiomes de M_c/Cext en théories DÉDIÉES).
Rien n'est postulé : M chaîne et le point fixe sont DÉMONTRÉS (.est_clos vérifié).
"""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_relation import totalement_ordonne
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.zorn_zermelo.ensembles_bourbaki_witt import (
    M, est_tour, M_est_une_chaine as ENONCE_CHAINE, bourbaki_witt as ENONCE_BW,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.zorn_zermelo import ensembles_bourbaki_witt_chaine as W


G, Es, P, A, Cc = var("G"), var("E"), var("p"), var("a"), var("c")


def Mt():
    return M(G, Es, P, A)


# ── theorie_ensembles INTANGIBLE = 22 ; théories dédiées séparées ─────────────
def test_theorie_ensembles_intacte():
    assert len(E.theorie_ensembles().axiomes) == 22


def test_theories_dediees_un_axiome():
    assert len(W.theorie_Mc().axiomes) == 1
    assert len(W.theorie_Cext().axiomes) == 1
    # et ces axiomes ne sont PAS dans theorie_ensembles
    assert W.axiome_Mc() not in E.theorie_ensembles().axiomes
    assert W.axiome_Cext() not in E.theorie_ensembles().axiomes


# ── ÉTAPE 1 — M_c est un TOUR ─────────────────────────────────────────────────
def test_Mc_membre_close():
    assert W.Mc_membre().est_clos


def test_Mc_inclus_M_close():
    assert W.Mc_inclus_M().est_clos


def test_Mc_est_tour():
    t = W.Mc_est_tour()
    cible = est_tour(G, Es, P, A, W.Mc(G, Es, P, A, Cc))
    assert t.conclusion == cible
    # hypothèses STRUCTURELLES uniquement (jamais « M_c tour » postulé)
    assert not t.est_clos
    assert W.est_extreme(G, Es, P, A, Cc) in t.hypotheses


# ── ÉTAPE 2 — M_c = M ⇒ comparabilité ────────────────────────────────────────
def test_M_inclus_Mc():
    t = W.M_inclus_Mc()
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import inclus
    assert t.conclusion == inclus(Mt(), W.Mc(G, Es, P, A, Cc))


def test_comparable_a_c():
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, pourtout, impl, appartient, ou
    t = W.comparable_a_c()
    # (∀x)(x∈M ⇒ (x≤c OU c≤x))
    vx = var("x")
    cible = pourtout("x", impl(appartient(vx, Mt()),
                               ou(W._le(vx, Cc, G), W._le(Cc, vx, G))))
    assert t.conclusion == cible


# ── ÉTAPE 3 — Cext est un TOUR (cœur dur : s_est_extreme) ─────────────────────
def test_a_dans_Cext():
    t = W.a_dans_Cext()
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import appartient
    assert t.conclusion == appartient(A, W.Cext(G, Es, P, A))


def test_Cext_clos_p():
    t = W.Cext_clos_p()
    assert not t.est_clos  # structurelles


def test_s_est_extreme_est_le_coeur_dur():
    # le sup d'une chaîne D⊂Cext est EXTRÊME — la partie la plus profonde
    t = W.s_est_extreme()
    assert t.conclusion == W.est_extreme(G, Es, P, A, var("s"))


def test_Cext_est_tour():
    t = W.Cext_est_tour()
    cible = est_tour(G, Es, P, A, W.Cext(G, Es, P, A))
    assert t.conclusion == cible


# ── ÉTAPE 4 — Cext = M ⇒ tout c∈M extrême ────────────────────────────────────
def test_tout_M_extreme():
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, pourtout, impl, appartient
    t = W.tout_M_extreme()
    vc = var("c")
    cible = pourtout("c", impl(appartient(vc, Mt()),
                               W.est_extreme(G, Es, P, A, vc)))
    assert t.conclusion == cible


# ── ÉTAPE 5 — 🎯 LE VERROU : M est une chaîne ────────────────────────────────
def test_M_est_une_chaine_egale_enonce():
    t = W.M_est_une_chaine()
    # == énoncé du module (totalement_ordonne(G,M)), VERROU LEVÉ
    assert t.conclusion == ENONCE_CHAINE(G, Es, P, A)
    assert t.conclusion == totalement_ordonne(G, Mt())


def test_M_est_une_chaine_hyps_structurelles():
    # conditionné aux SEULES hypothèses structurelles (comme point_fixe_de_sup) ;
    # M chaîne n'est JAMAIS postulé (pas clos « gratuitement »).
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_relation import est_ordre
    t = W.M_est_une_chaine()
    assert est_ordre(G, Es) in t.hypotheses
    assert not t.est_clos


# ── ÉTAPE 6 — 🎯🎯 POINT FIXE DE BOURBAKI–WITT (CLOS, == énoncé) ──────────────
def test_bourbaki_witt_theoreme_CLOS():
    t = W.bourbaki_witt_theoreme()
    assert t.est_clos                                   # INCONDITIONNEL
    assert t.conclusion == ENONCE_BW(G, Es, P, A)       # == énoncé du LEMME 3


def test_bourbaki_witt_avec_temoin_dans_E():
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import existe, et, egal, appartient
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.zorn_zermelo.ensembles_bourbaki_witt import pval
    t = W.bourbaki_witt_theoreme(avec_E=True)
    assert t.est_clos
    # conclusion renforcée : (∃s)(s∈E et p(s)=s)
    vs = var("s")
    corps = et(appartient(vs, Es), egal(pval(P, vs), vs))
    # antécédent identique, conséquent renforcé
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege import antecedent_consequent
    _, cons = antecedent_consequent(t.conclusion)
    assert cons == existe("s", corps)


# ── ÉTAPE 7 — cœur de Zorn ⇐ Bourbaki–Witt (CLOS) ─────────────────────────────
def test_bw_strict_contradiction_CLOS():
    t = W.bw_strict_contradiction()
    assert t.est_clos
    # conclusion = ¬( bw-hyps et inflationnaire_strict )
    assert t.conclusion.tag == "non"


def test_zorn_via_bw_enonce_est_redite():
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.zorn_zermelo.ensembles_zorn import zorn
    assert W.zorn_via_bw_enonce(G, Es) == zorn(G, Es)
