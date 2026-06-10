"""Tests du THÉORÈME DE ZORN (Théorème 2 §III.2) via Bourbaki–Witt.

🎯 zorn_theoreme() : ( est_ordre(G,E) ∧ est_inductif(G,E) ∧ E≠∅ )
                        ⇒ (∃m) element_maximal(G,E,m).

INVARIANT : theorie_ensembles() reste = 22 (P/Γ/Union en théories dédiées).
"""
from bourbaki.logique.formule import var, appartient, equiv, inclus
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.ordre import ensembles_zorn_theoreme as Z


G, Es, Cc, Dd = var("G"), var("E"), var("C"), var("D")


# ── theorie_ensembles INTANGIBLE = 22 ────────────────────────────────────────
def test_theorie_ensembles_intacte():
    assert len(E.theorie_ensembles().axiomes) == 22


def test_theories_dediees_un_axiome():
    assert len(Z.theorie_P().axiomes) == 1
    assert len(Z.theorie_Gamma().axiomes) == 1
    assert len(Z.theorie_Union().axiomes) == 1
    assert len(Z.theorie_f().axiomes) == 1
    te = E.theorie_ensembles().axiomes
    assert Z.axiome_P() not in te
    assert Z.axiome_Gamma() not in te
    assert Z.axiome_Union() not in te
    assert Z.axiome_f() not in te          # l'axiome τ de f reste hors theorie_ensembles


# ── ÉTAPE 1 — poset des chaînes P + graphe d'inclusion Γ ─────────────────────
def test_P_membre_close():
    assert Z.P_membre().est_clos


def test_Gamma_membre_close():
    assert Z.Gamma_membre().est_clos


def test_Gamma_est_ordre_close():
    from bourbaki.ordre.ensembles_ordre_relation import est_ordre
    t = Z.Gamma_est_ordre()
    assert t.est_clos
    assert t.conclusion == est_ordre(Z.Gamma(G, Es), Z.P(G, Es))


# ── ÉTAPE 3 — ∅ ∈ P plus petit élément ───────────────────────────────────────
def test_vide_est_chaine():
    from bourbaki.ordre.ensembles_zorn import chaine
    from bourbaki.ordre.ensembles_ordre_relation import antisymetrie, transitivite_rel
    t = Z.vide_est_chaine()
    assert t.conclusion == chaine(G, Es, E.VIDE)
    assert antisymetrie(G) in t.hypotheses
    assert transitivite_rel(G) in t.hypotheses


def test_vide_dans_P():
    t = Z.vide_dans_P()
    assert t.conclusion == appartient(E.VIDE, Z.P(G, Es))


def test_vide_plus_petit():
    from bourbaki.ordre.ensembles_ordre_relation import plus_petit_element
    t = Z.vide_plus_petit()
    assert t.conclusion == plus_petit_element(Z.Gamma(G, Es), Z.P(G, Es), E.VIDE)


# ── ÉTAPE 2 — (Γ,P) chaîne-complet (LE CŒUR : ⋃𝔇 borne sup) ──────────────────
def test_Union_membre_close():
    assert Z.Union_membre().est_clos


def test_Union_dans_P():
    Dd2 = var("D")
    t = Z.Union_dans_P()
    assert t.conclusion == appartient(Z.Union(G, Es, Dd2), Z.P(G, Es))


def test_Union_borne_sup():
    from bourbaki.ordre.ensembles_ordre_relation import borne_superieure
    Dd2 = var("D")
    t = Z.Union_borne_sup()
    assert t.conclusion == borne_superieure(Z.Gamma(G, Es), Dd2,
                                            Z.Union(G, Es, Dd2), Z.P(G, Es))


def test_Gamma_chaine_complet():
    from bourbaki.ordre.ensembles_bourbaki_witt import chaine_complet
    from bourbaki.ordre.ensembles_ordre_relation import antisymetrie, transitivite_rel
    t = Z.Gamma_chaine_complet()
    assert t.conclusion == chaine_complet(Z.Gamma(G, Es), Z.P(G, Es))
    # seules hyps STRUCTURELLES globales de G (jamais postulé)
    assert antisymetrie(G) in t.hypotheses
    assert transitivite_rel(G) in t.hypotheses
    assert not t.est_clos


# ── ÉTAPE 4 — chaîne strictement plus grande via τ (E sans maximal) ──────────
def test_ajoute_est_chaine():
    from bourbaki.ordre.ensembles_zorn import chaine
    Cc2, tt = var("C"), var("t")
    t = Z.ajoute_est_chaine()
    assert t.conclusion == chaine(G, Es, E.reunion(Cc2, E.singleton(tt)))


def test_strict_chaine_existe():
    from bourbaki.ordre.ensembles_zorn import est_inductif
    Cc2 = var("C")
    t = Z.strict_chaine_existe()
    assert t.conclusion == Z._enonce_strict_D(G, Es, Cc2, "D")
    assert est_inductif(G, Es) in t.hypotheses
    assert Z.sans_maximal(G, Es) in t.hypotheses
    assert appartient(Cc2, Z.P(G, Es)) in t.hypotheses


def test_f_application_dans():
    from bourbaki.ordre.ensembles_bourbaki_witt import application_dans
    from bourbaki.ordre.ensembles_zorn import est_inductif
    t = Z.f_application_dans()
    assert t.conclusion == application_dans(Z.P(G, Es), Z.zorn_f(G, Es))
    assert est_inductif(G, Es) in t.hypotheses
    assert Z.sans_maximal(G, Es) in t.hypotheses


def test_f_inflationnaire_strict():
    from bourbaki.ordre.ensembles_bourbaki_witt_chaine import inflationnaire_strict
    t = Z.f_inflationnaire_strict()
    assert t.conclusion == inflationnaire_strict(Z.Gamma(G, Es), Z.P(G, Es), Z.zorn_f(G, Es))


# ── ÉTAPE 5 — 🎯🎯🎯 LE THÉORÈME DE ZORN (CLOS, == énoncé) ───────────────────
def test_zorn_theoreme_CLOS():
    from bourbaki.ordre.ensembles_zorn import zorn
    t = Z.zorn_theoreme()
    assert t.est_clos                                   # INCONDITIONNEL — 0 hypothèse
    assert t.conclusion == zorn(G, Es)                  # == énoncé du THÉORÈME 2


def test_zorn_theoreme_conclusion_est_maximal():
    from bourbaki.logique.formule import existe, impl
    from bourbaki.ordre.ensembles_ordre_relation import element_maximal
    from bourbaki.logique.tactiques.tactiques_abrege import antecedent_consequent
    t = Z.zorn_theoreme()
    _, cons = antecedent_consequent(t.conclusion)
    assert cons == existe("m", element_maximal(G, Es, var("m")))
