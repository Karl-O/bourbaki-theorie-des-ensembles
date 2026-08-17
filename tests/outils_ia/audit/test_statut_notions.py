# -*- coding: utf-8 -*-
"""Tests — l'outil qui croise les `@livre` avec le verdict du noyau.

⚠️ CET OUTIL NE DÉMONTRE RIEN : il LIT des théorèmes déjà construits et compte
leurs hypothèses. Ce qu'on teste ici, c'est qu'il lit juste — parce qu'un
classificateur qui lit de travers accuse de fausse déclaration les docstrings
les plus honnêtes du dépôt. C'est arrivé, et les tests ci-dessous verrouillent
chacune des formes qui l'avaient piégé."""
from __future__ import annotations

from outils_ia.audit.statut_notions import (
    croisement, declaration, est_demontrable, verdict_noyau,
)


def test_clos_sec_est_lu_comme_clos():
    """La forme simple, celle qui annonce une preuve sans dette."""
    assert declaration("Théorème CLOS.") == ("CLOS", 0)
    assert declaration("[CLOS au sens du noyau]")[0] == "CLOS"


def test_clos_modulo_n_hypotheses():
    """« CLOS, 2 hyp » n'est PAS clos : c'est PARTIEL, et le nombre est lu."""
    assert declaration("[CLOS, 2 hyp]") == ("CLOS_MODULO", 2)
    assert declaration("Résultat CLOS (1 hyp).") == ("CLOS_MODULO", 1)


def test_clos_sous_hypothese_honnete():
    """LE PIÈGE QUI A FAIT TOMBER LA PREMIÈRE VERSION.

    `hyps?\\b` ne matche pas « HYPOTHÈSE » : après « HYP » vient « O », il n'y
    a pas de frontière de mot. Trois théorèmes dont la docstring écrit
    littéralement `hypotheses == {inclus(X,E)}` étaient donc classés CLOS, et
    l'outil les dénonçait comme sur-déclarés. Il faut la racine « hypoth »."""
    d = "Théorème CLOS-SOUS-L'HYPOTHÈSE-HONNÊTE {inclus(X,E)} : le contexte."
    assert declaration(d)[0] == "CLOS_MODULO"
    d2 = "Théorème CLOS-SOUS-LES-HYPOTHÈSES-HONNÊTES {inclus(X,E), inclus(Y,E)}."
    assert declaration(d2)[0] == "CLOS_MODULO"


def test_clos_hyps_honnetes_abrege():
    """L'autre forme du dépôt — « hyps » abrégé, sans « othèse ».

    Elle est tombée quand on a corrigé le piège précédent en remplaçant
    `hyps?\\b` par `hypoth` au lieu d'ajouter la racine : Ch.III était remonté
    de 111 à 122 CLOS. Les TROIS formes doivent coexister."""
    assert declaration("[CLOS, hyps HONNÊTES]")[0] == "CLOS_MODULO"


def test_reporte_et_muet():
    assert declaration("Proposition 5 — REPORTÉ (intersection finie).")[0] == "REPORTE"
    assert declaration("Simple définition du produit.") == ("MUET", None)
    assert declaration(None) == ("MUET", None)
    assert declaration("") == ("MUET", None)


def test_un_axiome_de_theorie_n_est_pas_une_hypothese():
    """« CLOS SOUS les 2 axiomes de la théorie » reste CLOS.

    Un axiome de `theorie_ensembles()` n'est pas une hypothèse non déchargée —
    le noyau rend bien 0 hypothèse. Confondre les deux ferait passer pour
    PARTIEL tout ce qui repose sur la théorie, c'est-à-dire presque tout."""
    d = "[CLOS au sens du noyau, SOUS les 2 axiomes de la théorie additive.]"
    assert declaration(d) == ("CLOS", 0)


def test_le_croisement_signale_le_report_perime():
    """🎯 LE CAS QUI COÛTE LE PLUS CHER : un acquis déclaré ouvert.

    Quatre reports périmés ont été trouvés à la main début août ; chacun
    risquait de faire REFAIRE un théorème déjà démontré."""
    assert croisement("REPORTE", "FAIT") == "REPORT_PERIME"


def test_le_croisement_signale_la_declaration_trop_forte():
    """L'inverse : une docstring qui annonce clos ce qui traîne des hypothèses."""
    assert croisement("CLOS", "PARTIEL") == "DECLARATION_TROP_FORTE"


def test_un_clos_modulo_partiel_est_un_ACCORD():
    """Déclarer « CLOS, 2 hyp » et être PARTIEL, c'est être d'accord.

    Sans cette règle, tout le travail honnêtement annoncé comme partiel
    serait dénoncé comme une contradiction."""
    assert croisement("CLOS_MODULO", "PARTIEL") == "ACCORD"


def test_ce_qui_n_est_pas_evaluable_n_est_jamais_tranche():
    """LE TEST DE SÛRETÉ : une notion qu'on ne sait pas évaluer n'est pas
    démontrée, et ne doit jamais être comptée comme telle. Un outil qui
    affirmerait sur ce qu'il ignore serait pire que pas d'outil."""
    for decl in ("CLOS", "CLOS_MODULO", "REPORTE", "MUET"):
        assert croisement(decl, "NON_EVALUABLE") == "NON_TRANCHE"
        assert croisement(decl, "PAS_UN_THEOREME") == "NON_TRANCHE"
        assert croisement(decl, "CONSTRUIT") == "NON_TRANCHE"


def test_seuls_les_types_demontrables_portent_la_question():
    """La question FAIT/PARTIEL n'a de sens que pour ce qui PROMET une preuve.

    Une Def qui construit un Terme n'est ni FAIT ni PARTIEL ; la compter dans
    le taux dilue la seule réponse chiffrée à « démontré == vérifié ? » —
    mesuré : une grande part des 354 « NON_EVALUABLE » de la première passe
    étaient des définitions qui construisaient très bien."""
    for t in ("Prop", "Th", "Cor", "Crit", "Lem", "Demo", "Sch", "Ax"):
        assert est_demontrable(t)
    for t in ("Def", "Rem", "Ex"):
        assert not est_demontrable(t)


def test_le_repli_arguments_generiques_evalue_une_notion_a_parametres():
    """Le repli du verdict : fn sans défauts s'appelle avec ses PROPRES noms.

    Convention du dépôt — les paramètres sont des noms de variables, convertis
    par `var()`/`_t()` à l'intérieur. `injectivite_g_construite(gterme, ...)`
    doit donc être évaluable, et rendre un théorème générique.

    Lent à froid (imports du chapitre III), instantané ensuite."""
    etat, n, detail = verdict_noyau(
        "bourbaki/iii_ensembles_ordonnes_cardinaux_entiers/iii_7_limites/"
        "prop1_proj/ensembles_g_construite.py",
        "injectivite_g_construite")
    assert etat in ("FAIT", "PARTIEL")
    assert n is not None


def test_le_repli_classe_une_definition_comme_CONSTRUIT():
    """Une définition qui rend un Terme est CONSTRUIT — pas un échec, pas un
    théorème. `classe` (II.6.2) construit le terme « classe de x mod R »."""
    etat, _n, _d = verdict_noyau(
        "bourbaki/ii_theorie_des_ensembles/ii_1_relations_collectivisantes/"
        "ensembles_abrege.py", "classe")
    assert etat == "CONSTRUIT"
