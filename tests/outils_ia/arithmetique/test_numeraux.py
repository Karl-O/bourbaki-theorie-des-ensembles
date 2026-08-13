"""Numéraux mémoïsés — et la régression qui protège le facteur 466.

Ces tests ne démontrent rien de neuf : ils figent que la construction reste CLOSE,
et surtout qu'elle reste PRATICABLE. C'est le second point qui compte : la même
preuve, sans partage des sous-termes, coûtait 559,7 s pour k = 11.

────────────────────────────────────────────────────────────────────────────────
🔴 POURQUOI LA MESURE DE COÛT SE FAIT EN SOUS-PROCESSUS (mesuré le 5 août 2026).

Une première version appelait `vider_caches()` puis reconstruisait dans le process
de test.  Résultat : chaque test passait ISOLÉMENT (0,08 à 10,6 s, ~40 s en tout),
et le FICHIER ENTIER ne terminait pas — même avec 50 minutes — en tournant dans la
comparaison structurelle profonde de `Formule.__eq__`.

La cause est celle-là même que le module existe pour éviter : vider le cache remet
les numéraux à neuf, mais les théorèmes déjà construits par les tests précédents
tiennent les ANCIENS termes.  Toute comparaison ultérieure croise alors du partagé
et du non-partagé, et repaie l'arbre τ entier.

Deux leçons, et la seconde est la vraie :
  · un « à froid » mesuré dans un process déjà chaud n'est pas un à froid ;
  · **un outil de mesure qui partage l'état de ce qu'il mesure fabrique le
    problème qu'il surveille.**  Le sous-processus n'est pas un contournement,
    c'est la seule façon correcte de mesurer un coût de première construction.
"""
import subprocess
import sys
import textwrap

import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    est_cardinal,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (
    est_fini, successeur, ZERO,
)
from outils_ia.arithmetique.numeraux import num, fini, cardinal_num

#: racine du dépôt, pour lancer un sous-processus depuis n'importe où
_RACINE = __file__.split("tests")[0]


def _mesure_a_froid(source: str) -> float:
    """Exécute `source` dans un process NEUF et rend la durée qu'il imprime.

    Le process de test a déjà construit des termes ; y mesurer une première
    construction n'aurait aucun sens (cf. l'en-tête)."""
    script = textwrap.dedent(source)
    r = subprocess.run([sys.executable, "-c", script], cwd=_RACINE,
                       capture_output=True, text=True, timeout=900)
    assert r.returncode == 0, f"sous-processus en échec :\n{r.stderr[-2000:]}"
    return float(r.stdout.strip().splitlines()[-1])


def test_le_numeral_est_bien_successeur_itere():
    """N(k) = successeur^k(Card ∅), et le cache ne change pas l'objet."""
    assert num(0) == ZERO
    assert num(3) == successeur(successeur(successeur(ZERO)))


def test_finitude_close_pour_k_arbitraire():
    """⊢ Fini(N(k)) pour des k que le dépôt ne code pas en dur (il s'arrête à 4)."""
    for k in (0, 1, 5, 11, 20):
        th = fini(k)
        assert th.est_clos and len(th.hypotheses) == 0
        assert th.conclusion == est_fini(num(k))
    assert len(E.theorie_ensembles().axiomes) == 22


def test_cardinalite_close():
    """⊢ est_cardinal(N(k)), par Fini(N(k)) puis fini_implique_cardinal."""
    th = cardinal_num(7)
    assert th.est_clos and th.conclusion == est_cardinal(num(7))


def test_le_cache_rend_la_construction_praticable():
    """🔴 RÉGRESSION DE PERFORMANCE — mesurée le 5 août 2026, en process NEUF.

    La MÊME preuve, avec les numéraux rebâtis à chaque appel au lieu d'être
    partagés, coûtait 559,7 s pour k = 11 ; avec cache, 1,2 s. Facteur 466.

    La cause n'est pas le nombre de pas de noyau — il est identique — mais le
    partage des sous-termes : sans lui, chaque `instancie` et chaque comparaison
    repaient l'arbre τ entier, dont la taille explose avec k.

    Le seuil est large exprès : on protège un ordre de grandeur, pas une
    milliseconde."""
    duree = _mesure_a_froid("""
        import time
        from outils_ia.arithmetique.numeraux import fini
        t0 = time.perf_counter()
        fini(15)
        print(time.perf_counter() - t0)
    """)
    assert duree < 90, (
        f"Fini(N(15)) a pris {duree:.1f} s en process neuf : la mémoïsation des "
        f"numéraux a-t-elle été retirée ? Sans elle, k=11 coûtait déjà 560 s.")


def test_les_etages_memoises_ne_se_repaient_pas():
    """Après Fini(N(20)), obtenir Fini(N(25)) ne repaie pas les vingt premiers.

    Mesuré dans un process neuf, pour la même raison que ci-dessus."""
    duree = _mesure_a_froid("""
        import time
        from outils_ia.arithmetique.numeraux import fini
        fini(20)
        t0 = time.perf_counter()
        fini(25)
        print(time.perf_counter() - t0)
    """)
    assert duree < 30, (
        f"les cinq étages supplémentaires ont coûté {duree:.1f} s : la mémoïsation "
        f"par étage ne fonctionne plus.")
