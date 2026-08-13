"""Script de migration : fichiers plats -> arborescence de packages.

Déplace chaque module source dans son package (noms conservés) et réécrit
TOUS les imports locaux avec le préfixe de package adéquat. Les références
`MOD.x` restent valides (on importe `from PKG import MOD`).
Idempotent-ish : à lancer une seule fois depuis un baseline propre.
"""
from __future__ import annotations
import os, re, subprocess, glob

ROOT = os.path.dirname(os.path.abspath(__file__))

# ── Correspondance module -> dossier cible (sous V9/) ─────────────────────────
MAP = {
    'assemblage': 'bourbaki/i_description_mathematique_formelle',
    # logique
    'formule': 'bourbaki/logique', 'noyau': 'bourbaki/logique',
    'noyau_abrege': 'bourbaki/logique', 'propositions': 'bourbaki/logique',
    'lecture': 'bourbaki/logique', 'notation': 'bourbaki/logique',
    'congruence_quantif': 'bourbaki/logique', 'verificateur_preuve': 'bourbaki/logique',
    # criteres
    'criteres_C': 'bourbaki/logique/criteres', 'criteres_CF': 'bourbaki/logique/criteres',
    'criteres_CS': 'bourbaki/logique/criteres', 'criteres_C_suite': 'bourbaki/logique/criteres',
    'criteres_C_suite2': 'bourbaki/logique/criteres', 'criteres_quantif2': 'bourbaki/logique/criteres',
    # tactiques
    'tactiques': 'bourbaki/logique/tactiques', 'tactiques_abrege': 'bourbaki/logique/tactiques',
    'tactiques_abrege2': 'bourbaki/logique/tactiques', 'tactiques_abrege_egalite': 'bourbaki/logique/tactiques',
    'tactiques_abrege_quantif': 'bourbaki/logique/tactiques', 'tactiques_egalite': 'bourbaki/logique/tactiques',
    'tactiques_prop': 'bourbaki/logique/tactiques',
    # ensembles top
    'ensembles_abrege': 'bourbaki/ensembles', 'ensembles_theoremes': 'bourbaki/ensembles',
    'theorie_ensembles': 'bourbaki/ensembles',
    # ensembles base
    'ensembles_vide': 'bourbaki/ensembles/base', 'ensembles_couples': 'bourbaki/ensembles/base',
    'ensembles_difference': 'bourbaki/ensembles/base', 'ensembles_correspondances': 'bourbaki/ensembles/base',
    # ensembles fonctions
    'ensembles_fonctions': 'bourbaki/ensembles/fonctions', 'ensembles_fonctions_composee': 'bourbaki/ensembles/fonctions',
    'ensembles_composee': 'bourbaki/ensembles/fonctions', 'ensembles_composee_assoc': 'bourbaki/ensembles/fonctions',
    'ensembles_composee_reciproque': 'bourbaki/ensembles/fonctions', 'ensembles_composee_valeurs': 'bourbaki/ensembles/fonctions',
    'ensembles_reciproque': 'bourbaki/ensembles/fonctions', 'ensembles_projections': 'bourbaki/ensembles/fonctions',
    'ensembles_projections_terme': 'bourbaki/ensembles/fonctions', 'ensembles_restrictions': 'bourbaki/ensembles/fonctions',
    'ensembles_retractions': 'bourbaki/ensembles/fonctions', 'ensembles_fonction_terme': 'bourbaki/ensembles/fonctions',
    'ensembles_morphismes': 'bourbaki/ensembles/fonctions', 'ensembles_isomorphismes': 'bourbaki/ensembles/fonctions',
    'ensembles_applications_universelles': 'bourbaki/ensembles/fonctions',
    # ensembles familles
    'ensembles_familles': 'bourbaki/ensembles/familles', 'ensembles_familles_demorgan': 'bourbaki/ensembles/familles',
    'ensembles_produit': 'bourbaki/ensembles/familles', 'ensembles_produit_famille': 'bourbaki/ensembles/familles',
    'ensembles_somme_disjointe': 'bourbaki/ensembles/familles', 'ensembles_limites': 'bourbaki/ensembles/familles',
    # cardinaux
    'ensembles_equipotence': 'bourbaki/cardinaux', 'ensembles_equivalence': 'bourbaki/cardinaux',
    'ensembles_bijection': 'bourbaki/cardinaux', 'ensembles_cardinaux': 'bourbaki/cardinaux',
    'ensembles_cardinaux_theoremes': 'bourbaki/cardinaux', 'ensembles_cardinaux_ordre': 'bourbaki/cardinaux',
    'ensembles_cantor': 'bourbaki/cardinaux', 'ensembles_vide_singleton': 'bourbaki/cardinaux',
    # cardinaux arithmetique
    'ensembles_arith_cardinale': 'bourbaki/cardinaux/arithmetique', 'ensembles_arith_somme': 'bourbaki/cardinaux/arithmetique',
    'ensembles_distributivite_cardinale': 'bourbaki/cardinaux/arithmetique',
    'ensembles_produit_equipotence': 'bourbaki/cardinaux/arithmetique', 'ensembles_produit_commute': 'bourbaki/cardinaux/arithmetique',
    'ensembles_somme_equipotence': 'bourbaki/cardinaux/arithmetique', 'ensembles_somme_commute': 'bourbaki/cardinaux/arithmetique',
    'ensembles_somme_associe': 'bourbaki/cardinaux/arithmetique', 'ensembles_somme_zero': 'bourbaki/cardinaux/arithmetique',
    # ordre
    'ensembles_ordre': 'bourbaki/ordre', 'ensembles_ordre_relation': 'bourbaki/ordre',
    'ensembles_bon_ordre': 'bourbaki/ordre',
    # entiers
    'ensembles_entiers': 'bourbaki/entiers', 'ensembles_entiers_theoremes': 'bourbaki/entiers',
    'ensembles_infinis': 'bourbaki/entiers', 'ensembles_infinis_theoremes': 'bourbaki/entiers',
    'ensembles_fini_zero': 'bourbaki/entiers', 'ensembles_zero_plus_un': 'bourbaki/entiers',
    # outils IA / experimentations
    'benchmark_ia': 'outils_ia', 'benchmark_goal_ia': 'outils_ia',
    'chercheur': 'outils_ia', 'chercheur_appris': 'outils_ia', 'chercheur_ia': 'outils_ia',
    'encodeur': 'outils_ia', 'modele': 'outils_ia', 'donnees_entrainement': 'outils_ia',
    'prouveur_goal': 'outils_ia', 'couverture': 'outils_ia', 'exemples_livre': 'outils_ia',
}

SCRATCH = ['_c24_suite.py', '_scratch_fini.py']


def pkg_of(mod):
    return MAP[mod].replace('/', '.')


def sh(*args):
    subprocess.run(args, cwd=ROOT, check=True)


def main():
    # 1) dossiers + __init__.py (tous les ancetres)
    dirs = set()
    for d in set(MAP.values()):
        parts = d.split('/')
        for i in range(1, len(parts) + 1):
            dirs.add('/'.join(parts[:i]))
    for d in sorted(dirs):
        os.makedirs(os.path.join(ROOT, d), exist_ok=True)
        ini = os.path.join(ROOT, d, '__init__.py')
        if not os.path.exists(ini):
            with open(ini, 'w', encoding='utf-8') as f:
                f.write('"""Package ' + d.replace('/', '.') + ' (formalisation Bourbaki).""" \n')
    print('dirs crees:', len(dirs))

    # 2) deplacement des modules source (os.replace ; git detecte les renommages)
    moved = 0
    for mod, d in MAP.items():
        src = os.path.join(ROOT, mod + '.py')
        if os.path.exists(src):
            os.replace(src, os.path.join(ROOT, d, mod + '.py'))
            moved += 1
    print('modules deplaces:', moved)

    # 3) suppression des brouillons morts
    for s in SCRATCH:
        p = os.path.join(ROOT, s)
        if os.path.exists(p):
            os.remove(p)
    print('brouillons supprimes')

    # 4) reecriture des imports dans TOUS les .py (recursif)
    # regex par module : from MOD import / import MOD as X / import MOD
    subs = []
    for mod in MAP:
        pk = pkg_of(mod)
        e = re.escape(mod)
        subs.append((re.compile(r'(?m)^(\s*)from\s+' + e + r'\s+import\b'),
                     r'\1from ' + pk + '.' + mod + ' import'))
        subs.append((re.compile(r'(?m)^(\s*)import\s+' + e + r'\s+as\s+(\w+)'),
                     r'\1from ' + pk + ' import ' + mod + r' as \2'))
        subs.append((re.compile(r'(?m)^(\s*)import\s+' + e + r'(\s*(?:#.*)?)$'),
                     r'\1from ' + pk + ' import ' + mod + r'\2'))
    files = []
    for base, _, fs in os.walk(ROOT):
        if '.git' in base or '__pycache__' in base or '.pytest_cache' in base:
            continue
        for f in fs:
            if f.endswith('.py') and f != 'migrate.py':
                files.append(os.path.join(base, f))
    nrw = 0
    for fp in files:
        txt = open(fp, encoding='utf-8').read()
        new = txt
        for rx, rep in subs:
            new = rx.sub(rep, new)
        if new != txt:
            open(fp, 'w', encoding='utf-8').write(new)
            nrw += 1
    print('fichiers reecrits:', nrw, '/', len(files))

    # 5) conftest.py racine (V9 sur sys.path)
    with open(os.path.join(ROOT, 'conftest.py'), 'w', encoding='utf-8') as f:
        f.write('import sys, os\nsys.path.insert(0, os.path.dirname(__file__))\n')
    print('conftest.py ecrit')


if __name__ == '__main__':
    main()
