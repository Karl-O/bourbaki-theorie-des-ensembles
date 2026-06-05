"""Range les test_*.py (à plat) dans tests/<miroir de l'arbre source>.

Les imports des tests sont déjà en `from bourbaki...` (réécrits par migrate.py) ;
les imports absolus marchent depuis n'importe quel dossier grâce au conftest
(V9 sur sys.path). On ne fait donc QUE déplacer les fichiers. Pas d'__init__.py
dans tests/ (pytest = mode rootdir, basenames uniques).
"""
from __future__ import annotations
import os, glob
from migrate import MAP  # module source -> dossier 'bourbaki/...' ou 'outils_ia'

ROOT = os.path.dirname(os.path.abspath(__file__))

# test_NAME.py -> module source de reference (overrides pour les noms != module)
OVERRIDES = {
    'test_reflexivite': 'noyau', 'test_egalite': 'tactiques_egalite',
    'test_quantif_abrege': 'tactiques_abrege_quantif', 'test_quantif_egalite': 'tactiques_abrege_egalite',
    'test_congruence_quantif': 'congruence_quantif',
    'test_ia_valeurs': 'modele', 'test_verificateur': 'verificateur_preuve',
    'test_entiers_calcul': 'ensembles_entiers', 'test_ensembles_theoremes': 'ensembles_theoremes',
    'test_tactiques_abrege': 'tactiques_abrege', 'test_tactiques_abrege2': 'tactiques_abrege2',
}


def src_dir_for(test_stem):
    """Retourne le dossier source ('bourbaki/...' ou 'outils_ia') du module testé."""
    name = test_stem[len('test_'):]              # ex. 'somme_associe', 'cardinaux_theoremes'
    if test_stem in OVERRIDES:
        return MAP[OVERRIDES[test_stem]]
    for cand in ('ensembles_' + name, name, 'tactiques_' + name, 'criteres_' + name):
        if cand in MAP:
            return MAP[cand]
    return None


def test_dir_for(src_dir):
    if src_dir == 'bourbaki':
        return 'tests'
    if src_dir.startswith('bourbaki/'):
        return 'tests/' + src_dir[len('bourbaki/'):]
    if src_dir == 'outils_ia':
        return 'tests/outils_ia'
    return 'tests'


def main():
    tests = [os.path.basename(p) for p in glob.glob(os.path.join(ROOT, 'test_*.py'))]
    placed, unknown = 0, []
    for t in tests:
        stem = t[:-3]
        sd = src_dir_for(stem)
        if sd is None:
            unknown.append(t); continue
        td = test_dir_for(sd)
        os.makedirs(os.path.join(ROOT, td), exist_ok=True)
        os.replace(os.path.join(ROOT, t), os.path.join(ROOT, td, t))
        placed += 1
    print('tests rangés:', placed)
    if unknown:
        print('NON CLASSÉS (à placer à la main):', unknown)


if __name__ == '__main__':
    main()
