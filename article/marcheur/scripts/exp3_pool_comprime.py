# -*- coding: utf-8 -*-
"""EXP3 : B4 avec le lemme derive SEUL au pool (compression = remplacement).

EXP2 a mesure : B4 + pool {assoc+, comm+, assoc-oplus} -> ferme en 962 s.
Ici : certifier L (3-4 s), puis B4 + pool {assoc-oplus SEUL} -> duree ?
Si secondes : le pas de re-essai du marcheur utilisera le pool COMPRIME.
Bonus : garde-fou — une variante FAUSSE de B4 doit rester ouverte.
"""
import sys, time
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[3]))

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, egal,
)
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_recollement_somme.ensembles_somme_disjointe import (
    somme_cardinale_binaire as SC,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (
    successeur,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_somme.ensembles_arith_somme import (
    somme_cardinale_commutative,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_somme.ensembles_somme_iteree import (
    somme_cardinale_associative_iteree,
)
from outils_ia.decouvertes.besoin import besoins

a, b, c, d = var("aM"), var("bM"), var("cM"), var("dM")

def oplus(x, y):
    return successeur(SC(x, y))

assoc = somme_cardinale_associative_iteree(a, b, c)
comm = somme_cardinale_commutative(a, b)
brut = {assoc.conclusion: ("assoc+", assoc), comm.conclusion: ("comm+", comm)}

B4 = egal(oplus(oplus(oplus(a, b), c), d), oplus(a, oplus(b, oplus(c, d))))

x, y, z = var("xM"), var("yM"), var("zM")
L = egal(oplus(oplus(x, y), z), oplus(x, oplus(y, z)))
t0 = time.time()
thL, _ = besoins(L, [], dict(brut), profondeur=4)
print("lemme L      : %s  %.2fs" % ("FERME" if thL else "None", time.time() - t0))
assert thL is not None and thL.est_clos and thL.conclusion == L

comprime = {thL.conclusion: ("assoc-oplus", thL)}
t0 = time.time()
th, m = besoins(B4, [], dict(comprime), profondeur=4)
print("B4 comprime  : %s  manques=%d  %.2fs" % (
    "FERME" if th else "None", len(m), time.time() - t0))
if th is not None:
    print("  est_clos=%s  ==B4:%s  hyps=%d" % (
        th.est_clos, th.conclusion == B4, len(th.hypotheses)))

#   garde-fou : variante FAUSSE (d remplace c a droite -> non-theoreme)
F4 = egal(oplus(oplus(oplus(a, b), c), d), oplus(a, oplus(b, oplus(d, d))))
t0 = time.time()
thF, _ = besoins(F4, [], dict(comprime), profondeur=4)
print("F4 (faux)    : %s  %.2fs" % ("FERME(!!)" if thF else "ouvert (bien)", time.time() - t0))

import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
print("axiomes:", len(E.theorie_ensembles().axiomes))
