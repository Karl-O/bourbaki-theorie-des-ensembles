# -*- coding: utf-8 -*-
"""Experience de la porte A4 : un but que le chainage seul ne ferme pas,
mais qu'une marche (certifier le lemme, l'ajouter au pool, re-essayer) ferme.

But B4 : ((a(+)b)(+)c)(+)d = a(+)(b(+)(c(+)d))   avec  x(+)y := succ(x+y)
Pool brut : associativite iteree de + , commutativite de + (les DEUX lois de v18).

Exp 1 : besoins(B4, pool brut) -> attendu None (chaine brute ~2x5 pas > max_pas=5)
Exp 2 : certifier L := (+)-assoc (le but de v18), l'ajouter au pool, re-essayer
        -> attendu ferme.
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
faits = {assoc.conclusion: ("assoc+", assoc), comm.conclusion: ("comm+", comm)}

B4 = egal(oplus(oplus(oplus(a, b), c), d), oplus(a, oplus(b, oplus(c, d))))

t0 = time.time()
th, manques = besoins(B4, [], dict(faits), profondeur=4)
t1 = time.time()
print("EXP1 direct  : th=%s  manques=%d  %.2fs" % (
    "FERME" if th is not None else "None", len(manques), t1 - t0))

# Exp 2 : certifier le lemme (+)-assoc (exactement le but de v18)
x, y, z = var("xM"), var("yM"), var("zM")
L = egal(oplus(oplus(x, y), z), oplus(x, oplus(y, z)))
t0 = time.time()
thL, mL = besoins(L, [], dict(faits), profondeur=4)
t1 = time.time()
print("EXP2 lemme L : th=%s  %.2fs" % ("FERME" if thL is not None else "None", t1 - t0))

if thL is not None:
    assert thL.est_clos and thL.conclusion == L
    faits2 = dict(faits)
    faits2[thL.conclusion] = ("assoc-oplus", thL)
    t0 = time.time()
    th2, m2 = besoins(B4, [], faits2, profondeur=4)
    t1 = time.time()
    print("EXP2 but B4  : th=%s  manques=%d  %.2fs" % (
        "FERME" if th2 is not None else "None", len(m2), t1 - t0))
    if th2 is not None:
        print("  est_clos=%s  conclusion==B4 : %s  hyps=%d" % (
            th2.est_clos, th2.conclusion == B4, len(th2.hypotheses)))

from bourbaki.ii_theorie_des_ensembles.ii_1_collectivisantes import axiomes_theorie as E  # noqa
try:
    from outils_ia.decouvertes.test_autonomie import E as _E
except Exception:
    _E = None
