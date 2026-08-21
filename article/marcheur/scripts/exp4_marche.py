# -*- coding: utf-8 -*-
"""EXP4 : la marche complete sur B4 — mesure de bout en bout."""
import sys, time
PART = (sys.argv[1] if len(sys.argv) > 1 else 'tout')
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
from outils_ia.decouvertes.autonomie.marcheur import marcher

a, b, c, d = var("aM"), var("bM"), var("cM"), var("dM")

def oplus(x, y):
    return successeur(SC(x, y))

assoc = somme_cardinale_associative_iteree(a, b, c)
comm = somme_cardinale_commutative(a, b)
brut = {assoc.conclusion: ("assoc+", assoc), comm.conclusion: ("comm+", comm)}

B4 = egal(oplus(oplus(oplus(a, b), c), d), oplus(a, oplus(b, oplus(c, d))))

def _sonde(e):
    print("  [%7.1fs]" % (time.time() - T0), e, flush=True)

T0 = time.time()
t0 = T0
th, journal = (marcher(B4, brut, sonde=_sonde)
               if PART in ('tout', 'b4') else (None, []))
duree = time.time() - t0
for e in journal:
    print(" ", e)
print("MARCHE : %s en %.2fs" % ("FERMEE" if th else "ouverte", duree))
if th is not None:
    print("  est_clos=%s  ==B4:%s  hyps=%d" % (
        th.est_clos, th.conclusion == B4, len(th.hypotheses)))

if PART == 'b4':
    import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
    print('axiomes:', len(E.theorie_ensembles().axiomes))
    sys.exit(0)

# garde-fou : la variante FAUSSE ne doit pas fermer a travers la MARCHE
F4 = egal(oplus(oplus(oplus(a, b), c), d), oplus(a, oplus(b, oplus(d, d))))
t0 = time.time()
thF, jF = marcher(F4, brut, sonde=_sonde)
print("F4 (faux) : %s en %.2fs" % ("FERME(!!)" if thF else "ouvert (bien)", time.time() - t0))
for e in jF:
    print(" ", e)

import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
print("axiomes:", len(E.theorie_ensembles().axiomes))
