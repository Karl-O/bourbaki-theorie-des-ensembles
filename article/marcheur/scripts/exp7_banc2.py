# -*- coding: utf-8 -*-
"""EXP7 : le banc 2 APRES la brique-pont — le marcheur doit fermer.

Jonction des deux fronts (21 aout) : les identites de quotients de E III.39
reposent sur ce schema, et le depot n'a (peut-etre) que la version
niveau-ENSEMBLES Card(A x (B u C)) = Card((A x B) u (A x C)) — le pont vers le
niveau OPERATIONS (produit_cardinal_binaire / somme_cardinale_binaire de
cardinaux) n'est pas certain.

Attendu : le mineur sort les motifs PCB et SC ; la conjecture croisee de tete
EST la distributivite ; l'oracle ne peut PAS la voir (produit d'un numeral par
un terme-somme : hors table, silence) ; la certification depuis le pool
{distributivite_cardinale, lois de +} REUSSIT ou NOMME le pont manquant.
Les deux issues sont des resultats : fermer = banc 2 amorce ; echouer = la
machine designe la brique du livre a ecrire (c'est le mode de travail du
projet depuis ev.373).
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
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_produit.ensembles_arith_cardinale import (
    produit_cardinal_binaire as PCB,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_produit.ensembles_distributivite_operations import (
    distributivite_operations,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_somme.ensembles_arith_somme import (
    somme_cardinale_commutative,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_somme.ensembles_somme_iteree import (
    somme_cardinale_associative_iteree,
)
from outils_ia.decouvertes.besoin import besoins
from outils_ia.decouvertes.autonomie.marcheur import marcher

a, b, c = var("aX"), var("bX"), var("cX")

dc = distributivite_operations("Adx", "Bdx", "Cdx")   # a.(b+c)=a.b+a.c, vars FRAICHES
#   (vars fraiches : le marcheur doit INSTANCIER la loi — pas la trouver toute faite)
comm = somme_cardinale_commutative(a, b)
assoc = somme_cardinale_associative_iteree(a, b, c)
brut = {dc.conclusion: ("distrib-ens", dc),
        comm.conclusion: ("comm+", comm),
        assoc.conclusion: ("assoc+", assoc)}

#   le but : la distributivite au niveau des OPERATIONS cardinales
BUT = egal(PCB(a, SC(b, c)), SC(PCB(a, b), PCB(a, c)))

T0 = time.time()

def _sonde(e):
    print("  [%7.1fs]" % (time.time() - T0), e, flush=True)

#   1. chainage direct (le cote gauche de la mesure)
th, manques = besoins(BUT, [], dict(brut), profondeur=4)
print("DIRECT  : %s  manques=%d  %.2fs" % (
    "FERME" if th else "None", len(manques), time.time() - T0), flush=True)

#   2. la marche
t0 = time.time()
th2, journal = marcher(BUT, brut, sonde=_sonde, paliers_max=1)
print("MARCHE  : %s en %.2fs" % ("FERMEE" if th2 else "ouverte", time.time() - t0))
if th2 is not None:
    print("  est_clos=%s  ==BUT:%s  hyps=%d" % (
        th2.est_clos, th2.conclusion == BUT, len(th2.hypotheses)))

import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
print("axiomes:", len(E.theorie_ensembles().axiomes))
