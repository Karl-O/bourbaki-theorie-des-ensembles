# -*- coding: utf-8 -*-
"""EXP5 (P6) : le marcheur pointe sur Goldbach — attendu : il NE FERME PAS.

Le but est l'enonce GENERAL goldbach() (tout n). La marche doit :
  - miner des motifs dans le but (lesquels ? a lire),
  - ne certifier aucun lemme decisif,
  - terminer TERMINAL avec ses manques nommes — aucune information
    mathematique creee. C'est la revendication P6 : le marcheur est un
    traverseur de derniers kilometres BALISES, pas un producteur de
    mathematiques nouvelles.

Pool : les deux memes lois brutes sur + que le banc oplus (aucun fait
arithmetique specifique — l'enonce du resultat attendu est l'ECHEC nomme).
"""
import sys, time
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[3]))

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_somme.ensembles_arith_somme import (
    somme_cardinale_commutative,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_somme.ensembles_somme_iteree import (
    somme_cardinale_associative_iteree,
)
from outils_ia.conjectures.goldbach import goldbach
from outils_ia.decouvertes.autonomie.marcheur import marcher

a, b, c = var("aG"), var("bG"), var("cG")
assoc = somme_cardinale_associative_iteree(a, b, c)
comm = somme_cardinale_commutative(a, b)
brut = {assoc.conclusion: ("assoc+", assoc), comm.conclusion: ("comm+", comm)}

BUT = goldbach()

T0 = time.time()

def _sonde(e):
    print("  [%7.1fs]" % (time.time() - T0), e, flush=True)

th, journal = marcher(BUT, brut, sonde=_sonde)
print("GOLDBACH : %s en %.2fs" % (
    "FERME(!!! — IMPOSSIBLE, verifier)" if th else "ouvert, manques nommes (attendu)",
    time.time() - T0))
n_term = [e for e in journal if e.get("type") == "terminal"]
print("terminal :", n_term)

import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
print("axiomes:", len(E.theorie_ensembles().axiomes))
