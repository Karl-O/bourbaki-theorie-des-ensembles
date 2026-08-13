"""FAÇADE de compatibilité — le contenu vit dans les sous-dossiers calqués sur le livre.

Arborescence (Bourbaki, Chap. I — Description de la mathématique formelle),
fichiers numérotés par sous-section du livre (préfixe ``outil_`` = hors-livre) :
  * ``i_1_termes_relations/``      §1  i_1_1_assemblage, i_1_2_criteres_CS,
                                       i_1_3_constructions_formatives, i_1_4_criteres_CF,
                                       i_1_app_lecture (outil_formule = couche abrégée, hors-livre)
  * ``i_2_theoremes/``             §2  i_2_2_demonstration + noyau/ criteres/ tactiques/ verification/
  * ``i_3_theories_logiques/``     §3  i_3_4_conjonction (E I.29), i_3_5_equivalence (E I.30)
  * ``i_4_theories_quantifiees/``  §4  i_4_1_quantificateurs (E I.32), i_4_3_*, i_4_4_*
  * ``i_5_theories_egalitaires/``  §5  i_5_1_egalite (E I.38), i_5_2_*, i_5_3_*

Ce module ne fait que RÉ-EXPORTER ces définitions pour les importeurs
historiques (``from bourbaki.i_description_mathematique_formelle.assemblage import ...``). Tout
NOUVEAU module doit importer directement depuis les sous-paquets ci-dessus.
"""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.i_1_1_assemblage import (
    Assemblage, SIGNES_LOGIQUES, est_lettre, lettres,
    concat, negation, disjonction, implication,
    positions_de, tau_x, substitution_b_x_a,
)
from bourbaki.i_description_mathematique_formelle.i_3_theories_logiques.i_3_4_conjonction import (
    conjonction)
from bourbaki.i_description_mathematique_formelle.i_3_theories_logiques.i_3_5_equivalence import (
    equivalence)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_1_quantificateurs import (
    existe, pour_tout)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_1_egalite import egalite

__all__ = [
    "Assemblage", "SIGNES_LOGIQUES", "est_lettre", "lettres",
    "concat", "negation", "disjonction", "implication",
    "positions_de", "tau_x", "substitution_b_x_a",
    "conjonction", "equivalence", "egalite", "existe", "pour_tout",
]
