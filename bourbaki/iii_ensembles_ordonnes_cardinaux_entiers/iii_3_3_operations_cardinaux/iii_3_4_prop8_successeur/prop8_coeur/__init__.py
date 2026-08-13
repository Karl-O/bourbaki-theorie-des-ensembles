"""§III.3.4 — Proposition 8 : CŒUR back-and-forth (CAS 1, le marqueur est fixé).

Sous-package du cœur de la Proposition 8 (« si a+1=b+1 alors a=b »).  Il établit
le CAS 1 de l'analyse de cas sur l'image du marqueur * = (∅,1) par une bijection
h : A⊔{∅} → B⊔{∅} :

        CAS 1 : h(*) = *   ⟹   Eq(A×{0}, B×{0}).

Idée : la RESTRICTION  g := h|(A×{0})  de la bijection h à la copie de gauche
A×{0} est une bijection A×{0} → B×{0}.  On prouve les quatre conjoints de
est_bijection_de(g, A×{0}, B×{0}) à partir des seules hypothèses « h bijection de
A⊔{∅} sur B⊔{∅} » et « h(*) = * » :

  • fonctionnel(g)        — sous-graphe d'un graphe fonctionnel (g ⊂ h) ;
  • injective_dans(g,·)   — héritée de h (g ⊂ h, A×{0} ⊂ A⊔{∅}) ;
  • dom g = A×{0}         — A×{0} ⊂ dom h = A⊔{∅}, et g ne retient que A×{0} ;
  • image(g,A×{0}) = B×{0} — le seul point retiré, *, allait sur * (hyp) ; comme *
        n'est ni dans A×{0} ni dans B×{0}, retirer * des deux côtés laisse une
        bijection des compléments.  (la partie dure : injectivité/fonctionnalité
        de h pour exclure que * soit atteint/atteigne depuis A×{0}.)

Puis Eq(A×{0}, B×{0}) par S5, et la combinaison avec eq_copies_gauches_implique_eq
(déjà clos) donnera, dans le module appelant, Eq(A, B) sous les hypothèses du CAS 1.

Le CAS 2 (échange a₀↦b₀) et l'assemblage final inconditionnel restent REPORTÉS.

API ré-exportée (cf. tests/cardinaux/arithmetique/test_prop8_coeur.py)."""
from __future__ import annotations

from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_4_prop8_successeur.prop8_coeur._g import (
    A0_terme, G_RESTR, membre_g_ssi_t, couple_g_si, g_inclus_h, g_fonctionnel,
    g_egale_h, g_injective)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_4_prop8_successeur.prop8_coeur._domaine import g_domaine
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_4_prop8_successeur.prop8_coeur._image import g_image
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_4_prop8_successeur.prop8_coeur._cas1 import (
    cas_fixe_bijection, eq_copies_cas_fixe)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_4_prop8_successeur.prop8_coeur._reduction import (
    eq_cas_fixe_implique_eq)

__all__ = ["A0_terme", "G_RESTR", "membre_g_ssi_t", "couple_g_si", "g_inclus_h",
           "g_fonctionnel", "g_egale_h", "g_injective", "g_domaine", "g_image",
           "cas_fixe_bijection", "eq_copies_cas_fixe", "eq_cas_fixe_implique_eq"]
