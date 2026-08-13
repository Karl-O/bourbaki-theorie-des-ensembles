"""§III.3.2 — CANTOR–BERNSTEIN, CLÔTURE (Corollaire 2 du Théorème 1).

API publique du package (ré-exporte les 4 étapes) :
  • image_reciproque_image (ÉTAPE 1)  — rétraction g⁻¹⟨g⟨S⟩⟩=S.
  • morceau_gI             (ÉTAPE 2)  — g⁻¹|(A∖D) bijection A∖D → B∖f⟨D⟩.
  • recollement_h          (ÉTAPE 3)  — h=(f|D)∪(g⁻¹|(A∖D)) bijection a → b.
  • cantor_bernstein       (ÉTAPE 4)  — (a≤b et b≤a) ⇒ Eq(a,b).  GRAND PRIX.
"""
from ._etapes12 import image_reciproque_image, morceau_gI
from ._recollement import recollement_h, cantor_bernstein

__all__ = ["image_reciproque_image", "morceau_gI",
           "recollement_h", "cantor_bernstein"]
