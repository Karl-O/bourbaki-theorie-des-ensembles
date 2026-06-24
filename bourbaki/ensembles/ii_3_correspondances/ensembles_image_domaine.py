"""§II.3.1 — Image du domaine = ensemble des valeurs (Bourbaki E II.10).

Énoncé Bourbaki VERBATIM (E II.10, §3, n°1, suite de la Déf. 3) :

  « comme (x,y) ∈ G entraîne x ∈ pr₁G, on a  G⟨pr₁G⟩ = pr₂G. »

RÉSULTAT (CLOS — 0 hypothèse, inconditionnel — certifié par le noyau LCF) :

  ⊢  G⟨pr₁G⟩ = pr₂G        c.-à-d.   ⊢  image(G, dom G) = img G

où image(G,X) = G⟨X⟩ (E.image), dom G = pr₁G (E.dom, AXIOME_DOM) et img G = pr₂G
(E.img, AXIOME_IMG).  C'est une ÉGALITÉ d'ensembles, donc le résultat est clos
(aucune prémisse honnête : tout couple de G ayant sa 1ᵉ coordonnée dans pr₁G,
l'image du domaine épuise déjà l'ensemble des valeurs).

STRATÉGIE (extensionnalité A1 = double inclusion sur G⟨pr₁G⟩ et pr₂G).

  ⊆  G⟨pr₁G⟩ ⊂ pr₂G — c'est `image_dans_img(G, X)` instancié en X := dom G
     (G⟨X⟩ ⊂ pr₂G pour TOUT X) ; direct.

  ⊇  pr₂G ⊂ G⟨pr₁G⟩ — (∀y)(y∈pr₂G ⇒ y∈G⟨pr₁G⟩).  Soit y :
       _inst_img : (y∈pr₂G) ⇔ (∃x)((x,y)∈G).
       Pour chaque x : (x,y)∈G ⇒ x∈pr₁G  (couple_dans_dom = « x∈pr₁G entraîné par
       (x,y)∈G », l'argument MÊME de Bourbaki) ; d'où (x,y)∈G ⇒ (x∈pr₁G et (x,y)∈G).
       _inst_image (sens ⇐, témoin x) : (x∈pr₁G et (x,y)∈G) ⇒ y∈G⟨pr₁G⟩.
       Composé : (x,y)∈G ⇒ y∈G⟨pr₁G⟩ ; existe_elimination(x) (y non lié) :
       (∃x)((x,y)∈G) ⇒ y∈G⟨pr₁G⟩ ; précomposé par _inst_img (sens ⇒) :
       y∈pr₂G ⇒ y∈G⟨pr₁G⟩ ; generalisation(y) ⇒ pr₂G ⊂ G⟨pr₁G⟩.

  Puis extensionnalite_appliquee(G⟨pr₁G⟩, pr₂G) sur (⊆ et ⊇) ⇒ G⟨pr₁G⟩ = pr₂G.

theorie_ensembles() INCHANGÉE (= 22) : aucun axiome ajouté (primitives N.* seules,
réutilisation de théorèmes/lemmes existants).
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (
    Terme, var, egal, et, appartient, inclus)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege import syllogisme
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    conjonction_intro, equivalence_avant, equivalence_arriere, projection_droite)
from bourbaki.logique.i_3_quantifies.tactiques_abrege_quantif import (
    existe_elimination, monotonie_existe)
from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_theoremes import (
    extensionnalite_appliquee)
from bourbaki.ensembles.ii_3_correspondances.ensembles_correspondances import (
    _inst_image, _inst_img)
from bourbaki.ensembles.fonctions.ii_3_general.ensembles_extensionnalite import (
    couple_dans_dom)


def _T(v):
    """Coercion nom → terme."""
    return v if isinstance(v, Terme) else var(v)


def image_domaine_egale_img(g="G"):
    """⊢ G⟨pr₁G⟩ = pr₂G   (= image(G, dom G) = img G).   (Bourbaki E II.10, §3, n°1.)

    CLOS (0 hypothèse, inconditionnel) : « comme (x,y)∈G entraîne x∈pr₁G, on a
    G⟨pr₁G⟩ = pr₂G ».  Double inclusion (A1) : ⊆ = image_dans_img spécialisé à
    X := dom G (toute image directe ⊂ pr₂G), ⊇ via couple_dans_dom
    (l'entraînement de Bourbaki) + _inst_image.

    NB : on RECONSTRUIT les inclusions avec des TERMES (X := dom G est un terme
    composé, non un nom) ; les helpers `image_dans_img`/`inclus` attendent des
    NOMS et re-wrappent via var() — on appelle donc directement _inst_image /
    _inst_img (qui acceptent des termes via instancie) et generalisation."""
    vG = _T(g)
    vy = var("z")   # élément d'image générique ; nom "z" = liant canonique de `inclus`
    domG = E.dom(vG)                                          # pr₁G
    imgG = E.img(vG)                                          # pr₂G
    imgDom = E.image(vG, domG)                                # G⟨pr₁G⟩

    # ── ⊆ : G⟨pr₁G⟩ ⊂ pr₂G — spécialisation de image_dans_img à X := dom G ────────
    # (z∈G⟨domG⟩ ⇒ z∈pr₂G) : (x∈domG et (x,z)∈G)⇒(x,z)∈G, ∃-monotone, via _inst_*.
    vx = var("x")
    proj = projection_droite(appartient(vx, domG),           # (x∈domG et (x,z)∈G)⇒(x,z)∈G
                             appartient(E.couple(vx, vy), vG))
    mono = monotonie_existe(proj, "x")                       # (∃x …domG)⇒(∃x (x,z)∈G)
    z_imp = syllogisme(equivalence_avant(_inst_image(vG, domG, vy)),
                       syllogisme(mono, equivalence_arriere(_inst_img(vG, vy))))
    incl_avant = N.generalisation("z", z_imp)                # G⟨domG⟩ ⊂ pr₂G  (liant "z")

    # ── ⊇ : pr₂G ⊂ G⟨pr₁G⟩ ───────────────────────────────────────────────────────
    # Pour x quelconque : (x,z)∈G ⇒ x∈pr₁G  (couple_dans_dom, l'entraînement Bourbaki).
    couple_xy = appartient(E.couple(vx, vy), vG)              # (x,z)∈G
    h_xy = N.assume(couple_xy)
    x_in_dom = N.modus_ponens(h_xy, N.loi_deduction(          # x∈pr₁G
        couple_xy, couple_dans_dom(vG, vx, vy)))
    # (x∈pr₁G et (x,z)∈G) ⇒ (∃x)(x∈pr₁G et (x,z)∈G) ⇒ z∈G⟨pr₁G⟩.
    body = et(appartient(vx, domG), couple_xy)                # x∈domG et (x,z)∈G  (= (x|x)corps)
    ex_body = N.modus_ponens(                                 # (∃x)(x∈domG et (x,z)∈G), témoin x
        conjonction_intro(x_in_dom, h_xy), N.s5(body, vx, "x"))
    car_img = _inst_image(vG, domG, vy)                       # z∈G⟨domG⟩ ⇔ (∃x)(x∈domG et (x,z)∈G)
    z_in_imgDom = N.modus_ponens(ex_body, equivalence_arriere(car_img))  # z∈G⟨pr₁G⟩
    couple_imp = N.loi_deduction(couple_xy, z_in_imgDom)      # (x,z)∈G ⇒ z∈G⟨pr₁G⟩
    ex_imp = existe_elimination(couple_imp, "x")             # (∃x)(x,z)∈G ⇒ z∈G⟨pr₁G⟩
    # Précompose par _inst_img (sens ⇒) : z∈pr₂G ⇒ (∃x)(x,z)∈G.
    car_img2 = _inst_img(vG, vy)                              # (z∈pr₂G) ⇔ (∃x)((x,z)∈G)
    z_imp2 = syllogisme(equivalence_avant(car_img2), ex_imp)  # z∈pr₂G ⇒ z∈G⟨pr₁G⟩
    incl_arriere = N.generalisation("z", z_imp2)             # pr₂G ⊂ G⟨pr₁G⟩ (liant "z")

    # ── A1 : (G⟨pr₁G⟩ ⊂ pr₂G  et  pr₂G ⊂ G⟨pr₁G⟩) ⇒ G⟨pr₁G⟩ = pr₂G ──────────────
    return N.modus_ponens(conjonction_intro(incl_avant, incl_arriere),
                          extensionnalite_appliquee(imgDom, imgG))


def image_domaine_egale_img_cible(g="G"):
    """Énoncé visé de `image_domaine_egale_img` (pour vérification stricte)."""
    vG = _T(g)
    return egal(E.image(vG, E.dom(vG)), E.img(vG))


__all__ = ["image_domaine_egale_img", "image_domaine_egale_img_cible"]
