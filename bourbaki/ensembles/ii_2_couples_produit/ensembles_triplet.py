"""§II.2 — Triplet ordonné (a,b,c) = ((a,b),c) et ses trois projections.

Bourbaki définit le triplet par (x,y,z) := ((x,y),z) (produit de plusieurs ensembles ;
Résumé §3 item 12).  Ses trois projections se lisent par composition des projections de
couples :
    pr₁³(t) = pr₁(pr₁ t),   pr₂³(t) = pr₂(pr₁ t),   pr₃³(t) = pr₂ t.
On CERTIFIE les trois réductions
    pr₁³((a,b,c)) = a,   pr₂³((a,b,c)) = b,   pr₃³((a,b,c)) = c
à partir de `projection_premiere` / `projection_seconde` (pr₁/pr₂ d'un couple, E II.7)
et de la congruence des termes (S6).

Convention de liants (comme `projection_premiere`, E II.7) : les composantes a, b, c sont
DISTINCTES de x, y (liants internes de pr₁/pr₂), ce qui évite la capture.  La bijection
canonique associative (a,b,c)↦((a,b),c) sur E×F×G est traitée ailleurs (produit ternaire
`eq_produit_associatif`).  Rien postulé ; theorie_ensembles INCHANGÉE (22 axiomes).
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import Terme, var, egal
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import instancie
from bourbaki.logique.i_4_egalitaires.tactiques_abrege_egalite import (
    composer_egalites, congruence_terme)
from bourbaki.ensembles.fonctions.hors_ii_3.ii_2_projections.ensembles_projections import (
    projection_premiere, projection_seconde)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def _pr1_terme(U, V):
    """⊢ pr₁((U,V)) = U  pour des TERMES U, V.

    `projection_premiere` n'accepte que des NOMS de variables (var(u)) ; on la
    généralise sur ses deux variables puis on instancie aux termes U, V."""
    g = N.generalisation("v", N.generalisation("u", projection_premiere("u", "v")))
    return instancie(instancie(g, V), U)          # pr₁((U,V)) = U


def _pr2_terme(U, V):
    """⊢ pr₂((U,V)) = V  pour des TERMES U, V  (dual de `_pr1_terme`)."""
    g = N.generalisation("v", N.generalisation("u", projection_seconde("u", "v")))
    return instancie(instancie(g, V), U)          # pr₂((U,V)) = V


def triplet(a="a", b="b", c="c"):
    """(a,b,c) := ((a,b),c)   (triplet ordonné de Bourbaki, E II)."""
    return E.couple(E.couple(_t(a), _t(b)), _t(c))


def triplet_pr1(t):
    """pr₁³ t := pr₁(pr₁ t)   (première coordonnée d'un triplet)."""
    return E.pr1(E.pr1(t))


def triplet_pr2(t):
    """pr₂³ t := pr₂(pr₁ t)   (deuxième coordonnée d'un triplet)."""
    return E.pr2(E.pr1(t))


def triplet_pr3(t):
    """pr₃³ t := pr₂ t   (troisième coordonnée d'un triplet)."""
    return E.pr2(t)


# @livre Ch.R §3 Def.- | E.R.12 item 12 (triplet (x,y,z)=((x,y),z)) | PDF p.315
def triplet_projection_1(a="a", b="b", c="c"):
    """⊢ pr₁³((a,b,c)) = a.   (composantes a, b, c distinctes de x, y.)

    pr₁(((a,b),c)) = (a,b)  (projection_premiere) ; congruence sous pr₁(·) puis
    pr₁((a,b)) = a  (projection_premiere)."""
    va, vb, vc = _t(a), _t(b), _t(c)
    cab = E.couple(va, vb)
    pr1_ext = _pr1_terme(cab, vc)                          # pr₁(((a,b),c)) = (a,b)
    cong = N.modus_ponens(pr1_ext, congruence_terme(       # pr₁(pr₁ t) = pr₁((a,b))
        E.pr1(triplet(va, vb, vc)), cab, E.pr1(var("w"))))
    pr1_inner = _pr1_terme(va, vb)                         # pr₁((a,b)) = a
    return composer_egalites(cong, pr1_inner)              # pr₁(pr₁ t) = a


# @livre Ch.R §3 Def.- | E.R.12 item 12 (triplet (x,y,z)=((x,y),z)) | PDF p.315
def triplet_projection_2(a="a", b="b", c="c"):
    """⊢ pr₂³((a,b,c)) = b.   (composantes a, b, c distinctes de x, y.)

    pr₁(((a,b),c)) = (a,b) ; congruence sous pr₂(·) puis pr₂((a,b)) = b."""
    va, vb, vc = _t(a), _t(b), _t(c)
    cab = E.couple(va, vb)
    pr1_ext = _pr1_terme(cab, vc)                          # pr₁(((a,b),c)) = (a,b)
    cong = N.modus_ponens(pr1_ext, congruence_terme(       # pr₂(pr₁ t) = pr₂((a,b))
        E.pr1(triplet(va, vb, vc)), cab, E.pr2(var("w"))))
    pr2_inner = _pr2_terme(va, vb)                         # pr₂((a,b)) = b
    return composer_egalites(cong, pr2_inner)              # pr₂(pr₁ t) = b


# @livre Ch.R §3 Def.- | E.R.12 item 12 (triplet (x,y,z)=((x,y),z)) | PDF p.315
def triplet_projection_3(a="a", b="b", c="c"):
    """⊢ pr₃³((a,b,c)) = c.   (composantes a, b, c distinctes de x, y.)

    Directement pr₂(((a,b),c)) = c  (projection_seconde)."""
    va, vb, vc = _t(a), _t(b), _t(c)
    return _pr2_terme(E.couple(va, vb), vc)                # pr₂(((a,b),c)) = c


def cible_triplet_projection_1(a="a", b="b", c="c"):
    """Conclusion exacte visée : pr₁³((a,b,c)) = a."""
    va, vb, vc = _t(a), _t(b), _t(c)
    return egal(triplet_pr1(triplet(va, vb, vc)), va)


def cible_triplet_projection_2(a="a", b="b", c="c"):
    """Conclusion exacte visée : pr₂³((a,b,c)) = b."""
    va, vb, vc = _t(a), _t(b), _t(c)
    return egal(triplet_pr2(triplet(va, vb, vc)), vb)


def cible_triplet_projection_3(a="a", b="b", c="c"):
    """Conclusion exacte visée : pr₃³((a,b,c)) = c."""
    va, vb, vc = _t(a), _t(b), _t(c)
    return egal(triplet_pr3(triplet(va, vb, vc)), vc)


__all__ = [
    "triplet", "triplet_pr1", "triplet_pr2", "triplet_pr3",
    "triplet_projection_1", "triplet_projection_2", "triplet_projection_3",
    "cible_triplet_projection_1", "cible_triplet_projection_2", "cible_triplet_projection_3",
]
