"""§II.3.7 / §III.3 — La composée de deux bijections est une bijection.

⊢ (est_bijection_de(F, X, Y) et est_bijection_de(G, Y, Z))
      ⇒ est_bijection_de(G∘F, X, Z).

FONDATION RÉUTILISABLE (transitivité de Eq, Prop. 8 cas 2, etc.) : on expose en
THÉORÈME FERMÉ l'assemblage `bij_comp` des quatre conjoints de la bijectivité de
la composée, déjà bâti à l'intérieur de `equipotence_transitive` mais qui n'y
était pas accessible sous une forme implicative directe.

Les quatre paliers sont DÉJÀ certifiés dans `ensembles_bijection.py` (on les
RÉUTILISE tels quels, rien n'est redéfini) :

  • fonctionnel : `composee_fonctionnelle(G,F)`
        ⊢ (F fonctionnel et G fonctionnel) ⇒ (G∘F fonctionnel)   (Prop. 6) ;
  • domaine    : `composee_domaine(G,F,X,Y)`
        ⊢_{dom F=X, image(F,X)=Y, dom G=Y}  dom(G∘F) = X            (2e conjoint) ;
  • injectif   : `composee_injective(G,F,X,Y)`
        ⊢_{F,G func, dom F=X, image(F,X)=Y, dom G=Y, F inj/X, G inj/Y}
          injective_dans(G∘F, X)                                    (3e conjoint) ;
  • image      : `composee_image(G,F,X,Y,Z)`
        ⊢_{image(F,X)=Y, image(G,Y)=Z}  image(G∘F, X) = Z           (Prop. 5).

`composee(G, F) = G∘F` (E.II.42, Déf. 6 : composee(gp, g) = gp∘g), donc avec
F : X→Y et G : Y→Z, la composée bijective est `E.composee(G, F)` de X vers Z.
On suit la convention de `equipotence_transitive` : paramètres (f, g, x, y, z).
"""
from __future__ import annotations

from bourbaki.logique.formule import var, egal, et, impl, Terme
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.logique.tactiques.tactiques_abrege2 import (conjonction_intro,
                               conjonction_elim_gauche, conjonction_elim_droite)
from bourbaki.cardinaux.ensembles_cardinaux import est_bijection_de
from bourbaki.cardinaux.ensembles_bijection import (composee_fonctionnelle,
                               composee_domaine, composee_injective,
                               composee_image, _cut, _conjoints_bijection)


def _T(v):
    """Coercion nom→terme (accepte un Terme ou un nom de variable)."""
    return v if isinstance(v, Terme) else var(v)


def composee_bijection_conjoints(f="F", g="G", x="X", y="Y", z="Z"):
    """⊢_{bij(F,X,Y), bij(G,Y,Z)}  est_bijection_de(G∘F, X, Z).

    Version « hypothèses ouvertes » : conclut la bijectivité de la composée à
    partir des deux hypothèses de bijectivité `est_bijection_de(F,X,Y)` et
    `est_bijection_de(G,Y,Z)` laissées dans le séquent. C'est le `bij_comp`
    interne de `equipotence_transitive`, ici nommé et réutilisable."""
    vF, vG, vX, vY, vZ = _T(f), _T(g), _T(x), _T(y), _T(z)
    comp = E.composee(vG, vF)                                   # G∘F
    hF = N.assume(est_bijection_de(vF, vX, vY))
    hG = N.assume(est_bijection_de(vG, vY, vZ))
    pFf, pFd, pFi, pFm = _conjoints_bijection(hF, vF, vX, vY)   # F : func, dom, inj, img
    pGf, pGd, pGi, pGm = _conjoints_bijection(hG, vG, vY, vZ)   # G : func, dom, inj, img

    # ── 4 conjoints de est_bijection_de(G∘F, X, Z) ─────────────────────────────
    c1 = N.modus_ponens(conjonction_intro(pFf[1], pGf[1]),
                        composee_fonctionnelle(g, f))           # G∘F fonctionnel (Prop. 6)
    c2 = _cut(composee_domaine(g, f, x, y), [pFd, pGd, pFm])    # dom(G∘F) = X
    c3 = _cut(composee_injective(g, f, x, y),
              [pFi, pGi, pFd, pFf, pFm, pGf, pGd])              # injective_dans(G∘F, X)
    c4 = _cut(composee_image(g, f, x, y, z), [pFm, pGm])        # image(G∘F, X) = Z

    # structure de est_bijection_de : ((func, dom), (inj, img))
    return conjonction_intro(conjonction_intro(c1, c2), conjonction_intro(c3, c4))


def composee_bijection(f="F", g="G", x="X", y="Y", z="Z"):
    """⊢ (est_bijection_de(F,X,Y) et est_bijection_de(G,Y,Z))
          ⇒ est_bijection_de(G∘F, X, Z).

    LA COMPOSÉE DE DEUX BIJECTIONS EST UNE BIJECTION (fondation réutilisable :
    transitivité de l'équipotence, Prop. 8 cas 2, sections/rétractions…).
    Assemble les quatre paliers déjà certifiés via la conjonction des deux
    hypothèses (importation)."""
    vF, vG, vX, vY, vZ = _T(f), _T(g), _T(x), _T(y), _T(z)
    bF = est_bijection_de(vF, vX, vY)
    bG = est_bijection_de(vG, vY, vZ)
    bij_comp = composee_bijection_conjoints(f, g, x, y, z)      # hyps {bF, bG} ⊢ bij(G∘F,X,Z)
    # importation : A⇒(B⇒C) ⟹ (A et B)⇒C  (décharge bG puis bF, recombine via la conjonction)
    imp1 = N.loi_deduction(bF, N.loi_deduction(bG, bij_comp))   # bF ⇒ (bG ⇒ bij(G∘F))
    hab = N.assume(et(bF, bG))
    inner = N.modus_ponens(conjonction_elim_droite(hab),
                           N.modus_ponens(conjonction_elim_gauche(hab), imp1))
    return N.loi_deduction(et(bF, bG), inner)


__all__ = ["composee_bijection", "composee_bijection_conjoints"]
