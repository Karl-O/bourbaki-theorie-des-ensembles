"""§III — QUATRE BRIQUES RÉUTILISABLES de la RESTRICTION d'une fonction/iso à un
sous-ensemble S1.

On NE prétend PAS prouver « la restriction est un iso sur son image » (le
recollement du codomaine = image(φ|S1) = φ⟨S1⟩ est porté ailleurs).  On livre les
QUATRE briques propres, chacune un Théorème :

  (1) restriction_fonctionnelle_piece :
        { est_fonctionnel(φ) }  ⊢  est_fonctionnel(φ|S1).
      RÉUTILISE `restriction_fonctionnelle` (ensembles_cantor_bernstein_fin), qui en
      donne la forme implicative CLOSE ; on la passe en forme à-hypothèse.

  (2) restriction_domaine_piece :
        { inclus(S1, dom φ) }  ⊢  egal(dom(φ|S1), S1).
      RÉUTILISE `restriction_dom_sous_inclusion` (ensembles_cantor_bernstein_bij),
      forme implicative CLOSE → forme à-hypothèse.

  (3) restriction_injective_piece :
        { injective_dans(φ, S2), inclus(S1, S2),
          est_fonctionnel(φ), inclus(S1, dom φ) }  ⊢  injective_dans(φ|S1, S1).
      NEUF.  La cible idéale ne porte que { injective_dans(φ,S2), inclus(S1,S2) },
      mais relier (φ|S1)(u) à φ(u) EXIGE l'unicité de la valeur, d'où les deux
      hypothèses additionnelles est_fonctionnel(φ) et inclus(S1, dom φ).  Elles sont
      INDISPENSABLES (un graphe vaut τy(faux) hors domaine ; sans fonctionnalité,
      (φ|S1)(u) n'est pas déterminée par φ(u)).  Le pont de valeur est
      `restriction_valeur` (liant-valeur y, défaut de injective_dans).

  (4) restriction_compatible_ordre_piece :
        { compatible_ordre(φ, S2, R, R'), inclus(S1, S2),
          est_fonctionnel(φ), inclus(S1, dom φ) }  ⊢  compatible_ordre(φ|S1, S1, R, R').
      NEUF (au-delà de `restriction_compatible_ordre` qui ne RESTREINT QUE L'ENSEMBLE,
      gardant la même fonction φ).  Ici la FONCTION devient φ|S1, donc φ(x) → (φ|S1)(x)
      dans le second membre de l'équivalence d'ordre.  `compatible_ordre` construit
      f(x) avec le liant-valeur « j » ; le pont vaut donc
      (φ|S1)(x)[j] = (φ|S1)(x)[y] = φ(x)[y] = φ(x)[j]
      via valeur_j_egal_y + restriction_valeur + valeur_y_egal_j (PONT j↔y, alpha_tau
      CS1).  Mêmes deux hypothèses additionnelles que (3), pour la même raison.
      ⚠ Variables de quantification a, b (pas x, y) : « y » est le liant-valeur du
      pont, on évite que le POINT s'appelle « y » (capture refusée par alpha_tau).

INVARIANT : theorie_ensembles() = 22.  Rien postulé : on réutilise des théorèmes
déjà certifiés (AXIOME_RESTRICTION est l'un des 22 axiomes).  NON vacueux : aucune
conclusion n'est l'une de ses hypothèses.
"""
from __future__ import annotations

from bourbaki.logique.formule import (
    Terme, var, egal, et, impl, appartient, pourtout, inclus, subst_f,
)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.ordre import ensembles_ordre_vocab as V
from bourbaki.ordre.ensembles_valeur_bridge import valeur_j_egal_y, valeur_y_egal_j
from bourbaki.logique.tactiques.tactiques_abrege_egalite import (
    composer_egalites, symetrie,
)
from bourbaki.logique.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    instancie, equivalence_transitivite,
)
from bourbaki.cardinaux.ensembles_cantor_bernstein_fin import restriction_fonctionnelle
from bourbaki.cardinaux.ensembles_cantor_bernstein_bij import (
    restriction_dom_sous_inclusion, restriction_valeur,
)
from bourbaki.cardinaux.ensembles_trichotomie_restriction import (
    restriction_compatible_ordre,
)
from bourbaki.cardinaux.ensembles_lemme4_croissante import _R_de


def _t(x):
    """var(x) sur un NOM ; coercition sûre si x est déjà un Terme (bug var(Terme))."""
    return x if isinstance(x, Terme) else var(x)


# ════════════════════════════════════════════════════════════════════════════
#  PIÈCE (1) — la restriction d'un graphe fonctionnel est fonctionnelle.
#  RÉUTILISE restriction_fonctionnelle (forme CLOSE) → forme à-hypothèse.
# ════════════════════════════════════════════════════════════════════════════
def restriction_fonctionnelle_piece(phi="phi", S1="S1"):
    """⊢ { est_fonctionnel(φ) }  ⊢  est_fonctionnel(φ|S1).

    RÉUTILISE `restriction_fonctionnelle` (ensembles_cantor_bernstein_fin), qui
    prouve la forme CLOSE  est_fonctionnel(φ) ⇒ est_fonctionnel(φ|S1) ; on la passe
    en forme à-hypothèse par modus ponens sur l'hypothèse assumée."""
    vphi = _t(phi)
    impl_clos = restriction_fonctionnelle(phi, S1)          # ⊢ func φ ⇒ func φ|S1  (clos)
    hyp = N.assume(E.est_fonctionnel(vphi))                 # { func φ }
    return N.modus_ponens(hyp, impl_clos)                   # { func φ } ⊢ func φ|S1


def restriction_fonctionnelle_piece_cible(phi="phi", S1="S1"):
    """ÉNONCÉ-cible (test miroir) : conclusion de la pièce (1)."""
    return E.est_fonctionnel(E.restriction(_t(phi), _t(S1)))


# ════════════════════════════════════════════════════════════════════════════
#  PIÈCE (2) — si S1 ⊆ dom φ, alors dom(φ|S1) = S1.
#  RÉUTILISE restriction_dom_sous_inclusion (forme CLOSE) → forme à-hypothèse.
# ════════════════════════════════════════════════════════════════════════════
def restriction_domaine_piece(phi="phi", S1="S1"):
    """⊢ { inclus(S1, dom φ) }  ⊢  egal(dom(φ|S1), S1).

    RÉUTILISE `restriction_dom_sous_inclusion` (ensembles_cantor_bernstein_bij), qui
    prouve la forme CLOSE  (S1⊂dom φ) ⇒ dom(φ|S1)=S1 (via AXIOME_RESTRICTION +
    AXIOME_DOM + extensionnalité A1) ; passée en forme à-hypothèse."""
    vphi, vS1 = _t(phi), _t(S1)
    impl_clos = restriction_dom_sous_inclusion(phi, S1)     # ⊢ (S1⊂dom φ) ⇒ dom(φ|S1)=S1  (clos)
    hyp = N.assume(inclus(vS1, E.dom(vphi)))                # { S1⊂dom φ }
    return N.modus_ponens(hyp, impl_clos)                   # { S1⊂dom φ } ⊢ dom(φ|S1)=S1


def restriction_domaine_piece_cible(phi="phi", S1="S1"):
    """ÉNONCÉ-cible (test miroir) : conclusion de la pièce (2)."""
    vphi, vS1 = _t(phi), _t(S1)
    return egal(E.dom(E.restriction(vphi, vS1)), vS1)


# ════════════════════════════════════════════════════════════════════════════
#  PIÈCE (3) — l'injectivité sur S2 ⊇ S1 se transmet à φ|S1 sur S1.
#  NEUF.  Pont de valeur (φ|S1)(u)=φ(u) via restriction_valeur (liant-valeur y).
# ════════════════════════════════════════════════════════════════════════════
def restriction_injective_piece(phi="phi", S1="S1", S2="S2", u="c", up="d"):
    """⊢ { injective_dans(φ, S2), inclus(S1, S2),
            est_fonctionnel(φ), inclus(S1, dom φ) }
          ⊢ injective_dans(φ|S1, S1).

    Soit u,u'∈S1.  Comme S1⊆dom φ et φ fonctionnel, (φ|S1)(u)=φ(u) et
    (φ|S1)(u')=φ(u') (restriction_valeur).  De (φ|S1)(u)=(φ|S1)(u') on tire
    φ(u)=φ(u') ; comme S1⊆S2, u,u'∈S2, donc l'injectivité de φ sur S2 donne u=u'.

    NOTE D'HONNÊTETÉ : la cible idéale ne porte que { injective_dans(φ,S2),
    inclus(S1,S2) }.  Mais relier (φ|S1)(u) à φ(u) EXIGE l'unicité de la valeur :
    sans est_fonctionnel(φ) et inclus(S1, dom φ), (φ|S1)(u) n'est pas déterminée par
    φ(u) (un graphe vaut τy(faux) hors de son domaine).  Ces deux hypothèses sont
    donc INDISPENSABLES, pas du gold-plating.

    Liants u, u' nommés « c », « d » par défaut (≠ holes internes w/y/v/z de
    restriction_valeur)."""
    vphi, vS1, vS2 = _t(phi), _t(S1), _t(S2)
    vu, vup = var(u), var(up)
    fX = E.restriction(vphi, vS1)
    fXu, fXup = E.valeur(fX, vu), E.valeur(fX, vup)          # liant-valeur y (défaut)
    phiu, phiup = E.valeur(vphi, vu), E.valeur(vphi, vup)

    Hinj = N.assume(E.injective_dans(vphi, vS2, u, up))     # φ injective sur S2
    HinclS2 = N.assume(inclus(vS1, vS2))                    # S1 ⊆ S2
    HinclDom = N.assume(inclus(vS1, E.dom(vphi)))           # S1 ⊆ dom φ

    # corps : (u∈S1 et u'∈S1 et (φ|S1)(u)=(φ|S1)(u')) ⇒ u=u'
    hyp = et(et(appartient(vu, vS1), appartient(vup, vS1)), egal(fXu, fXup))
    H = N.assume(hyp)
    uS1 = conjonction_elim_gauche(conjonction_elim_gauche(H))
    upS1 = conjonction_elim_droite(conjonction_elim_gauche(H))
    val_eq = conjonction_elim_droite(H)                     # (φ|S1)(u)=(φ|S1)(u')

    def fX_eq_phi(t, tS1):
        """sous {func φ, S1⊆dom φ, t∈S1} : ⊢ (φ|S1)(t)=φ(t)  (restriction_valeur)."""
        rv = restriction_valeur(vphi, vS1, t)               # {func φ, t∈S1, t∈dom φ} ⊢ (φ|S1)(t)=φ(t)
        tInDom = N.modus_ponens(tS1, instancie(HinclDom, t))            # t∈dom φ
        rv = N.modus_ponens(tInDom, N.loi_deduction(appartient(t, E.dom(vphi)), rv))
        rv = N.modus_ponens(tS1, N.loi_deduction(appartient(t, vS1), rv))
        return rv

    fu = fX_eq_phi(vu, uS1)                                 # (φ|S1)(u)=φ(u)
    fup = fX_eq_phi(vup, upS1)                              # (φ|S1)(u')=φ(u')
    # φ(u) = (φ|S1)(u) = (φ|S1)(u') = φ(u')
    phiu_eq_fXu = N.modus_ponens(fu, symetrie(fXu, phiu))   # φ(u)=(φ|S1)(u)
    phiu_eq_phiup = composer_egalites(
        composer_egalites(phiu_eq_fXu, val_eq), fup)        # φ(u)=φ(u')

    # injectivité de φ sur S2 : (u∈S2 et u'∈S2 et φ(u)=φ(u')) ⇒ u=u'
    inj_inst = instancie(instancie(Hinj, vu), vup)
    uS2 = N.modus_ponens(uS1, instancie(HinclS2, vu))       # u∈S2
    upS2 = N.modus_ponens(upS1, instancie(HinclS2, vup))    # u'∈S2
    u_eq_up = N.modus_ponens(
        conjonction_intro(conjonction_intro(uS2, upS2), phiu_eq_phiup), inj_inst)

    body = N.loi_deduction(hyp, u_eq_up)
    return N.generalisation(u, N.generalisation(up, body))  # injective_dans(φ|S1, S1)


def restriction_injective_piece_cible(phi="phi", S1="S1", S2="S2", u="c", up="d"):
    """ÉNONCÉ-cible (test miroir) : conclusion de la pièce (3)."""
    return E.injective_dans(E.restriction(_t(phi), _t(S1)), _t(S1), u, up)


# ════════════════════════════════════════════════════════════════════════════
#  PIÈCE (4) — φ|S1 reste compatible avec l'ordre sur S1 (φ:S2 compatible, S1⊆S2).
#  NEUF.  La FONCTION devient φ|S1 : φ(x) → (φ|S1)(x) via le PONT j↔y.
# ════════════════════════════════════════════════════════════════════════════
def restriction_compatible_ordre_piece(phi="phi", S1="S1", S2="S2", R="R", Rp="Rp",
                                       x="a", y="b"):
    """⊢ { compatible_ordre(φ, S2, R, R'), inclus(S1, S2),
            est_fonctionnel(φ), inclus(S1, dom φ) }
          ⊢ compatible_ordre(φ|S1, S1, R, R').

    DEUX TEMPS.
      (A) `restriction_compatible_ordre` RESTREINT L'ENSEMBLE :
          { compatible_ordre(φ,S2), S1⊆S2 } ⊢ compatible_ordre(φ,S1,R,R').
          (même fonction φ, ensemble S2 → S1).
      (B) on RESTREINT LA FONCTION φ → φ|S1 : pour x,y∈S1, on remplace φ(x),φ(y) par
          (φ|S1)(x),(φ|S1)(y) dans R'{·,·} via Leibniz (s6), grâce au pont de valeur
          (φ|S1)(t)[j] = φ(t)[j]  (valeur_j_egal_y ∘ restriction_valeur ∘
          valeur_y_egal_j ; liant-valeur « j » de compatible_ordre).

    NOTE D'HONNÊTETÉ : la cible idéale ne porte que { compatible_ordre(φ,S2,R,R'),
    inclus(S1,S2) }.  Mais changer la fonction en φ|S1 force le pont (φ|S1)(t)=φ(t),
    qui EXIGE est_fonctionnel(φ) et inclus(S1, dom φ).  Ces deux hypothèses sont
    INDISPENSABLES (c'est exactement le « value/codomaine matching subtil »).

    ⚠ Variables de quantification a, b par défaut (PAS x, y) : « y » est le liant du
    pont valeur_*_y ; un point nommé « y » provoquerait une capture refusée par
    alpha_tau."""
    Rf, Rpf = _R_de(R), _R_de(Rp)
    vphi, vS1, vS2 = _t(phi), _t(S1), _t(S2)
    vx, vy = var(x), var(y)
    fX = E.restriction(vphi, vS1)
    phix, phiy = E.valeur(vphi, vx, b='j'), E.valeur(vphi, vy, b='j')
    fXx, fXy = E.valeur(fX, vx, b='j'), E.valeur(fX, vy, b='j')

    HinclDom = N.assume(inclus(vS1, E.dom(vphi)))           # S1 ⊆ dom φ

    # (A) restriction de l'ENSEMBLE : compatible_ordre(φ, S1, R, R')  [hyps compat_S2, S1⊆S2]
    thmA = restriction_compatible_ordre(phi, S2, S1, R, Rp, x, y)
    bodyA = instancie(instancie(thmA, vx), vy)              # (x∈S1 et y∈S1) ⇒ (R{x,y} ⇔ R'{φ(x),φ(y)})

    # pont de valeur (φ|S1)(t)[j] = φ(t)[j], hyps {func φ, t∈dom φ, t∈S1}
    def val_bridge(t, tS1):
        b1 = valeur_j_egal_y(fX, t)                         # (φ|S1)(t)[j]=(φ|S1)(t)[y]  (clos)
        rv = restriction_valeur(vphi, vS1, t)               # (φ|S1)(t)[y]=φ(t)[y]       {func φ,t∈S1,t∈dom φ}
        b2 = valeur_y_egal_j(vphi, t)                       # φ(t)[y]=φ(t)[j]            (clos)
        e = composer_egalites(composer_egalites(b1, rv), b2)   # (φ|S1)(t)[j]=φ(t)[j]
        tInDom = N.modus_ponens(tS1, instancie(HinclDom, t))                # t∈dom φ
        e = N.modus_ponens(tInDom, N.loi_deduction(appartient(t, E.dom(vphi)), e))
        e = N.modus_ponens(tS1, N.loi_deduction(appartient(t, vS1), e))
        return e

    # corps cible : (x∈S1 et y∈S1) ⇒ (R{x,y} ⇔ R'{(φ|S1)(x),(φ|S1)(y)})
    Hpre = N.assume(et(appartient(vx, vS1), appartient(vy, vS1)))
    xS1 = conjonction_elim_gauche(Hpre)
    yS1 = conjonction_elim_droite(Hpre)

    px_fx = N.modus_ponens(val_bridge(vx, xS1), symetrie(fXx, phix))   # φ(x)[j]=(φ|S1)(x)[j]
    py_fy = N.modus_ponens(val_bridge(vy, yS1), symetrie(fXy, phiy))   # φ(y)[j]=(φ|S1)(y)[j]

    # Leibniz double : R'{φ(x),φ(y)} ⇔ R'{(φ|S1)(x),(φ|S1)(y)}
    h1, h2 = "hh1", "hh2"
    templ = Rpf(var(h1), var(h2))                          # ((h1,h1),(h1,h2)) ∈ R'
    eq1 = N.modus_ponens(px_fx, N.s6(phix, fXx, h1, subst_f(phiy, h2, templ)))
    eq2 = N.modus_ponens(py_fy, N.s6(phiy, fXy, h2, subst_f(fXx, h1, templ)))
    eqRp = equivalence_transitivite(eq1, eq2)              # R'{φ(x),φ(y)} ⇔ R'{(φ|S1)(x),(φ|S1)(y)}

    inner_A = N.modus_ponens(Hpre, bodyA)                  # R{x,y} ⇔ R'{φ(x),φ(y)}
    inner_target = equivalence_transitivite(inner_A, eqRp) # R{x,y} ⇔ R'{(φ|S1)(x),(φ|S1)(y)}
    body = N.loi_deduction(et(appartient(vx, vS1), appartient(vy, vS1)), inner_target)
    return N.generalisation(x, N.generalisation(y, body))  # compatible_ordre(φ|S1, S1, R, R')


def restriction_compatible_ordre_piece_cible(phi="phi", S1="S1", S2="S2",
                                             R="R", Rp="Rp", x="a", y="b"):
    """ÉNONCÉ-cible (test miroir) : conclusion de la pièce (4)."""
    Rf, Rpf = _R_de(R), _R_de(Rp)
    return V.compatible_ordre(E.restriction(_t(phi), _t(S1)), _t(S1), Rf, Rpf, x, y)


__all__ = [
    "restriction_fonctionnelle_piece", "restriction_fonctionnelle_piece_cible",
    "restriction_domaine_piece", "restriction_domaine_piece_cible",
    "restriction_injective_piece", "restriction_injective_piece_cible",
    "restriction_compatible_ordre_piece", "restriction_compatible_ordre_piece_cible",
]
