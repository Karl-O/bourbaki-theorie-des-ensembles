"""Couche égalitaire — §I.5.3 « Relations fonctionnelles » : univocité et C45.

Deux objets de ce module (chemin ABRÉGÉ, comme les voisins `tactiques_abrege_egalite`) :

  1. CONSTRUCTEUR  `relation_univoque_x(R, x, ...)`  (définition, E.I.40) :
        relation_univoque_x(R) := (∀y)(∀z)( ( (y|x)R et (z|x)R ) ⇒ (y = z) )
     « il existe AU PLUS un x tel que R ».  y, z sont des lettres FRAÎCHES (non
     libres dans R, distinctes entre elles et de x), conformément au livre.

  2. THÉORÈME  `c45_avant(R, x, ...)`  (critère C45, sens DIRECT, E.I.41 L.5-13) :
        { relation_univoque_x(R) }  ⊢  R ⇒ (x = τ_x(R))
     Le sens RÉCIPROQUE (« si R ⇒ (x=T) est un théorème, alors R est univoque »)
     est HORS SCOPE ici.

STRATÉGIE (calquée mot pour mot sur la preuve du livre, E.I.41 L.5-11) :
  Supposons R univoque (hypothèse `relation_univoque_x(R)`).  Adjoignons R.
    · S5 au terme x donne  R = (x|x)R ⇒ (∃x)R ; MP ⊢ (∃x)R.
    · le témoin canonique (déf-τ : (∃x)R ⇒ (τ_x(R)|x)R) ; MP ⊢ (τ_x(R)|x)R.
    · conjonction_intro :  ⊢ R et (τ_x(R)|x)R.
    · l'univocité instanciée en y:=x, z:=τ_x(R) donne
         (R et (τ_x(R)|x)R) ⇒ (x = τ_x(R))  [car (x|x)R = R, structurellement] ;
      MP ⊢ x = τ_x(R).
    · loi_deduction sur R décharge R :  { univoque } ⊢ R ⇒ (x = τ_x(R)).

INVARIANTS (preuve close/honnête) :
  · conclusion == R ⇒ (x = τ_x(R))  (égalité STRUCTURELLE, pas seulement alpha) ;
  · hypotheses == { relation_univoque_x(R) }  exactement (aucune hypothèse parasite) ;
  · est_clos == False (le théorème dépend honnêtement de l'univocité).
  Le contenu réel est l'unicité : c'est elle, instanciée, qui FORCE x = τ_x(R) ;
  rien d'une tautologie déguisée.

FRONTIÈRE DE CONFIANCE : tout passe par les primitives `N.*` du noyau abrégé et
des tactiques dérivées déjà certifiées (conjonction_intro, instancie). Aucune
fabrication de `Theoreme`, aucun monkeypatch.
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (
    var, egal, tau, impl, et, pourtout, subst_f, libres_f,
)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    conjonction_intro, instancie,
)


def _deux_fraiches(eviter: set) -> tuple[str, str]:
    """Deux lettres distinctes (préférence y, z ; sinon @k) hors de `eviter`.

    Sert à respecter la clause de fraîcheur du livre : y, z distinctes entre
    elles, distinctes de x et ne figurant pas dans R."""
    choix, sortie = ["y", "z", "u", "v", "w", "s", "t", "r"], []
    k = 0
    for _ in range(2):
        c = next((nom for nom in choix if nom not in eviter), None)
        if c is None:
            while ("@" + str(k)) in eviter:
                k += 1
            c = "@" + str(k)
        eviter = eviter | {c}
        sortie.append(c)
    return sortie[0], sortie[1]


# @livre Ch.I §5.3 Def.- | E I.40 L.34-46 | PDF p.40
def relation_univoque_x(R, x: str, y: str | None = None, z: str | None = None):
    """Relation « il existe au plus un x tel que R » (définition, E.I.40).

        relation_univoque_x(R) := (∀y)(∀z)( ( (y|x)R et (z|x)R ) ⇒ (y = z) )

    où (t|x)R = `subst_f(t, x, R)`.  y, z sont CHOISIES FRAÎCHES (distinctes
    entre elles, distinctes de x et non libres dans R), comme l'exige Bourbaki ;
    on peut les imposer mais elles doivent satisfaire la fraîcheur.  La lettre x
    n'est pas libre dans le résultat (elle est consommée par la substitution).
    """
    interdits = libres_f(R) | {x}
    if y is None or z is None:
        fy, fz = _deux_fraiches(interdits)
        y = y or fy
        z = z or fz
    if y == z or y in interdits or z in interdits:
        raise ValueError("y, z doivent être fraîches, distinctes et ≠ x")
    Ry = subst_f(var(y), x, R)                       # (y|x)R
    Rz = subst_f(var(z), x, R)                       # (z|x)R
    corps = impl(et(Ry, Rz), egal(var(y), var(z)))   # ((y|x)R et (z|x)R) ⇒ (y=z)
    return pourtout(y, pourtout(z, corps))           # (∀y)(∀z) …


# @livre Ch.I §5.3 Crit.45 | E I.41 L.5-13 | PDF p.41
def c45_avant(R, x: str, y: str | None = None, z: str | None = None):
    """C45, sens DIRECT (E.I.41 L.5-13) :

        { relation_univoque_x(R) }  ⊢  R ⇒ (x = τ_x(R)).

    Preuve fidèle au livre (cf. en-tête de module).  Le sens réciproque est
    hors scope.  `est_clos` vaut False : l'unique hypothèse non déchargée est
    exactement l'univocité de R en x.
    """
    uni = relation_univoque_x(R, x, y, z)            # (∀y)(∀z)(…)  = hypothèse C45
    t = tau(x, R)                                    # τ_x(R)
    witness = subst_f(t, x, R)                        # (τ_x(R)|x)R

    hR = N.assume(R)                                 # {R} ⊢ R
    # S5 au terme x : (x|x)R ⇒ (∃x)R, et (x|x)R = R (substitution identité) :
    exR = N.modus_ponens(hR, N.s5(R, var(x), x))     # {R} ⊢ (∃x)R
    wb = N.modus_ponens(exR, N.existe_temoin(R, x))  # {R} ⊢ (τ_x(R)|x)R
    assert wb.conclusion == witness                  # garde-fou : témoin structurel
    conj = conjonction_intro(hR, wb)                 # {R} ⊢ R et (τ_x(R)|x)R

    huni = N.assume(uni)                             # {uni} ⊢ univocité
    # instancie y:=x  puis  z:=τ_x(R) :
    imp = instancie(instancie(huni, var(x)), t)      # {uni} ⊢ (R et (τ_x(R)|x)R) ⇒ (x=τ_x(R))
    eq = N.modus_ponens(conj, imp)                   # {R, uni} ⊢ x = τ_x(R)
    return N.loi_deduction(R, eq)                    # {uni} ⊢ R ⇒ (x = τ_x(R))


__all__ = ["relation_univoque_x", "c45_avant"]
