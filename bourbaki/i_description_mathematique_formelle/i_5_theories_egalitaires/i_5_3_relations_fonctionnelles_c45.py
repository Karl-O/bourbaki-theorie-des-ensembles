"""Couche égalitaire — §I.5.3 « Relations fonctionnelles » : univocité et C45.

Deux objets de ce module (chemin ABRÉGÉ, comme les voisins `tactiques_abrege_egalite`) :

  1. CONSTRUCTEUR  `relation_univoque_x(R, x, ...)`  (définition, E.I.40) :
        relation_univoque_x(R) := (∀y)(∀z)( ( (y|x)R et (z|x)R ) ⇒ (y = z) )
     « il existe AU PLUS un x tel que R ».  y, z sont des lettres FRAÎCHES (non
     libres dans R, distinctes entre elles et de x), conformément au livre.

  2. THÉORÈME  `c45_avant(R, x, ...)`  (critère C45, sens DIRECT, E.I.41 L.5-13) :
        { relation_univoque_x(R) }  ⊢  R ⇒ (x = τ_x(R))

  3. SCHÉMA  `c45_arriere(R, x, T, thm_R_imp_T, ...)`  (C45, sens RÉCIPROQUE,
     E.I.41 L.14-19) : d'un THÉORÈME CLOS  ⊢ R ⇒ (x = T)  (T ne contenant pas x)
     produit  ⊢ relation_univoque_x(R)  — « R est univoque en x ».

Les deux critères C45 sont des MÉTATHÉORÈMES (critères de chapitre I) réalisés en
« fonction Python vérifiable » : pour chaque R concret elles ÉMETTENT une
dérivation du noyau ; aucune n'enregistre un `Theoreme` schématique.

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

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, egal, tau, impl, et, pourtout, subst_f, libres_f, libres_t, existe,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite, instancie,
)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
    symetrie, composer_egalites,
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
# @livre Ch.I §5.3 Def.- | E I.41 L.1-4 | PDF p.41  (fin de la définition : y, z lettres distinctes, ≠ x, hors de R et des axiomes explicites)
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

    Preuve fidèle au livre (cf. en-tête de module).  `est_clos` vaut False :
    l'unique hypothèse non déchargée est exactement l'univocité de R en x.
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


# @livre Ch.I §5.3 Demo.- | E I.41 L.14-19 | PDF p.41  (démo du sens RÉCIPROQUE de C45 — DÉRIVÉE, schéma c45_arriere)
def c45_arriere(R, x: str, T, thm_R_imp_T, y: str | None = None,
                z: str | None = None):
    """C45, sens RÉCIPROQUE (E.I.41 L.14-19) — schéma métathéorique vérifiable :

        Données : un terme T ne contenant PAS x (x n'est pas constante de 𝒯) et
        un THÉORÈME CLOS  thm_R_imp_T : ⊢ R ⇒ (x = T).
        Produit :  ⊢ relation_univoque_x(R, x)
                     = (∀y)(∀z)( ( (y|x)R et (z|x)R ) ⇒ (y = z) ).

    Route VERBATIM du livre (E.I.41 L.14-19) : x n'étant pas constante et ne
    figurant pas dans T, appliquer (y|x) puis (z|x) au théorème R ⇒ (x=T) donne
    les théorèmes (y|x)R ⇒ (y=T) et (z|x)R ⇒ (z=T) — ici, généralisation sur x
    (LICITE car R ⇒ (x=T) est CLOS) puis instanciation en y, z, avec
    (y|x)(x=T) = (y=T) car x ∉ T.  Sous (y|x)R et (z|x)R : y=T et z=T, d'où y=z
    par symétrie + transitivité de =.

    Comme c45_avant (sens direct), c'est une FONCTION-SCHÉMA (le métathéorème C45,
    critère de chapitre I) : elle n'enregistre AUCUN Theoreme schématique ; pour
    R, T concrets elle ÉMET une dérivation du noyau, ici CLOSE (est_clos).
    """
    if x in libres_t(T):
        raise ValueError("C45 réciproque : le terme T ne doit pas contenir x")
    xeqT = egal(var(x), T)
    if not thm_R_imp_T.est_clos or thm_R_imp_T.conclusion != impl(R, xeqT):
        raise ValueError(
            "thm_R_imp_T doit être un théorème CLOS de conclusion R ⇒ (x = T)")

    interdits = libres_f(R) | {x} | libres_t(T)
    if y is None or z is None:
        fy, fz = _deux_fraiches(interdits)
        y = y or fy
        z = z or fz
    if y == z or y in interdits or z in interdits:
        raise ValueError("y, z doivent être fraîches, distinctes, ≠ x, hors de R et T")

    # (∀x)(R ⇒ (x=T)) : généralisation LICITE (thm_R_imp_T CLOS ⇒ x non libre dans les hyp.)
    gen_x = N.generalisation(x, thm_R_imp_T)
    imp_y = instancie(gen_x, var(y))                 # (y|x)R ⇒ (y=T)   ((y|x)(x=T)=(y=T), x∉T)
    imp_z = instancie(gen_x, var(z))                 # (z|x)R ⇒ (z=T)

    Ry = subst_f(var(y), x, R)                       # (y|x)R
    Rz = subst_f(var(z), x, R)                       # (z|x)R
    hconj = N.assume(et(Ry, Rz))                     # { (y|x)R et (z|x)R }
    y_eq_T = N.modus_ponens(conjonction_elim_gauche(hconj), imp_y)   # y = T
    z_eq_T = N.modus_ponens(conjonction_elim_droite(hconj), imp_z)   # z = T
    T_eq_z = N.modus_ponens(z_eq_T, symetrie(var(z), T))             # T = z
    y_eq_z = composer_egalites(y_eq_T, T_eq_z)                       # y = z

    imp = N.loi_deduction(et(Ry, Rz), y_eq_z)        # ( (y|x)R et (z|x)R ) ⇒ (y=z)
    res = N.generalisation(z, imp)                   # (∀z)(…)   (clos ⇒ z non libre dans hyp.)
    res = N.generalisation(y, res)                   # (∀y)(∀z)(…) = relation_univoque_x(R)
    assert res.conclusion == relation_univoque_x(R, x, y, z), \
        "c45_arriere : conclusion ≠ relation_univoque_x(R, x)"
    assert res.est_clos, "c45_arriere : devrait être clos (thm_R_imp_T est clos)"
    return res


# @livre Ch.I §5.3 Def.- | E I.41 L.20-23 | PDF p.41
def relation_fonctionnelle_en_x(R, x: str, y: str | None = None,
                                z: str | None = None):
    """« Il existe un x et un seul tel que R »  (définition, E I.41 L.20-23).

    Bourbaki : « Soit R une relation de 𝒯. La relation "(∃x)R et il existe au
    plus un x tel que R" se désigne par "il existe un x et un seul tel que R".
    Si cette relation est un théorème de 𝒯, on dit que R est une RELATION
    FONCTIONNELLE en x dans 𝒯. »

    Construction VERBATIM : (∃x)R  et  relation_univoque_x(R)  (l'univocité
    E I.40 déjà déposée ci-dessus, mêmes conventions de lettres fraîches)."""
    return et(existe(x, R), relation_univoque_x(R, x, y, z))


__all__ = ["relation_univoque_x", "c45_avant", "c45_arriere",
           "relation_fonctionnelle_en_x"]
