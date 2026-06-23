"""Chapitre II — premiers théorèmes UTILISANT les axiomes A1 (extensionnalité) et A2 (paire).

On instancie les axiomes (∀-élimination) du noyau abrégé. Fidèle à Bourbaki :
A1, A2 sont les axiomes verbatim ; les théorèmes en découlent par instanciation.
"""
from __future__ import annotations

from bourbaki.logique.formule import Terme, var, egal, ou, et, appartient, equiv, pourtout
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.tactiques.tactiques_abrege import syllogisme
from bourbaki.logique.tactiques.tactiques_abrege2 import (instancie, conjonction_intro, comm_ou, comm_et,
                               projection_gauche, conjonction_elim_gauche,
                               conjonction_elim_droite, equivalence_avant,
                               equivalence_arriere, equivalence_symetrie,
                               equivalence_transitivite)
from bourbaki.logique.tactiques.tactiques_abrege_egalite import congruence_terme, composer_egalites


def _terme(t):
    """Accepte un Terme ou un nom de variable (str)."""
    return t if isinstance(t, Terme) else var(t)


def extensionnalite_appliquee(a="a", b="b"):
    """⊢ (a⊂b et b⊂a) ⇒ a=b.  Instance de A1 (a, b termes ou noms)."""
    a1 = N.axiome(E.theorie_ensembles(), E.A1)         # ⊢ (∀x)(∀y)((x⊂y et y⊂x)⇒x=y)
    return instancie(instancie(a1, _terme(a)), _terme(b))


def existence_paire(a="a", b="b"):
    """⊢ Coll_z(z=a ou z=b).  Instance de A2 : la paire {a,b} existe."""
    a2 = N.axiome(E.theorie_ensembles(), E.A2)         # ⊢ (∀x)(∀y) Coll_z(z=x ou z=y)
    return instancie(instancie(a2, var(a)), var(b))    # x:=a, y:=b


def _instance_paire(a, b, z):
    """⊢ (z ∈ {a,b}) ⇔ (z=a ou z=b)  (instance de l'axiome de la paire)."""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_PAIRE)
    return instancie(instancie(instancie(ax, a), b), z)


def appartient_paire_gauche(a="a", b="b"):
    """⊢ a ∈ {a,b}."""
    va, vb = var(a), var(b)
    c = _instance_paire(va, vb, va)                    # a∈{a,b} ⇔ (a=a ∨ a=b)
    oraa = N.modus_ponens(N.reflexivite(va), N.s2(egal(va, va), egal(va, vb)))
    return N.modus_ponens(oraa, equivalence_arriere(c))


def appartient_paire_droite(a="a", b="b"):
    """⊢ b ∈ {a,b}."""
    va, vb = var(a), var(b)
    c = _instance_paire(va, vb, vb)                    # b∈{a,b} ⇔ (b=a ∨ b=b)
    bb = N.modus_ponens(N.reflexivite(vb), N.s2(egal(vb, vb), egal(vb, va)))   # b=b∨b=a
    orba = N.modus_ponens(bb, N.s3(egal(vb, vb), egal(vb, va)))                # b=a∨b=b
    return N.modus_ponens(orba, equivalence_arriere(c))


def appartient_singleton(a="a"):
    """⊢ a ∈ {a}  ({a} = {a,a})."""
    return appartient_paire_gauche(a, a)


def vide_sans_element(a="a"):
    """⊢ ¬(a ∈ ∅)."""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_VIDE)   # (∀z)¬(z∈∅)
    return instancie(ax, var(a))


def egalite_par_extension(thm_u, thm_v, tu, tv, x="z"):
    """De ⊢(∀x)(x∈tu ⇔ R) et ⊢(∀x)(x∈tv ⇔ R), déduire ⊢ tu=tv (mêmes R)."""
    euv = equivalence_transitivite(instancie(thm_u, var(x)),
                                   equivalence_symetrie(instancie(thm_v, var(x))))
    incl_uv = N.generalisation(x, equivalence_avant(euv))
    incl_vu = N.generalisation(x, equivalence_arriere(euv))
    ext = extensionnalite_appliquee(_terme(tu), _terme(tv))
    return N.modus_ponens(conjonction_intro(incl_uv, incl_vu), ext)


def commutativite_paire(a="a", b="b"):
    """⊢ {a,b} = {b,a}."""
    va, vb, vz = var(a), var(b), var("z")
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_PAIRE)
    char_ab = instancie(instancie(ax, va), vb)          # (∀z)(z∈{a,b} ⇔ (z=a∨z=b))
    char_ba0 = instancie(instancie(ax, vb), va)         # (∀z)(z∈{b,a} ⇔ (z=b∨z=a))
    # convertir char_ba0 vers R = (z=a ∨ z=b)
    eba = equivalence_transitivite(instancie(char_ba0, vz),
                                   comm_ou(egal(vz, vb), egal(vz, va)))  # z∈{b,a} ⇔ (z=a∨z=b)
    char_ba = N.generalisation("z", eba)
    return egalite_par_extension(char_ab, char_ba, E.paire(va, vb), E.paire(vb, va))


def _instance_reunion(a, b, z):
    """⊢ (z ∈ a∪b) ⇔ (z∈a ou z∈b)."""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_REUNION)
    return instancie(instancie(instancie(ax, a), b), z)


def inclusion_reunion_gauche(a="a", b="b"):
    """⊢ a ⊂ (a∪b)."""
    va, vb, vz = var(a), var(b), var("z")
    c = _instance_reunion(va, vb, vz)                   # z∈a∪b ⇔ (z∈a ∨ z∈b)
    s2 = N.s2(appartient(vz, va), appartient(vz, vb))   # z∈a ⇒ (z∈a ∨ z∈b)
    imp = syllogisme(s2, equivalence_arriere(c))        # z∈a ⇒ z∈a∪b
    return N.generalisation("z", imp)                   # ⊢ a ⊂ (a∪b)


def commutativite_reunion(a="a", b="b"):
    """⊢ (a∪b) = (b∪a)."""
    va, vb, vz = var(a), var(b), var("z")
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_REUNION)
    char_ab = instancie(instancie(ax, va), vb)          # z∈a∪b ⇔ (z∈a ∨ z∈b)
    char_ba0 = instancie(instancie(ax, vb), va)         # z∈b∪a ⇔ (z∈b ∨ z∈a)
    eba = equivalence_transitivite(instancie(char_ba0, vz),
                                   comm_ou(appartient(vz, vb), appartient(vz, va)))
    char_ba = N.generalisation("z", eba)
    return egalite_par_extension(char_ab, char_ba, E.reunion(va, vb), E.reunion(vb, va))


def _instance_intersection(a, b, z):
    """⊢ (z ∈ a∩b) ⇔ (z∈a et z∈b)."""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_INTER)
    return instancie(instancie(instancie(ax, a), b), z)


def inclusion_intersection_gauche(a="a", b="b"):
    """⊢ a∩b ⊂ a."""
    va, vb, vz = var(a), var(b), var("z")
    c = _instance_intersection(va, vb, vz)              # z∈a∩b ⇔ (z∈a et z∈b)
    proj = projection_gauche(appartient(vz, va), appartient(vz, vb))  # (z∈a et z∈b) ⇒ z∈a
    imp = syllogisme(equivalence_avant(c), proj)        # z∈a∩b ⇒ z∈a
    return N.generalisation("z", imp)                   # ⊢ a∩b ⊂ a


def commutativite_intersection(a="a", b="b"):
    """⊢ (a∩b) = (b∩a)."""
    va, vb, vz = var(a), var(b), var("z")
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_INTER)
    char_ab = instancie(instancie(ax, va), vb)          # z∈a∩b ⇔ (z∈a et z∈b)
    char_ba0 = instancie(instancie(ax, vb), va)         # z∈b∩a ⇔ (z∈b et z∈a)
    eba = equivalence_transitivite(instancie(char_ba0, vz),
                                   comm_et(appartient(vz, vb), appartient(vz, va)))
    char_ba = N.generalisation("z", eba)
    return egalite_par_extension(char_ab, char_ba, E.intersection(va, vb), E.intersection(vb, va))


def couple_egal_si_composantes(x="x", y="y", xp="xp", yp="yp"):
    """⊢ (x=x' et y=y') ⇒ (x,y)=(x',y').  (sens facile de la Proposition 1, E.II.30.)

    Par congruence de = (C44) appliquée à chaque coordonnée, puis transitivité.
    """
    vx, vy, vxp, vyp = var(x), var(y), var(xp), var(yp)
    w = var("w")
    hyp = et(egal(vx, vxp), egal(vy, vyp))
    h = N.assume(hyp)
    exx = conjonction_elim_gauche(h)                    # x = x'
    eyy = conjonction_elim_droite(h)                    # y = y'
    # (x,y) = (x',y) : congruence sur la 1ʳᵉ coordonnée
    cong1 = congruence_terme(vx, vxp, E.couple(w, vy))  # (x=x') ⇒ ((x,y)=(x',y))
    e1 = N.modus_ponens(exx, cong1)
    # (x',y) = (x',y') : congruence sur la 2ᵉ coordonnée
    cong2 = congruence_terme(vy, vyp, E.couple(vxp, w)) # (y=y') ⇒ ((x',y)=(x',y'))
    e2 = N.modus_ponens(eyy, cong2)
    couple_eq = composer_egalites(e1, e2)               # (x,y) = (x',y')
    return N.loi_deduction(hyp, couple_eq)


def unicite_par_extension(u="u", v="v", R=None, x="z"):
    """{(∀x)(x∈u ⇔ R), (∀x)(x∈v ⇔ R)} ⊢ u = v.  (unicité par extensionnalité.)

    Cœur de l'unicité d'un ensemble défini par une propriété (C48 + A1) :
    deux ensembles ayant les mêmes éléments sont égaux.
    """
    if R is None:                                    # défaut : la paire {a,b}
        R = ou(egal(var(x), var("a")), egal(var(x), var("b")))
    vu, vv, vx = var(u), var(v), var(x)
    h1 = N.assume(pourtout(x, equiv(appartient(vx, vu), R)))   # u a pour éléments R
    h2 = N.assume(pourtout(x, equiv(appartient(vx, vv), R)))   # v a pour éléments R
    euv = equivalence_transitivite(instancie(h1, vx),          # (x∈u)⇔(x∈v)
                                   equivalence_symetrie(instancie(h2, vx)))
    incl_uv = N.generalisation(x, equivalence_avant(euv))      # u ⊂ v
    incl_vu = N.generalisation(x, equivalence_arriere(euv))    # v ⊂ u
    ext = extensionnalite_appliquee(u, v)                      # (u⊂v et v⊂u)⇒u=v
    return N.modus_ponens(conjonction_intro(incl_uv, incl_vu), ext)   # ⊢ u=v


def unicite_paire(a="a", b="b", u="u", v="v"):
    """{u est la paire {a,b}, v est la paire {a,b}} ⊢ u=v. (la paire est unique.)"""
    R = ou(egal(var("z"), var(a)), egal(var("z"), var(b)))
    return unicite_par_extension(u, v, R)


__all__ = ["extensionnalite_appliquee", "existence_paire",
           "egalite_par_extension", "unicite_par_extension", "unicite_paire",
           "commutativite_paire", "appartient_paire_gauche", "appartient_paire_droite",
           "appartient_singleton", "vide_sans_element",
           "inclusion_reunion_gauche", "commutativite_reunion",
           "inclusion_intersection_gauche", "commutativite_intersection",
           "couple_egal_si_composantes"]
