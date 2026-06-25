"""Chapitre II — premiers théorèmes UTILISANT les axiomes A1 (extensionnalité) et A2 (paire).

On instancie les axiomes (∀-élimination) du noyau abrégé. Fidèle à Bourbaki :
A1, A2 sont les axiomes verbatim ; les théorèmes en découlent par instanciation.
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (Terme, var, tau, egal, ou, et, non, impl, appartient, equiv,
                     pourtout, inclus, coll)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege import syllogisme
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (instancie, conjonction_intro,
                               comm_ou, comm_et, contraposition,
                               projection_gauche, conjonction_elim_gauche,
                               conjonction_elim_droite, equivalence_avant,
                               equivalence_arriere, equivalence_symetrie,
                               equivalence_transitivite)
from bourbaki.logique.i_4_egalitaires.tactiques_abrege_egalite import congruence_terme, composer_egalites


def _terme(t):
    """Accepte un Terme ou un nom de variable (str)."""
    return t if isinstance(t, Terme) else var(t)


# @livre Ch.II §1.3 Ax.A1 | E II.3 L.1-2 | PDF p.54
def extensionnalite_appliquee(a="a", b="b"):
    """⊢ (a⊂b et b⊂a) ⇒ a=b.  Instance de A1 (a, b termes ou noms)."""
    a1 = N.axiome(E.theorie_ensembles(), E.A1)         # ⊢ (∀x)(∀y)((x⊂y et y⊂x)⇒x=y)
    return instancie(instancie(a1, _terme(a)), _terme(b))


# @livre Ch.II §1.5 Ax.A2 | E II.4 L.16-16 | PDF p.55
def existence_paire(a="a", b="b"):
    """⊢ Coll_z(z=a ou z=b).  Instance de A2 : la paire {a,b} existe."""
    a2 = N.axiome(E.theorie_ensembles(), E.A2)         # ⊢ (∀x)(∀y) Coll_z(z=x ou z=y)
    return instancie(instancie(a2, var(a)), var(b))    # x:=a, y:=b


def _instance_paire(a, b, z):
    """⊢ (z ∈ {a,b}) ⇔ (z=a ou z=b)  (instance de l'axiome de la paire)."""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_PAIRE)
    return instancie(instancie(instancie(ax, a), b), z)


# @livre Ch.II §1.5 Def.2 | E II.4 L.21-22 | PDF p.55
def appartient_paire_gauche(a="a", b="b"):
    """⊢ a ∈ {a,b}."""
    va, vb = var(a), var(b)
    c = _instance_paire(va, vb, va)                    # a∈{a,b} ⇔ (a=a ∨ a=b)
    oraa = N.modus_ponens(N.reflexivite(va), N.s2(egal(va, va), egal(va, vb)))
    return N.modus_ponens(oraa, equivalence_arriere(c))


# @livre Ch.II §1.5 Def.2 | E II.4 L.21-22 | PDF p.55
def appartient_paire_droite(a="a", b="b"):
    """⊢ b ∈ {a,b}."""
    va, vb = var(a), var(b)
    c = _instance_paire(va, vb, vb)                    # b∈{a,b} ⇔ (b=a ∨ b=b)
    bb = N.modus_ponens(N.reflexivite(vb), N.s2(egal(vb, vb), egal(vb, va)))   # b=b∨b=a
    orba = N.modus_ponens(bb, N.s3(egal(vb, vb), egal(vb, va)))                # b=a∨b=b
    return N.modus_ponens(orba, equivalence_arriere(c))


# @livre Ch.II §1.5 Def.2 | E II.4 L.27-29 | PDF p.55
def appartient_singleton(a="a"):
    """⊢ a ∈ {a}  ({a} = {a,a})."""
    return appartient_paire_gauche(a, a)


# @livre Ch.II §1.7 Th.1 | E II.6 L.30-30 | PDF p.57
def vide_sans_element(a="a"):
    """⊢ ¬(a ∈ ∅)."""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_VIDE)   # (∀z)¬(z∈∅)
    return instancie(ax, var(a))


# @livre Ch.II §1.4 Crit.C48 | E II.3 L.8-15 | PDF p.54
def egalite_par_extension(thm_u, thm_v, tu, tv, x="z"):
    """De ⊢(∀x)(x∈tu ⇔ R) et ⊢(∀x)(x∈tv ⇔ R), déduire ⊢ tu=tv (mêmes R)."""
    euv = equivalence_transitivite(instancie(thm_u, var(x)),
                                   equivalence_symetrie(instancie(thm_v, var(x))))
    incl_uv = N.generalisation(x, equivalence_avant(euv))
    incl_vu = N.generalisation(x, equivalence_arriere(euv))
    ext = extensionnalite_appliquee(_terme(tu), _terme(tv))
    return N.modus_ponens(conjonction_intro(incl_uv, incl_vu), ext)


# @livre Ch.II §1.5 Def.2 | E II.4 L.21-22 | PDF p.55
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


# @livre Ch.R §1.14 Prop.(7) | E.R.4 L.26-26 | PDF p.307
def inclusion_reunion_gauche(a="a", b="b"):
    """⊢ a ⊂ (a∪b)."""
    va, vb, vz = var(a), var(b), var("z")
    c = _instance_reunion(va, vb, vz)                   # z∈a∪b ⇔ (z∈a ∨ z∈b)
    s2 = N.s2(appartient(vz, va), appartient(vz, vb))   # z∈a ⇒ (z∈a ∨ z∈b)
    imp = syllogisme(s2, equivalence_arriere(c))        # z∈a ⇒ z∈a∪b
    return N.generalisation("z", imp)                   # ⊢ a ⊂ (a∪b)


# @livre Ch.R §1.14 Prop.(6) | E.R.4 L.25-25 | PDF p.307
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


# @livre Ch.R §1.14 Prop.(7) | E.R.4 L.26-26 | PDF p.307
def inclusion_intersection_gauche(a="a", b="b"):
    """⊢ a∩b ⊂ a."""
    va, vb, vz = var(a), var(b), var("z")
    c = _instance_intersection(va, vb, vz)              # z∈a∩b ⇔ (z∈a et z∈b)
    proj = projection_gauche(appartient(vz, va), appartient(vz, vb))  # (z∈a et z∈b) ⇒ z∈a
    imp = syllogisme(equivalence_avant(c), proj)        # z∈a∩b ⇒ z∈a
    return N.generalisation("z", imp)                   # ⊢ a∩b ⊂ a


# @livre Ch.R §1.14 Prop.(6) | E.R.4 L.25-25 | PDF p.307
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


# @livre Ch.II §2.1 Prop.1 | E II.7 L.3-4 | PDF p.58
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


# @livre Ch.II §1.4 Crit.C48 | E II.3 L.8-15 | PDF p.54
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


# @livre Ch.II §1.5 Def.2 | E II.4 L.19-20 | PDF p.55
def unicite_paire(a="a", b="b", u="u", v="v"):
    """{u est la paire {a,b}, v est la paire {a,b}} ⊢ u=v. (la paire est unique.)"""
    R = ou(egal(var("z"), var(a)), egal(var("z"), var(b)))
    return unicite_par_extension(u, v, R)


def _singleton_membre(a, c):
    """⊢ (a ∈ {c}) ⇔ (a = c).  (re-démontré localement — ii_2 importe ii_1.)

    {c} = {c,c} : instance de l'axiome de la paire + idempotence de ∨ (S1/S2).
    """
    eq = egal(a, c)
    inst = _instance_paire(c, c, a)                    # (a∈{c,c}) ⇔ (a=c ∨ a=c)
    idem = conjonction_intro(N.s1(eq), N.s2(eq, eq))   # (a=c ∨ a=c) ⇔ (a=c)
    return equivalence_transitivite(inst, idem)        # (a∈{c}) ⇔ (a=c)


# @livre Ch.II §1.5 Def.2 | E II.4 L.29-29 | PDF p.55
def appartient_singleton_inclus(x="x", X="X"):
    """⊢ (x ∈ X) ⇔ ({x} ⊂ X).  (E.II.4 : « x∈X est équivalente à {x}⊂X ».)

    ⇐ : de {x}⊂X = (∀z)(z∈{x}⇒z∈X), instancier z:=x ; comme ⊢ x∈{x}, MP ⇒ x∈X.
    ⇒ : de x∈X, prouver (∀z)(z∈{x}⇒z∈X) : pour z, supposer z∈{x} ; via (z∈{x}⇔z=x)
        on tire z=x, puis par S6/Leibniz (z=x ⇒ ((z∈X)⇔(x∈X))) on transporte x∈X
        en z∈X ; décharger ⇒ (z∈{x}⇒z∈X) ; généraliser z ⇒ {x}⊂X.
    """
    vx, vX, vz = var(x), var(X), var("z")
    sx = E.singleton(vx)
    incl = inclus(sx, vX)                               # {x} ⊂ X = (∀z)(z∈{x}⇒z∈X)

    # ── sens ⇐ : {x}⊂X ⇒ x∈X ────────────────────────────────────────────────
    h_incl = N.assume(incl)
    inst_x = instancie(h_incl, vx)                     # {H} ⊢ (x∈{x} ⇒ x∈X)
    x_dans_X = N.modus_ponens(appartient_singleton(x), inst_x)  # {H} ⊢ x∈X
    sens_arriere = N.loi_deduction(incl, x_dans_X)     # ⊢ ({x}⊂X) ⇒ (x∈X)

    # ── sens ⇒ : x∈X ⇒ {x}⊂X ────────────────────────────────────────────────
    h_xX = N.assume(appartient(vx, vX))                # x∈X
    h_zx = N.assume(appartient(vz, sx))                # z∈{x}
    z_eg_x = N.modus_ponens(h_zx, equivalence_avant(_singleton_membre(vz, vx)))  # z=x
    leib = N.s6(vz, vx, "w", appartient(var("w"), vX)) # (z=x) ⇒ ((z∈X) ⇔ (x∈X))
    eq_zx = N.modus_ponens(z_eg_x, leib)               # (z∈X) ⇔ (x∈X)
    z_dans_X = N.modus_ponens(h_xX, equivalence_arriere(eq_zx))  # {x∈X, z∈{x}} ⊢ z∈X
    imp_z = N.loi_deduction(appartient(vz, sx), z_dans_X)        # {x∈X} ⊢ (z∈{x}⇒z∈X)
    gen = N.generalisation("z", imp_z)                 # {x∈X} ⊢ (∀z)(z∈{x}⇒z∈X) = {x}⊂X
    sens_avant = N.loi_deduction(appartient(vx, vX), gen)        # ⊢ (x∈X) ⇒ ({x}⊂X)

    return conjonction_intro(sens_avant, sens_arriere)  # ⊢ (x∈X) ⇔ ({x}⊂X)


# @livre Ch.II §1.4 Ex.2 | E II.3 L.30-31 | PDF p.54
def non_collectivisante_appartenance_propre(x="x"):
    """⊢ ¬ Coll_x(x ∉ x).  (E.II.3, n°4 : la relation x∉x n'est pas collectivisante.)

    Évitement bourbakiste du paradoxe de Russell (PAS d'« ensemble de Russell »).
    Par l'absurde : on suppose H = Coll_x(¬(x∈x)) = (∃y)(∀x)(x∈y ⇔ ¬(x∈x)).
    Témoin y0 = τy(...) (existe_temoin) ; instancier x:=y0 donne l'équivalence
    paradoxale (y0∈y0) ⇔ ¬(y0∈y0).  Le lemme propositionnel ⊢ ¬(P⇔¬P) (tautologie)
    fournit la contradiction ; on décharge H ⇒ ⊢ ¬H.  La conclusion ne contient pas
    y0 (témoin éliminé), donc la preuve est CLOSE.
    """
    f = non(appartient(var(x), var(x)))                # ¬(x∈x)
    H = coll(x, f)                                      # (∃y)(∀x)(x∈y ⇔ ¬(x∈x))
    y = H.lieur                                         # variable-témoin liée ('y')
    corps = H.sous[0]                                   # (∀x)(x∈y ⇔ ¬(x∈x))

    # existe_temoin : ⊢ (∃y)corps ⇒ (τy(corps)|y)corps  (témoin canonique t0 = τy(corps))
    h_H = N.assume(H)
    inst_corps = N.modus_ponens(h_H, N.existe_temoin(corps, y))  # {H} ⊢ (∀x)(x∈t0 ⇔ ¬(x∈x))
    t0 = tau(y, corps)                                 # le témoin τy(corps)
    equ = instancie(inst_corps, t0)                    # {H} ⊢ (t0∈t0) ⇔ ¬(t0∈t0)
    P = appartient(t0, t0)                             # P := t0∈t0
    return _non_equiv_negation(P, equ, H)              # ⊢ ¬H  (réduction à l'absurde)


def _non_equiv_negation(P, thm_para, H):
    """De {H} ⊢ (P ⇔ ¬P), déduire ⊢ ¬H.  (lemme ⊢ ¬(P⇔¬P) appliqué sous H.)

    Sous H : P⇒¬P (avant) et ¬P⇒P (arrière).  De P⇒¬P = ¬P∨¬P, S1 ⇒ {H}⊢¬P ;
    puis ¬P⇒P ⇒ {H}⊢P.  On décharge : ⊢ H⇒¬P et ⊢ H⇒P ; contraposée + syllogisme
    donnent ⊢ H⇒¬H = ¬H∨¬H, et S1 ⇒ ⊢ ¬H.
    """
    p_imp_np = equivalence_avant(thm_para)             # {H} ⊢ P ⇒ ¬P  = ¬P ∨ ¬P
    np = N.modus_ponens(p_imp_np, N.s1(non(P)))        # {H} ⊢ ¬P
    p = N.modus_ponens(np, equivalence_arriere(thm_para))   # {H} ⊢ P
    H_imp_p = N.loi_deduction(H, p)                    # ⊢ H ⇒ P
    H_imp_np = N.loi_deduction(H, np)                  # ⊢ H ⇒ ¬P
    np_imp_nH = contraposition(H_imp_p)                # ⊢ ¬P ⇒ ¬H
    H_imp_nH = syllogisme(H_imp_np, np_imp_nH)         # ⊢ H ⇒ ¬H  = ¬H ∨ ¬H
    return N.modus_ponens(H_imp_nH, N.s1(non(H)))      # ⊢ ¬H


__all__ = ["extensionnalite_appliquee", "existence_paire",
           "egalite_par_extension", "unicite_par_extension", "unicite_paire",
           "commutativite_paire", "appartient_paire_gauche", "appartient_paire_droite",
           "appartient_singleton", "vide_sans_element",
           "inclusion_reunion_gauche", "commutativite_reunion",
           "inclusion_intersection_gauche", "commutativite_intersection",
           "couple_egal_si_composantes",
           "appartient_singleton_inclus", "non_collectivisante_appartenance_propre"]
