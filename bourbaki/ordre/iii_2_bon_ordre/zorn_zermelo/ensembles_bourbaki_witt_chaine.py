"""Chapitre III §2 — LE VERROU de BOURBAKI–WITT : « M est une CHAÎNE ».

Module NEUF, importé depuis `ensembles_bourbaki_witt.py` (lu D'ABORD).  Il FERME
le cœur dur du Lemme 3 (point fixe sans choix) : le plus petit tour
M = ⋂{ tours } est TOTALEMENT ORDONNÉ.  C'est la PREUVE DE WITT par « éléments
extrêmes » (deux tours emboîtés), JAMAIS postulée.

NOTATIONS d'ordre (graphe G d'ordre sur E) :
    x ≤ y  :=  (x,y)∈G                         [_le]
    x < y  :=  ((x,y)∈G  et  x≠y)              [_lt]

HYPOTHÈSES DE TRAVAIL (portées explicitement, déchargées comme dans
`point_fixe_de_sup` — JAMAIS postulées) : antisymétrie(G), transitivité(G),
inflationnaire(G,E,p), a∈E plus petit élément de E, E chaîne-complet.  Toute la
construction (M, tour, sup) vit relativement à ces hypothèses structurelles.

DÉFINITION CLÉ — point EXTRÊME (Bourbaki–Witt) :
    est_extreme(c) := (∀x)( x∈M ⇒ ( x<c ⇒ p(x) ≤ c ) ).
« c n'est strictement entre AUCUN x et p(x). »

ÉTAPES (chacune sauvée + testée en isolé ; clé .est_clos vérifiée) :
  1. M_c := {x∈M | x≤c OU p(c)≤x} est un TOUR sous est_extreme(c).
  2. M_c = M  ⇒  (∀x∈M) x≤c OU c≤x  (c comparable à tout x).
  3. C := {c∈M | est_extreme(c)} est un TOUR.
  4. C = M  ⇒  TOUT c∈M est extrême.
  5. M_est_une_chaine : totalement_ordonne(G,M)  [LE THÉORÈME VISÉ].
  6. bourbaki_witt : point fixe p(s)=s (s = sup de M, plus grand élément).
  7. zorn_via_bw   : Zorn ⇐ Bourbaki–Witt + τ.

Les termes M_c et C sont des INTERSECTIONS/sélections collectivisantes (S8+A1),
introduites comme TERMES + axiomes DÉFINITIONNELS en théories DÉDIÉES (motif
`axiome_M`/`axiome_D`).  theorie_ensembles() reste INCHANGÉE = 22.
"""
from __future__ import annotations

from bourbaki.logique.formule import (
    Terme, var, egal, et, ou, non, impl, equiv, appartient, existe, pourtout, inclus,
)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.logique.tactiques.tactiques_abrege import syllogisme, a_implique_a
from bourbaki.logique.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    projection_gauche, projection_droite, contraposition, cas, tiers_exclu,
    equivalence_avant, equivalence_arriere, instancie, instanciation_en_x,
    comm_ou, demorgan_et,
)
from bourbaki.logique.tactiques.tactiques_abrege_quantif import (
    monotonie_existe, existe_elimination,
)
from bourbaki.logique.tactiques.tactiques_abrege_egalite import symetrie as _sym
from bourbaki.ordre.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_relation import (
    est_ordre, reflexivite_sur, antisymetrie, transitivite_rel, totalement_ordonne,
    majorant, borne_superieure, plus_grand_element, plus_petit_element,
)
from bourbaki.ordre.iii_2_bon_ordre.zorn_zermelo.ensembles_zorn import chaine
from bourbaki.ordre.iii_2_bon_ordre.zorn_zermelo.ensembles_bourbaki_witt import (
    pval, inflationnaire, application_dans, chaine_complet,
    est_tour, M, M_membre, M_inclus_E, M_inclus, a_dans_M, M_clos_p, M_clos_sup,
    p_de_sup_inferieur, point_fixe_de_sup, M_inclus_terme,
    bourbaki_witt, M_est_une_chaine as _M_chaine_enonce, zorn_via_bw,
)


# Trou de substitution Leibniz (S6) GARANTI FRAIS : ne collisionne avec aucune
# lettre/terme de la preuve (notamment pas avec « w », « s », « c », …).
_H = "hole_leibniz"


def _terme(t):
    return t if isinstance(t, Terme) else var(t)


def _le(x, y, G):
    """Formule « x ≤ y » := (x,y)∈G."""
    return appartient(E.couple(_terme(x), _terme(y)), _terme(G))


def _lt(x, y, G):
    """Formule « x < y » := ((x,y)∈G et x≠y)."""
    return et(_le(x, y, G), non(egal(_terme(x), _terme(y))))


def _cut(thm, hyp, preuve_hyp):
    """De Γ∪{H}⊢C et Δ⊢H, déduit Γ∪Δ⊢C (décharge de H puis MP)."""
    return N.modus_ponens(preuve_hyp, N.loi_deduction(hyp, thm))


def _inclus_refl(t):
    """⊢ t⊂t  pour un TERME t  (réflexivité de l'inclusion, instanciée)."""
    from bourbaki.logique.tactiques.tactiques_abrege import inclusion_reflexive
    th = inclusion_reflexive("_r")                            # _r⊂_r
    return instancie(N.generalisation("_r", th), _terme(t))   # t⊂t


def _incl_trans(a, b, c, ab, bc):
    """De ⊢ a⊂b [ab] et ⊢ b⊂c [bc] (a,b,c TERMES), déduit ⊢ a⊂c.

    Binders set-variables GARANTIS FRAIS (« _i1/_i2/_i3 ») : ne collisionnent jamais
    avec a,b,c (qui peuvent contenir var('u'/'v'/'w') quand l'élément d'un M_c/Cext
    porte un de ces noms)."""
    from bourbaki.logique.tactiques.tactiques_abrege2 import inclusion_transitive
    th = inclusion_transitive("_i1", "_i2", "_i3")
    for nm, tm in (("_i1", _terme(a)), ("_i2", _terme(b)), ("_i3", _terme(c))):
        th = instancie(N.generalisation(nm, th), tm)
    return N.modus_ponens(conjonction_intro(ab, bc), th)


# ── outillage d'ORDRE : faits déduits des hypothèses structurelles ────────────
#
# On porte chaque hypothèse structurelle (antisym/trans/inflationnaire) comme une
# hypothèse ASSUMÉE, déchargée et VÉRIFIÉE par les tests (motif point_fixe_de_sup).
# Ces helpers RENVOIENT directement un Theoreme « (faits) ⊢ conclusion ».

def _trans(G, x, y, z, hxy, hyz, vx="x", vy="y", vz="z"):
    """{ transitivite_rel(G), (x,y)∈G [hxy], (y,z)∈G [hyz] } ⊢ (x,z)∈G."""
    Ht = N.assume(transitivite_rel(G, vx, vy, vz))             # (∀xyz)(((x,y) et (y,z))⇒(x,z))
    inst = instancie(instancie(instancie(Ht, _terme(x)), _terme(y)), _terme(z))
    return N.modus_ponens(conjonction_intro(hxy, hyz), inst)   # (x,z)∈G


def _antisym(G, x, y, hxy, hyx, vx="x", vy="y"):
    """{ antisymetrie(G), (x,y)∈G [hxy], (y,x)∈G [hyx] } ⊢ x=y."""
    Ha = N.assume(antisymetrie(G, vx, vy))
    inst = instancie(instancie(Ha, _terme(x)), _terme(y))      # ((x,y) et (y,x))⇒x=y
    return N.modus_ponens(conjonction_intro(hxy, hyx), inst)   # x=y


def _inflat(G, E_set, p, x, hxE, vx="x"):
    """{ inflationnaire(G,E,p), x∈E [hxE] } ⊢ (x,p(x))∈G."""
    Hi = N.assume(inflationnaire(G, E_set, p, vx))             # (∀x)(x∈E⇒(x,p(x))∈G)
    inst = instancie(Hi, _terme(x))                            # x∈E⇒(x,p(x))∈G
    return N.modus_ponens(hxE, inst)                           # (x,p(x))∈G


def _refl(G, E_set, x, hxE, vx="x"):
    """{ reflexivite_sur(G,E), x∈E [hxE] } ⊢ (x,x)∈G."""
    Hr = N.assume(reflexivite_sur(G, E_set, vx))               # (∀x)(x∈E⇒(x,x)∈G)
    inst = instancie(Hr, _terme(x))                            # x∈E⇒(x,x)∈G
    return N.modus_ponens(hxE, inst)                           # (x,x)∈G


def _app_dans(E_set, p, x, hxE, vx="x"):
    """{ application_dans(E,p), x∈E [hxE] } ⊢ p(x)∈E."""
    Hd = N.assume(application_dans(E_set, p, vx))              # (∀x)(x∈E⇒p(x)∈E)
    return N.modus_ponens(hxE, instancie(Hd, _terme(x)))       # p(x)∈E


def _x_dans_E_de_M(G, E_set, p, a, x, hxM):
    """{ x∈M [hxM] } ⊢ x∈E   (via M⊂E = (∀z)(z∈M⇒z∈E), instancié en x)."""
    incl = M_inclus_E_terme(G, E_set, p, a)                    # M⊂E
    inst = instancie(incl, _terme(x))                          # x∈M⇒x∈E
    return N.modus_ponens(hxM, inst)                           # x∈E


def M_inclus_E_terme(G, E_set, p, a):
    """⊢ M ⊂ E  pour des TERMES G,E,p,a quelconques (forme (∀z)(z∈M⇒z∈E))."""
    th = M_inclus_E("G", "E", "p", "a")
    for nm, tm in (("G", G), ("E", E_set), ("p", p), ("a", a)):
        th = instancie(N.generalisation(nm, th), tm)
    return th


def _M_clos_p_terme(G, E_set, p, a, x):
    """⊢ (p(x)∈E) ⇒ (x∈M ⇒ p(x)∈M)  pour des TERMES quelconques  (forme CLOSE).

    On DÉCHARGE d'abord la résiduelle p(u)∈E de M_clos_p pour obtenir un théorème
    CLOS, on généralise/instancie aux termes, sans buter sur « E libre »."""
    th = M_clos_p("G", "E", "p", "a", "u")                   # (u∈M⇒p(u)∈M)  [p(u)∈E]
    th = N.loi_deduction(appartient(pval(var("p"), var("u")), var("E")), th)  # (p(u)∈E)⇒(u∈M⇒p(u)∈M)  CLOS
    for nm, tm in (("G", G), ("E", E_set), ("p", p), ("a", a), ("u", x)):
        th = instancie(N.generalisation(nm, th), tm)
    return th                                                # (p(x)∈E)⇒(x∈M⇒p(x)∈M)


def _px_dans_M(G, E_set, p, a, x, hxM):
    """{ application_dans(E,p), x∈M [hxM] } ⊢ p(x)∈M.

    Compose : x∈M⊂E ⇒ x∈E ⇒ p(x)∈E (application_dans) ⇒ décharge la résiduelle
    p(x)∈E de M_clos_p ⇒ p(x)∈M."""
    vG, vE, vp, va = _terme(G), _terme(E_set), _terme(p), _terme(a)
    xE = _x_dans_E_de_M(vG, vE, vp, va, x, hxM)               # x∈E
    pxE = _app_dans(vE, vp, x, xE)                            # p(x)∈E
    clos = _M_clos_p_terme(vG, vE, vp, va, x)                 # (p(x)∈E)⇒(x∈M⇒p(x)∈M)
    clos = N.modus_ponens(pxE, clos)                         # (x∈M⇒p(x)∈M)  [appl_dans, x∈M…]
    return N.modus_ponens(hxM, clos)                          # p(x)∈M


def _disj_clos_p(G, E_set, p, a, c, x, hxM, hdisj_x):
    """Cœur de la clôture par p de M_c : sous {est_extreme(c), c∈E, struct…},
    de ⊢ x∈M [hxM] et ⊢ (x≤c OU p(c)≤x) [hdisj_x] déduit ⊢ (p(x)≤c OU p(c)≤p(x))."""
    vG, vE, vp, va, vc = _terme(G), _terme(E_set), _terme(p), _terme(a), _terme(c)
    px, pc = pval(vp, x), pval(vp, vc)
    but = ou(_le(px, vc, vG), _le(pc, px, vG))                # p(x)≤c OU p(c)≤p(x)

    # ── BRANCHE A : x≤c ───────────────────────────────────────────────────────
    Hxc = N.assume(_le(x, vc, vG))                            # (x,c)∈G
    # sous-cas x=c / x≠c
    excl = tiers_exclu(egal(_terme(x), vc))                   # (x=c) OU ¬(x=c)
    #   x=c  →  p(c)≤p(x)  (réflexivité (p(c),p(c))∈G transportée par c=x)
    Hxeqc = N.assume(egal(_terme(x), vc))                     # x=c
    cE = N.assume(appartient(vc, vE))                         # c∈E
    pcE = _app_dans(vE, vp, vc, cE)                           # p(c)∈E
    pcpc = _refl(vG, vE, pc, pcE)                             # (p(c),p(c))∈G
    c_eq_x = N.modus_ponens(Hxeqc, _sym(_terme(x), vc))       # c=x
    # Leibniz : (c=x) ⇒ ((p(c),p(c))∈G ⇔ (p(c),p(x))∈G)   trou « w » : (p(c),p(w))∈G
    phi = _le(pc, pval(vp, var(_H)), vG)
    leib = N.s6(vc, _terme(x), _H, phi)                       # (c=x)⇒(Φ(c)⇔Φ(x))
    eqv = N.modus_ponens(c_eq_x, leib)                        # (p(c),p(c))∈G ⇔ (p(c),p(x))∈G
    pcpx = N.modus_ponens(pcpc, equivalence_avant(eqv))       # (p(c),p(x))∈G = p(c)≤p(x)
    A_eq = N.loi_deduction(egal(_terme(x), vc),
                           _ou_droite(pcpx, _le(px, vc, vG)))
    # A_eq : (x=c) ⇒ (p(x)≤c OU p(c)≤p(x))   [via OU-droite : p(c)≤p(x) ⇒ but]
    #   x≠c  →  x<c  →  est_extreme ⇒ p(x)≤c
    Hxne = N.assume(non(egal(_terme(x), vc)))                 # ¬(x=c)
    x_lt_c = conjonction_intro(Hxc, Hxne)                     # x<c = ((x,c)∈G et x≠c)
    Hext = N.assume(est_extreme(vG, vE, vp, va, vc))          # (∀x)(x∈M⇒(x<c⇒p(x)≤c))
    ext_x = instancie(Hext, _terme(x))                        # x∈M⇒(x<c⇒p(x)≤c)
    px_le_c = N.modus_ponens(x_lt_c, N.modus_ponens(hxM, ext_x))   # p(x)≤c
    A_ne = N.loi_deduction(non(egal(_terme(x), vc)),
                           _ou_gauche(px_le_c, _le(pc, px, vG)))
    A = cas(excl, A_eq, A_ne)                                 # (p(x)≤c OU p(c)≤p(x))   [x≤c, …]
    branche_A = N.loi_deduction(_le(x, vc, vG), A)            # (x≤c) ⇒ but

    # ── BRANCHE B : p(c)≤x ─────────────────────────────────────────────────────
    Hpcx = N.assume(_le(pc, x, vG))                           # (p(c),x)∈G
    xE = _x_dans_E_de_M(vG, vE, vp, va, x, hxM)               # x∈E
    x_le_px = _inflat(vG, vE, vp, x, xE)                      # (x,p(x))∈G
    pc_le_px = _trans(vG, pc, x, px, Hpcx, x_le_px)           # (p(c),p(x))∈G
    B = _ou_droite(pc_le_px, _le(px, vc, vG))                 # p(x)≤c OU p(c)≤p(x)
    branche_B = N.loi_deduction(_le(pc, x, vG), B)            # (p(c)≤x) ⇒ but

    return cas(hdisj_x, branche_A, branche_B)                # but, sous {hxM, hdisj_x, …}


def Mc_clos_p(G="G", E_set="E", p="p", a="a", c="c", x="x"):
    """⊢ (∀x)( x∈M_c ⇒ p(x)∈M_c ).   (M_c close par p — propriété (T2), ÉTAPE 1.)

    HYPS portées : est_extreme(c), c∈E, application_dans(E,p), inflationnaire(G,E,p),
    reflexivite_sur(G,E), transitivite_rel(G).  (Toutes déchargées à l'assemblage.)"""
    vG, vE, vp, va, vc, vx = var(G), var(E_set), var(p), var(a), var(c), var(x)
    Mct = Mc(vG, vE, vp, va, vc)
    hxMc = N.assume(appartient(vx, Mct))                      # x∈M_c
    corps = N.modus_ponens(hxMc, equivalence_avant(_inst_Mc(vG, vE, vp, va, vc, vx)))
    xM = conjonction_elim_gauche(corps)                      # x∈M
    disj_x = conjonction_elim_droite(corps)                  # x≤c OU p(c)≤x
    # p(x)∈M
    pxM = _px_dans_M(vG, vE, vp, va, vx, xM)                 # p(x)∈M
    # disjonction pour p(x) : p(x)≤c OU p(c)≤p(x)
    disj_px = _disj_clos_p(vG, vE, vp, va, vc, vx, xM, disj_x)
    pxMc = _Mc_intro(vG, vE, vp, va, vc, pval(vp, vx), pxM, disj_px)   # p(x)∈M_c
    body = N.loi_deduction(appartient(vx, Mct), pxMc)        # x∈M_c ⇒ p(x)∈M_c
    return N.generalisation(x, body)                         # (∀x)(x∈M_c⇒p(x)∈M_c)


def _C_inclus_M(G, E_set, p, a, c, C, hC_Mc):
    """{ C⊂M_c [hC_Mc] } ⊢ C⊂M   (transitivité C⊂M_c⊂M)."""
    from bourbaki.logique.tactiques.tactiques_abrege2 import inclusion_transitive
    vG, vE, vp, va, vc = _terme(G), _terme(E_set), _terme(p), _terme(a), _terme(c)
    Mct, Mt = Mc(vG, vE, vp, va, vc), M(vG, vE, vp, va)
    McM = Mc_inclus_M_terme(vG, vE, vp, va, vc)             # M_c⊂M
    return _incl_trans(_terme(C), Mct, Mt, hC_Mc, McM)      # C⊂M


def _M_clos_sup_terme(G, E_set, p, a, C, s):
    """⊢ ((C⊂M et chaine(G,E,C)) et borne_superieure(G,C,s,E)) ⇒ s∈M  (TERMES)."""
    th = M_clos_sup("G", "E", "p", "a", "C", "s")           # CLOS
    for nm, tm in (("G", G), ("E", E_set), ("p", p), ("a", a), ("C", C), ("s", s)):
        th = instancie(N.generalisation(nm, th), tm)
    return th


def Mc_clos_sup(G="G", E_set="E", p="p", a="a", c="c", C="C", s="s",
                x="x", y="y", z="z", w="w"):
    """⊢ (∀C)( (C⊂M_c et chaine(G,E,C)) ⇒ (∀w)( borne_sup(G,C,w,E) ⇒ w∈M_c ) ).

    (M_c close par sup de chaîne — propriété (T3), ÉTAPE 1.)  HYPS : c∈E + struct.
    Branche ALL : si ∀x∈C x≤c, alors c majore C, donc s≤c (s = plus petit majorant).
    Branche NOT : sinon ∃x∈C ¬(x≤c) ; x∈M_c ⇒ p(c)≤x, et x≤s ⇒ p(c)≤s (transitivité)."""
    vG, vE, vp, va, vc = var(G), var(E_set), var(p), var(a), var(c)
    vC, vs = var(C), var(w)   # le « sup » est nommé w pour matcher _clos_par_sup
    Mct, Mt = Mc(vG, vE, vp, va, vc), M(vG, vE, vp, va)
    pc = pval(vp, vc)

    hyp1 = et(inclus(vC, Mct), chaine(vG, vE, vC, x, y, z))   # C⊂M_c et chaine
    Hh = N.assume(hyp1)
    C_Mc = conjonction_elim_gauche(Hh)                       # C⊂M_c
    chaineC = conjonction_elim_droite(Hh)                    # chaine(G,E,C)
    Hbsup = N.assume(borne_superieure(vG, vC, vs, vE, x, y))  # borne_sup(G,C,s,E)
    maj_s = conjonction_elim_gauche(Hbsup)                   # majorant(G,C,s,E)
    least = conjonction_elim_droite(Hbsup)                   # (∀y)(majorant(G,C,y,E)⇒(s,y)∈G)
    s_majfun = conjonction_elim_droite(maj_s)                # (∀x)(x∈C⇒(x,s)∈G)
    s_in_E = conjonction_elim_gauche(maj_s)                  # s∈E

    # (1) s∈M  via M_clos_sup  (C⊂M de C⊂M_c⊂M)
    C_M = _C_inclus_M(vG, vE, vp, va, vc, vC, C_Mc)          # C⊂M
    msup = _M_clos_sup_terme(vG, vE, vp, va, vC, vs)         # ((C⊂M et chaine) et bsup)⇒s∈M
    sM = N.modus_ponens(conjonction_intro(conjonction_intro(C_M, chaineC), Hbsup), msup)  # s∈M

    # (2) disjonction s≤c OU p(c)≤s   — cas sur (∀x)(x∈C⇒x≤c)
    allxc = pourtout(x, impl(appartient(var(x), vC), _le(var(x), vc, vG)))
    excl = tiers_exclu(allxc)                                # allxc OU ¬allxc

    # BRANCHE ALL : c majore C ⇒ s≤c
    Hall = N.assume(allxc)                                   # (∀x)(x∈C⇒x≤c)
    HcE = N.assume(appartient(vc, vE))                       # c∈E
    maj_c = conjonction_intro(HcE, Hall)                    # majorant(G,C,c,E)
    least_c = instancie(least, vc)                          # majorant(G,C,c,E)⇒(s,c)∈G
    s_le_c = N.modus_ponens(maj_c, least_c)                 # (s,c)∈G = s≤c
    disj_all = _ou_gauche(s_le_c, _le(pc, vs, vG))          # s≤c OU p(c)≤s
    branche_all = N.loi_deduction(allxc, disj_all)          # allxc ⇒ disj

    # BRANCHE NOT : ∃x∈C ¬(x≤c) ; témoin x ⇒ p(c)≤x≤s ⇒ p(c)≤s
    Hnot = N.assume(non(allxc))                             # ¬(∀x)(x∈C⇒x≤c)
    # ¬(∀x)R = ¬¬(∃x)¬R → (∃x)¬R   (dne)
    from bourbaki.logique.tactiques.tactiques_abrege2 import dne as _dne
    from bourbaki.logique.tactiques.tactiques_abrege_quantif import congruence_existe
    Rxc = impl(appartient(var(x), vC), _le(var(x), vc, vG))  # x∈C⇒x≤c
    ex_negR = N.modus_ponens(Hnot, _dne(existe(x, non(Rxc))))   # (∃x)¬(x∈C⇒x≤c)
    # ¬(x∈C⇒x≤c) ⇔ (x∈C et ¬(x≤c))  sous ∃
    eqv = _neg_impl_equiv(appartient(var(x), vC), _le(var(x), vc, vG))
    ex_conj = N.modus_ponens(ex_negR, equivalence_avant(congruence_existe(eqv, x)))  # (∃x)(x∈C et ¬(x≤c))
    # per-témoin : (x∈C et ¬(x≤c)) ⇒ (s≤c OU p(c)≤s)
    conj_x = et(appartient(var(x), vC), non(_le(var(x), vc, vG)))
    Hwit = N.assume(conj_x)
    xC = conjonction_elim_gauche(Hwit)                      # x∈C
    nxc = conjonction_elim_droite(Hwit)                     # ¬(x≤c)
    # x∈M_c (C⊂M_c)
    C_Mc_x = N.modus_ponens(xC, instancie(C_Mc, var(x)))    # x∈M_c
    corps_x = N.modus_ponens(C_Mc_x, equivalence_avant(_inst_Mc(vG, vE, vp, va, vc, var(x))))
    disj_x = conjonction_elim_droite(corps_x)               # x≤c OU p(c)≤x
    # ¬(x≤c) ⇒ p(c)≤x  (élimine la gauche de disj_x)
    #   disj_x = (x≤c ∨ p(c)≤x) ; avec ¬(x≤c), disjunctive syllogism → p(c)≤x
    pc_le_x = _disj_syll(disj_x, nxc)                       # p(c)≤x
    # x≤s  (s majorant de C : (∀x)(x∈C⇒(x,s)∈G))
    x_le_s = N.modus_ponens(xC, instancie(s_majfun, var(x)))  # (x,s)∈G
    pc_le_s = _trans(vG, pc, var(x), vs, pc_le_x, x_le_s)   # (p(c),s)∈G
    disj_wit = _ou_droite(pc_le_s, _le(vs, vc, vG))         # s≤c OU p(c)≤s
    wit_imp = N.loi_deduction(conj_x, disj_wit)             # (x∈C et ¬(x≤c)) ⇒ disj
    # éliminer ∃ (x non libre dans disj : disj = s≤c OU p(c)≤s)
    ex_imp = existe_elimination(wit_imp, x)                 # (∃x)(x∈C et ¬(x≤c)) ⇒ disj
    disj_not = N.modus_ponens(ex_conj, ex_imp)              # disj  [Hnot]
    branche_not = N.loi_deduction(non(allxc), disj_not)     # ¬allxc ⇒ disj

    disj_s = cas(excl, branche_all, branche_not)            # s≤c OU p(c)≤s
    sMc = _Mc_intro(vG, vE, vp, va, vc, vs, sM, disj_s)     # w∈M_c

    # recompose (∀C)( hyp1 ⇒ (∀w)( bsup(G,C,w,E) ⇒ w∈M_c ) )
    inner = N.loi_deduction(borne_superieure(vG, vC, vs, vE, x, y), sMc)  # bsup(w)⇒w∈M_c
    inner_all = N.generalisation(w, inner)                  # (∀w)(bsup(w)⇒w∈M_c)
    body = N.loi_deduction(hyp1, inner_all)                 # hyp1 ⇒ (∀w)(bsup⇒w∈M_c)
    return N.generalisation(C, body)                        # (∀C)( hyp1 ⇒ (∀w)(bsup⇒w∈M_c) )


# ── ÉTAPE 1 (assemblage) : M_c est un TOUR sous est_extreme(c) ────────────────
def Mc_est_tour(G="G", E_set="E", p="p", a="a", c="c"):
    """⊢ est_tour(G,E,p,a,M_c).   (ÉTAPE 1 — M_c est un tour admissible.)

    HYPS portées (toutes structurelles + est_extreme(c) + c∈E + a plus petit élt) :
      est_extreme(c), c∈E, a∈E, plus_petit_element(G,E,a),
      application_dans(E,p), inflationnaire(G,E,p), reflexivite_sur(G,E),
      transitivite_rel(G).
    Assemble (T0) M_c⊂E, (T1) a∈M_c, (T2) clos par p, (T3) clos par sup."""
    vG, vE, vp, va, vc = var(G), var(E_set), var(p), var(a), var(c)
    t0 = Mc_inclus_E(G, E_set, p, a, c)                     # M_c⊂E
    t1 = a_dans_Mc(G, E_set, p, a, c)                       # a∈M_c
    t2 = Mc_clos_p(G, E_set, p, a, c)                       # clos par p
    t3 = Mc_clos_sup(G, E_set, p, a, c)                     # clos par sup
    return conjonction_intro(conjonction_intro(conjonction_intro(t0, t1), t2), t3)


# ════════════════════════════════════════════════════════════════════════════
#  ÉTAPE 2 — M_c = M   ⇒   (∀x∈M) x≤c OU c≤x   (c comparable à tout x∈M)
# ════════════════════════════════════════════════════════════════════════════
def M_inclus_Mc(G="G", E_set="E", p="p", a="a", c="c"):
    """⊢ M ⊂ M_c   (sous {est_extreme(c) + struct}).

    M_c est un tour (ÉTAPE 1) et M est le PLUS PETIT tour ⇒ M⊂M_c (M_inclus)."""
    vG, vE, vp, va, vc = var(G), var(E_set), var(p), var(a), var(c)
    Mct = Mc(vG, vE, vp, va, vc)
    tour = Mc_est_tour(G, E_set, p, a, c)                   # est_tour(G,E,p,a,M_c)  [hyps]
    M_inc = M_inclus_terme(vG, vE, vp, va, Mct)            # (S tour)⇒(M⊂S)  pour S=M_c
    return N.modus_ponens(tour, M_inc)                     # M⊂M_c   [hyps de tour]


def disj_a_c(G="G", E_set="E", p="p", a="a", c="c", x="x"):
    """⊢ (∀x)( x∈M ⇒ ( x≤c OU p(c)≤x ) )   (sous {est_extreme(c), c∈E + struct}).

    Forme « membre de M_c=M » de l'ÉTAPE 2 (avant le transport p(c)≤x ↦ c≤x) ;
    réutilisée par la clôture par p et par sup de C (ÉTAPE 3)."""
    vG, vE, vp, va, vc, vx = var(G), var(E_set), var(p), var(a), var(c), var(x)
    M_Mc = M_inclus_Mc(G, E_set, p, a, c)                  # M⊂M_c
    hxM = N.assume(appartient(vx, M(vG, vE, vp, va)))      # x∈M
    xMc = N.modus_ponens(hxM, instancie(M_Mc, vx))         # x∈M_c
    corps = N.modus_ponens(xMc, equivalence_avant(_inst_Mc(vG, vE, vp, va, vc, vx)))
    disj = conjonction_elim_droite(corps)                  # x≤c OU p(c)≤x
    body = N.loi_deduction(appartient(vx, M(vG, vE, vp, va)), disj)
    return N.generalisation(x, body)                       # (∀x)(x∈M⇒(x≤c OU p(c)≤x))


def comparable_a_c(G="G", E_set="E", p="p", a="a", c="c", x="x"):
    """⊢ (∀x)( x∈M ⇒ ( x≤c OU c≤x ) )   (sous {est_extreme(c), c∈E + struct}).

    ÉTAPE 2 : de M⊂M_c, tout x∈M est dans M_c, donc x≤c OU p(c)≤x ; et p(c)≤x avec
    c≤p(c) (inflationnaire) donne c≤x (transitivité).  Donc c est COMPARABLE à tout
    élément de M."""
    vG, vE, vp, va, vc, vx = var(G), var(E_set), var(p), var(a), var(c), var(x)
    pc = pval(vp, vc)
    M_Mc = M_inclus_Mc(G, E_set, p, a, c)                  # M⊂M_c
    hxM = N.assume(appartient(vx, M(vG, vE, vp, va)))      # x∈M
    xMc = N.modus_ponens(hxM, instancie(M_Mc, vx))         # x∈M_c
    corps = N.modus_ponens(xMc, equivalence_avant(_inst_Mc(vG, vE, vp, va, vc, vx)))
    disj = conjonction_elim_droite(corps)                  # x≤c OU p(c)≤x
    but = ou(_le(vx, vc, vG), _le(vc, vx, vG))             # x≤c OU c≤x
    # branche x≤c : direct (OU-gauche)
    Hxc = N.assume(_le(vx, vc, vG))
    bA = N.loi_deduction(_le(vx, vc, vG), _ou_gauche(Hxc, _le(vc, vx, vG)))
    # branche p(c)≤x : c≤p(c) (inflat, c∈E) puis transitivité c≤p(c)≤x ⇒ c≤x
    Hpcx = N.assume(_le(pc, vx, vG))                       # (p(c),x)∈G
    HcE = N.assume(appartient(vc, vE))                     # c∈E
    c_le_pc = _inflat(vG, vE, vp, vc, HcE)                 # (c,p(c))∈G
    c_le_x = _trans(vG, vc, pc, vx, c_le_pc, Hpcx)         # (c,x)∈G
    bB = N.loi_deduction(_le(pc, vx, vG), _ou_droite(c_le_x, _le(vx, vc, vG)))
    par_cas = cas(disj, bA, bB)                            # x≤c OU c≤x
    body = N.loi_deduction(appartient(vx, M(vG, vE, vp, va)), par_cas)
    return N.generalisation(x, body)                       # (∀x)(x∈M⇒(x≤c OU c≤x))


# ════════════════════════════════════════════════════════════════════════════
#  ÉTAPE 3 — l'ensemble C des points extrêmes  := { c∈M | est_extreme(c) }
#  (TERME + axiome DÉFINITIONNEL dédié ; motif axiome_M.)
# ════════════════════════════════════════════════════════════════════════════
def Cext(G, E_set, p, a):
    """C := { c∈M | est_extreme(c) }  (l'ensemble des points EXTRÊMES de M)."""
    return E.app("bw_Cext", _terme(G), _terme(E_set), _terme(p), _terme(a))


def _corps_Cext(G, E_set, p, a, z):
    """Corps de C :  z∈M et est_extreme(z)."""
    Mt = M(_terme(G), _terme(E_set), _terme(p), _terme(a))
    return et(appartient(_terme(z), Mt), est_extreme(G, E_set, p, a, _terme(z)))


def axiome_Cext(G="G", E_set="E", p="p", a="a", z="c"):
    """⊢-schéma (∀G E p a z)( z∈C ⇔ (z∈M et est_extreme(z)) ).

    Axiome DÉFINITIONNEL de la sélection des points extrêmes (S8+A1, motif
    axiome_M).  N'altère PAS theorie_ensembles()."""
    vG, vE, vp, va, vz = var(G), var(E_set), var(p), var(a), var(z)
    return pourtout(G, pourtout(E_set, pourtout(p, pourtout(a, pourtout(z,
        equiv(appartient(vz, Cext(vG, vE, vp, va)),
              _corps_Cext(vG, vE, vp, va, vz)))))))


def theorie_Cext(G="G", E_set="E", p="p", a="a", z="c"):
    """Théorie DÉDIÉE ne contenant que l'axiome de C (E.III.2, Witt, ÉTAPE 3)."""
    return N.Theorie("Cext-Bourbaki-Witt", [axiome_Cext(G, E_set, p, a, z)])


def _inst_Cext(G, E_set, p, a, z):
    """⊢ ( z∈C ⇔ (z∈M et est_extreme(z)) )   (axiome instancié aux TERMES)."""
    ax = N.axiome(theorie_Cext(), axiome_Cext())
    for tm in (G, E_set, p, a, z):
        ax = instancie(ax, _terme(tm))
    return ax


def Cext_membre(G="G", E_set="E", p="p", a="a", z="c"):
    """⊢ ( z∈C ) ⇔ ( z∈M et est_extreme(z) )."""
    return _inst_Cext(var(G), var(E_set), var(p), var(a), var(z))


def Cext_inclus_M(G="G", E_set="E", p="p", a="a"):
    """⊢ C ⊂ M.   (sélection dans M.)"""
    vG, vE, vp, va, vz = var(G), var(E_set), var(p), var(a), var("z")
    eq = _inst_Cext(vG, vE, vp, va, vz)
    z_imp = syllogisme(equivalence_avant(eq),
                       projection_gauche(appartient(vz, M(vG, vE, vp, va)),
                                         est_extreme(vG, vE, vp, va, vz)))
    return N.generalisation("z", z_imp)                    # C⊂M


def Cext_inclus_M_terme(G, E_set, p, a):
    """⊢ C ⊂ M  pour des TERMES."""
    th = Cext_inclus_M("G", "E", "p", "a")
    for nm, tm in (("G", G), ("E", E_set), ("p", p), ("a", a)):
        th = instancie(N.generalisation(nm, th), _terme(tm))
    return th


def Cext_inclus_E(G="G", E_set="E", p="p", a="a"):
    """⊢ C ⊂ E   (C⊂M⊂E)."""
    vG, vE, vp, va = var(G), var(E_set), var(p), var(a)
    Ct, Mt = Cext(vG, vE, vp, va), M(vG, vE, vp, va)
    C_M = Cext_inclus_M(G, E_set, p, a)
    M_E = M_inclus_E(G, E_set, p, a)
    return _incl_trans(Ct, Mt, vE, C_M, M_E)               # C⊂E


def _Cext_intro(G, E_set, p, a, z, hzM, hext):
    """De ⊢ z∈M [hzM] et ⊢ est_extreme(z) [hext], déduit ⊢ z∈C."""
    corps = conjonction_intro(hzM, hext)
    return N.modus_ponens(corps, equivalence_arriere(_inst_Cext(G, E_set, p, a, z)))


def a_est_extreme(G="G", E_set="E", p="p", a="a", x="x"):
    """⊢ est_extreme(a)   (sous {antisymetrie(G), plus_petit_element(G,E,a)}).

    a est EXTRÊME par VACUITÉ : aucun x∈M ne vérifie x<a.  En effet x∈M⊂E et a est
    le plus petit élément de E ⇒ a≤x ; si en outre x<a (x≤a et x≠a), l'antisymétrie
    de (x≤a, a≤x) donne x=a, contredisant x≠a.  Donc x<a ⇒ p(x)≤a (vacuité)."""
    vG, vE, vp, va, vx = var(G), var(E_set), var(p), var(a), var(x)
    Mt = M(vG, vE, vp, va)
    hxM = N.assume(appartient(vx, Mt))                     # x∈M
    xE = _x_dans_E_de_M(vG, vE, vp, va, vx, hxM)           # x∈E
    Hppe = N.assume(plus_petit_element(vG, vE, va))         # a∈E et (∀x)(x∈E⇒(a,x)∈G)
    a_min = conjonction_elim_droite(Hppe)                  # (∀x)(x∈E⇒(a,x)∈G)
    a_le_x = N.modus_ponens(xE, instancie(a_min, vx))      # (a,x)∈G
    # x<a ⇒ p(x)≤a (vacuité)
    Hlt = N.assume(_lt(vx, va, vG))                        # (x,a)∈G et x≠a
    x_le_a = conjonction_elim_gauche(Hlt)                  # (x,a)∈G
    x_ne_a = conjonction_elim_droite(Hlt)                  # ¬(x=a)
    x_eq_a = _antisym(vG, vx, va, x_le_a, a_le_x)          # x=a
    px_le_a = _ex_falso(x_eq_a, x_ne_a, _le(pval(vp, vx), va, vG))   # p(x)≤a (ex falso)
    inner = N.loi_deduction(_lt(vx, va, vG), px_le_a)      # x<a ⇒ p(x)≤a
    body = N.loi_deduction(appartient(vx, Mt), inner)      # x∈M ⇒ (x<a ⇒ p(x)≤a)
    return N.generalisation(x, body)                       # est_extreme(a)


def a_dans_Cext(G="G", E_set="E", p="p", a="a"):
    """⊢ a∈C   (sous {a∈E, antisymetrie(G), plus_petit_element(G,E,a)}).  (T1, ÉTAPE 3.)"""
    vG, vE, vp, va = var(G), var(E_set), var(p), var(a)
    aM = a_dans_M(G, E_set, p, a)                          # a∈M  [a∈E]
    aext = a_est_extreme(G, E_set, p, a)                   # est_extreme(a)  [antisym, ppe]
    return _Cext_intro(vG, vE, vp, va, va, aM, aext)       # a∈C


def pc_est_extreme(G="G", E_set="E", p="p", a="a", c="c", x="x"):
    """⊢ est_extreme(p(c))   (sous {c∈M, est_extreme(c), c∈E + struct}).

    Pour x∈M avec x<p(c) : par ÉTAPE 2 (disj_a_c) x≤c OU p(c)≤x.
      • p(c)≤x : avec x≤p(c) (de x<p(c)), antisym ⇒ x=p(c), contredit x≠p(c). VACUITÉ.
      • x≤c, sous-cas x<c : c extrême ⇒ p(x)≤c, et c≤p(c) (inflat) ⇒ p(x)≤p(c).
      •       sous-cas x=c : p(x)=p(c), réflexivité (p(c),p(c))∈G ⇒ p(x)≤p(c)."""
    vG, vE, vp, va, vc, vx = var(G), var(E_set), var(p), var(a), var(c), var(x)
    Mt = M(vG, vE, vp, va)
    pc, px = pval(vp, vc), pval(vp, vx)
    but = _le(px, pc, vG)                                  # p(x)≤p(c)

    hxM = N.assume(appartient(vx, Mt))                     # x∈M
    Hlt = N.assume(_lt(vx, pc, vG))                        # x<p(c) = (x≤p(c) et x≠p(c))
    x_le_pc = conjonction_elim_gauche(Hlt)                 # (x,p(c))∈G
    x_ne_pc = conjonction_elim_droite(Hlt)                 # ¬(x=p(c))

    # disjonction x≤c OU p(c)≤x  (ÉTAPE 2)
    dj = disj_a_c(G, E_set, p, a, c)                       # (∀x)(x∈M⇒(x≤c OU p(c)≤x))
    disj = N.modus_ponens(hxM, instancie(dj, vx))          # x≤c OU p(c)≤x

    # BRANCHE p(c)≤x : VACUITÉ (antisym avec x≤p(c) ⇒ x=p(c), contredit x≠p(c))
    Hpcx = N.assume(_le(pc, vx, vG))                       # (p(c),x)∈G
    x_eq_pc = _antisym(vG, vx, pc, x_le_pc, Hpcx)          # x=p(c)
    bB = N.loi_deduction(_le(pc, vx, vG), _ex_falso(x_eq_pc, x_ne_pc, but))   # p(c)≤x ⇒ but

    # BRANCHE x≤c : sous-cas x=c / x<c
    Hxc = N.assume(_le(vx, vc, vG))                        # (x,c)∈G
    excl = tiers_exclu(egal(vx, vc))                       # (x=c) OU ¬(x=c)
    #   x=c : p(x)=p(c), réflexivité
    Hxeqc = N.assume(egal(vx, vc))                         # x=c
    HcE = N.assume(appartient(vc, vE))                     # c∈E
    pcE = _app_dans(vE, vp, vc, HcE)                       # p(c)∈E
    pcpc = _refl(vG, vE, pc, pcE)                          # (p(c),p(c))∈G
    c_eq_x = N.modus_ponens(Hxeqc, _sym(vx, vc))           # c=x
    phi = _le(pval(vp, var(_H)), pc, vG)                   # Φ(·) = (p(·),p(c))∈G
    leib = N.s6(vc, vx, _H, phi)                           # (c=x)⇒(Φ(c)⇔Φ(x))
    eqv = N.modus_ponens(c_eq_x, leib)                     # (p(c),p(c))∈G ⇔ (p(x),p(c))∈G
    px_le_pc_eq = N.modus_ponens(pcpc, equivalence_avant(eqv))   # (p(x),p(c))∈G
    bEq = N.loi_deduction(egal(vx, vc), px_le_pc_eq)       # (x=c) ⇒ but
    #   x<c : c extrême ⇒ p(x)≤c ; c≤p(c) (inflat) ; transitivité p(x)≤c≤p(c)
    Hxne = N.assume(non(egal(vx, vc)))                     # ¬(x=c)
    x_lt_c = conjonction_intro(Hxc, Hxne)                  # x<c
    Hcext = N.assume(est_extreme(vG, vE, vp, va, vc))      # est_extreme(c)
    cext_x = instancie(Hcext, vx)                          # x∈M⇒(x<c⇒p(x)≤c)
    px_le_c = N.modus_ponens(x_lt_c, N.modus_ponens(hxM, cext_x))   # p(x)≤c
    c_le_pc = _inflat(vG, vE, vp, vc, HcE)                 # (c,p(c))∈G
    px_le_pc = _trans(vG, px, vc, pc, px_le_c, c_le_pc)    # (p(x),p(c))∈G
    bNe = N.loi_deduction(non(egal(vx, vc)), px_le_pc)     # ¬(x=c) ⇒ but
    bA_inner = cas(excl, bEq, bNe)                         # but  [x≤c, …]
    bA = N.loi_deduction(_le(vx, vc, vG), bA_inner)        # x≤c ⇒ but

    par_cas = cas(disj, bA, bB)                            # but = p(x)≤p(c)
    inner = N.loi_deduction(_lt(vx, pc, vG), par_cas)      # x<p(c) ⇒ p(x)≤p(c)
    body = N.loi_deduction(appartient(vx, Mt), inner)      # x∈M ⇒ (x<p(c)⇒p(x)≤p(c))
    return N.generalisation(x, body)                       # est_extreme(p(c))


def Cext_clos_p(G="G", E_set="E", p="p", a="a", c="c"):
    """⊢ (∀c)( c∈C ⇒ p(c)∈C ).   (C close par p — propriété (T2), ÉTAPE 3.)

    Pour c∈C : c∈M et est_extreme(c).  Alors p(c)∈M (M close par p) et
    est_extreme(p(c)) (pc_est_extreme).  Donc p(c)∈C.  HYPS struct + est_extreme via c∈C."""
    vG, vE, vp, va, vc = var(G), var(E_set), var(p), var(a), var(c)
    Ct = Cext(vG, vE, vp, va)
    hcC = N.assume(appartient(vc, Ct))                     # c∈C
    corps = N.modus_ponens(hcC, equivalence_avant(_inst_Cext(vG, vE, vp, va, vc)))
    cM = conjonction_elim_gauche(corps)                    # c∈M
    cext = conjonction_elim_droite(corps)                  # est_extreme(c)
    cE = _x_dans_E_de_M(vG, vE, vp, va, vc, cM)            # c∈E
    # p(c)∈M
    pcM = _px_dans_M(vG, vE, vp, va, vc, cM)               # p(c)∈M
    # est_extreme(p(c)) — décharge les résiduelles est_extreme(c) et c∈E de pc_est_extreme
    pcext = pc_est_extreme(G, E_set, p, a, c)              # est_extreme(p(c))  [est_extreme(c), c∈E,…]
    pcext = _cut(pcext, est_extreme(vG, vE, vp, va, vc), cext)
    pcext = _cut(pcext, appartient(vc, vE), cE)
    pcC = _Cext_intro(vG, vE, vp, va, pval(vp, vc), pcM, pcext)   # p(c)∈C
    body = N.loi_deduction(appartient(vc, Ct), pcC)        # c∈C ⇒ p(c)∈C
    return N.generalisation(c, body)                       # (∀c)(c∈C⇒p(c)∈C)


# ── T3 de l'ÉTAPE 3 : s = sup d'une chaîne D⊂C est EXTRÊME (cœur le plus dur) ──
#
# Conventions de variables internes (toutes des STRINGS, binders distincts) :
#   D = chaîne ⊂ C ;  s = sup de D ;  x = élément testé (x∈M, x<s) ;
#   c = témoin dans D ;  cp = second témoin c′∈D ( c < c′ ).
def _comparable_dans_D(G, E_set, D, c, cp, hcD, hcpD, htot):
    """{ totalement_ordonne(G,D) [htot], c∈D [hcD], c′∈D [hcpD] } ⊢ (c≤c′ OU c′≤c)."""
    vG = _terme(G)
    comp = conjonction_elim_droite(htot)                   # (∀x∀y)((x∈D et y∈D)⇒(x≤y OU y≤x))
    inst = instancie(instancie(comp, _terme(c)), _terme(cp))
    return N.modus_ponens(conjonction_intro(hcD, hcpD), inst)   # c≤c′ OU c′≤c


def _refl_de_M(G, E_set, p, a, t, htM):
    """{ reflexivite_sur(G,E), t∈M [htM] } ⊢ (t,t)∈G   (via t∈M⊂E)."""
    vG, vE, vp, va = _terme(G), _terme(E_set), _terme(p), _terme(a)
    tE = _x_dans_E_de_M(vG, vE, vp, va, t, htM)            # t∈E
    return _refl(vG, vE, t, tE)                            # (t,t)∈G


def _applique_least(least_s, m, hmE, maj_fun_c, c_binder):
    """{ least_s : (∀y)(majorant(G,D,y,E)⇒(s,y)∈G) } : de m∈E [hmE] et
    maj_fun_c = (∀<c_binder>)(<c_binder>∈D⇒(<c_binder>,m)∈G), déduit ⊢ (s,m)∈G.

    On INSTANCIE least_s en m, on lit l'antécédent attendu (= majorant(G,D,m,E)
    avec binder canonique), et on α-renomme maj_fun_c vers ce binder pour matcher."""
    from bourbaki.logique.tactiques.tactiques_abrege import antecedent_consequent
    from bourbaki.logique.tactiques.tactiques_abrege_quantif import alpha_pour_tout
    from bourbaki.logique.tactiques.tactiques_abrege2 import _peler_pourtout
    least_m = instancie(least_s, _terme(m))                       # majorant(G,D,m,E)⇒(s,m)∈G
    maj_attendu, _ = antecedent_consequent(least_m.conclusion)
    maj_fun_attendu = conjonction_elim_droite(N.assume(maj_attendu))  # (∀@)(@∈D⇒(@,m)∈G)  [maj_attendu]
    binder_att, _body = _peler_pourtout(maj_fun_attendu.conclusion)
    # α-rename maj_fun_c (binder c_binder) → binder_att
    _, body_c = _peler_pourtout(maj_fun_c.conclusion)
    if binder_att == c_binder:
        maj_fun_ren = maj_fun_c
    else:
        ren = alpha_pour_tout(c_binder, binder_att, body_c)        # (∀c_binder)R ⇔ (∀binder_att)R'
        maj_fun_ren = N.modus_ponens(maj_fun_c, equivalence_avant(ren))
    maj_m = conjonction_intro(hmE, maj_fun_ren)                   # majorant(G,D,m,E)
    return N.modus_ponens(maj_m, least_m)                        # (s,m)∈G


def _cp_extreme_et_le_s(G, E_set, p, a, D, s, cp, hcpD, D_C, s_maj_fun):
    """Pour un témoin c′∈D [hcpD] : renvoie le couple (est_extreme(c′), c′∈M, c′≤s).

    c′∈D⊂C ⇒ c′∈M et est_extreme(c′) ; c′∈D et s majorant de D ⇒ c′≤s."""
    vG, vE, vp, va = _terme(G), _terme(E_set), _terme(p), _terme(a)
    cpC = N.modus_ponens(hcpD, instancie(D_C, _terme(cp)))         # c′∈C
    corps = N.modus_ponens(cpC, equivalence_avant(_inst_Cext(vG, vE, vp, va, _terme(cp))))
    cpM = conjonction_elim_gauche(corps)                          # c′∈M
    cpext = conjonction_elim_droite(corps)                        # est_extreme(c′)
    cp_le_s = N.modus_ponens(hcpD, instancie(s_maj_fun, _terme(cp)))  # (c′,s)∈G
    return cpext, cpM, cp_le_s


def _xeqc_subcase(G, E_set, p, a, D, s, c, x, cp,
                  hcD, hxM, hx_eq_c, hx_le_s, hx_ne_s,
                  D_C, s_maj_fun, least_s, tot_D, cM):
    """Sous-cas x=c de l'extrémalité de s (ÉTAPE 3, T3 ; cœur le plus profond).

    De x=c et x<s on tire c<s ; c ne majore pas D (sinon s≤c=x<s absurde), d'où
    ∃c′∈D ¬(c′≤c) ; par totalité de D, c≤c′ et c≠c′, donc x=c<c′ ; c′ extrême
    (c′∈D⊂C) ⇒ p(x)≤c′, et c′≤s ⇒ p(x)≤s.  Renvoie ⊢ p(x)≤s."""
    vG, vE, vp, va = _terme(G), _terme(E_set), _terme(p), _terme(a)
    vc, vx, vs, vD = _terme(c), _terme(x), _terme(s), _terme(D)
    px = pval(vp, vx)
    but = _le(px, vs, vG)                                          # p(x)≤s
    ex_form = existe(cp, et(appartient(var(cp), vD), non(_le(var(cp), vc, vG))))

    # (A) ∃c′∈D ¬(c′≤c) — par contradiction sur « c majore D »
    allcp = pourtout(cp, impl(appartient(var(cp), vD), _le(var(cp), vc, vG)))
    Hmaj_c = N.assume(allcp)                                       # c majore D (∀cp)
    cE = _x_dans_E_de_M(vG, vE, vp, va, vc, cM)                    # c∈E
    s_le_c = _applique_least(least_s, vc, cE, Hmaj_c, cp)          # (s,c)∈G
    c_eq_x = N.modus_ponens(hx_eq_c, _sym(vx, vc))                 # c=x
    leib_sx = N.modus_ponens(c_eq_x, N.s6(vc, vx, _H, _le(vs, var(_H), vG)))  # (s,c)∈G⇔(s,x)∈G
    s_le_x = N.modus_ponens(s_le_c, equivalence_avant(leib_sx))    # (s,x)∈G
    x_eq_s = _antisym(vG, vx, vs, hx_le_s, s_le_x)                 # x=s
    absurde = _ex_falso(x_eq_s, hx_ne_s, ex_form)                  # ∃c′…  (ex falso)
    maj_c_imp = N.loi_deduction(allcp, absurde)                   # allcp ⇒ (∃c′…)
    from bourbaki.logique.tactiques.tactiques_abrege2 import dne as _dne
    from bourbaki.logique.tactiques.tactiques_abrege_quantif import congruence_existe
    Rcp = impl(appartient(var(cp), vD), _le(var(cp), vc, vG))     # c′∈D⇒c′≤c
    Hnall = N.assume(non(allcp))
    ex_neg = N.modus_ponens(Hnall, _dne(existe(cp, non(Rcp))))    # ∃c′¬(c′∈D⇒c′≤c)
    eqv = _neg_impl_equiv(appartient(var(cp), vD), _le(var(cp), vc, vG))
    ex_conj_nall = N.modus_ponens(ex_neg, equivalence_avant(congruence_existe(eqv, cp)))
    nall_imp = N.loi_deduction(non(allcp), ex_conj_nall)         # ¬allcp ⇒ (∃c′…)
    ex_conj = cas(tiers_exclu(allcp), maj_c_imp, nall_imp)        # (∃c′)(c′∈D et ¬(c′≤c))

    # (B) per-témoin c′ : (c′∈D et ¬(c′≤c)) ⇒ p(x)≤s
    conj_cp = et(appartient(var(cp), vD), non(_le(var(cp), vc, vG)))
    Hcp = N.assume(conj_cp)
    hcpD = conjonction_elim_gauche(Hcp)                           # c′∈D
    ncpc = conjonction_elim_droite(Hcp)                           # ¬(c′≤c)
    cpext, cpM, cp_le_s = _cp_extreme_et_le_s(G, E_set, p, a, D, s, cp, hcpD, D_C, s_maj_fun)
    # comparabilité c,c′ dans D : c≤c′ OU c′≤c ; ¬(c′≤c) ⇒ c≤c′
    from bourbaki.logique.tactiques.tactiques_abrege_egalite import composer_egalites
    comp = _comparable_dans_D(vG, vE, vD, vc, var(cp), hcD, hcpD, tot_D)  # c≤c′ OU c′≤c
    comp2 = N.modus_ponens(comp, equivalence_avant(             # c′≤c OU c≤c′
        comm_ou(_le(vc, var(cp), vG), _le(var(cp), vc, vG))))
    c_le_cp = _disj_syll(comp2, ncpc)                            # (c,c′)∈G  (élim c′≤c)
    # c≠c′ : si c=c′ alors (c′,c)∈G (réflexivité c∈M transportée), contredit ¬(c′≤c)
    cc = _refl_de_M(G, E_set, p, a, vc, cM)                      # (c,c)∈G
    Hc_eq_cp = N.assume(egal(vc, var(cp)))                       # c=c′
    leib_cpc = N.modus_ponens(Hc_eq_cp, N.s6(vc, var(cp), _H, _le(var(_H), vc, vG)))  # (c,c)∈G⇔(c′,c)∈G
    cpc = N.modus_ponens(cc, equivalence_avant(leib_cpc))        # (c′,c)∈G  [c=c′]
    ccp_imp = N.loi_deduction(egal(vc, var(cp)), cpc)           # (c=c′)⇒(c′≤c)
    c_ne_cp = N.modus_ponens(ncpc, contraposition(ccp_imp))    # ¬(c=c′)
    # x≤c′ : x=c, c≤c′ ⇒ (x,c′)∈G  (Φ(w)=(w,c′)∈G ; (x=c)⇒((x,c′)∈G⇔(c,c′)∈G))
    leib_xcp = N.modus_ponens(hx_eq_c, N.s6(vx, vc, _H, _le(var(_H), var(cp), vG)))
    x_le_cp = N.modus_ponens(c_le_cp, equivalence_arriere(leib_xcp))  # (x,c′)∈G
    # x≠c′ : (x=c′)⇒(c=c′) [c=x∘x=c′] contredit ¬(c=c′)
    xcp_imp = N.loi_deduction(egal(vx, var(cp)),
                              composer_egalites(c_eq_x, N.assume(egal(vx, var(cp)))))  # (x=c′)⇒(c=c′)
    x_ne_cp = N.modus_ponens(c_ne_cp, contraposition(xcp_imp))  # ¬(x=c′)
    x_lt_cp = conjonction_intro(x_le_cp, x_ne_cp)             # x<c′
    # c′ extrême : x∈M, x<c′ ⇒ p(x)≤c′
    cpext_x = instancie(cpext, vx)                            # x∈M⇒(x<c′⇒p(x)≤c′)
    px_le_cp = N.modus_ponens(x_lt_cp, N.modus_ponens(hxM, cpext_x))  # p(x)≤c′
    px_le_s = _trans(vG, px, var(cp), vs, px_le_cp, cp_le_s)  # p(x)≤s
    wit_imp = N.loi_deduction(conj_cp, px_le_s)              # (c′∈D et ¬(c′≤c)) ⇒ p(x)≤s
    ex_imp = existe_elimination(wit_imp, cp)                 # (∃c′…) ⇒ p(x)≤s
    return N.modus_ponens(ex_conj, ex_imp)                   # p(x)≤s


def s_est_extreme(G="G", E_set="E", p="p", a="a", D="D", s="s",
                  x="x", c="c", cp="cp", y="y", z="z"):
    """⊢ est_extreme(s)  pour s = sup d'une chaîne D⊂C.   (T3, ÉTAPE 3 — cœur dur.)

    HYPS portées : D⊂C, chaine(G,E,D), borne_superieure(G,D,s,E) + structurelles.
    Pour x∈M, x<s : cas sur (∀c∈D) p(c)≤x.
      • ALL : c≤p(c)≤x ∀c∈D ⇒ x majore D ⇒ s≤x ; avec x≤s, antisym ⇒ x=s, VACUITÉ.
      • NOT : ∃c∈D ¬(p(c)≤x) ; c∈D⊂C extrême ; disj_a_c ⇒ x≤c ; sous-cas x<c
        (c extrême + c≤s) ⇒ p(x)≤s ; sous-cas x=c ⇒ _xeqc_subcase ⇒ p(x)≤s."""
    vG, vE, vp, va = var(G), var(E_set), var(p), var(a)
    vD, vs, vx, vc = var(D), var(s), var(x), var(c)
    Mt, Ct = M(vG, vE, vp, va), Cext(vG, vE, vp, va)
    px = pval(vp, vx)
    but = _le(px, vs, vG)                                         # p(x)≤s

    hxM = N.assume(appartient(vx, Mt))                            # x∈M
    Hlt = N.assume(_lt(vx, vs, vG))                               # x<s
    x_le_s = conjonction_elim_gauche(Hlt)                        # (x,s)∈G
    x_ne_s = conjonction_elim_droite(Hlt)                        # ¬(x=s)

    # extraire les morceaux de chaine(G,E,D) et borne_superieure(G,D,s,E)
    HchaineD = N.assume(chaine(vG, vE, vD, x, y, z))             # C⊂E et totalement_ordonne(G,D)
    tot_D = conjonction_elim_droite(HchaineD)                   # totalement_ordonne(G,D)
    Hbsup = N.assume(borne_superieure(vG, vD, vs, vE, x, y))     # majorant(s) et least
    maj_s = conjonction_elim_gauche(Hbsup)                      # majorant(G,D,s,E)
    s_maj_fun = conjonction_elim_droite(maj_s)                  # (∀x)(x∈D⇒(x,s)∈G)
    least_s = conjonction_elim_droite(Hbsup)                    # (∀y)(maj(y)⇒(s,y)∈G)
    D_C = N.assume(inclus(vD, Ct))                              # D⊂C

    # cas sur (∀c∈D) p(c)≤x
    allc = pourtout(c, impl(appartient(vc, vD), _le(pval(vp, vc), vx, vG)))
    excl = tiers_exclu(allc)

    # BRANCHE ALL : x majore D ⇒ s≤x ⇒ x=s (vacuité)
    Hall = N.assume(allc)                                       # (∀c)(c∈D⇒p(c)≤x)
    #   x majore D : (∀X)(X∈D⇒(X,x)∈G)   via X≤p(X)≤x  (X∈D⊂C⊂M⊂E)
    HXD = N.assume(appartient(var(c), vD))                     # c∈D    (réutilise c)
    cC = N.modus_ponens(HXD, instancie(D_C, vc))               # c∈C
    cMm = conjonction_elim_gauche(N.modus_ponens(cC, equivalence_avant(_inst_Cext(vG, vE, vp, va, vc))))
    cEe = _x_dans_E_de_M(vG, vE, vp, va, vc, cMm)              # c∈E
    c_le_pc = _inflat(vG, vE, vp, vc, cEe)                     # (c,p(c))∈G
    pc_le_x = N.modus_ponens(HXD, instancie(Hall, vc))         # (p(c),x)∈G
    c_le_x = _trans(vG, vc, pval(vp, vc), vx, c_le_pc, pc_le_x)  # (c,x)∈G
    Xmaj_body = N.loi_deduction(appartient(vc, vD), c_le_x)    # c∈D⇒(c,x)∈G
    x_maj_fun = N.generalisation(c, Xmaj_body)                 # (∀c)(c∈D⇒(c,x)∈G)
    xE = _x_dans_E_de_M(vG, vE, vp, va, vx, hxM)              # x∈E
    s_le_x = _applique_least(least_s, vx, xE, x_maj_fun, c)   # (s,x)∈G
    x_eq_s = _antisym(vG, vx, vs, x_le_s, s_le_x)            # x=s
    bAll = N.loi_deduction(allc, _ex_falso(x_eq_s, x_ne_s, but))   # allc ⇒ but

    # BRANCHE NOT : ∃c∈D ¬(p(c)≤x)
    from bourbaki.logique.tactiques.tactiques_abrege2 import dne as _dne
    from bourbaki.logique.tactiques.tactiques_abrege_quantif import congruence_existe
    Rc = impl(appartient(vc, vD), _le(pval(vp, vc), vx, vG))   # c∈D⇒p(c)≤x
    Hnot = N.assume(non(allc))
    ex_neg = N.modus_ponens(Hnot, _dne(existe(c, non(Rc))))   # (∃c)¬(c∈D⇒p(c)≤x)
    eqv = _neg_impl_equiv(appartient(vc, vD), _le(pval(vp, vc), vx, vG))
    ex_conj = N.modus_ponens(ex_neg, equivalence_avant(congruence_existe(eqv, c)))  # (∃c)(c∈D et ¬(p(c)≤x))

    # per-témoin c : (c∈D et ¬(p(c)≤x)) ⇒ but
    conj_c = et(appartient(vc, vD), non(_le(pval(vp, vc), vx, vG)))
    Hc = N.assume(conj_c)
    hcD = conjonction_elim_gauche(Hc)                         # c∈D
    npcx = conjonction_elim_droite(Hc)                        # ¬(p(c)≤x)
    cC = N.modus_ponens(hcD, instancie(D_C, vc))              # c∈C
    corps_c = N.modus_ponens(cC, equivalence_avant(_inst_Cext(vG, vE, vp, va, vc)))
    cM = conjonction_elim_gauche(corps_c)                     # c∈M
    cext = conjonction_elim_droite(corps_c)                   # est_extreme(c)
    cE = _x_dans_E_de_M(vG, vE, vp, va, vc, cM)               # c∈E
    c_le_s = N.modus_ponens(hcD, instancie(s_maj_fun, vc))    # (c,s)∈G  (s majorant)
    # disj_a_c at c (M_c=M) : x≤c OU p(c)≤x ; ¬(p(c)≤x) ⇒ x≤c
    dj = disj_a_c(G, E_set, p, a, c)                          # (∀x)(x∈M⇒(x≤c OU p(c)≤x)) [est_extreme(c),c∈E]
    dj = _cut(dj, est_extreme(vG, vE, vp, va, vc), cext)
    dj = _cut(dj, appartient(vc, vE), cE)
    disj_xc = N.modus_ponens(hxM, instancie(dj, vx))         # x≤c OU p(c)≤x
    disj_xc2 = N.modus_ponens(disj_xc, equivalence_avant(    # p(c)≤x OU x≤c
        comm_ou(_le(vx, vc, vG), _le(pval(vp, vc), vx, vG))))
    x_le_c = _disj_syll(disj_xc2, npcx)                      # (x,c)∈G  (élim p(c)≤x)
    # sous-cas x=c / x<c
    excl2 = tiers_exclu(egal(vx, vc))
    #   x<c : c extrême ⇒ p(x)≤c ; c≤s ⇒ p(x)≤s
    Hxne = N.assume(non(egal(vx, vc)))
    x_lt_c = conjonction_intro(x_le_c, Hxne)                 # x<c
    cext_x = instancie(cext, vx)                             # x∈M⇒(x<c⇒p(x)≤c)
    px_le_c = N.modus_ponens(x_lt_c, N.modus_ponens(hxM, cext_x))   # p(x)≤c
    px_le_s_lt = _trans(vG, px, vc, vs, px_le_c, c_le_s)     # p(x)≤s
    bNe = N.loi_deduction(non(egal(vx, vc)), px_le_s_lt)     # ¬(x=c) ⇒ but
    #   x=c : _xeqc_subcase
    Hxeqc = N.assume(egal(vx, vc))                           # x=c
    sub = _xeqc_subcase(G, E_set, p, a, vD, vs, vc, vx, cp,
                        hcD, hxM, Hxeqc, x_le_s, x_ne_s,
                        D_C, s_maj_fun, least_s, tot_D, cM)  # p(x)≤s
    bEq = N.loi_deduction(egal(vx, vc), sub)                 # (x=c) ⇒ but
    wit_but = cas(excl2, bEq, bNe)                           # but  [conj_c, …]
    wit_imp = N.loi_deduction(conj_c, wit_but)               # (c∈D et ¬(p(c)≤x)) ⇒ but
    ex_imp = existe_elimination(wit_imp, c)                  # (∃c…) ⇒ but
    bNot = N.loi_deduction(non(allc), N.modus_ponens(ex_conj, ex_imp))  # ¬allc ⇒ but

    par_cas = cas(excl, bAll, bNot)                          # but = p(x)≤s
    inner = N.loi_deduction(_lt(vx, vs, vG), par_cas)        # x<s ⇒ p(x)≤s
    body = N.loi_deduction(appartient(vx, Mt), inner)        # x∈M ⇒ (x<s⇒p(x)≤s)
    return N.generalisation(x, body)                         # est_extreme(s)


def Cext_clos_sup(G="G", E_set="E", p="p", a="a", C="C", w="w",
                  x="x", y="y", z="z"):
    """⊢ (∀C)( (C⊂Cext et chaine(G,E,C)) ⇒ (∀w)( borne_sup(G,C,w,E) ⇒ w∈Cext ) ).

    (C close par sup de chaîne — propriété (T3), ÉTAPE 3.)  Pour chaîne C⊂Cext, sup
    w : w∈M (M close par sup, C⊂Cext⊂M) et est_extreme(w) (s_est_extreme).  Donc w∈C.
    HYPS : structurelles uniquement (chaine/bsup/D⊂C déchargées par le contexte)."""
    vG, vE, vp, va = var(G), var(E_set), var(p), var(a)
    vC, vw = var(C), var(w)
    Ct, Mt = Cext(vG, vE, vp, va), M(vG, vE, vp, va)

    hyp1 = et(inclus(vC, Ct), chaine(vG, vE, vC, x, y, z))     # C⊂Cext et chaine
    Hh = N.assume(hyp1)
    C_Ct = conjonction_elim_gauche(Hh)                        # C⊂Cext
    chaineC = conjonction_elim_droite(Hh)                     # chaine(G,E,C)
    Hbsup = N.assume(borne_superieure(vG, vC, vw, vE, x, y))   # borne_sup(G,C,w,E)

    # (1) w∈M  via M_clos_sup  (C⊂M de C⊂Cext⊂M)
    Ct_M = Cext_inclus_M_terme(vG, vE, vp, va)               # Cext⊂M
    C_M = _incl_trans(vC, Ct, Mt, C_Ct, Ct_M)               # C⊂M
    msup = _M_clos_sup_terme(vG, vE, vp, va, vC, vw)         # ((C⊂M et chaine) et bsup)⇒w∈M
    wM = N.modus_ponens(conjonction_intro(conjonction_intro(C_M, chaineC), Hbsup), msup)  # w∈M

    # (2) est_extreme(w)  via s_est_extreme  (chaine, bsup, C⊂Cext déchargés ici)
    wext = s_est_extreme(G, E_set, p, a, C, w, x, "c", "cp", y, z)   # est_extreme(w)  [chaine,bsup,C⊂Cext,…]
    wext = _cut(wext, inclus(vC, Ct), C_Ct)
    wext = _cut(wext, chaine(vG, vE, vC, x, y, z), chaineC)
    wext = _cut(wext, borne_superieure(vG, vC, vw, vE, x, y), Hbsup)

    wC = _Cext_intro(vG, vE, vp, va, vw, wM, wext)          # w∈Cext
    inner = N.loi_deduction(borne_superieure(vG, vC, vw, vE, x, y), wC)  # bsup⇒w∈Cext
    inner_all = N.generalisation(w, inner)                  # (∀w)(bsup⇒w∈Cext)
    body = N.loi_deduction(hyp1, inner_all)                 # hyp1⇒(∀w)(bsup⇒w∈Cext)
    return N.generalisation(C, body)                        # (∀C)(…)


# ── ÉTAPE 3 (assemblage) : C est un TOUR ──────────────────────────────────────
def Cext_est_tour(G="G", E_set="E", p="p", a="a"):
    """⊢ est_tour(G,E,p,a,Cext).   (ÉTAPE 3 — l'ensemble des points extrêmes est un tour.)

    HYPS : plus_petit_element(G,E,a), a∈E + structurelles (antisym, trans, refl,
    inflat, application_dans).  Assemble (T0) Cext⊂E, (T1) a∈Cext, (T2) clos par p,
    (T3) clos par sup.  Le clos_par_p est ré-α (binder c→x) pour matcher est_tour."""
    from bourbaki.logique.tactiques.tactiques_abrege_quantif import alpha_pour_tout
    vG, vE, vp, va = var(G), var(E_set), var(p), var(a)
    Ct = Cext(vG, vE, vp, va)
    t0 = Cext_inclus_E(G, E_set, p, a)                      # Cext⊂E
    t1 = a_dans_Cext(G, E_set, p, a)                        # a∈Cext
    t2c = Cext_clos_p(G, E_set, p, a)                       # (∀c)(c∈Cext⇒p(c)∈Cext)
    #   ré-α le binder c→x pour matcher _clos_par_p(E,p,Cext,"x")
    body_c = impl(appartient(var("c"), Ct), appartient(pval(vp, var("c")), Ct))
    ren = alpha_pour_tout("c", "x", body_c)                # (∀c)R ⇔ (∀x)(x|c)R
    t2 = N.modus_ponens(t2c, equivalence_avant(ren))       # (∀x)(x∈Cext⇒p(x)∈Cext)
    t3 = Cext_clos_sup(G, E_set, p, a)                     # clos par sup
    return conjonction_intro(conjonction_intro(conjonction_intro(t0, t1), t2), t3)


# ════════════════════════════════════════════════════════════════════════════
#  ÉTAPE 4 — C = M   ⇒   TOUT c∈M est extrême
# ════════════════════════════════════════════════════════════════════════════
def M_inclus_Cext(G="G", E_set="E", p="p", a="a"):
    """⊢ M ⊂ Cext   (sous {struct + plus_petit_element + a∈E}).

    Cext est un tour (ÉTAPE 3) et M est le plus petit tour ⇒ M⊂Cext (M_inclus)."""
    vG, vE, vp, va = var(G), var(E_set), var(p), var(a)
    Ct = Cext(vG, vE, vp, va)
    tour = Cext_est_tour(G, E_set, p, a)                   # est_tour(G,E,p,a,Cext)
    M_inc = M_inclus_terme(vG, vE, vp, va, Ct)            # (S tour)⇒(M⊂S)  pour S=Cext
    return N.modus_ponens(tour, M_inc)                    # M⊂Cext


def tout_M_extreme(G="G", E_set="E", p="p", a="a", c="c"):
    """⊢ (∀c)( c∈M ⇒ est_extreme(c) ).   (ÉTAPE 4 — tout élément de M est extrême.)

    De M⊂Cext, c∈M ⇒ c∈Cext ⇒ (Cext_membre) est_extreme(c)."""
    vG, vE, vp, va, vc = var(G), var(E_set), var(p), var(a), var(c)
    M_Ct = M_inclus_Cext(G, E_set, p, a)                  # M⊂Cext
    hcM = N.assume(appartient(vc, M(vG, vE, vp, va)))      # c∈M
    cCt = N.modus_ponens(hcM, instancie(M_Ct, vc))        # c∈Cext
    corps = N.modus_ponens(cCt, equivalence_avant(_inst_Cext(vG, vE, vp, va, vc)))
    cext = conjonction_elim_droite(corps)                 # est_extreme(c)
    body = N.loi_deduction(appartient(vc, M(vG, vE, vp, va)), cext)
    return N.generalisation(c, body)                      # (∀c)(c∈M⇒est_extreme(c))


# ════════════════════════════════════════════════════════════════════════════
#  ÉTAPE 5 — M_est_une_chaine : totalement_ordonne(G, M)   [LE THÉORÈME VISÉ]
# ════════════════════════════════════════════════════════════════════════════
def _est_ordre_M(G, E_set, p, a, x="x", y="y", z="z"):
    """{ est_ordre(G,E) } ⊢ est_ordre(G,M)   (ordre induit : antisym/trans = graphe,
    réflexivité ré-établie sur M via M⊂E)."""
    from bourbaki.ordre.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_relation import ordre_induit_sur_partie
    vG, vE, vp, va = _terme(G), _terme(E_set), _terme(p), _terme(a)
    Mt = M(vG, vE, vp, va)
    # ordre_induit_sur_partie(G,E,A) : { est_ordre(G,E), A⊂E } ⊢ est_ordre(G,A)
    th = ordre_induit_sur_partie(vG, vE, "A", x, y, z)
    # DÉCHARGE les deux hypothèses pour obtenir un théorème CLOS sur A, puis A:=M
    th = N.loi_deduction(inclus(var("A"), vE), th)          # { est_ordre(G,E) } ⊢ A⊂E ⇒ est_ordre(G,A)
    th = N.loi_deduction(est_ordre(vG, vE, x, y, z), th)    # ⊢ est_ordre(G,E) ⇒ (A⊂E ⇒ est_ordre(G,A))  CLOS sur A
    th = instancie(N.generalisation("A", th), Mt)           # ⊢ est_ordre(G,E) ⇒ (M⊂E ⇒ est_ordre(G,M))
    Hord = N.assume(est_ordre(vG, vE, x, y, z))             # est_ordre(G,E)
    M_E = M_inclus_E_terme(vG, vE, vp, va)                  # M⊂E
    return N.modus_ponens(M_E, N.modus_ponens(Hord, th))    # { est_ordre(G,E) } ⊢ est_ordre(G,M)


def M_est_une_chaine(G="G", E_set="E", p="p", a="a", x="x", y="y", z="z"):
    """⊢ totalement_ordonne(G, M).   (ÉTAPE 5 — LE VERROU de Bourbaki–Witt LEVÉ.)

    M est TOTALEMENT ORDONNÉ : c'est un ordre induit (est_ordre(G,M)), et deux
    éléments x,y∈M sont comparables — car y est EXTRÊME (ÉTAPE 4) et c (=y)
    comparable à tout x∈M (ÉTAPE 2, comparable_a_c).  HYPS : est_ordre(G,E) +
    application_dans + inflationnaire + plus_petit_element + a∈E (toutes structurelles,
    déchargées comme dans point_fixe_de_sup ; theorie_ensembles inchangée)."""
    from bourbaki.logique.tactiques.tactiques_abrege_quantif import (
        alpha_pour_tout, congruence_pour_tout,
    )
    vG, vE, vp, va = var(G), var(E_set), var(p), var(a)
    # éléments comparés : « u » (1er) et « v » (2nd) — NOMS FRAIS, disjoints des
    # binders internes (x,y,z,C,w,s) de comparable_a_c/Mc_* ; ré-α-isés en x,y à la fin.
    vu, vv = var("u"), var("v")
    Mt = M(vG, vE, vp, va)
    Hord = N.assume(est_ordre(vG, vE, x, y, z))             # est_ordre(G,E)
    # (1) est_ordre(G,M)
    ordM = _cut(_est_ordre_M(vG, vE, vp, va, x, y, z), est_ordre(vG, vE, x, y, z), Hord)
    # (2) comparabilité : (u∈M et v∈M) ⇒ (u≤v OU v≤u)
    Huv = N.assume(et(appartient(vu, Mt), appartient(vv, Mt)))
    uM = conjonction_elim_gauche(Huv)                       # u∈M
    vM = conjonction_elim_droite(Huv)                       # v∈M
    vE_ = _x_dans_E_de_M(vG, vE, vp, va, vv, vM)            # v∈E
    vext = N.modus_ponens(vM, instancie(tout_M_extreme(G, E_set, p, a), vv))   # est_extreme(v)
    comp = comparable_a_c(G, E_set, p, a, "v", "u")        # (∀u)(u∈M⇒(u≤v OU v≤u))  [est_extreme(v), v∈E]
    comp = _cut(comp, est_extreme(vG, vE, vp, va, vv), vext)
    comp = _cut(comp, appartient(vv, vE), vE_)
    disj = N.modus_ponens(uM, instancie(comp, vu))         # u≤v OU v≤u
    cmp_body = N.loi_deduction(et(appartient(vu, Mt), appartient(vv, Mt)), disj)
    comp_uv = N.generalisation("u", N.generalisation("v", cmp_body))   # (∀u)(∀v)(…)
    #   ré-α (∀u)(∀v) → (∀x)(∀y) pour matcher l'énoncé totalement_ordonne(G,M,x,y,z)
    inner_v = impl(et(appartient(vu, Mt), appartient(vv, Mt)),
                   ou(_le(vu, vv, vG), _le(vv, vu, vG)))
    comp_uy = N.modus_ponens(comp_uv, equivalence_avant(    # (∀u)(∀y)…
        congruence_pour_tout(alpha_pour_tout("v", y, inner_v), "u")))
    inner_y = impl(et(appartient(vu, Mt), appartient(var(y), Mt)),
                   ou(_le(vu, var(y), vG), _le(var(y), vu, vG)))
    body_u = pourtout(y, inner_y)                          # (∀y)(inner_y)  = corps sous ∀u
    comparables = N.modus_ponens(comp_uy, equivalence_avant(alpha_pour_tout("u", x, body_u)))
    return conjonction_intro(ordM, comparables)            # totalement_ordonne(G,M)


# ════════════════════════════════════════════════════════════════════════════
#  ÉTAPE 6 — bourbaki_witt : le POINT FIXE p(s)=s  (assemblage final, INCONDITIONNEL
#  modulo les hyps structurelles, comme tout le module)
# ════════════════════════════════════════════════════════════════════════════
def _chaine_M(G, E_set, p, a, x, y, z):
    """{ totalement_ordonne(G,M) } ⊢ chaine(G,E,M)  = (M⊂E et totalement_ordonne(G,M))."""
    vG, vE, vp, va = _terme(G), _terme(E_set), _terme(p), _terme(a)
    Mt = M(vG, vE, vp, va)
    Htot = N.assume(totalement_ordonne(vG, Mt, x, y, z))    # totalement_ordonne(G,M)
    M_E = M_inclus_E_terme(vG, vE, vp, va)                  # M⊂E
    return conjonction_intro(M_E, Htot)                    # chaine(G,E,M)


def bourbaki_witt_theoreme(G="G", E_set="E", p="p", a="a", s="s", x="x", y="y", z="z",
                           avec_E=False):
    """⊢ bourbaki_witt(G,E,p,a).   (ÉTAPE 6 — THÉORÈME DE POINT FIXE DE BOURBAKI–WITT.)

    ⊢ ( est_ordre(G,E) ∧ chaine_complet(G,E) ∧ application_dans(E,p)
        ∧ inflationnaire(G,E,p) ∧ plus_petit_element(G,E,a) ) ⇒ (∃s)( p(s)=s ).

    M est une CHAÎNE (ÉTAPE 5, M_est_une_chaine) ⊂ E chaîne-complet ⇒ M a une borne
    sup s ; M close par sup ⇒ s∈M ; s = plus grand élément de M ; p(s)∈M (close par p) ;
    p(s)≤s (s majore M⊇{p(s)}) et p(s)≥s (inflationnaire) ⇒ p(s)=s (antisymétrie).
    INCONDITIONNEL : le verrou « M chaîne » est désormais PROUVÉ (theorie_ensembles=22).

    Si avec_E=True, la conclusion est renforcée en (∃s)( s∈E et p(s)=s ) — le point
    fixe est un VRAI élément de E (le sup de M ⊂ E), forme utile pour Zorn (ÉTAPE 7)."""
    vG, vE, vp, va, vs = var(G), var(E_set), var(p), var(a), var(s)
    Mt = M(vG, vE, vp, va)

    # ── hypothèses globales du LEMME 3 (assumées, déchargées en bloc à la fin) ──
    Hord = N.assume(est_ordre(vG, vE, x, y, z))
    Hcc = N.assume(chaine_complet(vG, vE, "C", s, x, y, z))
    Happ = N.assume(application_dans(vE, vp, x))
    Hinf = N.assume(inflationnaire(vG, vE, vp, x))
    Hppe = N.assume(plus_petit_element(vG, vE, va))
    # composants d'est_ordre
    refl_E = conjonction_elim_gauche(conjonction_elim_gauche(Hord))   # reflexivite_sur(G,E)
    antisym = conjonction_elim_droite(conjonction_elim_gauche(Hord))  # antisymetrie(G)
    trans = conjonction_elim_droite(Hord)                            # transitivite_rel(G)
    ppe_E = conjonction_elim_gauche(Hppe)                            # a∈E

    # ── M est une chaîne (ÉTAPE 5) : décharge ses hyps structurelles ──────────
    tot_M = M_est_une_chaine(G, E_set, p, a, x, y, z)               # totalement_ordonne(G,M) [struct]
    for hyp_f, preuve in (
        (est_ordre(vG, vE, x, y, z), Hord),
        (application_dans(vE, vp, x), Happ),
        (inflationnaire(vG, vE, vp, x), Hinf),
        (reflexivite_sur(vG, vE, x), refl_E),
        (antisymetrie(vG, x, y), antisym),
        (transitivite_rel(vG, x, y, z), trans),
        (plus_petit_element(vG, vE, va), Hppe),
        (appartient(va, vE), ppe_E),
    ):
        tot_M = _cut(tot_M, hyp_f, preuve)
    # chaine(G,E,M)
    chaineM = conjonction_intro(M_inclus_E_terme(vG, vE, vp, va), tot_M)

    # ── chaine_complet ⇒ (∃s) borne_superieure(G,M,s,E) ───────────────────────
    cc_quant = conjonction_elim_droite(Hcc)                        # (∀C)(chaine(G,E,C)⇒(∃s)bsup)
    cc_M = instancie(cc_quant, Mt)                                # chaine(G,E,M)⇒(∃s)bsup(G,M,s,E)
    ex_bsup = N.modus_ponens(chaineM, cc_M)                       # (∃s)borne_superieure(G,M,s,E)

    # ── sous l'hypothèse borne_superieure(G,M,s,E), conclure (∃s')(p(s')=s') ───
    Hbsup = N.assume(borne_superieure(vG, Mt, vs, vE, x, y))      # bsup(G,M,s,E)
    maj_s = conjonction_elim_gauche(Hbsup)                        # majorant(G,M,s,E)
    s_in_E = conjonction_elim_gauche(maj_s)                       # s∈E
    s_maj_fun = conjonction_elim_droite(maj_s)                    # (∀x)(x∈M⇒(x,s)∈G)
    # s∈M  via M_clos_sup  ( (M⊂M et chaine(G,E,M)) et bsup )
    MM = _inclus_refl(Mt)                                         # M⊂M
    msup = _M_clos_sup_terme(vG, vE, vp, va, Mt, vs)             # ((M⊂M et chaine) et bsup)⇒s∈M
    sM = N.modus_ponens(conjonction_intro(conjonction_intro(MM, chaineM), Hbsup), msup)  # s∈M
    # plus_grand_element(G,M,s) = s∈M et (∀x)(x∈M⇒(x,s)∈G)
    pge_s = conjonction_intro(sM, s_maj_fun)                     # plus_grand_element(G,M,s)
    # p(s)∈M  via M_clos_p  (p(s)∈E de application_dans + s∈E)
    psM = _px_dans_M(vG, vE, vp, va, vs, sM)                     # p(s)∈M  [application_dans]
    psM = _cut(psM, application_dans(vE, vp, x), Happ)
    # point_fixe_de_sup : {antisym, inflat, s∈E, p(s)∈M, plus_grand_element} ⊢ p(s)=s
    pfix = point_fixe_de_sup(G, E_set, p, a, s, x, y)           # p(s)=s  [5 hyps]
    pfix = _cut(pfix, antisymetrie(vG, x, y), antisym)
    pfix = _cut(pfix, inflationnaire(vG, vE, vp, x), Hinf)
    pfix = _cut(pfix, appartient(vs, vE), s_in_E)
    pfix = _cut(pfix, appartient(pval(vp, vs), Mt), psM)
    pfix = _cut(pfix, plus_grand_element(vG, Mt, vs), pge_s)    # ⊢ p(s)=s  [hyps globales]
    # corps témoin : soit p(s)=s, soit (s∈E et p(s)=s)
    if avec_E:
        temoin = conjonction_intro(s_in_E, pfix)               # s∈E et p(s)=s
        corps = et(appartient(vs, vE), egal(pval(vp, vs), vs))
    else:
        temoin = pfix                                          # p(s)=s
        corps = egal(pval(vp, vs), vs)
    # (∃s) corps  via S5 témoin s
    s5 = N.s5(corps, vs, s)                                     # (s|s)corps ⇒ (∃s)corps
    ex_pfix = N.modus_ponens(temoin, s5)                       # (∃s)corps  [hyps, bsup]
    # éliminer le ∃ sur s : (borne_sup(G,M,s,E)) ⇒ (∃s)corps puis existe_elim
    bsup_imp = N.loi_deduction(borne_superieure(vG, Mt, vs, vE, x, y), ex_pfix)
    ex_imp = existe_elimination(bsup_imp, s)                    # (∃s)bsup ⇒ (∃s)corps
    conc = N.modus_ponens(ex_bsup, ex_imp)                      # (∃s)corps  [hyps globales]

    # ── décharger les 5 hypothèses globales en bloc (forme de l'énoncé) ────────
    hyp = et(et(et(et(est_ordre(vG, vE, x, y, z),
                      chaine_complet(vG, vE, "C", s, x, y, z)),
                   application_dans(vE, vp, x)),
                inflationnaire(vG, vE, vp, x)),
             plus_petit_element(vG, vE, va))
    Hbloc = N.assume(hyp)
    g1 = conjonction_elim_gauche(Hbloc)
    g2 = conjonction_elim_droite(Hbloc)                         # plus_petit_element
    g3 = conjonction_elim_droite(g1)                           # inflationnaire
    g4 = conjonction_elim_droite(conjonction_elim_gauche(g1))  # application_dans
    g5 = conjonction_elim_gauche(conjonction_elim_gauche(g1))  # … et chaine_complet
    ord_ = conjonction_elim_gauche(g5)                         # est_ordre
    cc_ = conjonction_elim_droite(g5)                          # chaine_complet
    for hyp_f, preuve in (
        (est_ordre(vG, vE, x, y, z), ord_),
        (chaine_complet(vG, vE, "C", s, x, y, z), cc_),
        (application_dans(vE, vp, x), g4),
        (inflationnaire(vG, vE, vp, x), g3),
        (plus_petit_element(vG, vE, va), g2),
    ):
        conc = _cut(conc, hyp_f, preuve)
    return N.loi_deduction(hyp, conc)                          # ⊢ hyp ⇒ (∃s)(p(s)=s)


# ════════════════════════════════════════════════════════════════════════════
#  ÉTAPE 7 — vers ZORN par la voie Bourbaki–Witt (cœur de contradiction)
#  Zorn complet ⇐ Bourbaki–Witt requiert le signe τ (axiome du choix) pour
#  construire p(x)=majorant STRICT, ET le pont « inductif ⇒ chaîne-complet » (la
#  borne sup d'une chaîne, obtenue en bien-ordonnant) — chantier ultérieur.  On
#  livre ICI le CŒUR INCONDITIONNEL : une application p INFLATIONNAIRE STRICTE est
#  INCOMPATIBLE avec les hypothèses de Bourbaki–Witt (qui forcent un point fixe).
# ════════════════════════════════════════════════════════════════════════════
def inflationnaire_strict(G, E_set, p, x="x"):
    """inflationnaire_strict(G,E,p) := (∀x)( x∈E ⇒ ( (x,p(x))∈G et x≠p(x) ) ).

    « p est STRICTEMENT inflationnaire » : p(x) > x pour tout x∈E.  C'est la forme
    qu'aurait le signe τ d'un majorant STRICT si E n'avait pas d'élément maximal."""
    vE, vx = _terme(E_set), var(x)
    return pourtout(x, impl(appartient(vx, vE),
                            et(_le(vx, pval(p, vx), G), non(egal(vx, pval(p, vx))))))


def bw_strict_contradiction(G="G", E_set="E", p="p", a="a", s="s", x="x", y="y", z="z"):
    """⊢ ¬( bw-hyps(G,E,p,a) ∧ inflationnaire_strict(G,E,p) ).

    CŒUR de Zorn ⇐ Bourbaki–Witt : les hypothèses de Bourbaki–Witt + une p
    STRICTEMENT inflationnaire sont CONTRADICTOIRES.  Bourbaki–Witt (forme avec_E)
    donne (∃s)(s∈E et p(s)=s) ; mais strictement inflationnaire donne s≠p(s) pour
    s∈E — absurde.  INCONDITIONNEL (theorie_ensembles=22).

    Le pas restant vers ZORN — construire p STRICT par le signe τ depuis « E n'a
    pas d'élément maximal », et obtenir chaine_complet à partir de inductif (bon
    ordre des chaînes) — relève de l'axiome du choix / récurrence transfinie ;
    REPORTÉ (chantier ultérieur).  Cette contradiction EN EST LE NOYAU LOGIQUE."""
    vG, vE, vp, va, vs = var(G), var(E_set), var(p), var(a), var(s)
    bw_hyp = et(et(et(et(est_ordre(vG, vE, x, y, z),
                         chaine_complet(vG, vE, "C", s, x, y, z)),
                      application_dans(vE, vp, x)),
                   inflationnaire(vG, vE, vp, x)),
                plus_petit_element(vG, vE, va))
    strict = inflationnaire_strict(vG, vE, vp, x)
    conj = et(bw_hyp, strict)
    H = N.assume(conj)
    bwh = conjonction_elim_gauche(H)                            # bw-hyps
    Hstrict = conjonction_elim_droite(H)                        # inflationnaire_strict
    # (1) Bourbaki–Witt (avec_E) ⇒ (∃s)(s∈E et p(s)=s)
    bw_thm = bourbaki_witt_theoreme(G, E_set, p, a, s, x, y, z, avec_E=True)
    ex_fix = N.modus_ponens(bwh, bw_thm)                        # (∃s)(s∈E et p(s)=s)  [conj]
    # (2) per-témoin s : (s∈E et p(s)=s) ⇒ ¬conj   (strict ⇒ s≠p(s) ; p(s)=s ⇒ s=p(s))
    corps = et(appartient(vs, vE), egal(pval(vp, vs), vs))
    Hw = N.assume(corps)
    sE = conjonction_elim_gauche(Hw)                            # s∈E
    Hps = conjonction_elim_droite(Hw)                          # p(s)=s
    strict_s = N.modus_ponens(sE, instancie(Hstrict, vs))      # (s,p(s))∈G et s≠p(s)
    s_ne_ps = conjonction_elim_droite(strict_s)                # ¬(s=p(s))
    s_eq_ps = N.modus_ponens(Hps, _sym(pval(vp, vs), vs))      # s=p(s)
    not_conj_w = _ex_falso(s_eq_ps, s_ne_ps, non(conj))        # ¬conj   [corps, conj]
    w_imp = N.loi_deduction(corps, not_conj_w)                 # (s∈E et p(s)=s) ⇒ ¬conj  [conj]
    not_conj = existe_elimination(w_imp, s)                    # (∃s)(…) ⇒ ¬conj   [conj]
    nc = N.modus_ponens(ex_fix, not_conj)                      # ¬conj   [conj]
    # conj ⊢ ¬conj  ⇒  ⊢ ¬conj   (tautologie (P⇒¬P)⇒¬P)
    conj_imp = N.loi_deduction(conj, nc)                       # ⊢ conj ⇒ ¬conj
    return _refute_self(conj_imp)                              # ⊢ ¬conj


def _refute_self(thm_P_imp_notP):
    """De ⊢ (P ⇒ ¬P) déduit ⊢ ¬P.   ((P⇒¬P) ≡ (¬P∨¬P) → ¬P par S1.)"""
    from bourbaki.logique.tactiques.tactiques_abrege import antecedent_consequent
    P, notP = antecedent_consequent(thm_P_imp_notP.conclusion)  # P⇒¬P = ¬P∨¬P
    return N.modus_ponens(thm_P_imp_notP, N.s1(notP))           # (¬P∨¬P)⇒¬P


def _le_de_lt(thm_lt):
    """De ⊢ (x<y) [= (x≤y et x≠y)] déduit ⊢ (x≤y)."""
    return conjonction_elim_gauche(thm_lt)


def _ou_gauche(thm_p, q):
    """De ⊢ P, déduit ⊢ (P OU Q)."""
    p = thm_p.conclusion
    return N.modus_ponens(thm_p, N.s2(p, q))                  # P ⇒ (P∨Q)


def _ou_droite(thm_q, p):
    """De ⊢ Q, déduit ⊢ (P OU Q)."""
    q = thm_q.conclusion
    pq = N.modus_ponens(thm_q, N.s2(q, p))                    # Q ⇒ (Q∨P)
    return N.modus_ponens(pq, N.s3(q, p))                     # (Q∨P) ⇒ (P∨Q)


def _ex_falso(thm_p, thm_np, q):
    """De ⊢ P [thm_p] et ⊢ ¬P [thm_np] déduit ⊢ Q  (ex falso quodlibet)."""
    p = thm_p.conclusion
    P_imp_Q = N.modus_ponens(thm_np, N.s2(non(p), q))        # ¬P ⇒ (¬P∨Q) = (P⇒Q)
    return N.modus_ponens(thm_p, P_imp_Q)                    # Q


def _disj_syll(thm_pq, thm_np):
    """De ⊢ (P ∨ Q) [thm_pq] et ⊢ ¬P [thm_np] déduit ⊢ Q.  (syllogisme disjonctif.)"""
    p, q = thm_pq.conclusion.sous                            # (P∨Q) = ou-nœud
    # cas P : P ⇒ Q  via P et ¬P ⇒ absurde ⇒ Q.  On utilise : ¬P ⊢ (P⇒Q).
    #   P⇒Q  =  ¬P ∨ Q  ;  de ¬P, S2 donne ¬P ⇒ (¬P ∨ Q) = (P⇒Q).
    P_imp_Q = N.modus_ponens(thm_np, N.s2(non(p), q))        # (P⇒Q)   [¬P]
    Q_imp_Q = a_implique_a(q)                                # (Q⇒Q)
    return cas(thm_pq, P_imp_Q, Q_imp_Q)                     # Q


def _neg_impl_equiv(P, Q):
    """⊢ ¬(P⇒Q) ⇔ (P et ¬Q).   (¬(P⇒Q) = ¬(¬P∨Q) ⇔ (¬¬P et ¬Q) ⇔ (P et ¬Q).)"""
    from bourbaki.logique.tactiques.tactiques_abrege2 import (
        demorgan_ou, dne, dni, et_congruence_gauche,
    )
    dm = demorgan_ou(non(P), Q)                              # ¬(¬P∨Q) ⇔ (¬¬P et ¬Q)
    dnP = conjonction_intro(dne(P), dni(P))                 # ¬¬P ⇔ P
    cong = et_congruence_gauche(dnP, non(Q))               # (¬¬P et ¬Q) ⇔ (P et ¬Q)
    from bourbaki.logique.tactiques.tactiques_abrege2 import equivalence_transitivite
    return equivalence_transitivite(dm, cong)              # ¬(P⇒Q) ⇔ (P et ¬Q)


# ════════════════════════════════════════════════════════════════════════════
#  DÉFINITION CLÉ — point EXTRÊME de Bourbaki–Witt
# ════════════════════════════════════════════════════════════════════════════
def est_extreme(G, E_set, p, a, c, x="x"):
    """est_extreme(c) := (∀x)( x∈M ⇒ ( x<c ⇒ p(x) ≤ c ) ).

    « c n'est strictement entre AUCUN x∈M et son image p(x) » : si x<c alors p(x)≤c.
    Cœur de la preuve de Witt (les éléments extrêmes balaient M sans « sauter »
    par-dessus c)."""
    vx = var(x)
    Mt = M(_terme(G), _terme(E_set), _terme(p), _terme(a))
    corps = impl(appartient(vx, Mt), impl(_lt(vx, c, G), _le(pval(p, vx), c, G)))
    return pourtout(x, corps)


# ════════════════════════════════════════════════════════════════════════════
#  ÉTAPE 1 — le tour M_c := { x∈M | x≤c OU p(c)≤x }   (TERME + axiome dédié)
# ════════════════════════════════════════════════════════════════════════════
def Mc(G, E_set, p, a, c):
    """M_c := { x∈M | x≤c OU p(c)≤x }  (sélection collectivisante dans M, S8+A1)."""
    return E.app("bw_Mc", _terme(G), _terme(E_set), _terme(p), _terme(a), _terme(c))


def _corps_Mc(G, E_set, p, a, c, z):
    """Corps de M_c :  z∈M et (z≤c OU p(c)≤z)."""
    Mt = M(_terme(G), _terme(E_set), _terme(p), _terme(a))
    return et(appartient(_terme(z), Mt), ou(_le(z, c, G), _le(pval(p, c), z, G)))


def axiome_Mc(G="G", E_set="E", p="p", a="a", c="c", z="z"):
    """⊢-schéma (∀G E p a c z)( z∈M_c ⇔ (z∈M et (z≤c OU p(c)≤z)) ).

    Axiome DÉFINITIONNEL de la sélection M_c (légitime S8+A1, motif axiome_M).
    N'altère PAS theorie_ensembles()."""
    vG, vE, vp, va, vc, vz = var(G), var(E_set), var(p), var(a), var(c), var(z)
    return pourtout(G, pourtout(E_set, pourtout(p, pourtout(a, pourtout(c, pourtout(z,
        equiv(appartient(vz, Mc(vG, vE, vp, va, vc)),
              _corps_Mc(vG, vE, vp, va, vc, vz))))))))


def theorie_Mc(G="G", E_set="E", p="p", a="a", c="c", z="z"):
    """Théorie DÉDIÉE ne contenant que l'axiome de M_c (E.III.2, Witt, ÉTAPE 1)."""
    return N.Theorie("Mc-Bourbaki-Witt", [axiome_Mc(G, E_set, p, a, c, z)])


def _inst_Mc(G, E_set, p, a, c, z):
    """⊢ ( z∈M_c ⇔ (z∈M et (z≤c OU p(c)≤z)) )   (axiome instancié aux TERMES)."""
    ax = N.axiome(theorie_Mc(), axiome_Mc())
    for tm in (G, E_set, p, a, c, z):
        ax = instancie(ax, _terme(tm))
    return ax


def Mc_membre(G="G", E_set="E", p="p", a="a", c="c", z="z"):
    """⊢ ( z∈M_c ) ⇔ ( z∈M et (z≤c OU p(c)≤z) )."""
    return _inst_Mc(var(G), var(E_set), var(p), var(a), var(c), var(z))


def Mc_inclus_M(G="G", E_set="E", p="p", a="a", c="c"):
    """⊢ M_c ⊂ M.   (M_c est une sélection dans M.)"""
    vG, vE, vp, va, vc, vz = var(G), var(E_set), var(p), var(a), var(c), var("z")
    eq = _inst_Mc(vG, vE, vp, va, vc, vz)                       # z∈M_c ⇔ (z∈M et …)
    z_imp = syllogisme(equivalence_avant(eq),
                       projection_gauche(appartient(vz, M(vG, vE, vp, va)),
                                         ou(_le(vz, vc, vG), _le(pval(vp, vc), vz, vG))))
    return N.generalisation("z", z_imp)                         # M_c ⊂ M


def Mc_inclus_M_terme(G, E_set, p, a, c):
    """⊢ M_c ⊂ M  pour des TERMES G,E,p,a,c quelconques."""
    th = Mc_inclus_M("G", "E", "p", "a", "c")
    for nm, tm in (("G", G), ("E", E_set), ("p", p), ("a", a), ("c", c)):
        th = instancie(N.generalisation(nm, th), _terme(tm))
    return th


def _Mc_intro(G, E_set, p, a, c, z, hzM, hdisj):
    """De ⊢ z∈M [hzM] et ⊢ (z≤c OU p(c)≤z) [hdisj], déduit ⊢ z∈M_c."""
    corps = conjonction_intro(hzM, hdisj)
    return N.modus_ponens(corps, equivalence_arriere(_inst_Mc(G, E_set, p, a, c, z)))


def Mc_inclus_E(G="G", E_set="E", p="p", a="a", c="c"):
    """⊢ M_c ⊂ E.   (M_c ⊂ M ⊂ E.)"""
    vG, vE, vp, va, vc = var(G), var(E_set), var(p), var(a), var(c)
    Mt = M(vG, vE, vp, va)
    Mc_M = Mc_inclus_M(G, E_set, p, a, c)                  # M_c ⊂ M  (lettres)
    M_E = M_inclus_E(G, E_set, p, a)                        # M ⊂ E
    return _incl_trans(Mc(vG, vE, vp, va, vc), Mt, vE, Mc_M, M_E)  # M_c ⊂ E


def a_dans_Mc(G="G", E_set="E", p="p", a="a", c="c"):
    """⊢ { a∈E, a plus petit élt de E } ⊢ a∈M_c.

    a∈M (a_dans_M) ; et a≤c (a est le plus petit élément de E, c∈E) → disjonction
    gauche.  Donc a∈M_c."""
    vG, vE, vp, va, vc = var(G), var(E_set), var(p), var(a), var(c)
    haE = N.assume(appartient(va, vE))                     # a∈E
    aM = a_dans_M(G, E_set, p, a)                          # a∈M   [a∈E]
    # a≤c : a plus petit élément de E, c∈E ⇒ (a,c)∈G
    Hppe = N.assume(plus_petit_element(vG, vE, va))         # a∈E et (∀x)(x∈E⇒(a,x)∈G)
    a_min = conjonction_elim_droite(Hppe)                  # (∀x)(x∈E⇒(a,x)∈G)
    HcE = N.assume(appartient(vc, vE))                     # c∈E
    a_le_c = N.modus_ponens(HcE, instancie(a_min, vc))     # (a,c)∈G
    disj = N.modus_ponens(a_le_c, N.s2(_le(va, vc, vG), _le(pval(vp, vc), va, vG)))  # a≤c OU p(c)≤a
    return _Mc_intro(vG, vE, vp, va, vc, va, aM, disj)     # a∈M_c


# ════════════════════════════════════════════════════════════════════════════
#  ÉNONCÉ DE ZORN (réduction documentée Zorn ⇐ Bourbaki–Witt)
# ════════════════════════════════════════════════════════════════════════════
def zorn_via_bw_enonce(G, E_set, m="m", C="C", x="x", y="y", z="z"):
    """zorn_via_bw_enonce(G,E) := énoncé de Zorn (ré-export depuis ensembles_zorn).

    Re-expose l'ÉNONCÉ — PAS une preuve.  Le cœur logique (bw_strict_contradiction)
    est PROUVÉ ; la fabrication par τ du majorant strict + le pont
    inductif⇒chaine_complet (bon ordre des chaînes) restent à assembler (axiome du
    choix).  JAMAIS postulé."""
    return zorn_via_bw(G, E_set, m, C, x, y, z)


__all__ = [
    # constante / notations
    "inflationnaire_strict",
    # ÉTAPE 1 — M_c tour
    "est_extreme", "Mc", "axiome_Mc", "theorie_Mc", "Mc_membre",
    "Mc_inclus_M", "Mc_inclus_M_terme", "Mc_inclus_E", "a_dans_Mc",
    "Mc_clos_p", "Mc_clos_sup", "Mc_est_tour",
    # ÉTAPE 2 — M_c = M
    "M_inclus_Mc", "disj_a_c", "comparable_a_c",
    # ÉTAPE 3 — Cext tour
    "Cext", "axiome_Cext", "theorie_Cext", "Cext_membre",
    "Cext_inclus_M", "Cext_inclus_M_terme", "Cext_inclus_E",
    "a_est_extreme", "a_dans_Cext", "pc_est_extreme", "Cext_clos_p",
    "s_est_extreme", "Cext_clos_sup", "Cext_est_tour",
    # ÉTAPE 4 — C = M
    "M_inclus_Cext", "tout_M_extreme",
    # ÉTAPE 5 — LE VERROU : M est une chaîne
    "M_est_une_chaine",
    # ÉTAPE 6 — point fixe de Bourbaki–Witt
    "bourbaki_witt_theoreme",
    # ÉTAPE 7 — cœur de Zorn ⇐ Bourbaki–Witt
    "bw_strict_contradiction", "zorn_via_bw_enonce",
]
