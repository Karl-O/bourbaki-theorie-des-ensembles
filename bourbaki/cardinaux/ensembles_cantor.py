"""§III.3 — Théorème de Cantor : Card X < Card P(X)  (E.III.3, début).

ÉTAPE 1 (certifiée par le noyau) :  ⊢ X ≤ P(X).

L'injection-témoin est l'application singleton  x ↦ {x}  de X dans P(X).  Son
graphe est  F := graphe_terme(X, {x})  (= {(x, {x}) | x ∈ X}, C54, E.II.46).  On
montre que F est :
  • FONCTIONNEL                 (graphe_terme_fonctionnel) ;
  • de DOMAINE X                (graphe_terme_domaine : dom F = X) ;
  • INJECTIF sur X              (injective_dans : {u}={u'} ⇒ u=u', singleton_injectif) ;
  • d'IMAGE incluse dans P(X)   (image(F,X) ⊂ P(X) : tout {u} pour u∈X est ⊂ X,
                                 donc ∈ P(X) par membre_parties).
Les quatre conjoints donnent  est_injection_de(F, X, P(X)), d'où, par S5 (témoin
F), (∃F) est_injection_de(F, X, P(X)) = inf_egal_card(X, P(X)) = « X ≤ P(X) ».

Lemmes intermédiaires re-utilisables :
  • graphe_terme_domaine_membre   {u∈A} ⊢ (u, T[u]) ∈ F  et  (∃y)((u,y)∈F) ;
  • graphe_terme_valeur           {u∈A} ⊢ F(u) = T[u] ;
  • graphe_terme_domaine          ⊢ dom(graphe_terme(A,T)) = A.

ÉTAPE 2 (Card X < Card P(X), argument diagonal) — FAITE, certifiée par le noyau :
  • paradoxe_diagonal           ⊢ ¬(P ⇔ ¬P)  (cœur logique : Russell/Cantor) ;
  • aucune_surjection_parties   {F bijection X→P(X)} ⊢ ¬(F bijection X→P(X)) :
      D := {z∈X | ¬(z∈F(z))} (diagonale_cantor, S8+A1) est une partie de X, donc
      D∈P(X) ; par surjectivité il existe d∈X avec F(d)=D ; alors
      d∈D ⇔ ¬(d∈D), instance de paradoxe_diagonal — contradiction ;
  • cantor_non_equipotent       ⊢ ¬Eq(X, P(X))  (élimination de ∃F + ex falso) ;
  • cantor_distinct             ⊢ ¬(X = P(X))    (sinon Eq par réflexivité) ;
  • cantor_strict               ⊢ X < P(X) = Card X < Card P(X)  (≤ et ≠).
"""
from __future__ import annotations

from bourbaki.logique.formule import (Terme, var, egal, et, non, equiv, appartient,
                     existe, subst_t)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.tactiques.tactiques_abrege import a_implique_a
from bourbaki.logique.tactiques.tactiques_abrege2 import (conjonction_intro, conjonction_elim_gauche,
                               conjonction_elim_droite, equivalence_avant,
                               equivalence_arriere, equivalence_transitivite,
                               equivalence_symetrie, equiv_neg, instancie)
from bourbaki.logique.tactiques.tactiques_abrege_egalite import (symetrie, symetrie as eg_symetrie,
                                      composer_egalites)
from bourbaki.logique.tactiques.tactiques_abrege_quantif import existe_elimination, congruence_existe, alpha_existe
from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_theoremes import egalite_par_extension
from bourbaki.ensembles.fonctions.ii_3_6_fonction_terme.ensembles_fonction_terme import membre_graphe_terme, graphe_terme_fonctionnel
from bourbaki.ensembles.fonctions.ii_3_4_fonctions_valeur.ensembles_fonctions import valeur_caracterisation
from bourbaki.ensembles.ii_2_couples_produit.ensembles_couples import singleton_injectif
from bourbaki.ensembles.familles.ii_5_produit_famille.ii_5_definitions.ensembles_produit_famille import membre_parties
from bourbaki.cardinaux.ensembles_cardinaux import est_injection_de


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# ── (u, T[u]) ∈ F  pour u∈A  +  u dans le domaine ─────────────────────────────
def graphe_terme_couple_dans(a, t, u="u", x="x", y="y"):
    """{u ∈ A} ⊢ (u, T[u]) ∈ F,   F = graphe_terme(A,T),  T[u] = (u|x)T.

    De membre_graphe_terme (généralisée sur v puis instanciée à T[u]) :
    ((u,T[u])∈F) ⇔ (u∈A et T[u]=T[u]).  Sous u∈A et T[u]=T[u] (réflexivité),
    le sens ⇐ donne (u,T[u])∈F."""
    vA = _t(a)
    vu = _t(u)
    Tu = subst_t(vu, x, t)                              # T[u]
    eq_v = membre_graphe_terme(vA, t, u, "v", x, y)     # ((u,v)∈F) ⇔ (u∈A et v=T[u]), v libre
    eq_all = N.generalisation("v", eq_v)                # (∀v)(...)
    eq_Tu = instancie(eq_all, Tu)                       # ((u,T[u])∈F) ⇔ (u∈A et T[u]=T[u])
    h_inA = N.assume(appartient(vu, vA))
    wit = conjonction_intro(h_inA, N.reflexivite(Tu))   # u∈A et T[u]=T[u]
    return N.modus_ponens(wit, equivalence_arriere(eq_Tu))   # (u,T[u])∈F   [hyp u∈A]


def graphe_terme_valeur(a, t, u="u", x="x", y="y"):
    """{u ∈ A} ⊢ F(u) = T[u],   F = graphe_terme(A,T),  T[u] = (u|x)T.

    (u,T[u])∈F (lemme ci-dessus) donne u dans le domaine ; valeur_caracterisation
    (C46, sous « F fonctionnel » — déchargée par graphe_terme_fonctionnel) donne
    T[u]=F(u) ; symétrie conclut."""
    vA = _t(a)
    vu, vy = _t(u), var(y)
    Tu = subst_t(vu, x, t)                              # T[u]
    F = E.graphe_terme(vA, t, x)
    fu = E.valeur(F, vu)                                # F(u)
    cpl = graphe_terme_couple_dans(a, t, u, x, y)       # {u∈A} ⊢ (u,T[u])∈F
    # u dans le domaine : (∃y)((u,y)∈F), témoin y:=T[u]
    dom_membre = N.modus_ponens(cpl, N.s5(appartient(E.couple(vu, vy), F), Tu, y))
    # valeur_caracterisation(F,u) : {F fonctionnel, (∃y)((u,y)∈F)} ⊢ ((u,y)∈F) ⇔ (y=F(u))
    vc = valeur_caracterisation(F, vu)                  # y libre
    vc_all = N.generalisation(y, vc)                    # (∀y)(((u,y)∈F) ⇔ (y=F(u)))
    vc_Tu = instancie(vc_all, Tu)                       # ((u,T[u])∈F) ⇔ (T[u]=F(u))
    Tu_fu = N.modus_ponens(cpl, equivalence_avant(vc_Tu))   # T[u]=F(u)  [hyps: F func, u∈A]
    fu_Tu = N.modus_ponens(Tu_fu, symetrie(Tu, fu))    # F(u)=T[u]
    # décharger l'hypothèse « F fonctionnel » de valeur_caracterisation
    fu_Tu = N.modus_ponens(graphe_terme_fonctionnel(vA, t, x, y),
                           N.loi_deduction(E.est_fonctionnel(F), fu_Tu))
    # décharger l'hypothèse de domaine (∃y)((u,y)∈F)
    fu_Tu = N.modus_ponens(dom_membre,
        N.loi_deduction(existe(y, appartient(E.couple(vu, vy), F)), fu_Tu))
    return fu_Tu                                        # {u∈A} ⊢ F(u)=T[u]


# ── dom(graphe_terme(A,T)) = A ────────────────────────────────────────────────
def graphe_terme_domaine(a, t, x="x", y="y", z="z"):
    """⊢ dom(graphe_terme(A,T)) = A.

    z∈dom F ⇔ (∃y)((z,y)∈F) ⇔ (∃y)(z∈A et y=T[z]) ⇔ z∈A.  Par extension (liant z,
    cohérent avec dom/A1)."""
    vA = _t(a)
    vz, vy = var(z), var(y)
    Tz = subst_t(vz, x, t)                              # T[z]
    F = E.graphe_terme(vA, t, x)
    # caractérisation du domaine : z∈dom F ⇔ (∃y)((z,y)∈F)
    ax_dom = N.axiome(E.theorie_ensembles(), E.AXIOME_DOM)
    dom_car = instancie(instancie(ax_dom, F), vz)       # z∈dom F ⇔ (∃y)((z,y)∈F)
    # (z,y)∈F ⇔ (z∈A et y=T[z])   (membre_graphe_terme, coordonnée libre z,y ;
    # nom interne du corps « yb » ≠ y pour ne pas collisionner avec le ∃y du domaine)
    mem = membre_graphe_terme(vA, t, z, y, x, "yb")     # ((z,y)∈F) ⇔ (z∈A et y=T[z])
    ex_eq = congruence_existe(mem, y)                   # (∃y)((z,y)∈F) ⇔ (∃y)(z∈A et y=T[z])
    inA = appartient(vz, vA)
    body = et(inA, egal(vy, Tz))
    # ⇒ : (∃y)(z∈A et y=T[z]) ⇒ z∈A
    fwd = existe_elimination(
        N.loi_deduction(body, conjonction_elim_gauche(N.assume(body))), y)
    # ⇐ : z∈A ⇒ (∃y)(z∈A et y=T[z])  via témoin y:=T[z]
    h_inA = N.assume(inA)
    wit = conjonction_intro(h_inA, N.reflexivite(Tz))   # (z|y... ) = z∈A et T[z]=T[z]
    bwd = N.loi_deduction(inA, N.modus_ponens(wit, N.s5(body, Tz, y)))
    ex_inA = conjonction_intro(fwd, bwd)                # (∃y)(z∈A et y=T[z]) ⇔ z∈A
    chain = equivalence_transitivite(dom_car,
              equivalence_transitivite(ex_eq, ex_inA))  # z∈dom F ⇔ z∈A
    selfA = N.generalisation(z, conjonction_intro(a_implique_a(inA), a_implique_a(inA)))
    char_dom = N.generalisation(z, chain)
    return egalite_par_extension(char_dom, selfA, E.dom(F), vA)


# ── L'application singleton x ↦ {x} : graphe G_X ──────────────────────────────
def _singleton_graphe(x):
    """G_X := graphe_terme(X, {x}) = {(x, {x}) | x ∈ X}  (graphe de x↦{x})."""
    return E.graphe_terme(_t(x), E.singleton(var("x")), "x")


def singleton_graphe_fonctionnel(x="X"):
    """⊢ G_X est fonctionnel,   G_X = graphe de x↦{x}.   (cas T={x} de C54.)"""
    return graphe_terme_fonctionnel(_t(x), E.singleton(var("x")), "x", "y")


def singleton_graphe_domaine(x="X"):
    """⊢ dom(G_X) = X.   (la fonction x↦{x} est définie sur tout X.)"""
    return graphe_terme_domaine(_t(x), E.singleton(var("x")), "x", "y", "z")


def singleton_graphe_valeur(x="X", u="u"):
    """{u ∈ X} ⊢ G_X(u) = {u}.   (x↦{x} vaut {u} en u, pour u∈X.)"""
    return graphe_terme_valeur(_t(x), E.singleton(var("x")), u, "x", "y")


def singleton_graphe_injective(x="X"):
    """⊢ injective_dans(G_X, X).   (x↦{x} injective sur X : {u}={u'} ⇒ u=u'.)

    G_X(u)={u} et G_X(u')={u'} (valeur), donc l'hypothèse G_X(u)=G_X(u') donne
    {u}={u'}, d'où u=u' par singleton_injectif."""
    vX, vu, vup = _t(x), var("u"), var("up")
    G = _singleton_graphe(x)
    su, sup = E.singleton(vu), E.singleton(vup)
    hyp = et(et(appartient(vu, vX), appartient(vup, vX)),
             egal(E.valeur(G, vu), E.valeur(G, vup)))
    h = N.assume(hyp)
    uinX = conjonction_elim_gauche(conjonction_elim_gauche(h))      # u∈X
    upinX = conjonction_elim_droite(conjonction_elim_gauche(h))     # u'∈X
    val_eq = conjonction_elim_droite(h)                            # G(u)=G(u')
    # G(u)={u}, G(u')={u'}  (décharger l'hypothèse u∈X / u'∈X de la valeur)
    gu = N.modus_ponens(uinX, N.loi_deduction(appartient(vu, vX),
                                              singleton_graphe_valeur(x, "u")))     # G(u)={u}
    gup = N.modus_ponens(upinX, N.loi_deduction(appartient(vup, vX),
                                                singleton_graphe_valeur(x, "up")))  # G(u')={u'}
    # {u} = G(u) = G(u') = {u'}
    su_gu = N.modus_ponens(gu, symetrie(E.valeur(G, vu), su))      # {u}=G(u)
    su_sup = composer_egalites(composer_egalites(su_gu, val_eq), gup)   # {u}={u'}
    u_up = N.modus_ponens(su_sup, singleton_injectif(vu, vup))     # u=u'
    inner = N.loi_deduction(hyp, u_up)
    return N.generalisation("u", N.generalisation("up", inner))   # injective_dans(G_X, X)


# ── image(G_X, X) ⊂ P(X) ──────────────────────────────────────────────────────
def singleton_inclus(u="u", x="X"):
    """{u ∈ X} ⊢ {u} ⊂ X.   ({u} = {z | z=u}, et u∈X, donc tout z∈{u} vérifie z∈X.)

    {u}⊂X = (∀z)(z∈{u} ⇒ z∈X).  z∈{u} ⇔ z=u (singleton_membre) ; z=u et u∈X
    donnent z∈X par Leibniz."""
    from bourbaki.ensembles.ii_2_couples_produit.ensembles_couples import singleton_membre
    vX, vu, vz = _t(x), var(u), var("z")
    su = E.singleton(vu)
    h_inX = N.assume(appartient(vu, vX))
    # z∈{u} ⇒ z∈X
    hz = N.assume(appartient(vz, su))
    z_eq_u = N.modus_ponens(hz, equivalence_avant(singleton_membre(vz, vu)))   # z=u
    z_inX = N.modus_ponens(h_inX, equivalence_arriere(
        N.modus_ponens(z_eq_u, N.s6(vz, vu, "w", appartient(var("w"), vX)))))  # z∈X
    imp = N.loi_deduction(appartient(vz, su), z_inX)              # z∈{u} ⇒ z∈X
    return N.generalisation("z", imp)                            # {u}⊂X   [hyp u∈X]


def singleton_dans_parties(u="u", x="X"):
    """{u ∈ X} ⊢ {u} ∈ P(X).   ({u}⊂X (singleton_inclus) puis membre_parties.)"""
    vX, vu = _t(x), var(u)
    su = E.singleton(vu)
    incl = singleton_inclus(u, x)                                # {u}⊂X   [hyp u∈X]
    # membre_parties(X, {u}) : ({u}∈P(X)) ⇔ ({u}⊂X)  — via instance-terme
    mp = membre_parties("X", "Y")                               # (Y∈P(X)) ⇔ (Y⊂X)
    mp_all = N.generalisation("X", N.generalisation("Y", mp))
    mp_inst = instancie(instancie(mp_all, vX), su)              # ({u}∈P(X)) ⇔ ({u}⊂X)
    return N.modus_ponens(incl, equivalence_arriere(mp_inst))   # {u}∈P(X)   [hyp u∈X]


def singleton_graphe_image_incluse(x="X"):
    """⊢ image(G_X, X) ⊂ P(X).   (l'image de x↦{x} est faite de parties {u}⊂X.)

    z∈G_X⟨X⟩ ⇔ (∃t)(t∈X et (t,z)∈G_X).  Or (t,z)∈G_X ⇔ (t∈X et z={t})
    (membre_graphe_terme), donc z est de la forme {t} avec t∈X, d'où z∈P(X)
    (singleton_dans_parties + Leibniz).  Conclusion = (∀z)(z∈G⟨X⟩ ⇒ z∈P(X))."""
    vX, vz, vt = _t(x), var("z"), var("t")
    G = _singleton_graphe(x)
    PX = E.parties(vX)
    # caractérisation de l'image directe : z∈G⟨X⟩ ⇔ (∃·)(·∈X et (·,z)∈G).
    # NB : G = graphe_terme(X, {x}) contient « x » LIBRE → l'instanciation de
    # l'axiome IMAGE (liant interne « x ») α-renomme le liant en un nom frais ;
    # on récupère ce liant tel quel et on le renomme en « t ».
    ax_img = N.axiome(E.theorie_ensembles(), E.AXIOME_IMAGE)
    img_car0 = instancie(instancie(instancie(ax_img, G), vX), vz)
    # equiv(L,EX) = et(impl(L,EX), impl(EX,L)) = non(ou(non(ou(non L,EX)), non(...)))
    # → on récupère le « EX » = (∃·)(…) sur le membre droit de la 1re implication.
    impl_LtoEX = img_car0.conclusion.sous[0].sous[0].sous[0]   # ou(non L, EX) = impl(L, EX)
    rhs_ex = impl_LtoEX.sous[1]                               # EX = (∃·)(·∈X et (·,z)∈G)
    assert rhs_ex.tag == "exists"
    nom_lie = rhs_ex.lieur                                    # nom frais choisi par l'instanciation
    inner_x = et(appartient(var(nom_lie), vX), appartient(E.couple(var(nom_lie), vz), G))
    ren = alpha_existe(nom_lie, "t", inner_x)                  # (∃·)…·… ⇔ (∃t)…t…
    img_car = equivalence_transitivite(img_car0, ren)          # z∈G⟨X⟩ ⇔ (∃t)(t∈X et (t,z)∈G)
    # (t,z)∈G ⇔ (t∈X et z={t})   (membre_graphe_terme, coordonnées t,z)
    st = E.singleton(vt)                                       # {t}
    mem = membre_graphe_terme(vX, E.singleton(var("x")), "t", "z", "x", "y")  # ((t,z)∈G) ⇔ (t∈X et z={t})
    # corps existentiel : (t∈X et (t,z)∈G) ; on prouve (∃t)(...) ⇒ z∈P(X)
    body = et(appartient(vt, vX), appartient(E.couple(vt, vz), G))
    hb = N.assume(body)
    t_inX = conjonction_elim_gauche(hb)                        # t∈X
    cond = N.modus_ponens(conjonction_elim_droite(hb), equivalence_avant(mem))  # t∈X et z={t}
    z_eq_st = conjonction_elim_droite(cond)                    # z={t}
    # {t}∈P(X)  (sous t∈X), puis Leibniz z={t} → z∈P(X)
    st_inPX = N.modus_ponens(t_inX, N.loi_deduction(appartient(vt, vX),
                                                    singleton_dans_parties("t", x)))  # {t}∈P(X)
    z_inPX = N.modus_ponens(st_inPX, equivalence_arriere(
        N.modus_ponens(z_eq_st, N.s6(vz, st, "w", appartient(var("w"), PX)))))  # z∈P(X)
    ex_imp = existe_elimination(N.loi_deduction(body, z_inPX), "t")  # (∃t)(t∈X et (t,z)∈G) ⇒ z∈P(X)
    # z∈G⟨X⟩ ⇒ z∈P(X)  via img_car
    z_in_img = N.assume(appartient(vz, E.image(G, vX)))
    ex = N.modus_ponens(z_in_img, equivalence_avant(img_car))  # (∃t)(t∈X et (t,z)∈G)
    z_inPX2 = N.modus_ponens(ex, ex_imp)                       # z∈P(X)
    imp = N.loi_deduction(appartient(vz, E.image(G, vX)), z_inPX2)
    return N.generalisation("z", imp)                          # image(G_X,X) ⊂ P(X)


# ── ÉTAPE 1 : X ≤ P(X) ────────────────────────────────────────────────────────
def inf_egal_parties(x="X"):
    """⊢ X ≤ P(X).   (Cantor, étape 1 : x↦{x} injecte X dans P(X), E.III.3.)

    L'injection-témoin est G_X = graphe de x↦{x} : fonctionnelle, de domaine X,
    injective sur X, d'image incluse dans P(X).  D'où est_injection_de(G_X, X, P(X)),
    puis (∃F) est_injection_de(F, X, P(X)) = inf_egal_card(X, P(X))."""
    vX = _t(x)
    G = _singleton_graphe(x)
    PX = E.parties(vX)
    inj = conjonction_intro(conjonction_intro(conjonction_intro(
        singleton_graphe_fonctionnel(x), singleton_graphe_domaine(x)),
        singleton_graphe_injective(x)), singleton_graphe_image_incluse(x))
    # inj : est_injection_de(G_X, X, P(X))
    return N.modus_ponens(inj, N.s5(est_injection_de(var("F"), vX, PX), G, "F"))  # X ≤ P(X)


# ── Cœur logique de l'argument diagonal : ¬(P ⇔ ¬P) ───────────────────────────
def paradoxe_diagonal(p):
    """⊢ ¬(P ⇔ ¬P).   (lemme de Russell/Cantor : aucune relation n'équivaut à sa
    négation — c'est la contradiction qui fait l'argument diagonal.)

    De P⇔¬P on tire ¬P (idempotence de P⇒¬P=¬P∨¬P) puis P (par ¬P⇒P), donc
    H⇒P et H⇒¬P ; par contraposition+dni, H⇒¬H, d'où ¬H (idempotence).
    Appliqué à P = (a ∈ D) avec D = {x∈X | x∉f(x)}, c'est exactement la
    contradiction « a∈D ⇔ a∉D » obtenue pour un antécédent a de D par f."""
    from bourbaki.logique.tactiques.tactiques_abrege2 import (conjonction_elim_gauche, conjonction_elim_droite,
                                   contraposition, dni)
    from bourbaki.logique.tactiques.tactiques_abrege import syllogisme
    H = equiv(p, non(p))                                  # P ⇔ ¬P
    hH = N.assume(H)
    f = conjonction_elim_gauche(hH)                      # P ⇒ ¬P
    g = conjonction_elim_droite(hH)                      # ¬P ⇒ P
    notP = N.modus_ponens(f, N.s1(non(p)))              # ¬P   [H]  (idempotence)
    Pthm = N.modus_ponens(notP, g)                      # P    [H]
    H_imp_P = N.loi_deduction(H, Pthm)                  # H ⇒ P
    H_imp_notP = N.loi_deduction(H, notP)               # H ⇒ ¬P
    P_imp_notH = syllogisme(dni(p), contraposition(H_imp_notP))   # P ⇒ ¬H
    H_imp_notH = syllogisme(H_imp_P, P_imp_notH)        # H ⇒ ¬H
    return N.modus_ponens(H_imp_notH, N.s1(non(H)))     # ¬H = ¬(P ⇔ ¬P)


# ── ÉTAPE 2 : Card X < Card P(X) — l'inégalité STRICTE (argument diagonal) ─────
def _ex_falso(thm_a, thm_na, z):
    """Γ ⊢ A, Δ ⊢ ¬A ⟹ Γ∪Δ ⊢ Z.   (ex falso quodlibet : ¬A ⇒ (A ⇒ Z), S2.)"""
    a = thm_a.conclusion
    a_imp_z = N.modus_ponens(thm_na, N.s2(non(a), z))   # ¬A ⇒ (A ⇒ Z) appliqué : (A⇒Z)
    return N.modus_ponens(thm_a, a_imp_z)               # Z


def aucune_surjection_parties(x="X", f="F"):
    """{est_bijection_de(F, X, P(X))} ⊢ ¬ est_bijection_de(F, X, P(X)).

    LE CŒUR DE CANTOR (E.III.3).  Sous l'hypothèse que F est (le graphe d')une
    bijection de X sur P(X), on construit l'ensemble diagonal
        D := { z∈X | ¬(z ∈ F(z)) }     (diagonale_cantor(X,F), S8+A1)
    qui est une partie de X (D ⊂ X), donc D ∈ P(X).  Par surjectivité
    (image(F,X) = P(X)), D ∈ image(F,X), donc il existe d ∈ X avec (d,D) ∈ F,
    d'où F(d) = D.  Alors
        d∈D ⇔ (d∈X et ¬(d∈F(d))) ⇔ ¬(d∈F(d)) ⇔ ¬(d∈D),
    soit (d∈D) ⇔ ¬(d∈D), CONTRADICTOIRE par paradoxe_diagonal.  L'hypothèse
    « F bijection X→P(X) » se réfute donc elle-même."""
    vX, vF = _t(x), _t(f)
    PX = E.parties(vX)
    D = E.diagonale_cantor(vX, vF)
    bij = est_bijection_de_local(vX, vF, PX)
    hbij = N.assume(bij)

    # ── extraire les conjoints de est_bijection_de(F, X, P(X)) ────────────────
    # est_bijection_de = ((F fonctionnel et dom F=X) et (injective_dans(F,X) et image(F,X)=P(X)))
    func_dom = conjonction_elim_gauche(hbij)
    F_func = conjonction_elim_gauche(func_dom)                 # F fonctionnel
    inj_surj = conjonction_elim_droite(hbij)
    surj = conjonction_elim_droite(inj_surj)                   # image(F,X) = P(X)

    # ── D ⊂ X, donc D ∈ P(X) ──────────────────────────────────────────────────
    vz = var("z")
    ax_D = N.axiome(E.theorie_diagonale_cantor(vX, vF), E.axiome_diagonale_cantor(vX, vF))
    D_car_z = instancie(ax_D, vz)            # z∈D ⇔ (z∈X et ¬(z∈F(z)))
    # z∈D ⇒ z∈X
    hzD = N.assume(appartient(vz, D))
    z_inX = conjonction_elim_gauche(N.modus_ponens(hzD, equivalence_avant(D_car_z)))   # z∈X
    D_sub_X = N.generalisation("z", N.loi_deduction(appartient(vz, D), z_inX))         # D⊂X
    # D∈P(X) via membre_parties (instance-terme)
    mp = membre_parties("X", "Y")
    mp_all = N.generalisation("X", N.generalisation("Y", mp))
    mp_inst = instancie(instancie(mp_all, vX), D)               # (D∈P(X)) ⇔ (D⊂X)
    D_inPX = N.modus_ponens(D_sub_X, equivalence_arriere(mp_inst))   # D∈P(X)  [hyp bij]

    # ── surjectivité : D ∈ image(F,X), puis (∃t)(t∈X et (t,D)∈F) ──────────────
    # image(F,X)=P(X) (surj) ⇒ (D∈P(X)) ⇔ (D∈image(F,X))   (Leibniz S6, trou w)
    surj_sym = N.modus_ponens(surj, eg_symetrie(E.image(vF, vX), PX))   # P(X)=image(F,X)
    PX_img = N.modus_ponens(surj_sym,
        N.s6(PX, E.image(vF, vX), "w", appartient(D, var("w"))))   # (D∈P(X)) ⇔ (D∈image(F,X))
    D_in_img = N.modus_ponens(D_inPX, equivalence_avant(PX_img))   # D∈image(F,X)
    # axiome IMAGE : D∈image(F,X) ⇔ (∃x)(x∈X et (x,D)∈F) ; renommer le liant x→t
    ax_img = N.axiome(E.theorie_ensembles(), E.AXIOME_IMAGE)
    img_car0 = instancie(instancie(instancie(ax_img, vF), vX), D)   # D∈F⟨X⟩ ⇔ (∃x)(x∈X et (x,D)∈F)
    inner_x = et(appartient(var("x"), vX), appartient(E.couple(var("x"), D), vF))
    ren = alpha_existe("x", "t", inner_x)                          # (∃x)…x… ⇔ (∃t)…t…
    img_car = equivalence_transitivite(img_car0, ren)              # D∈F⟨X⟩ ⇔ (∃t)(t∈X et (t,D)∈F)
    ex_t = N.modus_ponens(D_in_img, equivalence_avant(img_car))    # (∃t)(t∈X et (t,D)∈F)  [hyp bij]

    # ── sous le témoin t : (t∈X et (t,D)∈F) ⇒ ¬bij  (puis éliminer ∃t) ─────────
    vt = var("t")
    body = et(appartient(vt, vX), appartient(E.couple(vt, D), vF))
    hb = N.assume(body)
    t_inX = conjonction_elim_gauche(hb)                            # t∈X
    tD_inF = conjonction_elim_droite(hb)                           # (t,D)∈F
    # F(t)=D : valeur_caracterisation(F,t) sous « F fonctionnel » et « t∈dom F »
    ft = E.valeur(vF, vt)
    t_in_dom = N.modus_ponens(tD_inF, N.s5(appartient(E.couple(vt, var("y")), vF), D, "y"))
    vc = valeur_caracterisation(vF, vt)                            # y libre
    vc_all = N.generalisation("y", vc)                            # (∀y)(((t,y)∈F)⇔(y=F(t)))
    vc_D = instancie(vc_all, D)                                   # ((t,D)∈F) ⇔ (D=F(t))
    D_eq_ft = N.modus_ponens(tD_inF, equivalence_avant(vc_D))     # D=F(t)  [hyps F func, t∈dom F]
    # décharger « F fonctionnel » et « (∃y)((t,y)∈F) »
    D_eq_ft = N.modus_ponens(F_func, N.loi_deduction(E.est_fonctionnel(vF), D_eq_ft))
    D_eq_ft = N.modus_ponens(t_in_dom, N.loi_deduction(
        existe("y", appartient(E.couple(vt, var("y")), vF)), D_eq_ft))   # D=F(t)  [hyp bij]
    ft_eq_D = N.modus_ponens(D_eq_ft, eg_symetrie(D, ft))         # F(t)=D

    # caractérisation de t : t∈D ⇔ (t∈X et ¬(t∈F(t)))
    D_car_t = instancie(ax_D, vt)                                 # t∈D ⇔ (t∈X et ¬(t∈F(t)))
    # sous t∈X : (t∈X et ¬(t∈F(t))) ⇔ ¬(t∈F(t))
    notP = non(appartient(vt, ft))
    et_simpl = _et_garde_simpl(t_inX, notP)                       # (t∈X et ¬(t∈F(t))) ⇔ ¬(t∈F(t))
    # ¬(t∈F(t)) ⇔ ¬(t∈D)   (Leibniz F(t)=D dans « t∈· », puis negation-congruence)
    in_ft_eq_in_D = N.modus_ponens(ft_eq_D,
        N.s6(ft, D, "w", appartient(vt, var("w"))))               # (t∈F(t)) ⇔ (t∈D)
    not_eq = equiv_neg(in_ft_eq_in_D)                             # ¬(t∈F(t)) ⇔ ¬(t∈D)
    # chaîner : t∈D ⇔ (t∈X et ¬(t∈F(t))) ⇔ ¬(t∈F(t)) ⇔ ¬(t∈D)
    H = equivalence_transitivite(D_car_t,
          equivalence_transitivite(et_simpl, not_eq))             # (t∈D) ⇔ ¬(t∈D)
    notH = paradoxe_diagonal(appartient(vt, D))                  # ¬((t∈D) ⇔ ¬(t∈D))
    contradiction = _ex_falso(H, notH, non(bij))                # ¬bij  [hyps bij, body]
    imp = N.loi_deduction(body, contradiction)                  # body ⇒ ¬bij   [hyp bij]
    ex_imp = existe_elimination(imp, "t")                       # (∃t)body ⇒ ¬bij  [hyp bij]
    return N.modus_ponens(ex_t, ex_imp)                         # ¬bij   [hyp bij]


def _et_garde_simpl(thm_p, q):
    """Γ ⊢ P ⟹ Γ ⊢ (P et Q) ⇔ Q.   (sous P prouvé, le conjoint P est superflu.)"""
    p = thm_p.conclusion
    # ⇒ : (P et Q) ⇒ Q
    fwd = N.loi_deduction(et(p, q), conjonction_elim_droite(N.assume(et(p, q))))
    # ⇐ : Q ⇒ (P et Q)   (P est prouvé)
    hq = N.assume(q)
    bwd = N.loi_deduction(q, conjonction_intro(thm_p, hq))
    return conjonction_intro(fwd, bwd)


def est_bijection_de_local(X, F, Y):
    """Réexpose est_bijection_de(F, X, Y) (ensembles_cardinaux) avec termes."""
    from bourbaki.cardinaux.ensembles_cardinaux import est_bijection_de as _b
    return _b(F, X, Y)


def cantor_non_equipotent(x="X"):
    """⊢ ¬ Eq(X, P(X)).   (THÉORÈME DE CANTOR, inégalité stricte, E.III.3.)

    Eq(X, P(X)) = (∃F)(F bijection de X sur P(X)).  Pour tout tel F,
    aucune_surjection_parties réfute « F bijection » (argument diagonal) : sous
    bij on a ¬bij, donc (ex falso) ¬Eq.  D'où bij ⇒ ¬Eq, puis, comme F n'est pas
    libre dans ¬Eq, (∃F)bij ⇒ ¬Eq = Eq ⇒ ¬Eq ; l'idempotence (S1) conclut ¬Eq.
    Combiné à inf_egal_parties (⊢ X ≤ P(X)), cela donne Card X < Card P(X)."""
    from bourbaki.logique.formule import existe as _ex
    vX = _t(x)
    PX = E.parties(vX)
    bij = est_bijection_de_local(vX, var("F"), PX)
    Eq = _ex("F", bij)                                          # Eq(X,P(X)) = (∃F)bij
    self_refute = aucune_surjection_parties(x, "F")            # {bij} ⊢ ¬bij
    # sous bij : ¬bij (self_refute) et bij (hyp) ⟹ ¬Eq  (ex falso)
    notEq_under_bij = _ex_falso(N.assume(bij), self_refute, non(Eq))   # {bij} ⊢ ¬Eq
    bij_imp_notEq = N.loi_deduction(bij, notEq_under_bij)      # ⊢ bij ⇒ ¬Eq
    # F non libre dans ¬Eq ⟹ (∃F)bij ⇒ ¬Eq = Eq ⇒ ¬Eq
    Eq_imp_notEq = existe_elimination(bij_imp_notEq, "F")     # ⊢ Eq ⇒ ¬Eq
    return N.modus_ponens(Eq_imp_notEq, N.s1(non(Eq)))        # ⊢ ¬Eq


def cantor_distinct(x="X"):
    """⊢ ¬(X = P(X)).   (X n'est jamais égal à son ensemble des parties, E.III.3.)

    Si X = P(X), alors de Eq(X, X) (réflexivité, ensembles_equipotence) on tire
    Eq(X, P(X)) en réécrivant le second X en P(X) (Leibniz S6) — contredisant
    cantor_non_equipotent.  D'où ¬(X = P(X))."""
    from bourbaki.cardinaux.ensembles_equipotence import equipotence_reflexive
    from bourbaki.cardinaux.ensembles_cardinaux import equipotent
    vX = _t(x)
    PX = E.parties(vX)
    eq_XX = equipotence_reflexive(x)                          # ⊢ Eq(X, X)
    notEq = cantor_non_equipotent(x)                         # ⊢ ¬Eq(X, P(X))
    h = N.assume(egal(vX, PX))                                # X = P(X)
    # réécrire Eq(X, X) → Eq(X, P(X))  (Leibniz sur le 2e argument, trou w)
    leib = N.modus_ponens(h, N.s6(vX, PX, "w", equipotent(vX, var("w"))))   # Eq(X,X)⇔Eq(X,P(X))
    eq_XPX = N.modus_ponens(eq_XX, equivalence_avant(leib))  # Eq(X, P(X))   [hyp X=P(X)]
    contra = _ex_falso(eq_XPX, notEq, non(egal(vX, PX)))     # ¬(X=P(X))      [hyp X=P(X)]
    return N.modus_ponens(N.loi_deduction(egal(vX, PX), contra),
                          N.s1(non(egal(vX, PX))))            # ⊢ ¬(X = P(X))


def cantor_strict(x="X"):
    """⊢ X < P(X).   (THÉORÈME DE CANTOR, E.III.3 : Card X < Card P(X).)

    X < P(X) := (X ≤ P(X)) et (X ≠ P(X)).  X ≤ P(X) par inf_egal_parties
    (injection x↦{x}) ; X ≠ P(X) par cantor_distinct (sinon X et P(X) seraient
    équipotents, contre cantor_non_equipotent)."""
    from bourbaki.cardinaux.ensembles_cardinaux import inf_strict_card
    le = inf_egal_parties(x)                                 # ⊢ X ≤ P(X)
    ne = cantor_distinct(x)                                  # ⊢ ¬(X = P(X))
    return conjonction_intro(le, ne)                        # ⊢ (X ≤ P(X)) et (X ≠ P(X))


__all__ = ["graphe_terme_couple_dans", "graphe_terme_valeur", "graphe_terme_domaine",
           "singleton_graphe_fonctionnel", "singleton_graphe_domaine",
           "singleton_graphe_valeur", "singleton_graphe_injective",
           "singleton_inclus", "singleton_dans_parties",
           "singleton_graphe_image_incluse", "inf_egal_parties",
           "paradoxe_diagonal", "aucune_surjection_parties",
           "cantor_non_equipotent", "cantor_distinct", "cantor_strict"]
