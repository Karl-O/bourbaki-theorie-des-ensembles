"""§III.3.2 — Bornes de l'ordre ≤ des cardinaux : 0 ≤ a  et  a ≤ a+1.

Énoncé VERBATIM (E.III.3.2, « Relation d'ordre ≤ entre cardinaux ») :
    « On a 0 ≤ x pour tout cardinal x, et 1 ≤ x pour tout cardinal x ≠ 0. »

On certifie ici, par le noyau, les bornes inférieures de ≤ qui sont tractables et
INDÉPENDANTES de Cantor–Bernstein (réservé à l'antisymétrie) :

  (1) `zero_inf_egal`  ⊢ ∅ ≤ A     (= 0 ≤ a, sens « Card(∅) ≤ Card(A) » via Card∅=∅).
      Le TÉMOIN est l'APPLICATION VIDE : son graphe ∅ est une injection de ∅ dans A.
      est_injection_de(∅, ∅, A) := ∅ fonctionnel ∧ dom ∅ = ∅ ∧ injective_dans(∅, ∅)
      ∧ image(∅,∅) ⊂ A.  Les trois premiers conjoints sont VACUEMENT vrais (aucun
      couple n'appartient à ∅) ; image(∅,∅) = ∅ ⊂ A (le vide est inclus partout).
      `cardinal_zero_inf_egal`  ⊢ Card(∅) ≤ Card(A)  en instanciant au terme Card(A).

  (2) `inf_egal_successeur`  ⊢ A ≤ A ⊔ {∅}   (= a ≤ a+1, E.III.3.2 / III.4.1).
      Le TÉMOIN est l'INJECTION CANONIQUE GAUCHE  u ↦ (u,0)  de A dans A⊔{∅}, dont
      le graphe est  F = graphe_terme(A, (x,0))  (fonction définie par un terme,
      C54).  On certifie est_injection_de(F, A, A⊔{∅}) :
        • F fonctionnel        (graphe_terme_fonctionnel) ;
        • dom F = A            (chaque u∈A a l'unique image (u,0)) ;
        • F injective sur A    (F(u)=F(u')=(·,0) ⇒ u=u' par Prop. 1 sur les couples) ;
        • image(F,A) ⊂ A⊔{∅}   (image = { (u,0) | u∈A } ⊂ A⊔{∅} par l'injection
                                gauche dans la somme disjointe).
      `cardinal_inf_egal_successeur`  ⊢ Card(A) ≤ Card(A⊔{∅}) = a ≤ a+1.

Ces deux résultats sont des Propositions/Remarques de Bourbaki DÉRIVÉES (rien
postulé) : une injection explicite est exhibée et vérifiée conjoint par conjoint.

RÉFLEXIVITÉ (X≤X / Card X≤Card X) et TRANSITIVITÉ de ≤ sont déjà certifiées
ailleurs (ensembles_cardinaux_theoremes.inf_egal_reflexif/cardinal_inf_egal_reflexif,
ensembles_cardinaux_ordre.inf_egal_transitive) — on ne les duplique pas.
"""
from __future__ import annotations

from bourbaki.logique.formule import (Terme, var, egal, et, non, appartient, existe,
                                       inclus, subst_f)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.tactiques.tactiques_abrege import syllogisme, a_implique_a
from bourbaki.logique.tactiques.tactiques_abrege2 import (conjonction_intro,
                               conjonction_elim_gauche, conjonction_elim_droite,
                               equivalence_avant, equivalence_arriere,
                               equivalence_transitivite, instancie)
from bourbaki.logique.tactiques.tactiques_abrege_egalite import (symetrie, composer_egalites,
                               congruence_terme)
from bourbaki.logique.tactiques.tactiques_abrege_quantif import existe_elimination
from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_theoremes import egalite_par_extension
from bourbaki.ensembles.ii_2_couples_produit.ensembles_couples import couple_egal_implique_composantes
from bourbaki.cardinaux.ensembles_cardinaux import (est_injection_de, inf_egal_card, cardinal)
from bourbaki.cardinaux.arithmetique.ensembles_exposant_cardinal import (
    vide_est_fonctionnel, dom_vide_egale_vide, vide_inclus)
from bourbaki.cardinaux.ensembles_vide_singleton import image_sur_vide
from bourbaki.ensembles.familles.ii_4_reunion_intersection_familles.ii_4_recollement_somme.ensembles_somme_disjointe import (somme_disjointe, ZERO,
                               injection_gauche_dans_somme)
from bourbaki.ensembles.fonctions.ii_3_6_fonction_terme.ensembles_fonction_terme import (graphe_terme_fonctionnel,
                               _inst_axiome)
from bourbaki.ensembles.fonctions.ii_3_4_fonctions_valeur.ensembles_fonctions import valeur_caracterisation


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def _ex_falso(thm_a, thm_na, cible):
    """Γ⊢A, Δ⊢¬A ⟹ Γ∪Δ⊢Z.   (ex falso : ¬A ⇒ (A ⇒ Z), S2.)"""
    a = thm_a.conclusion
    return N.modus_ponens(thm_a, N.modus_ponens(thm_na, N.s2(non(a), cible)))


def _n_in_vide(t):
    """⊢ ¬(t ∈ ∅)  pour un TERME t quelconque.   (instance de AXIOME_VIDE.)"""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_VIDE)   # (∀z)¬(z∈∅)
    return instancie(ax, t)


def _cut(thm, pairs):
    """Remplace dans `thm` chaque hypothèse `formule` par les hyps de sa `preuve`."""
    for formule, preuve in pairs:
        thm = N.modus_ponens(preuve, N.loi_deduction(formule, thm))
    return thm


# ═══════════════════════════════════════════════════════════════════════════════
# (1)  0 ≤ a   —   l'application VIDE injecte ∅ dans A
# ═══════════════════════════════════════════════════════════════════════════════
def vide_injective_sur_vide():
    """⊢ injective_dans(∅, ∅).   (le graphe vide est injectif sur ∅, vacuement.)

    injective_dans(∅,∅) = (∀u)(∀u')(((u∈∅ et u'∈∅) et ∅(u)=∅(u')) ⇒ u=u').
    L'antécédent contient u∈∅, impossible (AXIOME_VIDE) ; ex falso donne u=u'."""
    vu, vup = var("u"), var("up")
    ante = et(et(appartient(vu, E.VIDE), appartient(vup, E.VIDE)),
              egal(E.valeur(E.VIDE, vu), E.valeur(E.VIDE, vup)))
    h = N.assume(ante)
    u_in = conjonction_elim_gauche(conjonction_elim_gauche(h))   # u∈∅
    n_u = _n_in_vide(vu)                                  # ¬(u∈∅)
    u_eq_up = _ex_falso(u_in, n_u, egal(vu, vup))         # u=u'  [sous l'hypothèse]
    body = N.loi_deduction(ante, u_eq_up)
    return N.generalisation("u", N.generalisation("up", body))


def image_vide_inclus(a="A"):
    """⊢ image(∅, ∅) ⊂ A.   (l'image du vide est ∅, inclus dans tout A.)

    image(∅,∅) = ∅ (image_sur_vide instancié au graphe ∅) et ∅ ⊂ A (vide_inclus) ;
    Leibniz (S6) réécrit le sujet ∅ ↦ image(∅,∅) dans « ∅ ⊂ A »."""
    vA = _t(a)
    img_all = N.generalisation("F", image_sur_vide("F"))         # (∀F)(image(F,∅)=∅)
    img_eq = instancie(img_all, E.VIDE)                          # image(∅,∅)=∅
    vide_sub_A = vide_inclus(vA)                                 # ∅ ⊂ A
    leib = N.s6(E.image(E.VIDE, E.VIDE), E.VIDE, "w", inclus(var("w"), vA))
    equiv = N.modus_ponens(img_eq, leib)                         # (image(∅,∅)⊂A) ⇔ (∅⊂A)
    return N.modus_ponens(vide_sub_A, equivalence_arriere(equiv))   # image(∅,∅) ⊂ A


def zero_inf_egal(a="A"):
    """⊢ ∅ ≤ A.   (« 0 ≤ a », E.III.3.2 ; l'application vide injecte ∅ dans A.)

    Témoin = le graphe vide ∅ : est_injection_de(∅, ∅, A) tient par ses quatre
    conjoints (fonctionnel/dom/injectif VACUEMENT, image⊂A par ∅⊂A).  S5 témoin ∅."""
    vA = _t(a)
    func = vide_est_fonctionnel()                        # est_fonctionnel(∅)
    domeq = dom_vide_egale_vide()                        # dom ∅ = ∅
    inj = vide_injective_sur_vide()                      # injective_dans(∅, ∅)
    img = image_vide_inclus(vA)                          # image(∅,∅) ⊂ A
    injection = conjonction_intro(conjonction_intro(conjonction_intro(
        func, domeq), inj), img)                         # est_injection_de(∅, ∅, A)
    return N.modus_ponens(injection,
        N.s5(est_injection_de(var("F"), E.VIDE, vA), E.VIDE, "F"))   # ∅ ≤ A


def cardinal_zero_inf_egal(a="A"):
    """⊢ Card(∅) ≤ Card(A).   (= 0 ≤ a sur les cardinaux ; E.III.3.2.)

    On généralise ∅ ≤ A en (∀A)(∅ ≤ A) puis on INSTANCIE au TERME Card(A), ce qui
    donne ∅ ≤ Card(A) ; comme Card(∅) = ∅ (cardinal_vide_egale_vide), on réécrit le
    membre GAUCHE ∅ ↦ Card(∅) par Leibniz (S6), d'où Card(∅) ≤ Card(A) = « 0 ≤ a »."""
    from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_fini_zero import cardinal_vide_egale_vide
    vA = _t(a)
    cardA = cardinal(vA)
    zero_all = N.generalisation("A", zero_inf_egal("A"))         # (∀A)(∅ ≤ A)
    le = instancie(zero_all, cardA)                              # ∅ ≤ Card(A)
    cve = cardinal_vide_egale_vide()                            # Card(∅) = ∅
    vide_eq_cardvide = N.modus_ponens(cve, symetrie(cardinal(E.VIDE), E.VIDE))  # ∅ = Card(∅)
    leib = N.s6(E.VIDE, cardinal(E.VIDE), "w", inf_egal_card(var("w"), cardA))
    equiv = N.modus_ponens(vide_eq_cardvide, leib)             # (∅≤CardA) ⇔ (Card∅≤CardA)
    return N.modus_ponens(le, equivalence_avant(equiv))        # Card(∅) ≤ Card(A)


# ═══════════════════════════════════════════════════════════════════════════════
# (2)  a ≤ a+1   —   l'injection canonique GAUCHE  u ↦ (u,0)  de A dans A⊔{∅}
# ═══════════════════════════════════════════════════════════════════════════════
# Graphe de l'injection gauche : F = graphe_terme(A, (x,0)).  Le terme défini est
# T(x) = (x, 0) (0 = ∅).  Liants internes du graphe : « x » (variable de C54),
# « yb » (2ᵉ coord du couple-témoin, ≠ y des projections).
# Le terme défini emploie la variable « d0 » (≠ « x »/« y », témoins des axiomes
# IMAGE et DOM) : ainsi le terme F ne contient AUCUN « x » ni « y » libre, et les
# instances d'AXIOME_IMAGE/AXIOME_DOM conservent leurs liants structurels « x »/« y »
# (pas de renommage capture-évitant en « @… » qui casserait l'appariement MP).
_CV = "d0"   # variable C54 (liée méta-théoriquement dans l'assemblage de F)


def _T_gauche():
    """Terme défini T(d0) = (d0, 0)  (0 = ∅)."""
    return E.couple(var(_CV), ZERO)


def _F(a):
    """F = graphe_terme(A, (d0,0)).   (graphe de l'application u ↦ (u,0).)"""
    return E.graphe_terme(_t(a), _T_gauche(), _CV)


def _membre(a, vu, V):
    """⊢ ((u,V) ∈ F) ⇔ (u∈A et V=(u,0)).   (membre du graphe-terme, 2ᵉ coord = terme V.)

    Réduction directe de l'axiome C54 instancié au couple (u,V) : (u,V)=(x,yb) et
    x∈A et yb=(x,0) équivaut (Prop. 1 sur les couples) à u∈A et V=(u,0).  Liants
    internes x, yb ; témoins x:=u, yb:=V au retour."""
    vA = _t(a)
    vx, vy = var(_CV), var("yb")
    cuv = E.couple(vu, V)
    inst = _inst_axiome(vA, _T_gauche(), cuv, _CV, "yb")        # ((u,V)∈F)⇔(∃d0)(∃yb)body
    Tu = E.couple(vu, ZERO)                                     # (u,0)
    body = et(et(egal(cuv, E.couple(vx, vy)), appartient(vx, vA)), egal(vy, _T_gauche()))
    cible = et(appartient(vu, vA), egal(V, Tu))                 # u∈A et V=(u,0)
    # ── ⇒ ────────────────────────────────────────────────────────────────────
    hb = N.assume(body)
    eqcpl = conjonction_elim_gauche(conjonction_elim_gauche(hb))   # (u,V)=(d0,yb)
    xA = conjonction_elim_droite(conjonction_elim_gauche(hb))      # d0∈A
    yT = conjonction_elim_droite(hb)                              # yb=(d0,0)
    comps = N.modus_ponens(eqcpl, couple_egal_implique_composantes(vu, V, vx, vy))  # u=d0 et V=yb
    ux = conjonction_elim_gauche(comps)                          # u=d0
    Vyb = conjonction_elim_droite(comps)                         # V=yb
    uA = N.modus_ponens(xA, equivalence_arriere(N.modus_ponens(
        ux, N.s6(vu, vx, "w", appartient(var("w"), vA)))))       # u∈A
    xu = N.modus_ponens(ux, symetrie(vu, vx))                    # d0=u
    Tx_Tu = N.modus_ponens(xu, congruence_terme(vx, vu, E.couple(var("w"), ZERO), "w"))  # (d0,0)=(u,0)
    V_eq_Tu = composer_egalites(Vyb, composer_egalites(yT, Tx_Tu))   # V=(u,0)
    avant = existe_elimination(existe_elimination(
        N.loi_deduction(body, conjonction_intro(uA, V_eq_Tu)), "yb"), _CV)
    # ── ⇐ ────────────────────────────────────────────────────────────────────
    hc = N.assume(cible)
    refl = N.reflexivite(cuv)                                    # (u,V)=(u,V)
    wit = conjonction_intro(conjonction_intro(refl, conjonction_elim_gauche(hc)),
                            conjonction_elim_droite(hc))         # (u|d0)(V|yb)body
    body_uy = subst_f(vu, _CV, body)                            # (u|d0)body
    ex_y = N.modus_ponens(wit, N.s5(body_uy, V, "yb"))          # (∃yb)(u|d0)body
    ex_xy = N.modus_ponens(ex_y, N.s5(existe("yb", body), vu, _CV))  # (∃d0)(∃yb)body
    arriere = N.loi_deduction(cible, ex_xy)
    return equivalence_transitivite(inst, conjonction_intro(avant, arriere))


def _inst_dom_F(f, x):
    """⊢ (x ∈ dom F) ⇔ (∃y)((x,y) ∈ F).   (instance de AXIOME_DOM en F, x.)"""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_DOM)
    return instancie(instancie(ax, f), x)


def gauche_fonctionnel(a="A"):
    """⊢ est_fonctionnel(F),  F = graphe_terme(A,(d0,0)).   (C54.)"""
    return graphe_terme_fonctionnel(_t(a), _T_gauche(), _CV, "yb")


def gauche_domaine(a="A"):
    """⊢ dom(F) = A,  F = graphe_terme(A,(x,0)).   (l'injection gauche est définie sur A.)

    z∈dom F ⇔ (∃y)((z,y)∈F) [AXIOME_DOM] ;  (z,(z,0))∈F donne le témoin pour z∈A,
    réciproquement un témoin y donne z∈A (via _membre).  Par extension (A1), liant z."""
    vA = _t(a)
    F = _F(vA)
    vz, vy = var("z"), var("y")
    Tz = E.couple(vz, ZERO)                              # (z,0)
    dom_car = _inst_dom_F(F, vz)                         # z∈dom F ⇔ (∃y)((z,y)∈F)
    # ⇒ : (∃y)((z,y)∈F) ⇒ z∈A   (chaque témoin y satisfait z∈A via _membre)
    hzy = N.assume(appartient(E.couple(vz, vy), F))
    z_inA = conjonction_elim_gauche(N.modus_ponens(hzy, equivalence_avant(_membre(vA, vz, vy))))
    fwd_inner = existe_elimination(
        N.loi_deduction(appartient(E.couple(vz, vy), F), z_inA), "y")
    fwd = syllogisme(equivalence_avant(dom_car), fwd_inner)   # z∈dom F ⇒ z∈A
    # ⇐ : z∈A ⇒ z∈dom F   (témoin y:=(z,0))
    hzA = N.assume(appartient(vz, vA))
    zT_in = N.modus_ponens(conjonction_intro(hzA, N.reflexivite(Tz)),
                           equivalence_arriere(_membre(vA, vz, Tz)))   # (z,(z,0))∈F
    ex_y = N.modus_ponens(zT_in, N.s5(appartient(E.couple(vz, vy), F), Tz, "y"))  # (∃y)(z,y)∈F
    z_dom = N.modus_ponens(ex_y, equivalence_arriere(dom_car))   # z∈dom F
    bwd = N.loi_deduction(appartient(vz, vA), z_dom)
    char = N.generalisation("z", conjonction_intro(fwd, bwd))   # (∀z)(z∈dom F ⇔ z∈A)
    self_A = N.generalisation("z", conjonction_intro(
        a_implique_a(appartient(vz, vA)), a_implique_a(appartient(vz, vA))))
    return egalite_par_extension(char, self_A, E.dom(F), vA, "z")


def gauche_valeur(a="A", u="u"):
    """⊢_{u∈A}  F(u) = (u, 0),   F = graphe_terme(A,(d0,0)).

    (u,(u,0))∈F (car u∈A et (u,0)=(u,0)) ; valeur_caracterisation (C46) généralisée
    sur y puis instanciée à (u,0) donne (u,0)=F(u) sous {F fonctionnel, (∃y)(u,y)∈F} ;
    on décharge ces deux hypothèses (F fonctionnel clos, domaine via le témoin)."""
    vA, vu = _t(a), _t(u)
    F = _F(vA)
    Tu = E.couple(vu, ZERO)                              # (u,0)
    huA = N.assume(appartient(vu, vA))                   # u∈A
    uTu_in = N.modus_ponens(conjonction_intro(huA, N.reflexivite(Tu)),
                            equivalence_arriere(_membre(vA, vu, Tu)))   # (u,(u,0))∈F
    ex_y = N.modus_ponens(uTu_in, N.s5(appartient(E.couple(vu, var("y")), F), Tu, "y"))  # (∃y)(u,y)∈F
    vc = valeur_caracterisation(F, vu)                   # ((u,y)∈F)⇔(y=F(u))   [hyps func+dom]
    vc_T = instancie(N.generalisation("y", vc), Tu)      # ((u,(u,0))∈F)⇔((u,0)=F(u))
    Tu_eq_Fu = N.modus_ponens(uTu_in, equivalence_avant(vc_T))   # (u,0)=F(u)
    Fu_eq_Tu = N.modus_ponens(Tu_eq_Fu, symetrie(Tu, E.valeur(F, vu)))   # F(u)=(u,0)
    out = _cut(Fu_eq_Tu, [(E.est_fonctionnel(F), gauche_fonctionnel(vA)),
                          (existe("y", appartient(E.couple(vu, var("y")), F)), ex_y)])
    return N.loi_deduction(appartient(vu, vA), out)      # u∈A ⇒ F(u)=(u,0)


def gauche_injective(a="A"):
    """⊢ injective_dans(F, A),  F = graphe_terme(A,(d0,0)).

    Forme : (∀u)(∀u')(((u∈A et u'∈A) et F(u)=F(u')) ⇒ u=u').  F(u)=(u,0), F(u')=(u',0)
    (gauche_valeur sous u∈A / u'∈A) ; de F(u)=F(u') on tire (u,0)=(u',0), donc
    (Prop. 1 sur les couples) u=u'.  Liants u, up (= ceux de injective_dans)."""
    vA = _t(a)
    F = _F(vA)
    vu, vup = var("u"), var("up")
    Tu, Tup = E.couple(vu, ZERO), E.couple(vup, ZERO)
    ante = et(et(appartient(vu, vA), appartient(vup, vA)),
              egal(E.valeur(F, vu), E.valeur(F, vup)))
    h = N.assume(ante)
    u_inA = conjonction_elim_gauche(conjonction_elim_gauche(h))     # u∈A
    up_inA = conjonction_elim_droite(conjonction_elim_gauche(h))    # u'∈A
    Fu_Fup = conjonction_elim_droite(h)                            # F(u)=F(u')
    # F(u)=(u,0)  et  F(u')=(u',0)   (gauche_valeur déchargé par u∈A / u'∈A)
    Fu_eq = N.modus_ponens(u_inA, gauche_valeur(vA, vu))           # F(u)=(u,0)
    Fup_eq = N.modus_ponens(up_inA, gauche_valeur(vA, vup))        # F(u')=(u',0)
    # (u,0) = F(u) = F(u') = (u',0)
    Tu_eq_Fu = N.modus_ponens(Fu_eq, symetrie(E.valeur(F, vu), Tu))    # (u,0)=F(u)
    Tu_eq_Tup = composer_egalites(composer_egalites(Tu_eq_Fu, Fu_Fup), Fup_eq)   # (u,0)=(u',0)
    comps = N.modus_ponens(Tu_eq_Tup, couple_egal_implique_composantes(vu, ZERO, vup, ZERO))
    u_eq_up = conjonction_elim_gauche(comps)                       # u=u'
    inner = N.loi_deduction(ante, u_eq_up)
    return N.generalisation("u", N.generalisation("up", inner))


def gauche_image_inclus(a="A"):
    """⊢ image(F, A) ⊂ A ⊔ {∅},   F = graphe_terme(A,(d0,0)).

    z∈F⟨A⟩ ⇔ (∃x)(x∈A et (x,z)∈F) [AXIOME_IMAGE].  Sous le corps, (u,z)∈F donne
    (u∈A et z=(u,0)) (_membre), et u∈A donne (u,0)∈A⊔{∅} (injection_gauche_dans_somme) ;
    Leibniz z=(u,0) ↦ z donne z∈A⊔{∅}.  ∃-élim → F⟨A⟩ ⊂ A⊔{∅}.  Liant z."""
    vA = _t(a)
    F = _F(vA)
    S = somme_disjointe(vA, E.singleton(E.VIDE))         # A ⊔ {∅}
    vz, vx = var("z"), var("x")
    ax_img = N.axiome(E.theorie_ensembles(), E.AXIOME_IMAGE)
    img_car = instancie(instancie(instancie(ax_img, F), vA), vz)   # z∈F⟨A⟩ ⇔ (∃x)(x∈A et (x,z)∈F)
    # le témoin « x » d'AXIOME_IMAGE ne clash pas avec « d0 » (variable C54 de F) →
    # l'instance garde son liant structurel « x », appariement MP direct.
    vu = vx                                                       # témoin = « x »
    body = et(appartient(vu, vA), appartient(E.couple(vu, vz), F))
    hb = N.assume(body)
    u_inA = conjonction_elim_gauche(hb)                  # u∈A
    uz_inF = conjonction_elim_droite(hb)                 # (u,z)∈F
    z_eq_Tu = conjonction_elim_droite(N.modus_ponens(uz_inF, equivalence_avant(_membre(vA, vu, vz))))  # z=(u,0)
    # (u,0)∈A⊔{∅}   (injection gauche : B={∅})
    Tu_inS = N.modus_ponens(u_inA, injection_gauche_dans_somme(vu, vA, E.singleton(E.VIDE)))  # (u,0)∈A⊔{∅}
    # z∈A⊔{∅}  via z=(u,0)  (Leibniz)
    Tu_eq_z = N.modus_ponens(z_eq_Tu, symetrie(vz, E.couple(vu, ZERO)))   # (u,0)=z
    z_inS = N.modus_ponens(Tu_inS, equivalence_avant(N.modus_ponens(
        Tu_eq_z, N.s6(E.couple(vu, ZERO), vz, "w", appartient(var("w"), S)))))   # z∈A⊔{∅}
    inner = existe_elimination(N.loi_deduction(body, z_inS), "x")   # (∃x)body ⇒ z∈A⊔{∅}
    z_in_imp = syllogisme(equivalence_avant(img_car), inner)        # z∈F⟨A⟩ ⇒ z∈A⊔{∅}
    return N.generalisation("z", z_in_imp)               # F⟨A⟩ ⊂ A⊔{∅}


def inf_egal_successeur(a="A"):
    """⊢ A ≤ A ⊔ {∅}.   (« a ≤ a+1 », E.III.3.2 / III.4.1 ; injection gauche u↦(u,0).)

    Témoin = F = graphe_terme(A,(x,0)).  est_injection_de(F, A, A⊔{∅}) tient par ses
    quatre conjoints (gauche_fonctionnel/domaine/injective/image_inclus) ; S5 témoin F."""
    vA = _t(a)
    F = _F(vA)
    S = somme_disjointe(vA, E.singleton(E.VIDE))         # A ⊔ {∅}
    func = gauche_fonctionnel(vA)                        # F fonctionnel
    domeq = gauche_domaine(vA)                           # dom F = A
    inj = gauche_injective(vA)                           # injective_dans(F, A)
    img = gauche_image_inclus(vA)                        # image(F,A) ⊂ A⊔{∅}
    injection = conjonction_intro(conjonction_intro(conjonction_intro(
        func, domeq), inj), img)                         # est_injection_de(F, A, A⊔{∅})
    return N.modus_ponens(injection,
        N.s5(est_injection_de(var("F"), vA, S), F, "F"))   # A ≤ A⊔{∅}


def cardinal_inf_egal_successeur(a="A"):
    """⊢ Card(A) ≤ Card(A ⊔ {∅}).   (= a ≤ a+1 sur les cardinaux ; E.III.3.2 / III.4.1.)

    On généralise A ≤ A⊔{∅} en (∀A)(A ≤ A⊔{∅}) puis on INSTANCIE au TERME Card(A) :
    Card(A) ≤ Card(A) ⊔ {∅}.  (a+1 = Card(A⊔{∅}) ; ici le membre droit est la somme
    disjointe du cardinal Card(A) avec {∅}, conforme au successeur cardinal.)"""
    vA = _t(a)
    succ_all = N.generalisation("A", inf_egal_successeur("A"))    # (∀A)(A ≤ A⊔{∅})
    return instancie(succ_all, cardinal(vA))                     # Card(A) ≤ Card(A)⊔{∅}


__all__ = ["vide_injective_sur_vide", "image_vide_inclus",
           "zero_inf_egal", "cardinal_zero_inf_egal",
           "gauche_fonctionnel", "gauche_domaine", "gauche_valeur",
           "gauche_injective", "gauche_image_inclus",
           "inf_egal_successeur", "cardinal_inf_egal_successeur"]
