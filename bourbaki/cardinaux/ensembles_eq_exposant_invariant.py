"""§III.3 — INVARIANCE DE 𝓕(·;A) PAR ÉQUIPOTENCE (lemme-clé pour l'arithmétique
cardinale exponentielle) :

        ⊢  Eq(X, Y)  ⇒  Eq( 𝓕(X;A) , 𝓕(Y;A) )

c.-à-d. « l'espace de fonctions respecte l'équipotence » : si X et Y sont
équipotents, alors 𝓕(X;A) et 𝓕(Y;A) le sont aussi.

ROUTE = CANTOR–BERNSTEIN (deux injections, AUCUNE surjectivité de l'injection) :
  Λ  : 𝓕(X;A) ↪ 𝓕(Y;A)   g ↦ ((K_g, Y), A),  K_g = { (e, g(φ⁻¹(e))) | e∈Y }
  Λ' : 𝓕(Y;A) ↪ 𝓕(X;A)   h ↦ ((K_h, X), A),  K_h = { (d, h(φ(d)))  | d∈X }
puis cantor_bernstein ⊢ Eq(𝓕(X;A), 𝓕(Y;A)).

Le tout sous le témoin F de Eq(X,Y) (F = graphe d'une bijection X→Y) ;
φ := F (un GRAPHE — valeur(F,d) directe), φ⁻¹ := reciproque(F) (graphe Y→X).

BUILDER GÉNÉRIQUE  `injection_via_pointmap(S, T, m)`  ⊢ inf_egal_card(𝓕(S;A), 𝓕(T;A))
sous l'hypothèse que m:T→S est un graphe-bijection (est_bijection_de(m,T,S)).
  • Direction 1 :  S=X, T=Y, m=reciproque(F)      (𝓕(X;A) ≤ 𝓕(Y;A))
  • Direction 2 :  S=Y, T=X, m=F                   (𝓕(Y;A) ≤ 𝓕(X;A))

K_g := graphe_terme(T, valeur(graphe_de(g), valeur(m,e,«m»), «m»), «e»).
  - bien-définition : valeur(m,e)∈S (m bijection : valeur dans image=S) +
    PONT valeur_dans_codomaine ⇒ g(m(e))∈A ⇒ K_g⊂T×A ⇒ K_g∈A^T ⇒ triple∈𝓕(T;A).
  - injectivité : K_g₁=K_g₂ ⇒ ∀e∈T g₁(m(e))=g₂(m(e)) ; m surjective (image=S) ⇒
    ∀s∈S g₁(s)=g₂(s) ⇒ (application_egale_par_valeurs) g₁=g₂.

theorie_ensembles INCHANGÉE (22 axiomes) ; AUCUN fichier existant modifié.
"""
from __future__ import annotations

from bourbaki.logique.formule import (Terme, var, egal, et, non, ou, impl,
                     appartient, existe, pourtout, inclus, subst_t, subst_f)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.logique.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, equivalence_transitivite, instancie,
    cas)
from bourbaki.logique.tactiques.tactiques_abrege_quantif import (
    existe_elimination, alpha_existe)
from bourbaki.logique.tactiques.tactiques_abrege_egalite import (
    symetrie, composer_egalites, congruence_terme)

from bourbaki.cardinaux.ensembles_cardinaux import (
    est_injection_de, inf_egal_card, equipotent, est_bijection_de)
from bourbaki.cardinaux.arithmetique.ensembles_graphe_de import (
    graphe_de, graphe_de_triple)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# ═══════════════════════════════════════════════════════════════════════════════
#  LIANTS sûrs (cf. PIÈGES) :
#    _PT = point courant du graphe_terme K_g ; _VB = liant τ des valeurs internes.
#    Les valeurs g(m(e)) figurent DANS un graphe_terme quantifié sur « y », donc le
#    τ interne utilise « m » (≠ y,x,z,e,a,b et ≠ noms-fonction g1,g2).
# ═══════════════════════════════════════════════════════════════════════════════
_PT = "e"          # point courant du graphe-terme K_g
_VBI = "k"         # liant τ de la valeur INTERNE  m(e) = valeur(m,e,«k»)  (lettre unique)
_VBO = "r"         # liant τ de la valeur EXTERNE  g(m(e)) = valeur(graphe_de g, m(e),«r»)
_VB = _VBI         # rétro-compat
_POINT = "g"       # point courant du graphe-terme externe W (la fonction)


def _cut(thm, paires):
    """Remplace chaque hypothèse `hyp` de `thm` par sa preuve, via loi_deduction+MP."""
    out = thm
    for hyp_formule, preuve in paires:
        out = N.modus_ponens(preuve, N.loi_deduction(hyp_formule, out))
    return out


def _membre_produit(u, v, a, b):
    """⊢ ((u,v) ∈ A×B) ⇔ (u∈A et v∈B)."""
    from bourbaki.ensembles.familles.ensembles_produit import couple_dans_produit_ssi
    return couple_dans_produit_ssi(_t(u), _t(v), _t(a), _t(b))


# ═══════════════════════════════════════════════════════════════════════════════
#  LE PONT « valeur d'un graphe » avec liant τ paramétré _VB (= « m »).
#  Re-dérivation capture-safe de couple_valeur_dans_graphe / valeur_dans_codomaine.
# ═══════════════════════════════════════════════════════════════════════════════
def _couple_valeur_q(g, e, x, binder=_VBI):
    """{dom G = E, x ∈ E} ⊢ (x, G(x)) ∈ G,  G(x) = valeur(G,x,binder).

    `binder` DOIT être absent (non lié) du terme x sinon le renommage-α capture :
    pour le point composé m(e) (qui contient τ«q»), prendre binder=«r»."""
    vG, vE, vx = _t(g), _t(e), _t(x)
    vq = var(binder)
    h_dom = N.assume(egal(E.dom(vG), vE))
    h_xin = N.assume(appartient(vx, vE))
    leib = N.s6(E.dom(vG), vE, "w", appartient(vx, var("w")))
    x_in_dom = N.modus_ponens(h_xin, equivalence_arriere(N.modus_ponens(h_dom, leib)))
    ax_dom = N.axiome(E.theorie_ensembles(), E.AXIOME_DOM)
    dom_car = instancie(instancie(ax_dom, vG), vx)
    inner_y = appartient(E.couple(vx, var("y")), vG)
    ren = alpha_existe("y", binder, inner_y)
    dom_car_q = equivalence_transitivite(dom_car, ren)
    ex_q = N.modus_ponens(x_in_dom, equivalence_avant(dom_car_q))
    r = appartient(E.couple(vx, vq), vG)
    return N.modus_ponens(ex_q, N.existe_temoin(r, binder))


def _valeur_codomaine_q(g, e, f, x, binder=_VBI):
    """{G ⊂ E×F, dom G = E, x ∈ E} ⊢ G(x) ∈ F,  G(x) = valeur(G,x,binder)."""
    from bourbaki.ensembles.familles.ensembles_produit import couple_dans_produit_ssi
    vG, vE, vF, vx = _t(g), _t(e), _t(f), _t(x)
    fx = E.valeur(vG, vx, binder)
    h_incl = N.assume(inclus(vG, E.produit(vE, vF)))
    cpl = _couple_valeur_q(vG, vE, vx, binder)
    incl_inst = instancie(h_incl, E.couple(vx, fx))
    in_prod = N.modus_ponens(cpl, incl_inst)
    ssi = couple_dans_produit_ssi(vx, fx, vE, vF)
    return conjonction_elim_droite(
        N.modus_ponens(in_prod, equivalence_avant(ssi)))


def _membre_graphe_terme_z(a, t, x, z="z", y="y"):
    """⊢ (z∈F) ⇔ (∃x)(∃y)(z=(x,y) et x∈A et y=T),  F=graphe_terme(A,T)."""
    va = _t(a)
    ax = N.axiome(E.theorie_graphe_terme(va, t, x, y, z),
                  E.axiome_graphe_terme(va, t, x, y, z))
    return instancie(ax, _t(z))


# ═══════════════════════════════════════════════════════════════════════════════
#  K_g  et ses propriétés structurelles.
# ───────────────────────────────────────────────────────────────────────────────
#   m(e)   := valeur(m, e, «m»)            (φ⁻¹(e) ou φ(d) — m est un GRAPHE)
#   g(m(e)) := valeur(graphe_de(g), m(e), «m»)
#   K_g    := graphe_terme(T, g(m(e)), «e»)
# ═══════════════════════════════════════════════════════════════════════════════
def _val_m(m):
    """m(e) = valeur(m, e, «q»)   (e = point courant _PT ; binder INTERNE _VBI)."""
    return E.valeur(_t(m), var(_PT), _VBI)


def _val_K(g, m):
    """g(m(e)) = valeur(graphe_de(g), m(e), «r»)   (binder EXTERNE _VBO)."""
    return E.valeur(graphe_de(_t(g)), _val_m(m), _VBO)


def K_g(g, t, m):
    """K_g := { (e, g(m(e))) | e∈T }   (graphe-terme, niveau GRAPHE)."""
    return E.graphe_terme(_t(t), _val_K(g, m), _PT)


def K_g_fonctionnelle(g, t, m):
    """⊢ est_fonctionnel(K_g).   (graphe-terme toujours fonctionnel, C54.)"""
    from bourbaki.ensembles.fonctions.ensembles_fonction_terme import graphe_terme_fonctionnel
    return graphe_terme_fonctionnel(_t(t), _val_K(g, m), _PT, "y")


def K_g_domaine(g, t, m):
    """⊢ dom(K_g) = T."""
    from bourbaki.cardinaux.ensembles_cantor import graphe_terme_domaine
    return graphe_terme_domaine(_t(t), _val_K(g, m), _PT, "y", "z")


# ═══════════════════════════════════════════════════════════════════════════════
#  m(e) ∈ S   pour e∈T   (m : T→S graphe-bijection ⇒ image(m,T)=S ⊇ {m(e)}).
# ═══════════════════════════════════════════════════════════════════════════════
def _inst_image_m(g, xset, y):
    """⊢ (y ∈ G⟨X⟩) ⇔ (∃x)(x∈X et (x,y)∈G).   (AXIOME_IMAGE, liant interne « x ».)"""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_IMAGE)
    return instancie(instancie(instancie(ax, _t(g)), _t(xset)), _t(y))


def _m_val_dans_image(m, t, point):
    """{ dom m = T, point ∈ T } ⊢ m(point) ∈ image(m, T),  m(point)=valeur(m,point,«m»).

    (point, m(point))∈m via _couple_valeur_q ; témoin point∈T ⇒ (∃x)(x∈T et
    (x,m(point))∈m) ⇒ m(point)∈m⟨T⟩.  Le point d'évaluation `point` doit éviter le
    liant interne « x » de AXIOME_IMAGE (ici on passe un terme/variable ≠ x)."""
    vm, vt, vp = _t(m), _t(t), _t(point)
    mp = E.valeur(vm, vp, _VB)                          # m(point)
    cpl = _couple_valeur_q(vm, vt, vp)                  # {dom m=T, point∈T} ⊢ (point,m(point))∈m
    ii = _inst_image_m(vm, vt, mp)                      # m(point)∈m⟨T⟩ ⇔ (∃x)(x∈T et (x,m(point))∈m)
    h_pt = N.assume(appartient(vp, vt))                 # point∈T
    wit = conjonction_intro(h_pt, cpl)                  # point∈T et (point,m(point))∈m
    body = et(appartient(var("x"), vt), appartient(E.couple(var("x"), mp), vm))
    ex = N.modus_ponens(wit, N.s5(body, vp, "x"))       # (∃x)(x∈T et (x,m(point))∈m)
    return N.modus_ponens(ex, equivalence_arriere(ii))  # m(point)∈m⟨T⟩


def _m_val_dans_S(m, s, t, point):
    """{ est_bijection_de(m, T, S), point ∈ T } ⊢ m(point) ∈ S,  m(point)=valeur(m,point,«m»).

    est_bijection_de donne dom m=T (2ᵉ conjoint) et image(m,T)=S (surjectivité,
    dernier conjoint de est_bijective).  m(point)∈image(m,T)=S."""
    vm, vs, vt, vp = _t(m), _t(s), _t(t), _t(point)
    mp = E.valeur(vm, vp, _VB)
    h_bij = N.assume(est_bijection_de(vm, vt, vs))      # bijection m:T→S
    # conjoints : ((m fonct et dom m=T) et est_bijective(m,T,S))
    dom_eq = conjonction_elim_droite(conjonction_elim_gauche(h_bij))   # dom m=T
    bijec = conjonction_elim_droite(h_bij)              # est_bijective(m,T,S)=inj et image=S
    img_eq = conjonction_elim_droite(bijec)             # image(m,T)=S
    # m(point)∈image(m,T)  (décharger dom m=T)
    in_img = _cut(_m_val_dans_image(vm, vt, vp), [(egal(E.dom(vm), vt), dom_eq)])
    # image(m,T)=S ⇒ (m(point)∈image(m,T) ⇔ m(point)∈S) ⇒ m(point)∈S
    return N.modus_ponens(in_img, equivalence_avant(N.modus_ponens(img_eq,
        N.s6(E.image(vm, vt), vs, "w", appartient(mp, var("w"))))))   # m(point)∈S


# ═══════════════════════════════════════════════════════════════════════════════
#  BIEN-DÉFINITION :  K_g ⊂ T×A  sous { graphe_de(g)⊂S×A, dom graphe_de(g)=S,
#                                       est_bijection_de(m,T,S) }.
#   Pour z∈K_g : z=(e,y), e∈T, y=g(m(e)).  m(e)∈S (_m_val_dans_S), donc g(m(e))∈A
#   (PONT _valeur_codomaine_q sur G=graphe_de(g) au point m(e)), d'où (e,y)∈T×A.
# ═══════════════════════════════════════════════════════════════════════════════
def K_g_inclus(g, s, t, m):
    """{ graphe_de(g)⊂S×A, dom graphe_de(g)=S, est_bijection_de(m,T,S) } ⊢ K_g ⊂ T×A.

    A est laissé symbolique via _aA (cf. injection_via_pointmap) ; ici on passe A=var('A').
    """
    return _K_g_inclus(_t(g), var("A"), _t(s), _t(t), _t(m))


def _K_g_inclus(vg, va, vs, vt, vm):
    G = graphe_de(vg)
    K = K_g(vg, vt, vm)
    T = _val_K(vg, vm)                                # g(m(e))  (point e)
    TA = E.produit(vt, va)                           # T×A
    ve, vy, vz = var(_PT), var("y"), var("z")
    me = _val_m(vm)                                  # m(e)

    hyp_incl = N.assume(inclus(G, E.produit(vs, va)))   # G ⊂ S×A
    hyp_dom = N.assume(egal(E.dom(G), vs))              # dom G = S

    car = _membre_graphe_terme_z(vt, T, _PT, "z", "y")  # z∈K_g ⇔ (∃e)(∃y)(z=(e,y) et e∈T et y=T_val)
    body = et(et(egal(vz, E.couple(ve, vy)), appartient(ve, vt)), egal(vy, T))
    hb = N.assume(body)
    z_eq = conjonction_elim_gauche(conjonction_elim_gauche(hb))   # z=(e,y)
    eT = conjonction_elim_droite(conjonction_elim_gauche(hb))     # e∈T
    y_eq_T = conjonction_elim_droite(hb)                          # y=g(m(e))
    # m(e)∈S  (décharger e∈T ; bijection reste hyp)
    me_in_S = _cut(_m_val_dans_S(vm, vs, vt, ve), [(appartient(ve, vt), eT)])  # m(e)∈S
    # g(m(e))∈A  (PONT, point m(e))
    vdc = _valeur_codomaine_q(G, vs, va, me, _VBO)   # {G⊂S×A, dom G=S, m(e)∈S} ⊢ g(m(e))∈A
    T_in_A = _cut(vdc, [
        (inclus(G, E.produit(vs, va)), hyp_incl),
        (egal(E.dom(G), vs), hyp_dom),
        (appartient(me, vs), me_in_S)])              # g(m(e))∈A
    y_in_A = N.modus_ponens(T_in_A, equivalence_arriere(N.modus_ponens(
        y_eq_T, N.s6(vy, T, "w", appartient(var("w"), va)))))     # y∈A
    ey_in_prod = N.modus_ponens(conjonction_intro(eT, y_in_A),
        equivalence_arriere(_membre_produit(ve, vy, vt, va)))      # (e,y)∈T×A
    z_in_prod = N.modus_ponens(ey_in_prod, equivalence_arriere(N.modus_ponens(
        z_eq, N.s6(vz, E.couple(ve, vy), "w", appartient(var("w"), TA)))))   # z∈T×A
    ex_imp = existe_elimination(existe_elimination(
        N.loi_deduction(body, z_in_prod), "y"), _PT)               # (∃e)(∃y)body ⇒ z∈T×A
    h_z = N.assume(appartient(vz, K))
    ex = N.modus_ponens(h_z, equivalence_avant(car))              # (∃e)(∃y)body
    z_in_TA = N.modus_ponens(ex, ex_imp)                          # z∈T×A
    imp_z = N.loi_deduction(appartient(vz, K), z_in_TA)           # z∈K_g ⇒ z∈T×A
    return N.generalisation("z", imp_z)                          # K_g ⊂ T×A


# ═══════════════════════════════════════════════════════════════════════════════
#  K_g ∈ A^T   et   ((K_g,T),A) ∈ 𝓕(T;A).
# ═══════════════════════════════════════════════════════════════════════════════
def _dans_exposant(va, vT, RG, incl_thm, func_thm, dom_thm):
    """{hyps de incl_thm} ⊢ RG ∈ A^T   (axiome_exposant ⇐)."""
    ax = N.axiome(E.theorie_exposant(vT, va), E.axiome_exposant(vT, va))
    car = instancie(ax, RG)
    corps = conjonction_intro(conjonction_intro(incl_thm, func_thm), dom_thm)
    return N.modus_ponens(corps, equivalence_arriere(car))


def _triple_dans_applications(va, vT, RG, in_exp_thm):
    """{hyps de in_exp_thm} ⊢ ((RG,T),A) ∈ 𝓕(T;A)   (axiome_applications ⇐, témoin RG)."""
    triple = E.couple(E.couple(RG, vT), va)
    ax = N.axiome(E.theorie_applications(vT, va, "t", "G"),
                  E.axiome_applications(vT, va, "t", "G"))
    car = instancie(ax, triple)
    cible = et(egal(triple, E.couple(E.couple(var("G"), vT), va)),
               appartient(var("G"), E.exposant(vT, va)))
    wit = conjonction_intro(N.reflexivite(triple), in_exp_thm)
    ex = N.modus_ponens(wit, N.s5(cible, RG, "G"))
    return N.modus_ponens(ex, equivalence_arriere(car))


def triple_K_dans_applications(g, s, t, m):
    """{ graphe_de(g)⊂S×A, dom graphe_de(g)=S, est_bijection_de(m,T,S) }
       ⊢ ((K_g,T),A) ∈ 𝓕(T;A).   (Λ(g) BIEN DÉFINIE en tant qu'application T→A.)"""
    vg, vs, vt, vm = _t(g), _t(s), _t(t), _t(m)
    va = var("A")
    RG = K_g(vg, vt, vm)
    in_exp = _dans_exposant(va, vt, RG,
        _K_g_inclus(vg, va, vs, vt, vm),
        K_g_fonctionnelle(vg, vt, vm),
        K_g_domaine(vg, vt, vm))
    return _triple_dans_applications(va, vt, RG, in_exp)


# ═══════════════════════════════════════════════════════════════════════════════
#  DÉCHARGE des hyps structurelles via  g∈𝓕(S;A)  (témoin G, graphe_de_triple).
#   De g∈𝓕(S;A) : témoin G avec g=((G,S),A), G∈A^S ; axiome_exposant ⇒ G⊂S×A,
#   dom G=S ; graphe_de_triple+Leibniz ⇒ graphe_de(g)=G ⇒ les deux faits voulus.
# ═══════════════════════════════════════════════════════════════════════════════
def _hyp_incl_struct(vg, va, vs):
    """La formule  graphe_de(g) ⊂ S×A."""
    return inclus(graphe_de(vg), E.produit(vs, va))


def _hyp_dom_struct(vg, vs):
    """La formule  dom(graphe_de(g)) = S."""
    return egal(E.dom(graphe_de(vg)), vs)


def triple_K_sous_appartenance(g, s, t, m):
    """{ g ∈ 𝓕(S;A), est_bijection_de(m,T,S) } ⊢ ((K_g,T),A) ∈ 𝓕(T;A).

    BIEN-DÉFINITION COMPLÈTE de Λ : les hyps structurelles sur graphe_de(g) sont
    déchargées par g∈𝓕(S;A) (décomposition générique, témoin G éliminé)."""
    from bourbaki.ensembles.fonctions.ensembles_application_valeur import (
        _conjoints_application, _exposant_conjoints, _graphe_de_f_egal_G)
    vg, vs, vt, vm = _t(g), _t(s), _t(t), _t(m)
    va = var("A")
    vG = var("G")
    triple_g = E.couple(E.couple(vG, vs), va)             # ((G,S),A)
    body = et(egal(vg, triple_g), appartient(vG, E.exposant(vs, va)))  # g=((G,S),A) et G∈A^S

    hb = N.assume(body)
    f_eq = conjonction_elim_gauche(hb)                    # g=((G,S),A)
    G_in_exp = conjonction_elim_droite(hb)                # G∈A^S
    # axiome_exposant ⇒ G⊂S×A, dom G=S
    g_incl, _g_func, g_dom = _exposant_conjoints(vG, vs, va, G_in_exp)  # G⊂S×A, fonct, dom G=S
    # graphe_de(g)=G
    gr_eq = _graphe_de_f_egal_G(vg, vs, va, vG, f_eq)     # graphe_de(g)=G
    grg = graphe_de(vg)
    incl_grg = N.modus_ponens(g_incl, equivalence_arriere(N.modus_ponens(gr_eq,
        N.s6(grg, vG, "w", inclus(var("w"), E.produit(vs, va))))))     # gr(g)⊂S×A
    dom_grg = N.modus_ponens(g_dom, equivalence_arriere(N.modus_ponens(gr_eq,
        N.s6(grg, vG, "w", egal(E.dom(var("w")), vs)))))               # dom gr(g)=S
    # décharger les deux hyps structurelles de triple_K_dans_applications
    base = triple_K_dans_applications(vg, vs, vt, vm)     # {gr⊂.., dom gr=.., bij} ⊢ triple∈𝓕(T;A)
    base = _cut(base, [(_hyp_incl_struct(vg, va, vs), incl_grg),
                       (_hyp_dom_struct(vg, vs), dom_grg)])  # {body, bij} ⊢ triple∈𝓕(T;A)
    inner = existe_elimination(N.loi_deduction(body, base), "G")   # (∃G)body ⇒ triple∈𝓕(T;A)
    # (∃G)body  vient de g∈𝓕(S;A) (axiome_applications)
    triple_g2 = E.couple(E.couple(vG, vs), va)
    ax = N.axiome(E.theorie_applications(vs, va, "t", "G"),
                  E.axiome_applications(vs, va, "t", "G"))
    car = instancie(ax, vg)                               # g∈𝓕(S;A) ⇔ (∃G)body
    h_app = N.assume(appartient(vg, E.applications(vs, va)))
    ex_body = N.modus_ponens(h_app, equivalence_avant(car))   # (∃G)body  [g∈𝓕(S;A)]
    return N.modus_ponens(ex_body, inner)                 # triple∈𝓕(T;A)  [g∈𝓕(S;A), bij]


# ═══════════════════════════════════════════════════════════════════════════════
#  L'INJECTION  Λ : 𝓕(S;A) ↪ 𝓕(T;A),  témoin W = graphe de Λ (graphe_terme).
#   Λ(g) := ((K_g,T),A),  W := graphe_terme(𝓕(S;A), Λ(g), «g»).
# ═══════════════════════════════════════════════════════════════════════════════
def _source(s):
    """𝓕(S;A)   (source / domaine de Λ)."""
    return E.applications(_t(s), var("A"))


def _but(t):
    """𝓕(T;A)   (but / codomaine de Λ)."""
    return E.applications(_t(t), var("A"))


def _lambda_valeur(g, t, m):
    """Λ(g) := ((K_g,T),A)   (l'application T→A image de g par Λ)."""
    return E.couple(E.couple(K_g(g, t, m), _t(t)), var("A"))


def W_lambda(s, t, m):
    """W := graphe_terme( 𝓕(S;A) , Λ(g) , «g» )   (le GRAPHE de Λ)."""
    vs, vt, vm = _t(s), _t(t), _t(m)
    return E.graphe_terme(_source(vs), _lambda_valeur(var(_POINT), vt, vm), _POINT)


def W_lambda_fonctionnel(s, t, m):
    """⊢ est_fonctionnel(W)."""
    from bourbaki.ensembles.fonctions.ensembles_fonction_terme import graphe_terme_fonctionnel
    vs, vt, vm = _t(s), _t(t), _t(m)
    return graphe_terme_fonctionnel(_source(vs), _lambda_valeur(var(_POINT), vt, vm), _POINT, "y")


def W_lambda_domaine(s, t, m):
    """⊢ dom(W) = 𝓕(S;A)."""
    from bourbaki.cardinaux.ensembles_cantor import graphe_terme_domaine
    vs, vt, vm = _t(s), _t(t), _t(m)
    return graphe_terme_domaine(_source(vs), _lambda_valeur(var(_POINT), vt, vm), _POINT, "y", "z")


def W_lambda_valeur(point_nom, s, t, m):
    """{g ∈ 𝓕(S;A)} ⊢ W(g) = Λ(g).   (point d'évaluation = NOM.)"""
    from bourbaki.cardinaux.ensembles_cantor import graphe_terme_valeur
    if not isinstance(point_nom, str):
        raise ValueError("W_lambda_valeur : point = NOM")
    vs, vt, vm = _t(s), _t(t), _t(m)
    return graphe_terme_valeur(_source(vs), _lambda_valeur(var(_POINT), vt, vm),
                               point_nom, _POINT, "y")


def _lambda_cod_en_point(vs, vt, vm, vg, g_in_thm):
    """{g∈𝓕(S;A), bij} ⊢ Λ(g) ∈ 𝓕(T;A)  (instanciation-terme au point g)."""
    base = triple_K_sous_appartenance(var(_POINT), vs, vt, vm)  # {pt∈𝓕(S;A),bij} ⊢ Λ(pt)∈𝓕(T;A)
    base_imp = N.loi_deduction(appartient(var(_POINT), _source(vs)), base)
    gen = N.generalisation(_POINT, base_imp)
    inst = instancie(gen, vg)                             # g∈𝓕(S;A) ⇒ Λ(g)∈𝓕(T;A)  [bij]
    return N.modus_ponens(g_in_thm, inst)                 # Λ(g)∈𝓕(T;A)  [g∈𝓕(S;A), bij]


def W_lambda_image_incluse(s, t, m):
    """{ est_bijection_de(m,T,S) } ⊢ image(W, 𝓕(S;A)) ⊂ 𝓕(T;A).   (BIEN-DÉFINITION.)"""
    vs, vt, vm = _t(s), _t(t), _t(m)
    dom = _source(vs)
    cod = _but(vt)
    W = W_lambda(vs, vt, vm)
    LAM = _lambda_valeur(var(_POINT), vt, vm)             # Λ(g), point g
    vz, vk = var("z"), var("t")
    from bourbaki.ensembles.fonctions.ensembles_fonction_terme import membre_graphe_terme

    ax_img = N.axiome(E.theorie_ensembles(), E.AXIOME_IMAGE)
    img0 = instancie(instancie(instancie(ax_img, W), dom), vz)
    impl_LtoEX = img0.conclusion.sous[0].sous[0].sous[0]
    rhs_ex = impl_LtoEX.sous[1]
    assert rhs_ex.tag == "exists"
    nom = rhs_ex.lieur
    inner = et(appartient(var(nom), dom), appartient(E.couple(var(nom), vz), W))
    ren = alpha_existe(nom, "t", inner)
    img_car = equivalence_transitivite(img0, ren)         # z∈W⟨dom⟩ ⇔ (∃t)(t∈dom et (t,z)∈W)

    mem = membre_graphe_terme(dom, LAM, "t", "z", _POINT, "y")  # ((t,z)∈W)⇔(t∈dom et z=Λ[t])
    Lam_t = subst_t(vk, _POINT, LAM)                      # Λ(t)
    body = et(appartient(vk, dom), appartient(E.couple(vk, vz), W))
    hb = N.assume(body)
    t_in = conjonction_elim_gauche(hb)
    tz_in = conjonction_elim_droite(hb)
    cond = N.modus_ponens(tz_in, equivalence_avant(mem))
    z_eq = conjonction_elim_droite(cond)                  # z=Λ(t)
    lam_t_in = _lambda_cod_en_point(vs, vt, vm, vk, t_in)  # Λ(t)∈cod  [bij]
    z_in_cod = N.modus_ponens(lam_t_in, equivalence_arriere(N.modus_ponens(
        z_eq, N.s6(vz, Lam_t, "w", appartient(var("w"), cod)))))   # z∈cod
    ex_imp = existe_elimination(N.loi_deduction(body, z_in_cod), "t")
    h_z = N.assume(appartient(vz, E.image(W, dom)))
    ex = N.modus_ponens(h_z, equivalence_avant(img_car))
    z_in = N.modus_ponens(ex, ex_imp)
    return N.generalisation("z", N.loi_deduction(appartient(vz, E.image(W, dom)), z_in))


# ═══════════════════════════════════════════════════════════════════════════════
#  INJECTIVITÉ de Λ  :  K_g₁ = K_g₂  ⇒  g₁ = g₂.
# ───────────────────────────────────────────────────────────────────────────────
#   K_g₁=K_g₂ ⇒ (∀e∈T) g₁(m(e))=g₂(m(e))  (graphe_terme_valeur) ;  m surjective
#   (image=S) : ∀s∈S, s=m(e) pour un e∈T, d'où g₁(s)=g₂(s) ;  application_egale_par
#   _valeurs ⇒ g₁=g₂.   (binders : valeur interne « qo » rebindée en « y ».)
# ═══════════════════════════════════════════════════════════════════════════════
def _valeur_eq_de_couple(vm, ve, vs):
    """{ est_fonctionnel(m), (e,s)∈m } ⊢ valeur(m,e,«qi») = s.

    valeur_caracterisation (C46) : ((e,y)∈m)⇔(y=m(e)) sous {m fonct, (∃y)((e,y)∈m)} ;
    (e,s)∈m donne le témoin de l'existentielle et, par le sens ⇒, s=m(e) (binder y),
    rebindé en « qi » (α-tau)."""
    from bourbaki.cardinaux.ensembles_bijection import valeur_caracterisation
    h_func = N.assume(E.est_fonctionnel(vm))
    h_cpl = N.assume(appartient(E.couple(ve, vs), vm))      # (e,s)∈m
    ex = N.modus_ponens(h_cpl, N.s5(appartient(E.couple(ve, var("y")), vm), vs, "y"))  # (∃y)((e,y)∈m)
    car = valeur_caracterisation(vm, ve)                    # {m fonct,(∃y)…} ⊢ ((e,y)∈m)⇔(y=m(e))
    car = _cut(car, [(E.est_fonctionnel(vm), h_func),
                     (existe("y", appartient(E.couple(ve, var("y")), vm)), ex)])
    # instancier le ssi en y:=s : ((e,s)∈m) ⇔ (s=valeur(m,e,«y»))
    car_s = instancie(N.generalisation("y", car), vs)       # ((e,s)∈m)⇔(s=m(e)[y])
    s_eq_me_y = N.modus_ponens(h_cpl, equivalence_avant(car_s))   # s=valeur(m,e,«y»)
    # rebind y→qi : valeur(m,e,«y»)=valeur(m,e,«qi»)
    reb = N.alpha_tau(appartient(E.couple(ve, var("y")), vm), "y", _VBI)  # val(m,e,y)=val(m,e,qi)
    me_y = E.valeur(vm, ve, "y")
    me_qi = E.valeur(vm, ve, _VBI)
    # s = val(m,e,y) = val(m,e,qi)
    s_eq_me_qi = composer_egalites(s_eq_me_y, reb)          # s=valeur(m,e,«qi»)
    return N.modus_ponens(s_eq_me_qi, symetrie(vs, me_qi))  # valeur(m,e,«qi»)=s


def _Kg_valeur_egal(g, t, m, e_nom):
    """{ u∈T } ⊢ K_g(u) = g(m(u)),   K_g(u)=valeur(K_g,u,«y»),  point u_nom NOM.

    graphe_terme_valeur : K_g(u)=Λ_val[u] = valeur(graphe_de g, valeur(m,u,qi), qo)."""
    from bourbaki.cardinaux.ensembles_cantor import graphe_terme_valeur
    vt = _t(t)
    return graphe_terme_valeur(vt, _val_K(g, m), e_nom, _PT, "y")


def _g_de_me(vg, vm, ve):
    """g(m(e)) = valeur(graphe_de g, valeur(m,e,«k»), «r»)   (au point e nommé)."""
    me = E.valeur(vm, ve, _VBI)
    return E.valeur(graphe_de(vg), me, _VBO)


def _g_de_s(vg, vs_term):
    """g(s) = valeur(graphe_de g, s, «r»)."""
    return E.valeur(graphe_de(vg), vs_term, _VBO)


def _g_values_at_s(vg1, vg2, vs, vt, vm, s_nom):
    """{ K_g₁=K_g₂, est_bijection_de(m,T,S), s∈S } ⊢ g₁(s)=g₂(s)  (binder «r»),
       point s = NOM (s_nom).

    s∈S=image(m,T) ⇒ témoin e∈T avec (e,s)∈m ; K_gᵢ(e)=gᵢ(m(e)) (graphe_terme_valeur,
    sous e∈T) ; K_g₁=K_g₂ ⇒ K_g₁(e)=K_g₂(e) ⇒ g₁(m(e))=g₂(m(e)) ; m(e)=s
    (_valeur_eq_de_couple, m fonct) ⇒ g₁(s)=g₂(s)."""
    from bourbaki.cardinaux.arithmetique.ensembles_produit_equipotence import _antecedent_image
    vs_pt = var(s_nom)
    Kg1, Kg2 = K_g(vg1, vt, vm), K_g(vg2, vt, vm)
    ve = var("d")          # témoin-antécédent (≠ _PT=«e», point interne de K_g)
    me = E.valeur(vm, ve, _VBI)                              # m(e)
    # bijection ⇒ dom m=T, m fonctionnel, image(m,T)=S
    h_bij = N.assume(est_bijection_de(vm, vt, vs))
    m_func = conjonction_elim_gauche(conjonction_elim_gauche(h_bij))   # m fonct
    img_eq = conjonction_elim_droite(conjonction_elim_droite(h_bij))   # image(m,T)=S
    # s∈S ⇒ s∈image(m,T) ⇒ (∃e)(e∈T et (e,s)∈m)
    h_s = N.assume(appartient(vs_pt, vs))
    s_in_img = N.modus_ponens(h_s, equivalence_arriere(N.modus_ponens(img_eq,
        N.s6(E.image(vm, vt), vs, "w", appartient(vs_pt, var("w"))))))  # s∈image(m,T)
    ante = _antecedent_image(vm, vt, vs_pt, "d")            # s∈img ⇒ (∃e)(e∈T et (e,s)∈m)
    ex_e = N.modus_ponens(s_in_img, ante)                  # (∃e)(e∈T et (e,s)∈m)
    # sous le témoin e :
    body = et(appartient(ve, vt), appartient(E.couple(ve, vs_pt), vm))
    hb = N.assume(body)
    eT = conjonction_elim_gauche(hb)                       # e∈T
    es_m = conjonction_elim_droite(hb)                     # (e,s)∈m
    # K_gᵢ(e)=gᵢ(m(e))   (graphe_terme_valeur au point e, sous e∈T)
    Kg1e = _cut(_Kg_valeur_egal(vg1, vt, vm, "d"), [(appartient(ve, vt), eT)])  # K_g₁(e)=g₁(m(e))
    Kg2e = _cut(_Kg_valeur_egal(vg2, vt, vm, "d"), [(appartient(ve, vt), eT)])  # K_g₂(e)=g₂(m(e))
    # K_g₁=K_g₂ ⇒ K_g₁(e)=K_g₂(e)
    h_Keq = N.assume(egal(Kg1, Kg2))
    Ke_eq = N.modus_ponens(h_Keq, congruence_terme(Kg1, Kg2, E.valeur(var("w"), ve, "y")))  # K_g₁(e)=K_g₂(e)
    # g₁(m(e)) = K_g₁(e) = K_g₂(e) = g₂(m(e))
    g1me = _g_de_me(vg1, vm, ve)
    g2me = _g_de_me(vg2, vm, ve)
    g1me_eq_Kg1e = N.modus_ponens(Kg1e, symetrie(E.valeur(Kg1, ve, "y"), g1me))  # g₁(m(e))=K_g₁(e)
    gme_eq = composer_egalites(composer_egalites(g1me_eq_Kg1e, Ke_eq), Kg2e)     # g₁(m(e))=g₂(m(e))
    # m(e)=s  (m fonct, (e,s)∈m)
    me_eq_s = _cut(_valeur_eq_de_couple(vm, ve, vs_pt),
                   [(E.est_fonctionnel(vm), m_func), (appartient(E.couple(ve, vs_pt), vm), es_m)])  # m(e)=s
    # transporter g₁(m(e))=g₂(m(e)) au point s : gᵢ(m(e)) → gᵢ(s)  via m(e)=s (Leibniz)
    g1s = _g_de_s(vg1, vs_pt)
    g2s = _g_de_s(vg2, vs_pt)
    g1_cong = N.modus_ponens(me_eq_s, congruence_terme(me, vs_pt, E.valeur(graphe_de(vg1), var("w"), _VBO)))  # g₁(m(e))=g₁(s)
    g2_cong = N.modus_ponens(me_eq_s, congruence_terme(me, vs_pt, E.valeur(graphe_de(vg2), var("w"), _VBO)))  # g₂(m(e))=g₂(s)
    # g₁(s)=g₁(m(e))=g₂(m(e))=g₂(s)
    g1s_eq_g1me = N.modus_ponens(g1_cong, symetrie(g1me, g1s))   # g₁(s)=g₁(m(e))
    gs_eq = composer_egalites(composer_egalites(g1s_eq_g1me, gme_eq), g2_cong)  # g₁(s)=g₂(s)  [body, K eq]
    # éliminer le témoin e : (∃e)body ⇒ g₁(s)=g₂(s)
    ex_imp = existe_elimination(N.loi_deduction(body, gs_eq), "d")
    return N.modus_ponens(ex_e, ex_imp)                    # g₁(s)=g₂(s)  [K eq, bij, s∈S]


def _g_values_at_s_y(vg1, vg2, vs, vt, vm, s_nom):
    """{ K_g₁=K_g₂, bij, s∈S } ⊢ valeur(graphe_de g₁,s,«y») = valeur(graphe_de g₂,s,«y»).

    _g_values_at_s donne l'égalité en binder «r» ; on rebinde «r»→«y» (α-tau) des
    deux côtés pour s'apparier à egalite_valeurs_application (binder défaut «y»)."""
    vs_pt = var(s_nom)
    base = _g_values_at_s(vg1, vg2, vs, vt, vm, s_nom)      # g₁(s)[r]=g₂(s)[r]
    # rebind r→y : valeur(graphe_de gᵢ, s, «r») = valeur(graphe_de gᵢ, s, «y»)
    reb1 = N.alpha_tau(appartient(E.couple(vs_pt, var(_VBO)), graphe_de(vg1)), _VBO, "y")
    reb2 = N.alpha_tau(appartient(E.couple(vs_pt, var(_VBO)), graphe_de(vg2)), _VBO, "y")
    g1r, g1y = _g_de_s(vg1, vs_pt), E.valeur(graphe_de(vg1), vs_pt, "y")
    g2r, g2y = _g_de_s(vg2, vs_pt), E.valeur(graphe_de(vg2), vs_pt, "y")
    # g₁(s)[y] = g₁(s)[r] = g₂(s)[r] = g₂(s)[y]
    g1y_eq_r = N.modus_ponens(reb1, symetrie(g1r, g1y))    # g₁(s)[y]=g₁(s)[r]
    return composer_egalites(composer_egalites(g1y_eq_r, base), reb2)   # g₁(s)[y]=g₂(s)[y]


def _g_egalite_valeurs(vg1, vg2, vs, vt, vm):
    """{ K_g₁=K_g₂, bij } ⊢ (∀x)(x∈S ⇒ valeur(graphe_de g₁,x,«y»)=valeur(graphe_de g₂,x,«y»)).

    = l'hypothèse « mêmes valeurs sur S » de application_egale_par_valeurs (3ᵉ prémisse)."""
    # point SÛR « s » (≠ « x » liant interne de _antecedent_image / AXIOME_IMAGE),
    # puis α-renommage (∀s)→(∀x) par instanciation + re-généralisation.
    vs_pt = var("s")
    pt = _g_values_at_s_y(vg1, vg2, vs, vt, vm, "s")        # {Keq,bij,s∈S} ⊢ g₁(s)[y]=g₂(s)[y]
    pt = N.loi_deduction(appartient(vs_pt, vs), pt)         # s∈S ⇒ …  [Keq,bij]
    raw = N.generalisation("s", pt)                        # (∀s)(s∈S⇒…)
    inst = instancie(raw, var("x"))                        # (s:=x)
    return N.generalisation("x", inst)                     # (∀x)(x∈S⇒…)


def lambda_injective_sous_appartenance(g1, g2, s, t, m):
    """{ g₁∈𝓕(S;A), g₂∈𝓕(S;A), bij, K_g₁=K_g₂ } ⊢ g₁ = g₂.

    Cœur INJECTIVITÉ.  Mêmes valeurs sur S (_g_egalite_valeurs, via surjectivité de m)
    ⇒ application_egale_par_valeurs ⊢ g₁=g₂."""
    from bourbaki.ensembles.fonctions.ensembles_application_valeur import (
        application_egale_par_valeurs, egalite_valeurs_application)
    vg1, vg2, vs, vt, vm = _t(g1), _t(g2), _t(s), _t(t), _t(m)
    eva = _g_egalite_valeurs(vg1, vg2, vs, vt, vm)         # {Keq,bij} ⊢ (∀x)(x∈S⇒…)
    base = application_egale_par_valeurs(vg1, vg2, vs, var("A"))  # {g₁∈𝓕,g₂∈𝓕,(∀x)…} ⊢ g₁=g₂
    target_eva = egalite_valeurs_application(vg1, vg2, vs)
    assert eva.conclusion == target_eva, "egalite_valeurs ≠ attendu par application_egale_par_valeurs"
    return _cut(base, [(target_eva, eva)])                 # {g₁∈𝓕,g₂∈𝓕,bij,Keq} ⊢ g₁=g₂


def _lambda_egal_donne_K(vg1, vg2, vt, vm):
    """{ Λ(g₁)=Λ(g₂) } ⊢ K_g₁=K_g₂.   (deux décompos de couples : ((K,T),A).)"""
    from bourbaki.ensembles.base.ensembles_couples import couple_egal_implique_composantes
    Kg1, Kg2 = K_g(vg1, vt, vm), K_g(vg2, vt, vm)
    va = var("A")
    L1, L2 = _lambda_valeur(vg1, vt, vm), _lambda_valeur(vg2, vt, vm)
    inner1, inner2 = E.couple(Kg1, vt), E.couple(Kg2, vt)
    h = N.assume(egal(L1, L2))                              # ((Kg₁,T),A)=((Kg₂,T),A)
    comp1 = N.modus_ponens(h, couple_egal_implique_composantes(inner1, va, inner2, va))
    inner_eq = conjonction_elim_gauche(comp1)              # (Kg₁,T)=(Kg₂,T)
    comp2 = N.modus_ponens(inner_eq, couple_egal_implique_composantes(Kg1, vt, Kg2, vt))
    return conjonction_elim_gauche(comp2)                  # Kg₁=Kg₂


def W_lambda_injective(s, t, m):
    """{ est_bijection_de(m,T,S) } ⊢ injective_dans(W, 𝓕(S;A)).

    (∀u)(∀u')((u∈dom et u'∈dom et W(u)=W(u')) ⇒ u=u').  W(·)=Λ(·) (W_lambda_valeur,
    sous ·∈dom) ⇒ Λ(g₁)=Λ(g₂) ⇒ K_g₁=K_g₂ (_lambda_egal_donne_K) ⇒ g₁=g₂
    (lambda_injective_sous_appartenance).  Variables-fonction « g1 »,« g2 » SÛRES,
    α-renommées en « u »,« up » pour s'apparier à injective_dans."""
    vs, vt, vm = _t(s), _t(t), _t(m)
    dom = _source(vs)
    Wt = W_lambda(vs, vt, vm)
    vg1, vg2 = var("g1"), var("g2")
    L1, L2 = _lambda_valeur(vg1, vt, vm), _lambda_valeur(vg2, vt, vm)
    Kg1, Kg2 = K_g(vg1, vt, vm), K_g(vg2, vt, vm)

    hyp = et(et(appartient(vg1, dom), appartient(vg2, dom)),
             egal(E.valeur(Wt, vg1), E.valeur(Wt, vg2)))
    h = N.assume(hyp)
    g1_in = conjonction_elim_gauche(conjonction_elim_gauche(h))
    g2_in = conjonction_elim_droite(conjonction_elim_gauche(h))
    W_eq = conjonction_elim_droite(h)                      # W(g₁)=W(g₂)
    Wg1 = _cut(W_lambda_valeur("g1", vs, vt, vm), [(appartient(vg1, dom), g1_in)])  # W(g₁)=Λ(g₁)
    Wg2 = _cut(W_lambda_valeur("g2", vs, vt, vm), [(appartient(vg2, dom), g2_in)])  # W(g₂)=Λ(g₂)
    lam_eq = composer_egalites(composer_egalites(
        N.modus_ponens(Wg1, symetrie(E.valeur(Wt, vg1), L1)), W_eq), Wg2)   # Λ(g₁)=Λ(g₂)
    K_eq = _cut(_lambda_egal_donne_K(vg1, vg2, vt, vm), [(egal(L1, L2), lam_eq)])   # K_g₁=K_g₂
    g_eq = lambda_injective_sous_appartenance("g1", "g2", vs, vt, vm)
    g_eq = _cut(g_eq, [(appartient(vg1, dom), g1_in),
                       (appartient(vg2, dom), g2_in),
                       (egal(Kg1, Kg2), K_eq)])            # g₁=g₂  [hyp, bij]
    inner = N.loi_deduction(hyp, g_eq)
    raw = N.generalisation("g1", N.generalisation("g2", inner))
    inst = instancie(instancie(raw, var("u")), var("up"))
    return N.generalisation("u", N.generalisation("up", inst))   # injective_dans(W, 𝓕(S;A))


# ═══════════════════════════════════════════════════════════════════════════════
#  Λ EST UNE INJECTION  ⟹  inf_egal_card(𝓕(S;A), 𝓕(T;A)).
# ═══════════════════════════════════════════════════════════════════════════════
def W_lambda_est_injection(s, t, m):
    """{ est_bijection_de(m,T,S) } ⊢ est_injection_de(W, 𝓕(S;A), 𝓕(T;A)).

    Les QUATRE conjoints : W fonctionnel, dom W=𝓕(S;A), W injective, image⊂𝓕(T;A)."""
    vs, vt, vm = _t(s), _t(t), _t(m)
    return conjonction_intro(conjonction_intro(conjonction_intro(
        W_lambda_fonctionnel(vs, vt, vm), W_lambda_domaine(vs, vt, vm)),
        W_lambda_injective(vs, vt, vm)), W_lambda_image_incluse(vs, vt, vm))


def injection_via_pointmap(s, t, m):
    """{ est_bijection_de(m,T,S) } ⊢ inf_egal_card(𝓕(S;A), 𝓕(T;A)).

    BUILDER GÉNÉRIQUE.  L'injection-témoin est W (W_lambda_est_injection) : par S5
    (témoin F:=W), (∃F) est_injection_de(F, 𝓕(S;A), 𝓕(T;A)) = inf_egal_card(·,·)."""
    vs, vt, vm = _t(s), _t(t), _t(m)
    dom = _source(vs)
    cod = _but(vt)
    Wt = W_lambda(vs, vt, vm)
    inj = W_lambda_est_injection(vs, vt, vm)
    return N.modus_ponens(inj, N.s5(est_injection_de(var("F"), dom, cod), Wt, "F"))


# ═══════════════════════════════════════════════════════════════════════════════
#  CLÔTURE FINALE  :  Eq(X,Y) ⇒ Eq(𝓕(X;A), 𝓕(Y;A))   (CANTOR–BERNSTEIN).
# ───────────────────────────────────────────────────────────────────────────────
#   Sous le témoin F de Eq(X,Y) (est_bijection_de(F,X,Y)) :
#     • Dir.1 :  m=reciproque(F), bijection F⁻¹:Y→X (reciproque_est_bijection)
#                ⇒ injection_via_pointmap(X,Y,F⁻¹) : 𝓕(X;A) ≤ 𝓕(Y;A).
#     • Dir.2 :  m=F, bijection F:X→Y ⇒ injection_via_pointmap(Y,X,F) : 𝓕(Y;A) ≤ 𝓕(X;A).
#   cantor_bernstein(𝓕(X;A),𝓕(Y;A)) ⇒ Eq(𝓕(X;A),𝓕(Y;A)) ; loi_deduction +
#   existe_elimination du témoin F discharge Eq(X,Y).
# ═══════════════════════════════════════════════════════════════════════════════
def eq_exposant_invariant(x="X", y="Y", a="a"):
    """⊢ Eq(X,Y) ⇒ Eq(𝓕(X;A), 𝓕(Y;A)).   (invariance de l'espace de fonctions.)

    Note : le paramètre `a` désigne le but A (les builders internes utilisent var('A')
    fixe ; on instancie A:=var(a) à la fin si a≠'A')."""
    from bourbaki.cardinaux.ensembles_cantor_bernstein_final import cantor_bernstein
    from bourbaki.cardinaux.ensembles_bijection import reciproque_est_bijection
    vx, vy = _t(x), _t(y)
    va = var("A")
    FX = E.applications(vx, va)                            # 𝓕(X;A)
    FY = E.applications(vy, va)                            # 𝓕(Y;A)
    vF = var("F")
    Finv = E.reciproque(vF)

    # corps du témoin de Eq(X,Y) : est_bijection_de(F,X,Y)
    bij_body = est_bijection_de(vF, vx, vy)
    h_bij = N.assume(bij_body)

    # Dir.1 : F⁻¹ bijection Y→X ; builder(X,Y,F⁻¹) sous est_bijection_de(F⁻¹,Y,X)
    rb = reciproque_est_bijection("F", "X", "Y")          # bij(F,X,Y) ⇒ bij(F⁻¹,Y,X)
    bij_inv = N.modus_ponens(h_bij, rb)                   # est_bijection_de(F⁻¹,Y,X)
    dir1 = injection_via_pointmap(vx, vy, Finv)           # {bij(F⁻¹,Y,X)} ⊢ 𝓕(X;A)≤𝓕(Y;A)
    dir1 = _cut(dir1, [(est_bijection_de(Finv, vy, vx), bij_inv)])   # 𝓕(X;A)≤𝓕(Y;A)  [bij(F,X,Y)]

    # Dir.2 : builder(Y,X,F) sous est_bijection_de(F,X,Y)
    dir2 = injection_via_pointmap(vy, vx, vF)             # {bij(F,X,Y)} ⊢ 𝓕(Y;A)≤𝓕(X;A)
    dir2 = _cut(dir2, [(est_bijection_de(vF, vx, vy), h_bij)])       # 𝓕(Y;A)≤𝓕(X;A)  [bij(F,X,Y)]

    # cantor_bernstein(𝓕(X;A),𝓕(Y;A)) : (𝓕(X;A)≤𝓕(Y;A) et 𝓕(Y;A)≤𝓕(X;A)) ⇒ Eq(𝓕(X;A),𝓕(Y;A))
    cb_nom = cantor_bernstein("A", "B", "f", "g")
    cb_gen = N.generalisation("A", N.generalisation("B", cb_nom))
    cb = instancie(instancie(cb_gen, FX), FY)            # version TERME (capture-safe)
    eqF = N.modus_ponens(conjonction_intro(dir1, dir2), cb)   # Eq(𝓕(X;A),𝓕(Y;A))  [bij(F,X,Y)]

    # discharge du témoin F : Eq(X,Y)=(∃F)bij(F,X,Y) ⇒ Eq(𝓕(X;A),𝓕(Y;A))
    imp = existe_elimination(N.loi_deduction(bij_body, eqF), "F")    # (∃F)bij ⇒ Eq(𝓕(X;A),𝓕(Y;A))
    # imp.conclusion = Eq(X,Y) ⇒ Eq(𝓕(X;A),𝓕(Y;A))   (Eq(X,Y) = existe("F", bij(F,X,Y)))
    out = imp
    if a != "A":
        # instancier A:=var(a) (généralisation puis instanciation)
        out = instancie(N.generalisation("A", out), _t(a))
    return out

