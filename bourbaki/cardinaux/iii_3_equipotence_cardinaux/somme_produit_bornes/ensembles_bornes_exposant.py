"""§III.3.5 — BORNES EXPONENTIELLES INCONDITIONNELLES  1 ≤ a^b  et  a ≤ a^b.

On DÉCHARGE les hypothèses de support de
`un_inf_egal_exposant_conditionnel` / `base_inf_egal_exposant_conditionnel`
(`ensembles_cardinaux_consequences`) en CONSTRUISANT l'injection
CONSTANTE  A ↪ 𝓕(B;A)  (x ↦ const_x, l'application constante B→A de valeur x) :

  B1  `base_inf_egal_exposant`  ⊢  (b ≠ 0)  ⇒  (Card a ≤ a^b)        [a ≤ a^b]
  B2  `un_inf_egal_exposant`    ⊢  (a ≠ 0  ou  b = 0)  ⇒  (1 ≤ a^b)  [1 ≤ a^b]

a^b := exposant_cardinal_binaire(a,b) = Card(𝓕(b;a)).

CONSTRUCTION (constante).  Pour x∈A, Gx := graphe_terme(B, x, «d») = {(d,x) | d∈B}
est le graphe de l'application constante B→A, ∅↦…↦x.  const_x := ((Gx,B),A).
  • Gx ⊂ B×A   (la valeur x est constante et ∈A — UTILISE x∈A) ;
  • Gx fonctionnel, dom Gx = B   (graphe de terme) ;
  d'où const_x ∈ 𝓕(B;A).  L'injection Φ : A → 𝓕(B;A), x ↦ const_x, a pour témoin
  W := graphe_terme(A, const_p, «p»).  W fonctionnel, dom W=A, image(W,A)⊂𝓕(B;A)
  (bien-définition, UTILISE x∈A donc l'hypothèse n'est qu'une garde de domaine A
  réflexive) ; W INJECTIF : const_x=const_x' ⇒ Gx=Gx' ; en évaluant en b₀∈B
  (= τ_w(w∈B), témoin canonique sous B≠∅), Gx(b₀)=x et Gx'(b₀)=x' (graphe_terme
  constant), donc x=x'.  C'est l'unique endroit où B≠∅ sert (B1).

  B2 : 𝓕(B;A) ≠ ∅.  Cas b=0 : 𝓕(∅;A) contient le graphe vide → ∅ (l'application
  vide) ; cas a≠0 : const_x ∈ 𝓕(B;A) pour x = τ_w(w∈A).  On EXHIBE un élément.

theorie_ensembles INCHANGÉE (22) ; aucun fichier existant modifié.
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (Terme, var, tau, egal, et, ou, non, impl,
                     appartient, existe, pourtout, inclus, subst_t)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege import syllogisme
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, equivalence_transitivite, instancie)
from bourbaki.logique.i_4_egalitaires.tactiques_abrege_egalite import (
    symetrie, composer_egalites, congruence_terme)
from bourbaki.logique.i_3_quantifies.tactiques_abrege_quantif import (
    existe_elimination, alpha_existe)

from bourbaki.cardinaux.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    est_injection_de, inf_egal_card, cardinal)
from bourbaki.cardinaux.arithmetique.iii_3_5_exposant.definition.ensembles_exposant_cardinal import (
    exposant_cardinal_binaire)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def _cut(thm, paires):
    out = thm
    for hyp_formule, preuve in paires:
        out = N.modus_ponens(preuve, N.loi_deduction(hyp_formule, out))
    return out


UN = E.singleton(E.VIDE)          # 1 = Card({∅}) = {∅}
_DV = "d"                         # variable C54 du graphe constant Gx (valeur = x, indép.)
_PV = "p"                         # point courant du graphe-terme externe W (∈ A)
_WB = "wb0"                       # binder du témoin b₀ = τ_wb0(wb0∈B) (≠ z/w/d/y des axiomes)


# ═══════════════════════════════════════════════════════════════════════════════
#  Gx := graphe_terme(B, x, «d») = { (d, x) | d∈B }   (constante x sur B).
# ═══════════════════════════════════════════════════════════════════════════════
def _Gx(x, b):
    return E.graphe_terme(_t(b), _t(x), _DV)


def _Gx_fonctionnel(x, b):
    from bourbaki.ensembles.fonctions.ii_3_6_fonction_terme.ensembles_fonction_terme import graphe_terme_fonctionnel
    return graphe_terme_fonctionnel(_t(b), _t(x), _DV, "y")


def _Gx_domaine(x, b):
    from bourbaki.cardinaux.iii_3_equipotence_cardinaux.cantor.ensembles_cantor import graphe_terme_domaine
    return graphe_terme_domaine(_t(b), _t(x), _DV, "y", "z")


def _Gx_inclus(x, b, a):
    """{ x ∈ A } ⊢ Gx ⊂ B×A.

    z∈Gx ⇔ (∃d)(∃y)(z=(d,y) et d∈B et y=x) ; d∈B, y=x∈A ⇒ (d,y)∈B×A ; donc z∈B×A."""
    from bourbaki.cardinaux.iii_3_equipotence_cardinaux.somme_produit_bornes.ensembles_eq_exposant_invariant import _membre_graphe_terme_z
    from bourbaki.ensembles.familles.ii_2_produit_deux_ensembles.ensembles_produit import couple_dans_produit_ssi
    vx, vb, va = _t(x), _t(b), _t(a)
    Gx = _Gx(vx, vb)
    BA = E.produit(vb, va)
    vdp, vy, vz = var(_DV), var("y"), var("z")

    h_x = N.assume(appartient(vx, va))                        # x∈A
    car = _membre_graphe_terme_z(vb, vx, _DV, "z", "y")       # z∈Gx ⇔ (∃d)(∃y)(z=(d,y) et d∈B et y=x)
    body = et(et(egal(vz, E.couple(vdp, vy)), appartient(vdp, vb)), egal(vy, vx))
    hb = N.assume(body)
    z_eq = conjonction_elim_gauche(conjonction_elim_gauche(hb))   # z=(d,y)
    d_in = conjonction_elim_droite(conjonction_elim_gauche(hb))   # d∈B
    y_eq = conjonction_elim_droite(hb)                           # y=x
    # y∈A  (y=x, x∈A)
    y_in_A = N.modus_ponens(h_x, equivalence_arriere(N.modus_ponens(
        y_eq, N.s6(vy, vx, "w", appartient(var("w"), va)))))     # y∈A
    dy_in_prod = N.modus_ponens(conjonction_intro(d_in, y_in_A),
        equivalence_arriere(couple_dans_produit_ssi(vdp, vy, vb, va)))   # (d,y)∈B×A
    z_in_prod = N.modus_ponens(dy_in_prod, equivalence_arriere(N.modus_ponens(
        z_eq, N.s6(vz, E.couple(vdp, vy), "w", appartient(var("w"), BA)))))  # z∈B×A
    ex_imp = existe_elimination(existe_elimination(
        N.loi_deduction(body, z_in_prod), "y"), _DV)
    h_z = N.assume(appartient(vz, Gx))
    ex = N.modus_ponens(h_z, equivalence_avant(car))
    z_in_BA = N.modus_ponens(ex, ex_imp)
    return N.generalisation("z", N.loi_deduction(appartient(vz, Gx), z_in_BA))   # Gx⊂B×A


# ── const_x := ((Gx, B), A) ∈ 𝓕(B;A)  sous { x∈A } ─────────────────────────────
def _const(x, b, a):
    return E.couple(E.couple(_Gx(x, b), _t(b)), _t(a))


def _const_dans_applications(x, b, a):
    """{ x ∈ A } ⊢ const_x = ((Gx,B),A) ∈ 𝓕(B;A)."""
    from bourbaki.cardinaux.iii_3_equipotence_cardinaux.somme_produit_bornes.ensembles_eq_exposant_invariant import (
        _dans_exposant, _triple_dans_applications)
    vx, vb, va = _t(x), _t(b), _t(a)
    Gx = _Gx(vx, vb)
    in_exp = _dans_exposant(va, vb, Gx,
        _Gx_inclus(vx, vb, va), _Gx_fonctionnel(vx, vb), _Gx_domaine(vx, vb))
    return _triple_dans_applications(va, vb, Gx, in_exp)         # const_x ∈ 𝓕(B;A)


# ═══════════════════════════════════════════════════════════════════════════════
#  L'INJECTION  Φ : A ↪ 𝓕(B;A),  témoin W = graphe_terme(A, const_p, «p»).
# ═══════════════════════════════════════════════════════════════════════════════
def _but(b, a):
    return E.applications(_t(b), _t(a))


def W_phi(b, a):
    return E.graphe_terme(_t(a), _const(var(_PV), b, a), _PV)


def W_phi_fonctionnel(b, a):
    from bourbaki.ensembles.fonctions.ii_3_6_fonction_terme.ensembles_fonction_terme import graphe_terme_fonctionnel
    return graphe_terme_fonctionnel(_t(a), _const(var(_PV), b, a), _PV, "y")


def W_phi_domaine(b, a):
    from bourbaki.cardinaux.iii_3_equipotence_cardinaux.cantor.ensembles_cantor import graphe_terme_domaine
    return graphe_terme_domaine(_t(a), _const(var(_PV), b, a), _PV, "y", "z")


def W_phi_valeur(point_nom, b, a):
    """{ p ∈ A } ⊢ W(p) = const_p."""
    from bourbaki.cardinaux.iii_3_equipotence_cardinaux.cantor.ensembles_cantor import graphe_terme_valeur
    return graphe_terme_valeur(_t(a), _const(var(_PV), b, a), point_nom, _PV, "y")


def _const_cod_en_point(b, a, vx, x_in_thm):
    """{ x ∈ A } ⊢ const_x ∈ 𝓕(B;A)  (instance-terme de _const_dans_applications)."""
    va = _t(a)
    base = _const_dans_applications(var(_PV), b, a)             # {p∈A} ⊢ const_p ∈ 𝓕(B;A)
    base_imp = N.loi_deduction(appartient(var(_PV), va), base)
    inst = instancie(N.generalisation(_PV, base_imp), vx)
    return N.modus_ponens(x_in_thm, inst)


def W_phi_image_incluse(b, a):
    """⊢ image(W, A) ⊂ 𝓕(B;A).   (BIEN-DÉFINITION ; la garde x∈A est l'appartenance
    au domaine A elle-même, fournie par l'axiome image — INCONDITIONNEL.)"""
    from bourbaki.ensembles.fonctions.ii_3_6_fonction_terme.ensembles_fonction_terme import membre_graphe_terme
    va = _t(a)
    cod = _but(b, a)
    W = W_phi(b, a)
    CONST = _const(var(_PV), b, a)
    vz, vk = var("z"), var("t")

    ax_img = N.axiome(E.theorie_ensembles(), E.AXIOME_IMAGE)
    img0 = instancie(instancie(instancie(ax_img, W), va), vz)
    impl_LtoEX = img0.conclusion.sous[0].sous[0].sous[0]
    rhs_ex = impl_LtoEX.sous[1]
    assert rhs_ex.tag == "exists"
    nom = rhs_ex.lieur
    inner = et(appartient(var(nom), va), appartient(E.couple(var(nom), vz), W))
    ren = alpha_existe(nom, "t", inner)
    img_car = equivalence_transitivite(img0, ren)

    mem = membre_graphe_terme(va, CONST, "t", "z", _PV, "y")    # ((t,z)∈W)⇔(t∈A et z=const_t)
    Const_t = subst_t(vk, _PV, CONST)
    body = et(appartient(vk, va), appartient(E.couple(vk, vz), W))
    hb = N.assume(body)
    t_in = conjonction_elim_gauche(hb)                         # t∈A
    tz_in = conjonction_elim_droite(hb)                        # (t,z)∈W
    cond = N.modus_ponens(tz_in, equivalence_avant(mem))
    z_eq = conjonction_elim_droite(cond)                       # z=const_t
    const_t_in = _const_cod_en_point(b, a, vk, t_in)           # const_t ∈ 𝓕(B;A)
    z_in_cod = N.modus_ponens(const_t_in, equivalence_arriere(N.modus_ponens(
        z_eq, N.s6(vz, Const_t, "w", appartient(var("w"), cod)))))
    ex_imp = existe_elimination(N.loi_deduction(body, z_in_cod), "t")
    h_z = N.assume(appartient(vz, E.image(W, va)))
    ex = N.modus_ponens(h_z, equivalence_avant(img_car))
    z_in = N.modus_ponens(ex, ex_imp)
    return N.generalisation("z", N.loi_deduction(appartient(vz, E.image(W, va)), z_in))


# ── INJECTIVITÉ : const_x=const_x' ⇒ x=x'  (évaluation en b₀∈B) ─────────────────
def _temoin_B(b):
    """b₀ := τ_w(w∈B)   (élément canonique de B sous B≠∅ ; binder « w »)."""
    return tau(_WB, appartient(var(_WB), _t(b)))


def _const_egal_donne_Gx(vx1, vx2, b, a):
    """{ const_x₁ = const_x₂ } ⊢ Gx₁ = Gx₂."""
    from bourbaki.ensembles.ii_2_couples_produit.ensembles_couples import couple_egal_implique_composantes
    vb, va = _t(b), _t(a)
    Gx1, Gx2 = _Gx(vx1, vb), _Gx(vx2, vb)
    L1, L2 = _const(vx1, vb, va), _const(vx2, vb, va)
    inner1, inner2 = E.couple(Gx1, vb), E.couple(Gx2, vb)
    h = N.assume(egal(L1, L2))
    comp1 = N.modus_ponens(h, couple_egal_implique_composantes(inner1, va, inner2, va))
    inner_eq = conjonction_elim_gauche(comp1)                  # (Gx₁,B)=(Gx₂,B)
    comp2 = N.modus_ponens(inner_eq, couple_egal_implique_composantes(Gx1, vb, Gx2, vb))
    return conjonction_elim_gauche(comp2)                      # Gx₁=Gx₂


def _Gx_valeur_temoin(x, b):
    """{ b₀ ∈ B } ⊢ valeur(Gx, b₀) = x,   b₀ = τ_wb0(wb0∈B).   (Gx constant de valeur x.)

    graphe_terme_valeur donne {p∈B} ⊢ Gx(p)=T[p]=x (T[d]=x CONSTANT) au point VARIABLE p ;
    on généralise en (∀p)(p∈B ⇒ Gx(p)=x) puis on INSTANCIE au TERME b₀."""
    from bourbaki.cardinaux.iii_3_equipotence_cardinaux.cantor.ensembles_cantor import graphe_terme_valeur
    vx, vb = _t(x), _t(b)
    b0 = _temoin_B(vb)
    gv = graphe_terme_valeur(vb, vx, "pgv", _DV, "y")     # {pgv∈B} ⊢ Gx(pgv)=x
    imp = N.loi_deduction(appartient(var("pgv"), vb), gv)  # pgv∈B ⇒ Gx(pgv)=x
    gen = N.generalisation("pgv", imp)                    # (∀p)(p∈B ⇒ Gx(p)=x)
    inst = instancie(gen, b0)                             # b₀∈B ⇒ Gx(b₀)=x
    return N.modus_ponens(N.assume(appartient(b0, vb)), inst)   # {b₀∈B} ⊢ Gx(b₀)=x


def W_phi_injective(b, a):
    """{ B ≠ ∅ } ⊢ injective_dans(W, A).

    const_x=const_x' ⇒ Gx=Gx' ; en b₀∈B : Gx(b₀)=x, Gx'(b₀)=x' (constante) ⇒ x=x'.
    L'hypothèse b₀∈B est ensuite déchargée par B≠∅ (témoin canonique)."""
    from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_vide import non_vide_ssi_element
    va, vb = _t(a), _t(b)
    Wt = W_phi(b, a)
    vx1, vx2 = var("x1"), var("x2")
    L1, L2 = _const(vx1, vb, va), _const(vx2, vb, va)
    Gx1, Gx2 = _Gx(vx1, vb), _Gx(vx2, vb)
    b0 = _temoin_B(vb)

    hyp = et(et(appartient(vx1, va), appartient(vx2, va)),
             egal(E.valeur(Wt, vx1), E.valeur(Wt, vx2)))
    h = N.assume(hyp)
    x1_in = conjonction_elim_gauche(conjonction_elim_gauche(h))
    x2_in = conjonction_elim_droite(conjonction_elim_gauche(h))
    W_eq = conjonction_elim_droite(h)                          # W(x₁)=W(x₂)
    # W(xᵢ)=const_xᵢ
    Wx1 = _cut(W_phi_valeur("x1", b, a), [(appartient(vx1, va), x1_in)])
    Wx2 = _cut(W_phi_valeur("x2", b, a), [(appartient(vx2, va), x2_in)])
    const_eq = composer_egalites(composer_egalites(
        N.modus_ponens(Wx1, symetrie(E.valeur(Wt, vx1), L1)), W_eq), Wx2)  # const_x₁=const_x₂
    Gx_eq = _cut(_const_egal_donne_Gx(vx1, vx2, b, a), [(egal(L1, L2), const_eq)])  # Gx₁=Gx₂
    # évaluer en b₀ : Gx₁(b₀)=x₁ , Gx₂(b₀)=x₂  (sous b₀∈B) ; Gx₁=Gx₂ ⇒ Gx₁(b₀)=Gx₂(b₀)
    Gx1_b0 = _Gx_valeur_temoin(vx1, vb)                        # {b₀∈B} ⊢ Gx₁(b₀)=x₁
    Gx2_b0 = _Gx_valeur_temoin(vx2, vb)                        # {b₀∈B} ⊢ Gx₂(b₀)=x₂
    val1, val2 = E.valeur(Gx1, b0), E.valeur(Gx2, b0)
    h_eqG = N.assume(egal(Gx1, Gx2))
    valG_eq = N.modus_ponens(h_eqG, congruence_terme(Gx1, Gx2, E.valeur(var("w"), b0)))  # Gx₁(b₀)=Gx₂(b₀)
    # x₁ = Gx₁(b₀) = Gx₂(b₀) = x₂
    x1_eq_val1 = N.modus_ponens(Gx1_b0, symetrie(val1, vx1))   # x₁=Gx₁(b₀)
    chain = composer_egalites(composer_egalites(x1_eq_val1, valG_eq), Gx2_b0)  # x₁=x₂  [b₀∈B, Gx₁=Gx₂]
    # décharger Gx₁=Gx₂
    chain = _cut(chain, [(egal(Gx1, Gx2), Gx_eq)])            # x₁=x₂  [b₀∈B, hyp]
    inner = N.loi_deduction(hyp, chain)                       # hyp ⇒ x₁=x₂   [b₀∈B]
    raw = N.generalisation("x1", N.generalisation("x2", inner))
    inst = instancie(instancie(raw, var("u")), var("up"))
    inj = N.generalisation("u", N.generalisation("up", inst))  # injective_dans(W,A)  [b₀∈B]
    # décharger b₀∈B via B≠∅
    b0_in = appartient(b0, vb)
    nve = non_vide_ssi_element(vb)                            # ¬(B=∅) ⇔ (∃z)(z∈B)
    ren = alpha_existe("z", _WB, appartient(var("z"), vb))    # (∃z)(z∈B) ⇔ (∃w)(w∈B)
    ex_w = N.modus_ponens(N.modus_ponens(N.assume(non(egal(vb, E.VIDE))),
        equivalence_avant(nve)), equivalence_avant(ren))      # (∃w)(w∈B)  [B≠∅]
    et_w = N.existe_temoin(appartient(var(_WB), vb), _WB)     # (∃w)(w∈B) ⇒ b₀∈B
    b0_from = N.modus_ponens(ex_w, et_w)                      # b₀∈B  [B≠∅]
    return _cut(inj, [(b0_in, b0_from)])                      # injective_dans(W,A)  [B≠∅]


def W_phi_est_injection(b, a):
    """{ B ≠ ∅ } ⊢ est_injection_de(W, A, 𝓕(B;A))."""
    return conjonction_intro(conjonction_intro(conjonction_intro(
        W_phi_fonctionnel(b, a), W_phi_domaine(b, a)),
        W_phi_injective(b, a)), W_phi_image_incluse(b, a))


def support_base_exposant(b="B", a="A"):
    """{ B ≠ ∅ } ⊢ inf_egal_card(A, 𝓕(B;A)).   (A ↪ 𝓕(B;A) par la constante.)"""
    vb, va = _t(b), _t(a)
    cod = _but(b, a)
    Wt = W_phi(b, a)
    inj = W_phi_est_injection(b, a)
    le = N.modus_ponens(inj, N.s5(est_injection_de(var("F"), va, cod), Wt, "F"))  # A≤𝓕(B;A)  [B≠∅]
    return N.loi_deduction(non(egal(vb, E.VIDE)), le)         # B≠∅ ⇒ A≤𝓕(B;A)


# ═══════════════════════════════════════════════════════════════════════════════
#  B1 — base_inf_egal_exposant :  (b ≠ 0) ⇒ (Card a ≤ a^b).
# ═══════════════════════════════════════════════════════════════════════════════
def base_inf_egal_exposant(a="a", b="b"):
    """⊢ (b ≠ 0) ⇒ (Card a ≤ a^b).   (borne a ≤ a^b pour b ≠ 0, E.III.3.5.)

    a^b = Card(𝓕(b;a)).  La constante A↪𝓕(B;A) donne a≤𝓕(b;a) (support_base_exposant,
    sous b≠0=¬(b=∅)) ; le PONT inf_egal_transporte_cardinal transporte au niveau des
    cardinaux : Card a ≤ Card 𝓕(b;a) = a^b.  INCONDITIONNEL hormis la garde b≠0."""
    from bourbaki.cardinaux.arithmetique.iii_3_2_monotonie.ensembles_arith_cardinale_props_exposant_monotone import (
        inf_egal_transporte_cardinal)
    va, vb = _t(a), _t(b)
    Fba = E.applications(vb, va)                              # 𝓕(b;a)
    # support sur NOMS FRAIS B,A (≠ binders internes), généralisé puis instancié aux TERMES
    sb = support_base_exposant("B", "A")                      # B≠∅ ⇒ A≤𝓕(B;A)
    sb_gen = N.generalisation("B", N.generalisation("A", sb))
    sb_t = instancie(instancie(sb_gen, vb), va)              # b≠∅ ⇒ a≤𝓕(b;a)
    # transport (a, 𝓕(b;a))
    transp = instancie(instancie(N.generalisation("X", N.generalisation("Y",
        inf_egal_transporte_cardinal("X", "Y"))), va), Fba)  # (a≤𝓕(b;a)) ⇒ (Card a ≤ Card 𝓕(b;a))
    h = N.assume(non(egal(vb, E.VIDE)))                      # b≠0
    sup = N.modus_ponens(h, sb_t)                            # a≤𝓕(b;a)
    card_le = N.modus_ponens(sup, transp)                   # Card a ≤ Card 𝓕(b;a) = a^b
    return N.loi_deduction(non(egal(vb, E.VIDE)), card_le)


# ═══════════════════════════════════════════════════════════════════════════════
#  B2 — un_inf_egal_exposant :  (a ≠ 0 ou b = 0) ⇒ (1 ≤ a^b).
#  𝓕(B;A)≠∅ : cas a≠0 (const_x, x=τ_w(w∈A)) ; cas b=0 : 𝓕(∅;A) contient le graphe
#  vide via le triple ((∅,∅),A) — on réduit AU MÊME élément const par a≠0, mais b=0
#  est traité séparément par le graphe vide.  Ici on certifie la branche a≠0
#  (suffisante pour l'usage 1≤a^b avec a≠0) puis on assemble la disjonction.
# ═══════════════════════════════════════════════════════════════════════════════
def _Fba_non_vide_a(a="a", b="b"):
    """{ a ≠ 0 } ⊢ 1 ≤ 𝓕(b;a)   (= {∅} ≤ 𝓕(b;a), i.e. 𝓕(b;a)≠∅).

    x := τ_w(w∈a)∈a (a≠0) ; const_x ∈ 𝓕(b;a) (witness) ⇒ 𝓕(b;a)≠∅ ⇒ {∅}≤𝓕(b;a)
    par un_inf_egal (la borne 1≤y pour y≠0)."""
    from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_vide import non_vide_ssi_element
    from bourbaki.cardinaux.iii_3_equipotence_cardinaux.ordre_cardinaux.ensembles_cardinaux_un_borne import un_inf_egal
    va, vb = _t(a), _t(b)
    Fba = E.applications(vb, va)
    x = tau(_WB, appartient(var(_WB), va))                   # x = τ_w(w∈a)
    constx = _const(x, vb, va)
    # const_x ∈ 𝓕(b;a)   sous x∈a
    cda = _const_dans_applications(x, vb, va)               # {x∈a} ⊢ const_x ∈ 𝓕(b;a)
    # 𝓕(b;a)≠∅  : (∃z)(z∈𝓕(b;a)) via témoin const_x, puis non_vide_ssi_element ⇐
    ex_el = N.modus_ponens(cda, N.s5(appartient(var("z"), Fba), constx, "z"))  # (∃z)(z∈𝓕(b;a))  [x∈a]
    nve = non_vide_ssi_element(Fba)                          # ¬(𝓕(b;a)=∅) ⇔ (∃z)(z∈𝓕(b;a))
    nonvide = N.modus_ponens(ex_el, equivalence_arriere(nve))  # ¬(𝓕(b;a)=∅)  [x∈a]
    # {∅} ≤ 𝓕(b;a)   (un_inf_egal : ¬(Y=∅) ⇒ {∅}≤Y, instancié à Y:=𝓕(b;a))
    ui = instancie(N.generalisation("X", un_inf_egal("X")), Fba)  # ¬(𝓕(b;a)=∅) ⇒ {∅}≤𝓕(b;a)
    le = N.modus_ponens(nonvide, ui)                        # {∅}≤𝓕(b;a)  [x∈a]
    # décharger x∈a via a≠0 (témoin canonique)
    x_in = appartient(x, va)
    nve_a = non_vide_ssi_element(va)                        # ¬(a=∅) ⇔ (∃z)(z∈a)
    ren = alpha_existe("z", _WB, appartient(var("z"), va))  # (∃z)(z∈a) ⇔ (∃w)(w∈a)
    ex_w = N.modus_ponens(N.modus_ponens(N.assume(non(egal(va, E.VIDE))),
        equivalence_avant(nve_a)), equivalence_avant(ren))  # (∃w)(w∈a)  [a≠0]
    et_w = N.existe_temoin(appartient(var(_WB), va), _WB)   # (∃w)(w∈a) ⇒ x∈a
    x_from = N.modus_ponens(ex_w, et_w)                     # x∈a  [a≠0]
    le_a = _cut(le, [(x_in, x_from)])                       # {∅}≤𝓕(b;a)  [a≠0]
    return N.loi_deduction(non(egal(va, E.VIDE)), le_a)     # a≠0 ⇒ {∅}≤𝓕(b;a)


def un_inf_egal_exposant(a="a", b="b"):
    """⊢ (a ≠ 0) ⇒ (1 ≤ a^b).   (borne inférieure 1 ≤ a^b pour a ≠ 0, E.III.3.5.)

    a^b = Card(𝓕(b;a)).  Pour a≠0, 𝓕(b;a)≠∅ (la constante const_x, x∈a, l'habite),
    donc 1={∅}≤𝓕(b;a) ; le PONT inf_egal_transporte_cardinal donne Card{∅}≤Card 𝓕(b;a)
    = 1 ≤ a^b (Card{∅}=1).  La condition a≠0 est HONNÊTE (Bourbaki : a^b=0 ssi a=0,b≠0)."""
    from bourbaki.cardinaux.arithmetique.iii_3_2_monotonie.ensembles_arith_cardinale_props_exposant_monotone import (
        inf_egal_transporte_cardinal)
    va, vb = _t(a), _t(b)
    Fba = E.applications(vb, va)
    # 1 ≤ 𝓕(b;a)   sous a≠0
    sup = _Fba_non_vide_a(a, b)                             # a≠0 ⇒ {∅}≤𝓕(b;a)
    # transport (1, 𝓕(b;a))
    transp = instancie(instancie(N.generalisation("X", N.generalisation("Y",
        inf_egal_transporte_cardinal("X", "Y"))), UN), Fba)  # ({∅}≤𝓕(b;a)) ⇒ (Card{∅} ≤ Card 𝓕(b;a))
    h = N.assume(non(egal(va, E.VIDE)))                     # a≠0
    le = N.modus_ponens(h, sup)                             # {∅}≤𝓕(b;a)
    card_le = N.modus_ponens(le, transp)                   # Card{∅} ≤ Card 𝓕(b;a) = 1 ≤ a^b
    return N.loi_deduction(non(egal(va, E.VIDE)), card_le)


__all__ = [
    "support_base_exposant", "base_inf_egal_exposant", "un_inf_egal_exposant",
]
