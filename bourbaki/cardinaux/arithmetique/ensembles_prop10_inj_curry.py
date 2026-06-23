"""§III.3.5 — PROPOSITION 10 (forme CURRYING), DIRECTION A : a^(b·c) ≤ (a^b)^c.

        ⊢ inf_egal_card(𝓕(B×C; A), 𝓕(C; 𝓕(B;A)))                  (= a^(b·c) ≤ (a^b)^c)

INJECTION DE CURRY  Λ : 𝓕(B×C;A) ↪ 𝓕(C; 𝓕(B;A)),  f ↦ Λval0(f) = ((curry0(f),C),𝓕(B;A)),
où curry0(f) = { (c, f_c) | c∈C },  f_c = slice0(f,c) = ((tranche0(f,c),B),A),
tranche0(f,c) = { (b, G(b,c)) | b∈B },  G = graphe_de(f).  (Représentation FIDÈLE AU
PONT : f(b,c) = graphe_de(f)((b,c)), cf. `ensembles_prop10_close`.)

C'est l'ANALOGUE EXACT de `inf_egal_phi` (Prop 9, `ensembles_prop9_close`) : on construit
le GRAPHE-TERME W_Λ = { (f, Λval0(f)) | f∈𝓕(B×C;A) } et on ferme les QUATRE conjoints de
est_injection_de(W_Λ, 𝓕(B×C;A), 𝓕(C;𝓕(B;A))) :

  (1) W_Lambda_fonctionnel       — C54 (graphe-terme automatique) ;
  (2) W_Lambda_domaine           — C54 ;
  (3) W_Lambda_image_incluse     — DIRECT depuis `lambda_val0_dans_codomaine` (CLOS) :
        f∈𝓕(B×C;A) ⇒ Λval0(f)∈𝓕(C;𝓕(B;A)) ;
  (4) W_Lambda_injective         — EXTENSIONNALITÉ À DEUX NIVEAUX :
        Λval0(f₁)=Λval0(f₂) ⟹ (strip triple) curry0(f₁)=curry0(f₂)
        ⟹ (niv.1, application_egale_par_valeurs sur 𝓕(C;𝓕(B;A))) slice0(f₁,c)=slice0(f₂,c) ∀c∈C
        ⟹ (strip triple) tranche0(f₁,c)=tranche0(f₂,c) ∀c
        ⟹ (niv.0, graphe_terme_valeur) G₁(b,c)=G₂(b,c) ∀(b,c)∈B×C
        ⟹ (application_egale_par_valeurs sur 𝓕(B×C;A)) f₁=f₂.

Puis est_injection_de assemblé + S5 (témoin F:=W_Λ) ⟹
  inf_egal_curry() ⊢ inf_egal_card(𝓕(B×C;A), 𝓕(C;𝓕(B;A))).

C'est la Direction A de la Proposition 10 — un THÉORÈME RÉEL (a^(b·c) ≤ (a^b)^c),
indépendant de la Direction B (uncurry).  Avec inf_egal_curry + Direction B + cantor_bernstein
+ _prop1_direct_t, on CLÔT inconditionnellement la Proposition 10.

theorie_ensembles INCHANGÉE (22 axiomes) ; AUCUN fichier existant modifié.
═══════════════════════════════════════════════════════════════════════════════
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (Terme, var, egal, et, appartient, inclus,
                                       pourtout, impl, subst_t)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, equivalence_transitivite, instancie)
from bourbaki.logique.i_3_quantifies.tactiques_abrege_quantif import existe_elimination
from bourbaki.logique.i_4_egalitaires.tactiques_abrege_egalite import (
    symetrie, composer_egalites, congruence_terme)
from bourbaki.ensembles.ii_2_couples_produit.ensembles_couples import (
    couple_egal_implique_composantes)
from bourbaki.ensembles.fonctions.ii_3_6_fonction_terme.ensembles_fonction_terme import (
    graphe_terme_fonctionnel, membre_graphe_terme)
from bourbaki.cardinaux.ensembles_cantor import (
    graphe_terme_domaine, graphe_terme_valeur)
from bourbaki.cardinaux.ensembles_cardinaux import (
    est_injection_de, inf_egal_card)
from bourbaki.cardinaux.arithmetique.ensembles_graphe_de import graphe_de
from bourbaki.ensembles.fonctions.hors_ii_3.ii_5_produit_famille.ensembles_application_valeur import (
    application_egale_par_valeurs, egalite_valeurs_application)
from bourbaki.cardinaux.arithmetique.ensembles_prop10_currying import (
    espace_BA, domaine_lambda, codomaine_lambda)
from bourbaki.cardinaux.arithmetique.ensembles_prop10_close import (
    tranche0, slice0, curry0, lambda_val0, lambda_val0_dans_codomaine,
    _PTB, _PTC)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# ═══════════════════════════════════════════════════════════════════════════════
#  LIANTS — repris de ensembles_prop10_close (mêmes choix d'évitement) :
#   • « f »  : point courant du graphe W_Λ (niveau 2) ;
#   • « t » (=_PTC) : point courant de curry0 (la variable c, niveau 1) ;
#   • « x » (=_PTB) : point courant de tranche0 (la variable b, niveau 0) ;
#   • « m » : liant τ de la valeur G(b,c).
# ═══════════════════════════════════════════════════════════════════════════════
_POINT = "f"          # point courant du graphe W_Λ (niveau 2)


# ═══════════════════════════════════════════════════════════════════════════════
#  cut helper (loi_deduction puis modus_ponens, comme prop9_close._cut)
# ═══════════════════════════════════════════════════════════════════════════════
def _cut(thm, paires):
    """Remplace chaque hypothèse `hyp` de `thm` par sa preuve `preuve`."""
    out = thm
    for hyp_formule, preuve in paires:
        out = N.modus_ponens(preuve, N.loi_deduction(hyp_formule, out))
    return out


# ═══════════════════════════════════════════════════════════════════════════════
#  LE GRAPHE W_Λ DE Λ  (témoin de l'injection)
# ═══════════════════════════════════════════════════════════════════════════════
def W_Lambda(a="A", b="B", c="C"):
    """W_Λ := graphe_terme( 𝓕(B×C;A) , Λval0(f) , « f » ) = { (f, Λval0(f)) | f∈𝓕(B×C;A) }."""
    va, vb, vc = _t(a), _t(b), _t(c)
    return E.graphe_terme(domaine_lambda(va, vb, vc),
                          lambda_val0(var(_POINT), va, vb, vc), _POINT)


# ── CONJOINT 1 — W_Λ fonctionnel  (C54, automatique) ──────────────────────────
def W_Lambda_fonctionnel(a="A", b="B", c="C"):
    """⊢ est_fonctionnel(W_Λ).   (graphe-terme toujours fonctionnel, C54.)"""
    va, vb, vc = _t(a), _t(b), _t(c)
    return graphe_terme_fonctionnel(domaine_lambda(va, vb, vc),
                                    lambda_val0(var(_POINT), va, vb, vc), _POINT, "y")


# ── CONJOINT 2 — dom W_Λ = 𝓕(B×C;A)  (C54, automatique) ───────────────────────
def W_Lambda_domaine(a="A", b="B", c="C"):
    """⊢ dom(W_Λ) = 𝓕(B×C; A).   (Λ définie sur tout 𝓕(B×C;A) ; C54.)"""
    va, vb, vc = _t(a), _t(b), _t(c)
    return graphe_terme_domaine(domaine_lambda(va, vb, vc),
                                lambda_val0(var(_POINT), va, vb, vc), _POINT, "y", "z")


def W_Lambda_valeur(f="g", a="A", b="B", c="C"):
    """{f ∈ 𝓕(B×C;A)} ⊢ W_Λ(f) = Λval0(f).   (point d'évaluation NOM ≠ f,x,t,y,m.)"""
    if not isinstance(f, str):
        raise ValueError("W_Lambda_valeur : point d'évaluation = NOM (string)")
    va, vb, vc = _t(a), _t(b), _t(c)
    return graphe_terme_valeur(domaine_lambda(va, vb, vc),
                               lambda_val0(var(_POINT), va, vb, vc), f, _POINT, "y")


# ═══════════════════════════════════════════════════════════════════════════════
#  CONJOINT 3 — image(W_Λ, 𝓕(B×C;A)) ⊂ 𝓕(C;𝓕(B;A))   (BIEN-DÉFINITION)
#   DIRECT depuis lambda_val0_dans_codomaine (CLOS) : f∈dom ⇒ Λval0(f)∈cod.
# ═══════════════════════════════════════════════════════════════════════════════
def W_Lambda_image_incluse(a="A", b="B", c="C"):
    """⊢ image(W_Λ, 𝓕(B×C;A)) ⊂ 𝓕(C;𝓕(B;A)).

    z∈W_Λ⟨dom⟩ ⇔ (∃t)(t∈dom et (t,z)∈W_Λ).  (t,z)∈W_Λ ⇔ (t∈dom et z=Λval0(t))
    (membre_graphe_terme), donc z=Λval0(t) avec t∈dom ; lambda_val0_dans_codomaine
    ⊢ Λval0(t)∈cod, d'où z∈cod (Leibniz).  Conclusion = inclusion."""
    va, vb, vc = _t(a), _t(b), _t(c)
    dom = domaine_lambda(va, vb, vc)
    cod = codomaine_lambda(va, vb, vc)
    W = W_Lambda(va, vb, vc)
    LAM = lambda_val0(var(_POINT), va, vb, vc)       # Λval0(f), point f
    # ⚠ le témoin doit éviter « t » (=_PTC, binder de curry0 DANS W → libre dans la
    # représentation τ du graphe-terme) ET « x »,« m » : on prend « tt ».
    WIT = "tt"
    vz, vt = var("z"), var(WIT)
    from bourbaki.logique.i_3_quantifies.tactiques_abrege_quantif import alpha_existe

    # z∈W⟨dom⟩ ⇔ (∃tt)(tt∈dom et (tt,z)∈W)  (AXIOME_IMAGE ; liant frais α-renommé tt)
    ax_img = N.axiome(E.theorie_ensembles(), E.AXIOME_IMAGE)
    img0 = instancie(instancie(instancie(ax_img, W), dom), vz)
    impl_LtoEX = img0.conclusion.sous[0].sous[0].sous[0]
    rhs_ex = impl_LtoEX.sous[1]
    assert rhs_ex.tag == "exists"
    nom = rhs_ex.lieur
    inner = et(appartient(var(nom), dom), appartient(E.couple(var(nom), vz), W))
    ren = alpha_existe(nom, WIT, inner)
    img_car = equivalence_transitivite(img0, ren)    # z∈W⟨dom⟩ ⇔ (∃tt)(tt∈dom et (tt,z)∈W)

    # (tt,z)∈W ⇔ (tt∈dom et z=Λval0(tt))   [membre_graphe_terme, point f, coords tt,z]
    mem = membre_graphe_terme(dom, LAM, WIT, "z", _POINT, "y")  # ((tt,z)∈W)⇔(tt∈dom et z=Λval0[tt])
    Lam_t = subst_t(vt, _POINT, LAM)                 # Λval0(tt) = Λval0[f:=tt]

    body = et(appartient(vt, dom), appartient(E.couple(vt, vz), W))
    hb = N.assume(body)
    t_in = conjonction_elim_gauche(hb)               # tt∈dom
    tz_in = conjonction_elim_droite(hb)              # (tt,z)∈W
    cond = N.modus_ponens(tz_in, equivalence_avant(mem))   # tt∈dom et z=Λval0(tt)
    z_eq = conjonction_elim_droite(cond)             # z=Λval0(tt)
    # Λval0(tt)∈cod  (lambda_val0_dans_codomaine instancié en tt ; hyp tt∈dom déchargée)
    lam_t_in = _lambda_cod_en_point(va, vb, vc, vt, t_in)   # Λval0(tt)∈cod
    # z∈cod  (z=Λval0(tt), Leibniz)
    z_in_cod = N.modus_ponens(lam_t_in, equivalence_arriere(N.modus_ponens(
        z_eq, N.s6(vz, Lam_t, "w", appartient(var("w"), cod)))))   # z∈cod
    ex_imp = existe_elimination(N.loi_deduction(body, z_in_cod), WIT)  # (∃tt)body ⇒ z∈cod
    h_z = N.assume(appartient(vz, E.image(W, dom)))
    ex = N.modus_ponens(h_z, equivalence_avant(img_car))   # (∃t)body
    z_in = N.modus_ponens(ex, ex_imp)                # z∈cod
    return N.generalisation("z", N.loi_deduction(appartient(vz, E.image(W, dom)), z_in))


def _lambda_cod_en_point(va, vb, vc, vt, t_in_thm):
    """De {t∈dom} (t_in_thm) ⊢ Λval0(t) ∈ cod, par instanciation-terme de
    lambda_val0_dans_codomaine au point t (hyp f∈dom déchargée)."""
    dom = domaine_lambda(va, vb, vc)
    # lambda_val0_dans_codomaine("f",…) : ⊢ f∈dom ⇒ Λval0(f)∈cod  (CLOS, déjà une implication)
    base_imp = lambda_val0_dans_codomaine("f", va, vb, vc)   # ⊢ f∈dom ⇒ Λval0(f)∈cod
    gen = N.generalisation("f", base_imp)            # (∀f)(f∈dom ⇒ Λval0(f)∈cod)
    inst = instancie(gen, vt)                        # t∈dom ⇒ Λval0(t)∈cod
    return N.modus_ponens(t_in_thm, inst)            # Λval0(t)∈cod   [hyp t∈dom]


# ═══════════════════════════════════════════════════════════════════════════════
#  CONJOINT 4 — INJECTIVITÉ de Λ  (extensionnalité À DEUX NIVEAUX)
# ───────────────────────────────────────────────────────────────────────────────
#   Λval0(f₁)=Λval0(f₂) ⟹ curry0(f₁)=curry0(f₂) (strip triple)
#   ⟹ slice0(f₁,c)=slice0(f₂,c) ∀c∈C (niveau 1, application_egale_par_valeurs)
#   ⟹ tranche0(f₁,c)=tranche0(f₂,c) (strip triple)
#   ⟹ G₁(b,c)=G₂(b,c) ∀(b,c)∈B×C (niveau 0, graphe_terme_valeur)
#   ⟹ f₁=f₂ (application_egale_par_valeurs sur 𝓕(B×C;A)).
# ═══════════════════════════════════════════════════════════════════════════════
def _strip_triple(triple_eq, g1, mid, top, g2):
    """De ⊢ ((g₁,mid),top)=((g₂,mid),top), tire ⊢ g₁=g₂.  (deux décompos de couples.)"""
    inner1 = E.couple(g1, mid)
    inner2 = E.couple(g2, mid)
    comp1 = N.modus_ponens(triple_eq,
                           couple_egal_implique_composantes(inner1, top, inner2, top))
    inner_eq = conjonction_elim_gauche(comp1)        # (g₁,mid)=(g₂,mid)
    comp2 = N.modus_ponens(inner_eq,
                           couple_egal_implique_composantes(g1, mid, g2, mid))
    return conjonction_elim_gauche(comp2)            # g₁=g₂


def _lambda_egal_donne_curry(vf1, vf2, va, vb, vc):
    """{Λval0(f₁)=Λval0(f₂)} ⊢ curry0(f₁)=curry0(f₂).

    Λval0(fᵢ)=((curry0(fᵢ),C),𝓕(B;A)) ; strip triple (couple externe + paire interne)."""
    FBA = espace_BA(va, vb)
    cu1, cu2 = curry0(vf1, va, vb, vc), curry0(vf2, va, vb, vc)
    L1 = lambda_val0(vf1, va, vb, vc)
    L2 = lambda_val0(vf2, va, vb, vc)
    h = N.assume(egal(L1, L2))                       # Λval0(f₁)=Λval0(f₂)
    return _strip_triple(h, cu1, vc, FBA, cu2)       # curry0(f₁)=curry0(f₂)


# ── NIVEAU 1 : curry0 égaux ⇒ slice0(f₁,c)=slice0(f₂,c) pour c∈C ───────────────
def _slice_egal_en_point(vf1, vf2, va, vb, vc, c_nom):
    """{ curry0(f₁)=curry0(f₂),  c∈C } ⊢ slice0(f₁,c) = slice0(f₂,c)   (c_nom : NOM).

    graphe_terme_valeur : curry0(fᵢ)(c)=slice0(fᵢ,c) sous c∈C ; curry0(f₁)=curry0(f₂)
    ⇒ curry0(f₁)(c)=curry0(f₂)(c) (congruence) ; chaîner."""
    vcpt = var(c_nom)
    cu1, cu2 = curry0(vf1, va, vb, vc), curry0(vf2, va, vb, vc)
    sl1 = slice0(vf1, vcpt, va, vb)                  # slice0(f₁,c)
    sl2 = slice0(vf2, vcpt, va, vb)                  # slice0(f₂,c)
    # le terme-valeur de curry0 : slice0(f,_PTC) ; en c via graphe_terme_valeur
    sl_term1 = slice0(vf1, var(_PTC), va, vb)
    sl_term2 = slice0(vf2, var(_PTC), va, vb)
    val1 = graphe_terme_valeur(vc, sl_term1, c_nom, _PTC, "y")  # {c∈C} ⊢ curry0(f₁)(c)=slice0(f₁,c)
    val2 = graphe_terme_valeur(vc, sl_term2, c_nom, _PTC, "y")  # {c∈C} ⊢ curry0(f₂)(c)=slice0(f₂,c)
    h_eq = N.assume(egal(cu1, cu2))                  # curry0(f₁)=curry0(f₂)
    # curry0(f₁)(c)=curry0(f₂)(c)  (congruence valeur(·,c,"y"))
    cu1c_eq_cu2c = N.modus_ponens(h_eq,
        congruence_terme(cu1, cu2, E.valeur(var("w"), vcpt, "y")))   # curry0(f₁)(c)=curry0(f₂)(c)
    # slice0(f₁,c)=curry0(f₁)(c)  (symétrie de val1)
    sl1_eq_cu1c = N.modus_ponens(val1, symetrie(E.valeur(cu1, vcpt, "y"), sl1))  # slice0(f₁,c)=curry0(f₁)(c)
    # slice0(f₁,c)=curry0(f₁)(c)=curry0(f₂)(c)=slice0(f₂,c)
    return composer_egalites(composer_egalites(sl1_eq_cu1c, cu1c_eq_cu2c), val2)


# ── NIVEAU 0 : tranche0 égaux ⇒ G₁((b,c))=G₂((b,c)) pour (b,c)∈B×C ─────────────
def _tranche_egal_de_slice(slice_eq, vf1, vf2, va, vb, vc, vcpt):
    """De ⊢ slice0(f₁,c)=slice0(f₂,c), tire ⊢ tranche0(f₁,c)=tranche0(f₂,c).
    slice0(fᵢ,c)=((tranche0(fᵢ,c),B),A) ; strip triple."""
    tr1 = tranche0(vf1, vcpt, va, vb)
    tr2 = tranche0(vf2, vcpt, va, vb)
    return _strip_triple(slice_eq, tr1, vb, va, tr2)   # tranche0(f₁,c)=tranche0(f₂,c)


def _val_G_y(vf, vbpt, vcpt):
    """G(b,c) avec binder « y » = valeur(graphe_de(f), (b,c), « y »).

    (la machinerie graphe_terme_valeur produit la valeur avec binder « y » ; on
    travaille en « y » tout au long de l'extensionnalité de niveau 0.)"""
    return E.valeur(graphe_de(vf), E.couple(vbpt, vcpt), "y")


def _Gval_egal_en_couple(vf1, vf2, va, vb, vc, b_nom, c_nom):
    """{ tranche0(f₁,c)=tranche0(f₂,c), b∈B } ⊢ G₁((b,c)) = G₂((b,c))   (binder « y »).

    graphe_terme_valeur : tranche0(fᵢ,c)(b)=Tᵢ[b]=G_i((b,c)) sous b∈B ;
    tranche0(f₁,c)=tranche0(f₂,c) ⇒ tranche0(f₁,c)(b)=tranche0(f₂,c)(b) ; chaîner.

    ⚠ tranche0(f,c) = graphe_terme(B, valeur(graphe_de(f),(x,c),« m »), « x »).
    graphe_terme_valeur produit donc tranche0(fᵢ,c)(b) = valeur(graphe_de(fᵢ),(b,c),« m »)
    (binder « m » substitué pour x:=b).  On α-renomme « m »→« y » des deux côtés pour
    atterrir sur _val_G_y (binder « y »), consommable par application_egale_par_valeurs."""
    vbpt = var(b_nom)
    vcpt = var(c_nom)
    G1, G2 = graphe_de(vf1), graphe_de(vf2)
    bc = E.couple(vbpt, vcpt)
    tr1 = tranche0(vf1, vcpt, va, vb)
    tr2 = tranche0(vf2, vcpt, va, vb)
    # termes-valeur internes de tranche0 (binder _VAL="m") évalués en x:=b :
    from bourbaki.cardinaux.arithmetique.ensembles_prop10_close import _val_G
    T1 = _val_G(vf1, var(_PTB), vcpt)                # valeur(G₁,(x,c),"m")
    T2 = _val_G(vf2, var(_PTB), vcpt)                # valeur(G₂,(x,c),"m")
    val1 = graphe_terme_valeur(vb, T1, b_nom, _PTB, "y")  # {b∈B} ⊢ tranche0(f₁,c)(b)=T1[b]=valeur(G₁,(b,c),"m")
    val2 = graphe_terme_valeur(vb, T2, b_nom, _PTB, "y")  # {b∈B} ⊢ tranche0(f₂,c)(b)=valeur(G₂,(b,c),"m")
    T1b = subst_t(vbpt, _PTB, T1)                    # valeur(G₁,(b,c),"m")
    T2b = subst_t(vbpt, _PTB, T2)                    # valeur(G₂,(b,c),"m")
    h_eq = N.assume(egal(tr1, tr2))                  # tranche0(f₁,c)=tranche0(f₂,c)
    # tranche0(f₁,c)(b)=tranche0(f₂,c)(b)  (congruence valeur(·,b,"y"))
    tr1b_eq_tr2b = N.modus_ponens(h_eq,
        congruence_terme(tr1, tr2, E.valeur(var("w"), vbpt, "y")))   # tr₁(b)=tr₂(b)
    # T1[b]=tr₁(b)  (symétrie de val1)
    T1b_eq_tr1b = N.modus_ponens(val1, symetrie(E.valeur(tr1, vbpt, "y"), T1b))  # T1[b]=tr₁(b)
    # T1[b]=tr₁(b)=tr₂(b)=T2[b]   i.e. valeur(G₁,(b,c),"m")=valeur(G₂,(b,c),"m")
    Tm_eq = composer_egalites(composer_egalites(T1b_eq_tr1b, tr1b_eq_tr2b), val2)
    # α-renommer « m »→« y » des deux côtés : valeur(Gᵢ,(b,c),"m")=valeur(Gᵢ,(b,c),"y")
    r1 = appartient(E.couple(bc, var("m")), G1)      # ((b,c),m)∈G₁
    r2 = appartient(E.couple(bc, var("m")), G2)      # ((b,c),m)∈G₂
    reb1 = N.alpha_tau(r1, "m", "y")                 # valeur(G₁,(b,c),"m")=valeur(G₁,(b,c),"y")
    reb2 = N.alpha_tau(r2, "m", "y")                 # valeur(G₂,(b,c),"m")=valeur(G₂,(b,c),"y")
    # valeur(G₁,(b,c),"y") = valeur(G₁,(b,c),"m") = valeur(G₂,(b,c),"m") = valeur(G₂,(b,c),"y")
    # reb1 : T1b = _val_G_y(f₁)  (i.e. G₁(b,c)[m]=G₁(b,c)[y]) ; on veut G₁(b,c)[y]=G₁(b,c)[m] :
    y1_eq_m1 = N.modus_ponens(reb1, symetrie(T1b, _val_G_y(vf1, vbpt, vcpt)))  # G₁(b,c)[y]=G₁(b,c)[m]
    return composer_egalites(composer_egalites(y1_eq_m1, Tm_eq), reb2)  # G₁(b,c)[y]=G₂(b,c)[y]


def _valeurs_coincident_sur_produit(vf1, vf2, va, vb, vc):
    """{ curry0(f₁)=curry0(f₂) } ⊢ (∀w)(w∈B×C ⇒ G₁(w)=G₂(w))   (binder « y », Gᵢ=graphe_de(fᵢ)).

    Décompose w∈B×C en (b,c) (axiome produit) ; niveau 1 (curry0 égaux ⇒ slice0 égaux
    via _slice_egal_en_point) ; niveau 0 (tranche0 égaux ⇒ Gᵢ((b,c)) égaux via
    _Gval_egal_en_couple) ; Leibniz w=(b,c).  C'est l'hypothèse des valeurs de
    application_egale_par_valeurs(f₁,f₂,B×C,A)."""
    from bourbaki.ensembles.familles.ii_2_produit_deux_ensembles.ensembles_produit import _instance_produit
    G1, G2 = graphe_de(vf1), graphe_de(vf2)
    BC = E.produit(vb, vc)
    cu1, cu2 = curry0(vf1, va, vb, vc), curry0(vf2, va, vb, vc)
    vw = var("w0")                                   # point courant du produit (≠ "w" trou congruence)
    # cible : valeur(G₁,w0,"y")=valeur(G₂,w0,"y")
    val_eq = egal(E.valeur(G1, vw, "y"), E.valeur(G2, vw, "y"))

    # w0∈B×C ⇔ (∃b)(∃c)(w0=(b,c) et b∈B et c∈C)  (axiome produit, binders renommés bb,cc)
    from bourbaki.logique.i_3_quantifies.tactiques_abrege_quantif import alpha_existe
    car0 = _instance_produit(vb, vc, vw)             # w0∈B×C ⇔ (∃p)(∃q)(w0=(p,q) et p∈B et q∈C)
    # repérer les binders p,q de _instance_produit et les renommer en bb,cc
    rhs = car0.conclusion.sous[0].sous[0].sous[0].sous[1]   # le (∃p)(∃q)(...)
    assert rhs.tag == "exists"
    p_nom = rhs.lieur                                # binder externe (« p »)
    inner_ex = rhs.sous[0]
    assert inner_ex.tag == "exists"
    q_nom = inner_ex.lieur                           # binder interne (« q »)
    # corps : w0=(p,q) et p∈B et q∈C
    body_pq = et(et(egal(vw, E.couple(var(p_nom), var(q_nom))),
                    appartient(var(p_nom), vb)),
                 appartient(var(q_nom), vc))
    hb = N.assume(body_pq)
    w_eq = conjonction_elim_gauche(conjonction_elim_gauche(hb))   # w0=(p,q)
    p_inB = conjonction_elim_droite(conjonction_elim_gauche(hb))  # p∈B
    q_inC = conjonction_elim_droite(hb)                          # q∈C
    # niveau 1 : slice0(f₁,q)=slice0(f₂,q)  sous curry0 eq et q∈C
    sl_eq = _slice_egal_en_point(vf1, vf2, va, vb, vc, q_nom)
    sl_eq = _cut(sl_eq, [(appartient(var(q_nom), vc), q_inC)])    # {curry0 eq} ⊢ slice0(f₁,q)=slice0(f₂,q)
    # niveau 0a : tranche0(f₁,q)=tranche0(f₂,q)
    tr_eq = _tranche_egal_de_slice(sl_eq, vf1, vf2, va, vb, vc, var(q_nom))
    # niveau 0b : G₁((p,q))=G₂((p,q))  sous tranche0 eq et p∈B
    gval = _Gval_egal_en_couple(vf1, vf2, va, vb, vc, p_nom, q_nom)
    gval = _cut(gval, [(egal(tranche0(vf1, var(q_nom), va, vb),
                             tranche0(vf2, var(q_nom), va, vb)), tr_eq),
                       (appartient(var(p_nom), vb), p_inB)])       # {curry0 eq} ⊢ G₁((p,q))=G₂((p,q))
    # Leibniz : w0=(p,q) ⇒ G₁(w0)=G₂(w0)
    pq = E.couple(var(p_nom), var(q_nom))
    # G₁((p,q))[y]=G₁(w0)[y] via w0=(p,q)  (congruence valeur(G₁,·,"y"))
    g1_pq_eq_w = N.modus_ponens(w_eq,
        congruence_terme(vw, pq, E.valeur(G1, var("@h"), "y"), "@h"))   # G₁(w0)[y]=G₁((p,q))[y]
    g2_pq_eq_w = N.modus_ponens(w_eq,
        congruence_terme(vw, pq, E.valeur(G2, var("@h"), "y"), "@h"))   # G₂(w0)[y]=G₂((p,q))[y]
    # G₁(w0)[y]=G₁((p,q))[y]=G₂((p,q))[y]→G₂(w0)[y]
    g2w_eq = N.modus_ponens(g2_pq_eq_w,
        symetrie(E.valeur(G2, vw, "y"), E.valeur(G2, pq, "y")))     # G₂((p,q))[y]=G₂(w0)[y]
    val_w = composer_egalites(composer_egalites(g1_pq_eq_w, gval), g2w_eq)  # G₁(w0)[y]=G₂(w0)[y]
    # éliminer les témoins p,q (la conclusion val_eq ne contient ni p ni q)
    ex_imp = existe_elimination(existe_elimination(
        N.loi_deduction(body_pq, val_w), q_nom), p_nom)            # (∃p)(∃q)body ⇒ val_eq
    h_w = N.assume(appartient(vw, BC))
    ex = N.modus_ponens(h_w, equivalence_avant(car0))             # (∃p)(∃q)body
    val_final = N.modus_ponens(ex, ex_imp)                       # val_eq  [hyp w0∈B×C, curry0 eq]
    return N.generalisation("w0", N.loi_deduction(appartient(vw, BC), val_final))


def lambda_injective_sous_appartenance(f1="f1", f2="f2", a="A", b="B", c="C"):
    """{ f₁∈𝓕(B×C;A), f₂∈𝓕(B×C;A), Λval0(f₁)=Λval0(f₂) } ⊢ f₁ = f₂.

    INJECTIVITÉ de Λ (cœur, extensionnalité à 2 niveaux).  Λval0(f₁)=Λval0(f₂)
    ⇒ curry0(f₁)=curry0(f₂) (_lambda_egal_donne_curry) ⇒ valeurs de Gᵢ coïncident
    sur B×C (_valeurs_coincident_sur_produit) ; application_egale_par_valeurs(f₁,f₂,B×C,A)
    conclut f₁=f₂."""
    vf1, vf2, va, vb, vc = _t(f1), _t(f2), _t(a), _t(b), _t(c)
    BC = E.produit(vb, vc)
    # curry0(f₁)=curry0(f₂)  de Λval0 eq
    cu_eq = _lambda_egal_donne_curry(vf1, vf2, va, vb, vc)        # {Λval0 eq} ⊢ curry0 eq
    # valeurs coïncident sur B×C
    vals = _valeurs_coincident_sur_produit(vf1, vf2, va, vb, vc)  # {curry0 eq} ⊢ (∀w0)(w0∈B×C⇒G₁=G₂)
    vals = _cut(vals, [(cu_eq.conclusion, cu_eq)])               # {Λval0 eq} ⊢ vals
    # application_egale_par_valeurs : {f₁∈𝓕,f₂∈𝓕, (∀x)(x∈B×C⇒G₁(x)=G₂(x))} ⊢ f₁=f₂
    aev = application_egale_par_valeurs(vf1, vf2, BC, va)
    # son hyp de valeurs utilise le binder « x » (egalite_valeurs_application) ; on aligne
    # notre vals (binder « w0 ») sur « x » par α-renommage du ∀.  ⚠ on NE PEUT PAS
    # généraliser sur « x » (x est libre dans l'hyp Λval0 eq — τ-leak du binder tranche0) :
    # on utilise alpha_pour_tout (équivalence CLOSE renommant le liant lié, x∉body), qui
    # ne fait QU'un modus_ponens — pas de généralisation sur x au niveau des hypothèses.
    vals_x = _renomme_pourtout_vals(vals, vf1, vf2, BC)
    return _cut(aev, [(vals_x.conclusion, vals_x)])              # {f₁∈𝓕,f₂∈𝓕,Λval0 eq} ⊢ f₁=f₂


def _renomme_pourtout_vals(vals_thm, vf1, vf2, BC):
    """Aligne (∀w0)(w0∈BC⇒G₁(w0)=G₂(w0))  →  (∀x)(x∈BC⇒G₁(x)=G₂(x))   (binder « x »).

    Via alpha_pour_tout (équivalence close renommant le liant w0→x ; « x » non libre dans
    le CORPS R(w0), seul l'extérieur Λval0 eq porte le τ-leak de x).  La cible est
    LITTÉRALEMENT egalite_valeurs_application(f₁,f₂,BC) (binder « x », valeur défaut)."""
    from bourbaki.logique.i_3_quantifies.tactiques_abrege_quantif import alpha_pour_tout
    G1, G2 = graphe_de(vf1), graphe_de(vf2)
    vw = var("w0")
    body = impl(appartient(vw, BC),
                egal(E.valeur(G1, vw, "y"), E.valeur(G2, vw, "y")))   # R(w0)
    equiv = alpha_pour_tout("w0", "x", body)         # (∀w0)R ⇔ (∀x)(x|w0)R
    return N.modus_ponens(vals_thm, equivalence_avant(equiv))   # Γ ⊢ (∀x)(x∈BC⇒G₁(x)=G₂(x))


def W_Lambda_injective(a="A", b="B", c="C"):
    """⊢ injective_dans(W_Λ, 𝓕(B×C;A)).

    (∀u)(∀u')((u∈dom et u'∈dom et W(u)=W(u')) ⇒ u=u').  W(·)=Λval0(·) (W_Lambda_valeur,
    sous ·∈dom) ⇒ Λval0(f₁)=Λval0(f₂) ; lambda_injective_sous_appartenance ⇒ f₁=f₂.

    Variables-fonction nommées « f1 », « f2 » (≠ liants internes u,v,z de la machinerie
    graphe_terme_valeur) puis α-renommées « u »,« up » pour s'apparier à injective_dans."""
    va, vb, vc = _t(a), _t(b), _t(c)
    dom = domaine_lambda(va, vb, vc)
    Wt = W_Lambda(va, vb, vc)
    vf1, vf2 = var("f1"), var("f2")
    L1 = lambda_val0(vf1, va, vb, vc)
    L2 = lambda_val0(vf2, va, vb, vc)

    hyp = et(et(appartient(vf1, dom), appartient(vf2, dom)),
             egal(E.valeur(Wt, vf1), E.valeur(Wt, vf2)))   # f₁∈dom et f₂∈dom et W(f₁)=W(f₂)
    h = N.assume(hyp)
    f1_in = conjonction_elim_gauche(conjonction_elim_gauche(h))
    f2_in = conjonction_elim_droite(conjonction_elim_gauche(h))
    W_eq = conjonction_elim_droite(h)                            # W(f₁)=W(f₂)
    Wf1 = _cut(W_Lambda_valeur("f1", va, vb, vc), [(appartient(vf1, dom), f1_in)])  # W(f₁)=Λval0(f₁)
    Wf2 = _cut(W_Lambda_valeur("f2", va, vb, vc), [(appartient(vf2, dom), f2_in)])  # W(f₂)=Λval0(f₂)
    lam_eq = composer_egalites(composer_egalites(
        N.modus_ponens(Wf1, symetrie(E.valeur(Wt, vf1), L1)), W_eq), Wf2)   # Λval0(f₁)=Λval0(f₂)
    f_eq = lambda_injective_sous_appartenance("f1", "f2", va, vb, vc)
    f_eq = _cut(f_eq, [(appartient(vf1, dom), f1_in),
                       (appartient(vf2, dom), f2_in),
                       (egal(L1, L2), lam_eq)])                 # f₁=f₂  [hyp]
    inner = N.loi_deduction(hyp, f_eq)
    raw = N.generalisation("f1", N.generalisation("f2", inner))  # (∀f1)(∀f2)…
    inst = instancie(instancie(raw, var("u")), var("up"))        # P[f1:=u, f2:=up]
    return N.generalisation("u", N.generalisation("up", inst))   # (∀u)(∀up)… = injective_dans


# ═══════════════════════════════════════════════════════════════════════════════
#  DIRECTION A : 𝓕(B×C;A) ≤ 𝓕(C;𝓕(B;A))   (Λ est une injection)
# ═══════════════════════════════════════════════════════════════════════════════
def W_Lambda_est_injection(a="A", b="B", c="C"):
    """⊢ est_injection_de(W_Λ, 𝓕(B×C;A), 𝓕(C;𝓕(B;A))).

    Les QUATRE conjoints (E.III.3.2) : W_Λ fonctionnel, dom W_Λ=𝓕(B×C;A), injective sur
    𝓕(B×C;A), image⊂𝓕(C;𝓕(B;A))."""
    va, vb, vc = _t(a), _t(b), _t(c)
    return conjonction_intro(conjonction_intro(conjonction_intro(
        W_Lambda_fonctionnel(va, vb, vc), W_Lambda_domaine(va, vb, vc)),
        W_Lambda_injective(va, vb, vc)), W_Lambda_image_incluse(va, vb, vc))


def inf_egal_curry(a="A", b="B", c="C"):
    """⊢ inf_egal_card(𝓕(B×C;A), 𝓕(C;𝓕(B;A))).   (= « a^(b·c) ≤ (a^b)^c ».)

    L'injection-témoin est W_Λ (W_Lambda_est_injection) : par S5 (témoin F:=W_Λ),
    (∃F) est_injection_de(F, 𝓕(B×C;A), 𝓕(C;𝓕(B;A))) = inf_egal_card(·,·)."""
    va, vb, vc = _t(a), _t(b), _t(c)
    dom = domaine_lambda(va, vb, vc)
    cod = codomaine_lambda(va, vb, vc)
    Wt = W_Lambda(va, vb, vc)
    inj = W_Lambda_est_injection(va, vb, vc)         # est_injection_de(W_Λ, dom, cod)
    return N.modus_ponens(inj, N.s5(est_injection_de(var("F"), dom, cod), Wt, "F"))


__all__ = [
    "W_Lambda", "W_Lambda_fonctionnel", "W_Lambda_domaine", "W_Lambda_valeur",
    "W_Lambda_image_incluse", "W_Lambda_injective",
    "W_Lambda_est_injection", "inf_egal_curry",
    "lambda_injective_sous_appartenance",
]
