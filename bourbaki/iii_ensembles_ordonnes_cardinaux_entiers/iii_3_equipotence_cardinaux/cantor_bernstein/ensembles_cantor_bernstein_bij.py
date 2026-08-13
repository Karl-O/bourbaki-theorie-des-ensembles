"""§III.3.2 — CANTOR–BERNSTEIN, ASSEMBLAGE de la bijection (Corollaire 2 du Th. 1).

Énoncé (E.III.3.2, Cor. 2, VERBATIM ROADMAP_chap2-4.md) :
    « Deux ensembles tels que chacun soit équipotent à une partie de l'autre
      sont équipotents. »
    Implémentation §III.3.2 : x ≤ y :⇔ (∃f)(f injection de x dans y), donc
        (a ≤ b  et  b ≤ a)  ⇒  Eq(a, b).

ACQUIS amont (ne rien redéfinir) :
  • R28 ensembles_cantor_bernstein : φ, D, phi_point_fixe ⊢ φ(D)=D.
  • R29 ensembles_cantor_bernstein_fin : pivot_AmoinsD ⊢{g inj} A∖D=g⟨B∖f⟨D⟩⟩,
        partie_disjoint_complement, partie_reunion_complement, restriction_-
        fonctionnelle, sous_graphe_fonctionnel.
  • R25 ensembles_restriction_somme + ensembles_recollement_bijection :
        reunion_graphes_fonctionnelle, valeur_reunion_*, image_reunion_graphes,
        reunion_graphes_injective.

PLAN (la bijection h = (f|D) ∪ (g⁻¹|(A∖D))) :
  (i)   f|D : restriction(f,D) — fonctionnelle, dom=D (sous D⊂dom F), image=f⟨D⟩,
        injective sur D.
  (ii)  gI : restriction(g⁻¹, A∖D) — g⁻¹ fonctionnel (g inj), dom=A∖D (pivot),
        image=B∖f⟨D⟩, injective.
  (iii) h = f|D ∪ gI ; D et A∖D disjoints (partie_disjoint_complement) ⇒ h fonct.
        + dom h = D∪(A∖D) = a (partie_reunion_complement).
  (iv)  injective_dans(h,a) via reunion_graphes_injective (f⟨D⟩, B∖f⟨D⟩ disjointes).
  (v)   image(h,a) = f⟨D⟩∪(B∖f⟨D⟩) = b (image_reunion_graphes + recouvrement).
  (vi)  est_bijection_de(h,a,b) → témoin → Eq(a,b) → décharge ∃ → cantor_bernstein.

BRIQUES GÉNÉRALES sur la restriction certifiées ici (réutilisables) :
  • restriction_image_egale_image  ⊢ image(f|X, X) = image(f, X)         [clos]
  • restriction_dom_sous_inclusion ⊢ (X ⊂ dom F) ⇒ (dom(f|X) = X)        [clos]
  • restriction_valeur             {F fonct, u∈X, u∈dom F} ⊢ (f|X)(u)=F(u)
  • restriction_injective    {F fonct, inj/X, X⊂dom F} ⊢ injective_dans(f|X, X)

MORCEAU 1 ENTIÈREMENT ASSEMBLÉ (certifié clos) :
  • morceau_fD  ⊢ est_injection_de(f,a,b) ⇒ est_bijection_de(f|D, D, f⟨D⟩).

REPORTÉ honnêtement (le 2ᵉ morceau et la conclusion — voir rapport de mission) :
  • morceau_gI : g⁻¹|(A∖D) bijection (A∖D) → (B∖f⟨D⟩).  Les conjoints func/dom/inj
    sont à portée (reciproque_fonctionnelle/domaine/injective + restriction_* +
    pivot A∖D⊂dom g⁻¹=image(g,b)).  Le SEUL verrou est l'IMAGE :
    image(g⁻¹, A∖D) = B∖f⟨D⟩, qui exige le lemme « g⁻¹⟨g⟨S⟩⟩ = S pour S⊂b, g inj »
    (rétraction g⁻¹∘g = id sur b), preuve A1 multi-équivalence non encore disponible.
  • cantor_bernstein : recollement h=morceau_fD∪morceau_gI (reunion_graphes_-
    fonctionnelle/injective + image_reunion_graphes des deux morceaux ; D∩(A∖D)=∅,
    f⟨D⟩∩(B∖f⟨D⟩)=∅, D∪(A∖D)=a, f⟨D⟩∪(B∖f⟨D⟩)=b) puis témoin → Eq(a,b) → décharge ∃.
    Tout l'outillage de recollement (TEMPS 1) est prêt ; reste morceau_gI.

Tout sort du noyau (PROUVE == certifie) ; AUCUN axiome nouveau.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (Terme, var, egal, et, ou, non, impl,
                                       appartient, existe, pourtout, inclus)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege import syllogisme
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    projection_gauche, projection_droite,
    equivalence_avant, equivalence_arriere, equivalence_transitivite,
    instancie, instanciation_en_x)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import symetrie, composer_egalites
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import (
    existe_elimination, congruence_existe, alpha_existe, et_existe_droite)
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_5_restrictions_prolongements.ensembles_restrictions import couple_restriction
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_4_fonctions.ensembles_fonctions import (
    valeur_caracterisation, valeur_dans_graphe)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_theoremes import egalite_par_extension


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def _inst_dom(f, x):
    """⊢ (x ∈ dom F) ⇔ (∃y)((x,y) ∈ F)."""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_DOM)
    return instancie(instancie(ax, f), x)


def _inst_image(g, xset, y):
    """⊢ (y ∈ G⟨X⟩) ⇔ (∃x)(x∈X et (x,y)∈G)."""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_IMAGE)
    return instancie(instancie(instancie(ax, g), xset), y)


def _couple_restriction(f, x, u, v):
    """⊢ ((u,v) ∈ f|X) ⇔ (u∈X et (u,v)∈F)  pour des TERMES f,x,u,v quelconques.

    (couple_restriction n'accepte que des NOMS — version à lettres généralisée
    puis instanciée aux termes, robuste aux valeurs composées f(u).)"""
    th = couple_restriction("F", "X", "u", "v")    # à lettres F,X,u,v
    for nm, tm in (("F", _t(f)), ("X", _t(x)), ("u", _t(u)), ("v", _t(v))):
        th = instancie(N.generalisation(nm, th), tm)
    return th


# ── (i.image) image(f|X, X) = image(f, X) ─────────────────────────────────────
def restriction_image_egale_image(f="F", x="X"):
    """⊢ image(f|X, X) = image(f, X).   (restreindre puis imager sur X = imager sur X.)

    v∈(f|X)⟨X⟩ ⇔ (∃u)(u∈X et (u,v)∈f|X) ⇔ (∃u)(u∈X et (u∈X et (u,v)∈F))
              ⇔ (∃u)(u∈X et (u,v)∈F) ⇔ v∈f⟨X⟩.  (inconditionnel.)"""
    vF, vX = _t(f), _t(x)
    vv, vu = var("z"), var("u")     # élément « z » (liant inclus/A1), antécédent « u »
    fX = E.restriction(vF, vX)
    uX = appartient(vu, vX)
    uvF = appartient(E.couple(vu, vv), vF)
    uvfX = appartient(E.couple(vu, vv), fX)

    carImgFX = _inst_image(fX, vX, vv)          # v∈(f|X)⟨X⟩ ⇔ (∃u)(u∈X et (u,v)∈f|X)  [binder u]
    carImgF = _inst_image(vF, vX, vv)           # v∈f⟨X⟩ ⇔ (∃u)(u∈X et (u,v)∈F)         [binder u]
    # AXIOME_IMAGE binder is « x » : renommer en « u » dans les deux
    renFX = alpha_existe("x", "u", et(appartient(var("x"), vX),
                                      appartient(E.couple(var("x"), vv), fX)))
    renF = alpha_existe("x", "u", et(appartient(var("x"), vX),
                                     appartient(E.couple(var("x"), vv), vF)))
    carImgFX = equivalence_transitivite(carImgFX, renFX)   # ⇔ (∃u)(u∈X et (u,v)∈f|X)
    carImgF = equivalence_transitivite(carImgF, renF)      # ⇔ (∃u)(u∈X et (u,v)∈F)

    cr = _couple_restriction(vF, vX, vu, vv)     # (u,v)∈f|X ⇔ (u∈X et (u,v)∈F)
    # corps : (u∈X et (u,v)∈f|X) ⇔ (u∈X et (u,v)∈F)
    #   ⇒ : extraire (u,v)∈F via cr ; ⇐ : reconstruire (u,v)∈f|X via cr.
    hb = N.assume(et(uX, uvfX))
    fwd_body = N.loi_deduction(et(uX, uvfX), conjonction_intro(
        conjonction_elim_gauche(hb),
        conjonction_elim_droite(N.modus_ponens(conjonction_elim_droite(hb),
                                               equivalence_avant(cr)))))   # ⇒ (u∈X et (u,v)∈F)
    hc = N.assume(et(uX, uvF))
    bwd_body = N.loi_deduction(et(uX, uvF), conjonction_intro(
        conjonction_elim_gauche(hc),
        N.modus_ponens(conjonction_intro(conjonction_elim_gauche(hc),
                                         conjonction_elim_droite(hc)),
                       equivalence_arriere(cr))))           # ⇐ (u∈X et (u,v)∈f|X)
    body_eq = conjonction_intro(fwd_body, bwd_body)         # (u∈X et (u,v)∈f|X) ⇔ (u∈X et (u,v)∈F)
    ex_eq = congruence_existe(body_eq, "u")                 # (∃u)… ⇔ (∃u)…

    chain = equivalence_transitivite(carImgFX,
                equivalence_transitivite(ex_eq, equivalence_symetrie_local(carImgF)))
    #   v∈(f|X)⟨X⟩ ⇔ v∈f⟨X⟩
    char_LR = N.generalisation("z", equivalence_avant(chain))   # (f|X)⟨X⟩ ⊂ f⟨X⟩
    char_RL = N.generalisation("z", equivalence_arriere(chain)) # f⟨X⟩ ⊂ (f|X)⟨X⟩
    ext = instancie(instancie(N.axiome(E.theorie_ensembles(), E.A1),
                              E.image(fX, vX)), E.image(vF, vX))
    return N.modus_ponens(conjonction_intro(char_LR, char_RL), ext)


# ── (i.dom) dom(f|X) = X  sous X ⊂ dom F ──────────────────────────────────────
def restriction_dom_sous_inclusion(f="F", x="X"):
    """⊢ (X ⊂ dom F) ⇒ (dom(f|X) = X).

    u∈dom(f|X) ⇔ (∃v)((u,v)∈f|X) ⇔ (∃v)(u∈X et (u,v)∈F) ⇔ (u∈X et (∃v)(u,v)∈F)
              ⇔ (u∈X et u∈dom F).  Sous X⊂dom F : ⇔ u∈X."""
    vF, vX = _t(f), _t(x)
    vu, vv = var("z"), var("v")     # élément « z » (liant inclus/A1)
    fX = E.restriction(vF, vX)
    uX = appartient(vu, vX)
    uvF = appartient(E.couple(vu, vv), vF)
    uvfX = appartient(E.couple(vu, vv), fX)

    hsub = N.assume(inclus(vX, E.dom(vF)))                  # X ⊂ dom F
    uX_uDom = N.modus_ponens(hsub, instanciation_en_x(impl(uX, appartient(vu, E.dom(vF))), "z"))

    carDomFX = _inst_dom(fX, vu)                            # u∈dom(f|X) ⇔ (∃v)((u,v)∈f|X)  [binder y]
    carDomF = _inst_dom(vF, vu)                             # u∈dom F ⇔ (∃v)((u,v)∈F)        [binder y]
    renFX = alpha_existe("y", "v", appartient(E.couple(vu, var("y")), fX))
    renF = alpha_existe("y", "v", appartient(E.couple(vu, var("y")), vF))
    carDomFX = equivalence_transitivite(carDomFX, renFX)    # ⇔ (∃v)((u,v)∈f|X)
    carDomF = equivalence_transitivite(carDomF, renF)       # ⇔ (∃v)((u,v)∈F)

    cr = _couple_restriction(vF, vX, vu, vv)                 # (u,v)∈f|X ⇔ (u∈X et (u,v)∈F)
    ex_cr = congruence_existe(cr, "v")                      # (∃v)(u,v)∈f|X ⇔ (∃v)(u∈X et (u,v)∈F)
    # (∃v)(u∈X et (u,v)∈F) ⇔ (u∈X et (∃v)(u,v)∈F)   (et_existe_droite, u∈X sans v)
    distrib = et_existe_droite(uX, "v", uvF)               # (u∈X et (∃v)(u,v)∈F) ⇔ (∃v)(u∈X et (u,v)∈F)
    # chaîner : u∈dom(f|X) ⇔ (∃v)(u,v)∈f|X ⇔ (∃v)(u∈X et (u,v)∈F) ⇔ (u∈X et (∃v)(u,v)∈F)
    chain = equivalence_transitivite(carDomFX,
                equivalence_transitivite(ex_cr, equivalence_symetrie_local(distrib)))
    #   chain : u∈dom(f|X) ⇔ (u∈X et (∃v)(u,v)∈F)
    # (∃v)(u,v)∈F = u∈dom F (carDomF, sens arrière) ; sous X⊂dom F le 2e conj est impliqué
    # ⇒ : u∈dom(f|X) ⇒ u∈X  (projection gauche)
    fwd = syllogisme(equivalence_avant(chain), projection_gauche(uX,
                       existe("v", uvF)))                   # u∈dom(f|X) ⇒ u∈X
    # ⇐ : u∈X ⇒ u∈dom(f|X)  : u∈X et u∈dom F (=(∃v)(u,v)∈F) → corps → chain arrière
    hX = N.assume(uX)
    uDom = N.modus_ponens(hX, uX_uDom)                      # u∈dom F
    exv = N.modus_ponens(uDom, equivalence_avant(carDomF))  # (∃v)(u,v)∈F
    corps = conjonction_intro(hX, exv)                      # u∈X et (∃v)(u,v)∈F
    uInFX = N.modus_ponens(corps, equivalence_arriere(chain))   # u∈dom(f|X)
    bwd = N.loi_deduction(uX, uInFX)                        # u∈X ⇒ u∈dom(f|X)

    char_LR = N.generalisation("z", fwd)                    # dom(f|X) ⊂ X
    char_RL = N.generalisation("z", bwd)                    # X ⊂ dom(f|X)
    ext = instancie(instancie(N.axiome(E.theorie_ensembles(), E.A1),
                              E.dom(fX)), vX)
    eqset = N.modus_ponens(conjonction_intro(char_LR, char_RL), ext)   # dom(f|X)=X
    return N.loi_deduction(inclus(vX, E.dom(vF)), eqset)


def equivalence_symetrie_local(thm_eq):
    """⊢ (A⇔B) ⟹ ⊢ (B⇔A)  (symétrie de ⇔, local)."""
    return conjonction_intro(equivalence_arriere(thm_eq), equivalence_avant(thm_eq))


# ── (i.valeur) (f|X)(u) = F(u)  pour u∈X∩dom F ────────────────────────────────
def restriction_valeur(f="F", x="X", u="u"):
    """{F fonctionnel, u∈X, u∈dom F} ⊢ (f|X)(u) = F(u).

    (u,F(u))∈F (valeur_dans_graphe) et u∈X ⇒ (u,F(u))∈f|X (couple_restriction) ;
    f|X est fonctionnel (sous_graphe ⊂ F) donc par unicité (f|X)(u)=F(u)."""
    vF, vX, vu = _t(f), _t(x), _t(u)
    fX = E.restriction(vF, vX)
    Fu = E.valeur(vF, vu)
    huX = N.assume(appartient(vu, vX))                      # u∈X
    huDom = N.assume(appartient(vu, E.dom(vF)))             # u∈dom F

    # (u, F(u)) ∈ F
    exF = N.modus_ponens(huDom, equivalence_avant(_inst_dom(vF, vu)))   # (∃y)(u,y)∈F
    u_Fu_F = N.modus_ponens(exF, N.loi_deduction(
        existe("y", appartient(E.couple(vu, var("y")), vF)),
        valeur_dans_graphe(vF, vu)))                        # (u,F(u))∈F
    # (u, F(u)) ∈ f|X  via couple_restriction
    cr = _couple_restriction(vF, vX, vu, Fu)                 # (u,F(u))∈f|X ⇔ (u∈X et (u,F(u))∈F)
    u_Fu_fX = N.modus_ponens(conjonction_intro(huX, u_Fu_F), equivalence_arriere(cr))
    # f|X fonctionnel (sous F fonctionnel)
    funcFX = N.modus_ponens(N.assume(E.est_fonctionnel(vF)),
                            _restriction_fonctionnelle_terme(vF, vX))  # {F fonct} ⊢ func(f|X)
    # (∃y)((u,y)∈f|X)
    exFX = N.modus_ponens(u_Fu_fX, N.s5(appartient(E.couple(vu, var("y")), fX), Fu, "y"))
    # valeur_caracterisation(f|X, u) instanciée à y:=F(u)
    vc = valeur_caracterisation(fX, vu)                     # hyps : func(f|X), (∃y)((u,y)∈f|X)
    vc_Fu = instancie(N.generalisation("y", vc), Fu)        # ((u,F(u))∈f|X) ⇔ (F(u)=(f|X)(u))
    Fu_eq = N.modus_ponens(u_Fu_fX, equivalence_avant(vc_Fu))   # F(u)=(f|X)(u)
    res = N.modus_ponens(Fu_eq, symetrie(Fu, E.valeur(fX, vu)))  # (f|X)(u)=F(u)
    # décharge des hyps func(f|X) et (∃y)((u,y)∈f|X) (toutes deux prouvées)
    res = N.modus_ponens(funcFX, N.loi_deduction(E.est_fonctionnel(fX), res))
    res = N.modus_ponens(exFX, N.loi_deduction(
        existe("y", appartient(E.couple(vu, var("y")), fX)), res))
    return res


# ── (i.inj) injective_dans(f|X, X)  sous F injective sur X (et X⊂dom F) ────────
def restriction_injective(f="F", x="X"):
    """{F fonctionnel, injective_dans(F,X), X⊂dom F} ⊢ injective_dans(f|X, X).

    Pour u,u'∈X : (f|X)(u)=F(u), (f|X)(u')=F(u') (restriction_valeur, sous u,u'∈dom F
    fournis par X⊂dom F) ; donc (f|X)(u)=(f|X)(u') ⇒ F(u)=F(u') ⇒ u=u' (F inj/X)."""
    vF, vX = _t(f), _t(x)
    vu, vup = var("u"), var("up")
    fX = E.restriction(vF, vX)
    hfunc = N.assume(E.est_fonctionnel(vF))
    hinj = N.assume(E.injective_dans(vF, vX))
    hsub = N.assume(inclus(vX, E.dom(vF)))

    hyp = et(et(appartient(vu, vX), appartient(vup, vX)),
             egal(E.valeur(fX, vu), E.valeur(fX, vup)))
    h = N.assume(hyp)
    uX = conjonction_elim_gauche(conjonction_elim_gauche(h))
    upX = conjonction_elim_droite(conjonction_elim_gauche(h))
    val_eq = conjonction_elim_droite(h)                    # (f|X)(u)=(f|X)(u')

    def fX_eq_F(t, tX):
        """sous t∈X : ⊢ (f|X)(t)=F(t)  [hyps F fonct, X⊂dom F restent]."""
        rv = restriction_valeur(vF, vX, t)                # {F fonct, t∈X, t∈dom F} ⊢ (f|X)(t)=F(t)
        rv = N.modus_ponens(tX, N.loi_deduction(appartient(t, vX), rv))  # décharge t∈X
        tDom = N.modus_ponens(tX, instancie(hsub, t))     # t∈dom F (via X⊂dom F)
        rv = N.modus_ponens(tDom, N.loi_deduction(appartient(t, E.dom(vF)), rv))  # décharge t∈dom F
        return rv

    fXu_Fu = fX_eq_F(vu, uX)                               # (f|X)(u)=F(u)
    fXup_Fup = fX_eq_F(vup, upX)                           # (f|X)(u')=F(u')
    # F(u) = (f|X)(u) = (f|X)(u') = F(u')
    Fu_Fup = composer_egalites(composer_egalites(
        N.modus_ponens(fXu_Fu, symetrie(E.valeur(fX, vu), E.valeur(vF, vu))),  # F(u)=(f|X)(u)
        val_eq), fXup_Fup)                                # = F(u')
    inj = instancie(instancie(hinj, vu), vup)             # (u∈X et u'∈X et F(u)=F(u'))⇒u=u'
    u_eq = N.modus_ponens(conjonction_intro(conjonction_intro(uX, upX), Fu_Fup), inj)
    inner = N.loi_deduction(hyp, u_eq)
    return N.generalisation("u", N.generalisation("up", inner))


# ── MORCEAU 1 : f|D est une bijection de D sur f⟨D⟩ ───────────────────────────
# @livre Ch.III §3.2 Cor.2 | E III.25 L.13-15 | PDF p.128
#   (Cantor–Bernstein, démonstration machine : morceau f|D de la bijection
#    h = (f|D) ∪ (g⁻¹|(A∖D)) ; l'énoncé du livre est aux lignes citées.)
def morceau_fD(a="A", b="B", f="f", g="g"):
    """{est_injection_de(f,a,b)} ⊢ est_bijection_de(f|D, D, f⟨D⟩).

    f|D = restriction(f, D) où D = CB.D(a,b,f,g) (point fixe de Knaster–Tarski).
    De est_injection_de(f,a,b) = (f fonct ∧ dom f=a ∧ inj/a ∧ image(f,a)⊂b) on tire :
      • f|D fonctionnel        (restriction_fonctionnelle, sous f fonct) ;
      • dom(f|D)=D             (restriction_dom_sous_inclusion, sous D⊂dom f=a) ;
      • injective_dans(f|D, D) (restriction_injective : f inj sur D — restriction de
        l'injectivité gardée — et D⊂dom f) ;
      • image(f|D, D)=f⟨D⟩     (restriction_image_egale_image, inconditionnel).
    """
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.cantor_bernstein import ensembles_cantor_bernstein as CB
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import est_injection_de, est_bijection_de
    vA, vB, vf, vg = _t(a), _t(b), _t(f), _t(g)
    dterm = CB.D(vA, vB, vf, vg)
    fD = E.restriction(vf, dterm)

    hinj = N.assume(est_injection_de(vf, vA, vB))           # f injection a→b
    f_func = conjonction_elim_gauche(conjonction_elim_gauche(conjonction_elim_gauche(hinj)))  # f fonct
    f_dom = conjonction_elim_droite(conjonction_elim_gauche(conjonction_elim_gauche(hinj)))   # dom f=a
    f_injX = conjonction_elim_droite(conjonction_elim_gauche(hinj))   # injective_dans(f,a)

    # D ⊂ dom f : D⊂a (D_inclus_A, clos) puis réécrire a → dom f (a=dom f par sym de dom f=a)
    D_inA = CB.D_inclus_A(a, b, f, g)                       # ⊢ D⊂A
    a_eq_domf = N.modus_ponens(f_dom, symetrie(E.dom(vf), vA))   # a=dom f
    D_inDomf = N.modus_ponens(D_inA, equivalence_avant(N.modus_ponens(a_eq_domf,
        N.s6(vA, E.dom(vf), "w", inclus(dterm, var("w"))))))    # D⊂dom f   [hyp inj via f_dom]

    # injective_dans(f, D) : restriction de l'injectivité gardée a→D (D⊂a)
    fD_inj_on_D = _injective_dans_restreint(vf, vA, dterm, D_inA)   # {inj/a} ⊢ injective_dans(f,D)
    fD_inj_on_D = N.modus_ponens(f_injX, N.loi_deduction(           # décharge inj/a
        E.injective_dans(vf, vA), fD_inj_on_D))                     # {inj(f,a)→}⊢ injective_dans(f,D)

    # 1) f|D fonctionnel
    c_func = N.modus_ponens(f_func, _restriction_fonctionnelle_terme(vf, dterm))
    # 2) dom(f|D)=D
    c_dom = N.modus_ponens(D_inDomf, restriction_dom_sous_inclusion(vf, dterm))
    # 3) injective_dans(f|D, D)
    ri = restriction_injective(vf, dterm)                  # {f fonct, inj/D, D⊂dom f} ⊢ inj(f|D,D)
    c_inj = N.modus_ponens(f_func, N.loi_deduction(E.est_fonctionnel(vf),
            N.modus_ponens(fD_inj_on_D, N.loi_deduction(E.injective_dans(vf, dterm),
            N.modus_ponens(D_inDomf, N.loi_deduction(inclus(dterm, E.dom(vf)), ri))))))
    # 4) image(f|D, D)=f⟨D⟩
    c_img = restriction_image_egale_image(vf, dterm)       # clos
    # est_bijection_de(f|D, D, f⟨D⟩) = ((func ∧ dom=D) ∧ (inj/D ∧ image=f⟨D⟩))
    bij = conjonction_intro(conjonction_intro(c_func, c_dom),
                            conjonction_intro(c_inj, c_img))
    return N.loi_deduction(est_injection_de(vf, vA, vB), bij)


def _restriction_incluse_terme(f, x):
    """⊢ f|X ⊂ F  pour des TERMES f, x quelconques."""
    from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_5_restrictions_prolongements.ensembles_restrictions import restriction_incluse
    th = restriction_incluse("F", "X")            # clos : ⊢ f|X⊂F
    th = instancie(N.generalisation("F", th), _t(f))
    th = instancie(N.generalisation("X", th), _t(x))
    return th


def _restriction_fonctionnelle_terme(f, x):
    """⊢ est_fonctionnel(F) ⇒ est_fonctionnel(f|X)  pour des TERMES f, x.

    f|X ⊂ F (restriction_incluse) + sous_graphe_fonctionnel."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.cantor_bernstein.ensembles_cantor_bernstein_fin import sous_graphe_fonctionnel
    vF, vX = _t(f), _t(x)
    fX = E.restriction(vF, vX)
    sgf = sous_graphe_fonctionnel(vF, fX)         # (func F et f|X⊂F) ⇒ func f|X
    inc = _restriction_incluse_terme(vF, vX)      # f|X ⊂ F
    hfunc = N.assume(E.est_fonctionnel(vF))
    conc = N.modus_ponens(conjonction_intro(hfunc, inc), sgf)
    return N.loi_deduction(E.est_fonctionnel(vF), conc)


def _injective_dans_restreint(f, a, d, D_in_a):
    """{injective_dans(F, A)} et ⊢(D⊂A) ⟹ {injective_dans(F,A)} ⊢ injective_dans(F, D).

    L'injectivité gardée sur A descend à toute partie D⊂A (la garde u,u'∈D⊂A est
    plus forte que u,u'∈A).  D_in_a est une PREUVE de D⊂A (ici close, D_inclus_A)."""
    vF, vA, vD = _t(f), _t(a), _t(d)
    vu, vup = var("u"), var("up")
    hinj = N.assume(E.injective_dans(vF, vA))
    hyp = et(et(appartient(vu, vD), appartient(vup, vD)),
             egal(E.valeur(vF, vu), E.valeur(vF, vup)))
    h = N.assume(hyp)
    uD = conjonction_elim_gauche(conjonction_elim_gauche(h))
    upD = conjonction_elim_droite(conjonction_elim_gauche(h))
    val = conjonction_elim_droite(h)
    uA = N.modus_ponens(uD, instancie(D_in_a, vu))         # u∈A
    upA = N.modus_ponens(upD, instancie(D_in_a, vup))      # u'∈A
    inj = instancie(instancie(hinj, vu), vup)
    u_eq = N.modus_ponens(conjonction_intro(conjonction_intro(uA, upA), val), inj)
    inner = N.loi_deduction(hyp, u_eq)
    return N.generalisation("u", N.generalisation("up", inner))


__all__ = ["restriction_image_egale_image", "restriction_dom_sous_inclusion",
           "restriction_valeur", "restriction_injective", "morceau_fD"]
