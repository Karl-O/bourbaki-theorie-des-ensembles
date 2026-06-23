"""§II.3.8 — Rétractions / sections : Proposition 8 (dual surjectif),
Théorème 1 (a–f), Corollaire.  (Module NEUF, mission II38-retr-sect.)

Ce module COMPLÈTE `ensembles_retractions.py` (Prop. 8 cas injectif déjà clos :
`retraction_implique_injective`, et sens réciproque surjectif `section_construite_par_tau`).
Il fournit ici :

  • PROPOSITION 8 — sens direct, CAS SURJECTIF (`section_implique_surjective_valeur`)
      ⊢ (s section associée à f) ⇒ (∀y)(y∈B ⇒ (∃x)(y = f(x)))
      INCONDITIONNEL : si f∘s = Id_B, alors tout y∈B admet l'antécédent x = s(y).
      C'est la surjectivité « au niveau des valeurs » (∀y∈B)(∃x) y=f(x), duale de
      `retraction_implique_injective`.

  • THÉORÈME 1 a) — composition d'injections (`theoreme1_a_injective`)
      RÉUTILISE `composee_injective` (assemblage des 7 hyps structurelles) :
      ⊢_{F,F' func, dom F=A, image(F,A)=B, dom F'=B, F inj/A, F' inj/B}
        injective_dans(F'∘F, A).
      ET la composition des rétractions au niveau des valeurs
      (`theoreme1_a_retraction_valeur`) : r∘r' est une rétraction de f''=f'∘f
      (identité matricielle (r∘r')((f'∘f)(x)) = x sur A), conditionnée aux hyps C46.

  • THÉORÈME 1 c) — f'' injective ⇒ f injective (`theoreme1_c_injective`)
      ⊢_{F,F' func, dom F=A, F'∘F injective sur A}  injective_dans(F, A).
      Cœur : f(u)=f(u') ⟹ f'(f(u))=f'(f(u')) ⟹ (f'∘f)(u)=(f'∘f)(u') ⟹ u=u'.

  • THÉORÈME 1 d) — f'' surjective ⇒ f' surjective, au niveau des valeurs
      (`theoreme1_d_surjective_valeur`)
      ⊢ (∀z∈C)(∃x∈A) z=(f'∘f)(x)  ⇒  (∀z∈C)(∃y) z=f'(y)   [y = f(x)].

  • COROLLAIRE — g∘f = Id_A et f∘g = Id_B ⇒ f, g injectives (et donc, avec la
      surjectivité, bijectives) (`corollaire_f_injective`, `corollaire_g_injective`) ;
      l'identification complète g = f⁻¹ est REPORTÉE (pont valeurs↔graphe sur f⁻¹).

Conventions : f : A→B, f' : B→C, f'' = f'∘f ; `E.composee(G, F) = G∘F` (Déf. 6).
Les parties exigeant le pont surjectivité-image (image(f,A)=B) restent conditionnées
aux hypothèses C46 explicites (jamais postulées) ou REPORTÉES (cf. rapport).
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (var, egal, et, appartient, impl, pourtout,
                                       existe, Terme)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (conjonction_intro,
                               conjonction_elim_gauche, conjonction_elim_droite,
                               instancie, equivalence_avant, equivalence_arriere)
from bourbaki.logique.i_4_egalitaires.tactiques_abrege_egalite import (symetrie,
                               composer_egalites, congruence_terme)
from bourbaki.ensembles.fonctions.ii_3_8_retractions_sections.ensembles_composee_valeurs import composition_valeur_t


def _T(v):
    """Coercion nom→terme (accepte un Terme ou un nom de variable)."""
    return v if isinstance(v, Terme) else var(v)


def _eqsym(thm):
    """⊢ (a=b) ⟹ ⊢ (b=a)."""
    a, b = thm.conclusion.termes
    return N.modus_ponens(thm, symetrie(a, b))


def _inst_dom(f, x):
    """⊢ (x ∈ dom F) ⇔ (∃y)((x,y) ∈ F).   (instance de l'axiome du domaine.)"""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_DOM)
    return instancie(instancie(ax, _T(f)), _T(x))


def _membre_implique_dom(f, x, a, u_in_a, hdom):
    """{dom F = A, u∈A} ⊢ (∃y)((u,y) ∈ F).   (u∈A ⟹ u∈dom F ⟹ témoin existe.)"""
    vF, vu, vA = _T(f), _T(x), _T(a)
    u_in_dom = N.modus_ponens(u_in_a, equivalence_arriere(N.modus_ponens(
        hdom, N.s6(E.dom(vF), vA, "w", appartient(vu, var("w"))))))   # u∈dom F
    return N.modus_ponens(u_in_dom, equivalence_avant(_inst_dom(vF, vu)))  # (∃y)(u,y)∈F


# ── PROPOSITION 8 — sens direct, CAS SURJECTIF ────────────────────────────────
def section_implique_surjective_valeur(s="S", f="F", b="B"):
    """⊢ (s section associée à f) ⇒ (∀y)(y∈B ⇒ (∃x)(f(x) = y)).   (Prop. 8 direct, surjectif.)

    Si f∘s = Id_B (c.-à-d. (∀y∈B) f(s(y))=y), tout y∈B est atteint : l'antécédent
    canonique est x := s(y), car f(s(y)) = y.  C'est la SURJECTIVITÉ au niveau des
    valeurs (∀y∈B)(∃x) f(x)=y, duale de `retraction_implique_injective`.
    INCONDITIONNEL (aucune hyp résiduelle).  Le sens « (∃x) y=f(x) » s'en déduit
    par symétrie de l'égalité ; on garde la forme f(x)=y, capture-saine."""
    vS, vF, vB, vy = _T(s), _T(f), _T(b), var("y")
    hsec = N.assume(E.est_section(vS, vF, vB))          # (∀y)(y∈B ⇒ f(s(y))=y)
    inst = instancie(hsec, vy)                          # y∈B ⇒ f(s(y))=y
    hyB = N.assume(appartient(vy, vB))
    fsy_y = N.modus_ponens(hyB, inst)                   # f(s(y)) = y
    sy = E.valeur(vS, vy)                               # s(y) = l'antécédent x
    # (∃x)(f(x) = y)  par S5 (témoin x = s(y)) ; l'instance-témoin est f(s(y))=y
    R = egal(E.valeur(vF, var("x")), vy)               # f(x) = y
    ex = N.modus_ponens(fsy_y, N.s5(R, sy, "x"))        # (∃x)(f(x) = y)
    inner = N.loi_deduction(appartient(vy, vB), ex)     # y∈B ⇒ (∃x)(f(x)=y)
    gen = N.generalisation("y", inner)
    return N.loi_deduction(E.est_section(vS, vF, vB), gen)


def cible_section_implique_surjective_valeur(s="S", f="F", b="B"):
    """Cible exacte de section_implique_surjective_valeur (tests)."""
    vS, vF, vB, vy = _T(s), _T(f), _T(b), var("y")
    R = egal(E.valeur(vF, var("x")), vy)
    return impl(E.est_section(vS, vF, vB),
                pourtout("y", impl(appartient(vy, vB), existe("x", R))))


# ── THÉORÈME 1 c) — f'' = f'∘f injective ⇒ f injective ────────────────────────
def _cv_point(vFp, vF, vA, vB, uu, uu_inA, hdomF, hdomFp, happlique):
    """Sous {dom F=A, dom Fp=B, (∀v∈A)f(v)∈B, F'∘F fonctionnel} et uu∈A :
    renvoie ⊢ (F'∘F)(uu) = F'(F(uu))  (composition_valeur_t avec ses 3 hyps C46
    déchargées des hyps STRUCTURELLES)."""
    comp = E.composee(vFp, vF)
    # (∃y)(uu,y)∈F   [via uu∈A=dom F]
    ex_uF = _membre_implique_dom(vF, uu, vA, uu_inA, hdomF)
    fuu = E.valeur(vF, uu)
    # f(uu)∈B   [happlique : (∀v)(v∈A ⇒ f(v)∈B)]
    fuu_inB = N.modus_ponens(uu_inA, instancie(happlique, uu))
    # (∃y)(f(uu),y)∈Fp   [via f(uu)∈B=dom Fp]
    ex_fuFp = _membre_implique_dom(vFp, fuu, vB, fuu_inB, hdomFp)
    # f'∘f fonctionnel  (hypothèse structurelle déjà assumée hors d'ici)
    hcompfunc = N.assume(E.est_fonctionnel(comp))
    cv = composition_valeur_t(vFp, vF, uu)                       # 3 hyps : compfunc, ex_uF, ex_fuFp
    cv = N.modus_ponens(hcompfunc, N.loi_deduction(E.est_fonctionnel(comp), cv))
    cv = N.modus_ponens(ex_uF, N.loi_deduction(
        existe("y", appartient(E.couple(uu, var("y")), vF)), cv))
    cv = N.modus_ponens(ex_fuFp, N.loi_deduction(
        existe("y", appartient(E.couple(fuu, var("y")), vFp)), cv))
    return cv


def theoreme1_c_injective(f="F", fp="Fp", a="A", b="B"):
    """⊢_{F'∘F func, dom F=A, dom F'=B, (∀v∈A)f(v)∈B, F'∘F inj/A}  injective_dans(F, A).

    THÉORÈME 1 c) : si f'' = f'∘f est injective sur A, f l'est aussi.
    Démonstration de Bourbaki : f(u)=f(u') ⟹ f'(f(u))=f'(f(u')) ⟹
    (f'∘f)(u)=(f'∘f)(u') ⟹ u=u'.

    Hypothèses STRUCTURELLES (jamais postulées, déchargées de la suite) :
    f'∘f fonctionnel, dom F=A, dom F'=B et « f applique A dans B »
    [(∀v)(v∈A ⇒ f(v)∈B)] — ce sont exactement les données « f : A→B, f' : B→C »
    du Théorème 1.  Les conditions C46 ponctuelles de `composition_valeur_t`
    en sont DÉRIVÉES inline (via _cv_point), ce qui permet la généralisation."""
    vF, vFp, vA, vB = _T(f), _T(fp), _T(a), _T(b)
    vu, vup, vv = var("u"), var("up"), var("v")
    comp = E.composee(vFp, vF)                                   # f'' = f'∘f
    hinj = N.assume(E.injective_dans(comp, vA))                  # f'' injective sur A
    hdomF = N.assume(egal(E.dom(vF), vA))                        # dom F = A
    hdomFp = N.assume(egal(E.dom(vFp), vB))                      # dom F' = B
    happlique = N.assume(pourtout("v", impl(appartient(vv, vA),  # (∀v)(v∈A ⇒ f(v)∈B)
                                  appartient(E.valeur(vF, vv), vB))))
    hyp = et(et(appartient(vu, vA), appartient(vup, vA)),
             egal(E.valeur(vF, vu), E.valeur(vF, vup)))          # u,u'∈A et f(u)=f(u')
    h = N.assume(hyp)
    u_inA = conjonction_elim_gauche(conjonction_elim_gauche(h))
    up_inA = conjonction_elim_droite(conjonction_elim_gauche(h))
    fu_eq = conjonction_elim_droite(h)                           # f(u) = f(u')
    fu, fup = E.valeur(vF, vu), E.valeur(vF, vup)
    # f(u)=f(u') ⟹ f'(f(u))=f'(f(u'))   (congruence sous f'(·))
    fpfu_eq = N.modus_ponens(fu_eq, congruence_terme(
        fu, fup, E.valeur(vFp, var("w")), "w"))                 # f'(f(u)) = f'(f(u'))
    # (f'∘f)(u) = f'(f(u))   et   (f'∘f)(u') = f'(f(u'))   (composition au point)
    cv_u = _cv_point(vFp, vF, vA, vB, vu, u_inA, hdomF, hdomFp, happlique)
    cv_up = _cv_point(vFp, vF, vA, vB, vup, up_inA, hdomF, hdomFp, happlique)
    # (f'∘f)(u) = (f'∘f)(u')   par transitivité
    comp_eq = composer_egalites(composer_egalites(cv_u, fpfu_eq), _eqsym(cv_up))
    # u = u'   par injectivité de f'' sur A
    inst = instancie(instancie(hinj, vu), vup)
    u_eq = N.modus_ponens(
        conjonction_intro(conjonction_intro(u_inA, up_inA), comp_eq), inst)
    inner = N.loi_deduction(hyp, u_eq)
    return N.generalisation("u", N.generalisation("up", inner))


def cible_theoreme1_c_injective(f="F", a="A"):
    """Cible : la conclusion est injective_dans(F, A)."""
    return E.injective_dans(_T(f), _T(a))


# ── THÉORÈME 1 a) — composition d'injections (RÉUTILISE composee_injective) ────
def theoreme1_a_injective(fp="Fp", f="F", a="A", b="B"):
    """⊢_{F,F' func, dom F=A, image(F,A)=B, dom F'=B, F inj/A, F' inj/B}
       injective_dans(F'∘F, A).   (Théorème 1 a, partie « f'' injection ».)

    « Si f et f' sont des injections, f'' = f'∘f est une injection. »  C'est
    EXACTEMENT le 3e conjoint de la transitivité de l'équipotence, déjà certifié
    sous le nom `composee_injective` (E.II.46) : on le ré-expose ici comme
    Théorème 1 a (les 7 hyps structurelles sont celles de « f:A→B, f':B→C inj »).
    """
    from bourbaki.cardinaux.ensembles_bijection import composee_injective
    return composee_injective(fp, f, a, b)


def cible_theoreme1_a_injective(fp="Fp", f="F", a="A"):
    """Cible : injective_dans(F'∘F, A)."""
    return E.injective_dans(E.composee(_T(fp), _T(f)), _T(a))


# ── THÉORÈME 1 a) — composition des rétractions (niveau VALEURS, forme matricielle) ─
def theoreme1_a_retraction_valeur(r="R", rp="Rp", f="F", fp="Fp", a="A", b="B"):
    """⊢_{R rétr. de F sur A, R' rétr. de F' sur B, f(x)∈B}
        (x∈A) ⇒ r(r'(f'(f(x)))) = x.   (Théorème 1 a, partie « r∘r' rétraction de f'' ».)

    « Si r, r' sont des rétractions associées à f et f', r∘r' est une rétraction
    associée à f'' = f'∘f. »  Lue MATRICIELLEMENT au niveau des valeurs (encodage
    du projet, Déf. 11), « r∘r' est une rétraction de f'∘f » signifie que, pour tout
    x∈A,  (r∘r')((f'∘f)(x)) = x ; en dépliant les composées au niveau des valeurs
    (g∘h)(t)=g(h(t)), cela s'écrit  r(r'(f'(f(x)))) = x.  C'est exactement la
    démonstration de Bourbaki :
        r(r'(f'(f(x)))) = r(f(x)) = x.

    On livre ici cette FORME DÉPLIÉE (sans la τ-composée-de-composées, qui
    déclenche la capture de liant documentée dans composee_associee_droite_valeur).
    Le passage à la forme repliée (r∘r')((f'∘f)(x)) via composition_valeur_t en un
    point qui est lui-même une valeur τ est REPORTÉ (cf. rapport, verrou τ-capture).

    Hypothèses laissées explicites (jamais postulées) :
      • R rétraction de F sur A     [est_retraction(R,F,A) : (∀x∈A) r(f(x))=x]
      • R' rétraction de F' sur B    [est_retraction(R',F',B) : (∀y∈B) r'(f'(y))=y]
      • f(x)∈B  (pour appliquer la rétraction de f' au point f(x))."""
    vR, vRp, vF, vFp, vA, vB = _T(r), _T(rp), _T(f), _T(fp), _T(a), _T(b)
    vx = var("x")
    fx = E.valeur(vF, vx)                                  # f(x)
    fpfx = E.valeur(vFp, fx)                               # f'(f(x))
    hxA = N.assume(appartient(vx, vA))                     # x∈A
    # (4) r'(f'(f(x))) = f(x)          [R' rétraction de F' sur B, au point f(x)∈B]
    hretRp = N.assume(E.est_retraction(vRp, vFp, vB))     # (∀y∈B) r'(f'(y))=y
    inst_rp = instancie(hretRp, fx)                       # f(x)∈B ⇒ r'(f'(f(x)))=f(x)
    hfxB = N.assume(appartient(fx, vB))
    rp_fpfx = N.modus_ponens(hfxB, inst_rp)              # r'(f'(f(x))) = f(x)
    # (5) r(f(x)) = x                 [R rétraction de F sur A, au point x∈A]
    hretR = N.assume(E.est_retraction(vR, vF, vA))       # (∀x∈A) r(f(x))=x
    inst_r = instancie(hretR, vx)                        # x∈A ⇒ r(f(x))=x
    r_fx = N.modus_ponens(hxA, inst_r)                   # r(f(x)) = x
    #  r(r'(f'(f(x)))) = r(f(x))                          (congruence sous r(·))
    rp_fpfx_term = E.valeur(vRp, fpfx)                    # r'(f'(f(x)))
    r_cong = N.modus_ponens(rp_fpfx, congruence_terme(
        rp_fpfx_term, fx, E.valeur(vR, var("w")), "w"))  # r(r'(f'(f(x)))) = r(f(x))
    #  r(r'(f'(f(x)))) = x                                + (5)
    r_eq_x = composer_egalites(r_cong, r_fx)             # r(r'(f'(f(x)))) = x
    return N.loi_deduction(appartient(vx, vA), r_eq_x)   # (x∈A) ⇒ r(r'(f'(f(x))))=x


def cible_theoreme1_a_retraction_valeur(r="R", rp="Rp", f="F", fp="Fp", a="A"):
    """Cible : (x∈A) ⇒ r(r'(f'(f(x)))) = x."""
    vR, vRp, vF, vFp, vA = _T(r), _T(rp), _T(f), _T(fp), _T(a)
    vx = var("x")
    fx = E.valeur(vF, vx)
    lhs = E.valeur(vR, E.valeur(vRp, E.valeur(vFp, fx)))
    return impl(appartient(vx, vA), egal(lhs, vx))


# ── THÉORÈME 1 d) — f'' = f'∘f surjective ⇒ f' surjective (niveau VALEURS) ─────
def theoreme1_d_surjective_valeur(f="F", fp="Fp", c="C"):
    """⊢ [(∀z)(z∈C ⇒ (∃x)(f'(f(x)) = z))] ⇒ [(∀z)(z∈C ⇒ (∃y)(f'(y) = z))].

    THÉORÈME 1 d) : « Si f'' = f'∘f est une surjection, f' est une surjection. »
    Au niveau des valeurs : si tout z∈C est de la forme f'(f(x)) (surjectivité de
    f'' = f'∘f, lue dépliée f'(f(x))=z), alors tout z∈C est de la forme f'(y) — il
    suffit de prendre y = f(x).  INCONDITIONNEL (aucune hyp résiduelle).
    Bourbaki donne en outre f∘s' comme section associée à f' (REPORTÉ : exige le
    pont surjectivité↔image et la composée-au-point τ)."""
    vF, vFp, vC = _T(f), _T(fp), _T(c)
    vz, vx = var("z"), var("x")
    Rpp = egal(E.valeur(vFp, E.valeur(vF, vx)), vz)        # f'(f(x)) = z
    hyp = pourtout("z", impl(appartient(vz, vC), existe("x", Rpp)))
    hsurj = N.assume(hyp)
    inst = instancie(hsurj, vz)                            # z∈C ⇒ (∃x)(f'(f(x))=z)
    hzC = N.assume(appartient(vz, vC))
    ex_x = N.modus_ponens(hzC, inst)                       # (∃x)(f'(f(x))=z)
    # corps : f'(f(x))=z ⟹ (∃yy)(f'(yy)=z)   (témoin yy = f(x))
    # NB witness variable « yy » ≠ liant interne « y » de valeur(·) (anti-capture).
    fx = E.valeur(vF, vx)
    Rp = egal(E.valeur(vFp, var("yy")), vz)               # f'(yy) = z
    body = N.modus_ponens(N.assume(Rpp), N.s5(Rp, fx, "yy"))  # {f'(f(x))=z} ⊢ (∃yy)(f'(yy)=z)
    step = N.loi_deduction(Rpp, body)                      # f'(f(x))=z ⇒ (∃yy)(f'(yy)=z)
    # éliminer le ∃x  (existe_elimination : (R⇒Q)⇒((∃x R)⇒Q) avec x∉Q)
    from bourbaki.logique.i_3_quantifies.tactiques_abrege_quantif import existe_elimination
    ex_y = N.modus_ponens(ex_x, existe_elimination(step, "x"))   # (∃yy)(f'(yy)=z)
    inner = N.loi_deduction(appartient(vz, vC), ex_y)      # z∈C ⇒ (∃yy)(f'(yy)=z)
    gen = N.generalisation("z", inner)
    return N.loi_deduction(hyp, gen)


def cible_theoreme1_d_surjective_valeur(f="F", fp="Fp", c="C"):
    """Cible : [(∀z∈C)(∃x) f'(f(x))=z] ⇒ [(∀z∈C)(∃yy) f'(yy)=z]."""
    vF, vFp, vC = _T(f), _T(fp), _T(c)
    vz, vx = var("z"), var("x")
    Rpp = egal(E.valeur(vFp, E.valeur(vF, vx)), vz)
    Rp = egal(E.valeur(vFp, var("yy")), vz)
    return impl(pourtout("z", impl(appartient(vz, vC), existe("x", Rpp))),
                pourtout("z", impl(appartient(vz, vC), existe("yy", Rp))))


# ── COROLLAIRE — g∘f = Id_A, f∘g = Id_B ⇒ f, g injectives, g = f⁻¹ ─────────────
def corollaire_f_injective(g="G", f="F", a="A"):
    """⊢ (g∘f = Id_A) ⇒ f injective sur A.   (Corollaire, partie « f injective ».)

    Si g∘f = Id_A (matriciel : (∀x∈A) g(f(x))=x), alors g est une rétraction de f,
    donc f est injective (Prop. 8 direct).  On RÉUTILISE retraction_implique_injective
    (l'hypothèse est_retraction(G,F,A) EST « g∘f=Id_A » au sens du projet)."""
    from bourbaki.ensembles.fonctions.ii_3_8_retractions_sections.ensembles_retractions import retraction_implique_injective
    return retraction_implique_injective(g, f, a)


def corollaire_g_injective(g="G", f="F", b="B"):
    """⊢ (f∘g = Id_B) ⇒ g injective sur B.   (Corollaire, partie « g injective ».)

    Symétriquement : si f∘g = Id_B (matriciel : (∀y∈B) f(g(y))=y), f est une
    rétraction de g, donc g est injective.  On instancie retraction_implique_injective
    avec (rétraction := f, fonction := g) : est_retraction(F,G,B) ⇒ injective_dans(G,B)."""
    from bourbaki.ensembles.fonctions.ii_3_8_retractions_sections.ensembles_retractions import retraction_implique_injective
    return retraction_implique_injective(f, g, b)


# COROLLAIRE g = f⁻¹ : REPORTÉ (non implémenté ici).  L'identification g = reciproque(F)
# (au niveau des valeurs g(f(x))=x ou des graphes) exige le pont valeurs↔graphe sur f⁻¹.
# NB : une fonction « corollaire_g_egal_reciproque » a été RETIRÉE — elle ne donnait que
# la tautologie vide  est_retraction ⇒ est_retraction  (P⇒P), donc INFIDÈLE au corollaire
# de Bourbaki (signalé par audit). Rien ne doit être exposé tant que g=f⁻¹ n'est pas prouvé.


__all__ = ["section_implique_surjective_valeur",
           "cible_section_implique_surjective_valeur",
           "theoreme1_c_injective", "cible_theoreme1_c_injective",
           "theoreme1_a_injective", "cible_theoreme1_a_injective",
           "theoreme1_a_retraction_valeur", "cible_theoreme1_a_retraction_valeur",
           "theoreme1_d_surjective_valeur", "cible_theoreme1_d_surjective_valeur",
           "corollaire_f_injective", "corollaire_g_injective"]
