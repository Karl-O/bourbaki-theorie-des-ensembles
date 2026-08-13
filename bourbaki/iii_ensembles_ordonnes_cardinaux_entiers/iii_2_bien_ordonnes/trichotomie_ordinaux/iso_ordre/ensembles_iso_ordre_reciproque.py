"""§III.1.3 / §III.2 — L'isomorphisme RÉCIPROQUE d'un isomorphisme d'ensembles
ordonnés est un isomorphisme (KEYSTONE de la trichotomie, Th3 §III.2).

ÉNONCÉ (Bourbaki E.III.1.3, immédiat : « la bijection réciproque d'un isomorphisme
de (E,≤) sur (E',≤') est un isomorphisme de (E',≤') sur (E,≤) ») :

    { est_isomorphisme_ordre(φ, S, T, R, R'),  est_fonctionnel(φ),  dom φ = S }
        ⊢  est_isomorphisme_ordre(φ⁻¹, T, S, R', R).

POURQUOI les deux dernières hypothèses sont EXPLICITES (et non gratuites) : la
définition `est_isomorphisme_ordre` ne porte que `est_bijective` (2 conjoints :
injective_dans + surjective image=T) — elle NE contient PAS `est_fonctionnel(φ)`
ni `dom φ = S`.  Or `reciproque_est_bijection` (Prop. 7, E.II.3.7) opère sur
`est_bijection_de` (4 conjoints : func ∧ dom=S ∧ inj ∧ img=T).  C'est le DÉCALAGE
2-vs-4 : on le franchit en prenant func et dom=S en hypothèses (vraies pour tout
iso d'ordre représenté par un graphe d'application — les seuls isos du projet),
ce qui permet de reconstituer `est_bijection_de(φ,S,T)` et d'appliquer Prop. 7.
Le CŒUR substantiel est le conjoint (b), compatible_ordre de φ⁻¹.

PREUVE.
  (a) BIJECTION : est_bijective(φ,S,T) est extrait de l'iso (projection gauche) ;
      assemblé avec func + dom=S il donne est_bijection_de(φ,S,T) ; Prop. 7 le
      transporte en est_bijection_de(φ⁻¹,T,S), dont on ré-extrait est_bijective.

  (b) COMPATIBLE_ORDRE(φ⁻¹, T, R', R) — pour x,w ∈ T (BINDERS x, w, JAMAIS y, qui
      capturerait le τ_y de valeur(φ⁻¹, var y)) :
          R'{x,w}  ⇔  R{φ⁻¹(x), φ⁻¹(w)}.
      On transporte par compatible_ordre(φ,S,R,R') INSTANCIÉE en (φ⁻¹(x),φ⁻¹(w)) :
          R{φ⁻¹(x),φ⁻¹(w)}  ⇔  R'{φ(φ⁻¹(x)), φ(φ⁻¹(w))}
      (déchargée car φ⁻¹(x),φ⁻¹(w) ∈ S = img(φ⁻¹,T)), puis on réécrit
      φ(φ⁻¹(x))=x et φ(φ⁻¹(w))=w (« section » : φ∘φ⁻¹=Id_T), d'où
          R{φ⁻¹(x),φ⁻¹(w)}  ⇔  R'{x,w} ;  on symétrise.

      SECTION φ(φ⁻¹(x))=x pour x∈T : φ⁻¹ fonctionnel et dom φ⁻¹=T ⇒ (x,φ⁻¹(x))∈φ⁻¹
      (valeur_dans_graphe), donc (φ⁻¹(x),x)∈φ (couple_reciproque), et comme φ est
      fonctionnel avec φ⁻¹(x) dans son domaine, valeur_caracterisation donne
      x = φ(φ⁻¹(x)).
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (var, egal, et, equiv, impl, appartient, existe, Terme)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, equivalence_symetrie,
    equivalence_transitivite, instancie)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_vocab import (
    est_isomorphisme_ordre, compatible_ordre,
    isomorphisme_ordre_est_bijection, isomorphisme_ordre_compatible)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import est_bijection_de
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.equipotence.ensembles_bijection import reciproque_est_bijection
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_2_reciproque.ensembles_reciproque import couple_reciproque
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_4_fonctions.ensembles_fonctions import valeur_dans_graphe
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_1_relations_ordre.isomorphismes_ordre.ensembles_valeur_bridge import valeur_j_egal_y, valeur_y_egal_j


def _T(v):
    """Coercion nom→terme (accepte un Terme ou un nom de variable)."""
    return v if isinstance(v, Terme) else var(v)


def _rw(thm, eq_thm, contexte, hole="hj0"):
    """Réécrit `a`→`b` dans la formule de `thm` via Leibniz S6, où eq_thm ⊢ a=b et
    `contexte(trou)` reconstruit la formule de thm avec `a` remplacé par le trou.
    Retourne ⊢ thm.conclusion[a:=b].  (Pont liant-valeur τ_j↔τ_y aux frontières.)"""
    a, b = eq_thm.conclusion.termes                       # a = b
    eqv = N.modus_ponens(eq_thm, N.s6(a, b, hole, contexte(var(hole))))   # F[a] ⇔ F[b]
    return N.modus_ponens(thm, equivalence_avant(eqv))    # F[b]


def _R_defaut(nom):
    """Relation relationnelle générique R{a,b} := (a,b) ∈ G_nom (graphe arbitraire)."""
    vG = var(nom)
    return lambda a, b: appartient(E.couple(a, b), vG)


# ════════════════════════════════════════════════════════════════════════════
#  SECTION : φ(φ⁻¹(x)) = x pour x ∈ T  (φ∘φ⁻¹ = Id_T)
# ════════════════════════════════════════════════════════════════════════════
def _couple_inverse(vphi, vT, vx):
    """{ dom(φ⁻¹) = T,  x ∈ T }  ⊢  (φ⁻¹(x), x) ∈ φ.   (φ⁻¹(x) := valeur(φ⁻¹, x).)

    x∈T=dom φ⁻¹ ⇒ (∃y)((x,y)∈φ⁻¹) ⇒ (x,φ⁻¹(x))∈φ⁻¹ (valeur_dans_graphe), donc
    (φ⁻¹(x),x)∈φ par couple_reciproque.  Cœur géométrique partagé section/membre."""
    Phinv = E.reciproque(vphi)
    finv_x = E.valeur(Phinv, vx)                       # φ⁻¹(x)
    # x ∈ dom φ⁻¹  (depuis x∈T et dom φ⁻¹ = T)
    hxT = N.assume(appartient(vx, vT))
    hdom = N.assume(egal(E.dom(Phinv), vT))
    x_in_domrec = N.modus_ponens(hxT, equivalence_arriere(N.modus_ponens(
        hdom, N.s6(E.dom(Phinv), vT, "w0", appartient(vx, var("w0"))))))  # x∈dom φ⁻¹
    # (∃y)((x,y)∈φ⁻¹)  (déplie x∈dom φ⁻¹ via AXIOME_DOM)
    ax_dom = instancie(instancie(N.axiome(E.theorie_ensembles(), E.AXIOME_DOM),
                                 Phinv), vx)            # x∈dom φ⁻¹ ⇔ (∃y)((x,y)∈φ⁻¹)
    ex_xy = N.modus_ponens(x_in_domrec, equivalence_avant(ax_dom))      # (∃y)((x,y)∈φ⁻¹)
    # (x, φ⁻¹(x)) ∈ φ⁻¹
    x_finv = N.modus_ponens(ex_xy, N.loi_deduction(
        existe("y", appartient(E.couple(vx, var("y")), Phinv)),
        valeur_dans_graphe(Phinv, vx)))                # (x,φ⁻¹(x))∈φ⁻¹
    # (φ⁻¹(x), x) ∈ φ   via couple_reciproque GÉNÉRIQUE puis spécialisation.
    #   On évite couple_reciproque(φ, x, φ⁻¹(x)) DIRECT : ses trous internes p,q,w
    #   capturent quand la coordonnée vx vaut « w ».  On prouve d'abord la forme
    #   générique sur coordonnées fraîches cu,cv (≠ p,q,w,x,y), on la généralise,
    #   puis on l'instancie en (cu:=x, cv:=φ⁻¹(x)) — pure substitution sans trou.
    cr_gen = couple_reciproque(vphi, "cu", "cv")       # ((cu,cv)∈φ⁻¹) ⇔ ((cv,cu)∈φ)
    #   généralise cv (intérieur) puis cu (extérieur) → instancie cu:=x, cv:=φ⁻¹(x)
    cr = instancie(instancie(
        N.generalisation("cu", N.generalisation("cv", cr_gen)), vx), finv_x)
    #   ((x,φ⁻¹(x))∈φ⁻¹) ⇔ ((φ⁻¹(x),x)∈φ)
    return N.modus_ponens(x_finv, equivalence_avant(cr))               # (φ⁻¹(x),x)∈φ


def section_reciproque(phi, x, T):
    """{ est_fonctionnel(φ), dom(φ⁻¹) = T,  x ∈ T }  ⊢  φ(φ⁻¹(x)) = x.

    φ⁻¹(x) := valeur(φ⁻¹, x).  Cœur : (φ⁻¹(x),x)∈φ (_couple_inverse) ; comme
    (φ⁻¹(x),φ(φ⁻¹(x)))∈φ (valeur_dans_graphe) et φ fonctionnel, x=φ(φ⁻¹(x)),
    symétrisé.  On NE passe PAS par valeur_caracterisation (dont le « y » milieu se
    capturerait avec le τ_y interne de φ⁻¹(x)) : est_fonctionnel quantifie sur
    u,v,z, donc aucune capture."""
    vphi, vx, vT = _T(phi), _T(x), _T(T)
    Phinv = E.reciproque(vphi)
    finv_x = E.valeur(Phinv, vx)                       # φ⁻¹(x)
    phi_finv_x = E.valeur(vphi, finv_x)                # φ(φ⁻¹(x))

    finv_x_in_phi = _couple_inverse(vphi, vT, vx)      # (φ⁻¹(x),x)∈φ  {dom φ⁻¹=T, x∈T}
    # (∃y)((φ⁻¹(x),y)∈φ)  : φ⁻¹(x) est dans le domaine de φ (déduit de (φ⁻¹(x),x)∈φ)
    ex_z = N.modus_ponens(finv_x_in_phi,
        N.s5(appartient(E.couple(finv_x, var("y")), vphi), vx, "y"))   # (∃y)((φ⁻¹(x),y)∈φ)
    # (φ⁻¹(x), φ(φ⁻¹(x))) ∈ φ   (valeur_dans_graphe ; déchargé de ex_z)
    finv_phi = N.modus_ponens(ex_z, N.loi_deduction(
        existe("y", appartient(E.couple(finv_x, var("y")), vphi)),
        valeur_dans_graphe(vphi, finv_x)))             # (φ⁻¹(x),φ(φ⁻¹(x)))∈φ
    # φ fonctionnel : ((φ⁻¹(x),φ(φ⁻¹(x)))∈φ et (φ⁻¹(x),x)∈φ) ⇒ φ(φ⁻¹(x))=x
    #   v:=φ(φ⁻¹(x)), z:=x → consequent DIRECTEMENT φ(φ⁻¹(x))=x (PAS de symetrie, dont
    #   le trou littéral « w » casserait quand x=« w »).  Binders u,v,z (≠ y) → aucune
    #   capture par le τ_y de φ⁻¹(x).
    hfunc = N.assume(E.est_fonctionnel(vphi))
    inst = instancie(instancie(instancie(hfunc, finv_x), phi_finv_x), vx)
    return N.modus_ponens(conjonction_intro(finv_phi, finv_x_in_phi), inst)   # φ(φ⁻¹(x))=x


# ════════════════════════════════════════════════════════════════════════════
#  CONJOINT (b) : compatible_ordre(φ⁻¹, T, R', R)
# ════════════════════════════════════════════════════════════════════════════
def compatible_ordre_reciproque(phi, S, T, R, Rp):
    """{ est_fonctionnel(φ), dom φ = S,  compatible_ordre(φ,S,R,R'),
         dom(φ⁻¹) = T }
            ⊢  compatible_ordre(φ⁻¹, T, R', R)   [binders x, w].

    Le « cœur » de la réciprocité : pour x,w∈T, R'{x,w} ⇔ R{φ⁻¹(x),φ⁻¹(w)}, via
    compatible_ordre(φ,S,R,R') instanciée en (φ⁻¹(x),φ⁻¹(w)) + section φ∘φ⁻¹=Id_T.
    L'appartenance φ⁻¹(x)∈S vient de (φ⁻¹(x),x)∈φ et dom φ=S (φ⁻¹(x) = 1ʳᵉ
    coordonnée d'un couple de φ) — d'où l'on n'a PAS besoin de img(φ⁻¹,T)=S.
    Hypothèse dom φ⁻¹=T : fournie (déchargée) par l'appelant depuis est_bijection_de
    (φ⁻¹,T,S)."""
    vphi, vS, vT = _T(phi), _T(S), _T(T)
    Phinv = E.reciproque(vphi)
    vx, vw = var("x"), var("w")                        # BINDERS x, w — JAMAIS y
    finv_x = E.valeur(Phinv, vx)                       # φ⁻¹(x)
    finv_w = E.valeur(Phinv, vw)                       # φ⁻¹(w)

    # — corps sous l'hypothèse (x∈T et w∈T) —
    hyp = et(appartient(vx, vT), appartient(vw, vT))
    h = N.assume(hyp)
    x_inT = conjonction_elim_gauche(h)
    w_inT = conjonction_elim_droite(h)

    # (φ⁻¹(x),x)∈φ et (φ⁻¹(w),w)∈φ   (via _couple_inverse ; déchargé de x∈T,w∈T)
    finvx_in_phi = _decharge_xinT(_couple_inverse(vphi, vT, vx), vx, vT, x_inT)  # (φ⁻¹(x),x)∈φ
    finvw_in_phi = _decharge_xinT(_couple_inverse(vphi, vT, vw), vw, vT, w_inT)  # (φ⁻¹(w),w)∈φ
    # φ⁻¹(x)∈S et φ⁻¹(w)∈S   (1ʳᵉ coordonnée d'un couple de φ, dom φ=S)
    finv_x_inS = _premier_dans_S(vphi, vS, finv_x, vx, finvx_in_phi)   # φ⁻¹(x)∈S
    finv_w_inS = _premier_dans_S(vphi, vS, finv_w, vw, finvw_in_phi)   # φ⁻¹(w)∈S

    # compatible_ordre(φ,S,R,R') instanciée en (φ⁻¹(x), φ⁻¹(w)).
    #   ⚠️ BINDERS x,w (PAS x,y) pour la clause de φ : avec le second binder « y »,
    #   fy=valeur(φ,var y)=τy((y,y)∈φ) S'AUTO-CAPTURE (POISON) et n'est plus
    #   instanciable.  Avec « w », fy=τy((w,y)∈φ) est sain.
    # ── PONT 1 (hypothèse) : compatible_ordre(φ,S,R,R') est construit en liant « j » par
    #   la fonction ; on le PONTE ∀x∀w vers le liant « y » sur les variables PLAINES x,w
    #   (φ(x)=τj((x,j)∈φ) → τy((x,y)∈φ), x plaine ⇒ pas d'imbrication, pas de capture).
    #   La preuve interne (section en « y ») se raccorde ainsi sans toucher aux τy imbriqués.
    hcompat_j = N.assume(compatible_ordre(vphi, vS, R, Rp, x="x", y="w"))   # [τj], ∀x∀w
    hx, hw = var("x"), var("w")
    xwS = et(appartient(hx, vS), appartient(hw, vS))
    phw_j = E.valeur(vphi, hw, b="j")
    phx_y = E.valeur(vphi, hx)                          # φ(x)[τy]
    body_j = instancie(instancie(hcompat_j, hx), hw)    # (x∈S∧w∈S)⇒(R{x,w}⇔R'{φx[τj],φw[τj]})
    body_y = _rw(body_j, valeur_j_egal_y(vphi, hx),
                 lambda h: impl(xwS, equiv(R(hx, hw), Rp(h, phw_j))))
    body_y = _rw(body_y, valeur_j_egal_y(vphi, hw),
                 lambda h: impl(xwS, equiv(R(hx, hw), Rp(phx_y, h))))
    hcompat = N.generalisation("x", N.generalisation("w", body_y))   # compatible_ordre(φ)[τy]
    inst = instancie(instancie(hcompat, finv_x), finv_w)
    #   (φ⁻¹(x)∈S et φ⁻¹(w)∈S) ⇒ (R{φ⁻¹(x),φ⁻¹(w)} ⇔ R'{φ(φ⁻¹(x))[τy],φ(φ⁻¹(w))[τy]})
    equiv_phi = N.modus_ponens(conjonction_intro(finv_x_inS, finv_w_inS), inst)
    #   R{φ⁻¹(x),φ⁻¹(w)} ⇔ R'{φ(φ⁻¹(x))[τy], φ(φ⁻¹(w))[τy]}   (raccordé à la section en « y »)

    # section : φ(φ⁻¹(x))=x  et  φ(φ⁻¹(w))=w   (preuve INTERNE en liant « y », inchangée)
    sec_x = _section_local(vphi, vx, vT, x_inT)        # φ(φ⁻¹(x))[τy]=x
    sec_w = _section_local(vphi, vw, vT, w_inT)        # φ(φ⁻¹(w))[τy]=w
    phi_finv_x = E.valeur(vphi, finv_x)                # φ(φ⁻¹(x))[τy]
    phi_finv_w = E.valeur(vphi, finv_w)                # φ(φ⁻¹(w))[τy]

    # réécriture Leibniz (S6) : R'{φ(φ⁻¹(x)),φ(φ⁻¹(w))} ⇔ R'{x,w}
    leib1 = N.modus_ponens(sec_x, N.s6(phi_finv_x, vx, "w0", Rp(var("w0"), phi_finv_w)))
    #   R'{φ(φ⁻¹(x)),φ(φ⁻¹(w))} ⇔ R'{x, φ(φ⁻¹(w))}
    leib2 = N.modus_ponens(sec_w, N.s6(phi_finv_w, vw, "w0", Rp(vx, var("w0"))))
    #   R'{x,φ(φ⁻¹(w))} ⇔ R'{x, w}
    rp_eq = equivalence_transitivite(leib1, leib2)     # R'{φ(φ⁻¹(x)),φ(φ⁻¹(w))} ⇔ R'{x,w}

    # R{φ⁻¹(x),φ⁻¹(w)} ⇔ R'{x,w}, puis symétrie ⇒ R'{x,w} ⇔ R{φ⁻¹(x),φ⁻¹(w)}
    chained = equivalence_transitivite(equiv_phi, rp_eq)   # R{φ⁻¹(x)[τy],φ⁻¹(w)[τy]} ⇔ R'{x,w}
    body = equivalence_symetrie(chained)                   # R'{x,w} ⇔ R{φ⁻¹(x)[τy],φ⁻¹(w)[τy]}

    # ── PONT 2 (frontière corps→cible) : φ⁻¹(·) en τy → τj ──
    #   la cible compatible_ordre(φ⁻¹,T,R',R) écrit φ⁻¹(·) en liant « j » ; le corps
    #   est en « y » (valeur_dans_graphe/AXIOME_DOM internes).  On réécrit y→j.
    finv_x_j, finv_w_j = E.valeur(Phinv, vx, b="j"), E.valeur(Phinv, vw, b="j")
    body = _rw(body, valeur_y_egal_j(Phinv, vx),
               lambda hh: equiv(Rp(vx, vw), R(hh, finv_w)))
    body = _rw(body, valeur_y_egal_j(Phinv, vw),
               lambda hh: equiv(Rp(vx, vw), R(finv_x_j, hh)))
    #   body : R'{x,w} ⇔ R{φ⁻¹(x)[τj], φ⁻¹(w)[τj]}  = corps de compatible_ordre(φ⁻¹,T,R',R)

    inner = N.loi_deduction(hyp, body)
    return N.generalisation("x", N.generalisation("w", inner))


def _decharge_xinT(thm, vx, vT, x_inT_thm):
    """Décharge l'hypothèse « x∈T » de `thm` en la branchant sur x_inT_thm
    (qui prouve x∈T sans cette hypothèse)."""
    return N.modus_ponens(x_inT_thm,
        N.loi_deduction(appartient(vx, vT), thm))


def _premier_dans_S(vphi, vS, finvt, vt, couple_thm):
    """{ dom φ = S } + (⊢ (φ⁻¹(t),t)∈φ)  ⊢  φ⁻¹(t) ∈ S.

    φ⁻¹(t) est la 1ʳᵉ coordonnée d'un couple de φ, donc dans dom φ = S.  Binders
    FRAIS « c0 » (existentiel) et « h0 » (trou S6) : ni t (=x ou w) ni le τ_y
    interne de φ⁻¹(t) ne peuvent être capturés (variante capture-free de
    _premier_dans_X, dont le trou littéral « w » casserait sur φ⁻¹(w))."""
    # (∃y)((φ⁻¹(t),y)∈φ)  (témoin y := t ; binder « y » DIRECT pour matcher AXIOME_DOM
    #   — le τ_y interne de φ⁻¹(t) est clos, donc non capturé par ce ∃y)
    ex_y = N.modus_ponens(couple_thm,
        N.s5(appartient(E.couple(finvt, var("y")), vphi), vt, "y"))
    # φ⁻¹(t) ∈ dom φ   (AXIOME_DOM : φ⁻¹(t)∈dom φ ⇔ (∃y)((φ⁻¹(t),y)∈φ))
    ax_dom = instancie(instancie(N.axiome(E.theorie_ensembles(), E.AXIOME_DOM),
                                 vphi), finvt)
    in_dom = N.modus_ponens(ex_y, equivalence_arriere(ax_dom))   # φ⁻¹(t)∈dom φ
    # dom φ = S  ⇒  φ⁻¹(t)∈S   (trou S6 FRAIS « h0 » : ni t ni le τ_y de φ⁻¹(t) capturés)
    hdom = N.assume(egal(E.dom(vphi), vS))
    return N.modus_ponens(in_dom, equivalence_avant(N.modus_ponens(
        hdom, N.s6(E.dom(vphi), vS, "h0", appartient(finvt, var("h0"))))))   # φ⁻¹(t)∈S


def _section_local(vphi, vx, vT, x_inT_thm):
    """Section φ(φ⁻¹(x))=x déchargée de x∈T (mais GARDANT {φ func, dom φ⁻¹=T}).

    Utilise section_reciproque puis branche son hyp « x∈T » sur le théorème
    x_inT_thm (déjà dérivé de (x∈T et w∈T))."""
    sec = section_reciproque(vphi, vx, vT)             # {φ func, dom φ⁻¹=T, x∈T} ⊢ φ(φ⁻¹(x))=x
    return N.modus_ponens(x_inT_thm,
        N.loi_deduction(appartient(vx, vT), sec))      # décharge x∈T par x_inT_thm


# ════════════════════════════════════════════════════════════════════════════
#  THÉORÈME KEYSTONE : l'iso réciproque est un iso d'ordre
# ════════════════════════════════════════════════════════════════════════════
# @livre Ch.III §2.5 Demo.3 | E III.21 L.23-38 | PDF p.124  (outil de la démonstration du Th. 3 : réciproque d'un iso d'ordre — énoncé général en E III.1, non recensé ici)
def reciproque_isomorphisme_ordre(phi="phi", S="S", T="T", R=None, Rp=None):
    """{ est_isomorphisme_ordre(φ,S,T,R,R'),  est_fonctionnel(φ),  dom φ = S }
            ⊢  est_isomorphisme_ordre(φ⁻¹, T, S, R', R).

    KEYSTONE (Bourbaki E.III.1.3 ; brique de Th3 §III.2) : la bijection réciproque
    d'un isomorphisme d'ensembles ordonnés est un isomorphisme.

    Conjoint (a) : est_bijective(φ⁻¹,T,S) via reciproque_est_bijection (Prop. 7),
    le pont 2→4 conjoints étant bouclé par les hyps func + dom=S.
    Conjoint (b) : compatible_ordre(φ⁻¹,T,R',R) via compatible_ordre_reciproque."""
    vphi, vS, vT = _T(phi), _T(S), _T(T)
    if R is None:
        R = _R_defaut("G")
    if Rp is None:
        Rp = _R_defaut("Gp")
    Phinv = E.reciproque(vphi)

    # ── hypothèses du séquent ──────────────────────────────────────────────────
    #   ⚠️ BINDERS x,w (PAS x,y) pour la clause de compatibilité de l'iso : le
    #   second binder « y » empoisonnerait fy=valeur(φ,var y) par auto-capture τ_y.
    #   C'est la forme SAINE (fidèle, simple α-renommage du liant) de l'iso.
    iso = est_isomorphisme_ordre(vphi, vS, vT, R, Rp, x="x", y="w")
    h_iso = N.assume(iso)                                            # iso φ (binders x,w)
    h_func = N.assume(E.est_fonctionnel(vphi))                        # φ fonctionnel
    h_dom = N.assume(egal(E.dom(vphi), vS))                           # dom φ = S

    # ── (a) bijection : reconstruire est_bijection_de(φ,S,T) puis Prop. 7 ──────
    bijve = isomorphisme_ordre_est_bijection(vphi, vS, vT, R, Rp, x="x", y="w")
    bijve = N.modus_ponens(h_iso, N.loi_deduction(iso, bijve))       # {iso}⊢ est_bijective(φ,S,T)
    bij_de = conjonction_intro(conjonction_intro(h_func, h_dom), bijve)  # est_bijection_de(φ,S,T)
    rb = reciproque_est_bijection(vphi, vS, vT)                       # bij(φ,S,T) ⇒ bij(φ⁻¹,T,S)
    bij_rec = N.modus_ponens(bij_de, rb)                             # est_bijection_de(φ⁻¹,T,S)
    # conjoints de est_bijection_de(φ⁻¹,T,S) = ((func,dom=T),est_bijective(φ⁻¹,T,S))
    gauche_rec = conjonction_elim_gauche(bij_rec)
    finv_dom = conjonction_elim_droite(gauche_rec)                   # dom φ⁻¹ = T
    finv_bijve = conjonction_elim_droite(bij_rec)                    # est_bijective(φ⁻¹,T,S)

    # ── (b) compatible_ordre(φ⁻¹,T,R',R) ──────────────────────────────────────
    compat_phi = isomorphisme_ordre_compatible(vphi, vS, vT, R, Rp, x="x", y="w")
    compat_phi = N.modus_ponens(h_iso, N.loi_deduction(iso, compat_phi))   # {iso}⊢ compatible_ordre(φ,S,R,R')

    compat_rec = compatible_ordre_reciproque(vphi, vS, vT, R, Rp)
    # hyps de compat_rec : {φ func, dom φ=S, compatible_ordre(φ,S,R,R'), dom φ⁻¹=T}.
    # On décharge :
    #   - compatible_ordre(φ,S,R,R')  par compat_phi
    #   - dom(φ⁻¹)=T                   par finv_dom
    #   - φ fonctionnel               reste h_func  (hyp du séquent)
    #   - dom φ=S                      reste h_dom   (hyp du séquent)
    compat_rec = _decharge(compat_rec, [
        (compatible_ordre(vphi, vS, R, Rp, x="x", y="w"), compat_phi),
        (egal(E.dom(Phinv), vT), finv_dom),
    ])

    return conjonction_intro(finv_bijve, compat_rec)


def _decharge(thm, pairs):
    """Remplace dans `thm` chaque hypothèse `formule` par les hyps de sa `preuve`
    (loi_deduction puis modus_ponens) — cf. `_cut` de ensembles_bijection."""
    for formule, preuve in pairs:
        thm = N.modus_ponens(preuve, N.loi_deduction(formule, thm))
    return thm


def cible_reciproque_isomorphisme_ordre(phi="phi", S="S", T="T", R=None, Rp=None):
    """Conclusion exacte de reciproque_isomorphisme_ordre (pour les tests)."""
    vphi, vS, vT = _T(phi), _T(S), _T(T)
    if R is None:
        R = _R_defaut("G")
    if Rp is None:
        Rp = _R_defaut("Gp")
    return est_isomorphisme_ordre(E.reciproque(vphi), vT, vS, Rp, R, x="x", y="w")


__all__ = ["section_reciproque", "compatible_ordre_reciproque",
           "reciproque_isomorphisme_ordre", "cible_reciproque_isomorphisme_ordre"]
