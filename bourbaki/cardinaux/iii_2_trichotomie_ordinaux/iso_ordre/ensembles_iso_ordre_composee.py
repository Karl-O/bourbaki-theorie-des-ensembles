"""§III.1.3 / §III.2 — La COMPOSÉE de deux isomorphismes d'ordre est un isomorphisme.

⊢_{ iso(g,T,U,R',R''), iso(f,S,T,R,R'), f,g fonctionnels, dom f=S, dom g=T }
    est_isomorphisme_ordre(g∘f, S, U, R, R'').

KEYSTONE de la trichotomie des ordinaux (Th3 §III.2) : la « glue » composition des
isos d'ordre AU NIVEAU GRAPHE.  Bourbaki, E.III.1.3 : « si f est un isomorphisme de
(E,Γ) sur (E',Γ') et g un isomorphisme de (E',Γ') sur (E'',Γ''), alors g∘f est un
isomorphisme de (E,Γ) sur (E'',Γ'') ».

DEUX CONJOINTS (est_isomorphisme_ordre = bijective ET compatible_ordre) :

  (a) BIJECTION.  iso(f,S,T,…) ⊢ f bijective de S sur T (proj. gauche) ; avec les
      hypothèses EXPLICITES « f fonctionnel » et « dom f=S » on RECONSTITUE le
      prédicat à 4 conjoints est_bijection_de(f,S,T) (= func ∧ dom=S ∧ bijective).
      De même est_bijection_de(g,T,U).  `composee_bijection_conjoints` (la composée
      de deux bijections est une bijection, §II.3.7) donne est_bijection_de(g∘f,S,U),
      dont on RE-EXTRAIT est_bijective(g∘f,S,U) (proj. droite).  C'est le BRIDGE 2↔4
      (est_bijective porte 2 conjoints ; est_bijection_de en porte 4) : on le franchit
      via les hypothèses fonctionnel/dom posées explicitement.

  (b) COMPATIBLE_ORDRE(g∘f, S, R, R'').  Pour x,w ∈ S (binders x,w — JAMAIS y, qui
      capturerait le τ_y de valeur) :
        R{x,w} ⇔ R'{f(x),f(w)}                        [compatible_ordre(f,S,R,R')]
        R'{f(x),f(w)} ⇔ R''{g(f(x)),g(f(w))}          [compatible_ordre(g,T,R',R''),
                                                         appliqué en f(x),f(w)∈T]
      f(x),f(w) ∈ T car f surjective sur T (image(f,S)=T) — lemme
      `valeur_dans_but_surjectif`.  Transitivité des ⇔ : R{x,w} ⇔ R''{g(f(x)),g(f(w))}.
      Enfin (g∘f)(x)=g(f(x)) et (g∘f)(w)=g(f(w))  [composition_valeur] réécrivent
      (Leibniz S6) les deux arguments : R{x,w} ⇔ R''{(g∘f)(x),(g∘f)(w)}.

Module NEUF, ne modifie aucun fichier existant.  theorie_ensembles INCHANGÉE (22
axiomes) : tout sort des théorèmes/lemmes déjà certifiés et des règles primitives.
Rien n'est postulé, aucune tautologie, aucun affaiblissement.
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (Terme, var, egal, et, appartient, existe,
                                       afficher_f)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, equivalence_transitivite,
    equivalence_symetrie, instancie)
from bourbaki.ensembles.fonctions.ii_3_4_fonctions_valeur.ensembles_fonctions import valeur_dans_graphe
from bourbaki.ensembles.fonctions.ii_3_7_composee_fonctions.ensembles_fonctions_composee import composition_valeur
from bourbaki.ordre.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_vocab import (est_isomorphisme_ordre,
                                                  compatible_ordre)
from bourbaki.ordre.iii_1_relations_ordre.isomorphismes_ordre.ensembles_pont_binder import pont_compatible
from bourbaki.cardinaux.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import est_bijection_de
from bourbaki.cardinaux.iii_3_equipotence_cardinaux.equipotence.ensembles_composee_bijection import composee_bijection_conjoints


def _T(v):
    """Coercion nom→terme (accepte un Terme ou un nom de variable)."""
    return v if isinstance(v, Terme) else var(v)


# ════════════════════════════════════════════════════════════════════════════
#  Lemme représentationnel : f(pt) ∈ T  pour pt∈S, quand f surjective sur T.
#  (Slots de Leibniz « slot0 »/« slot1 » FRAIS pour tolérer pt = x OU pt = w.)
# ════════════════════════════════════════════════════════════════════════════
def _couple_dans_graphe(vf, vS, vpt):
    """{dom f = S, pt ∈ S} ⊢ (pt, f(pt)) ∈ f.

    pt∈S et dom f=S ⇒ pt∈dom f (Leibniz, slot frais « slot0 ») ; AXIOME_DOM :
    pt∈dom f ⇔ (∃y)((pt,y)∈f) ; valeur_dans_graphe (existe_temoin/τ) ⇒ (pt,f(pt))∈f.
    Réécriture interne de couple_valeur_dans_graphe avec un slot Leibniz frais (le
    slot « w » de l'original entrerait en collision avec pt = w)."""
    h_dom = N.assume(egal(E.dom(vf), vS))
    h_pt = N.assume(appartient(vpt, vS))
    leib = N.s6(E.dom(vf), vS, "slot0", appartient(vpt, var("slot0")))
    pt_in_dom = N.modus_ponens(h_pt,
        equivalence_arriere(N.modus_ponens(h_dom, leib)))            # pt ∈ dom f
    ax_dom = N.axiome(E.theorie_ensembles(), E.AXIOME_DOM)
    dom_car = instancie(instancie(ax_dom, vf), vpt)                  # pt∈dom f ⇔ (∃y)((pt,y)∈f)
    ex_y = N.modus_ponens(pt_in_dom, equivalence_avant(dom_car))     # (∃y)((pt,y)∈f)
    cpl = valeur_dans_graphe(vf, vpt)                                # {(∃y)((pt,y)∈f)} ⊢ (pt,f(pt))∈f
    ex_form = existe("y", appartient(E.couple(vpt, var("y")), vf))
    return N.modus_ponens(ex_y, N.loi_deduction(ex_form, cpl))


def valeur_dans_but_surjectif(vf, vS, vT, vpt):
    """{dom f = S, image(f,S) = T, pt ∈ S} ⊢ f(pt) ∈ T.

    (pt,f(pt))∈f [_couple_dans_graphe] et pt∈S ⇒ f(pt)∈image(f,S) (AXIOME_IMAGE,
    sens ⇐) ; image(f,S)=T ⇒ f(pt)∈T (Leibniz, slot frais « slot1 »).  C'est « f
    prend ses valeurs dans son but » dérivé de la SURJECTIVITÉ (image=but), valable
    pour pt = x comme pour pt = w."""
    vf, vS, vT, vpt = _T(vf), _T(vS), _T(vT), _T(vpt)
    fpt = E.valeur(vf, vpt)                                          # f(pt)
    cpl = _couple_dans_graphe(vf, vS, vpt)                           # (pt,f(pt))∈f
    h_pt = N.assume(appartient(vpt, vS))                             # pt∈S
    conj = conjonction_intro(h_pt, cpl)                              # pt∈S et (pt,f(pt))∈f
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_IMAGE)
    axi = instancie(instancie(instancie(ax, vf), vS), fpt)           # f(pt)∈img ⇔ (∃z)(z∈S et (z,f(pt))∈f)
    back = equivalence_arriere(axi)                                  # (∃z)(…) ⇒ f(pt)∈image(f,S)
    ante = back.conclusion.sous[0].sous[0]                           # l'existentielle (∃z)(…) telle qu'écrite par l'axiome
    body = ante.sous[0]                                              # z∈S et (z,f(pt))∈f
    ex_intro = N.s5(body, vpt, ante.lieur)                          # (pt|z)body ⇒ (∃z)body
    ex = N.modus_ponens(conj, ex_intro)                             # (∃z)(z∈S et (z,f(pt))∈f)
    fpt_in_img = N.modus_ponens(ex, back)                           # f(pt)∈image(f,S)
    h_img = N.assume(egal(E.image(vf, vS), vT))                     # image(f,S)=T
    leib2 = N.s6(E.image(vf, vS), vT, "slot1", appartient(fpt, var("slot1")))
    return N.modus_ponens(fpt_in_img,
        equivalence_avant(N.modus_ponens(h_img, leib2)))            # f(pt)∈T


# ════════════════════════════════════════════════════════════════════════════
#  Helpers internes du conjoint (a) — reconstitution du prédicat à 4 conjoints.
# ════════════════════════════════════════════════════════════════════════════
def _bijection_de_depuis_iso(viso_bij, vF, vfunc_thm, vdom_thm):
    """De  ⊢ est_bijective(F,X,Y)  (extrait de l'iso),  ⊢ est_fonctionnel(F),
    ⊢ dom F=X  →  ⊢ est_bijection_de(F,X,Y)  (= ((func, dom), bijective)).

    Reconstitue, par conjonction, le prédicat à 4 conjoints à partir des 2 conjoints
    de est_bijective et des deux hypothèses structurelles explicites.  BRIDGE 2→4."""
    return conjonction_intro(conjonction_intro(vfunc_thm, vdom_thm), viso_bij)


# ════════════════════════════════════════════════════════════════════════════
#  LE THÉORÈME  (forme « hypothèses explicites », réutilisable / chaînable)
# ════════════════════════════════════════════════════════════════════════════
def composee_isomorphisme_ordre(f="f", g="g", S="S", T="T", U="U",
                                R=None, Rp=None, Rpp=None):
    """{ iso(g,T,U,R',R''), iso(f,S,T,R,R'), f fonctionnel, dom f=S,
         g fonctionnel, dom g=T }  ⊢  est_isomorphisme_ordre(g∘f, S, U, R, R'').

    LA COMPOSÉE DE DEUX ISOMORPHISMES D'ORDRE EST UN ISOMORPHISME D'ORDRE
    (E.III.1.3).  Conditionnel aux quatre hypothèses structurelles fonctionnel/dom
    (le BRIDGE 2↔4 des bijections), VRAIES pour tous les isos-graphes du projet ;
    le cœur substantiel est la compatibilité d'ordre de la composée.

    R, R', R'' : relations (Terme,Terme)→Formule (≤ sur S, T, U).  Par défaut on
    prend les relations « graphe » R_g{a,b}:=(a,b)∈Rg, idem Rpg, Rppg (cohérent avec
    est_isomorphisme_ordre).  Binders d'ordre x, x2 (le 2ᵉ « w » canonique est rebaptisé
    x2 : la lettre liée est immatérielle, et ce nom évite à la fois le τ_y de valeur
    [capture] ET le slot interne « w » de composition_valeur/valeur_caracterisation)."""
    if R is None:
        R = lambda a, b: appartient(E.couple(a, b), var("Rg"))
    if Rp is None:
        Rp = lambda a, b: appartient(E.couple(a, b), var("Rpg"))
    if Rpp is None:
        Rpp = lambda a, b: appartient(E.couple(a, b), var("Rppg"))

    vf, vg, vS, vT, vU = _T(f), _T(g), _T(S), _T(T), _T(U)
    comp = E.composee(vg, vf)                                        # g∘f
    vx, vw = var("x"), var("x2")
    fx, fw = E.valeur(vf, vx), E.valeur(vf, vw)                     # f(x), f(x2)

    # ── Hypothèses explicites du séquent ────────────────────────────────────────
    h_iso_g = N.assume(est_isomorphisme_ordre(vg, vT, vU, Rp, Rpp, "x", "x2"))
    h_iso_f = N.assume(est_isomorphisme_ordre(vf, vS, vT, R, Rp, "x", "x2"))
    h_func_f = N.assume(E.est_fonctionnel(vf))
    h_dom_f = N.assume(egal(E.dom(vf), vS))
    h_func_g = N.assume(E.est_fonctionnel(vg))
    h_dom_g = N.assume(egal(E.dom(vg), vT))

    # projections gauche (bijective) / droite (compatible_ordre) des deux isos
    bij_f = conjonction_elim_gauche(h_iso_f)                         # est_bijective(f,S,T)
    co_f = conjonction_elim_droite(h_iso_f)                          # compatible_ordre(f,S,R,R')[τj]
    bij_g = conjonction_elim_gauche(h_iso_g)                         # est_bijective(g,T,U)
    co_g = conjonction_elim_droite(h_iso_g)                          # compatible_ordre(g,T,R',R'')[τj]
    # PONT j→y : la preuve interne (valeur f(x), g(·), composition_valeur) est en « y » ;
    # on convertit les deux compatible_ordre du liant « j » (compatible_ordre fonction)
    # vers « y » sur les variables PLAINES x,x2 (pas de capture).
    co_f = pont_compatible(co_f, vf, vS, R, Rp, "x", "x2", "j2y")    # compatible_ordre(f,S,R,R')[τy]
    co_g = pont_compatible(co_g, vg, vT, Rp, Rpp, "x", "x2", "j2y")  # compatible_ordre(g,T,R',R'')[τy]

    # ══ CONJOINT (a) : BIJECTION  est_bijective(g∘f, S, U) ══════════════════════
    bd_f = _bijection_de_depuis_iso(bij_f, vf, h_func_f, h_dom_f)    # est_bijection_de(f,S,T)
    bd_g = _bijection_de_depuis_iso(bij_g, vg, h_func_g, h_dom_g)    # est_bijection_de(g,T,U)
    # composée de deux bijections (§II.3.7), hyps {bd_f, bd_g} déchargées par MP
    bd_comp = composee_bijection_conjoints(f, g, S, T, U)           # {bd_f,bd_g} ⊢ est_bijection_de(g∘f,S,U)
    bd_comp = N.modus_ponens(bd_f,
        N.loi_deduction(est_bijection_de(vf, vS, vT), bd_comp))
    bd_comp = N.modus_ponens(bd_g,
        N.loi_deduction(est_bijection_de(vg, vT, vU), bd_comp))     # est_bijection_de(g∘f,S,U)
    conj_a = conjonction_elim_droite(bd_comp)                       # est_bijective(g∘f,S,U)

    # ══ CONJOINT (b) : COMPATIBLE_ORDRE(g∘f, S, R, R'') ═════════════════════════
    # cible : (∀x)(∀w)((x∈S et w∈S) ⇒ (R{x,w} ⇔ R''{(g∘f)(x),(g∘f)(w)}))
    h_xw = N.assume(et(appartient(vx, vS), appartient(vw, vS)))     # x∈S et w∈S
    x_in_S = conjonction_elim_gauche(h_xw)
    w_in_S = conjonction_elim_droite(h_xw)

    # (1) R{x,w} ⇔ R'{f(x),f(w)}   [compatible_ordre(f,S,R,R') en x,w]
    eq1 = instancie(instancie(co_f, vx), vw)                        # (x∈S et w∈S) ⇒ (R{x,w}⇔R'{f(x),f(w)})
    eq1 = N.modus_ponens(h_xw, eq1)                                 # R{x,w} ⇔ R'{f(x),f(w)}

    # f(x)∈T, f(w)∈T  (surjectivité : image(f,S)=T, 2e conjoint de est_bijective(f,S,T))
    f_surj = conjonction_elim_droite(bij_f)                        # ⊢ image(f,S)=T
    fx_in_T = _decharge_valeur_but(vf, vS, vT, vx, h_dom_f, f_surj, x_in_S)   # f(x)∈T
    fw_in_T = _decharge_valeur_but(vf, vS, vT, vw, h_dom_f, f_surj, w_in_S)   # f(w)∈T

    # (2) R'{f(x),f(w)} ⇔ R''{g(f(x)),g(f(w))}   [compatible_ordre(g,T,R',R'') en f(x),f(w)]
    eq2 = instancie(instancie(co_g, fx), fw)                        # (f(x)∈T et f(w)∈T) ⇒ (R'{f(x),f(w)}⇔R''{g(f(x)),g(f(w))})
    eq2 = N.modus_ponens(conjonction_intro(fx_in_T, fw_in_T), eq2)  # R'{f(x),f(w)} ⇔ R''{g(f(x)),g(f(w))}

    # (3) transitivité : R{x,w} ⇔ R''{g(f(x)),g(f(w))}
    eq_gfx = equivalence_transitivite(eq1, eq2)

    # (4) réécriture (g∘f)(x)=g(f(x)), (g∘f)(w)=g(f(w))  [composition_valeur]  via S6
    gof_x = E.valeur(comp, vx)                                      # (g∘f)(x)
    gof_w = E.valeur(comp, vw)                                      # (g∘f)(w)
    gfx = E.valeur(vg, fx)                                          # g(f(x))
    gfw = E.valeur(vg, fw)                                          # g(f(w))
    # composition_valeur(g,f,pt) : ⊢ (g∘f)(pt) = g(f(pt))  [hyps : func f, func g, pt∈domf, f(pt)∈domg]
    cv_x = _decharge_composition_valeur(vf, vg, vS, vT, vx, h_func_f, h_func_g,
                                        h_dom_f, h_dom_g, f_surj, x_in_S)   # (g∘f)(x)=g(f(x))
    cv_w = _decharge_composition_valeur(vf, vg, vS, vT, vw, h_func_f, h_func_g,
                                        h_dom_f, h_dom_g, f_surj, w_in_S)   # (g∘f)(w)=g(f(w))
    # remplacer g(f(x)) -> (g∘f)(x) puis g(f(x2)) -> (g∘f)(x2)  (Leibniz S6, slots frais).
    # s6x : ((g∘f)(x)=g(f(x))) ⇒ (R''{(g∘f)(x),g(f(x2))} ⇔ R''{g(f(x)),g(f(x2))})
    # ⇒ MP(cv_x) ; symétrie : R''{g(f(x)),g(f(x2))} ⇔ R''{(g∘f)(x),g(f(x2))} (chaînable après eq_gfx)
    s6x = N.s6(gof_x, gfx, "slotA", Rpp(var("slotA"), gfw))
    eq_step1 = equivalence_transitivite(eq_gfx,
        equivalence_symetrie(N.modus_ponens(cv_x, s6x)))           # R{x,x2} ⇔ R''{(g∘f)(x),g(f(x2))}
    # s6w : ((g∘f)(x2)=g(f(x2))) ⇒ (R''{(g∘f)(x),(g∘f)(x2)} ⇔ R''{(g∘f)(x),g(f(x2))})
    # ⇒ MP(cv_w) ; symétrie : R''{(g∘f)(x),g(f(x2))} ⇔ R''{(g∘f)(x),(g∘f)(x2)}
    s6w = N.s6(gof_w, gfw, "slotB", Rpp(gof_x, var("slotB")))
    eq_final = equivalence_transitivite(eq_step1,
        equivalence_symetrie(N.modus_ponens(cv_w, s6w)))           # R{x,x2} ⇔ R''{(g∘f)(x),(g∘f)(x2)}

    # (∀x)(∀x2)((x∈S et x2∈S) ⇒ (R{x,x2} ⇔ R''{(g∘f)(x),(g∘f)(x2)}))
    body = N.loi_deduction(et(appartient(vx, vS), appartient(vw, vS)), eq_final)
    conj_b = N.generalisation("x", N.generalisation("x2", body))   # compatible_ordre(g∘f,S,R,R'')[τy]
    # PONT y→j : la cible est_isomorphisme_ordre(g∘f,…) écrit (g∘f)(·) en liant « j »
    # (compatible_ordre fonction) ; on convertit le corps prouvé en « y » vers « j ».
    conj_b = pont_compatible(conj_b, comp, vS, R, Rpp, "x", "x2", "y2j")   # …[τj] = cible

    # ── ASSEMBLAGE : est_isomorphisme_ordre(g∘f, S, U, R, R'') ───────────────────
    return conjonction_intro(conj_a, conj_b)


def composee_isomorphisme_ordre_implication(f="f", g="g", S="S", T="T", U="U",
                                            R=None, Rp=None, Rpp=None):
    """⊢  ( iso(g,T,U,R',R'') et iso(f,S,T,R,R') et f fonctionnel et dom f=S
            et g fonctionnel et dom g=T )  ⇒  est_isomorphisme_ordre(g∘f,S,U,R,R'').

    FORME CLOSE (0 hypothèse) du keystone : les six prémisses structurelles sont
    rassemblées en conjonction puis déchargées (loi de déduction).  C'est la version
    INCONDITIONNELLE — un théorème fermé — directement chaînable dans la trichotomie.
    Le contenu reste exactement celui de `composee_isomorphisme_ordre` : aucune
    hypothèse cachée, aucune tautologie (les six prémisses sont substantielles)."""
    if R is None:
        R = lambda a, b: appartient(E.couple(a, b), var("Rg"))
    if Rp is None:
        Rp = lambda a, b: appartient(E.couple(a, b), var("Rpg"))
    if Rpp is None:
        Rpp = lambda a, b: appartient(E.couple(a, b), var("Rppg"))
    vf, vg, vS, vT, vU = _T(f), _T(g), _T(S), _T(T), _T(U)

    thm = composee_isomorphisme_ordre(f, g, S, T, U, R, Rp, Rpp)     # 6 hyps ⊢ iso(g∘f,…)
    # décharge les 6 hypothèses, dans un ordre fixe, en les recombinant en conjonction
    h_iso_g = est_isomorphisme_ordre(vg, vT, vU, Rp, Rpp, "x", "x2")
    h_iso_f = est_isomorphisme_ordre(vf, vS, vT, R, Rp, "x", "x2")
    h_func_f = E.est_fonctionnel(vf)
    h_dom_f = egal(E.dom(vf), vS)
    h_func_g = E.est_fonctionnel(vg)
    h_dom_g = egal(E.dom(vg), vT)
    premisses = [h_iso_g, h_iso_f, h_func_f, h_dom_f, h_func_g, h_dom_g]
    conj = premisses[0]
    for p in premisses[1:]:
        conj = et(conj, p)
    # hypothèse-conjonction : on en extrait chaque conjoint et on le « met en place »
    hconj = N.assume(conj)
    # extraction itérative (conj = (((((iso_g et iso_f) et func_f) et dom_f) et func_g) et dom_g))
    parts = []
    cur = hconj
    for _ in range(len(premisses) - 1):
        parts.append(conjonction_elim_droite(cur))
        cur = conjonction_elim_gauche(cur)
    parts.append(cur)                                               # le premier conjoint
    parts = list(reversed(parts))                                  # ordre = premisses
    # décharge chaque hypothèse de `thm` en la remplaçant par sa preuve extraite
    for formule, preuve in zip(premisses, parts):
        thm = N.modus_ponens(preuve, N.loi_deduction(formule, thm))
    return N.loi_deduction(conj, thm)


# ── micro-helpers de décharge (gardent le séquent propre) ─────────────────────
def _decharge_valeur_but(vf, vS, vT, vpt, h_dom_f, f_surj, pt_in_S):
    """f(pt)∈T : instancie valeur_dans_but_surjectif et décharge ses 3 hyps
    {dom f=S, image(f,S)=T, pt∈S} par les preuves fournies (chaînage MP)."""
    thm = valeur_dans_but_surjectif(vf, vS, vT, vpt)               # hyps {dom f=S, image(f,S)=T, pt∈S}
    thm = N.modus_ponens(h_dom_f, N.loi_deduction(egal(E.dom(vf), vS), thm))
    thm = N.modus_ponens(f_surj, N.loi_deduction(egal(E.image(vf, vS), vT), thm))
    thm = N.modus_ponens(pt_in_S, N.loi_deduction(appartient(vpt, vS), thm))
    return thm


def _decharge_composition_valeur(vf, vg, vS, vT, vpt, h_func_f, h_func_g,
                                 h_dom_f, h_dom_g, f_surj, pt_in_S):
    """(g∘f)(pt) = g(f(pt)) : instancie composition_valeur et décharge ses 4 hyps
    {(∃y)((pt,y)∈f), func g, (∃y)((f(pt),y)∈g), func f} par les preuves fournies.

    Les deux existentielles « pt∈dom f » et « f(pt)∈dom g » sont fabriquées depuis
    {dom f=S, pt∈S} et {dom g=T, f(pt)∈T}."""
    fpt = E.valeur(vf, vpt)
    cv = composition_valeur(_name(vg), _name(vf), _name(vpt))      # 4 hyps ouvertes

    # hyp « func f » et « func g »
    cv = N.modus_ponens(h_func_f, N.loi_deduction(E.est_fonctionnel(vf), cv))
    cv = N.modus_ponens(h_func_g, N.loi_deduction(E.est_fonctionnel(vg), cv))

    # hyp « (∃y)((pt,y)∈f) »  ⟸  pt∈dom f  ⟸  {dom f=S, pt∈S}
    ex_f = _existe_couple(vf, vS, vpt)                            # ⊢ (∃y)((pt,y)∈f)  [hyps dom f=S, pt∈S]
    ex_f = N.modus_ponens(h_dom_f, N.loi_deduction(egal(E.dom(vf), vS), ex_f))
    ex_f = N.modus_ponens(pt_in_S, N.loi_deduction(appartient(vpt, vS), ex_f))
    ex_f_form = existe("y", appartient(E.couple(vpt, var("y")), vf))
    cv = N.modus_ponens(ex_f, N.loi_deduction(ex_f_form, cv))

    # hyp « (∃y)((f(pt),y)∈g) »  ⟸  f(pt)∈dom g  ⟸  {dom g=T, f(pt)∈T}
    fpt_in_T = _decharge_valeur_but(vf, vS, vT, vpt, h_dom_f, f_surj, pt_in_S)   # f(pt)∈T
    ex_g = _existe_couple(vg, vT, fpt)                            # ⊢ (∃y)((f(pt),y)∈g)  [hyps dom g=T, f(pt)∈T]
    ex_g = N.modus_ponens(h_dom_g, N.loi_deduction(egal(E.dom(vg), vT), ex_g))
    ex_g = N.modus_ponens(fpt_in_T, N.loi_deduction(appartient(fpt, vT), ex_g))
    ex_g_form = existe("y", appartient(E.couple(fpt, var("y")), vg))
    cv = N.modus_ponens(ex_g, N.loi_deduction(ex_g_form, cv))
    return cv


def _existe_couple(vG, vD, vpt):
    """{dom G = D, pt ∈ D} ⊢ (∃y)((pt,y) ∈ G).

    pt∈D et dom G=D ⇒ pt∈dom G (Leibniz, slot frais « slot0 ») ; AXIOME_DOM :
    pt∈dom G ⇔ (∃y)((pt,y)∈G).  (Les deux hypothèses restent ouvertes ; le caller
    les décharge par MP.)"""
    h_dom = N.assume(egal(E.dom(vG), vD))
    h_pt = N.assume(appartient(vpt, vD))
    leib = N.s6(E.dom(vG), vD, "slot0", appartient(vpt, var("slot0")))
    pt_in_dom = N.modus_ponens(h_pt,
        equivalence_arriere(N.modus_ponens(h_dom, leib)))            # pt ∈ dom G
    ax_dom = N.axiome(E.theorie_ensembles(), E.AXIOME_DOM)
    dom_car = instancie(instancie(ax_dom, vG), vpt)                  # pt∈dom G ⇔ (∃y)((pt,y)∈G)
    return N.modus_ponens(pt_in_dom, equivalence_avant(dom_car))     # (∃y)((pt,y)∈G)


def _name(t):
    """Nom de variable d'un Terme-variable (pour les helpers paramétrés par nom)."""
    return t.nom if isinstance(t, Terme) and t.tag == "var" else t


__all__ = ["composee_isomorphisme_ordre",
           "composee_isomorphisme_ordre_implication",
           "valeur_dans_but_surjectif"]
