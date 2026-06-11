"""§III.2 — Théorème 3 (TRICHOTOMIE) : dom(h) est un SEGMENT de E (initialité).

────────────────────────────────────────────────────────────────────────────────
RÔLE.  Complète l'étape (d.3) du blueprint DESIGN_trichotomie_III2.md : l'iso
MAXIMAL h (ensembles_trichotomie_scaffold) a pour domaine S₀ := dom(h) et pour
image T₀ := pr₂(h).  Pour conclure « h : S₀ ≅ T₀, S₀ segment de E, T₀ segment de F »
il faut établir que dom(h) (et pr₂(h)) sont des SEGMENTS — c.-à-d. CLOS VERS LE BAS
(initiaux).  Le scaffold a déjà clos l'INCLUSION dom(h)⊂E (M.h_dom_inclus_E) et
pr₂(h)⊂F (M.h_img_inclus_F) ; ce module fournit la clause d'INITIALITÉ manquante,
qui, conjointe à l'inclusion, DONNE est_segment(dom h, R, E).

est_segment(S,R,E) (E.III.2.1, Déf. 2) = S⊂E  ET
    (∀x)(∀y)( (x∈S et y∈E et R{y,x}) ⇒ y∈S )          [INITIALITÉ / clôture-bas].

────────────────────────────────────────────────────────────────────────────────
IDÉE (fidèle Bourbaki, dom).  x∈dom h ⇒ (x,v)∈h ⇒ (h_membre_donne_temoin) il existe
un segment S de E, un segment T de F, un iso φ:S≅T avec x∈S, v=φ(x).  Si y∈E et
y≤x, alors par INITIALITÉ de S (S segment de E), y∈S.  Alors (y, φ(y)) ∈ h
(couple_iso_dans_h), donc y∈dom h.

LE SEUL pas non porté par le scaffold INCONDITIONNEL : couple_iso_dans_h exige
φ(y)∈F.  C'est la propriété de CODOMAINE de l'iso bijectif φ:S→T⊂F (φ(y)∈T⊂F) ;
est_isomorphisme_ordre porte est_bijective(φ,S,T) mais PAS la structure de graphe
(φ⊂S×T, dom φ=S) nécessaire à valeur_dans_codomaine.  On la PREND donc en HYPOTHÈSE
explicite CLEAN, universellement quantifiée sur (p,S,T,φ), JAMAIS postulée :

    val_dans_F(E,R,F,Rp) :=
      (∀p)(∀S)(∀T)(∀φ)( ( p∈E et est_segment(S,R,E) et est_segment(T,Rp,F)
                          et est_isomorphisme_ordre(φ,S,T,R,Rp) et p∈S )
                        ⇒ valeur(φ,p) ∈ F ).

C'est VRAI (φ(p)∈T par bijectivité, T⊂F par segment) et c'est EXACTEMENT le maillon
de codomaine manquant — reporté comme hypothèse, jamais comme théorème.

────────────────────────────────────────────────────────────────────────────────
CE MODULE LIVRE (salvage fort gradué, honnête, theorie=22) :

  ⚠️ CONDITIONNEL (hypothèse de codomaine EXPLICITE val_dans_F) :
     • dom_h_initial_sous_val   : sous {val_dans_F} ⊢ clause d'INITIALITÉ de dom(h).
     • dom_h_est_segment_sous_val: sous {val_dans_F} ⊢ est_segment(dom h, R, E).
       (la borne dom(h)⊂E est INCONDITIONNELLE, M.h_dom_inclus_E ; seule l'initialité
        porte l'hypothèse de codomaine.)

  ⚠️ REPORTÉ — pr₂(h) segment de F : l'initialité de l'IMAGE requiert l'iso INVERSE /
     la surjectivité de φ (maillon distinct), reporté dans
     ensembles_trichotomie_img_segment.py (hypothèses explicites).

INVARIANT : theorie_ensembles() = 22.  Rien postulé : tout DÉRIVE de l'axiome de h
(scaffold), AXIOME_DOM, est_segment (Déf. 2) et l'hypothèse de codomaine EXPLICITE.
NON vacueux : la conclusion y∈dom(h) / est_segment(dom h,…) n'est aucune hypothèse.
"""
from __future__ import annotations

from bourbaki.logique.formule import (
    Terme, var, egal, et, non, impl, equiv, appartient, existe, pourtout, inclus,
)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.ordre import ensembles_ordre_vocab as V
from bourbaki.logique.tactiques.tactiques_abrege import syllogisme
from bourbaki.logique.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, instancie,
)
from bourbaki.logique.tactiques.tactiques_abrege_quantif import existe_elimination
from bourbaki.cardinaux import ensembles_trichotomie_scaffold as TS
from bourbaki.cardinaux import ensembles_trichotomie_scaffold_maximalite as M


def _t(t):
    return t if isinstance(t, Terme) else var(t)


def _R_de(R):
    """Relation (a,b)↦(a,b)∈R associée au graphe R (convention projet)."""
    vR = _t(R)
    return lambda a, b: appartient(E.couple(_t(a), _t(b)), vR)


def _inst_dom(g, x):
    """⊢ (x ∈ dom G) ⇔ (∃y)((x,y) ∈ G).   (le ∃ natif est sur le liant « y ».)"""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_DOM)
    return instancie(instancie(ax, g), x)


# ════════════════════════════════════════════════════════════════════════════
#  HYPOTHÈSE DE CODOMAINE (EXPLICITE) — le seul maillon non porté par le scaffold.
# ════════════════════════════════════════════════════════════════════════════
def val_dans_F(E_set="E", R="R", F_set="F", Rp="Rp",
               p="p", S="S", T="T", phi="phi"):
    """FORMULE de CODOMAINE des isos témoins de h :

        (∀p)(∀S)(∀T)(∀φ)(
            ( p∈E et est_segment(S,R,E) et est_segment(T,Rp,F)
              et est_isomorphisme_ordre(φ,S,T,R,Rp) et p∈S )
          ⇒ valeur(φ,p) ∈ F ).

    « la valeur φ(p) d'un iso de segments φ:S≅T (S segment de E, T segment de F),
    pour p dans le segment domaine S, appartient à F. »  VRAIE (φ(p)∈T par
    bijectivité de φ:S→T, T⊂F car T segment de F) ; c'est le maillon de CODOMAINE
    que est_isomorphisme_ordre ne porte pas explicitement (il porte est_bijective
    mais pas la structure de graphe φ⊂S×T / dom φ=S).  Prise en HYPOTHÈSE explicite,
    JAMAIS postulée comme théorème."""
    Rf, Rpf = _R_de(R), _R_de(Rp)
    vE, vF = _t(E_set), _t(F_set)
    vp, vS, vT, vphi = var(p), var(S), var(T), var(phi)
    premisse = et(et(et(et(
        appartient(vp, vE),
        E.est_segment(vS, Rf, vE)),
        E.est_segment(vT, Rpf, vF)),
        V.est_isomorphisme_ordre(vphi, vS, vT, Rf, Rpf)),
        appartient(vp, vS))
    return pourtout(p, pourtout(S, pourtout(T, pourtout(phi,
        impl(premisse, appartient(E.valeur(vphi, vp), vF))))))


def _coeur_temoin(E_set, R, F_set, Rp, x_t, v_t, S, T, phi):
    """FORMULE coeur(S,T,φ ; x,v) telle qu'elle sort de h_membre_donne_temoin :

        est_segment(S,R,E) et est_segment(T,Rp,F)
        et est_isomorphisme_ordre(φ,S,T,R,Rp) et x∈S et v=valeur(φ,x).

    x_t, v_t : TERMES (les coordonnées du couple) ; S,T,phi : NOMS de liants ∃."""
    Rf, Rpf = _R_de(R), _R_de(Rp)
    vE, vF = _t(E_set), _t(F_set)
    vS, vT, vphi = var(S), var(T), var(phi)
    return et(et(et(et(
        E.est_segment(vS, Rf, vE),
        E.est_segment(vT, Rpf, vF)),
        V.est_isomorphisme_ordre(vphi, vS, vT, Rf, Rpf)),
        appartient(x_t, vS)),
        egal(v_t, E.valeur(vphi, x_t)))


# ════════════════════════════════════════════════════════════════════════════
#  Clause d'INITIALITÉ de dom(h)  —  CONDITIONNEL à val_dans_F.
# ════════════════════════════════════════════════════════════════════════════
def dom_h_initial_sous_val(E_set="E", R="R", F_set="F", Rp="Rp",
                           x="xa", y="ya", S="S", T="T", phi="phi"):
    """⊢ { val_dans_F } ⊢ (∀x)(∀y)( (x∈dom h et y∈E et R{y,x}) ⇒ y∈dom h ).

    Clause d'INITIALITÉ (clôture-bas) de dom(h) : SOUS l'hypothèse de codomaine
    explicite val_dans_F, dom(h) est clos vers le bas.  CONDITIONNEL, theorie=22.

    PREUVE.  x∈dom h ⇒ (∃z)((x,z)∈h) ⇒ (h_membre_donne_temoin) (∃S)(∃T)(∃φ) coeur ;
    on élimine les existentielles (existe_elimination) ; sous le coeur, par initialité
    du segment S (S segment de E), y∈S, puis (y,φ(y))∈h (couple_iso_dans_h + val_dans_F),
    d'où (∃z)((y,z)∈h), i.e. y∈dom h.  NON vacueux : y∈dom h n'est aucune hypothèse.

    ⚠️ ALIGNEMENT DES LIANTS : le ∃ natif de AXIOME_DOM est sur « y » (lieur interne) ;
    on utilise donc « y » (= « z » ci-dessous) comme liant des deux existentielles de
    domaine, et des NOMS distincts (xa, ya) pour les variables universelles x, y, afin
    qu'aucune capture ni renommage-α ne soit nécessaire."""
    Rf, Rpf = _R_de(R), _R_de(Rp)
    vE, vF = _t(E_set), _t(F_set)
    vx, vy = var(x), var(y)
    h = TS.h_iso_max(E_set, R, F_set, Rp)
    # ⚠️ DEUX liants distincts :
    #   • zd  = couple value côté x (∃zd((x,zd)∈h)) ; doit ≠ « y » car le coeur porte
    #     « zd = valeur(φ,x) » et valeur(·) lie « y » par défaut (verrou liant valeur).
    #   • zy  = « y » = liant NATIF du ∃ de AXIOME_DOM côté y (aucun valeur ⇒ sûr).
    zd, zy = "zd", "y"
    vzd, vzy = var(zd), var(zy)

    # ════════ sous le coeur témoin (S,T,φ ; x, zd), démontrer y∈dom h ════════
    coeur = _coeur_temoin(E_set, R, F_set, Rp, vx, vzd, S, T, phi)
    Hcoeur = N.assume(coeur)
    c4 = conjonction_elim_gauche(Hcoeur)                       # …et x∈S
    Hx_in_S = conjonction_elim_droite(c4)                      # x∈S
    c3 = conjonction_elim_gauche(c4)                           # …et iso
    Hiso = conjonction_elim_droite(c3)                         # iso(φ,S,T)
    c2 = conjonction_elim_gauche(c3)                           # …et seg T
    Hseg_T = conjonction_elim_droite(c2)                       # est_segment(T,Rp,F)
    Hseg_S = conjonction_elim_gauche(c2)                       # est_segment(S,R,E)

    vS, vT, vphi = var(S), var(T), var(phi)
    phi_y = E.valeur(vphi, vy)                                 # φ(y)

    # ── INITIALITÉ de S : (x∈S et y∈E et R{y,x}) ⇒ y∈S ──
    Hy_in_E = N.assume(appartient(vy, vE))                     # y∈E
    HRyx = N.assume(Rf(vy, vx))                                # R{y,x}
    init_S = conjonction_elim_droite(Hseg_S)                   # (∀a)(∀b)(… ⇒ b∈S)
    init_xy = instancie(instancie(init_S, vx), vy)             # (x∈S et y∈E et R{y,x})⇒y∈S
    premisse_init = conjonction_intro(
        conjonction_intro(Hx_in_S, Hy_in_E), HRyx)             # (x∈S et y∈E) et R{y,x}
    Hy_in_S = N.modus_ponens(premisse_init, init_xy)          # y∈S

    # ── φ(y)∈F via val_dans_F (instanciée à p:=y, S,T,φ) ──
    Hval = N.assume(val_dans_F(E_set, R, F_set, Rp))
    val_inst = instancie(instancie(instancie(instancie(Hval, vy), vS), vT), vphi)
    premisse_val = conjonction_intro(conjonction_intro(conjonction_intro(
        conjonction_intro(Hy_in_E, Hseg_S), Hseg_T), Hiso), Hy_in_S)
    Hphi_y_in_F = N.modus_ponens(premisse_val, val_inst)      # φ(y)∈F

    # ── (y, vv) ∈ h  via couple_iso_dans_h, vv VARIABLE FRAÎCHE pour la valeur ──
    # ⚠️ on N'INJECTE PAS le terme φ(y) comme valeur (il mentionne le liant φ que
    #    couple_iso_dans_h ré-existentialise ⇒ capture).  On prend une VARIABLE vv
    #    avec les hypothèses vv∈F et vv=φ(y), qu'on éliminera ensuite par ∃vv.
    vv_name = "vv"
    vvv = var(vv_name)
    cid = TS.couple_iso_dans_h(E_set, R, F_set, Rp, S, T, phi, y, vv_name)
    Hvv_F = N.assume(appartient(vvv, vF))                      # vv∈F   (hyp, à éliminer)
    Hvv_eq = N.assume(egal(vvv, phi_y))                        # vv=φ(y)(hyp, à éliminer)
    preuves = [
        (E.est_segment(vS, Rf, vE), Hseg_S),
        (E.est_segment(vT, Rpf, vF), Hseg_T),
        (V.est_isomorphisme_ordre(vphi, vS, vT, Rf, Rpf), Hiso),
        (appartient(vy, vS), Hy_in_S),
        (appartient(vy, vE), Hy_in_E),
        (appartient(vvv, vF), Hvv_F),
        (egal(vvv, phi_y), Hvv_eq),
    ]
    couple_in_h = cid
    for hyp_f, preuve in preuves:
        couple_in_h = N.modus_ponens(preuve, N.loi_deduction(hyp_f, couple_in_h))
    # couple_in_h : {coeur, y∈E, R{y,x}, vv∈F, vv=φ(y)} ⊢ (y, vv) ∈ h

    # ── (∃zy)((y,zy)∈h)  (liant natif zy=« y »)  puis  y∈dom h ──
    body_ex = appartient(E.couple(vy, vzy), h)                 # (y,zy)∈h   (zy liant)
    ex_z = N.modus_ponens(couple_in_h, N.s5(body_ex, vvv, zy)) # (∃zy)((y,zy)∈h)
    dom_eq_y = _inst_dom(h, vy)                                # y∈domh ⇔ (∃y)((y,y)∈h)
    y_in_dom_vv = N.modus_ponens(ex_z, equivalence_arriere(dom_eq_y))  # y∈dom h [..,vv∈F,vv=φ(y)]

    # ── éliminer vv : (vv∈F et vv=φ(y)) ⇒ y∈dom h, puis (∃vv)(…) ⇒ y∈dom h ──
    prem_vv = et(appartient(vvv, vF), egal(vvv, phi_y))
    Hprem_vv = N.assume(prem_vv)
    # y_in_dom_vv dépend de {vv∈F, vv=φ(y)} ; on décharge ces deux, puis on FOURNIT
    # les conjoints de prem_vv → y∈dom h sous {coeur, y∈E, R{y,x}, prem_vv}.
    y_in_dom_2 = N.modus_ponens(
        conjonction_elim_droite(Hprem_vv),                    # vv=φ(y)
        N.modus_ponens(conjonction_elim_gauche(Hprem_vv),     # vv∈F
                       N.loi_deduction(appartient(vvv, vF),
                           N.loi_deduction(egal(vvv, phi_y), y_in_dom_vv))))
    # y_in_dom_2 : {coeur, y∈E, R{y,x}, prem_vv} ⊢ y∈dom h
    imp_vv = N.loi_deduction(prem_vv, y_in_dom_2)             # prem_vv ⇒ y∈dom h
    ex_vv_to_dom = existe_elimination(imp_vv, vv_name)        # (∃vv)prem_vv ⇒ y∈dom h
    # (∃vv)(vv∈F et vv=φ(y)) depuis φ(y)∈F (témoin vv:=φ(y), φ(y)=φ(y))
    refl = N.reflexivite(phi_y)                               # φ(y)=φ(y)
    ex_vv = N.modus_ponens(
        conjonction_intro(Hphi_y_in_F, refl),                # φ(y)∈F et φ(y)=φ(y)
        N.s5(prem_vv, phi_y, vv_name))                       # ⇒ (∃vv)(vv∈F et vv=φ(y))
    y_in_dom = N.modus_ponens(ex_vv, ex_vv_to_dom)           # y∈dom h [coeur,y∈E,R{y,x},val]

    # ════════ décharger le coeur, puis éliminer φ, T, S ════════
    imp_coeur = N.loi_deduction(coeur, y_in_dom)              # coeur ⇒ y∈dom h
    imp_phi = existe_elimination(imp_coeur, phi)             # (∃φ)coeur ⇒ y∈dom h
    imp_T = existe_elimination(imp_phi, T)                   # (∃T)(∃φ)coeur ⇒ y∈dom h
    imp_S = existe_elimination(imp_T, S)                     # (∃S)(∃T)(∃φ)coeur ⇒ y∈dom h

    # ════════ raccord à (x,zd)∈h via h_membre_donne_temoin, puis (∃zd)((x,zd)∈h) ════════
    # ⚠️ liants par DÉFAUT (u,v) pour h_membre_donne_temoin (v≠« y » : sinon capture du
    #    τ-binder « y » de valeur(φ,u) lors de la construction du témoin) ; on instancie
    #    ensuite au couple (x, zd).
    hdt = TS.h_membre_donne_temoin(E_set, R, F_set, Rp, "u", "v", S, T, phi)
    # hdt : (∀u)(∀v)( (u,v)∈h ⇒ (∃S)(∃T)(∃φ) coeur(S,T,φ ; u, v) )
    couple_imp = instancie(instancie(hdt, vx), vzd)          # (x,zd)∈h ⇒ (∃S)(∃T)(∃φ)coeur(…;x,zd)
    cz_to_dom = syllogisme(couple_imp, imp_S)                # (x,zd)∈h ⇒ y∈dom h
    ex_v_to_dom = existe_elimination(cz_to_dom, zd)          # (∃zd)((x,zd)∈h) ⇒ y∈dom h
    # AXIOME_DOM donne x∈domh ⇔ (∃y)((x,y)∈h) ; α-renommer (∃y)→(∃zd) pour raccorder.
    from bourbaki.logique.tactiques.tactiques_abrege_quantif import alpha_existe
    dom_eq_x = _inst_dom(h, vx)                              # x∈domh ⇔ (∃y)((x,y)∈h)
    body_x_native = appartient(E.couple(vx, vzy), h)         # (x,y)∈h   (liant natif « y »)
    ren_x = alpha_existe(zy, zd, body_x_native)             # (∃y)((x,y)∈h) ⇔ (∃zd)((x,zd)∈h)
    x_dom_to_ex = syllogisme(equivalence_avant(dom_eq_x),
                             equivalence_avant(ren_x))        # x∈domh ⇒ (∃zd)((x,zd)∈h)
    x_to_dom = syllogisme(x_dom_to_ex, ex_v_to_dom)         # x∈domh ⇒ y∈dom h

    # ════════ assembler la prémisse de est_segment : (x∈domh et y∈E) et R{y,x} ════════
    # x_to_dom a hyps {y∈E, R{y,x}, val_dans_F}.  On DÉCHARGE y∈E et R{y,x} (en
    # antécédents), puis on rebâtit depuis la prémisse triple de est_segment, dont les
    # conjoints fournissent x∈domh, y∈E, R{y,x} ; seul val_dans_F subsiste en hypothèse.
    imp1 = N.loi_deduction(Rf(vy, vx), x_to_dom)            # {y∈E,val} ⊢ R{y,x}⇒(x∈domh⇒y∈domh)
    imp2 = N.loi_deduction(appartient(vy, vE), imp1)        # {val} ⊢ y∈E⇒(R{y,x}⇒(x∈domh⇒y∈domh))
    premisse_seg = et(et(appartient(vx, E.dom(h)), appartient(vy, vE)), Rf(vy, vx))
    Hprem = N.assume(premisse_seg)
    Hx_dom = conjonction_elim_gauche(conjonction_elim_gauche(Hprem))   # x∈dom h
    Hy_E2 = conjonction_elim_droite(conjonction_elim_gauche(Hprem))    # y∈E
    HRyx2 = conjonction_elim_droite(Hprem)                            # R{y,x}
    step = N.modus_ponens(HRyx2, N.modus_ponens(Hy_E2, imp2))   # x∈domh ⇒ y∈dom h
    y_in_dom_final = N.modus_ponens(Hx_dom, step)              # y∈dom h  [hyps: premisse_seg, val]
    body = N.loi_deduction(premisse_seg, y_in_dom_final)      # premisse ⇒ y∈dom h  [hyps: val]
    return N.generalisation(x, N.generalisation(y, body))    # initialité de dom(h)


def dom_h_initial_cible(E_set="E", R="R", F_set="F", Rp="Rp", x="xa", y="ya"):
    """ÉNONCÉ-cible (test miroir) de la clause d'initialité de dom(h)."""
    Rf = _R_de(R)
    vE = _t(E_set)
    h = TS.h_iso_max(E_set, R, F_set, Rp)
    vx, vy = var(x), var(y)
    return pourtout(x, pourtout(y,
        impl(et(et(appartient(vx, E.dom(h)), appartient(vy, vE)), Rf(vy, vx)),
             appartient(vy, E.dom(h)))))


# ════════════════════════════════════════════════════════════════════════════
#  dom(h) est un SEGMENT de E  —  CONDITIONNEL à val_dans_F.
# ════════════════════════════════════════════════════════════════════════════
def dom_h_est_segment_sous_val(E_set="E", R="R", F_set="F", Rp="Rp",
                               x="xa", y="ya", S="S", T="T", phi="phi"):
    """⊢ { val_dans_F } ⊢ est_segment(dom h, R, E).

    Conjonction de la borne dom(h)⊂E (INCONDITIONNELLE, M.h_dom_inclus_E) et de la
    clause d'initialité (dom_h_initial_sous_val, conditionnelle à val_dans_F).
    est_segment(dom h, R, E) = et( dom h ⊂ E , initialité-clause ).  CONDITIONNEL,
    theorie=22.  NON vacueux."""
    incl = M.h_dom_inclus_E(E_set, R, F_set, Rp)             # dom(h) ⊂ E  (INCOND.)
    init = dom_h_initial_sous_val(E_set, R, F_set, Rp, x, y, S, T, phi)
    return conjonction_intro(incl, init)


def dom_h_est_segment_cible(E_set="E", R="R", F_set="F", Rp="Rp", x="xa", y="ya"):
    """ÉNONCÉ-cible (test miroir) : est_segment(dom h, R, E) avec binders (x,y)."""
    Rf = _R_de(R)
    vE = _t(E_set)
    h = TS.h_iso_max(E_set, R, F_set, Rp)
    return E.est_segment(E.dom(h), Rf, vE, x, y)


__all__ = [
    "val_dans_F",
    "dom_h_initial_sous_val", "dom_h_initial_cible",
    "dom_h_est_segment_sous_val", "dom_h_est_segment_cible",
]
