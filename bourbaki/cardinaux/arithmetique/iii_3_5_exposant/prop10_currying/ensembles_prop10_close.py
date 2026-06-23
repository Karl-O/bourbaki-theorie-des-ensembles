"""§III.3.5 — PROPOSITION 10 / Corollaire 3 (forme CURRYING) : a^(b·c) = (a^b)^c.
CLÔTURE PARTIELLE — BIEN-DÉFINITION de Λ (niveaux 0 et 1) via le PONT
membership×valeur `valeur_dans_codomaine`, en représentation FIDÈLE au pont
(f(b,c) = valeur(graphe_de(f),(b,c)) = G(b,c), PAS valeur(f,...) sur le triple).

ÉNONCÉ visé (Proposition 10, currying, E.III.3.5, Cor. 3 ; signature `cible_prop10`
dans `ensembles_prop10_currying`) :

        ⊢ Card(𝓕(B×C; A)) = Card(𝓕(C; 𝓕(B;A)))                 (= a^(b·c) = (a^b)^c)

═══════════════════════════════════════════════════════════════════════════════
POURQUOI UNE CONSTRUCTION PROPRE (et non la réutilisation de `tranche` du module
`ensembles_prop10_currying`) :  ce dernier code la valeur f(b,c) comme valeur(f,…)
SUR LE TRIPLE f=((G,B×C),A) — ce qui, comme le rappelle la fiche du PONT, est du
« garbage » : la VRAIE valeur de Bourbaki est G(b,c) = valeur(graphe_de(f),(b,c)).
Le PONT `valeur_dans_codomaine(G,…)` ne s'applique qu'au GRAPHE G = graphe_de(f).
On reconstruit donc ici Λ en représentation FIDÈLE au pont :

  gr(f) := graphe_de(f) = pr₁(pr₁ f)                     (le graphe G de f)
  tranche0(f,c) := graphe_terme( B , gr(f)((q,c)) , « q » ) = { (b, G(b,c)) | b∈B }
  slice0(f,c)   := ( ( tranche0(f,c) , B ) , A )         (la tranche EMBALLÉE B→A)

═══════════════════════════════════════════════════════════════════════════════
CONTENU (paliers SÛRS, clos ; SALVAGE fort) :

NIVEAU 0 (TRANCHE).  Sous {gr⊂(B×C)×A, dom gr=B×C, c∈C} (= conjoints du témoin de
f∈𝓕(B×C;A) : G∈A^(B×C) ⟹ G⊂(B×C)×A et dom G=B×C) :
  • tranche0_inclus_produit ⊢ tranche0(f,c) ⊂ B×A   [PONT le long de q∈B] ;
  • tranche0_fonctionnel    ⊢ est_fonctionnel(tranche0(f,c))        [C54] ;
  • tranche0_domaine        ⊢ dom(tranche0(f,c)) = B                [C54] ;
  • tranche0_dans_exposant  ⊢ tranche0(f,c) ∈ A^B   [axiome_exposant : ⊂B×A ∧ fonct ∧ dom=B] ;
  • slice0_dans_BA          ⊢ slice0(f,c) = ((tranche0(f,c),B),A) ∈ 𝓕(B;A)
        [axiome_applications, témoin G:=tranche0(f,c)].

C'est le NIVEAU 0 COMPLET de la bien-définition de Λ (chaque tranche est une vraie
application B→A).  Le NIVEAU 1 (curry(f)∈𝓕(B;A)^C puis Λval(f)∈𝓕(C;𝓕(B;A))) et
l'injectivité/surjectivité à deux niveaux restent REPORTÉS — verrou identique,
redoublé par l'imbrication ; cf.
`ensembles_prop10_currying.bijection_currying_conjoints_durs_REPORTE`.

Aucun axiome ajouté (theorie_ensembles inchangée = 22) : axiome_exposant /
axiome_applications (instances GÉNÉRALES déjà admises), PONT valeur_dans_codomaine,
graphe_de_triple, C54.  Rien n'est postulé.
═══════════════════════════════════════════════════════════════════════════════
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (Terme, var, egal, et, appartient, inclus)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, instancie)
from bourbaki.logique.i_3_quantifies.tactiques_abrege_quantif import existe_elimination
from bourbaki.logique.i_4_egalitaires.tactiques_abrege_egalite import (
    composer_egalites, congruence_terme)
from bourbaki.ensembles.fonctions.ii_3_6_fonction_terme.ensembles_fonction_terme import (
    graphe_terme_fonctionnel)
from bourbaki.cardinaux.ensembles_cantor import graphe_terme_domaine
from bourbaki.ensembles.familles.ii_2_produit_deux_ensembles.ensembles_produit import couple_dans_produit
from bourbaki.ensembles.fonctions.ii_3_4_fonctions_valeur.ensembles_valeur_codomaine import (
    valeur_dans_codomaine)
from bourbaki.cardinaux.arithmetique.fondations.ensembles_graphe_de import (
    graphe_de, graphe_de_triple)
from bourbaki.cardinaux.arithmetique.iii_3_5_exposant.prop10_currying.ensembles_prop10_currying import (
    espace_BA, _VAL, membership_BCA, exposant_BA)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# ── LIANTS de la tranche0 (NIVEAU 0, standalone) ───────────────────────────────
# Le point courant interne du graphe-terme tranche0 est « x » (= _PTB).  La
# machinerie graphe-terme du projet (graphe_terme_domaine/fonctionnel,
# membre_graphe_terme, AXIOME_DOM/IMAGE) est CALIBRÉE sur le liant canonique « x »
# (et y/z pour le domaine) : on l'utilise tel quel ici (niveau 0 isolé, pas
# d'imbrication à 2 niveaux comme dans `ensembles_prop10_currying`).
#   • « x »  : point courant (la variable b) ;
#   • « m »  : liant τ de la valeur G((x,c))  (= _VAL, exotique) ;
#   • « r »  : 2ᵉ coordonnée dans la décomposition C54 de z'∈tranche0 ;
#   • « z »  : trou « w » de l'axiome C54 (le z' courant).
# T = G((x,c)) contient libres {x, c, f}, bornés {a, b (pr₁ de graphe_de), m} —
# disjoints de {y, z, r, u, v} utilisés par la machinerie : aucune capture.
_PTB = "x"
_DEC_VAL = "r"


# ═══════════════════════════════════════════════════════════════════════════════
# TERMES FIDÈLES AU PONT (f(b,c) = graphe_de(f)((b,c)))
# ═══════════════════════════════════════════════════════════════════════════════
def gr(f):
    """gr(f) := graphe_de(f) = pr₁(pr₁ f)   (le GRAPHE G de l'application f=((G,E),F))."""
    return graphe_de(_t(f))


def _val_G(f, b_pt, c_pt):
    """G(b,c) := valeur(graphe_de(f), (b_pt, c_pt), « m »)   — la VRAIE valeur de f.

    τ-liant « m » (= _VAL, exotique) : choisi DISTINCT de « y », car la machinerie
    graphe-terme (domaine/fonctionnel) réemploie « y » comme coordonnée et un τy
    libre dans T y créerait une collision.  Le PONT `valeur_dans_codomaine` produit,
    lui, la valeur avec le liant « y » (E.valeur défaut) : on RECOLLE les deux par
    α-renommage (`N.alpha_tau`, CS1) au point de consommation (cf. _pont_val_m)."""
    return E.valeur(gr(f), E.couple(_t(b_pt), _t(c_pt)), _VAL)


def tranche0(f, c_pt, a="A", b="B"):
    """tranche0(f,c) := graphe_terme( B , G(x,c) , « x » ) = { (b, G(b,c)) | b∈B }.

    Le GRAPHE FIDÈLE de b ↦ G(b,c) sur B, où G=graphe_de(f) (valeur au sens pont).
    Point courant « x » ; valeur G((x,c)) avec τ-liant « m »."""
    vb = _t(b)
    return E.graphe_terme(vb, _val_G(f, var(_PTB), c_pt), _PTB)


def slice0(f, c_pt, a="A", b="B"):
    """slice0(f,c) := ( ( tranche0(f,c) , B ) , A )   (la tranche EMBALLÉE B→A)."""
    va, vb = _t(a), _t(b)
    return E.couple(E.couple(tranche0(f, c_pt, va, vb), vb), va)


# ═══════════════════════════════════════════════════════════════════════════════
# NIVEAU 0 — tranche0(f,c) ⊂ B×A   (le PONT le long du point courant q∈B)
# ═══════════════════════════════════════════════════════════════════════════════
def _couple_dans_produit_t(vu, vv, vA, vB):
    """⊢ (u∈A et v∈B) ⇒ (u,v)∈A×B   (u,v,A,B TERMES) — couple_dans_produit généralisé.

    Généralisation u(outer)→v→A→B(inner) ; instanciation DANS LE MÊME ORDRE
    (instancie pèle l'extérieur d'abord) : u:=vu, v:=vv, A:=vA, B:=vB."""
    gen = N.generalisation("u", N.generalisation("v",
        N.generalisation("A", N.generalisation("B",
            couple_dans_produit("u", "v", "A", "B")))))
    return instancie(instancie(instancie(instancie(gen, vu), vv), vA), vB)


def tranche0_inclus_produit(f="f", c="c", a="A", b="B", cc="C"):
    """{gr⊂(B×C)×A, dom gr=B×C, c∈C} ⊢ tranche0(f,c) ⊂ B×A,   gr=graphe_de(f).

    NIVEAU 0 de la bien-définition de Λ.  tranche0(f,c)= { (q, G(q,c)) | q∈B }.
    Tout z'∈tranche0(f,c) s'écrit (q, r) avec q∈B et r=G((q,c)) (axiome C54, liant
    valeur frais « r »).  Or (q,c)∈B×C (couple_dans_produit : q∈B et c∈C), donc, par
    le PONT valeur_dans_codomaine(gr, B×C, A, (q,c)), G((q,c))∈A — i.e. r∈A.  Avec
    q∈B, (q,r)∈B×A, d'où z'=(q,r)∈B×A.  Conclusion (∀z')(z'∈tranche0 ⇒ z'∈B×A).

    Les hypothèses gr⊂(B×C)×A et dom gr=B×C sont EXACTEMENT les conjoints du témoin
    de f∈𝓕(B×C;A) (G∈A^(B×C) ⟹ G⊂(B×C)×A et dom G=B×C, axiome_exposant)."""
    vf, vc, va, vb, vcc = _t(f), _t(c), _t(a), _t(b), _t(cc)
    G = gr(vf)                                          # graphe_de(f)
    BC = E.produit(vb, vcc)                             # B×C
    T = _val_G(vf, var(_PTB), vc)                       # G((x,c))  (point courant x)
    tr = tranche0(vf, vc, va, vb)                       # graphe_terme(B, T, "x")
    BA = E.produit(vb, va)                              # B×A

    vz = var("z")
    vq, vr = var(_PTB), var(_DEC_VAL)
    # axiome C54 de tranche0, sur z' : z'∈tr ⇔ (∃x)(∃r)(z'=(x,r) et x∈B et r=T)
    th = E.theorie_graphe_terme(vb, T, _PTB, _DEC_VAL, "z")
    ax = N.axiome(th, E.axiome_graphe_terme(vb, T, _PTB, _DEC_VAL, "z"))   # (∀z)(...)
    car = instancie(ax, vz)
    body = et(et(egal(vz, E.couple(vq, vr)), appartient(vq, vb)), egal(vr, T))
    hb = N.assume(body)
    z_eq = conjonction_elim_gauche(conjonction_elim_gauche(hb))    # z'=(q,r)
    q_inB = conjonction_elim_droite(conjonction_elim_gauche(hb))   # q∈B
    r_eq_T = conjonction_elim_droite(hb)                          # r=T=G((q,c))

    # (q,c)∈B×C
    h_cinC = N.assume(appartient(vc, vcc))
    qc_in_BC = N.modus_ponens(conjonction_intro(q_inB, h_cinC),
                              _couple_dans_produit_t(vq, vc, vb, vcc))   # (q,c)∈B×C
    # PONT : G((q,c))∈A  sous {gr⊂(B×C)×A, dom gr=B×C, (q,c)∈B×C}.
    # ⚠ le pont produit la valeur avec le τ-liant « y » (E.valeur défaut) :
    #     val_y := valeur(G,(q,c),« y »)   alors que   T = valeur(G,(q,c),« m »).
    pont = valeur_dans_codomaine(G, BC, va, E.couple(vq, vc))     # val_y∈A  [hyps]
    valy_inA = N.modus_ponens(qc_in_BC, N.loi_deduction(
        appartient(E.couple(vq, vc), BC), pont))                 # val_y∈A
    # α-renommage CS1 : T = valeur(G,(q,c),« m ») = valeur(G,(q,c),« y ») = val_y.
    R_m = appartient(E.couple(E.couple(vq, vc), var(_VAL)), G)    # corps du τm : ((q,c),m)∈G
    alpha = N.alpha_tau(R_m, _VAL, "y")                          # T = val_y
    val_y = E.valeur(G, E.couple(vq, vc))                        # valeur(G,(q,c),« y »)
    # T∈A  (Leibniz : T=val_y et val_y∈A)
    T_inA = N.modus_ponens(valy_inA, equivalence_arriere(
        N.modus_ponens(alpha, N.s6(T, val_y, "w", appartient(var("w"), va)))))  # T∈A
    # r=T et T∈A ⇒ r∈A (Leibniz)
    r_inA = N.modus_ponens(T_inA, equivalence_arriere(
        N.modus_ponens(r_eq_T, N.s6(vr, T, "w", appartient(var("w"), va)))))  # r∈A
    # (q,r)∈B×A
    qr_in_BA = N.modus_ponens(conjonction_intro(q_inB, r_inA),
                              _couple_dans_produit_t(vq, vr, vb, va))   # (q,r)∈B×A
    # z'=(q,r) ⇒ z'∈B×A (Leibniz)
    z_in_BA = N.modus_ponens(qr_in_BA, equivalence_arriere(
        N.modus_ponens(z_eq, N.s6(vz, E.couple(vq, vr), "w",
                                  appartient(var("w"), BA)))))     # z'∈B×A
    imp_body = N.loi_deduction(body, z_in_BA)
    elim = existe_elimination(existe_elimination(imp_body, _DEC_VAL), _PTB)
    hz = N.assume(appartient(vz, tr))
    ex_body = N.modus_ponens(hz, equivalence_avant(car))
    z_in_BA_f = N.modus_ponens(ex_body, elim)
    imp_z = N.loi_deduction(appartient(vz, tr), z_in_BA_f)
    return N.generalisation("z", imp_z)                  # tranche0(f,c) ⊂ B×A


def tranche0_fonctionnel(f="f", c="c", a="A", b="B"):
    """⊢ est_fonctionnel(tranche0(f,c)).   (x ↦ G(x,c) a une valeur unique ; C54.)"""
    vf, vc, va, vb = _t(f), _t(c), _t(a), _t(b)
    T = _val_G(vf, var(_PTB), vc)
    return graphe_terme_fonctionnel(vb, T, _PTB, "y")


def tranche0_domaine(f="f", c="c", a="A", b="B"):
    """⊢ dom(tranche0(f,c)) = B.   (x ↦ G(x,c) est définie sur tout B ; C54.)"""
    vf, vc, va, vb = _t(f), _t(c), _t(a), _t(b)
    T = _val_G(vf, var(_PTB), vc)
    return graphe_terme_domaine(vb, T, _PTB, "y", "z")


def tranche0_dans_exposant(f="f", c="c", a="A", b="B", cc="C"):
    """{gr⊂(B×C)×A, dom gr=B×C, c∈C} ⊢ tranche0(f,c) ∈ A^B.

    axiome_exposant : G∈A^B ⇔ (G⊂B×A et G fonctionnel et dom G=B).  Les trois
    conjoints sont tranche0_inclus_produit (sous hyps), tranche0_fonctionnel (C54),
    tranche0_domaine (C54)."""
    vf, vc, va, vb, vcc = _t(f), _t(c), _t(a), _t(b), _t(cc)
    tr = tranche0(vf, vc, va, vb)
    ax = N.axiome(E.theorie_exposant(vb, va), E.axiome_exposant(vb, va))   # (∀G)(...)
    car = instancie(ax, tr)        # tr∈A^B ⇔ (tr⊂B×A et tr fonct et dom tr=B)
    incl = tranche0_inclus_produit(vf, vc, va, vb, vcc)   # tr⊂B×A  [sous hyps]
    fonct = tranche0_fonctionnel(vf, vc, va, vb)          # est_fonctionnel(tr)
    dom_eq = tranche0_domaine(vf, vc, va, vb)             # dom tr=B
    corps = conjonction_intro(conjonction_intro(incl, fonct), dom_eq)
    return N.modus_ponens(corps, equivalence_arriere(car))   # tr∈A^B  [sous hyps]


def slice0_dans_BA(f="f", c="c", a="A", b="B", cc="C"):
    """{gr⊂(B×C)×A, dom gr=B×C, c∈C} ⊢ slice0(f,c) = ((tranche0(f,c),B),A) ∈ 𝓕(B;A).

    axiome_applications : t∈𝓕(B;A) ⇔ (∃G)(t=((G,B),A) et G∈A^B).  Témoin
    G:=tranche0(f,c) : slice0(f,c)=((tranche0,B),A) (réflexivité) et tranche0∈A^B
    (tranche0_dans_exposant, sous hyps)."""
    vf, vc, va, vb, vcc = _t(f), _t(c), _t(a), _t(b), _t(cc)
    tr = tranche0(vf, vc, va, vb)
    triple = slice0(vf, vc, va, vb)                       # ((tranche0,B),A)
    ax = N.axiome(E.theorie_applications(vb, va), E.axiome_applications(vb, va))  # (∀t)(...)
    car = instancie(ax, triple)    # triple∈𝓕(B;A) ⇔ (∃G)(triple=((G,B),A) et G∈A^B)
    in_exp = tranche0_dans_exposant(vf, vc, va, vb, vcc)  # tranche0∈A^B  [sous hyps]
    refl = N.reflexivite(triple)                          # triple=((tranche0,B),A)
    wit = conjonction_intro(refl, in_exp)
    body = et(egal(triple, E.couple(E.couple(var("G"), vb), va)),
              appartient(var("G"), E.exposant(vb, va)))
    ex_G = N.modus_ponens(wit, N.s5(body, tr, "G"))       # (∃G)body
    return N.modus_ponens(ex_G, equivalence_arriere(car))  # triple∈𝓕(B;A)  [sous hyps]


# ═══════════════════════════════════════════════════════════════════════════════
# DISCHARGE — les hypothèses gr⊂(B×C)×A / dom gr=B×C viennent de f∈𝓕(B×C;A).
# ═══════════════════════════════════════════════════════════════════════════════
def slice0_dans_BA_via_membership(f="f", c="c", a="A", b="B", cc="C", w="G"):
    """⊢ f ∈ 𝓕(B×C; A) ⇒ ( c ∈ C ⇒ slice0(f,c) ∈ 𝓕(B; A) ).   [CLOS]

    BIEN-DÉFINITION de NIVEAU 0, AUTONOME et CLOSE : la VALEUR de la curryfiée Λ(f) en c —
    la tranche emballée f_c = slice0(f,c) — est une vraie application B→A, dès que
    f est une application B×C→A et c∈C.  (C'est le « pour chaque c∈C, f_c∈𝓕(B;A) »
    requis par la bien-définition de Λval(f)∈𝓕(C;𝓕(B;A)) ; le NIVEAU 1, recoller
    les f_c en curry(f)∈𝓕(B;A)^C, reste reporté.)

    Témoin G de f∈𝓕(B×C;A) (axiome_applications) : f=((G,B×C),A) et G∈A^(B×C).
    Alors graphe_de(f) = graphe_de(((G,B×C),A)) = G (graphe_de_triple + congruence),
    et G∈A^(B×C) ⟹ G⊂(B×C)×A et dom G=B×C (exposant_BA).  On RÉÉCRIT G→graphe_de(f)
    (Leibniz) pour décharger les deux hypothèses-graphe de slice0_dans_BA, puis on
    élimine ∃G (existe_elimination ; G n'apparaît pas dans la conclusion)."""
    vf, vc, va, vb, vcc = _t(f), _t(c), _t(a), _t(b), _t(cc)
    vG = var(w)
    BC = E.produit(vb, vcc)
    triple = E.couple(E.couple(vG, BC), va)              # ((G, B×C), A)
    G_de_f = graphe_de(vf)                               # graphe_de(f)

    # corps témoin de f∈𝓕(B×C;A) : (f=((G,B×C),A) et G∈A^(B×C))
    body = et(egal(vf, triple), appartient(vG, E.exposant(BC, va)))
    hbody = N.assume(body)
    h_eq = conjonction_elim_gauche(hbody)               # f = ((G,B×C),A)
    h_inexp = conjonction_elim_droite(hbody)            # G ∈ A^(B×C)

    # graphe_de(f) = G  : congruence (f=triple ⇒ graphe_de(f)=graphe_de(triple))
    #                     puis graphe_de_triple(G,B×C,A) : graphe_de(triple)=G.
    cong = N.modus_ponens(h_eq, congruence_terme(vf, triple, graphe_de(var("w"))))  # gr(f)=gr(triple)
    gr_triple = graphe_de_triple(vG, BC, va)            # graphe_de(triple) = G
    gr_eq_G = composer_egalites(cong, gr_triple)        # graphe_de(f) = G

    # G⊂(B×C)×A et dom G=B×C  (exposant_BA : G∈A^(B×C) ⇔ (G⊂(B×C)×A et fonct et dom=B×C))
    exp_car = exposant_BA(vG, va, BC)                   # G∈A^(B×C) ⇔ (G⊂(B×C)×A et fonct et dom=B×C)
    triple_conj = N.modus_ponens(h_inexp, equivalence_avant(exp_car))
    G_incl = conjonction_elim_gauche(conjonction_elim_gauche(triple_conj))   # G⊂(B×C)×A
    G_domeq = conjonction_elim_droite(triple_conj)                          # dom G=B×C

    # réécriture G→graphe_de(f) : Leibniz dans le SENS G=graphe_de(f).
    from bourbaki.logique.i_4_egalitaires.tactiques_abrege_egalite import symetrie
    G_eq_gr = N.modus_ponens(gr_eq_G, symetrie(G_de_f, vG))   # G = graphe_de(f)

    prod_BC_A = E.produit(BC, va)
    grf_incl = N.modus_ponens(G_incl, equivalence_avant(        # graphe_de(f)⊂(B×C)×A
        N.modus_ponens(G_eq_gr, N.s6(vG, G_de_f, "u", inclus(var("u"), prod_BC_A)))))
    grf_domeq = N.modus_ponens(G_domeq, equivalence_avant(      # dom graphe_de(f)=B×C
        N.modus_ponens(G_eq_gr, N.s6(vG, G_de_f, "u", egal(E.dom(var("u")), BC)))))

    # décharger les deux hypothèses-graphe de slice0_dans_BA
    slice_thm = slice0_dans_BA(vf, vc, va, vb, vcc)     # {gr⊂(B×C)×A, dom gr=B×C, c∈C} ⊢ slice0∈𝓕(B;A)
    step1 = N.modus_ponens(grf_incl, N.loi_deduction(
        inclus(G_de_f, prod_BC_A), slice_thm))
    step2 = N.modus_ponens(grf_domeq, N.loi_deduction(
        egal(E.dom(G_de_f), BC), step1))                # {c∈C, body} ⊢ slice0∈𝓕(B;A)
    # éliminer ∃G : body ⇒ slice0∈𝓕(B;A), puis (∃G)body ⇒ slice0∈𝓕(B;A)
    imp_body = N.loi_deduction(body, step2)             # {c∈C} ⊢ body ⇒ slice0∈𝓕(B;A)
    elim = existe_elimination(imp_body, w)              # {c∈C} ⊢ (∃G)body ⇒ slice0∈𝓕(B;A)
    # (∃G)body ⇔ f∈𝓕(B×C;A)  (membership_BCA)
    mem = membership_BCA(vf, va, vb, vcc)               # f∈𝓕(B×C;A) ⇔ (∃G)(f=((G,B×C),A) et G∈A^(B×C))
    h_f = N.assume(appartient(vf, E.applications(BC, va)))
    exG = N.modus_ponens(h_f, equivalence_avant(mem))   # (∃G)body
    concl = N.modus_ponens(exG, elim)                   # {f∈𝓕(B×C;A), c∈C} ⊢ slice0∈𝓕(B;A)
    # FOLD les deux hypothèses → théorème CLOS :  f∈𝓕(B×C;A) ⇒ (c∈C ⇒ slice0∈𝓕(B;A))
    step_c = N.loi_deduction(appartient(vc, vcc), concl)        # {f∈𝓕(B×C;A)} ⊢ c∈C ⇒ slice0∈𝓕(B;A)
    return N.loi_deduction(appartient(vf, E.applications(BC, va)), step_c)  # CLOS


# ═══════════════════════════════════════════════════════════════════════════════
# NIVEAU 1 — curry0(f) = { (c, f_c) | c∈C } est un graphe C→𝓕(B;A), et Λval0(f)
# = ((curry0(f),C),𝓕(B;A)) ∈ 𝓕(C;𝓕(B;A)).  (Le pas est DÉBLOQUÉ par le niveau 0 :
# le « pont » au niveau 1 est `slice0_dans_BA_via_membership`, déjà clos.)
# ═══════════════════════════════════════════════════════════════════════════════
#   • point courant de curry0 : « t » (la variable c).  Choisi DISTINCT de « x »
#     (point de tranche0, sinon capture inter-niveaux) ET de {p, q} (binders internes
#     de couple_dans_produit_ssi, réveillés par le PONT au sein du niveau 0 lorsqu'on
#     instancie slice0 au point courant) ET de {u, v} (binders de _couple_dans_produit_t).
#     « t » satisfait tout cela et reste compatible avec graphe_terme_domaine (y/z).
_PTC = "t"


def curry0(f, a="A", b="B", c="C"):
    """curry0(f) := graphe_terme( C , slice0(f,p) , « p » ) = { (c, f_c) | c∈C }.   (terme)

    Le GRAPHE de la curryfiée c ↦ f_c sur C, f_c = slice0(f,p) = ((tranche0(f,p),B),A).
    Point courant « p » (≠ « x » interne de tranche0 → pas de capture inter-niveaux)."""
    va, vb, vc = _t(a), _t(b), _t(c)
    return E.graphe_terme(vc, slice0(f, var(_PTC), va, vb), _PTC)


def lambda_val0(f, a="A", b="B", c="C"):
    """Λval0(f) := ( ( curry0(f) , C ) , 𝓕(B;A) )   (l'image de f par Λ, EMBALLÉE).

    La curryfiée f̃ emballée en application C→𝓕(B;A) : le triple ((curry0(f),C),𝓕(B;A))
    ∈ 𝓕(C;𝓕(B;A)).  C'est exactement Λ(f) = f̃, en représentation FIDÈLE AU PONT."""
    va, vb, vc = _t(a), _t(b), _t(c)
    return E.couple(E.couple(curry0(f, va, vb, vc), vc), espace_BA(va, vb))


def curry0_inclus_produit(f="f", a="A", b="B", c="C"):
    """⊢ f∈𝓕(B×C;A) ⇒ curry0(f) ⊂ C × 𝓕(B;A).   [CLOS]

    NIVEAU 1 de la bien-définition de Λ.  curry0(f)={ (p, f_p) | p∈C }.  Tout
    z'∈curry0(f) s'écrit (p, r) avec p∈C et r=slice0(f,p) (axiome C54, liant valeur
    « r »).  Or, sous f∈𝓕(B×C;A) et p∈C, slice0(f,p)∈𝓕(B;A)
    (`slice0_dans_BA_via_membership`, NIVEAU 0 clos) — i.e. r∈𝓕(B;A).  Avec p∈C,
    (p,r)∈C×𝓕(B;A), d'où z'=(p,r)∈C×𝓕(B;A).  Le « pont » de niveau 1 est le NIVEAU 0."""
    vf, va, vb, vc = _t(f), _t(a), _t(b), _t(c)
    BC = E.produit(vb, vc)
    FBA = espace_BA(va, vb)                              # 𝓕(B;A)
    sl = slice0(vf, var(_PTC), va, vb)                   # slice0(f,p)  (point courant p)
    cu = curry0(vf, va, vb, vc)                          # graphe_terme(C, slice0(f,p), "p")
    C_FBA = E.produit(vc, FBA)                           # C×𝓕(B;A)
    h_f = appartient(vf, E.applications(BC, va))         # f∈𝓕(B×C;A)

    vz = var("z")
    vp, vr = var(_PTC), var(_DEC_VAL)
    th = E.theorie_graphe_terme(vc, sl, _PTC, _DEC_VAL, "z")
    ax = N.axiome(th, E.axiome_graphe_terme(vc, sl, _PTC, _DEC_VAL, "z"))   # (∀z)(...)
    car = instancie(ax, vz)
    body = et(et(egal(vz, E.couple(vp, vr)), appartient(vp, vc)), egal(vr, sl))
    hb = N.assume(body)
    z_eq = conjonction_elim_gauche(conjonction_elim_gauche(hb))    # z'=(p,r)
    p_inC = conjonction_elim_droite(conjonction_elim_gauche(hb))   # p∈C
    r_eq_sl = conjonction_elim_droite(hb)                          # r=slice0(f,p)

    # slice0(f,p)∈𝓕(B;A)  via slice0_dans_BA_via_membership (sous f∈𝓕(B×C;A) et p∈C)
    via = slice0_dans_BA_via_membership(vf, vp, va, vb, vc)   # f∈𝓕(B×C;A) ⇒ (p∈C ⇒ slice0(f,p)∈𝓕(B;A))
    h_hf = N.assume(h_f)
    sl_inFBA = N.modus_ponens(p_inC, N.modus_ponens(h_hf, via))   # slice0(f,p)∈𝓕(B;A)  [hyp f∈…]
    # r=slice0(f,p) et slice0(f,p)∈𝓕(B;A) ⇒ r∈𝓕(B;A) (Leibniz)
    r_inFBA = N.modus_ponens(sl_inFBA, equivalence_arriere(
        N.modus_ponens(r_eq_sl, N.s6(vr, sl, "w", appartient(var("w"), FBA)))))  # r∈𝓕(B;A)
    # (p,r)∈C×𝓕(B;A)
    pr_in_prod = N.modus_ponens(conjonction_intro(p_inC, r_inFBA),
                                _couple_dans_produit_t(vp, vr, vc, FBA))   # (p,r)∈C×𝓕(B;A)
    # z'=(p,r) ⇒ z'∈C×𝓕(B;A)
    z_in_prod = N.modus_ponens(pr_in_prod, equivalence_arriere(
        N.modus_ponens(z_eq, N.s6(vz, E.couple(vp, vr), "w",
                                  appartient(var("w"), C_FBA)))))   # z'∈C×𝓕(B;A)
    imp_body = N.loi_deduction(body, z_in_prod)
    elim = existe_elimination(existe_elimination(imp_body, _DEC_VAL), _PTC)
    hz = N.assume(appartient(vz, cu))
    ex_body = N.modus_ponens(hz, equivalence_avant(car))
    z_in_prod_f = N.modus_ponens(ex_body, elim)
    imp_z = N.loi_deduction(appartient(vz, cu), z_in_prod_f)    # {f∈…} ⊢ z'∈cu ⇒ z'∈C×𝓕(B;A)
    incl = N.generalisation("z", imp_z)                        # {f∈…} ⊢ curry0(f) ⊂ C×𝓕(B;A)
    return N.loi_deduction(h_f, incl)                          # CLOS : f∈𝓕(B×C;A) ⇒ curry0(f)⊂C×𝓕(B;A)


def curry0_fonctionnel(f="f", a="A", b="B", c="C"):
    """⊢ est_fonctionnel(curry0(f)).   (c ↦ f_c a une valeur unique ; C54.)"""
    vf, va, vb, vc = _t(f), _t(a), _t(b), _t(c)
    sl = slice0(vf, var(_PTC), va, vb)
    return graphe_terme_fonctionnel(vc, sl, _PTC, "y")


def curry0_domaine(f="f", a="A", b="B", c="C"):
    """⊢ dom(curry0(f)) = C.   (c ↦ f_c est définie sur tout C ; C54.)"""
    vf, va, vb, vc = _t(f), _t(a), _t(b), _t(c)
    sl = slice0(vf, var(_PTC), va, vb)
    return graphe_terme_domaine(vc, sl, _PTC, "y", "z")


def curry0_dans_exposant(f="f", a="A", b="B", c="C"):
    """⊢ f∈𝓕(B×C;A) ⇒ curry0(f) ∈ 𝓕(B;A)^C.   [CLOS]

    axiome_exposant : G∈𝓕(B;A)^C ⇔ (G⊂C×𝓕(B;A) et G fonctionnel et dom G=C).  Les
    trois conjoints : curry0_inclus_produit (sous f∈𝓕(B×C;A)), curry0_fonctionnel
    (C54), curry0_domaine (C54)."""
    vf, va, vb, vc = _t(f), _t(a), _t(b), _t(c)
    BC = E.produit(vb, vc)
    FBA = espace_BA(va, vb)
    cu = curry0(vf, va, vb, vc)
    h_f = appartient(vf, E.applications(BC, va))
    ax = N.axiome(E.theorie_exposant(vc, FBA), E.axiome_exposant(vc, FBA))   # (∀G)(...)
    car = instancie(ax, cu)        # cu∈𝓕(B;A)^C ⇔ (cu⊂C×𝓕(B;A) et cu fonct et dom cu=C)
    incl_imp = curry0_inclus_produit(vf, va, vb, vc)     # f∈… ⇒ cu⊂C×𝓕(B;A)
    h_hf = N.assume(h_f)
    incl = N.modus_ponens(h_hf, incl_imp)                # cu⊂C×𝓕(B;A)  [hyp f∈…]
    fonct = curry0_fonctionnel(vf, va, vb, vc)           # est_fonctionnel(cu)
    dom_eq = curry0_domaine(vf, va, vb, vc)              # dom cu=C
    corps = conjonction_intro(conjonction_intro(incl, fonct), dom_eq)
    in_exp = N.modus_ponens(corps, equivalence_arriere(car))   # cu∈𝓕(B;A)^C  [hyp f∈…]
    return N.loi_deduction(h_f, in_exp)                  # CLOS : f∈… ⇒ curry0(f)∈𝓕(B;A)^C


def lambda_val0_dans_codomaine(f="f", a="A", b="B", c="C"):
    """⊢ f∈𝓕(B×C;A) ⇒ Λval0(f) = ((curry0(f),C),𝓕(B;A)) ∈ 𝓕(C; 𝓕(B;A)).   [CLOS]

    BIEN-DÉFINITION COMPLÈTE de Λ (les DEUX niveaux) : pour f∈𝓕(B×C;A), la curryfiée
    EMBALLÉE Λval0(f) est une vraie application C→𝓕(B;A).  C'est l'image de f par Λ
    qui tombe DANS le codomaine 𝓕(C;𝓕(B;A)) — autrement dit Λ est BIEN DÉFINIE (sa
    valeur a son image dans le codomaine), conjoint (i) reporté de
    `ensembles_prop10_currying`, ICI CLOS (en représentation fidèle au pont).

    axiome_applications : t∈𝓕(C;𝓕(B;A)) ⇔ (∃G)(t=((G,C),𝓕(B;A)) et G∈𝓕(B;A)^C).
    Témoin G:=curry0(f) : Λval0(f)=((curry0(f),C),𝓕(B;A)) (réflexivité) et
    curry0(f)∈𝓕(B;A)^C (curry0_dans_exposant, sous f∈𝓕(B×C;A))."""
    vf, va, vb, vc = _t(f), _t(a), _t(b), _t(c)
    BC = E.produit(vb, vc)
    FBA = espace_BA(va, vb)
    cu = curry0(vf, va, vb, vc)
    triple = lambda_val0(vf, va, vb, vc)                 # ((curry0(f),C),𝓕(B;A))
    h_f = appartient(vf, E.applications(BC, va))
    ax = N.axiome(E.theorie_applications(vc, FBA), E.axiome_applications(vc, FBA))  # (∀t)(...)
    car = instancie(ax, triple)    # triple∈𝓕(C;𝓕(B;A)) ⇔ (∃G)(triple=((G,C),𝓕(B;A)) et G∈𝓕(B;A)^C)
    exp_imp = curry0_dans_exposant(vf, va, vb, vc)       # f∈… ⇒ curry0(f)∈𝓕(B;A)^C
    h_hf = N.assume(h_f)
    in_exp = N.modus_ponens(h_hf, exp_imp)               # curry0(f)∈𝓕(B;A)^C  [hyp f∈…]
    refl = N.reflexivite(triple)                         # triple=((curry0(f),C),𝓕(B;A))
    wit = conjonction_intro(refl, in_exp)
    body = et(egal(triple, E.couple(E.couple(var("G"), vc), FBA)),
              appartient(var("G"), E.exposant(vc, FBA)))
    ex_G = N.modus_ponens(wit, N.s5(body, cu, "G"))      # (∃G)body
    in_appl = N.modus_ponens(ex_G, equivalence_arriere(car))   # triple∈𝓕(C;𝓕(B;A))  [hyp f∈…]
    return N.loi_deduction(h_f, in_appl)                 # CLOS : f∈… ⇒ Λval0(f)∈𝓕(C;𝓕(B;A))


__all__ = [
    "gr", "tranche0", "slice0",
    "tranche0_inclus_produit", "tranche0_fonctionnel", "tranche0_domaine",
    "tranche0_dans_exposant", "slice0_dans_BA",
    "slice0_dans_BA_via_membership",
    "curry0", "lambda_val0",
    "curry0_inclus_produit", "curry0_fonctionnel", "curry0_domaine",
    "curry0_dans_exposant", "lambda_val0_dans_codomaine",
]
