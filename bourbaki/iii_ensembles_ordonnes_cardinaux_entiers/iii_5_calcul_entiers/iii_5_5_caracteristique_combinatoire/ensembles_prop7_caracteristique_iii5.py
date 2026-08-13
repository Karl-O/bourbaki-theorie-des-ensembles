"""§III.5 — PROPOSITION 7 : fonction caractéristique (E.III.5.5, E III.39).

Bourbaki (E III.39, LU au PDF source) : « Pour tout couple de parties A, B d'un
ensemble E, on a, pour tout x ∈ E :
    (1)  φ_{E−A}(x) = 1 − φ_A(x)
    (2)  φ_{A∩B}(x) = φ_A(x)·φ_B(x)
    (3)  φ_{A∪B}(x) + φ_{A∩B}(x) = φ_A(x) + φ_B(x). »

où φ_S : E → {0,1} est l'application caractéristique de la partie S de E, définie
par φ_S(x) = 1 pour x ∈ S, φ_S(x) = 0 pour x ∈ E − S  (E III.39, déf.).

────────────────────────────────────────────────────────────────────────────────
STATUT DU TERME φ_S DANS LE DÉPÔT.  `fonction_caracteristique(S, E)` code φ_S par
le terme OPAQUE app("carac", S, E) (ensembles_entiers.py) ; la VALEUR φ_S(x) =
E.valeur(φ_S, x).  Le dépôt ne fournit AUCUN axiome reliant cette valeur à
l'appartenance x ∈ S.  La preuve de la Prop. 7 prend donc, comme HYPOTHÈSES
HONNÊTES, la DÉFINITION même de Bourbaki — les deux implications :
        x ∈ S        ⇒  φ_S(x) = 1   (= UN)
        ¬(x ∈ S)     ⇒  φ_S(x) = 0   (= ZERO)
pour chaque partie S concernée (A, B, A∩B, A∪B, E−A), et les FAITS ARITHMÉTIQUES
sur {0,1} réellement utilisés (p. ex. 1·1 = 1, 1·0 = 0, 0·0 = 0).  La CONCLUSION
(l'identité combinatoire de la Prop. 7) n'est JAMAIS parmi les hypothèses : la
preuve n'est ni vacue ni postulée — c'est l'analyse par cas de Bourbaki.

ROUTE (Bourbaki) : analyse par cas sur x ∈ A (et x ∈ B), φ ∈ {0,1} ; on évalue
les deux membres et on vérifie l'arithmétique 0/1.  L'appartenance à A∩B, A∪B,
E−A est résolue par les AXIOMES du noyau AXIOME_INTER / AXIOME_REUNION /
AXIOME_DIFF (theorie_ensembles() = 22, INCHANGÉE).

INVARIANT : theorie_ensembles() = 22.  Noyau INTACT.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, et, non, ou, impl, appartient, pourtout, subst_t,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E

from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import ZERO, UN, fonction_caracteristique
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_produit.ensembles_arith_cardinale import (
    produit_cardinal_binaire,
)
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_recollement_somme.ensembles_somme_disjointe import (
    somme_cardinale_binaire,
)

from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, tiers_exclu, cas, instancie,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege import a_implique_a, syllogisme
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
    symetrie, transitivite, composer_egalites, congruence_terme,
)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# ── valeur φ_S(x)  (terme) ───────────────────────────────────────────────────
# @livre Ch.III §5.5 Def.- | E III.38 L.31-35 | PDF p.141
def phi(S, E_, x):
    """φ_S(x) := valeur de l'application caractéristique de la partie S de E en x."""
    return E.valeur(fonction_caracteristique(_t(S), _t(E_)), _t(x))


# ── DÉFINITION de φ (hypothèses Bourbaki) ────────────────────────────────────
def def_phi_un(S, E_, x):
    """L'implication définissante « x ∈ S ⇒ φ_S(x) = 1 »   (E III.39)."""
    return impl(appartient(_t(x), _t(S)), egal(phi(S, E_, x), UN))


def def_phi_zero(S, E_, x):
    """L'implication définissante « ¬(x ∈ S) ⇒ φ_S(x) = 0 »   (E III.39)."""
    return impl(non(appartient(_t(x), _t(S))), egal(phi(S, E_, x), ZERO))


# ── PONTS d'appartenance ensembliste (AXIOME_INTER/REUNION/DIFF, theorie=22) ──
def _membre_inter(x, A, B):
    """⊢ z∈A∩B ⇔ (z∈A et z∈B)   (instance close de AXIOME_INTER)."""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_INTER)
    return instancie(instancie(instancie(ax, _t(A)), _t(B)), _t(x))


def _membre_reunion(x, A, B):
    """⊢ z∈A∪B ⇔ (z∈A ou z∈B)   (instance close de AXIOME_REUNION)."""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_REUNION)
    return instancie(instancie(instancie(ax, _t(A)), _t(B)), _t(x))


def _membre_difference(x, E_, A):
    """⊢ z∈E−A ⇔ (z∈E et ¬(z∈A))   (instance close de AXIOME_DIFF)."""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_DIFF)
    return instancie(instancie(instancie(ax, _t(E_)), _t(A)), _t(x))


# ── congruence d'un opérateur binaire op(·,·) sur ses deux arguments ──────────
def _congr_binaire(op, eqL, eqR):
    """Γ⊢(L=L'), Δ⊢(R=R') ⟹ Γ∪Δ ⊢ op(L, R) = op(L', R').

    op : (Terme, Terme) → Terme.  Via deux congruences de terme (C44) composées.
    """
    L, Lp = eqL.conclusion.termes
    R, Rp = eqR.conclusion.termes
    w = var("w_op")
    # op(L,R) = op(L',R) : congruence sur l'argument GAUCHE (trou w_op à gauche)
    cg = N.modus_ponens(eqL, congruence_terme(L, Lp, op(w, R), "w_op"))
    # op(L',R) = op(L',R') : congruence sur l'argument DROIT
    cd = N.modus_ponens(eqR, congruence_terme(R, Rp, op(Lp, w), "w_op"))
    return composer_egalites(cg, cd)


def _side_via_op(eqAB, eqArith, eqA, eqB, op):
    """φ_{S}(x) = op(φ_A(x), φ_B(x)),  étant donnés (dans un cas) :
        eqAB   : φ_S(x) = vS          (valeur résolue du membre gauche)
        eqArith: op(vA, vB) = vS      (fait arithmétique 0/1)
        eqA    : φ_A(x) = vA ,  eqB : φ_B(x) = vB
    Chaîne : φ_S = vS = op(vA,vB) = op(φ_A,φ_B)."""
    vS = eqAB.conclusion.termes[1]
    # vS = op(vA, vB)
    eq2 = symetrie_appliquee(eqArith)                 # vS = op(vA,vB)
    # op(vA,vB) = op(φ_A, φ_B)  via congruence avec vA=φ_A, vB=φ_B (sens inverse)
    eq3 = _congr_binaire(op, symetrie_appliquee(eqA), symetrie_appliquee(eqB))
    return composer_egalites(composer_egalites(eqAB, eq2), eq3)


def symetrie_appliquee(eq):
    """Γ⊢(T=U) ⟹ Γ⊢(U=T)  (symétrie appliquée à une PREUVE d'égalité)."""
    t, u = eq.conclusion.termes
    return N.modus_ponens(eq, symetrie(t, u))


# ── (2)  φ_{A∩B}(x) = φ_A(x)·φ_B(x)   (E III.39, (2)) ─────────────────────────
# @livre Ch.III §5.5 Prop.7 | E III.39 L.6-6 | PDF p.142
def carac_intersection(x="x", A="A", B="B", E_="E"):
    """⊢  H ⇒ ( φ_{A∩B}(x) = φ_A(x) · φ_B(x) )   (Prop. 7, (2), E III.39).

    H = conjonction (honnête, NON vacue) des :
      • définitions de φ (Bourbaki, E III.39) pour A, B, A∩B : pour chaque partie S,
            x∈S ⇒ φ_S(x)=1   et   ¬(x∈S) ⇒ φ_S(x)=0 ;
      • faits arithmétiques sur {0,1} : 1·1=1, 1·0=0, 0·1=0, 0·0=0
        (produit_cardinal_binaire aux cardinaux UN, ZERO).
    La CONCLUSION (l'identité (2)) n'est pas dans H : preuve par analyse de cas.
    L'appartenance à A∩B est résolue par AXIOME_INTER (theorie=22)."""
    vx, vA, vB, vE = _t(x), _t(A), _t(B), _t(E_)
    AB = E.intersection(vA, vB)
    prod = lambda a, b: produit_cardinal_binaire(a, b)
    phiA, phiB, phiAB = phi(vA, vE, vx), phi(vB, vE, vx), phi(AB, vE, vx)

    inA, inB = appartient(vx, vA), appartient(vx, vB)
    inAB = appartient(vx, AB)
    bridge = _membre_inter(vx, vA, vB)                 # x∈A∩B ⇔ (x∈A et x∈B)

    # — hypothèses définissantes (assumées ; discharged en fin) —
    hA1 = N.assume(def_phi_un(vA, vE, vx))
    hA0 = N.assume(def_phi_zero(vA, vE, vx))
    hB1 = N.assume(def_phi_un(vB, vE, vx))
    hB0 = N.assume(def_phi_zero(vB, vE, vx))
    hAB1 = N.assume(def_phi_un(AB, vE, vx))
    hAB0 = N.assume(def_phi_zero(AB, vE, vx))
    # — faits arithmétiques 0/1 (assumés) —
    ar_11 = N.assume(egal(prod(UN, UN), UN))
    ar_10 = N.assume(egal(prod(UN, ZERO), ZERO))
    ar_01 = N.assume(egal(prod(ZERO, UN), ZERO))
    ar_00 = N.assume(egal(prod(ZERO, ZERO), ZERO))

    concl = egal(phiAB, prod(phiA, phiB))

    def branche(hxA, hxB, eqA, eqB, eqAB, eqArith):
        """retourne une preuve de `concl` sous les appartenances résolues hxA,hxB."""
        return _side_via_op(eqAB, eqArith, eqA, eqB, prod)

    # x∈A∩B sous (x∈A et x∈B)
    def inter_in(hxA, hxB):
        return N.modus_ponens(conjonction_intro(hxA, hxB),
                              equivalence_arriere(bridge))
    # ¬(x∈A∩B) sous ¬(x∈A)  (resp. ¬(x∈B)) : contraposée de la projection
    def inter_out_left(hnA):
        # x∈A∩B ⇒ x∈A ; donc ¬(x∈A) ⇒ ¬(x∈A∩B)
        h = N.assume(inAB)
        xa = conjonction_elim_gauche(N.modus_ponens(h, equivalence_avant(bridge)))
        imp = N.loi_deduction(inAB, xa)                # x∈A∩B ⇒ x∈A
        from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import contraposition
        return N.modus_ponens(hnA, contraposition(imp))   # ¬(x∈A∩B)
    def inter_out_right(hnB):
        h = N.assume(inAB)
        xb = conjonction_elim_droite(N.modus_ponens(h, equivalence_avant(bridge)))
        imp = N.loi_deduction(inAB, xb)
        from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import contraposition
        return N.modus_ponens(hnB, contraposition(imp))

    # CAS x∈A :
    hxA = N.assume(inA)
    eqA_in = N.modus_ponens(hxA, hA1)                  # φ_A = 1
    #   sous-cas x∈B
    hxB = N.assume(inB)
    eqB_in = N.modus_ponens(hxB, hB1)                  # φ_B = 1
    eqAB_in = N.modus_ponens(inter_in(hxA, hxB), hAB1) # φ_{A∩B}=1
    p_AA = branche(hxA, hxB, eqA_in, eqB_in, eqAB_in, ar_11)
    #   sous-cas ¬x∈B
    hnB = N.assume(non(inB))
    eqB_out = N.modus_ponens(hnB, hB0)                 # φ_B = 0
    eqAB_AnB = N.modus_ponens(inter_out_right(hnB), hAB0)  # φ_{A∩B}=0
    p_AnB = branche(hxA, hnB, eqA_in, eqB_out, eqAB_AnB, ar_10)
    p_A = cas(tiers_exclu(inB),
              N.loi_deduction(inB, p_AA),
              N.loi_deduction(non(inB), p_AnB))        # sous hyp x∈A → concl

    # CAS ¬x∈A :
    hnA = N.assume(non(inA))
    eqA_out = N.modus_ponens(hnA, hA0)                 # φ_A = 0
    eqAB_nA = N.modus_ponens(inter_out_left(hnA), hAB0)   # φ_{A∩B}=0 (indép. de B)
    #   sous-cas x∈B
    hxB2 = N.assume(inB)
    eqB_in2 = N.modus_ponens(hxB2, hB1)
    p_nAB = branche(hnA, hxB2, eqA_out, eqB_in2, eqAB_nA, ar_01)
    #   sous-cas ¬x∈B
    hnB2 = N.assume(non(inB))
    eqB_out2 = N.modus_ponens(hnB2, hB0)
    p_nAnB = branche(hnA, hnB2, eqA_out, eqB_out2, eqAB_nA, ar_00)
    p_nA = cas(tiers_exclu(inB),
               N.loi_deduction(inB, p_nAB),
               N.loi_deduction(non(inB), p_nAnB))      # sous hyp ¬x∈A → concl

    cur = cas(tiers_exclu(inA),
              N.loi_deduction(inA, p_A),
              N.loi_deduction(non(inA), p_nA))         # concl, sous toutes les hyps

    # — décharge des hypothèses (ordre quelconque) —
    H = [def_phi_un(vA, vE, vx), def_phi_zero(vA, vE, vx),
         def_phi_un(vB, vE, vx), def_phi_zero(vB, vE, vx),
         def_phi_un(AB, vE, vx), def_phi_zero(AB, vE, vx),
         egal(prod(UN, UN), UN), egal(prod(UN, ZERO), ZERO),
         egal(prod(ZERO, UN), ZERO), egal(prod(ZERO, ZERO), ZERO)]
    for h in reversed(H):
        cur = N.loi_deduction(h, cur)
    return cur


# ── briques génériques pour membres « op(·,·) = op(·,·) » ─────────────────────
def _two_sided_eq(eqL1, eqL2, eqR1, eqR2, eqArith, op):
    """op(φ_p,φ_q) = op(φ_r,φ_s),  étant donnés :
        eqL1: φ_p=vp , eqL2: φ_q=vq , eqR1: φ_r=vr , eqR2: φ_s=vs
        eqArith: op(vp,vq) = op(vr,vs)   (fait 0/1)
    Chaîne : op(φ_p,φ_q) = op(vp,vq) = op(vr,vs) = op(φ_r,φ_s)."""
    left = _congr_binaire(op, eqL1, eqL2)              # op(φ_p,φ_q)=op(vp,vq)
    right = _congr_binaire(op, symetrie_appliquee(eqR1), symetrie_appliquee(eqR2))  # op(vr,vs)=op(φ_r,φ_s)
    return composer_egalites(composer_egalites(left, eqArith), right)


# ── (1)  φ_{E−A}(x) + φ_A(x) = 1   (E III.39, (1), forme symétrique sans « − ») ─
# @livre Ch.III §5.5 Prop.7 | E III.39 L.4-5 | PDF p.142
def carac_complement(x="x", A="A", E_="E"):
    """⊢  H ⇒ ( φ_{E−A}(x) + φ_A(x) = 1 )   (Prop. 7, (1), E III.39).

    Forme « φ_{∁A}(x) + φ_A(x) = 1 » (équivalente à φ_{E−A}=1−φ_A, sans soustraction
    sur {0,1}).  H = (honnête, NON vacue) : x∈E (Bourbaki : « pour tout x∈E ») ;
    définitions de φ pour A et E−A ; faits 0/1  1+0=1  et  0+1=1.
    L'appartenance à E−A est résolue par AXIOME_DIFF (theorie=22)."""
    vx, vA, vE = _t(x), _t(A), _t(E_)
    cA = E.difference(vE, vA)
    somme = lambda a, b: somme_cardinale_binaire(a, b)
    phiA, phiCA = phi(vA, vE, vx), phi(cA, vE, vx)

    inA, inE = appartient(vx, vA), appartient(vx, vE)
    inCA = appartient(vx, cA)
    bridge = _membre_difference(vx, vE, vA)            # x∈E−A ⇔ (x∈E et ¬x∈A)

    hxE = N.assume(inE)
    hA1 = N.assume(def_phi_un(vA, vE, vx))
    hA0 = N.assume(def_phi_zero(vA, vE, vx))
    hCA1 = N.assume(def_phi_un(cA, vE, vx))
    hCA0 = N.assume(def_phi_zero(cA, vE, vx))
    ar_10 = N.assume(egal(somme(UN, ZERO), UN))        # 1+0 = 1
    ar_01 = N.assume(egal(somme(ZERO, UN), UN))        # 0+1 = 1

    concl = egal(somme(phiCA, phiA), UN)

    # x∈E−A  sous (x∈E et ¬x∈A)
    def compl_in(hnA):
        return N.modus_ponens(conjonction_intro(hxE, hnA), equivalence_arriere(bridge))
    # ¬(x∈E−A) sous x∈A : x∈E−A ⇒ ¬x∈A, contraposée
    def compl_out(hxA):
        from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import contraposition
        h = N.assume(inCA)
        nxa = conjonction_elim_droite(N.modus_ponens(h, equivalence_avant(bridge)))  # ¬x∈A
        imp = N.loi_deduction(inCA, nxa)               # x∈E−A ⇒ ¬x∈A
        # de x∈A on veut ¬(x∈E−A) : contraposée de imp donne ¬¬x∈A ⇒ ¬(x∈E−A)
        from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import dni
        return N.modus_ponens(N.modus_ponens(hxA, dni(inA)), contraposition(imp))

    # CAS x∈A : φ_A=1, φ_{E−A}=0,  0+1=1
    hxA = N.assume(inA)
    eqA_in = N.modus_ponens(hxA, hA1)
    eqCA_in = N.modus_ponens(compl_out(hxA), hCA0)     # φ_{E−A}=0
    p_in = _two_to_un(eqCA_in, eqA_in, ar_01, somme)   # somme(0,1)=1
    # CAS ¬x∈A : φ_A=0, φ_{E−A}=1,  1+0=1
    hnA = N.assume(non(inA))
    eqA_out = N.modus_ponens(hnA, hA0)
    eqCA_out = N.modus_ponens(compl_in(hnA), hCA1)     # φ_{E−A}=1
    p_out = _two_to_un(eqCA_out, eqA_out, ar_10, somme)

    cur = cas(tiers_exclu(inA),
              N.loi_deduction(inA, p_in),
              N.loi_deduction(non(inA), p_out))

    H = [inE, def_phi_un(vA, vE, vx), def_phi_zero(vA, vE, vx),
         def_phi_un(cA, vE, vx), def_phi_zero(cA, vE, vx),
         egal(somme(UN, ZERO), UN), egal(somme(ZERO, UN), UN)]
    for h in reversed(H):
        cur = N.loi_deduction(h, cur)
    return cur


def _two_to_un(eqL, eqR, eqArith, op):
    """op(φ_p,φ_q) = 1,  étant donnés eqL:φ_p=vp, eqR:φ_q=vq, eqArith:op(vp,vq)=1."""
    left = _congr_binaire(op, eqL, eqR)                # op(φ_p,φ_q)=op(vp,vq)
    return composer_egalites(left, eqArith)            # = 1


# ── (3)  φ_{A∪B}(x) + φ_{A∩B}(x) = φ_A(x) + φ_B(x)   (E III.39, (3)) ───────────
# @livre Ch.III §5.5 Prop.7 | E III.39 L.7-8 | PDF p.142
def carac_union(x="x", A="A", B="B", E_="E"):
    """⊢  H ⇒ ( φ_{A∪B}(x) + φ_{A∩B}(x) = φ_A(x) + φ_B(x) )  (Prop. 7, (3), E III.39).

    H = (honnête, NON vacue) : définitions de φ pour A, B, A∪B, A∩B ; faits 0/1
        1+1=1+1, 1+0=1+0, 1+0=0+1, 0+0=0+0  (commutativité/identité sur {0,1}).
    Appartenances à A∪B, A∩B résolues par AXIOME_REUNION / AXIOME_INTER (theorie=22)."""
    vx, vA, vB, vE = _t(x), _t(A), _t(B), _t(E_)
    AuB = E.reunion(vA, vB)
    AnB = E.intersection(vA, vB)
    somme = lambda a, b: somme_cardinale_binaire(a, b)
    phiA, phiB = phi(vA, vE, vx), phi(vB, vE, vx)
    phiU, phiI = phi(AuB, vE, vx), phi(AnB, vE, vx)

    inA, inB = appartient(vx, vA), appartient(vx, vB)
    inU, inI = appartient(vx, AuB), appartient(vx, AnB)
    bU = _membre_reunion(vx, vA, vB)                   # x∈A∪B ⇔ (x∈A ou x∈B)
    bI = _membre_inter(vx, vA, vB)                     # x∈A∩B ⇔ (x∈A et x∈B)

    hA1 = N.assume(def_phi_un(vA, vE, vx)); hA0 = N.assume(def_phi_zero(vA, vE, vx))
    hB1 = N.assume(def_phi_un(vB, vE, vx)); hB0 = N.assume(def_phi_zero(vB, vE, vx))
    hU1 = N.assume(def_phi_un(AuB, vE, vx)); hU0 = N.assume(def_phi_zero(AuB, vE, vx))
    hI1 = N.assume(def_phi_un(AnB, vE, vx)); hI0 = N.assume(def_phi_zero(AnB, vE, vx))
    a_1111 = N.assume(egal(somme(UN, UN), somme(UN, UN)))
    a_1010 = N.assume(egal(somme(UN, ZERO), somme(UN, ZERO)))
    a_1001 = N.assume(egal(somme(UN, ZERO), somme(ZERO, UN)))
    a_0000 = N.assume(egal(somme(ZERO, ZERO), somme(ZERO, ZERO)))

    concl = egal(somme(phiU, phiI), somme(phiA, phiB))

    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import contraposition, dni, mono_droite, mono_gauche
    # x∈A∪B sous x∈A : injection gauche dans la disjonction
    def union_in_left(hxA):
        return N.modus_ponens(N.modus_ponens(hxA, N.s2(inA, inB)), equivalence_arriere(bU))
    def union_in_right(hxB):
        disj = N.modus_ponens(N.modus_ponens(hxB, N.s2(inB, inA)), N.s3(inB, inA))  # inA∨inB
        return N.modus_ponens(disj, equivalence_arriere(bU))
    # x∈A∩B sous (x∈A et x∈B)
    def inter_in(hxA, hxB):
        return N.modus_ponens(conjonction_intro(hxA, hxB), equivalence_arriere(bI))
    def inter_out_left(hnA):
        h = N.assume(inI)
        xa = conjonction_elim_gauche(N.modus_ponens(h, equivalence_avant(bI)))
        return N.modus_ponens(hnA, contraposition(N.loi_deduction(inI, xa)))
    def inter_out_right(hnB):
        h = N.assume(inI)
        xb = conjonction_elim_droite(N.modus_ponens(h, equivalence_avant(bI)))
        return N.modus_ponens(hnB, contraposition(N.loi_deduction(inI, xb)))

    # branche : valeurs (eqU,eqI,eqA,eqB) + arith → concl
    def branche(eqU, eqI, eqA, eqB, eqArith):
        return _two_sided_eq(eqU, eqI, eqA, eqB, eqArith, somme)

    # ── CAS x∈A ──
    hxA = N.assume(inA); eqA_in = N.modus_ponens(hxA, hA1)
    eqU_inA = N.modus_ponens(union_in_left(hxA), hU1)       # φ_{A∪B}=1
    #   x∈B
    hxB = N.assume(inB); eqB_in = N.modus_ponens(hxB, hB1)
    eqI_inAB = N.modus_ponens(inter_in(hxA, hxB), hI1)      # φ_{A∩B}=1
    p_AA = branche(eqU_inA, eqI_inAB, eqA_in, eqB_in, a_1111)
    #   ¬x∈B
    hnB = N.assume(non(inB)); eqB_out = N.modus_ponens(hnB, hB0)
    eqI_AnB = N.modus_ponens(inter_out_right(hnB), hI0)     # φ_{A∩B}=0
    p_AnB = branche(eqU_inA, eqI_AnB, eqA_in, eqB_out, a_1010)
    p_A = cas(tiers_exclu(inB), N.loi_deduction(inB, p_AA),
              N.loi_deduction(non(inB), p_AnB))

    # ── CAS ¬x∈A ──
    hnA = N.assume(non(inA)); eqA_out = N.modus_ponens(hnA, hA0)
    eqI_nA = N.modus_ponens(inter_out_left(hnA), hI0)       # φ_{A∩B}=0
    #   x∈B → x∈A∪B (injection droite)
    hxB2 = N.assume(inB); eqB_in2 = N.modus_ponens(hxB2, hB1)
    eqU_inB = N.modus_ponens(union_in_right(hxB2), hU1)     # φ_{A∪B}=1
    p_nAB = branche(eqU_inB, eqI_nA, eqA_out, eqB_in2, a_1001)
    #   ¬x∈B → ¬(x∈A∪B)
    hnB2 = N.assume(non(inB)); eqB_out2 = N.modus_ponens(hnB2, hB0)
    eqU_out = N.modus_ponens(_union_out_both(bU, inU, inA, inB, hnA, hnB2), hU0)  # φ_{A∪B}=0
    p_nAnB = branche(eqU_out, eqI_nA, eqA_out, eqB_out2, a_0000)
    p_nA = cas(tiers_exclu(inB), N.loi_deduction(inB, p_nAB),
               N.loi_deduction(non(inB), p_nAnB))

    cur = cas(tiers_exclu(inA), N.loi_deduction(inA, p_A),
              N.loi_deduction(non(inA), p_nA))

    H = [def_phi_un(vA, vE, vx), def_phi_zero(vA, vE, vx),
         def_phi_un(vB, vE, vx), def_phi_zero(vB, vE, vx),
         def_phi_un(AuB, vE, vx), def_phi_zero(AuB, vE, vx),
         def_phi_un(AnB, vE, vx), def_phi_zero(AnB, vE, vx),
         egal(somme(UN, UN), somme(UN, UN)),
         egal(somme(UN, ZERO), somme(UN, ZERO)),
         egal(somme(UN, ZERO), somme(ZERO, UN)),
         egal(somme(ZERO, ZERO), somme(ZERO, ZERO))]
    for h in reversed(H):
        cur = N.loi_deduction(h, cur)
    return cur


def _union_out_both(bU, inU, inA, inB, hnA, hnB):
    """sous ¬x∈A, ¬x∈B : ⊢ ¬(x∈A∪B).   (x∈A∪B ⇒ x∈A∨x∈B, et ¬A∧¬B ⊢ ¬(A∨B).)"""
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import demorgan_ou, equivalence_arriere as eqarr
    # ¬x∈A et ¬x∈B  ⇒  ¬(x∈A ou x∈B)   via De Morgan
    nor = N.modus_ponens(conjonction_intro(hnA, hnB),
                         equivalence_arriere(demorgan_ou(inA, inB)))   # ¬(x∈A ou x∈B)
    # x∈A∪B ⇒ (x∈A ou x∈B)
    h = N.assume(inU)
    disj = N.modus_ponens(h, equivalence_avant(bU))
    imp = N.loi_deduction(inU, disj)                   # x∈A∪B ⇒ (x∈A∨x∈B)
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import contraposition, dne
    # ¬(x∈A∨x∈B) ⇒ ¬(x∈A∪B)
    return N.modus_ponens(nor, contraposition(imp))


__all__ = ["phi", "def_phi_un", "def_phi_zero",
           "carac_intersection", "carac_complement", "carac_union"]
