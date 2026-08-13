"""§III.3.2 — CANTOR–BERNSTEIN, suite : du point fixe φ(D)=D vers la bijection.

Énoncé (E.III.3.2, Cor. 2 du Théorème 1, lu VERBATIM dans ROADMAP_chap2-4.md) :
    « Deux ensembles tels que chacun soit équipotent à une partie de l'autre
      sont équipotents. »
    Implémentation (§III.3.2) : x ≤ y :⇔ (∃f)(f injection de x dans y), donc
        (a ≤ b  et  b ≤ a)  ⇒  Eq(a, b).

Le point fixe de Knaster–Tarski  φ(D)=D  est DÉJÀ clos (round 28,
ensembles_cantor_bernstein.phi_point_fixe), avec
    φ(S) = A ∖ g⟨ B ∖ f⟨S⟩ ⟩.

CE MODULE — additif, ne redéfinit RIEN — fournit les PALIERS suivants :

  • double_complement  : ⊢ (Y ⊂ A) ⇒ (A∖(A∖Y) = Y)              [loi du double
        complément, brique du PIVOT].
  • image_dans_codomaine_diff : de g injection B→A, ⊢ g⟨B∖f⟨D⟩⟩ ⊂ A
        (l'image d'une partie de B par g reste dans A).
  • pivot_AmoinsD (ÉTAPE 1, LE PIVOT) :
        de g injection B→A,  ⊢ A∖D = g⟨B∖f⟨D⟩⟩.
        (de φ(D)=D : D = A∖g⟨B∖f⟨D⟩⟩, donc A∖D = A∖(A∖g⟨B∖f⟨D⟩⟩) = g⟨B∖f⟨D⟩⟩
         par double_complement, sous g⟨B∖f⟨D⟩⟩ ⊂ A.)

C'est le PIVOT exigé par la mission : sur A∖D, tout élément est g(b) pour un
b∈B∖f⟨D⟩.  Les morceaux f|D et g⁻¹|(A∖D), leur recollement et la bijection
2-morceaux sont DOCUMENTÉS dans le rapport de mission (assemblage final reporté).

Tout sort du noyau (PROUVE == certifie) ; AUCUN axiome nouveau (on réutilise
AXIOME_DIFF + phi_point_fixe + est_injection_de + image_croissante).
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (var, egal, et, ou, non, impl, appartient,
                                       existe, pourtout, inclus, Terme)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege import syllogisme
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    projection_gauche, projection_droite, contraposition,
    equivalence_avant, equivalence_arriere, instancie, instanciation_en_x,
    inclusion_transitive, cas, tiers_exclu)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import symetrie, composer_egalites
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_1_graphes_correspondances.ensembles_correspondances import image_croissante
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_theoremes import egalite_par_extension
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.cantor_bernstein import ensembles_cantor_bernstein as CB
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import est_injection_de


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def _inst_diff(e, x, z):
    """⊢ (z ∈ E∖X) ⇔ (z∈E et ¬(z∈X))   (instance de AXIOME_DIFF)."""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_DIFF)
    return instancie(instancie(instancie(ax, e), x), z)


# ── BRIQUE : loi du double complément  A∖(A∖Y) = Y  (sous Y⊂A) ─────────────────

def double_complement(a="A", y="Y", z="z"):
    """⊢ (Y ⊂ A) ⇒ (A∖(A∖Y) = Y).

    Loi du double complément (valable seulement quand Y⊂A).  Membre à membre :
      z∈A∖(A∖Y) ⇔ (z∈A et ¬(z∈A∖Y))
                ⇔ (z∈A et ¬(z∈A et ¬(z∈Y))).
    Sous Y⊂A : ce dernier ⇔ z∈Y.
      ⇒ : z∈A et ¬(z∈A et ¬z∈Y).  De z∈A, si z∉Y alors (z∈A et ¬z∈Y) vraie,
          contradiction ; donc z∈Y.
      ⇐ : z∈Y ⇒ z∈A (Y⊂A) ; et ¬(z∈A et ¬z∈Y) car z∈Y réfute ¬z∈Y.
    """
    vA, vY, vz = _t(a), _t(y), _t(z)
    AmY = E.difference(vA, vY)               # A∖Y
    AmAmY = E.difference(vA, AmY)            # A∖(A∖Y)
    zA, zY = appartient(vz, vA), appartient(vz, vY)

    hsub = N.assume(inclus(vY, vA))                                   # Y⊂A
    zY_zA = N.modus_ponens(hsub, instanciation_en_x(impl(zY, zA), "z"))  # z∈Y ⇒ z∈A

    carAmAmY = _inst_diff(vA, AmY, vz)        # z∈A∖(A∖Y) ⇔ (z∈A et ¬(z∈A∖Y))
    carAmY = _inst_diff(vA, vY, vz)           # z∈A∖Y ⇔ (z∈A et ¬z∈Y)

    # ── ⇒ : z∈A∖(A∖Y) ⇒ z∈Y ───────────────────────────────────────────────────
    hL = N.assume(appartient(vz, AmAmY))
    pair = N.modus_ponens(hL, equivalence_avant(carAmAmY))   # z∈A et ¬(z∈A∖Y)
    zA_L = conjonction_elim_gauche(pair)                     # z∈A
    n_zAmY = conjonction_elim_droite(pair)                   # ¬(z∈A∖Y)
    # ¬(z∈A et ¬z∈Y)  (transport de ¬(z∈A∖Y) par carAmY)
    n_conj = N.modus_ponens(n_zAmY, contraposition(equivalence_arriere(carAmY)))  # ¬(z∈A et ¬z∈Y)
    # de z∈A et ¬(z∈A et ¬z∈Y) déduire z∈Y :
    #   suppose ¬z∈Y ; alors (z∈A et ¬z∈Y) vrai → contredit n_conj ; donc ¬¬z∈Y → z∈Y
    h_nzY = N.assume(non(zY))
    conj_true = conjonction_intro(zA_L, h_nzY)               # z∈A et ¬z∈Y   [hyp ¬z∈Y]
    # ex falso : conj_true vs n_conj  →  z∈Y
    contra = N.modus_ponens(conj_true, N.modus_ponens(n_conj, N.s2(non(et(zA, non(zY))), zY)))
    nnzY = N.loi_deduction(non(zY), contra)                  # ¬z∈Y ⇒ z∈Y
    # ¬z∈Y ⇒ z∈Y, et z∈Y ⇒ z∈Y (trivial) → tiers exclu pas requis : on utilise
    # (¬P⇒P)⇒P  via S3/contraposition.  Plus simple : ¬z∈Y ⇒ z∈Y donne, par
    # contraposée, ¬z∈Y ⇒ ¬¬z∈Y... on conclut z∈Y par double négation déchargée :
    zY_L = N.modus_ponens(nnzY, _absorption(zY))             # z∈Y
    fwd = N.loi_deduction(appartient(vz, AmAmY), zY_L)       # z∈A∖(A∖Y) ⇒ z∈Y

    # ── ⇐ : z∈Y ⇒ z∈A∖(A∖Y) ───────────────────────────────────────────────────
    hR = N.assume(zY)
    zA_R = N.modus_ponens(hR, zY_zA)                         # z∈A
    # ¬(z∈A et ¬z∈Y)  : de z∈Y, ¬z∈Y est faux → la conjonction est fausse
    hconj = N.assume(et(zA, non(zY)))
    contra2 = N.modus_ponens(hR, N.modus_ponens(conjonction_elim_droite(hconj),
                                                N.s2(non(zY), non(et(zA, non(zY))))))
    n_conj_R = N.loi_deduction(et(zA, non(zY)), contra2)     # (z∈A et ¬z∈Y) ⇒ ¬(...)
    n_conj_R = N.modus_ponens(n_conj_R, _absorption_neg(et(zA, non(zY))))  # ¬(z∈A et ¬z∈Y)
    # ¬(z∈A∖Y)
    n_zAmY_R = N.modus_ponens(n_conj_R, contraposition(equivalence_avant(carAmY)))  # ¬(z∈A∖Y)
    pair_R = conjonction_intro(zA_R, n_zAmY_R)               # z∈A et ¬(z∈A∖Y)
    zAmAmY = N.modus_ponens(pair_R, equivalence_arriere(carAmAmY))  # z∈A∖(A∖Y)
    bwd = N.loi_deduction(zY, zAmAmY)                        # z∈Y ⇒ z∈A∖(A∖Y)

    eqv = conjonction_intro(fwd, bwd)                        # z∈A∖(A∖Y) ⇔ z∈Y
    incl_LR = N.generalisation("z", equivalence_avant(eqv))  # A∖(A∖Y) ⊂ Y
    incl_RL = N.generalisation("z", equivalence_arriere(eqv))  # Y ⊂ A∖(A∖Y)
    ext = N.axiome(E.theorie_ensembles(), E.A1)
    ext = instancie(instancie(ext, AmAmY), vY)              # (A∖(A∖Y)⊂Y et Y⊂A∖(A∖Y)) ⇒ =
    eqset = N.modus_ponens(conjonction_intro(incl_LR, incl_RL), ext)  # A∖(A∖Y)=Y
    return N.loi_deduction(inclus(vY, vA), eqset)           # (Y⊂A) ⇒ (A∖(A∖Y)=Y)


def _absorption(p):
    """⊢ (¬P ⇒ P) ⇒ P.   (loi de Clavius / consequentia mirabilis, dérivée S1-S4.)

    Voie sûre : par cas sur le tiers exclu P∨¬P (abrégé) — sous P, P ; sous
    ¬P, l'hypothèse ¬P⇒P fournit P."""
    te = tiers_exclu(p)                       # ⊢ P ∨ ¬P
    h = N.assume(impl(non(p), p))             # ¬P ⇒ P
    br_P = N.loi_deduction(p, N.assume(p))    # P ⇒ P
    br_nP = N.loi_deduction(non(p), N.modus_ponens(N.assume(non(p)), h))  # ¬P ⇒ P
    conc = cas(te, br_P, br_nP)               # P   [hyp ¬P⇒P]
    return N.loi_deduction(impl(non(p), p), conc)


def _absorption_neg(p):
    """⊢ (P ⇒ ¬P) ⇒ ¬P.   (dual : si P entraîne sa négation, P est faux.)"""
    te = tiers_exclu(p)                       # ⊢ P ∨ ¬P
    h = N.assume(impl(p, non(p)))             # P ⇒ ¬P
    # P ⇒ ¬P  : sous P, on a ¬P, contradiction → ¬P (ex falso) ; sous ¬P, ¬P.
    hP = N.assume(p)
    nP_fromP = N.modus_ponens(hP, h)          # ¬P  [hyp P]
    # ex falso : P et ¬P ⊢ ¬P (trivial : on a déjà ¬P)
    br_P = N.loi_deduction(p, nP_fromP)       # P ⇒ ¬P
    br_nP = N.loi_deduction(non(p), N.assume(non(p)))  # ¬P ⇒ ¬P
    conc = cas(te, br_P, br_nP)               # ¬P   [hyp P⇒¬P]
    return N.loi_deduction(impl(p, non(p)), conc)


# ── image d'une partie de B reste dans A (g : B→A injection) ──────────────────

def image_dans_codomaine_diff(a="A", b="B", f="f", g="g"):
    """{g injection B→A}  ⊢  g⟨B∖f⟨D⟩⟩ ⊂ A.

    B∖f⟨D⟩ ⊂ B (différence ⊂ surensemble), donc g⟨B∖f⟨D⟩⟩ ⊂ g⟨B⟩ (image
    croissante) ⊂ A (4ᵉ conjoint de est_injection_de : image(g,B)⊂A)."""
    vA, vB, vf, vg = _t(a), _t(b), _t(f), _t(g)
    dterm = CB.D(vA, vB, vf, vg)
    BfD = E.difference(vB, E.image(vf, dterm))     # B∖f⟨D⟩
    gBfD = E.image(vg, BfD)                         # g⟨B∖f⟨D⟩⟩
    gB = E.image(vg, vB)                            # g⟨B⟩

    # B∖f⟨D⟩ ⊂ B
    sub_BfD_B = _diff_inclus(vB, E.image(vf, dterm))   # B∖f⟨D⟩ ⊂ B
    # g⟨B∖f⟨D⟩⟩ ⊂ g⟨B⟩
    gmono = _img_croiss(vg, BfD, vB)               # (B∖f⟨D⟩ ⊂ B) ⇒ (g⟨B∖f⟨D⟩⟩ ⊂ g⟨B⟩)
    sub_gBfD_gB = N.modus_ponens(sub_BfD_B, gmono)
    # g⟨B⟩ ⊂ A   (4ᵉ conjoint de g injection)
    hinj = N.assume(est_injection_de(vg, vB, vA))
    sub_gB_A = conjonction_elim_droite(hinj)       # image(g,B) ⊂ A
    # transitivité
    trans = inclusion_transitive_terme(gBfD, gB, vA)
    return N.modus_ponens(conjonction_intro(sub_gBfD_gB, sub_gB_A), trans)


def _diff_inclus(e, x, z="z"):
    """⊢ (E∖X) ⊂ E.   (la différence est incluse dans le minuende.)"""
    vE, vX, vz = _t(e), _t(x), var(z)
    car = _inst_diff(vE, vX, vz)                   # z∈E∖X ⇔ (z∈E et ¬z∈X)
    z_imp = syllogisme(equivalence_avant(car),
                       projection_gauche(appartient(vz, vE), non(appartient(vz, vX))))
    return N.generalisation(z, z_imp)              # (E∖X) ⊂ E


def _img_croiss(g, x, y):
    """⊢ (X ⊂ Y) ⇒ (g⟨X⟩ ⊂ g⟨Y⟩)  pour des TERMES g,x,y."""
    th = image_croissante("G", "X", "Y")
    th = instancie(N.generalisation("G", th), g)
    th = instancie(N.generalisation("X", th), x)
    th = instancie(N.generalisation("Y", th), y)
    return th


def inclusion_transitive_terme(a, b, c):
    """⊢ ((a⊂b) et (b⊂c)) ⇒ (a⊂c)  pour des TERMES a,b,c."""
    th = inclusion_transitive("a", "b", "c")
    for nm, tm in (("a", a), ("b", b), ("c", c)):
        th = instancie(N.generalisation(nm, th), tm)
    return th


# ── ÉTAPE 1 — LE PIVOT :  A∖D = g⟨B∖f⟨D⟩⟩ ─────────────────────────────────────

# @livre Ch.III §3.2 Cor.2 | E III.25 L.13-15 | PDF p.128
#   (Cantor–Bernstein, démonstration machine : pivot A∖D = g⟨B∖f⟨D⟩⟩ ;
#    l'énoncé du livre est aux lignes citées.)
def pivot_AmoinsD(a="A", b="B", f="f", g="g"):
    """{g injection B→A}  ⊢  A∖D = g⟨B∖f⟨D⟩⟩.    (ÉTAPE 1, LE PIVOT.)

    De phi_point_fixe : φ(D) = D, i.e.  A∖g⟨B∖f⟨D⟩⟩ = D.  Par symétrie
    D = A∖g⟨B∖f⟨D⟩⟩, d'où, par congruence,  A∖D = A∖(A∖g⟨B∖f⟨D⟩⟩).  Comme
    g⟨B∖f⟨D⟩⟩ ⊂ A (image_dans_codomaine_diff), double_complement donne
    A∖(A∖g⟨B∖f⟨D⟩⟩) = g⟨B∖f⟨D⟩⟩.  Transitivité ⇒ A∖D = g⟨B∖f⟨D⟩⟩.

    Sur A∖D, tout élément est donc g(b) pour un b ∈ B∖f⟨D⟩ : c'est ce qui
    permet de recoller g⁻¹ sur A∖D dans la bijection finale."""
    from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import congruence_terme
    vA, vB, vf, vg = _t(a), _t(b), _t(f), _t(g)
    dterm = CB.D(vA, vB, vf, vg)
    gBfD = E.image(vg, E.difference(vB, E.image(vf, dterm)))   # g⟨B∖f⟨D⟩⟩
    phiD = CB.phi(vA, vB, vf, vg, dterm)                       # = A∖g⟨B∖f⟨D⟩⟩  (def φ)

    # 1) D = φ(D) = A∖g⟨B∖f⟨D⟩⟩   (symétrie de phi_point_fixe ; phiD == A∖gBfD)
    pf = CB.phi_point_fixe(a, b, f, g)                         # φ(D)=D
    D_eq_phiD = N.modus_ponens(pf, symetrie(phiD, dterm))      # D = φ(D) = A∖gBfD

    # 2) A∖D = A∖(A∖gBfD)   (congruence du terme A∖• le long de D = A∖gBfD)
    AmD = E.difference(vA, dterm)
    cong = N.modus_ponens(D_eq_phiD,
                          congruence_terme(dterm, phiD, E.difference(vA, var("w"))))
    #   cong : A∖D = A∖(A∖gBfD)         (car phiD = difference(A, gBfD))

    # 3) A∖(A∖gBfD) = gBfD   (double_complement sous gBfD ⊂ A)
    sub = image_dans_codomaine_diff(a, b, f, g)               # {g inj} ⊢ gBfD ⊂ A
    dc = _double_complement_terme(vA, gBfD)                   # (gBfD⊂A) ⇒ (A∖(A∖gBfD)=gBfD)
    dc_app = N.modus_ponens(sub, dc)                         # A∖(A∖gBfD) = gBfD   [g inj]

    # 4) A∖D = gBfD   (transitivité des égalités)
    return composer_egalites(cong, dc_app)                   # {g inj} ⊢ A∖D = g⟨B∖f⟨D⟩⟩


def _double_complement_terme(a, y):
    """⊢ (Y⊂A) ⇒ (A∖(A∖Y)=Y)  pour des TERMES a, y."""
    th = double_complement("A", "Y", "z")
    th = instancie(N.generalisation("A", th), a)
    th = instancie(N.generalisation("Y", th), y)
    return th


# ── PARTITION : X ⊔ (A∖X) = A  (disjonction + recouvrement) ────────────────────
# Faits ensemblistes GÉNÉRAUX servant l'assemblage de la bijection 2-morceaux :
#   • avec X := D, A := A   →  D ∩ (A∖D) = ∅   (domaines DISJOINTS du recollement)
#   • avec X := f⟨D⟩, A := B (sous f⟨D⟩⊂B) → f⟨D⟩ ∪ (B∖f⟨D⟩) = B   (image = B)
#   • avec X := f⟨D⟩, A := B → f⟨D⟩ ∩ (B∖f⟨D⟩) = ∅   (images des 2 morceaux disjointes)

def _inst_inter(a, b, z):
    """⊢ (z ∈ A∩B) ⇔ (z∈A et z∈B)   (instance de AXIOME_INTER)."""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_INTER)
    return instancie(instancie(instancie(ax, a), b), z)


def _inst_reunion(a, b, z):
    """⊢ (z ∈ A∪B) ⇔ (z∈A ou z∈B)   (instance de AXIOME_REUNION)."""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_REUNION)
    return instancie(instancie(instancie(ax, a), b), z)


def partie_disjoint_complement(a="A", x="X", z="z"):
    """⊢ X ∩ (A∖X) = ∅.    (une partie et son complément sont DISJOINTS.)

    z∈X∩(A∖X) ⇔ (z∈X et (z∈A et ¬z∈X)) → z∈X et ¬z∈X → faux ; donc l'intersection
    n'a aucun élément, i.e. = ∅.  (Avec X:=D, A:=A : D∩(A∖D)=∅, disjonction des
    domaines du recollement f|D ∪ g⁻¹|(A∖D).)"""
    vA, vX, vz = _t(a), _t(x), _t(z)
    AmX = E.difference(vA, vX)               # A∖X
    inter = E.intersection(vX, AmX)          # X∩(A∖X)
    carI = _inst_inter(vX, AmX, vz)          # z∈X∩(A∖X) ⇔ (z∈X et z∈A∖X)
    carD = _inst_diff(vA, vX, vz)            # z∈A∖X ⇔ (z∈A et ¬z∈X)
    zVide = N.axiome(E.theorie_ensembles(), E.AXIOME_VIDE)   # (∀z)¬(z∈∅)
    n_zVide = instancie(zVide, vz)           # ¬(z∈∅)

    # ⇒ : z∈X∩(A∖X) ⇒ z∈∅  (ex falso : z∈X et ¬z∈X)
    hI = N.assume(appartient(vz, inter))
    pair = N.modus_ponens(hI, equivalence_avant(carI))      # z∈X et z∈A∖X
    zX = conjonction_elim_gauche(pair)                      # z∈X
    n_zX = conjonction_elim_droite(N.modus_ponens(conjonction_elim_droite(pair),
                                                  equivalence_avant(carD)))  # ¬z∈X
    # ex falso → z∈∅ (n'importe quoi)
    zVideC = N.modus_ponens(zX, N.modus_ponens(n_zX, N.s2(non(appartient(vz, vX)),
                                                         appartient(vz, E.VIDE))))
    fwd = N.loi_deduction(appartient(vz, inter), zVideC)    # z∈inter ⇒ z∈∅
    incl_LR = N.generalisation(z, fwd)                      # inter ⊂ ∅
    # ⇐ : z∈∅ ⇒ z∈inter  (ex falso depuis ¬(z∈∅))
    hV = N.assume(appartient(vz, E.VIDE))
    zInterC = N.modus_ponens(hV, N.modus_ponens(n_zVide,
                                                N.s2(non(appartient(vz, E.VIDE)),
                                                     appartient(vz, inter))))
    bwd = N.loi_deduction(appartient(vz, E.VIDE), zInterC)  # z∈∅ ⇒ z∈inter
    incl_RL = N.generalisation(z, bwd)                      # ∅ ⊂ inter
    ext = instancie(instancie(N.axiome(E.theorie_ensembles(), E.A1), inter), E.VIDE)
    return N.modus_ponens(conjonction_intro(incl_LR, incl_RL), ext)   # X∩(A∖X)=∅


def partie_reunion_complement(a="A", x="X", z="z"):
    """⊢ (X ⊂ A) ⇒ (X ∪ (A∖X) = A).    (une partie et son complément RECOUVRENT A.)

    ⇒ : z∈X∪(A∖X) ⇒ z∈A — sous z∈X par X⊂A, sous z∈A∖X directement (1ʳᵉ comp.).
    ⇐ : z∈A ⇒ par tiers exclu z∈X ou ¬z∈X ; le 1ᵉʳ cas place z dans X (gauche), le
        2ᵈ dans A∖X (z∈A et ¬z∈X, droite).
    (Avec X:=f⟨D⟩, A:=B sous f⟨D⟩⊂B : f⟨D⟩ ∪ (B∖f⟨D⟩) = B → image de la
    bijection 2-morceaux = B.)"""
    vA, vX, vz = _t(a), _t(x), _t(z)
    AmX = E.difference(vA, vX)               # A∖X
    reun = E.reunion(vX, AmX)                # X∪(A∖X)
    zA, zX = appartient(vz, vA), appartient(vz, vX)
    carR = _inst_reunion(vX, AmX, vz)        # z∈X∪(A∖X) ⇔ (z∈X ou z∈A∖X)
    carD = _inst_diff(vA, vX, vz)            # z∈A∖X ⇔ (z∈A et ¬z∈X)

    hsub = N.assume(inclus(vX, vA))                                # X⊂A
    zX_zA = N.modus_ponens(hsub, instanciation_en_x(impl(zX, zA), "z"))  # z∈X ⇒ z∈A

    # ⇒ : z∈X∪(A∖X) ⇒ z∈A
    hR = N.assume(appartient(vz, reun))
    disj = N.modus_ponens(hR, equivalence_avant(carR))            # z∈X ou z∈A∖X
    br_X = zX_zA                                                  # z∈X ⇒ z∈A
    br_AmX = syllogisme(equivalence_avant(carD),
                        projection_gauche(zA, non(zX)))           # z∈A∖X ⇒ z∈A
    zA_fromR = cas(disj, br_X, br_AmX)                            # z∈A
    fwd = N.loi_deduction(appartient(vz, reun), zA_fromR)         # z∈reun ⇒ z∈A
    incl_LR = N.generalisation(z, fwd)                            # reun ⊂ A   [X⊂A]

    # ⇐ : z∈A ⇒ z∈X∪(A∖X)
    hA = N.assume(zA)
    te = tiers_exclu(zX)                                          # z∈X ou ¬z∈X
    # z∈X ⇒ reun  (gauche)
    in_left = N.modus_ponens(N.assume(zX), N.s2(zX, appartient(vz, AmX)))   # z∈X ⇒ (z∈X ou z∈A∖X)
    br_zX = N.loi_deduction(zX, N.modus_ponens(in_left, equivalence_arriere(carR)))  # z∈X ⇒ reun
    # ¬z∈X ⇒ reun  (droite : z∈A et ¬z∈X → z∈A∖X)
    h_nzX = N.assume(non(zX))
    zAmX = N.modus_ponens(conjonction_intro(hA, h_nzX), equivalence_arriere(carD))   # z∈A∖X
    # z∈A∖X ⇒ (z∈A∖X ∨ z∈X) ⇒ (z∈X ∨ z∈A∖X)
    in_right = N.modus_ponens(zAmX, syllogisme(N.s2(appartient(vz, AmX), zX),
                                               N.s3(appartient(vz, AmX), zX)))   # z∈X ou z∈A∖X
    br_nzX = N.loi_deduction(non(zX),
                             N.modus_ponens(in_right, equivalence_arriere(carR)))    # ¬z∈X ⇒ reun
    zReun = cas(te, br_zX, br_nzX)                                # z∈reun   [hyp z∈A, X⊂A]
    bwd = N.loi_deduction(zA, zReun)                             # z∈A ⇒ z∈reun
    incl_RL = N.generalisation(z, bwd)                          # A ⊂ reun

    ext = instancie(instancie(N.axiome(E.theorie_ensembles(), E.A1), reun), vA)
    eqset = N.modus_ponens(conjonction_intro(incl_LR, incl_RL), ext)   # reun = A
    return N.loi_deduction(inclus(vX, vA), eqset)               # (X⊂A) ⇒ (X∪(A∖X)=A)


# ── ÉTAPE 2 (i) — f|D est une fonction injective sur D ────────────────────────
# Briques GÉNÉRALES sur la restriction (morceau « f|D » de la bijection finale).

def sous_graphe_fonctionnel(f="F", g="G"):
    """⊢ (est_fonctionnel(F) et G⊂F) ⇒ est_fonctionnel(G).

    Une PARTIE d'un graphe fonctionnel est fonctionnelle : si (u,v),(u,z)∈G⊂F
    alors (u,v),(u,z)∈F, et la fonctionnalité de F donne v=z.  (Avec G:=f|X⊂F :
    toute restriction d'une fonction est une fonction.)"""
    vF, vG = _t(f), _t(g)
    vu, vv, vz = var("u"), var("v"), var("z")
    cplv, cplz = E.couple(vu, vv), E.couple(vu, vz)
    conj = et(E.est_fonctionnel(vF), inclus(vG, vF))            # func F et G⊂F
    hyp_glob = N.assume(conj)
    hfunc = conjonction_elim_gauche(hyp_glob)                   # func F
    hsub = conjonction_elim_droite(hyp_glob)                    # G⊂F = (∀z)(z∈G⇒z∈F)
    sub_v = instancie(hsub, cplv)                               # (u,v)∈G ⇒ (u,v)∈F
    sub_z = instancie(hsub, cplz)                               # (u,z)∈G ⇒ (u,z)∈F
    fF = instancie(instancie(instancie(hfunc, vu), vv), vz)     # ((u,v)∈F et (u,z)∈F)⇒v=z
    hyp = N.assume(et(appartient(cplv, vG), appartient(cplz, vG)))
    vF_in = N.modus_ponens(conjonction_elim_gauche(hyp), sub_v)  # (u,v)∈F
    zF_in = N.modus_ponens(conjonction_elim_droite(hyp), sub_z)  # (u,z)∈F
    v_eq_z = N.modus_ponens(conjonction_intro(vF_in, zF_in), fF)  # v=z
    inner = N.loi_deduction(et(appartient(cplv, vG), appartient(cplz, vG)), v_eq_z)
    gen = N.generalisation("u", N.generalisation("v", N.generalisation("z", inner)))  # func G
    return N.loi_deduction(conj, gen)                          # (func F et G⊂F) ⇒ func G


def restriction_fonctionnelle(f="F", x="X"):
    """⊢ est_fonctionnel(F) ⇒ est_fonctionnel(f|X).   (toute restriction d'une
    fonction est une fonction : f|X ⊂ F (restriction_incluse) + sous_graphe.)"""
    from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_5_restrictions_prolongements.ensembles_restrictions import restriction_incluse
    vF, vX = _t(f), _t(x)
    fX = E.restriction(vF, vX)
    sgf = sous_graphe_fonctionnel(vF, fX)                       # (func F et f|X⊂F) ⇒ func f|X
    fnom = f if isinstance(f, str) else f.nom
    xnom = x if isinstance(x, str) else x.nom
    inc = restriction_incluse(fnom, xnom)                      # f|X ⊂ F
    hfunc = N.assume(E.est_fonctionnel(vF))
    conc = N.modus_ponens(conjonction_intro(hfunc, inc), sgf)   # func f|X   [func F]
    return N.loi_deduction(E.est_fonctionnel(vF), conc)


__all__ = ["double_complement", "image_dans_codomaine_diff", "pivot_AmoinsD",
           "partie_disjoint_complement", "partie_reunion_complement",
           "sous_graphe_fonctionnel", "restriction_fonctionnelle",
           "inclusion_transitive_terme"]
