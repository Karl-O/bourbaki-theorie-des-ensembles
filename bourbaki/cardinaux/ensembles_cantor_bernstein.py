"""§III.3.2 — Vers le THÉORÈME DE CANTOR–BERNSTEIN (Corollaire 2 du Théorème 1).

Énoncé (E.III.3.2, Cor. 2, lu VERBATIM dans ROADMAP_chap2-4.md) :
    « Deux ensembles tels que chacun soit équipotent à une partie de l'autre
      sont équipotents. »
    i.e.  (Card X ≤ Card Y  et  Card Y ≤ Card X)  ⇒  Eq(X, Y).

CIBLE DE CE ROUND = le CŒUR de la preuve : le POINT FIXE de Knaster–Tarski,
qui ÉVITE la récurrence (C61 absente).

Soient f : A → B et g : B → A deux injections.  On pose l'opérateur sur 𝔓(A)
    φ(S) := A ∖ g⟨B ∖ f⟨S⟩⟩ = difference(A, image(g, difference(B, image(f, S)))).
φ est croissant (φ_monotone).  Par Knaster–Tarski, l'intersection D des parties
φ-closes (φ(S) ⊂ S) est un POINT FIXE : φ(D) = D.  Sur D, f est une bijection
A→f⟨D⟩ ; sur A∖D, g⁻¹ recolle ; la bijection finale = round suivant.

PALIERS (chacun sauvé + testé en isolé) :
  (1) phi(A,B,f,g,S) terme + phi_membre : z∈φ(S) ⇔ (z∈A et ¬(z∈g⟨B∖f⟨S⟩⟩))
  (2) phi_monotone : S⊂S′ ⇒ φ(S)⊂φ(S′)            ← lemme CLÉ, le plus réutilisable
  (3) D + axiome caractérisant  (intersection des parties φ-closes)
  (4) phi_point_fixe : φ(D)=D                       ← Knaster–Tarski

Outillage réutilisé : image_croissante (Prop.2, E.II.40, monotonie de l'image
directe), AXIOME_DIFF (différence), inclus, inclusion_transitive.
RIEN n'est postulé hors un axiome de DÉFINITION fidèle (l'intersection des parties
φ-closes est collectivisante par S8 + A1, comme produit/image/diagonale).
"""
from __future__ import annotations

from bourbaki.logique.formule import (var, egal, et, ou, non, impl, appartient,
                                       existe, pourtout, inclus, equiv)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.logique.tactiques.tactiques_abrege import syllogisme
from bourbaki.logique.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    projection_gauche, projection_droite, contraposition,
    equivalence_avant, equivalence_arriere, instancie, instanciation_en_x,
    inclusion_transitive)
from bourbaki.ensembles.base.ensembles_correspondances import image_croissante


# ── PALIER 1 : l'opérateur φ et sa caractérisation ────────────────────────────

def phi(a, b, f, g, s):
    """φ(S) := A ∖ g⟨ B ∖ f⟨S⟩ ⟩   (opérateur de Knaster–Tarski sur 𝔓(A)).

    Terme construit à partir des primitives difference/image — AUCUN axiome
    nouveau (φ n'est qu'une combinaison de termes déjà axiomatisés)."""
    return E.difference(a, E.image(g, E.difference(b, E.image(f, s))))


def _inst_diff(e, x, z):
    """⊢ (z ∈ E∖X) ⇔ (z∈E et ¬(z∈X))   (instance de AXIOME_DIFF)."""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_DIFF)
    return instancie(instancie(instancie(ax, e), x), z)


def phi_membre(a="A", b="B", f="f", g="g", s="S", z="z"):
    """⊢ (z ∈ φ(S)) ⇔ (z∈A et ¬(z ∈ g⟨B∖f⟨S⟩⟩)).

    Caractérisation membre de φ(S) (PALIER 1), simple instance de AXIOME_DIFF
    sur E=A, X=g⟨B∖f⟨S⟩⟩."""
    vA, vS, vz = var(a), var(s), var(z)
    gbfs = E.image(var(g), E.difference(var(b), E.image(var(f), vS)))   # g⟨B∖f⟨S⟩⟩
    return _inst_diff(vA, gbfs, vz)        # z∈A∖g⟨…⟩ ⇔ (z∈A et ¬(z∈g⟨…⟩))


# ── différence ANTI-monotone (brique de φ_monotone) ───────────────────────────

def difference_anti_monotone(e="E", x="X", y="Y", z="z"):
    """⊢ (X ⊂ Y) ⇒ ((E∖Y) ⊂ (E∖X)).

    La différence E∖· est DÉCROISSANTE : plus on retranche, plus le résultat
    rapetisse.  Brique anti-monotone du sandwich de φ_monotone."""
    vE, vX, vY, vz = var(e), var(x), var(y), var(z)
    zE = appartient(vz, vE)
    zX, zY = appartient(vz, vX), appartient(vz, vY)
    h = N.assume(inclus(vX, vY))
    zX_zY = instanciation_en_x(impl(zX, zY), z)        # (∀z)(z∈X⇒z∈Y) ⇒ (z∈X⇒z∈Y)
    zX_zY = N.modus_ponens(h, zX_zY)                   # z∈X ⇒ z∈Y
    nzY_nzX = contraposition(zX_zY)                    # ¬(z∈Y) ⇒ ¬(z∈X)
    # (z∈E et ¬(z∈Y)) ⇒ (z∈E et ¬(z∈X))
    ante = et(zE, non(zY))
    ha = N.assume(ante)
    conc = conjonction_intro(conjonction_elim_gauche(ha),
                             N.modus_ponens(conjonction_elim_droite(ha), nzY_nzX))
    inner = N.loi_deduction(ante, conc)               # (z∈E et ¬zY) ⇒ (z∈E et ¬zX)
    z_imp = syllogisme(equivalence_avant(_inst_diff(vE, vY, vz)),
                       syllogisme(inner, equivalence_arriere(_inst_diff(vE, vX, vz))))
    #   z∈E∖Y ⇒ (zE et ¬zY) ⇒ (zE et ¬zX) ⇒ z∈E∖X
    return N.loi_deduction(inclus(vX, vY), N.generalisation(z, z_imp))


# ── PALIER 2 : φ est croissant (lemme CLÉ) ────────────────────────────────────

def phi_monotone(a="A", b="B", f="f", g="g", s="S", sp="Sp"):
    """⊢ (S ⊂ S′) ⇒ (φ(S) ⊂ φ(S′)).   (PALIER 2 — croissance de φ, lemme CLÉ.)

    Sandwich :   S⊂S′
      → f⟨S⟩ ⊂ f⟨S′⟩            (image croissante, Prop.2)
      → B∖f⟨S′⟩ ⊂ B∖f⟨S⟩        (différence anti-monotone)
      → g⟨B∖f⟨S′⟩⟩ ⊂ g⟨B∖f⟨S⟩⟩  (image croissante)
      → A∖g⟨B∖f⟨S⟩⟩ ⊂ A∖g⟨B∖f⟨S′⟩⟩ = φ(S)⊂φ(S′)  (différence anti-monotone)
    """
    vA, vB, vf, vg = var(a), var(b), var(f), var(g)
    vS, vSp = var(s), var(sp)
    fS, fSp = E.image(vf, vS), E.image(vf, vSp)              # f⟨S⟩, f⟨S′⟩
    BfS, BfSp = E.difference(vB, fS), E.difference(vB, fSp)  # B∖f⟨S⟩, B∖f⟨S′⟩
    gBfS, gBfSp = E.image(vg, BfS), E.image(vg, BfSp)        # g⟨B∖f⟨S⟩⟩, g⟨B∖f⟨S′⟩⟩

    h = N.assume(inclus(vS, vSp))                            # S ⊂ S′
    # 1) f⟨S⟩ ⊂ f⟨S′⟩
    step1 = N.modus_ponens(h, image_croissante(f, s, sp))    # image_croissante(f) : S⊂S′ ⇒ f⟨S⟩⊂f⟨S′⟩
    # 2) B∖f⟨S′⟩ ⊂ B∖f⟨S⟩       (anti-mono avec X=f⟨S⟩, Y=f⟨S′⟩)
    step2 = N.modus_ponens(step1, _diff_anti(vB, fS, fSp))
    # 3) g⟨B∖f⟨S′⟩⟩ ⊂ g⟨B∖f⟨S⟩⟩  (image croissante de g, sur l'inclusion step2)
    step3 = N.modus_ponens(step2, _img_croiss(vg, BfSp, BfS))
    # 4) A∖g⟨B∖f⟨S⟩⟩ ⊂ A∖g⟨B∖f⟨S′⟩⟩   (anti-mono avec X=gBfSp, Y=gBfS)
    step4 = N.modus_ponens(step3, _diff_anti(vA, gBfSp, gBfS))
    # step4 conclusion = φ(S) ⊂ φ(S′)
    return N.loi_deduction(inclus(vS, vSp), step4)


# ── helpers TERME (monotonies appliquées à des termes composés) ───────────────

def _diff_anti(e, x, y):
    """⊢ (X ⊂ Y) ⇒ ((E∖Y) ⊂ (E∖X))  pour des TERMES e,x,y quelconques.

    On prouve la version à lettres « E »,« X »,« Y » (≠ z liant interne) puis on
    INSTANCIE aux termes — robuste grâce au fix α (binders exotiques @N)."""
    th = difference_anti_monotone("E", "X", "Y", "z")        # ⊢ (X⊂Y)⇒((E∖Y)⊂(E∖X))
    th = instancie(N.generalisation("E", th), e)
    th = instancie(N.generalisation("X", th), x)
    th = instancie(N.generalisation("Y", th), y)
    return th


def _img_croiss(g, x, y):
    """⊢ (X ⊂ Y) ⇒ (g⟨X⟩ ⊂ g⟨Y⟩)  pour des TERMES g,x,y quelconques."""
    th = image_croissante("G", "X", "Y")                     # ⊢ (X⊂Y)⇒(G⟨X⟩⊂G⟨Y⟩)
    th = instancie(N.generalisation("G", th), g)
    th = instancie(N.generalisation("X", th), x)
    th = instancie(N.generalisation("Y", th), y)
    return th


# ── PALIER 3 : D = ⋂ { S ∈ 𝔓(A) | φ(S) ⊂ S }  (les parties φ-closes) ───────────
#
# D est collectivisant (S8 : sélection dans A ; A1 : unicité), comme produit /
# image / diagonale.  On l'introduit comme TERME + axiome DÉFINITIONNEL fidèle,
# exposé via une mini-théorie dédiée `theorie_D` (pattern theorie_graphe_terme /
# theorie_intervalle_entiers), SANS toucher à theorie_ensembles().
#
#   D(A,B,f,g) := { z ∈ A | (∀S)( (S⊂A et φ(S)⊂S) ⇒ z∈S ) }
#
# (« S⊂A » EST « S∈𝔓(A) » modulo AXIOME_PARTIES (A3) ; on prend la forme ⊂,
#  plus directe, équivalente et fidèle.)


def D(a, b, f, g):
    """D := ⋂ { S ⊂ A | φ(S) ⊂ S }  (intersection des parties φ-closes)."""
    return E.app("D_kt", a, b, f, g)


def _phi_clos(a, b, f, g, s):
    """« S est φ-close » := (S ⊂ A) et (φ(S) ⊂ S).

    Liant interne de ⊂ = « z » (cohérent avec inclus/A1 et avec
    inclusion_transitive, dont le liant par défaut est « z » → pas de désaccord
    de binder lors du sandwich φ(D)⊂φ(S)⊂S)."""
    return et(inclus(s, a), inclus(phi(a, b, f, g, s), s))


def _allS(a, b, f, g, z):
    """(∀S)( (S⊂A et φ(S)⊂S) ⇒ z∈S )   (le 2e conjoint du corps de D)."""
    return pourtout("S", impl(_phi_clos(a, b, f, g, var("S")), appartient(z, var("S"))))


def _corps_D(a, b, f, g, z):
    """Corps de D :  z∈A et (∀S)( S φ-close ⇒ z∈S )."""
    return et(appartient(z, a), _allS(a, b, f, g, z))


def axiome_D(a="A", b="B", f="f", g="g", z="z"):
    """⊢-schéma  (∀A)(∀B)(∀f)(∀g)(∀z)( z∈D ⇔ (z∈A et (∀S)(S φ-close ⇒ z∈S)) ).

    Axiome DÉFINITIONNEL de l'intersection des parties φ-closes (légitime S8+A1)."""
    vA, vB, vf, vg, vz = var(a), var(b), var(f), var(g), var(z)
    return pourtout(a, pourtout(b, pourtout(f, pourtout(g, pourtout(z,
        equiv(appartient(vz, D(vA, vB, vf, vg)),
              _corps_D(vA, vB, vf, vg, vz)))))))


def theorie_D(a="A", b="B", f="f", g="g", z="z"):
    """Théorie ne contenant que l'axiome de D (E.III.3.2, Knaster–Tarski)."""
    return N.Theorie("D-Knaster-Tarski", [axiome_D(a, b, f, g, z)])


def _inst_D(a, b, f, g, z):
    """⊢ ( z∈D ⇔ (z∈A et (∀S)(S φ-close ⇒ z∈S)) )   (axiome instancié aux TERMES)."""
    ax = N.axiome(theorie_D(), axiome_D())
    return instancie(instancie(instancie(instancie(instancie(ax, a), b), f), g), z)


def D_membre(a="A", b="B", f="f", g="g", z="z"):
    """⊢ ( z∈D ) ⇔ ( z∈A et (∀S)( (S⊂A et φ(S)⊂S) ⇒ z∈S ) ).   (PALIER 3.)"""
    return _inst_D(var(a), var(b), var(f), var(g), var(z))


def D_inclus_A(a="A", b="B", f="f", g="g"):
    """⊢ D ⊂ A.   (l'intersection des parties φ-closes est incluse dans A.)"""
    vA, vB, vf, vg, vz = var(a), var(b), var(f), var(g), var("z")
    eq = _inst_D(vA, vB, vf, vg, vz)                     # z∈D ⇔ (z∈A et ∀S…)
    z_imp = syllogisme(equivalence_avant(eq),
                       projection_gauche(appartient(vz, vA),
                                         _allS(vA, vB, vf, vg, vz)))
    return N.generalisation("z", z_imp)                 # (∀z)(z∈D⇒z∈A) = D⊂A


def D_inclus(a="A", b="B", f="f", g="g", s="S"):
    """⊢ ( (S⊂A et φ(S)⊂S) ) ⇒ ( D ⊂ S ).

    D est inclus dans CHAQUE partie φ-close (c'est l'intersection)."""
    vA, vB, vf, vg, vS, vz = var(a), var(b), var(f), var(g), var(s), var("z")
    clos = _phi_clos(vA, vB, vf, vg, vS)                 # S⊂A et φ(S)⊂S
    h = N.assume(clos)
    eq = _inst_D(vA, vB, vf, vg, vz)
    # z∈D ⇒ (∀S)(S φ-close ⇒ z∈S)
    z_to_all = syllogisme(equivalence_avant(eq),
                          projection_droite(appartient(vz, vA),
                                            _allS(vA, vB, vf, vg, vz)))
    # z∈D ⇒ z∈S  (sous l'hypothèse « S φ-close ») :
    hz = N.assume(appartient(vz, D(vA, vB, vf, vg)))     # z∈D
    all_from_z = N.modus_ponens(hz, z_to_all)           # (∀S)(S φ-close⇒z∈S)   [hyp z∈D]
    inst_from_z = instancie(all_from_z, vS)             # (S φ-close ⇒ z∈S)     [hyp z∈D]
    zS = N.modus_ponens(h, inst_from_z)                 # z∈S   [hyps z∈D, clos]
    z_imp = N.loi_deduction(appartient(vz, D(vA, vB, vf, vg)), zS)  # (z∈D⇒z∈S)  [hyp clos]
    incl = N.generalisation("z", z_imp)                 # D⊂S   [hyp clos]
    return N.loi_deduction(clos, incl)                  # ⊢ (S φ-close) ⇒ (D⊂S)


def phi_D_inclus_A(a="A", b="B", f="f", g="g"):
    """⊢ φ(D) ⊂ A.   (φ(·)=A∖… est toujours ⊂ A, trivialement.)"""
    vA, vB, vf, vg, vz = var(a), var(b), var(f), var(g), var("z")
    dterm = D(vA, vB, vf, vg)
    mem_D = _phi_membre_terme(vA, vB, vf, vg, dterm, vz)  # z∈φ(D) ⇔ (z∈A et ¬(z∈g⟨B∖f⟨D⟩⟩))
    gbfD = E.image(vg, E.difference(vB, E.image(vf, dterm)))   # g⟨B∖f⟨D⟩⟩
    z_imp = syllogisme(equivalence_avant(mem_D),
                       projection_gauche(appartient(vz, vA), non(appartient(vz, gbfD))))
    return N.generalisation("z", z_imp)                 # φ(D)⊂A


def _phi_membre_terme(a, b, f, g, s, z):
    """⊢ ( z∈φ(S) ) ⇔ ( z∈A et ¬(z∈g⟨B∖f⟨S⟩⟩) )  pour des TERMES quelconques."""
    gbfs = E.image(g, E.difference(b, E.image(f, s)))
    return _inst_diff(a, gbfs, z)


# ── PALIER 4 : φ(D) = D  (THÉORÈME DE KNASTER–TARSKI, cœur de Cantor–Bernstein) ─

def phi_D_inclus_D(a="A", b="B", f="f", g="g"):
    """⊢ φ(D) ⊂ D.   (D est φ-close : φ(D)⊂φ(S)⊂S pour toute S φ-close → φ(D)⊂⋂=D.)"""
    vA, vB, vf, vg, vz = var(a), var(b), var(f), var(g), var("z")
    dterm = D(vA, vB, vf, vg)
    phiD_A = phi_D_inclus_A(a, b, f, g)                  # φ(D)⊂A
    phiD_A_z = N.modus_ponens(phiD_A, instanciation_en_x(
        impl(appartient(vz, phi(vA, vB, vf, vg, dterm)), appartient(vz, vA)), "z"))  # z∈φ(D)⇒z∈A

    # but : z∈φ(D) ⇒ (z∈A et (∀S)(S φ-close ⇒ z∈S)) ⇒ z∈D
    hz = N.assume(appartient(vz, phi(vA, vB, vf, vg, dterm)))   # z∈φ(D)
    zA = N.modus_ponens(hz, phiD_A_z)                   # z∈A   [hyp z∈φ(D)]
    # (∀S)(S φ-close ⇒ z∈S) :
    clos = _phi_clos(vA, vB, vf, vg, var("S"))          # (S⊂A et φ(S)⊂S)
    hcl = N.assume(clos)
    # D⊂S  (D_inclus)  →  φ(D)⊂φ(S)  (phi_monotone)  →  φ(S)⊂S (hyp)  →  φ(D)⊂S
    DS = N.modus_ponens(hcl, D_inclus(a, b, f, g, "S"))            # D⊂S   [hyp clos]
    phiDS = N.modus_ponens(DS, _phi_mono_terme(vA, vB, vf, vg, dterm, var("S")))  # φ(D)⊂φ(S) [clos]
    phiS_S = conjonction_elim_droite(hcl)              # φ(S)⊂S   [hyp clos]
    phiD_S = N.modus_ponens(conjonction_intro(phiDS, phiS_S),
                            inclusion_transitive_terme(phi(vA, vB, vf, vg, dterm),
                                                       phi(vA, vB, vf, vg, var("S")),
                                                       var("S")))  # φ(D)⊂S [clos]
    # φ(D)⊂S instancié en z : z∈φ(D)⇒z∈S, MP hz → z∈S
    phiD_S_z = N.modus_ponens(phiD_S, instanciation_en_x(
        impl(appartient(vz, phi(vA, vB, vf, vg, dterm)), appartient(vz, var("S"))), "z"))  # [clos]
    zS = N.modus_ponens(hz, phiD_S_z)                  # z∈S   [hyps z∈φ(D), clos]
    S_imp = N.loi_deduction(clos, zS)                  # (S φ-close ⇒ z∈S)   [hyp z∈φ(D)]
    allS = N.generalisation("S", S_imp)               # (∀S)(S φ-close ⇒ z∈S)  [hyp z∈φ(D)]
    corps = conjonction_intro(zA, allS)               # z∈A et (∀S)…   [hyp z∈φ(D)]
    zD = N.modus_ponens(corps, equivalence_arriere(_inst_D(vA, vB, vf, vg, vz)))  # z∈D [hyp z∈φ(D)]
    z_imp = N.loi_deduction(appartient(vz, phi(vA, vB, vf, vg, dterm)), zD)       # z∈φ(D)⇒z∈D
    return N.generalisation("z", z_imp)               # φ(D)⊂D


def D_inclus_phi_D(a="A", b="B", f="f", g="g"):
    """⊢ D ⊂ φ(D).   (de φ(D)⊂D + monotone : φ(φ(D))⊂φ(D), donc φ(D) est φ-close ;
       D⊂(toute φ-close) → D⊂φ(D).)"""
    vA, vB, vf, vg = var(a), var(b), var(f), var(g)
    dterm = D(vA, vB, vf, vg)
    phiD = phi(vA, vB, vf, vg, dterm)
    phiD_D = phi_D_inclus_D(a, b, f, g)                # φ(D)⊂D
    # φ(φ(D)) ⊂ φ(D)  (φ monotone appliqué à φ(D)⊂D)
    phiphiD_phiD = N.modus_ponens(phiD_D, _phi_mono_terme(vA, vB, vf, vg, phiD, dterm))
    # φ(D) ⊂ A   (φ(D)=A∖… trivialement ⊂ A)
    phiD_A = phi_D_inclus_A(a, b, f, g)               # φ(D)⊂A
    # φ(D) est φ-close : (φ(D)⊂A et φ(φ(D))⊂φ(D))
    clos_phiD = conjonction_intro(phiD_A, phiphiD_phiD)
    # D ⊂ (toute φ-close) appliqué à S:=φ(D)
    return N.modus_ponens(clos_phiD, D_inclus_terme(vA, vB, vf, vg, phiD))


def phi_point_fixe(a="A", b="B", f="f", g="g"):
    """⊢ φ(D) = D.   (THÉORÈME DE KNASTER–TARSKI — point fixe, cœur de Cantor–Bernstein.)

    Double inclusion φ(D)⊂D (D φ-close) et D⊂φ(D) (φ(D) φ-close), puis A1."""
    from bourbaki.ensembles.ensembles_theoremes import extensionnalite_appliquee
    vA, vB, vf, vg = var(a), var(b), var(f), var(g)
    dterm = D(vA, vB, vf, vg)
    phiD = phi(vA, vB, vf, vg, dterm)
    double = conjonction_intro(phi_D_inclus_D(a, b, f, g),   # φ(D)⊂D
                               D_inclus_phi_D(a, b, f, g))   # D⊂φ(D)
    return N.modus_ponens(double, extensionnalite_appliquee(phiD, dterm))  # φ(D)=D


# ── helpers TERME pour phi_monotone, inclusion_transitive, D_inclus ───────────

def _phi_mono_terme(a, b, f, g, s, sp):
    """⊢ (S⊂S′)⇒(φ(S)⊂φ(S′))  où A,B,f,g,S,S′ sont des TERMES."""
    th = phi_monotone("A", "B", "f", "g", "S", "Sp")
    for nm, tm in (("A", a), ("B", b), ("f", f), ("g", g), ("S", s), ("Sp", sp)):
        th = instancie(N.generalisation(nm, th), tm)
    return th


def inclusion_transitive_terme(a, b, c):
    """⊢ ((a⊂b) et (b⊂c)) ⇒ (a⊂c)  pour des TERMES a,b,c."""
    th = inclusion_transitive("a", "b", "c")
    for nm, tm in (("a", a), ("b", b), ("c", c)):
        th = instancie(N.generalisation(nm, th), tm)
    return th


def D_inclus_terme(a, b, f, g, s):
    """⊢ ((S⊂A et φ(S)⊂S)) ⇒ (D⊂S)  où S est un TERME."""
    th = D_inclus("A", "B", "f", "g", "S")    # version à lettres
    for nm, tm in (("A", a), ("B", b), ("f", f), ("g", g), ("S", s)):
        th = instancie(N.generalisation(nm, th), tm)
    return th


__all__ = ["phi", "phi_membre", "difference_anti_monotone", "phi_monotone",
           "D", "axiome_D", "theorie_D", "D_membre", "D_inclus_A", "D_inclus",
           "phi_D_inclus_A", "phi_D_inclus_D", "D_inclus_phi_D", "phi_point_fixe"]
