"""§III.7.2 — Proposition 2 (limite projective d'un système projectif d'applications).

Module NEUF, complémentaire de `ensembles_limites`, `ensembles_limites_canoniques`,
`ensembles_limites_props2` (importés, AUCUNE modification).  On y prouve le CŒUR
ATTEIGNABLE de la PROPOSITION 2 (E.III.7.2, E III.54) et de son COROLLAIRE :

  PROPOSITION 2.  (E_α,f_{αβ}), (E'_α,f'_{αβ}) deux systèmes projectifs relatifs à I ;
  pour chaque α∈I, u_α : E_α → E'_α, les (u_α) formant un système projectif
  d'applications.  Soit u = lim← u_α : E → E' (E=lim←E_α, E'=lim←E'_α).
    COROLLAIRE.  Si u_α est injective pour tout α∈I, alors u est injective.

  CONTENU FIDÈLE de la preuve Bourbaki (E III.54) : « u(x)=x' signifie par définition
  que u_α(x_α)=x'_α pour tout α », c.-à-d. la limite d'applications agit
  COORDONNÉE PAR COORDONNÉE :
        (LU)   pr_α(u(z)) = u_α(pr_α z)        pour z∈E=lim← et α∈I.
  C'est la relation g_α∘u = u_α∘f_α de la Prop.1 lue au niveau des valeurs (sur la
  limite f_α=pr_α, g_α=pr'_α).  On la pose comme AXIOME DÉFINITIONNEL de la valeur de
  u=lim←u_α dans une THÉORIE DÉDIÉE paramétrée (motif axiome_lim_proj /
  axiome_cone_canonique : S8 sélection du graphe + A1 unicité).  theorie_ensembles()
  reste à 22.

  PREUVE de l'injectivité (Corollaire), fidèle à Bourbaki :
   soit u(y)=u(z), y,z∈E.  Pour chaque α :
        u_α(pr_α y) = pr_α(u(y))        [(LU) en y]
                    = pr_α(u(z))        [congruence : u(y)=u(z)]
                    = u_α(pr_α z)       [(LU) en z].
   u_α injective (sur E_α, et pr_α y, pr_α z ∈ E_α) ⟹ pr_α y = pr_α z, pour tout α.
   Deux points de E=lim← (⊂ ∏_α E_α) de mêmes projections sont égaux
   (extensionnalité du produit) ⟹ y = z.

REPORTÉ honnêtement (champ REPORTES) : l'IDENTITÉ « u⁻¹(x') = lim← u_α⁻¹(x'_α) » de la
Prop.2 (égalité d'ensembles ; exige l'image-réciproque effective et le système
projectif de parties u_α⁻¹(x'_α)) ; le cas BIJECTIF du Corollaire (surjectivité —
absente sans cône universel) ; Prop.3 (cofinal ⇒ g bijective : la BIJECTIVITÉ reste
hors d'atteinte, seul le sens facile « g bien définie » est déjà prouvé dans
`ensembles_limites_props2.cofinal_canonique_compatible`).

Hypothèses résiduelles de l'injectivité (toutes HONNÊTES, NON vacuous, NON fausses) :
  • u_α injective (∀α) — l'hypothèse même du Corollaire ;
  • (LU) — l'axiome définitionnel de la valeur de u (théorie dédiée) ;
  • y,z ∈ E=lim← et pr_α y, pr_α z ∈ E_α, et y,z points-graphes du produit — domaines
    + bonne-formation (issus de l'appartenance à la limite, partie du produit).
La conclusion « y = z » n'apparaît dans aucune hypothèse (anti-tautologie).
"""
from __future__ import annotations

from bourbaki.logique.formule import (
    Terme, var, app, egal, et, impl, appartient, pourtout,
)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.ensembles.familles import ensembles_limites as L
from bourbaki.ordre import ensembles_limites_canoniques as C
from bourbaki.logique.tactiques.tactiques_abrege2 import (
    instancie, conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
)
from bourbaki.logique.tactiques.tactiques_abrege_egalite import (
    composer_egalites, symetrie, congruence_terme,
)
from bourbaki.ensembles.familles.ensembles_extensionnalite_produit import (
    extensionnalite_produit,
)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def _gleq():
    """Préordre ≤ par défaut (même convention que tous les modules limites)."""
    return lambda u, v: appartient(E.couple(u, v), var("Gleq"))


# ════════════════════════════════════════════════════════════════════════════
#  Terme  u = lim← u_α : E → E'  et son AXIOME DÉFINITIONNEL (LU)
# ════════════════════════════════════════════════════════════════════════════
def lim_proj_u(EfamE, fE, EfamF, fF, u):
    """u = lim← u_α : E=lim←E_α → E'=lim←E'_α  (terme du graphe, Prop.2/Cor.1).

    Le MÊME terme que `C.lim_proj_applications` — réexporté ici pour lisibilité."""
    return C.lim_proj_applications(EfamE, fE, EfamF, fF, u)


def lim_proj_u_valeur(EfamE, fE, EfamF, fF, u, z):
    """u(z) := valeur(lim← u_α, z)  (valeur de la limite d'applications en z∈E)."""
    return E.valeur(lim_proj_u(EfamE, fE, EfamF, fF, u), z)


def axiome_lim_proj_u(EfamE, fE, EfamF, fF, u, leq, i, a="a", z="z"):
    """AXIOME définitionnel (LU) de la valeur de u=lim←u_α (E.III.7.2, preuve Prop.2) :
        (∀α)(∀z)( (α∈I et z∈lim←E_α) ⇒ pr_α(u(z)) = u_α(pr_α z) ).

    « la limite d'applications agit coordonnée par coordonnée » — c'est g_α∘u=u_α∘f_α
    lu au niveau des valeurs (f_α=pr_α, g_α=pr'_α sur les limites).  Légitimé par S8
    (sélection du graphe {(z,(u_α(pr_α z))_α)} dans E × ∏_α E'_α) + A1 — même statut
    que AXIOME_PRODUIT_FAM / axiome_lim_proj / axiome_cone_canonique."""
    va, vz = var(a), var(z)
    u_z = lim_proj_u_valeur(EfamE, fE, EfamF, fF, u, vz)
    ua = C.u_indice(u, va)
    hyp = et(appartient(va, i), appartient(vz, L.lim_proj(EfamE, fE)))
    concl = egal(E.projection_indice(u_z, va),
                 E.valeur(ua, E.projection_indice(vz, va)))
    return pourtout(a, pourtout(z, impl(hyp, concl)))


def theorie_lim_proj_u(EfamE, fE, EfamF, fF, u, leq, i):
    """Théorie dédiée ne contenant que l'axiome (LU) de la valeur de u=lim←u_α."""
    return N.Theorie("Lim-proj-applications",
                     [axiome_lim_proj_u(EfamE, fE, EfamF, fF, u, leq, i)])


# ════════════════════════════════════════════════════════════════════════════
#  (LU) instancié — la α-coordonnée de u(z)
# ════════════════════════════════════════════════════════════════════════════
def lim_u_coordonnee(EfamE="E", fE="f", EfamF="Ep", fF="fp", u="u", leq=None, i="I",
                     a="a", z="z"):
    """{ α∈I, z∈lim←E_α } ⊢ pr_α(u(z)) = u_α(pr_α z).   (LU) instancié.

    La α-coordonnée de u(z) est u_α appliqué à la α-coordonnée de z : c'est la
    définition coordonnée-par-coordonnée de u=lim←u_α (E III.54)."""
    if leq is None:
        leq = _gleq()
    vEE, vfE, vEF, vfF, vu, vi = _t(EfamE), _t(fE), _t(EfamF), _t(fF), _t(u), _t(i)
    va, vz = _t(a), _t(z)
    ax = N.axiome(theorie_lim_proj_u(vEE, vfE, vEF, vfF, vu, leq, vi),
                  axiome_lim_proj_u(vEE, vfE, vEF, vfF, vu, leq, vi))
    inst = instancie(instancie(ax, va), vz)          # (α∈I et z∈lim←) ⇒ pr_α(u(z))=u_α(pr_α z)
    Ha = N.assume(appartient(va, vi))
    Hz = N.assume(appartient(vz, L.lim_proj(vEE, vfE)))
    return N.modus_ponens(conjonction_intro(Ha, Hz), inst)


# ════════════════════════════════════════════════════════════════════════════
#  CŒUR : u(y)=u(z) ⟹ u_α(pr_α y) = u_α(pr_α z)  (par coordonnée)
# ════════════════════════════════════════════════════════════════════════════
def lim_u_coordonnee_egale(EfamE="E", fE="f", EfamF="Ep", fF="fp", u="u", leq=None,
                           i="I", a="a", y="yy", z="zz"):
    """{ α∈I, y∈lim←, z∈lim←, u(y)=u(z) } ⊢ u_α(pr_α y) = u_α(pr_α z).

    De l'égalité u(y)=u(z) on tire l'égalité de TOUTES les coordonnées composées par
    u_α (E III.54) :
        u_α(pr_α y) = pr_α(u(y))     [(LU) en y, renversé]
                    = pr_α(u(z))     [congruence : u(y)=u(z) sous pr_α]
                    = u_α(pr_α z).    [(LU) en z]."""
    if leq is None:
        leq = _gleq()
    vEE, vfE, vEF, vfF, vu, vi = _t(EfamE), _t(fE), _t(EfamF), _t(fF), _t(u), _t(i)
    va, vy, vz = _t(a), _t(y), _t(z)
    u_y = lim_proj_u_valeur(vEE, vfE, vEF, vfF, vu, vy)
    u_z = lim_proj_u_valeur(vEE, vfE, vEF, vfF, vu, vz)
    pra_uy = E.projection_indice(u_y, va)
    pra_uz = E.projection_indice(u_z, va)
    ua = C.u_indice(vu, va)
    ua_pry = E.valeur(ua, E.projection_indice(vy, va))   # u_α(pr_α y)
    ua_prz = E.valeur(ua, E.projection_indice(vz, va))   # u_α(pr_α z)

    # (LU) en y : pr_α(u(y)) = u_α(pr_α y) ;  renversée → u_α(pr_α y) = pr_α(u(y))
    luy = lim_u_coordonnee(vEE, vfE, vEF, vfF, vu, leq, vi, a, y)        # pr_α(u(y))=u_α(pr_α y)
    luy_sym = N.modus_ponens(luy, symetrie(pra_uy, ua_pry))             # u_α(pr_α y)=pr_α(u(y))
    # congruence : u(y)=u(z) ⟹ pr_α(u(y)) = pr_α(u(z))
    Heq = N.assume(egal(u_y, u_z))
    cong = N.modus_ponens(Heq, congruence_terme(
        u_y, u_z, E.projection_indice(var("w"), va), "w"))             # pr_α(u(y))=pr_α(u(z))
    # (LU) en z : pr_α(u(z)) = u_α(pr_α z)
    luz = lim_u_coordonnee(vEE, vfE, vEF, vfF, vu, leq, vi, a, z)        # pr_α(u(z))=u_α(pr_α z)
    # chaîne :  u_α(pr_α y) = pr_α(u(y)) = pr_α(u(z)) = u_α(pr_α z)
    ch1 = composer_egalites(luy_sym, cong)                              # u_α(pr_α y)=pr_α(u(z))
    return composer_egalites(ch1, luz)                                  # u_α(pr_α y)=u_α(pr_α z)


# ════════════════════════════════════════════════════════════════════════════
#  u_α injective ⟹ pr_α y = pr_α z  (par coordonnée)
# ════════════════════════════════════════════════════════════════════════════
def lim_u_projection_egale(EfamE="E", fE="f", EfamF="Ep", fF="fp", u="u", leq=None,
                           i="I", Efam_alpha="Ea", a="a", y="yy", z="zz"):
    """{ α∈I, y∈lim←, z∈lim←, u(y)=u(z),  u_α injective sur E_α,
         pr_α y∈E_α, pr_α z∈E_α } ⊢ pr_α y = pr_α z.

    De u_α(pr_α y)=u_α(pr_α z) (lim_u_coordonnee_egale) et de l'injectivité de u_α sur
    E_α (avec pr_α y, pr_α z ∈ E_α), on conclut pr_α y = pr_α z (E III.54).

    `Efam_alpha` = le terme E_α = valeur de la famille source en α (le DOMAINE de u_α
    sur lequel porter l'injectivité gardée)."""
    if leq is None:
        leq = _gleq()
    vEE, vfE, vEF, vfF, vu, vi = _t(EfamE), _t(fE), _t(EfamF), _t(fF), _t(u), _t(i)
    va, vy, vz, vEa = _t(a), _t(y), _t(z), _t(Efam_alpha)
    ua = C.u_indice(vu, va)
    pry = E.projection_indice(vy, va)
    prz = E.projection_indice(vz, va)

    # u_α(pr_α y) = u_α(pr_α z)
    coord_eq = lim_u_coordonnee_egale(vEE, vfE, vEF, vfF, vu, leq, vi, a, y, z)
    # injectivité GARDÉE de u_α sur E_α : (pr_α y,pr_α z∈E_α et u_α(pr_α y)=u_α(pr_α z)) ⇒ pr_α y=pr_α z
    # binders NEUFS « vinj/vinjp » : le défaut « u/up » de injective_dans collisionne
    # avec le var('u') interne de u_α=app("u_indice",u,α) → capture lors de
    # l'instanciation des projections.  On nomme les liants hors-collision.
    inj = N.assume(E.injective_dans(ua, vEa, u="vinj", up="vinjp"))   # (∀v)(∀v')((v∈E_α et v'∈E_α et u_α(v)=u_α(v'))⇒v=v')
    inj_inst = instancie(instancie(inj, pry), prz)       # (pr_α y∈E_α et pr_α z∈E_α et u_α(pr_α y)=u_α(pr_α z))⇒pr_α y=pr_α z
    Hpry = N.assume(appartient(pry, vEa))
    Hprz = N.assume(appartient(prz, vEa))
    premisse = conjonction_intro(conjonction_intro(Hpry, Hprz), coord_eq)
    return N.modus_ponens(premisse, inj_inst)            # pr_α y = pr_α z


# ════════════════════════════════════════════════════════════════════════════
#  COROLLAIRE Prop. 2 — u_α injective (∀α) ⟹ u injective : y = z
# ════════════════════════════════════════════════════════════════════════════
def prop2_injectivite(EfamE="E", fE="f", EfamF="Ep", fF="fp", u="u", leq=None,
                      i="I", a="a", y="yy", z="zz"):
    """{ (∀α)( α∈I ⇒ ( u_α injective sur E_α ) ) ;
         (∀α)( α∈I ⇒ ( pr_α y∈E_α et pr_α z∈E_α ) ) ;
         y∈lim← ; z∈lim← ; u(y)=u(z) ;
         y,z∈∏ ; est_un_graphe(y) ; est_un_graphe(z) }  ⊢  y = z.

    COROLLAIRE de la Proposition 2 (E.III.7.2, E III.54) : si chaque u_α est injective,
    alors u=lim←u_α est injective.  Preuve fidèle à Bourbaki :
      • pour tout α∈I : pr_α y = pr_α z       [lim_u_projection_egale + injectivité u_α] ;
      • y,z ∈ ∏_α E_α de mêmes projections ⟹ y = z   [extensionnalité du produit].

    Hypothèses résiduelles HONNÊTES (aucune fausse ; conclusion y=z absente d'elles) :
      injectivité-famille des u_α ; appartenance des projections aux E_α ;
      y,z∈lim← + u(y)=u(z) (la prémisse d'injectivité de u) ;
      y,z∈∏ et bien-formés (points-graphes), issus de l'appartenance à la limite (⊂ ∏).
    """
    if leq is None:
        leq = _gleq()
    vEE, vfE, vEF, vfF, vu, vi = _t(EfamE), _t(fE), _t(EfamF), _t(fF), _t(u), _t(i)
    va, vy, vz = var(a), _t(y), _t(z)
    pry = E.projection_indice(vy, va)
    prz = E.projection_indice(vz, va)
    Ea = E.valeur_famille(vEE, va)                       # E_α = (E_α)(α)

    # ── (∀α)( α∈I ⇒ pr_α y = pr_α z ) ──────────────────────────────────────
    # injectivité-famille : (∀α)(α∈I ⇒ u_α injective sur E_α)
    Hinj_fam = N.assume(pourtout(a, impl(appartient(va, vi),
                         E.injective_dans(C.u_indice(vu, va), Ea, u="vinj", up="vinjp"))))
    inj_a = N.modus_ponens(N.assume(appartient(va, vi)), instancie(Hinj_fam, va))  # u_α inj sur E_α
    # appartenance-famille des projections : (∀α)(α∈I ⇒ (pr_α y∈E_α et pr_α z∈E_α))
    Hproj_fam = N.assume(pourtout(a, impl(appartient(va, vi),
                         et(appartient(pry, Ea), appartient(prz, Ea)))))
    proj_a = N.modus_ponens(N.assume(appartient(va, vi)), instancie(Hproj_fam, va))
    Hpry = conjonction_elim_gauche(proj_a)              # pr_α y ∈ E_α
    Hprz = conjonction_elim_droite(proj_a)              # pr_α z ∈ E_α

    # pr_α y = pr_α z  (sous : α∈I + injectivité + appartenances + y,z∈lim← + u(y)=u(z))
    pr_eq = lim_u_projection_egale(vEE, vfE, vEF, vfF, vu, leq, vi, Ea, a, y, z)
    #   pr_eq porte comme hyp : (u_α inj sur E_α), (pr_α y∈E_α), (pr_α z∈E_α),
    #   (α∈I), (y∈lim←), (z∈lim←), (u(y)=u(z)).
    #   On décharge les trois premières par inj_a, Hpry, Hprz (mêmes formules),
    #   et α∈I en implication pour généraliser.
    imp1 = N.loi_deduction(
        E.injective_dans(C.u_indice(vu, va), Ea, u="vinj", up="vinjp"), pr_eq)
    pr_eq1 = N.modus_ponens(inj_a, imp1)
    imp2 = N.loi_deduction(appartient(pry, Ea), pr_eq1)
    pr_eq2 = N.modus_ponens(Hpry, imp2)
    imp3 = N.loi_deduction(appartient(prz, Ea), pr_eq2)
    pr_eq3 = N.modus_ponens(Hprz, imp3)                 # {α∈I, y,z∈lim←, u(y)=u(z), fam-hyps} ⊢ pr_α y=pr_α z
    # décharger α∈I et généraliser : (∀α)(α∈I ⇒ pr_α y=pr_α z)
    imp_a = N.loi_deduction(appartient(va, vi), pr_eq3)
    forall_proj = N.generalisation(a, imp_a)            # (∀α)(α∈I ⇒ pr_α y=pr_α z)

    # ── extensionnalité du produit : y,z∈∏ + graphes + (∀α)(α∈I⇒pr_α y=pr_α z) ⟹ y=z
    ext = extensionnalite_produit(vEE, vi, vy, vz, a)   # ⊢ ( y∈∏ et z∈∏ et gr(y) et gr(z) et (∀ι)(ι∈I⇒pr_ι y=pr_ι z) ) ⇒ y=z
    prod = E.produit_famille(vEE, vi)
    Hy_prod = N.assume(appartient(vy, prod))
    Hz_prod = N.assume(appartient(vz, prod))
    Hgy = N.assume(E.est_un_graphe(vy))
    Hgz = N.assume(E.est_un_graphe(vz))
    conj_ext = conjonction_intro(conjonction_intro(conjonction_intro(conjonction_intro(
        Hy_prod, Hz_prod), Hgy), Hgz), forall_proj)
    return N.modus_ponens(conj_ext, ext)               # y = z


# Résultats DURS introduits mais NON prouvés (honnêteté).
REPORTES = [
    "Proposition 2 (E.III.7.2) : identité d'ensembles u⁻¹(x') = lim← u_α⁻¹(x'_α) — "
    "exige l'image-réciproque effective + le système projectif de parties u_α⁻¹(x'_α) "
    "— REPORTÉ (seule l'injectivité du Corollaire est prouvée).",
    "Corollaire Prop. 2, cas BIJECTIF (u bijective si u_α bijectives) — la "
    "SURJECTIVITÉ exige le cône universel / la limite des préimages — REPORTÉ.",
    "Proposition 3 (§III.7.2) : cofinal ⇒ g canonique BIJECTIVE — la bijectivité "
    "reste hors d'atteinte (seul « g bien définie / compatible » est prouvé dans "
    "ensembles_limites_props2.cofinal_canonique_compatible) — REPORTÉ.",
]


__all__ = [
    "lim_proj_u", "lim_proj_u_valeur",
    "axiome_lim_proj_u", "theorie_lim_proj_u",
    "lim_u_coordonnee", "lim_u_coordonnee_egale", "lim_u_projection_egale",
    "prop2_injectivite",
    "REPORTES",
]
