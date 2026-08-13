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
absente sans cône universel).

⚠️ PÉRIMÉ, corrigé le 4 août 2026 : ce préambule annonçait aussi la Prop. 3
(« la BIJECTIVITÉ reste hors d'atteinte, seul le sens facile est prouvé »).
C'est FAUX depuis les ev. 167-173 : les DEUX SENS sont démontrés ET quantifiés
dans `prop1_proj/` (injectivité `prop3_g_injective_universelle`, 2 hyps ;
surjectivité `prolongement_coherent_universel`, 4 hyps), sans axiome du choix.
Ce qui reste n'est pas la bijectivité mais l'objet-FONCTION : exhiber g avec
`func` + `dom` pour atteindre littéralement `est_bijection_de`.

Hypothèses résiduelles de l'injectivité (toutes HONNÊTES, NON vacuous, NON fausses) :
  • u_α injective (∀α) — l'hypothèse même du Corollaire ;
  • (LU) — l'axiome définitionnel de la valeur de u (théorie dédiée) ;
  • y,z ∈ E=lim← et pr_α y, pr_α z ∈ E_α — domaines.
La bonne formation (y,z ∈ ∏ et points-graphes) n'y figure PLUS : elle était
annotée « issue de l'appartenance à la limite », ce qui décrivait un théorème
non écrit — il l'est désormais (`prop1_proj/ensembles_lim_graphe`), et les
quatre conjoints sont déduits (9 → 5 hypothèses).
La conclusion « y = z » n'apparaît dans aucune hypothèse (anti-tautologie).
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, app, egal, et, impl, appartient, pourtout,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites import ensembles_limites as L
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites import ensembles_limites_canoniques as C
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites.ensembles_limites_props2 import cofinal_canonique_coordonnee
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    instancie, conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
    composer_egalites, symetrie, congruence_terme,
)
from bourbaki.ii_theorie_des_ensembles.ii_5_produit_famille.ii_5_definitions.ensembles_extensionnalite_produit import (
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
# @livre Ch.III §7.2 Def.- | E III.54 L.1-5 | PDF p.157
def lim_proj_u(EfamE, fE, EfamF, fF, u):
    """u = lim← u_α : E=lim←E_α → E'=lim←E'_α  (terme du graphe, Prop.2/Cor.1).

    Le MÊME terme que `C.lim_proj_applications` — réexporté ici pour lisibilité."""
    return C.lim_proj_applications(EfamE, fE, EfamF, fF, u)


def lim_proj_u_valeur(EfamE, fE, EfamF, fF, u, z):
    """u(z) := valeur(lim← u_α, z)  (valeur de la limite d'applications en z∈E)."""
    return E.valeur(lim_proj_u(EfamE, fE, EfamF, fF, u), z)


# @livre Ch.III §7.2 Prop.2 | E III.54 L.39-40 | PDF p.157
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
# @livre Ch.III §7.2 Prop.2 | E III.54 L.39-40 | PDF p.157
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
# @livre Ch.III §7.2 Cor.- | E III.54 L.41-42 | PDF p.157
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
# @livre Ch.III §7.2 Cor.- | E III.54 L.41-42 | PDF p.157
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
# @livre Ch.III §7.2 Cor.- | E III.54 L.41-42 | PDF p.157
def prop2_injectivite(EfamE="E", fE="f", EfamF="Ep", fF="fp", u="u", leq=None,
                      i="I", a="a", y="yy", z="zz"):
    """{ (∀α)( α∈I ⇒ ( u_α injective sur E_α ) ) ;
         (∀α)( α∈I ⇒ ( pr_α y∈E_α et pr_α z∈E_α ) ) ;
         y∈lim← ; z∈lim← ; u(y)=u(z) }  ⊢  y = z.                    [5 hyps].

    COROLLAIRE de la Proposition 2 (E.III.7.2, E III.54) : si chaque u_α est injective,
    alors u=lim←u_α est injective.  Preuve fidèle à Bourbaki :
      • pour tout α∈I : pr_α y = pr_α z       [lim_u_projection_egale + injectivité u_α] ;
      • y,z ∈ ∏_α E_α de mêmes projections ⟹ y = z   [extensionnalité du produit].

    Hypothèses résiduelles HONNÊTES (aucune fausse ; conclusion y=z absente d'elles) :
      injectivité-famille des u_α ; appartenance des projections aux E_α ;
      y,z∈lim← + u(y)=u(z) (la prémisse d'injectivité de u).

    ✅ Les quatre conditions de bonne formation que réclame l'extensionnalité du
    produit — y,z∈∏ et est_un_graphe(y), est_un_graphe(z) — ne sont plus
    SUPPOSÉES : elles se déduisent de « y,z ∈ lim← », déjà présente, par
    lim←⊂∏ (`_lim_dans_produit`) puis `point_limite_est_graphe` (§7.1).  Elles
    étaient auparavant portées comme hypothèses honnêtes avec la mention
    qu'elles en découlaient ; c'est désormais écrit, et le compte passe de 9 à 5.
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
    #   Les quatre prémisses de bonne formation sont DÉDUITES de « y,z ∈ lim← »,
    #   déjà supposée : lim← ⊂ ∏ (_lim_dans_produit) puis « point du produit =
    #   graphe » (point_limite_est_graphe).  Rien n'est donc supposé en plus.
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites.ensembles_cone_unicite import (
        _lim_dans_produit,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites.prop1_proj.ensembles_lim_graphe import (
        point_limite_est_graphe,
    )
    ext = extensionnalite_produit(vEE, vi, vy, vz, a)   # ⊢ ( y∈∏ et z∈∏ et gr(y) et gr(z) et (∀ι)(ι∈I⇒pr_ι y=pr_ι z) ) ⇒ y=z
    lim = L.lim_proj(vEE, vfE)
    Hy_lim = N.assume(appartient(vy, lim))
    Hz_lim = N.assume(appartient(vz, lim))
    # ⚠️ paramètres BRUTS : ces briques font var() en interne (piège mesuré).
    Hy_prod = _lim_dans_produit(EfamE, fE, leq, i, vy, Hy_lim)
    Hz_prod = _lim_dans_produit(EfamE, fE, leq, i, vz, Hz_lim)
    Hgy = point_limite_est_graphe(EfamE, fE, leq, i, vy, Hy_lim)
    Hgz = point_limite_est_graphe(EfamE, fE, leq, i, vz, Hz_lim)
    conj_ext = conjonction_intro(conjonction_intro(conjonction_intro(conjonction_intro(
        Hy_prod, Hz_prod), Hgy), Hgz), forall_proj)
    return N.modus_ponens(conj_ext, ext)               # y = z


# ════════════════════════════════════════════════════════════════════════════
#  PROPOSITION 3 (§III.7.2) — cofinal ⇒ g canonique INJECTIVE (cœur pointwise)
#  g(x)=(f_α(x))_{α∈J}.  Si g(x)=g(x'), alors pr_α x=pr_α x' pour α∈J ; par
#  cofinalité, pour tout λ∈I il existe α∈J avec λ≤α, et la relation (1) propage
#  l'égalité : pr_λ x = f_{λα}(pr_α x) = f_{λα}(pr_α x') = pr_λ x'.
# ════════════════════════════════════════════════════════════════════════════
# @livre Ch.III §7.2 Prop.3 | E III.55 L.6-13 | PDF p.158
def prop3_g_coordonnee_egale(Efam="E", f="f", leq=None, i="I", J="J",
                             x="xx", xp="xp", a="a", gterme=None,
                             formule_3=None):
    """{ α∈J, x∈lim←_I, x'∈lim←_I, g(x)=g(x') } ⊢ pr_α x = pr_α x'.

    SENS « g injective sur les indices de J » : de g(x)=g(x') on tire l'égalité des
    coordonnées d'indice α∈J de x et x' (E III.55).  Preuve :
        pr_α x = f_α(x)            [(3) renversé : pr_α(g(x))=f_α(x) ; f_α=pr_α sur lim]
               = pr_α(g(x))        [formule (3), via canonique f_α(x)=pr_α x]
               = pr_α(g(x'))       [congruence : g(x)=g(x')]
               = pr_α x'.          [(3) puis canonique, en x']
    On enchaîne directement pr_α(g(x))=f_α(x)=pr_α x (et idem x').

    PARAMÉTRIQUE EN LE TERME g (migration, 4 août 2026) : `gterme` + `formule_3`
    vont de pair, défaut = terme opaque + son axiome.  Voir
    `cofinal_canonique_compatible` pour la règle de cohérence."""
    if leq is None:
        leq = _gleq()
    vE, vf, vi, vJ = _t(Efam), _t(f), _t(i), _t(J)
    va, vx, vxp = _t(a), _t(x), _t(xp)
    g = gterme if gterme is not None else C.application_canonique_g(vE, vf, vJ)
    pra_gx = E.projection_indice(E.valeur(g, vx), va)     # pr_α(g(x))
    prx = E.projection_indice(vx, va)                     # pr_α x

    # (3) en x : pr_α(g(x)) = f_α(x)   ;  canonique : f_α(x)=pr_α x  (x∈lim_I, α∈J⊂I)
    eq3_x = cofinal_canonique_coordonnee(vE, vf, leq, vi, vJ, x, a, formule_3)
    canon_x = _canon_proj_au_point(vE, vf, leq, vi, va, vx)            # f_α(x)=pr_α x
    # pr_α x = pr_α(g(x))  : renverser eq3_x∘canon_x
    gx_to_prx = composer_egalites(eq3_x, canon_x)                     # pr_α(g(x))=pr_α x
    prx_eq_gx = N.modus_ponens(gx_to_prx, symetrie(pra_gx, prx))      # pr_α x=pr_α(g(x))
    # congruence : g(x)=g(x') ⟹ pr_α(g(x))=pr_α(g(x'))
    Heq = N.assume(egal(E.valeur(g, vx), E.valeur(g, vxp)))
    cong = N.modus_ponens(Heq, congruence_terme(
        E.valeur(g, vx), E.valeur(g, vxp),
        E.projection_indice(var("w"), va), "w"))                     # pr_α(g(x))=pr_α(g(x'))
    # pr_α(g(x')) = f_α(x') = pr_α x'
    eq3_xp = cofinal_canonique_coordonnee(vE, vf, leq, vi, vJ, xp, a, formule_3)
    canon_xp = _canon_proj_au_point(vE, vf, leq, vi, va, vxp)          # f_α(x')=pr_α x'
    gxp_to_prxp = composer_egalites(eq3_xp, canon_xp)                 # pr_α(g(x'))=pr_α x'
    # chaîne : pr_α x = pr_α(g(x)) = pr_α(g(x')) = pr_α x'
    ch1 = composer_egalites(prx_eq_gx, cong)                          # pr_α x=pr_α(g(x'))
    return composer_egalites(ch1, gxp_to_prxp)                        # pr_α x=pr_α x'


def _canon_proj_au_point(Efam, f, leq, i, a_terme, z_terme):
    """{ z∈lim←, α∈I } ⊢ f_α(z)=pr_α z, termes α,z quelconques (instance axiome (2))."""
    vE, vf, vi = _t(Efam), _t(f), _t(i)
    va, vz = _t(a_terme), _t(z_terme)
    ax = N.axiome(C.theorie_canonique_proj(vE, vf, leq, vi),
                  C.axiome_canonique_proj(vE, vf, leq, vi))
    inst = instancie(instancie(ax, va), vz)
    Hz = N.assume(appartient(vz, L.lim_proj(vE, vf)))
    Ha = N.assume(appartient(va, vi))
    return N.modus_ponens(conjonction_intro(Hz, Ha), inst)


# @livre Ch.III §7.2 Prop.3 | E III.55 L.6-13 | PDF p.158
def prop3_g_injective_pointwise(Efam="E", f="f", leq=None, i="I", J="J",
                                lam="lam", a="a", x="xx", xp="xp",
                                gterme=None, formule_3=None):
    """{ λ∈I, α∈J, λ≤α, x∈lim←_I, x'∈lim←_I, g(x)=g(x') } ⊢ pr_λ x = pr_λ x'.

    CŒUR de l'injectivité de g (Prop. 3, E III.55) sous un TÉMOIN cofinal α∈J, λ≤α.
    Bourbaki : « comme J est cofinal dans I, il existe λ tel que α≤λ ; comme
    f_α(f_α(x))≠... ».  Ici, pour λ∈I quelconque et α∈J majorant (λ≤α fourni par la
    cofinalité), on propage l'égalité des α-coordonnées (prop3_g_coordonnee_egale) le
    long de la transition f_{λα} via la relation (1) :
        pr_λ x = f_{λα}(pr_α x)        [relation (1) en x∈lim_I, λ≤α]
               = f_{λα}(pr_α x')       [congruence : pr_α x=pr_α x']
               = pr_λ x'.              [relation (1) en x', renversée].

    La cofinalité de J (∃ témoin α) reste portée ICI comme HYPOTHÈSE de témoin
    (λ∈I, α∈J, λ≤α) : c'est le CŒUR ponctuel, pas le résultat final.
    ✅ La suite est faite ailleurs et n'est plus reportée : le témoin quelconque
    est remplacé par le témoin canonique β(λ) puis on généralise
    (`prop1_proj/ensembles_prop3_injectif_total`, x=x' puis forme universelle),
    et la SURJECTIVITÉ est démontrée dans
    `prop1_proj/ensembles_prolongement_cofinal` — le tout sans axiome du choix.

    PARAMÉTRIQUE EN LE TERME g (migration, 4 août 2026) : `gterme` + `formule_3`
    sont passés tels quels à `prop3_g_coordonnee_egale` ; défaut = terme opaque.
    C'est par ce paramètre que l'injectivité pourra parler du g CONSTRUIT, et
    donc être conjointe à `func`/`dom` sans mélanger deux termes."""
    if leq is None:
        leq = _gleq()
    vE, vf, vi, vJ = _t(Efam), _t(f), _t(i), _t(J)
    vlam, va, vx, vxp = var(lam), var(a), _t(x), _t(xp)
    # ⚠️ CORRIGÉ le 4 août 2026 — DOUBLE ENVELOPPAGE.  `limite_projective_relation_1`
    # fait `var(Efam)`/`var(f)` en interne : lui passer les TERMES vE/vf produisait
    # var(var('f')), donc une hypothèse « x ∈ lim←(var E, var f) » syntaxiquement
    # DISTINCTE du « x ∈ lim←(E, f) » que produisent les autres briques.  Le théorème
    # portait alors DEUX hypothèses disant la même chose, et sa forme universelle une
    # prémisse à conjoint redondant.  On lui passe désormais les paramètres BRUTS :
    # les deux formes coïncident et les hypothèses fusionnent (7 → 5).
    vf_rel = _t(f)
    flama = L.appl_proj(vf_rel, vlam, va)                 # f_{λα}  (apparié à relation_1)
    prx_a = E.projection_indice(vx, va)                   # pr_α x
    prxp_a = E.projection_indice(vxp, va)                 # pr_α x'
    prxp_lam = E.projection_indice(vxp, vlam)             # pr_λ x'

    # relation (1) en x, au couple (λ,α) avec λ≤α : pr_λ x = f_{λα}(pr_α x)
    rel1_x = L.limite_projective_relation_1(Efam, f, leq, vi, vx, lam, a)
    rel1_xp = L.limite_projective_relation_1(Efam, f, leq, vi, vxp, lam, a)
    prem = et(et(appartient(vlam, vi), appartient(va, vi)), leq(vlam, va))
    Hprem = N.assume(prem)
    eq1_x = N.modus_ponens(Hprem, rel1_x)                 # pr_λ x = f_{λα}(pr_α x)
    eq1_xp = N.modus_ponens(Hprem, rel1_xp)               # pr_λ x' = f_{λα}(pr_α x')
    # α∈J ⊂ I requis par limite (déjà via prem α∈I) ; et α∈J pour prop3_g_coordonnee_egale.
    # égalité des α-coordonnées : pr_α x = pr_α x'
    coord_eq = prop3_g_coordonnee_egale(vE, vf, leq, vi, vJ, x, xp, a,
                                        gterme, formule_3)                 # pr_α x=pr_α x'
    # f_{λα}(pr_α x) = f_{λα}(pr_α x')  (congruence)
    cong = N.modus_ponens(coord_eq, congruence_terme(
        prx_a, prxp_a, E.valeur(flama, var("w")), "w"))   # f_{λα}(pr_α x)=f_{λα}(pr_α x')
    # pr_λ x' = f_{λα}(pr_α x')  renversée → f_{λα}(pr_α x') = pr_λ x'
    eq1_xp_sym = N.modus_ponens(eq1_xp, symetrie(prxp_lam, E.valeur(flama, prxp_a)))
    # chaîne : pr_λ x = f_{λα}(pr_α x) = f_{λα}(pr_α x') = pr_λ x'
    ch1 = composer_egalites(eq1_x, cong)                  # pr_λ x=f_{λα}(pr_α x')
    return composer_egalites(ch1, eq1_xp_sym)             # pr_λ x=pr_λ x'


# Résultats DURS introduits mais NON prouvés (honnêteté).
REPORTES = [
    "Proposition 2 (E.III.7.2) : identité d'ensembles u⁻¹(x') = lim← u_α⁻¹(x'_α) — "
    "exige l'image-réciproque effective + le système projectif de parties u_α⁻¹(x'_α) "
    "— REPORTÉ (seule l'injectivité du Corollaire est prouvée).",
    "Corollaire Prop. 2, cas BIJECTIF (u bijective si u_α bijectives) — la "
    "SURJECTIVITÉ exige le cône universel / la limite des préimages — REPORTÉ.",
    "Proposition 3 (§III.7.2) — RÉSOLU, plus rien de reporté ici : ce module en "
    "fournit le CŒUR ponctuel (prop3_g_coordonnee_egale, prop3_g_injective_pointwise : "
    "pr_λ x=pr_λ x' sous témoin cofinal λ≤α∈J) ; la généralisation ∀λ + "
    "extensionnalité ⇒ x=x' et sa forme universelle sont dans "
    "prop1_proj/ensembles_prop3_injectif_total, la SURJECTIVITÉ dans "
    "prop1_proj/ensembles_prolongement_cofinal, sans axiome du choix.  Le seul "
    "écart restant à `est_bijection_de` est l'objet-FONCTION (func + dom), "
    "consigné dans le REPORTES de ensembles_prop3_injectif_total.",
]


__all__ = [
    "lim_proj_u", "lim_proj_u_valeur",
    "axiome_lim_proj_u", "theorie_lim_proj_u",
    "lim_u_coordonnee", "lim_u_coordonnee_egale", "lim_u_projection_egale",
    "prop2_injectivite",
    "prop3_g_coordonnee_egale", "prop3_g_injective_pointwise",
    "REPORTES",
]
