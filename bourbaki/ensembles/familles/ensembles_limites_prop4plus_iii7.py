"""§III.7 — Limites projectives : TRANSITIVITÉ des canoniques de restriction (formule
(4), E.III.52) et CŒUR de la Proposition 4 (E.III.57, double limite projective).

Module NEUF, complémentaire de `ensembles_limites`, `ensembles_limites_canoniques`,
`ensembles_limites_props`, `ensembles_limites_props2` (importés, AUCUNE modification).
On y prouve, au NIVEAU DES VALEURS (pointwise), deux résultats encore non couverts :

  ── 1.  FORMULE (4) (E.III.52) :  g'' = g' ∘ g   (transitivité des canoniques) ──
  Soit J' ⊂ J ⊂ I trois ensembles d'indices emboîtés ; E = lim←_I, E' = lim←_J,
  E'' = lim←_J' les limites projectives correspondantes ; g : E → E' (restriction à
  J), g' : E' → E'' (restriction à J'), g'' : E → E'' (restriction à J') les
  applications canoniques (formule (3)).  Bourbaki énonce (formule (4)) :
        (4)   g'' = g' ∘ g.
  CONTENU pointwise : pour α∈J' et x∈E=lim←_I,
        pr_α(g''(x)) = f_α(x)               [(3) pour g'', α∈J'⊂I]
                     = pr_α(g(x))           [f_α=pr_α sur la limite + (3) pour g, α∈J'⊂J]
                     = f'_α(g(x))           [f'_α=pr_α sur E'=lim←_J, g(x)∈E', α∈J']
                     = pr_α(g'(g(x))).       [(3) pour g', g(x)∈E', α∈J']
  La α-coordonnée (α∈J') de g''(x) coïncide donc avec celle de (g'∘g)(x) : c'est la
  formule (4) lue coordonnée par coordonnée.  [theoreme `formule_4_coordonnee`]

  ── 2.  PROPOSITION 4 / CŒUR (E.III.57, formules (14)-(15)) — double limite ──
  Pour un système projectif (E^λ_α, f^{λμ}_{αβ}) relatif au PRODUIT I×L et z∈G=
  ∏_{(α,λ)} E^λ_α (vu via F⊂∏_{α,λ}), « z∈E=lim←_{α,λ} » équivaut à la conjonction
  des deux familles de conditions (Bourbaki, E.III.57) :
        (14)   pr^λ_α(z) = h^{λμ}_α(pr^μ_α(z))     pour λ≤μ ;
        (15)   pr^λ_α(z) = f^λ_{αβ}(pr^λ_β(z))     pour α≤β,
  qui se RECOLLENT en la condition unique du système sur I×L :
        pr^λ_α(z) = f^{λμ}_{αβ}(pr^μ_β(z))         pour (α,λ)≤(β,μ),
  via f^{λμ}_{αβ} = f^λ_{αβ}∘h^{λμ}_β (= h^{λμ}_α∘f^μ_{αβ}, formule (11)).  On prouve
  ICI le PAS-CLÉ de la réciproque (E.III.57) :
        pr^λ_α(z) = f^λ_{αβ}(h^{λμ}_β(pr^μ_β(z))) = f^{λμ}_{αβ}(pr^μ_β(z))
  c.-à-d. que (14)+(15) donnent la condition (1) du système I×L (« z∈E »).
  [theoreme `prop4_condition_recollee`]

CODAGE.  Réutilise `C.application_canonique_g`, `C.axiome_canonique_g` (formule (3))
et `C.f_canon_proj`/`C.axiome_canonique_proj` (f_α=pr_α sur la limite), ainsi que
`C.restriction_systeme_indices` pour le système restreint à J.  Pour la Prop. 4, le
préordre produit et la factorisation (11) f^{λμ}_{αβ}=f^λ_{αβ}∘h^{λμ}_β sont portés
comme HYPOTHÈSES explicites (jamais postulées) — c'est la donnée (11) de Bourbaki.

theorie_ensembles() reste à 22 axiomes (aucun ajout).  Toutes les hypothèses
résiduelles sont HONNÊTES (appartenances aux limites = domaines/codomaines des
canoniques) et SATISFIABLES (cf. test : aucune paire contradictoire ; conclusion
absente des hypothèses).
"""
from __future__ import annotations

from bourbaki.logique.formule import (
    Terme, var, app, egal, et, impl, appartient, pourtout,
)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.ensembles.familles import ensembles_limites as L
from bourbaki.ordre.iii_7_limites import ensembles_limites_canoniques as C
from bourbaki.logique.tactiques.tactiques_abrege2 import (
    instancie, conjonction_intro,
)
from bourbaki.logique.tactiques.tactiques_abrege_egalite import (
    composer_egalites, symetrie, congruence_terme,
)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def _gleq():
    """Préordre ≤ par défaut (même convention que tous les modules limites)."""
    return lambda u, v: appartient(E.couple(u, v), var("Gleq"))


# ════════════════════════════════════════════════════════════════════════════
#  Briques : (3) au point + (f_α=pr_α) au point, pour des TERMES quelconques.
# ════════════════════════════════════════════════════════════════════════════
def _coord_g_au_point(Efam, f, leq, i, J, a_terme, x_terme):
    """{ x∈lim←(Efam,f), α∈J } ⊢ pr_α(g(x)) = f_α(x).   (formule (3), au point.)

    Instance DIRECTE (termes natifs, aucun double-`var`) de l'axiome canonique g
    de la restriction à J (C.axiome_canonique_g) en (α,x) termes quelconques."""
    vE, vf, vi, vJ = _t(Efam), _t(f), _t(i), _t(J)
    va, vx = _t(a_terme), _t(x_terme)
    ax = N.axiome(C.theorie_canonique_g(vE, vf, leq, vi, vJ),
                  C.axiome_canonique_g(vE, vf, leq, vi, vJ))
    inst = instancie(instancie(ax, va), vx)              # hyp ⇒ pr_α(g(x))=f_α(x)
    Hx = N.assume(appartient(vx, L.lim_proj(vE, vf)))
    Ha = N.assume(appartient(va, vJ))
    return N.modus_ponens(conjonction_intro(Hx, Ha), inst)   # pr_α(g(x)) = f_α(x)


def _canon_proj_au_point(Efam, f, leq, i, a_terme, z_terme):
    """{ z∈lim←(Efam,f), α∈I } ⊢ f_α(z) = pr_α z.   (formule (2), au point.)

    Instance directe de l'axiome de la valeur canonique projective (E.III.7.1, (2)),
    en (α,z) termes quelconques."""
    vE, vf, vi = _t(Efam), _t(f), _t(i)
    va, vz = _t(a_terme), _t(z_terme)
    ax = N.axiome(C.theorie_canonique_proj(vE, vf, leq, vi),
                  C.axiome_canonique_proj(vE, vf, leq, vi))
    inst = instancie(instancie(ax, va), vz)              # hyp ⇒ f_α(z)=pr_α z
    Hz = N.assume(appartient(vz, L.lim_proj(vE, vf)))
    Ha = N.assume(appartient(va, vi))
    return N.modus_ponens(conjonction_intro(Hz, Ha), inst)   # f_α(z)=pr_α z


# ════════════════════════════════════════════════════════════════════════════
#  1.  FORMULE (4) : g'' = g' ∘ g  (transitivité), lue coordonnée par coordonnée.
# ════════════════════════════════════════════════════════════════════════════
def formule_4_coordonnee(Efam="E", f="f", leq=None, i="I", J="J", Jp="Jp",
                         x="xx", a="a"):
    """{ α∈J' ,  α∈J ,  x∈lim←_I ,  g(x)∈lim←_J } ⊢ pr_α(g''(x)) = pr_α(g'(g(x))).

    FORMULE (4) (E.III.52) g'' = g' ∘ g, lue coordonnée par coordonnée (α∈J').
    g = canonique de restriction à J ;  g'' = canonique de restriction à J' (sur E) ;
    g' = canonique de restriction à J' du système RESTREINT à J (sur E'=lim←_J).

    Chaîne fidèle à Bourbaki :
        pr_α(g''(x)) = f_α(x)            [(3) pour g'', α∈J']
                     = pr_α(g(x))        [f_α=pr_α sur lim←_I + (3) pour g, α∈J⊃J']
                     = f'_α(g(x))        [f'_α=pr_α sur E'=lim←_J, g(x)∈E', α∈J]
                     = pr_α(g'(g(x))).    [(3) pour g', g(x)∈E', α∈J'].

    HYPOTHÈSES (toutes HONNÊTES, satisfiables) :
      • α∈J' et α∈J (J'⊂J : l'indice est commun) ;
      • x∈lim←_I (domaine de g, g'') ;
      • g(x)∈lim←_J = E' (codomaine de g = domaine de g', g(x) est bien dans E').
    Conclusion NEUVE (pr_α(g''(x))=pr_α(g'(g(x))) n'est aucune des hypothèses).
    """
    if leq is None:
        leq = _gleq()
    vE, vf, vi, vJ, vJp = _t(Efam), _t(f), _t(i), _t(J), _t(Jp)
    va, vx = var(a), _t(x)
    # système restreint à J (support de E'=lim←_J et de g')
    Er = C.restriction_systeme_indices(vE, vf, vJ)
    gx = E.valeur(C.application_canonique_g(vE, vf, vJ), vx)       # g(x)

    # (i)  pr_α(g''(x)) = f_α(x)        [(3) pour g'' = restriction à J', α∈J']
    eq_gpp = _coord_g_au_point(vE, vf, leq, vi, vJp, va, vx)       # pr_α(g''(x))=f_α(x)
    # (ii) f_α(x) = pr_α(g(x))          [(3) pour g, α∈J] renversée
    eq_g = _coord_g_au_point(vE, vf, leq, vi, vJ, va, vx)          # pr_α(g(x))=f_α(x)
    pra_gx = E.projection_indice(gx, va)
    fa_x = C.application_canonique_proj_valeur(vE, vf, va, vx)     # f_α(x)
    eq_g_sym = N.modus_ponens(eq_g, symetrie(pra_gx, fa_x))        # f_α(x)=pr_α(g(x))
    # (iii) pr_α(g(x)) = f'_α(g(x))     [f'_α=pr_α sur E'=lim←_J, g(x)∈E', α∈J] renversée
    eq_fp = _canon_proj_au_point(Er, vf, leq, vJ, va, gx)         # f'_α(g(x))=pr_α(g(x))
    fpa_gx = C.application_canonique_proj_valeur(Er, vf, va, gx)   # f'_α(g(x))
    eq_fp_sym = N.modus_ponens(eq_fp, symetrie(fpa_gx, pra_gx))    # pr_α(g(x))=f'_α(g(x))
    # (iv) f'_α(g(x)) = pr_α(g'(g(x)))  [(3) pour g' sur Er, restriction à J', g(x)∈E', α∈J'] renversée
    eq_gp = _coord_g_au_point(Er, vf, leq, vJ, vJp, va, gx)        # pr_α(g'(g(x)))=f'_α(g(x))
    gp_gx = E.valeur(C.application_canonique_g(Er, vf, vJp), gx)   # g'(g(x))
    pra_gp_gx = E.projection_indice(gp_gx, va)
    eq_gp_sym = N.modus_ponens(eq_gp, symetrie(pra_gp_gx, fpa_gx)) # f'_α(g(x))=pr_α(g'(g(x)))

    # chaîne : pr_α(g''(x)) = f_α(x) = pr_α(g(x)) = f'_α(g(x)) = pr_α(g'(g(x)))
    ch1 = composer_egalites(eq_gpp, eq_g_sym)             # pr_α(g''(x))=pr_α(g(x))
    ch2 = composer_egalites(ch1, eq_fp_sym)               # pr_α(g''(x))=f'_α(g(x))
    return composer_egalites(ch2, eq_gp_sym)              # pr_α(g''(x))=pr_α(g'(g(x)))


# ════════════════════════════════════════════════════════════════════════════
#  2.  PROPOSITION 4 (E.III.57) — pas-clé de la condition recollée (14)+(15)⇒(1).
# ════════════════════════════════════════════════════════════════════════════
def prop4_condition_recollee(Efam="E", fL="fL", hL="hL", fIL="fIL", leq=None,
                             i="I", a="a", b="b", lam="lam", mu="mu", z="zz"):
    """{ (15) en (α,β,λ) :  pr^λ_α(z) = f^λ_{αβ}(pr^λ_β(z)) ;
         (14) en (α,λ,μ) :  pr^λ_α(z) = h^{λμ}_α(pr^μ_α(z)) ;
         (11) factorisation au point pr^μ_β(z) :
              f^{λμ}_{αβ}(pr^μ_β(z)) = f^λ_{αβ}(h^{λμ}_β(pr^μ_β(z))) }
       ⊢  pr^λ_α(z) = f^{λμ}_{αβ}(pr^μ_β(z)).

    PAS-CLÉ de la réciproque de la Proposition 4 (E.III.57) : les conditions (14) et
    (15) du système I×L se RECOLLENT, via la factorisation (11)
    f^{λμ}_{αβ} = f^λ_{αβ}∘h^{λμ}_β, en la condition (1) du système produit
    (« z∈E=lim←_{α,λ} »).  Chaîne EXACTE de Bourbaki :
        pr^λ_α(z) = f^λ_{αβ}(pr^λ_β(z))                       [(15)]
                  = f^λ_{αβ}(h^{λμ}_β(pr^μ_β(z)))             [(14) en β, sous f^λ_{αβ}]
                  = f^{λμ}_{αβ}(pr^μ_β(z)).                    [(11), renversée].

    CODAGE des transitions :
      f^λ_{αβ}   = appl_proj(fL, (α,λ), (β,λ))  — transition du système λ-fixé ;
      h^{λμ}_α   = appl_proj(hL, (α,λ), (α,μ))  — transition L à α-fixé ;
      f^{λμ}_{αβ}= appl_proj(fIL, (α,λ), (β,μ)) — transition du système produit.
    pr^λ_α(z) := projection_indice(z, (α,λ)).  (14)/(15)/(11) portées en HYPOTHÈSES
    explicites (la donnée (11) du système, jamais postulée).  Conclusion NEUVE.
    """
    if leq is None:
        leq = _gleq()
    vfL, vhL, vfIL = _t(fL), _t(hL), _t(fIL)
    va, vb = var(a), var(b)
    vlam, vmu, vz = var(lam), var(mu), _t(z)
    # indices produit
    al = E.couple(va, vlam)        # (α,λ)
    bl = E.couple(vb, vlam)        # (β,λ)
    bm = E.couple(vb, vmu)         # (β,μ)
    am = E.couple(va, vmu)         # (α,μ)
    # projections
    prla_z = E.projection_indice(vz, al)    # pr^λ_α(z)
    prlb_z = E.projection_indice(vz, bl)    # pr^λ_β(z)
    prmb_z = E.projection_indice(vz, bm)    # pr^μ_β(z)
    # transitions
    fl_ab = L.appl_proj(vfL, al, bl)        # f^λ_{αβ} : E^λ_β → E^λ_α
    hl_b = L.appl_proj(vhL, bl, bm)         # h^{λμ}_β : E^μ_β → E^λ_β
    fil_ab = L.appl_proj(vfIL, al, bm)      # f^{λμ}_{αβ} : E^μ_β → E^λ_α

    # (15) : pr^λ_α(z) = f^λ_{αβ}(pr^λ_β(z))
    H15 = N.assume(egal(prla_z, E.valeur(fl_ab, prlb_z)))
    # (14) en β : pr^λ_β(z) = h^{λμ}_β(pr^μ_β(z))
    H14b = N.assume(egal(prlb_z, E.valeur(hl_b, prmb_z)))
    # f^λ_{αβ}(pr^λ_β(z)) = f^λ_{αβ}(h^{λμ}_β(pr^μ_β(z)))   [congruence sous f^λ_{αβ}]
    cong = N.modus_ponens(H14b, congruence_terme(
        prlb_z, E.valeur(hl_b, prmb_z), E.valeur(fl_ab, var("w")), "w"))
    # (11) au point : f^{λμ}_{αβ}(pr^μ_β(z)) = f^λ_{αβ}(h^{λμ}_β(pr^μ_β(z)))
    H11 = N.assume(egal(E.valeur(fil_ab, prmb_z),
                        E.valeur(fl_ab, E.valeur(hl_b, prmb_z))))
    H11_sym = N.modus_ponens(H11, symetrie(
        E.valeur(fil_ab, prmb_z), E.valeur(fl_ab, E.valeur(hl_b, prmb_z))))
    # chaîne : pr^λ_α(z) = f^λ_{αβ}(pr^λ_β(z)) = f^λ_{αβ}(h^{λμ}_β(pr^μ_β(z))) = f^{λμ}_{αβ}(pr^μ_β(z))
    ch1 = composer_egalites(H15, cong)       # pr^λ_α(z) = f^λ_{αβ}(h^{λμ}_β(pr^μ_β(z)))
    return composer_egalites(ch1, H11_sym)   # pr^λ_α(z) = f^{λμ}_{αβ}(pr^μ_β(z))


# Résultats DURS introduits/cernés mais NON prouvés (honnêteté).
REPORTES = [
    "Formule (4) g''=g'∘g (E.III.52) : prouvée COORDONNÉE PAR COORDONNÉE "
    "(formule_4_coordonnee) ; l'égalité d'APPLICATIONS g''=g'∘g (extensionnalité sur "
    "la limite E''⊂∏_{J'}) reste REPORTÉE.",
    "Proposition 4 (E.III.57) bijection canonique F→E des doubles limites : le PAS-CLÉ "
    "(14)+(15)+(11) ⇒ condition (1) du système I×L est prouvé (prop4_condition_recollee) ; "
    "la BIJECTION canonique complète (identification F=∏_λ F^λ ⊃ F ≅ E) reste REPORTÉE "
    "(extensionnalité produit + égalité d'ensembles F=E).",
    "Corollaires 1/2 de la Prop. 4 (E.III.57, formules (17)/(18)) — REPORTÉS "
    "(se réduisent à la Prop. 4 par le même recollement).",
]


__all__ = [
    "formule_4_coordonnee",
    "prop4_condition_recollee",
    "REPORTES",
]
