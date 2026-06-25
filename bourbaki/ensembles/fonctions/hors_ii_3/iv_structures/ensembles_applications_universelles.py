"""§IV.3.1 — Applications universelles : fragment OBJET.

Le §IV.3 est, comme tout le chapitre IV, ABSTRAIT AU PLUS HAUT DEGRÉ.  La donnée
d'un problème d'application universelle est une donnée (Σ, σ, α) où :
  • Σ est une ESPÈCE DE STRUCTURE (paramètre quantifié sur les espèces : méta) ;
  • σ une notion de MORPHISME pour Σ (terme générique σ{x,y,s,t}, postulé MO_I–III) ;
  • α{x,s} un TERME GÉNÉRIQUE définissant les « α-applications » (postulé QM_I–II).
Ces objets — échelons, structures génériques, espèces, transportabilité — relèvent
du MÉTALANGAGE DES ESPÈCES et ne sont PAS exprimables par une seule formule du
fragment objet {var,τ,=,∈,¬,∨,∃}.  Ils sont REPORTÉS honnêtement (cf. rapport).

CE QUI EST EXPRIMABLE — et que l'on encode + prouve ici — c'est la STRUCTURE
LOGIQUE de la propriété universelle elle-même, indépendamment du contenu de Σ, σ,
α.  Exactement comme `ensembles_morphismes`/`ensembles_isomorphismes` encodent le
σ-morphisme/isomorphisme pour un échelon relationnel concret, on PARAMÈTRE ici la
propriété universelle par des PRÉDICATS abstraits (callables Python → Formule) :
  • `morph(f)`    : « f est un morphisme de F_E dans F »   (clause σ-morphisme) ;
  • `alpha(phi)`  : « φ est une α-application de E dans F » (clause α-application) ;
  • `fact(f)`     : « φ = f ∘ φ_E »                         (clause de factorisation).
Le lecteur passe SES prédicats (p.ex. ceux d'`ensembles_morphismes` pour Σ
relationnelle) ; les THÉORÈMES prouvés ici valent QUEL QUE SOIT leur contenu, car
ils ne reposent que sur la structure ∃!/∀ de (AU), (AU_I′), (AU_II′).

DÉFINITIONS (prédicats, niveau objet) — verbatim Texte.tex §IV.3.1 :
  • (AU)     est_universel : « pour toute α-application φ de E dans un Σ-ensemble F,
             il existe un morphisme et UN SEUL f tel que φ = f∘φ_E ».
             Codée  (∃!f)(morph(f) et fact(f))  = (∃f)(corps) et (unicité).
  • (AU_I′)  au_i_prime : « il existe un morphisme f tel que φ = f∘φ_E »   (∃f)(corps).
  • (AU_II′) au_ii_prime : « deux morphismes qui coïncident dans φ_E(E) sont égaux ».
             Au niveau du corps de factorisation : deux f,f' factorisant φ sont égaux,
             soit  (∀f)(∀f')((corps{f} et corps{f'}) ⇒ f=f').

THÉORÈMES DIRECTS certifiés par le noyau (purement logiques, ∃!/∀) :
  • au_implique_au_i_prime  : (AU) ⟹ (AU_I′).
       « Il est clair que (AU) entraîne (AU_I′) » (Texte.tex) — projection de la
       composante d'EXISTENCE hors de l'existence-UNIQUE.
  • au_implique_au_ii_prime : (AU) ⟹ (AU_II′).
       La composante d'UNICITÉ de (AU) EST (AU_II′) sur le corps de factorisation.
  • au_i_et_ii_implique_au   : ((AU_I′) et (AU_II′)) ⟹ (AU).
       « si ces deux conditions sont réalisées, le morphisme f … est unique d'après
       (AU_II′) » — reconstruit l'existence-unique.  Avec les deux précédents :
       (AU) ⟺ ((AU_I′) et (AU_II′)) — le critère équivalent du Texte.tex.

REPORTÉ honnêtement (cf. champ « reportes ») :
  • La quantification « pour tout Σ-ensemble F / toute α-application φ » EST une
    quantification sur les STRUCTURES (méta).  Ici les théorèmes sont prouvés sur
    le CORPS (à F, φ fixés) ; le préfixe (∀F)(∀φ) « Σ-ensemble » n'est pas un ∀
    objet (F porte une structure d'espèce Σ).  C'est la part fidèlement exprimable.
  • Unicité À UN ISOMORPHISME UNIQUE PRÈS (Texte.tex, via CST8) : exige la
    manipulation f₂∘f₁ = Id et le critère CST8 (bijection-morphisme ⇒ iso) —
    machinerie de composition + transport de structure HORS fragment objet ici.
  • (CU_I)–(CU_III), CST22 (EXISTENCE d'une solution), CST23 (injectivité de φ_E),
    Σ-ensemble libre, corps des fractions, produit tensoriel, Stone-Čech : LOURDS
    et/ou méta (produits d'espèces, cardinal majorant, structures permises).
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import var, egal, et, impl, existe, pourtout
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (conjonction_intro, conjonction_elim_gauche,
                               conjonction_elim_droite, instancie,
                               instanciation)
from bourbaki.logique.i_3_quantifies.tactiques_abrege_quantif import existe_elimination


# ── corps de factorisation : morph(f) et (φ = f∘φ_E) ──────────────────────────
def corps_factorisation(morph, fact, f="f"):
    """« f est un morphisme de F_E dans F tel que φ = f∘φ_E » := morph(f) et fact(f).

    morph, fact : callables Terme→Formule (le lecteur passe ses prédicats σ / =)."""
    vf = var(f)
    return et(morph(vf), fact(vf))


# ── (AU_I′) : (∃f)(morph(f) et fact(f)) ───────────────────────────────────────
# @livre Ch.IV §3.2 Crit.- | E IV.23 L.19-20 | PDF p.226
def au_i_prime(morph, fact, f="f"):
    """(AU_I′) : « il existe un morphisme f de F_E dans F tel que φ = f∘φ_E »
    (Texte.tex §IV.3.1).  Codé (∃f)(morph(f) et fact(f))."""
    return existe(f, corps_factorisation(morph, fact, f))


# ── (AU_II′) : (∀f)(∀f')((corps{f} et corps{f'}) ⇒ f=f') ──────────────────────
# @livre Ch.IV §3.2 Crit.- | E IV.23 L.21-22 | PDF p.226
def au_ii_prime(morph, fact, f="f", g="fp"):
    """(AU_II′) : « deux morphismes f, f' de F_E dans F qui coïncident dans φ_E(E)
    sont égaux » (Texte.tex §IV.3.1).  Au niveau du corps : deux factorisations de
    φ sont égales.  Codé (∀f)(∀f')((corps{f} et corps{f'}) ⇒ f=f')."""
    vf, vg = var(f), var(g)
    cf = corps_factorisation(morph, fact, f)
    cg = corps_factorisation(morph, fact, g)
    return pourtout(f, pourtout(g, impl(et(cf, cg), egal(vf, vg))))


# ── (AU) : (∃!f)(morph(f) et fact(f)) = (AU_I′) et (AU_II′) ────────────────────
# @livre Ch.IV §3.2 Def.- | E IV.23 L.1-2 | PDF p.226
def est_universel(morph, fact, f="f", g="fp"):
    """(AU) : « il existe un morphisme et UN SEUL f de F_E dans F tel que φ = f∘φ_E »
    (Texte.tex §IV.3.1, condition d'universalité).  Codé comme l'existence-unique de
    Bourbaki :  (∃f)(corps) et (∀f)(∀f')((corps{f} et corps{f'}) ⇒ f=f')
    soit exactement (AU_I′) et (AU_II′)."""
    return et(au_i_prime(morph, fact, f), au_ii_prime(morph, fact, f, g))


# ── THÉORÈME : (AU) ⟹ (AU_I′)  (« (AU) entraîne (AU_I′) ») ─────────────────────
# @livre Ch.IV §3.2 Demo.- | E IV.23 L.24-25 | PDF p.226
def au_implique_au_i_prime(morph, fact, f="f", g="fp"):
    """⊢ (AU) ⇒ (AU_I′).   (Texte.tex : « il est clair que (AU) entraîne (AU_I′) ».)

    (AU) = (AU_I′) et (AU_II′) ; projection gauche de la conjonction."""
    au = est_universel(morph, fact, f, g)
    h = N.assume(au)
    return N.loi_deduction(au, conjonction_elim_gauche(h))   # ⊢ (AU) ⇒ (AU_I′)


# ── THÉORÈME : (AU) ⟹ (AU_II′)  (la composante d'unicité de (AU)) ──────────────
def au_implique_au_ii_prime(morph, fact, f="f", g="fp"):
    """⊢ (AU) ⇒ (AU_II′).   La composante d'UNICITÉ de l'existence-unique (AU) EST
    exactement (AU_II′) sur le corps de factorisation (Texte.tex : l'unicité de f
    dans (AU) donne que deux factorisations coïncidant dans φ_E(E) sont égales)."""
    au = est_universel(morph, fact, f, g)
    h = N.assume(au)
    return N.loi_deduction(au, conjonction_elim_droite(h))   # ⊢ (AU) ⇒ (AU_II′)


# ── THÉORÈME : ((AU_I′) et (AU_II′)) ⟹ (AU)  (critère équivalent) ──────────────
def au_i_et_ii_implique_au(morph, fact, f="f", g="fp"):
    """⊢ ((AU_I′) et (AU_II′)) ⇒ (AU).   (Texte.tex : « si ces deux conditions sont
    réalisées, le morphisme f dont l'existence est assurée par (AU_I′) est unique
    d'après (AU_II′) ».)  Reconstruit l'existence-UNIQUE = (AU) à partir de
    l'existence (AU_I′) et de l'unicité (AU_II′)."""
    a1 = au_i_prime(morph, fact, f)
    a2 = au_ii_prime(morph, fact, f, g)
    h = N.assume(et(a1, a2))
    au = conjonction_intro(conjonction_elim_gauche(h), conjonction_elim_droite(h))
    return N.loi_deduction(et(a1, a2), au)                   # ⊢ ((AU_I′) et (AU_II′)) ⇒ (AU)


# ── THÉORÈME : (AU) ⟹ ((AU_I′) et (AU_II′))  (l'autre sens du critère) ─────────
def au_implique_au_i_et_ii(morph, fact, f="f", g="fp"):
    """⊢ (AU) ⇒ ((AU_I′) et (AU_II′)).   Sens réciproque du critère équivalent :
    (AU) est par définition la conjonction de (AU_I′) et (AU_II′)."""
    au = est_universel(morph, fact, f, g)
    h = N.assume(au)
    return N.loi_deduction(au,
        conjonction_intro(conjonction_elim_gauche(h), conjonction_elim_droite(h)))


# ── THÉORÈME : (AU) ⟹ (∃ morphisme factorisant)  pour UNE α-application donnée ─
def factorisation_existe(morph, fact, f="f", g="fp"):
    """⊢ (AU) ⇒ (∃f)(morph(f) et (φ = f∘φ_E)).   Conséquence directe de
    au_implique_au_i_prime : toute α-application φ de E (dans F) SE FACTORISE par
    φ_E (Texte.tex : « toute α-application de E dans un Σ-ensemble F se prolonge en
    un morphisme de F_E dans F »)."""
    return au_implique_au_i_prime(morph, fact, f, g)


# ── THÉORÈME : (AU) + deux factorisations ⟹ égalité  (unicité appliquée) ───────
def factorisation_unique(morph, fact, s, t, f="f", g="fp"):
    """{(AU)} ⊢ (corps{S} et corps{T}) ⇒ S=T,  pour deux morphismes-témoins S, T.

    Instancie la composante d'unicité (AU_II′) de (AU) aux deux termes S et T : si
    S et T factorisent tous deux φ, alors S=T (UNICITÉ de la factorisation, contenu
    de « f est unique d'après (AU_II′) »).  S, T : termes (morphismes témoins)."""
    au = est_universel(morph, fact, f, g)
    h = N.assume(au)
    a2 = conjonction_elim_droite(h)                          # (AU_II′)  (sous {AU})
    inst = instancie(instancie(a2, s), t)                    # (corps{S} et corps{T}) ⇒ S=T
    return inst
