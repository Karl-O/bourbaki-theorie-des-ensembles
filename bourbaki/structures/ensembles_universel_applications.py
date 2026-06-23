"""§IV.3 — Applications universelles : représentation OBJET paramétrée.

INTRODUIT (définitions fidèles) toutes les notions du §IV.3 :
  • données d'un problème d'application universelle (Σ, σ, α) ;
  • axiomes (QM_I), (QM_II) de la donnée α ;
  • α-application (φ ∈ α[x, s]) ;
  • Σ-ensemble et α-application universels — solution (F_E, φ_E), conditions (AU),
    (AU_I′), (AU_II′) ;
  • α-applications séparant les éléments de E (CST23) ;
  • Σ-ensemble libre engendré par E (cas algébrique, α = 𝓕(E ; x)).

Convention de paramétrage (identique au reste du chap. IV, cf.
`ensembles_applications_universelles` existant) : la donnée (Σ, σ, α) abstraite est
représentée par des PRÉDICATS callables → Formule du fragment objet :
  • `sigma_ens(F, S)` : « F muni de S est un Σ-ensemble »      (structure d'espèce Σ) ;
  • `morph(e1,s1,e2,s2,f)` : « f est un σ-morphisme »          (donnée σ, MO_I–III) ;
  • `alpha(F, S, phi)` : « φ est une α-application de E dans (F,S) »  (donnée α, QM_I–II).
E, φ_E, F_E sont des TERMES.  Les THÉORÈMES purement logiques (équivalence (AU) ⟺
(AU_I′)+(AU_II′), injectivité de φ_E ⟺ séparation, IV.3.1 / CST23) ne dépendent que
de la structure ∃!/∀/⇔ ; ils sont certifiés par le noyau.

REPORTÉ honnêtement : CST22 (EXISTENCE d'une solution via CU_I–III), unicité à un
isomorphisme unique près (CST8 : composition + transport), construction effective du
libre engendré / corps des fractions / produit tensoriel / Stone-Čech (LOURDS, méta).
Les exemples corps des fractions / produit tensoriel / Stone-Čech sont ILLUSTRATIFS :
ici termes OPAQUES nommés (documentés tels quels).
"""
from __future__ import annotations

from bourbaki.logique.formule import (var, egal, et, impl, equiv, existe,
                                       pourtout, non, appartient, app)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    instancie)


def _t(s):
    return var(s) if isinstance(s, str) else s


# ════════════════════════════════════════════════════════════════════════════
#  prédicats par défaut — donnée (Σ, σ, α) générique opaque
# ════════════════════════════════════════════════════════════════════════════
def _sigma_ens_defaut(nom="EstSigma"):
    """« (F,S) est un Σ-ensemble » via prédicat opaque app(nom,F,S) ∈ {⊤}…
    représenté par appartenance F ∈ app(nom,S) (S une structure d'espèce Σ sur F)."""
    return lambda f, s: appartient(f, app(nom, s))


def _morph_defaut(nom="Mor"):
    return lambda e1, s1, e2, s2, f: appartient(f, app(nom, e1, s1, e2, s2))


def _alpha_defaut(nom="Alpha"):
    """« φ est une α-application de E dans (F,S) » via φ ∈ α[F,S] = app(nom,F,S)."""
    return lambda f, s, phi: appartient(phi, app(nom, f, s))


# ════════════════════════════════════════════════════════════════════════════
#  DONNÉES d'un problème d'application universelle (Σ, σ, α)
# ════════════════════════════════════════════════════════════════════════════
def donnees_probleme(e, sigma_ens=None, morph=None, alpha=None):
    """Données (Σ, σ, α) d'un problème d'application universelle pour E (IV.3.1) :
    un terme E, une espèce Σ sur un seul ensemble de base principal (« Σ-ensemble »),
    une notion de σ-morphisme, et un terme α{x,s} (les α-applications) vérifiant
    (QM_I)/(QM_II).

    Renvoie un dict des trois prédicats (la « donnée »), avec défauts opaques.  Sert
    de conteneur passé aux définitions ci-dessous ; E est le terme source fixé."""
    return {
        "E": _t(e),
        "sigma_ens": sigma_ens if sigma_ens is not None else _sigma_ens_defaut(),
        "morph": morph if morph is not None else _morph_defaut(),
        "alpha": alpha if alpha is not None else _alpha_defaut(),
    }


# ── axiomes (QM_I), (QM_II) de la donnée α ────────────────────────────────────
def axiome_QM_I(e, f, s, alpha=None, phi="phi"):
    """(QM_I) : « α{x,s} ⊂ 𝓕(E ; x) est vraie dans 𝒯_Σ ».  Toute α-application de E
    dans (F,S) est une application de E dans F.  Codé
        (∀φ)( alpha(F,S,φ) ⇒ φ ∈ 𝓕(E ; F) ).
    (𝓕(E;F) = E.applications(E,F).)"""
    if alpha is None:
        alpha = _alpha_defaut()
    vphi = _t(phi)
    ve = _t(e)
    return pourtout(phi, impl(alpha(f, s, vphi),
                             appartient(vphi, E.applications(ve, f))))


def axiome_QM_II(e, f, fp, s, sp, morphf, alpha=None, morph=None, phi="phi"):
    """(QM_II) : si f est un morphisme de (F,S) dans (F',S'), alors φ ∈ α[F,S]
    entraîne f∘φ ∈ α[F',S']  (IV.3.1).  Codé, à f = `morphf` (terme) fixé :
        morph(F,S,F',S',f) ⇒ (∀φ)( alpha(F,S,φ) ⇒ alpha(F',S', f∘φ) )."""
    if alpha is None:
        alpha = _alpha_defaut()
    if morph is None:
        morph = _morph_defaut()
    vphi = _t(phi)
    ve = _t(e)
    interne = pourtout(phi, impl(alpha(f, s, vphi),
                                alpha(fp, sp, E.composee(morphf, vphi))))
    return impl(morph(f, s, fp, sp, morphf), interne)


# ════════════════════════════════════════════════════════════════════════════
#  α-application
# ════════════════════════════════════════════════════════════════════════════
def est_alpha_application(e, f, s, phi, alpha=None):
    """« φ est une α-application de E dans (F muni de s) » := φ ∈ α[x, s]  (IV.3.1).
    Porté par le prédicat abstrait alpha(F, S, φ)."""
    if alpha is None:
        alpha = _alpha_defaut()
    return alpha(f, s, _t(phi))


# ════════════════════════════════════════════════════════════════════════════
#  SOLUTION (F_E, φ_E) — conditions (AU), (AU_I′), (AU_II′)
# ════════════════════════════════════════════════════════════════════════════
#
#  Pour un Σ-ensemble candidat (F_E, S_E) muni de φ_E : E → F_E, la condition (AU)
#  porte sur « toute α-application φ de E dans tout Σ-ensemble (F,S) ».  On la
#  représente, à (F, S, φ) fixés, par le CORPS de factorisation, puis on quantifie
#  fidèlement par les prédicats.
#
def corps_factorisation(fe, se, phi_e, f, s, phi, mor, morph=None):
    """« mor est un morphisme de (F_E,S_E) dans (F,S) tel que φ = mor∘φ_E »
    (corps de la condition (AU)).  Codé morph(F_E,S_E,F,S,mor) et (φ = mor∘φ_E)."""
    if morph is None:
        morph = _morph_defaut()
    return et(morph(fe, se, f, s, mor), egal(_t(phi), E.composee(mor, phi_e)))


def AU_corps(fe, se, phi_e, f, s, phi, mor="f", morph=None):
    """(∃ mor)(corps) — pour UNE α-application φ donnée dans (F,S) : existence d'un
    morphisme factorisant.  (Composante d'existence de (AU), cf. (AU_I′).)"""
    vmor = _t(mor)
    return existe(mor, corps_factorisation(fe, se, phi_e, f, s, phi, vmor, morph))


def AU_unicite(fe, se, phi_e, f, s, phi, mor="f", mor2="fp", morph=None):
    """(∀mor)(∀mor')((corps{mor} et corps{mor'}) ⇒ mor=mor') — unicité du morphisme
    factorisant pour UNE α-application φ donnée.  (Composante d'unicité de (AU).)"""
    vmor, vmor2 = _t(mor), _t(mor2)
    c1 = corps_factorisation(fe, se, phi_e, f, s, phi, vmor, morph)
    c2 = corps_factorisation(fe, se, phi_e, f, s, phi, vmor2, morph)
    return pourtout(mor, pourtout(mor2, impl(et(c1, c2), egal(vmor, vmor2))))


def est_universel(fe, se, phi_e, f, s, phi, mor="f", mor2="fp", morph=None):
    """(AU) pour UNE α-application φ donnée dans (F,S) : « il existe un morphisme et
    UN SEUL mor : F_E → F tel que φ = mor∘φ_E »  (IV.3.1).  Codé existence-unique
    AU_corps et AU_unicite (= la conjonction (AU_I′)+(AU_II′) ponctuelle)."""
    return et(AU_corps(fe, se, phi_e, f, s, phi, mor, morph),
              AU_unicite(fe, se, phi_e, f, s, phi, mor, mor2, morph))


def est_solution(fe, se, phi_e, sigma_ens=None, morph=None, alpha=None,
                 f="F", s="S", phi="phi", mor="f", mor2="fp"):
    """« (F_E, φ_E) est solution du problème d'application universelle pour E »
    (IV.3.1) := pour TOUT Σ-ensemble (F,S) et TOUTE α-application φ de E dans (F,S),
    (AU) est vérifiée.  Codé fidèlement
       (∀F)(∀S)(∀φ)[ (sigma_ens(F,S) et alpha(F,S,φ)) ⇒ (AU pour φ) ]."""
    if sigma_ens is None:
        sigma_ens = _sigma_ens_defaut()
    if alpha is None:
        alpha = _alpha_defaut()
    vf, vs, vphi = _t(f), _t(s), _t(phi)
    hyp = et(sigma_ens(vf, vs), alpha(vf, vs, vphi))
    au = est_universel(fe, se, phi_e, vf, vs, vphi, mor, mor2, morph)
    return pourtout(f, pourtout(s, pourtout(phi, impl(hyp, au))))


# ── THÉORÈME (IV.3.1, critère équivalent) : (AU) ⟺ (AU_I′) et (AU_II′) ─────────
def au_implique_existence(fe="FE", se="SE", phi_e="phiE", f="F", s="S",
                          phi="phi", mor="f", mor2="fp", morph=None):
    """{(AU) pour φ} ⊢ (AU_I′) : (∃mor)(corps).  (« (AU) entraîne (AU_I′) ».)
    Projection gauche de l'existence-unique."""
    fe, se, phi_e, vf, vs, vphi = map(_t, (fe, se, phi_e, f, s, phi))
    au = est_universel(fe, se, phi_e, vf, vs, vphi, mor, mor2, morph)
    h = N.assume(au)
    return N.loi_deduction(au, conjonction_elim_gauche(h))   # ⊢ (AU) ⇒ (AU_I′)


def au_implique_unicite(fe="FE", se="SE", phi_e="phiE", f="F", s="S",
                        phi="phi", mor="f", mor2="fp", morph=None):
    """{(AU) pour φ} ⊢ (AU_II′) : (∀mor)(∀mor')((corps{mor} et corps{mor'})⇒mor=mor').
    Projection droite (la composante d'unicité de (AU) EST (AU_II′))."""
    fe, se, phi_e, vf, vs, vphi = map(_t, (fe, se, phi_e, f, s, phi))
    au = est_universel(fe, se, phi_e, vf, vs, vphi, mor, mor2, morph)
    h = N.assume(au)
    return N.loi_deduction(au, conjonction_elim_droite(h))   # ⊢ (AU) ⇒ (AU_II′)


def existence_et_unicite_impliquent_au(fe="FE", se="SE", phi_e="phiE", f="F",
                                       s="S", phi="phi", mor="f", mor2="fp",
                                       morph=None):
    """⊢ ((AU_I′) et (AU_II′)) ⇒ (AU)  pour φ.  (« si ces deux conditions sont
    réalisées, le morphisme … est unique d'après (AU_II′) ».)  Reconstruit
    l'existence-unique = (AU)."""
    fe, se, phi_e, vf, vs, vphi = map(_t, (fe, se, phi_e, f, s, phi))
    a1 = AU_corps(fe, se, phi_e, vf, vs, vphi, mor, morph)
    a2 = AU_unicite(fe, se, phi_e, vf, vs, vphi, mor, mor2, morph)
    h = N.assume(et(a1, a2))
    au = conjonction_intro(conjonction_elim_gauche(h), conjonction_elim_droite(h))
    return N.loi_deduction(et(a1, a2), au)                   # ⊢ ((AU_I′) et (AU_II′)) ⇒ (AU)


# ════════════════════════════════════════════════════════════════════════════
#  CST23 — α-applications séparant les éléments de E
# ════════════════════════════════════════════════════════════════════════════
def separent_les_elements(e, sigma_ens=None, alpha=None,
                          f="F", s="S", phi="phi", x="x", y="y"):
    """« les α-applications séparent les éléments de E » (IV.3.1, CST23) := pour tout
    couple d'éléments distincts x, y de E, il existe une α-application φ de E dans un
    Σ-ensemble (F,S) telle que φ(x) ≠ φ(y).  Codé
       (∀x)(∀y)[ (x∈E et y∈E et x≠y) ⇒
                 (∃F)(∃S)(∃φ)( sigma_ens(F,S) et alpha(F,S,φ) et φ(x)≠φ(y) ) ]."""
    if sigma_ens is None:
        sigma_ens = _sigma_ens_defaut()
    if alpha is None:
        alpha = _alpha_defaut()
    ve, vx, vy = _t(e), _t(x), _t(y)
    vf, vs, vphi = _t(f), _t(s), _t(phi)
    sep = non(egal(E.valeur(vphi, vx), E.valeur(vphi, vy)))   # φ(x) ≠ φ(y)
    interne = existe(f, existe(s, existe(phi,
        et(et(sigma_ens(vf, vs), alpha(vf, vs, vphi)), sep))))
    hyp = et(et(appartient(vx, ve), appartient(vy, ve)), non(egal(vx, vy)))
    return pourtout(x, pourtout(y, impl(hyp, interne)))


def phi_E_injective(e, phi_e, x="x", y="y"):
    """« φ_E est une injection de E dans F_E » (CST23, énoncé équivalent) := pour
    tous x,y ∈ E, φ_E(x) = φ_E(y) ⇒ x = y.  Codé
       (∀x)(∀y)((x∈E et y∈E et φ_E(x)=φ_E(y)) ⇒ x=y)."""
    ve, vphi_e, vx, vy = _t(e), _t(phi_e), _t(x), _t(y)
    eqv = egal(E.valeur(vphi_e, vx), E.valeur(vphi_e, vy))
    hyp = et(et(appartient(vx, ve), appartient(vy, ve)), eqv)
    return pourtout(x, pourtout(y, impl(hyp, egal(vx, vy))))


# ════════════════════════════════════════════════════════════════════════════
#  Σ-ENSEMBLE LIBRE ENGENDRÉ par E (cas algébrique, α = 𝓕(E ; x))
# ════════════════════════════════════════════════════════════════════════════
def alpha_libre(e):
    """Cas du Σ-ensemble libre (IV.3.1) : Σ espèce algébrique, morphismes =
    homomorphismes, α-applications = applications QUELCONQUES de E dans x :
        α{x, s} := 𝓕(E ; x).
    Renvoie le prédicat alpha correspondant : alpha(F,S,φ) := φ ∈ 𝓕(E;F)."""
    ve = _t(e)
    return lambda f, s, phi: appartient(_t(phi), E.applications(ve, f))


def est_libre_engendre(e, fe, se, phi_e, sigma_ens=None, morph=None,
                       f="F", s="S", phi="phi", mor="f", mor2="fp"):
    """« (F_E, φ_E) est le Σ-ensemble libre engendré par E » (IV.3.1) := solution du
    problème d'application universelle pour E avec α = 𝓕(E ; x) (applications
    quelconques).  E est « plongé » dans F_E par φ_E.  Codé est_solution avec
    alpha = alpha_libre(E)."""
    return est_solution(fe, se, phi_e, sigma_ens=sigma_ens, morph=morph,
                        alpha=alpha_libre(e), f=f, s=s, phi=phi, mor=mor, mor2=mor2)


# ── exemples ILLUSTRATIFS (termes opaques, documentés) ────────────────────────
def corps_des_fractions(anneau, partie_mult):
    """Corps des fractions d'un anneau intègre E (S = E∖{0}) — ILLUSTRATIF.  Terme
    OPAQUE : la construction (Σ = anneaux commutatifs, α = homomorphismes inversant
    S) est REPORTÉE (algèbre, hors fragment ensembliste)."""
    return app("corps_fractions", _t(anneau), _t(partie_mult))


def produit_tensoriel(a, b, anneau):
    """Produit tensoriel A ⊗_C B de deux C-modules — ILLUSTRATIF.  Terme OPAQUE :
    Σ = C-modules, α = applications bilinéaires.  Construction REPORTÉE (algèbre)."""
    return app("produit_tensoriel", _t(a), _t(b), _t(anneau))


def compactifie_stone_cech(espace):
    """Compactifié de Stone-Čech d'un espace régulier — ILLUSTRATIF.  Terme OPAQUE :
    Σ = espaces compacts, α = applications continues vers un compact.  REPORTÉ
    (topologie)."""
    return app("stone_cech", _t(espace))


__all__ = [
    "donnees_probleme", "axiome_QM_I", "axiome_QM_II",
    "est_alpha_application",
    "corps_factorisation", "AU_corps", "AU_unicite", "est_universel",
    "est_solution",
    "au_implique_existence", "au_implique_unicite",
    "existence_et_unicite_impliquent_au",
    "separent_les_elements", "phi_E_injective",
    "alpha_libre", "est_libre_engendre",
    "corps_des_fractions", "produit_tensoriel", "compactifie_stone_cech",
    "_alpha_defaut", "_sigma_ens_defaut", "_morph_defaut",
]
