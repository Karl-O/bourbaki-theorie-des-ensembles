"""§IV.3 (complément) — Parties Σ-permises, cardinal à possibilité Σ-permise,
conditions (CU_I)–(CU_III), critères CST22 / CST8 : représentation OBJET paramétrée.

Module NEUF qui COMPLÈTE la couverture du chapitre IV en INTRODUISANT (définitions
fidèles, niveau objet) les notions du §IV.3 (« critère d'existence d'une solution »,
IV, p. 16) qui n'étaient encore que REPORTÉES dans
`ensembles_universel_applications` :

  • Partie Σ-permise d'un Σ-ensemble (IV.3.2, p. 16) ;
  • condition (CU_I) : existence d'une structure produit sur tout produit de
    Σ-ensembles ;
  • condition (CU_II) : l'application (φ_ι)_{ι∈I} dans le produit est une
    α-application ;
  • condition (CU_III) (= condition CUₘ « à possibilité Σ-permise ») : existence d'un
    cardinal 𝔞 tel que toute α-application se factorise par une partie Σ-permise de
    cardinal ≤ 𝔞 ;
  • cardinal 𝔞 « à possibilité Σ-permise » — le cardinal témoin de (CU_III) ;
  • critère CST22 : (CU_I)+(CU_II)+(CU_III) ⟹ existence d'une solution du problème
    d'application universelle ;
  • critère CST8 : unicité de la solution à un isomorphisme unique près.

CONVENTION DE PARAMÉTRAGE (identique au reste du chap. IV, cf.
`ensembles_universel_applications` / `ensembles_universel_morphismes`).  La donnée
abstraite (Σ, σ, α) est portée par des PRÉDICATS callables → Formule du fragment
objet :
  • `sigma_ens(F, S)`        : « (F muni de S) est un Σ-ensemble » ;
  • `morph(e1,s1,e2,s2,f)`   : « f est un σ-morphisme de (e1,s1) dans (e2,s2) » ;
  • `alpha(F, S, phi)`       : « φ est une α-application de E dans (F,S) » ;
  • `induit(F, S, G)`        : « la structure 𝒮 de F INDUIT une structure d'espèce Σ
                               sur la partie G » (notion IV.2 « structure induite »,
                               cf. `ensembles_universel_morphismes.structure_induite`).
Ces prédicats par défaut sont opaques (réutilisés depuis le module IV.3 existant).

theorie_ensembles() reste à 22 axiomes : ce module n'en crée AUCUN (les conditions
(CU_I)–(CU_III) sont des HYPOTHÈSES de CST22, pas des axiomes de la théorie ; les
cardinaux et le produit s'appuient sur les modules existants).

REPORTÉ honnêtement (méta / lourd) : la PREUVE de CST22 (construction de F_E par
quotient d'un Σ-ensemble libre de cardinal borné) et de CST8 (composition + transport
de structure), qui sortent du fragment ensembliste — voir le champ `reportes`.  Ici on
INTRODUIT les notions et l'on certifie les LEMMES DIRECTS (projections logiques des
conjonctions (CU_I)∧(CU_II)∧(CU_III), forme de CST22).
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (var, app, egal, et, impl, equiv, existe,
                                       pourtout, non, appartient, inclus)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.cardinaux.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (cardinal, est_cardinal,
                                                    inf_egal_card)
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite)
from bourbaki.structures.ensembles_universel_applications import (
    _sigma_ens_defaut, _morph_defaut, _alpha_defaut, est_solution)


def _t(s):
    return var(s) if isinstance(s, str) else s


# ════════════════════════════════════════════════════════════════════════════
#  prédicat par défaut SUPPLÉMENTAIRE — « 𝒮 induit une structure Σ sur G »
# ════════════════════════════════════════════════════════════════════════════
def _induit_defaut(nom="InduitSigma"):
    """« la structure 𝒮 de F induit une structure d'espèce Σ sur la partie G » via un
    prédicat opaque app(nom, F, S, G) (terme ∈ {⊤}).  Le lecteur passe son propre
    `induit` (p.ex. l'existence d'une structure induite au sens IV.2, portée par la
    propriété (IN) à un indice de `structure_induite`)."""
    return lambda f, s, g: appartient(g, app(nom, f, s))


# ════════════════════════════════════════════════════════════════════════════
#  IV.3.2 — PARTIE Σ-PERMISE
# ════════════════════════════════════════════════════════════════════════════
# @livre Ch.IV §3.2 Def.- | E IV.23 L.42-43 | PDF p.226
def est_partie_sigma_permise(f, s, g, induit=None):
    """« la partie G du Σ-ensemble (F,S) est Σ-PERMISE » (IV.3.2, p. 16).

      « On dit qu'une partie G d'un Σ-ensemble F est Σ-permise si la structure de F
        induit une structure d'espèce Σ sur G. »

    Conjonction de deux clauses :
      1° G ⊂ F  (G est une PARTIE de F) ;
      2° la structure 𝒮 de F INDUIT une structure d'espèce Σ sur G.
    La clause 2° est portée par le prédicat abstrait `induit(F, S, G)` (notion
    « structure induite », IV.2)."""
    if induit is None:
        induit = _induit_defaut()
    vf, vg = _t(f), _t(g)
    return et(inclus(vg, vf), induit(vf, _t(s), vg))


# ════════════════════════════════════════════════════════════════════════════
#  CONDITIONS (CU_I), (CU_II), (CU_III)  — hypothèses du critère CST22
# ════════════════════════════════════════════════════════════════════════════
# @livre Ch.IV §3.2 Def.CU_I | E IV.23 L.36-37 | PDF p.226
def condition_CU_I(i, ff, sf, sigma_ens=None, struct_prod="Sprod", iota="iota"):
    """(CU_I) : « Sur tout produit d'une famille de Σ-ensembles, il existe une
    structure produit d'espèce Σ »  (IV.3, p. 16).

    À famille de Σ-ensembles (A_ι, 𝒮_ι)_{ι∈I} fixée — ff(ι) = A_ι, sf(ι) = 𝒮_ι —,
    on affirme que le produit ∏_ι A_ι porte une structure produit 𝒮 d'espèce Σ :
        (∀ι)(ι∈I ⇒ sigma_ens(A_ι, 𝒮_ι))  ⇒  sigma_ens(∏_ι A_ι, 𝒮_prod).
    `struct_prod` = le terme de la structure produit (existence postulée par (CU_I))."""
    if sigma_ens is None:
        sigma_ens = _sigma_ens_defaut()
    vi, viota = _t(i), var(iota)
    hyp = pourtout(iota, impl(appartient(viota, vi),
                              sigma_ens(ff(viota), sf(viota))))
    prod = E.produit_famille(ff(viota), vi)            # ∏_ι A_ι
    sp = _t(struct_prod)
    return impl(hyp, sigma_ens(prod, sp))


# @livre Ch.IV §3.2 Def.CU_II | E IV.23 L.38-41 | PDF p.226
def condition_CU_II(e, i, ff, sf, phif, struct_prod="Sprod", alpha=None,
                    sigma_ens=None, phi_prod="phiprod", iota="iota"):
    """(CU_II) : « Soit (F_ι)_{ι∈I} une famille de Σ-ensembles, et pour tout ι ∈ I
    soit φ_ι une α-application de E dans F_ι.  Alors l'application (φ_ι)_{ι∈I} de E
    dans ∏_{ι∈I} F_ι (muni de la structure produit) est une α-application »  (IV.3, p. 16).

    À (F_ι, 𝒮_ι, φ_ι)_{ι∈I} fixée — ff(ι)=F_ι, sf(ι)=𝒮_ι, phif(ι)=φ_ι —, on affirme :
        (∀ι)(ι∈I ⇒ (sigma_ens(F_ι,𝒮_ι) et alpha(F_ι,𝒮_ι, φ_ι)))
              ⇒ alpha(∏_ι F_ι, 𝒮_prod, (φ_ι)_{ι∈I}).
    `phi_prod` = l'application produit (φ_ι)_{ι∈I} (terme : son graphe)."""
    if alpha is None:
        alpha = _alpha_defaut()
    if sigma_ens is None:
        sigma_ens = _sigma_ens_defaut()
    vi, viota = _t(i), var(iota)
    clause = et(sigma_ens(ff(viota), sf(viota)),
                alpha(ff(viota), sf(viota), phif(viota)))
    hyp = pourtout(iota, impl(appartient(viota, vi), clause))
    prod = E.produit_famille(ff(viota), vi)            # ∏_ι F_ι
    sp = _t(struct_prod)
    phip = _t(phi_prod)
    return impl(hyp, alpha(prod, sp, phip))


# @livre Ch.IV §3.2 Def.CU_III | E IV.24 L.1-5 | PDF p.227
def possibilite_sigma_permise(a, e, f, s, phi, sigma_ens=None, alpha=None,
                              morph=None, induit=None, g="G", g2="Gp",
                              mor="f", mor2="fp"):
    """Corps de (CU_III) à cardinal 𝔞, Σ-ensemble (F,S) et α-application φ fixés —
    la « possibilité Σ-permise » de 𝔞 pour (F,S,φ) (IV.3, p. 16) :

      « il existe une partie Σ-permise G de F contenant φ(E), de cardinal ≤ 𝔞, telle
        que l'application de E dans G qui a même graphe que φ soit une α-application,
        et que deux morphismes de G dans un Σ-ensemble qui coïncident dans φ(E)
        soient égaux. »

    Codé (∃G)[ G Σ-permise de F  et  φ(E) ⊂ G  et  Card(G) ≤ 𝔞  et
               alpha(G, 𝒮|G, φ)  et  (∀F')(∀S')(∀f)(∀f')(
                  (morph(G,…,F',S',f) et morph(G,…,F',S',f') et
                   « f, f' coïncident dans φ(E) »)  ⇒  f = f' ) ].
    φ(E) = E.image(φ, E) (image directe).  La structure induite par 𝒮 sur G est notée
    app("struct_induite", F, S, G) (notion IV.2)."""
    if sigma_ens is None:
        sigma_ens = _sigma_ens_defaut()
    if alpha is None:
        alpha = _alpha_defaut()
    if morph is None:
        morph = _morph_defaut()
    if induit is None:
        induit = _induit_defaut()
    va, ve, vf, vs, vphi = map(_t, (a, e, f, s, phi))
    vg, vg2 = var(g), var(g2)
    vmor, vmor2 = var(mor), var(mor2)
    sG = app("struct_induite", vf, vs, vg)             # 𝒮 induite sur G

    permise = est_partie_sigma_permise(vf, vs, vg, induit)        # G Σ-permise
    contient = inclus(E.image(vphi, ve), vg)                       # φ(E) ⊂ G
    borne = inf_egal_card(cardinal(vg), va)                        # Card(G) ≤ 𝔞
    restr_alpha = alpha(vg, sG, vphi)                             # E→G a même graphe, α-appl.

    # « deux morphismes de G dans un Σ-ensemble qui coïncident dans φ(E) sont égaux »
    vfp, vsp = var(g2 + "F"), var(g2 + "S")
    coincide = pourtout("x", impl(appartient(var("x"), E.image(vphi, ve)),
                                  egal(E.valeur(vmor, var("x")),
                                       E.valeur(vmor2, var("x")))))
    sep_clause = impl(et(et(morph(vg, sG, vfp, vsp, vmor),
                            morph(vg, sG, vfp, vsp, vmor2)),
                         coincide),
                      egal(vmor, vmor2))
    separation = pourtout(g2 + "F", pourtout(g2 + "S",
                          pourtout(mor, pourtout(mor2, sep_clause))))

    corps = et(et(et(et(permise, contient), borne), restr_alpha), separation)
    return existe(g, corps)


# @livre Ch.IV §3.2 Def.CU_III | E IV.24 L.1-5 | PDF p.227
def condition_CU_III(a, e, sigma_ens=None, alpha=None, morph=None, induit=None,
                     f="F", s="S", phi="phi", g="G"):
    """(CU_III) (= condition CUₘ « à possibilité Σ-permise ») : « Il existe un cardinal
    𝔞 possédant les propriétés suivantes : pour tout Σ-ensemble F et toute
    α-application φ de E dans F, il existe une partie Σ-permise G de F contenant φ(E),
    de cardinal ≤ 𝔞, telle que … »  (IV.3, p. 16).

    À cardinal 𝔞 = `a` fixé, la PROPRIÉTÉ de 𝔞 est :
        (∀F)(∀S)(∀φ)[ (sigma_ens(F,S) et alpha(F,S,φ)) ⇒ possibilite_sigma_permise(𝔞,…) ].
    (CU_III) elle-même affirme l'EXISTENCE d'un tel cardinal — cf.
    `cardinal_a_possibilite_sigma_permise`.  Renvoie la propriété de 𝔞."""
    if sigma_ens is None:
        sigma_ens = _sigma_ens_defaut()
    if alpha is None:
        alpha = _alpha_defaut()
    va, ve = _t(a), _t(e)
    vf, vs, vphi = var(f), var(s), var(phi)
    hyp = et(sigma_ens(vf, vs), alpha(vf, vs, vphi))
    corps = possibilite_sigma_permise(va, ve, vf, vs, vphi,
                                      sigma_ens=sigma_ens, alpha=alpha,
                                      morph=morph, induit=induit, g=g)
    return pourtout(f, pourtout(s, pourtout(phi, impl(hyp, corps))))


# @livre Ch.IV §3.2 Def.CU_III | E IV.24 L.1-5 | PDF p.227
def cardinal_a_possibilite_sigma_permise(e, sigma_ens=None, alpha=None,
                                         morph=None, induit=None, a="a",
                                         f="F", s="S", phi="phi", g="G"):
    """Cardinal 𝔞 « à possibilité Σ-permise » pour E (IV.3, (CU_III)) := l'EXISTENCE
    d'un cardinal 𝔞 tel que tout couple (Σ-ensemble F, α-application φ) admette une
    factorisation par une partie Σ-permise de F de cardinal ≤ 𝔞.

    C'est l'énoncé COMPLET de (CU_III) :
        (∃𝔞)[ 𝔞 est un cardinal  et  (propriété de 𝔞, cf. condition_CU_III) ].
    Codé (∃a)( est_cardinal(a) et condition_CU_III(a, E, …) )."""
    va = var(a)
    prop = condition_CU_III(va, e, sigma_ens=sigma_ens, alpha=alpha,
                            morph=morph, induit=induit, f=f, s=s, phi=phi, g=g)
    return existe(a, et(est_cardinal(va), prop))


# ════════════════════════════════════════════════════════════════════════════
#  CRITÈRE CST22 — existence d'une solution
# ════════════════════════════════════════════════════════════════════════════
# @livre Ch.IV §3.2 Crit.CST22 | E IV.24 L.7-9 | PDF p.227
def hypotheses_CST22(e, i, ff, sf, phif, a, sigma_ens=None, morph=None,
                     alpha=None, induit=None):
    """Conjonction des trois conditions (CU_I) et (CU_II) et (CU_III), hypothèses du
    critère CST22 (IV.3) — « Si les conditions (CU_I) à (CU_III) sont vérifiées, le
    problème d'application universelle pour E admet une solution. »

    Renvoie (CU_I) et (CU_II) et (CU_III) (à famille (A_ι,𝒮_ι,φ_ι) et cardinal 𝔞
    fixés pour (CU_I)/(CU_II), 𝔞 le témoin de (CU_III))."""
    cu1 = condition_CU_I(i, ff, sf, sigma_ens=sigma_ens)
    cu2 = condition_CU_II(e, i, ff, sf, phif, alpha=alpha, sigma_ens=sigma_ens)
    cu3 = condition_CU_III(a, e, sigma_ens=sigma_ens, alpha=alpha,
                           morph=morph, induit=induit)
    return et(et(cu1, cu2), cu3)


# @livre Ch.IV §3.2 Crit.CST22 | E IV.24 L.7-9 | PDF p.227
def conclusion_CST22(fe, se, phi_e, sigma_ens=None, morph=None, alpha=None):
    """Conclusion du critère CST22 : « le problème d'application universelle pour E
    admet une solution » := il existe un Σ-ensemble (F_E,S_E) et une α-application
    φ_E formant une solution (IV.3).  Codé est_solution(F_E,S_E,φ_E, …) — la
    construction effective de (F_E,φ_E) est REPORTÉE (preuve de CST22)."""
    return est_solution(fe, se, phi_e, sigma_ens=sigma_ens, morph=morph, alpha=alpha)


# @livre Ch.IV §3.2 Crit.CST22 | E IV.24 L.7-9 | PDF p.227
def critere_CST22(e, i, ff, sf, phif, a, fe, se, phi_e, sigma_ens=None,
                  morph=None, alpha=None, induit=None):
    """Critère CST22 (IV.3) — forme ÉNONCÉE : « Si (CU_I) à (CU_III) sont vérifiées,
    le problème d'application universelle pour E admet une solution. »

    Codé hypotheses_CST22(…) ⇒ conclusion_CST22(…).  La VÉRITÉ de cette implication
    (l'existence effective de la solution) est REPORTÉE — construction de F_E par
    quotient d'un Σ-ensemble libre de cardinal ≤ 𝔞 (preuve méta/algébrique).  On
    INTRODUIT ici l'énoncé fidèle ; les LEMMES logiques directs (extraction de chaque
    CU_k depuis l'hypothèse) sont certifiés ci-dessous."""
    hyp = hypotheses_CST22(e, i, ff, sf, phif, a, sigma_ens=sigma_ens,
                           morph=morph, alpha=alpha, induit=induit)
    ccl = conclusion_CST22(fe, se, phi_e, sigma_ens=sigma_ens, morph=morph,
                           alpha=alpha)
    return impl(hyp, ccl)


# ── LEMMES DIRECTS (purement logiques) — extraction des conditions (CU_k) ──────
def cst22_extrait_CU_I(e="E", i="I0", ff=None, sf=None, phif=None, a="a",
                       sigma_ens=None, morph=None, alpha=None, induit=None):
    """{(CU_I) et (CU_II) et (CU_III)} ⊢ (CU_I).

    Lemme logique : l'hypothèse de CST22 est la conjonction (CU_I)∧(CU_II)∧(CU_III) ;
    on en EXTRAIT (CU_I) par les éliminations de conjonction.  Certifie que l'énoncé
    de CST22 est bien FORMÉ et que (CU_I) en est une composante.  Renvoie le théorème
    conditionnel hyp ⇒ (CU_I)."""
    if ff is None:
        ff = lambda t: app("A", t)
    if sf is None:
        sf = lambda t: app("Sig", t)
    if phif is None:
        phif = lambda t: app("phi", t)
    hyp = hypotheses_CST22(e, i, ff, sf, phif, a, sigma_ens=sigma_ens,
                           morph=morph, alpha=alpha, induit=induit)
    h = N.assume(hyp)                                   # hyp ⊢ hyp
    cu12 = conjonction_elim_gauche(h)                   # ⊢ (CU_I) et (CU_II)
    cu1 = conjonction_elim_gauche(cu12)                 # ⊢ (CU_I)
    return N.loi_deduction(hyp, cu1)                    # ⊢ hyp ⇒ (CU_I)


def cst22_extrait_CU_III(e="E", i="I0", ff=None, sf=None, phif=None, a="a",
                         sigma_ens=None, morph=None, alpha=None, induit=None):
    """{(CU_I) et (CU_II) et (CU_III)} ⊢ (CU_III).  (Projection droite de la
    conjonction des hypothèses de CST22.)  Renvoie hyp ⇒ (CU_III)."""
    if ff is None:
        ff = lambda t: app("A", t)
    if sf is None:
        sf = lambda t: app("Sig", t)
    if phif is None:
        phif = lambda t: app("phi", t)
    hyp = hypotheses_CST22(e, i, ff, sf, phif, a, sigma_ens=sigma_ens,
                           morph=morph, alpha=alpha, induit=induit)
    h = N.assume(hyp)                                   # hyp ⊢ hyp
    cu3 = conjonction_elim_droite(h)                    # ⊢ (CU_III)
    return N.loi_deduction(hyp, cu3)                    # ⊢ hyp ⇒ (CU_III)


# ════════════════════════════════════════════════════════════════════════════
#  CRITÈRE CST8 — unicité de la solution à un isomorphisme unique près
# ════════════════════════════════════════════════════════════════════════════
# @livre Ch.IV §2.1 Crit.CST8 | E IV.12 L.26-29 | PDF p.215
def solution_isomorphisme_unique(fe, se, phi_e, fep, sep, phi_ep, morph=None,
                                 mor="f1", mor2="f2"):
    """Critère CST8 (IV.3) — « unicité à un isomorphisme unique près » : si (F_E,φ_E)
    et (F_E',φ_E') sont deux solutions du problème pour E, il existe un morphisme
    unique f₁ : F_E → F_E' et un morphisme unique f₂ : F_E' → F_E avec φ_E' = f₁∘φ_E
    et φ_E = f₂∘φ_E' ; alors f₂∘f₁ = Id_{F_E} et f₁∘f₂ = Id_{F_E'}, donc f₁ est un
    isomorphisme de F_E sur F_E' et f₂ son réciproque  (IV, p. 12, CST8).

    Codé l'EXISTENCE des morphismes croisés témoignant de l'isomorphisme :
        (∃f₁)(∃f₂)[ morph(F_E,S_E,F_E',S_E',f₁) et morph(F_E',S_E',F_E,S_E,f₂) et
                    φ_E' = f₁∘φ_E  et  φ_E = f₂∘φ_E'
                    et f₂∘f₁ = Id_{F_E} et f₁∘f₂ = Id_{F_E'} ].
    (Le caractère UNIQUE des f_i découle de (AU_II′) ; l'unicité fine est REPORTÉE
    avec la preuve.)"""
    if morph is None:
        morph = _morph_defaut()
    fe, se, phi_e, fep, sep, phi_ep = map(_t, (fe, se, phi_e, fep, sep, phi_ep))
    vf1, vf2 = var(mor), var(mor2)
    m1 = morph(fe, se, fep, sep, vf1)                  # f₁ : F_E → F_E'
    m2 = morph(fep, sep, fe, se, vf2)                  # f₂ : F_E' → F_E
    fact1 = egal(phi_ep, E.composee(vf1, phi_e))       # φ_E' = f₁∘φ_E
    fact2 = egal(phi_e, E.composee(vf2, phi_ep))       # φ_E = f₂∘φ_E'
    inv1 = egal(E.composee(vf2, vf1), E.diagonale(fe))  # f₂∘f₁ = Id_{F_E}
    inv2 = egal(E.composee(vf1, vf2), E.diagonale(fep)) # f₁∘f₂ = Id_{F_E'}
    corps = et(et(et(et(et(m1, m2), fact1), fact2), inv1), inv2)
    return existe(mor, existe(mor2, corps))


__all__ = [
    "est_partie_sigma_permise",
    "condition_CU_I", "condition_CU_II", "possibilite_sigma_permise",
    "condition_CU_III", "cardinal_a_possibilite_sigma_permise",
    "hypotheses_CST22", "conclusion_CST22", "critere_CST22",
    "cst22_extrait_CU_I", "cst22_extrait_CU_III",
    "solution_isomorphisme_unique",
    "_induit_defaut",
]
