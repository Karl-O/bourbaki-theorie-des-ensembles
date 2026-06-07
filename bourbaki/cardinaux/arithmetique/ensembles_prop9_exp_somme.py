"""§III.3.5 — PROPOSITION 9 (forme exponentielle) : a^(b+c) = a^b · a^c
(Cor. 1 de la Proposition 10, E.III.3.5).  CONSTRUCTION DE LA BIJECTION Φ.

ÉNONCÉ visé (forme cardinale binaire du projet) :

    ⊢ Card(𝓕(B⊔C; A)) = Card(𝓕(B;A) × 𝓕(C;A))

via la BIJECTION naturelle
        Φ : 𝓕(B⊔C; A) → 𝓕(B;A) × 𝓕(C;A),   f ↦ (f|B , f|C)
où f|B = « f restreinte à la copie de B » est l'application u ↦ f((u,0)) sur B
(de même f|C : v ↦ f((v,1)) sur C).  L'INVERSE est le RECOLLEMENT : à (g,h) on
associe l'application qui vaut g(u) sur la copie (u,0) de B et h(v) sur la copie
(v,1) de C (réunion de deux graphes à domaines disjoints).

La bijection complète d'ESPACES DE FONCTIONS est le vrai morceau dur (réindexation
le long des injections + extensionnalité fonctionnelle).  Le SOCLE round 24
(`ensembles_exposant_somme`) a déjà posé les caractérisations membership des trois
espaces et la décomposition structurelle.  Ce module — round 25 — pose les DEUX
demi-constructions (restriction et recollement) comme PALIERS CERTIFIÉS, en
exploitant l'infra extensionnalité (`graphe_egal_par_valeurs`) et recollement
(`reunion_graphes_fonctionnelle`).

═══════════════════════════════════════════════════════════════════════════════
ÉTAT (SALVAGE, paliers sûrs livrés au fur et à mesure) :

PALIER 0 (CLOS) — ÉNONCÉ-CIBLE (formule) :
  • cible_prop9_exp_somme(A,B,C) : Card(𝓕(B⊔C;A)) = Card(𝓕(B;A) × 𝓕(C;A)).

PALIER R (CLOS) — RESTRICTION f ↦ f|B (et f|C), demi-image gauche de Φ :
  • restriction_gauche(f,B)            : terme f|B = graphe_terme(B, f((e,0))) ;
  • restriction_gauche_fonctionnelle(f,B)  ⊢ f|B est fonctionnel  [C54] ;
  • restriction_gauche_domaine(f,B)        ⊢ dom(f|B) = B ;
  • restriction_gauche_valeur(f,B,u)       {u∈B} ⊢ (f|B)(u) = f((u,0)) ;
  • restriction_droite(f,C)            : terme f|C = graphe_terme(C, f((e,1))) ;
  • restriction_droite_fonctionnelle / _domaine / _valeur  (miroir copie 1).
  Donc f|B (resp. f|C) est une VRAIE FONCTION de domaine B (resp. C) valant
  f((u,0)) (resp. f((v,1))) — la donnée du couple (f|B,f|C) image de Φ.

PALIER G (CLOS) — RECOLLEMENT (g,h) ↦ g∪h, inverse de Φ :
  • recollement(g,h)                   : terme g∪h (réimporté de l'infra) ;
  • recollement_fonctionnel(g,h,B,C)
        ⊢ ( g fonctionnel et h fonctionnel et dom g ⊂ B×{0} et dom h ⊂ C×{1} )
          ⇒ (g∪h) est fonctionnel.
  Deux graphes fonctionnels portés par les copies marquées DISJOINTES (0≠1) se
  recollent sans conflit de valeur en une fonction sur B⊔C.

CŒUR REPORTÉ (l'égalité finale via la bijection Φ + _prop1_direct_t) : la mise en
bijection complète exige de prouver, par EXTENSIONNALITÉ fonctionnelle, que Φ est
injective (deux f de mêmes restrictions sont égales sur B⊔C) et surjective (tout
couple (g,h) se relève par recollement réindexé), ce qui demande de TRANSPORTER
g,h le long des injections ι_B,ι_C et d'identifier (recollement)|B = g — un
appariement de graphes valeur-par-valeur sur B⊔C lourd, hors budget de ce round.
Raison précise : voir `bijection_phi_REPORTE`.
═══════════════════════════════════════════════════════════════════════════════
"""
from __future__ import annotations

from bourbaki.logique.formule import (Terme, var, egal, et, non, ou, impl,
                     appartient, existe, pourtout, inclus, subst_t)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.cardinaux.ensembles_cardinaux import cardinal
from bourbaki.ensembles.familles.ensembles_somme_disjointe import (
    somme_disjointe, ZERO, UN)
# Infra restriction par GRAPHE-TERME (C54) :
from bourbaki.ensembles.fonctions.ensembles_fonction_terme import (
    graphe_terme_fonctionnel)
from bourbaki.cardinaux.ensembles_cantor import (
    graphe_terme_domaine, graphe_terme_valeur)
# Infra RECOLLEMENT (round 25) :
from bourbaki.ensembles.fonctions.ensembles_restriction_somme import (
    recollement, reunion_graphes_fonctionnelle, domaines_disjoints_si_marques)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# ═══════════════════════════════════════════════════════════════════════════════
# PALIER 0 — ÉNONCÉ-CIBLE (formule)  :  Card(𝓕(B⊔C;A)) = Card(𝓕(B;A) × 𝓕(C;A))
# ═══════════════════════════════════════════════════════════════════════════════
def cible_prop9_exp_somme(a="A", b="B", c="C"):
    """L'ÉNONCÉ visé (Proposition 9, forme exponentielle) :
    Card(𝓕(B⊔C; A)) = Card(𝓕(B;A) × 𝓕(C;A))  =  a^(b+c) = a^b · a^c.

    Renvoie la FORMULE (non un théorème) — fixe la signature de la cible, identique
    aux membres de gauche/droite définis dans `ensembles_exposant_somme`
    (exposant_somme_cardinal / produit_exposants_cardinal)."""
    va, vb, vc = _t(a), _t(b), _t(c)
    BC = somme_disjointe(vb, vc)
    gauche = cardinal(E.applications(BC, va))                       # Card(𝓕(B⊔C;A))
    droite = cardinal(E.produit(E.applications(vb, va),             # Card(𝓕(B;A)×𝓕(C;A))
                                E.applications(vc, va)))
    return egal(gauche, droite)


# ═══════════════════════════════════════════════════════════════════════════════
# PALIER R — RESTRICTION  f ↦ f|B  (et f|C) : la demi-image gauche/droite de Φ.
#   f|B := graphe de  u ↦ f((u,0))  sur B  = graphe_terme(B, f((e,0))).
#   Le terme-valeur f((e,0)) emploie un liant de τ EXOTIQUE « c » (≠ y interne de
#   la machinerie graphe-terme) pour éviter toute capture (verrou liant-valeur).
# ═══════════════════════════════════════════════════════════════════════════════
_VAL_BINDER = "c"        # liant du τ de la valeur f((e,·)) — exotique, ≠ {u,v,z,w,x,y}
_GRAPHE_VAR = "e"        # variable du graphe-terme (point courant) — ≠ {u,v,z,w,x,y}
# Points d'ÉVALUATION interdits pour la valeur d'une restriction : le liant « e »
# du graphe ET les liants internes {v,w,y,z} de la machinerie graphe-terme/valeur
# (valeur_caracterisation lie « y », est_fonctionnel lie u,v,z, le trou de
# congruence est « w »).  Sûrs : u, m, p, a, b, …  (cf. exploration round 25).
_POINTS_INTERDITS = {_GRAPHE_VAR, "v", "w", "y", "z"}


def _verifie_point(pt):
    nom = pt if isinstance(pt, str) else (pt.nom if pt.tag == "var" else None)
    if nom in _POINTS_INTERDITS:
        raise ValueError(
            "le point d'évaluation d'une restriction doit éviter "
            f"{sorted(_POINTS_INTERDITS)} (collision de liant) ; reçu « {nom} »")


def _terme_val_gauche(f):
    """f((e,0))  =  valeur(f, (e,0))  — la valeur de f sur la copie gauche (e,0).

    Liant de τ « c » (exotique) ; le point courant du graphe est « e »."""
    return E.valeur(_t(f), E.couple(var(_GRAPHE_VAR), ZERO), _VAL_BINDER)


def _terme_val_droite(f):
    """f((e,1))  =  valeur(f, (e,1))  — la valeur de f sur la copie droite (e,1)."""
    return E.valeur(_t(f), E.couple(var(_GRAPHE_VAR), UN), _VAL_BINDER)


def restriction_gauche(f, b):
    """f|B := graphe_terme(B, f((e,0)))  = { (u, f((u,0))) | u ∈ B }  (terme).

    La restriction de f à la copie GAUCHE B de la somme disjointe : l'application
    u ↦ f((u,0)) sur B.  C'est la première composante de Φ(f) = (f|B, f|C)."""
    vf, vb = _t(f), _t(b)
    return E.graphe_terme(vb, _terme_val_gauche(vf), _GRAPHE_VAR)


def restriction_droite(f, c):
    """f|C := graphe_terme(C, f((e,1)))  = { (v, f((v,1))) | v ∈ C }  (terme).

    La restriction de f à la copie DROITE C : l'application v ↦ f((v,1)) sur C.
    Seconde composante de Φ(f) = (f|B, f|C)."""
    vf, vc = _t(f), _t(c)
    return E.graphe_terme(vc, _terme_val_droite(vf), _GRAPHE_VAR)


# ── f|B est une FONCTION (C54) ────────────────────────────────────────────────
def restriction_gauche_fonctionnelle(f="f", b="B"):
    """⊢ est_fonctionnel(f|B).   (la restriction u↦f((u,0)) sur B est une fonction.)

    Cas T = f((e,0)) du critère C54 (graphe_terme_fonctionnel) : un graphe-terme est
    toujours fonctionnel (une seule valeur f((u,0)) par antécédent u)."""
    vf, vb = _t(f), _t(b)
    return graphe_terme_fonctionnel(vb, _terme_val_gauche(vf), _GRAPHE_VAR, "y")


def restriction_gauche_domaine(f="f", b="B"):
    """⊢ dom(f|B) = B.   (la restriction f|B est définie sur TOUTE la copie B.)"""
    vf, vb = _t(f), _t(b)
    return graphe_terme_domaine(vb, _terme_val_gauche(vf), _GRAPHE_VAR, "y", "z")


def restriction_gauche_valeur(f="f", b="B", u="u"):
    """{u ∈ B} ⊢ (f|B)(u) = f((u,0)).   (la valeur de la restriction gauche en u.)

    ⚠️ le point d'évaluation doit éviter le liant du graphe « e » ET les liants
    internes {v,w,y,z} de la machinerie (sinon capture) : (f|B)(u) = T[e:=u] =
    f((u,0)).  Points sûrs : u, m, p, a, b, …"""
    vf, vb = _t(f), _t(b)
    _verifie_point(u)
    return graphe_terme_valeur(vb, _terme_val_gauche(vf), u, _GRAPHE_VAR, "y")


# ── f|C est une FONCTION (C54, miroir copie 1) ────────────────────────────────
def restriction_droite_fonctionnelle(f="f", c="C"):
    """⊢ est_fonctionnel(f|C).   (la restriction v↦f((v,1)) sur C est une fonction.)"""
    vf, vc = _t(f), _t(c)
    return graphe_terme_fonctionnel(vc, _terme_val_droite(vf), _GRAPHE_VAR, "y")


def restriction_droite_domaine(f="f", c="C"):
    """⊢ dom(f|C) = C.   (la restriction f|C est définie sur TOUTE la copie C.)"""
    vf, vc = _t(f), _t(c)
    return graphe_terme_domaine(vc, _terme_val_droite(vf), _GRAPHE_VAR, "y", "z")


def restriction_droite_valeur(f="f", c="C", v="m"):
    """{v ∈ C} ⊢ (f|C)(v) = f((v,1)).   (la valeur de la restriction droite en v.)

    ⚠️ le point d'évaluation doit éviter le liant du graphe « e » ET les liants
    internes {v,w,y,z} (sinon capture) — le DÉFAUT est donc « m » (et non « v »,
    qui est un liant interne).  Points sûrs : m, u, p, a, b, …"""
    vf, vc = _t(f), _t(c)
    _verifie_point(v)
    return graphe_terme_valeur(vc, _terme_val_droite(vf), v, _GRAPHE_VAR, "y")


# ═══════════════════════════════════════════════════════════════════════════════
# PALIER G — RECOLLEMENT  (g,h) ↦ g∪h  : l'INVERSE de Φ.
#   Deux graphes fonctionnels g, h portés par les copies marquées B×{0}, C×{1} se
#   recollent en une FONCTION sur B⊔C, car les copies sont DISJOINTES (0 ≠ 1).
# ═══════════════════════════════════════════════════════════════════════════════
def recollement_gauche_droite(g, h):
    """g ∪ h := recollement(g, h)  (terme).   La fonction qui vaut g(u) sur (u,0)
    et h(v) sur (v,1).  (Réexposé de l'infra recollement, RIEN redéfini.)"""
    return recollement(_t(g), _t(h))


def recollement_fonctionnel(g="G", h="H", b="B", c="C"):
    """⊢ ( est_fonctionnel(G) et est_fonctionnel(H)
          et (dom G) ⊂ (B×{0}) et (dom H) ⊂ (C×{1}) )
        ⇒  est_fonctionnel(G ∪ H).

    RECOLLEMENT (inverse de Φ).  Si G, H sont fonctionnels et leurs domaines vivent
    dans les copies marquées DISJOINTES B×{0}, C×{1} (séparées par 0≠1), alors
    G∪H ne crée aucun conflit de valeur : c'est une fonction sur B⊔C.

    Preuve : `domaines_disjoints_si_marques` déduit ¬(u∈domG et u∈domH) de
    l'inclusion dans les copies marquées ; on généralise sur u et on décharge
    l'hypothèse de disjonction du PIVOT `reunion_graphes_fonctionnelle`."""
    vg, vh, vb, vc = _t(g), _t(h), _t(b), _t(c)
    B0 = E.produit(vb, E.singleton(ZERO))                  # B×{0}
    C1 = E.produit(vc, E.singleton(UN))                    # C×{1}
    GuH = E.reunion(vg, vh)

    # PIVOT : {G func, H func, (∀u)¬(u∈domG et u∈domH)} ⊢ est_fonctionnel(G∪H)
    pivot = reunion_graphes_fonctionnelle(vg, vh)

    # DISJONCTION des domaines déduite des copies marquées, puis généralisée sur u :
    #   {dom G ⊂ B×{0}, dom H ⊂ C×{1}} ⊢ (∀u)¬(u∈domG et u∈domH)
    disj_u = domaines_disjoints_si_marques(vg, vh, vb, vc, "u")   # ¬(u∈domG et u∈domH)
    disj = N.generalisation("u", disj_u)
    disj_f = pourtout("u", non(et(appartient(var("u"), E.dom(vg)),
                                  appartient(var("u"), E.dom(vh)))))
    assert disj.conclusion == disj_f

    # décharger la disjonction du pivot puis la fournir par disj :
    #   {G func, H func} ⊢ disj ⇒ func(G∪H)        (loi_deduction)
    #   {G func, H func, domG⊂B×{0}, domH⊂C×{1}} ⊢ func(G∪H)   (MP avec disj)
    pivot_imp = N.loi_deduction(disj_f, pivot)
    func_GuH = N.modus_ponens(disj, pivot_imp)            # est_fonctionnel(G∪H)

    # décharger les 4 hypothèses restantes en une seule conjonction-implication
    hyp = et(et(et(E.est_fonctionnel(vg), E.est_fonctionnel(vh)),
                inclus(E.dom(vg), B0)), inclus(E.dom(vh), C1))
    # func_GuH porte exactement {func G, func H, domG⊂B0, domH⊂C1} comme hypothèses ;
    # on les ré-introduit comme antécédent conjonctif via assume + projections.
    hh = N.assume(hyp)
    from bourbaki.logique.tactiques.tactiques_abrege2 import (
        conjonction_elim_gauche, conjonction_elim_droite)
    p_hH = conjonction_elim_droite(hh)                    # dom H ⊂ C×{1}
    r1 = conjonction_elim_gauche(hh)
    p_hG = conjonction_elim_droite(r1)                    # dom G ⊂ B×{0}
    r2 = conjonction_elim_gauche(r1)
    p_fG = conjonction_elim_gauche(r2)                    # G fonctionnel
    p_fH = conjonction_elim_droite(r2)                    # H fonctionnel
    # remplacer chaque hypothèse de func_GuH par sa preuve sous {hyp}
    out = func_GuH
    out = _cut(out, E.est_fonctionnel(vg), p_fG)
    out = _cut(out, E.est_fonctionnel(vh), p_fH)
    out = _cut(out, inclus(E.dom(vg), B0), p_hG)
    out = _cut(out, inclus(E.dom(vh), C1), p_hH)
    return N.loi_deduction(hyp, out)                      # HYP ⇒ est_fonctionnel(G∪H)


def _cut(thm, hyp_formule, preuve):
    """Remplace l'hypothèse `hyp_formule` de `thm` par sa preuve `preuve`
    (loi_deduction puis modus_ponens) — règle de coupure standard."""
    imp = N.loi_deduction(hyp_formule, thm)              # (décharge hyp_formule)
    return N.modus_ponens(preuve, imp)                  # MP avec la preuve


# ═══════════════════════════════════════════════════════════════════════════════
# CŒUR REPORTÉ : la bijection Φ complète  f ↦ (f|B, f|C)  et l'égalité finale
# ═══════════════════════════════════════════════════════════════════════════════
def bijection_phi_REPORTE():
    """REPORTÉ (non clos) — la bijection Φ : 𝓕(B⊔C;A) → 𝓕(B;A)×𝓕(C;A) complète.

    Ce module ferme les DEUX demi-constructions :
      • la RESTRICTION f ↦ f|B (et f|C), qui sont de VRAIES FONCTIONS de domaines
        B, C (restriction_gauche/droite_fonctionnelle / _domaine / _valeur) ;
      • le RECOLLEMENT (g,h) ↦ g∪h, FONCTION sur B⊔C dès que g, h vivent sur les
        copies marquées disjointes (recollement_fonctionnel).

    Restent REPORTÉS (hors budget de ce round) :
      (i)  Φ BIEN DÉFINIE à valeurs dans 𝓕(B;A)×𝓕(C;A) : il faut que f|B ∈ 𝓕(B;A),
           c.-à-d. que sa valeur f((u,0)) ∈ A pour u∈B ; cela exige de TRANSPORTER
           l'hypothèse « f∈𝓕(B⊔C;A) » (donc f((u,0))∈A car (u,0)∈B⊔C) à travers
           l'injection ι_B : u↦(u,0) — pont membership × valeur non posé ;
      (ii) INJECTIVITÉ de Φ : f|B = f'|B et f|C = f'|C ⇒ f = f' par EXTENSIONNALITÉ
           fonctionnelle (graphe_egal_par_valeurs) sur B⊔C : tout antécédent de f
           est une copie (u,0) ou (v,1), et la valeur y coïncide via la restriction
           correspondante — cas-analyse sur la somme disjointe, lourde ;
      (iii)SURJECTIVITÉ de Φ : depuis (g,h) arbitraire, le recollement réindexé
           ψ(g,h) := (u,0)↦g(u) ∪ (v,1)↦h(v) vérifie ψ(g,h)|B = g et ψ(g,h)|C = h
           (recollement_fonctionnel donne déjà ψ(g,h) fonction) — même verrou
           d'extensionnalité fonctionnelle réindexée que (ii).

    Une fois Φ bijection, Eq(𝓕(B⊔C;A), 𝓕(B;A)×𝓕(C;A)) puis la Proposition 1 (sens
    direct, `_prop1_direct_t`) donnent l'égalité-cible `cible_prop9_exp_somme`."""
    raise NotImplementedError(
        "Bijection Φ : 𝓕(B⊔C;A) → 𝓕(B;A)×𝓕(C;A) complète reportée : réindexation "
        "le long des injections ι_B,ι_C (i) + extensionnalité fonctionnelle pour "
        "injectivité (ii) / surjectivité (iii).  Ce module livre la restriction "
        "f↦(f|B,f|C) et le recollement (g,h)↦g∪h, entièrement certifiés.")


__all__ = [
    "cible_prop9_exp_somme",
    "restriction_gauche", "restriction_droite",
    "restriction_gauche_fonctionnelle", "restriction_gauche_domaine",
    "restriction_gauche_valeur",
    "restriction_droite_fonctionnelle", "restriction_droite_domaine",
    "restriction_droite_valeur",
    "recollement_gauche_droite", "recollement_fonctionnel",
    "bijection_phi_REPORTE",
]
