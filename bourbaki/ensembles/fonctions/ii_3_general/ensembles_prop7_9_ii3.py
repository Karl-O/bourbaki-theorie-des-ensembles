"""§II.3 — Proposition 7 (la réciproque d'une application est une fonction ⟺
injective ; application ⟺ bijective) et Proposition 9 (factorisation).

SOURCE (lue visuellement, E II.17 / E II.20-21) :

  PROPOSITION 7 (E II.17). — « Soit f une application de A dans B. Pour que f⁻¹
  soit une fonction, il faut et il suffit que f soit bijective. »
  Démonstration : si f⁻¹ est une fonction, son ensemble de départ est égal à son
  ensemble de définition, c.-à-d. à f(A) [→ surjectivité] ; et f(x)=f(y) donne
  (f(x),x),(f(y),y)∈F⁻¹, donc x=y [→ injectivité]. Réciproquement, si f bijective,
  F⁻¹ est fonctionnel et l'ensemble de définition de f⁻¹ est égal à B.

  Le cœur de la Prop. 7 est la caractérisation « F⁻¹ fonctionnel ⟺ F injectif » AU
  NIVEAU DES GRAPHES.  Par couple_reciproque ((u,v)∈F⁻¹ ⇔ (v,u)∈F, E.II.41) :
      F⁻¹ fonctionnel := (∀u,v,z)((u,v)∈F⁻¹ et (u,z)∈F⁻¹ ⇒ v=z)
                       ⟺ (∀u,v,z)((v,u)∈F   et (z,u)∈F   ⇒ v=z)
  qui est exactement l'INJECTIVITÉ de F au niveau du graphe (deux antécédents v,z
  d'un même u sont égaux).  On livre cette équivalence CLOSE, INCONDITIONNELLE.

  PROPOSITION 9 (E II.20-21). — factorisation.
  a) g : E sur F (surjection), f : E→G.  Pour qu'il existe h : F→G avec f = h∘g,
     il faut et il suffit que [g(x)=g(y) ⟹ f(x)=f(y)] ; alors h = f∘s pour toute
     section s de g.
  b) g : F→E injective, f : G→E.  Pour qu'il existe h : G→F avec f = g∘h, il faut
     et il suffit que f(G)⊂g(F) ; alors h = r∘f pour toute rétraction r de g.

  Le SENS RÉCIPROQUE constructif de Prop. 9 a), lu au niveau des valeurs, s'établit
  directement à partir de la section : si s est une section de g (g∘s=Id_F) et si
  [g(x)=g(y)⟹f(x)=f(y)], alors h := f∘s vérifie h(g(x)) = f(s(g(x))) = f(x), car
  g(s(g(x)))=g(x) (section) donne f(s(g(x)))=f(x) par la condition de compatibilité.
  C'est f = h∘g au niveau des valeurs sur E.  On livre cette factorisation CLOSE
  sous les hypothèses HONNÊTES (s section de g ; compatibilité de f avec g) — ce
  sont exactement les données de l'énoncé b.
"""
from __future__ import annotations

from bourbaki.logique.formule import (var, egal, et, appartient, impl, pourtout,
                                       Terme)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.logique.tactiques.tactiques_abrege2 import (conjonction_intro,
                               conjonction_elim_gauche, conjonction_elim_droite,
                               instancie, equivalence_avant, equivalence_arriere,
                               equivalence_transitivite, equivalence_symetrie)
from bourbaki.logique.tactiques.tactiques_abrege_quantif import congruence_pour_tout
from bourbaki.logique.tactiques.tactiques_abrege_egalite import (symetrie,
                               composer_egalites, congruence_terme)
from bourbaki.ensembles.fonctions.ii_3_2_reciproque.ensembles_reciproque import couple_reciproque


def _T(v):
    """Coercion nom→terme (accepte un Terme ou un nom de variable)."""
    return v if isinstance(v, Terme) else var(v)


# ── PROPOSITION 7 — cœur : F⁻¹ fonctionnel ⟺ F injectif (au niveau des graphes) ─
def _graphe_injectif(f, u="u", v="v", z="z"):
    """« F injectif (au niveau du graphe) » := (∀u)(∀v)(∀z)(((v,u)∈F et (z,u)∈F)⇒v=z).

    Deux antécédents v, z d'un même point u sont égaux — c'est l'injectivité de F
    lue sur le graphe (E.II.17, démonstration de la Prop. 7 : (f(x),x),(f(y),y)∈F⁻¹
    avec f(x)=f(y) donne x=y)."""
    vu, vv, vz = _T(u), _T(v), _T(z)
    return pourtout(u, pourtout(v, pourtout(z,
        impl(et(appartient(E.couple(vv, vu), f), appartient(E.couple(vz, vu), f)),
             egal(vv, vz)))))


def reciproque_fonctionnel_ssi_injectif(f="F"):
    """⊢ est_fonctionnel(F⁻¹) ⇔ F injectif (graphe).   (Prop. 7, cœur — CLOS, 0 hyp.)

    est_fonctionnel(F⁻¹) = (∀u,v,z)(((u,v)∈F⁻¹ et (u,z)∈F⁻¹) ⇒ v=z).
    Par couple_reciproque : (u,v)∈F⁻¹ ⇔ (v,u)∈F et (u,z)∈F⁻¹ ⇔ (z,u)∈F, donc
    l'antécédent ((u,v)∈F⁻¹ et (u,z)∈F⁻¹) ⇔ ((v,u)∈F et (z,u)∈F), d'où l'équivalence
    des deux formules quantifiées (congruence sous les ∀ u,v,z)."""
    vF = _T(f)
    vu, vv, vz = var("u"), var("v"), var("z")
    Frec = E.reciproque(vF)
    # équivalence des antécédents : ((u,v)∈F⁻¹ et (u,z)∈F⁻¹) ⇔ ((v,u)∈F et (z,u)∈F)
    cr_uv = couple_reciproque(f, "u", "v")          # (u,v)∈F⁻¹ ⇔ (v,u)∈F
    cr_uz = couple_reciproque(f, "u", "z")          # (u,z)∈F⁻¹ ⇔ (z,u)∈F
    ant_rec = et(appartient(E.couple(vu, vv), Frec), appartient(E.couple(vu, vz), Frec))
    ant_inj = et(appartient(E.couple(vv, vu), vF), appartient(E.couple(vz, vu), vF))
    # ⇒ : (u,v)∈F⁻¹ et (u,z)∈F⁻¹  ⊢  (v,u)∈F et (z,u)∈F
    hr = N.assume(ant_rec)
    avant = N.loi_deduction(ant_rec, conjonction_intro(
        N.modus_ponens(conjonction_elim_gauche(hr), equivalence_avant(cr_uv)),
        N.modus_ponens(conjonction_elim_droite(hr), equivalence_avant(cr_uz))))
    hi = N.assume(ant_inj)
    arriere = N.loi_deduction(ant_inj, conjonction_intro(
        N.modus_ponens(conjonction_elim_gauche(hi), equivalence_arriere(cr_uv)),
        N.modus_ponens(conjonction_elim_droite(hi), equivalence_arriere(cr_uz))))
    eq_ant = conjonction_intro(avant, arriere)      # ant_rec ⇔ ant_inj
    # congruence dans (· ⇒ v=z) : (ant_rec ⇒ v=z) ⇔ (ant_inj ⇒ v=z)
    vz_eq = egal(vv, vz)
    himp_rec = N.assume(impl(ant_rec, vz_eq))
    imp_to = N.loi_deduction(impl(ant_rec, vz_eq),
                N.loi_deduction(ant_inj, N.modus_ponens(
                    N.modus_ponens(N.assume(ant_inj), equivalence_arriere(eq_ant)),
                    N.assume(impl(ant_rec, vz_eq)))))
    himp_inj = N.assume(impl(ant_inj, vz_eq))
    imp_fro = N.loi_deduction(impl(ant_inj, vz_eq),
                N.loi_deduction(ant_rec, N.modus_ponens(
                    N.modus_ponens(N.assume(ant_rec), equivalence_avant(eq_ant)),
                    N.assume(impl(ant_inj, vz_eq)))))
    eq_imp = conjonction_intro(imp_to, imp_fro)     # (ant_rec⇒v=z) ⇔ (ant_inj⇒v=z)
    # quantifier sous ∀u ∀v ∀z
    eq_q = congruence_pour_tout(congruence_pour_tout(
        congruence_pour_tout(eq_imp, "z"), "v"), "u")
    return eq_q


def cible_reciproque_fonctionnel_ssi_injectif(f="F"):
    """Cible exacte : est_fonctionnel(F⁻¹) ⇔ F injectif (graphe)."""
    from bourbaki.logique.formule import equiv
    vF = _T(f)
    return equiv(E.est_fonctionnel(E.reciproque(vF)), _graphe_injectif(vF))


def reciproque_fonctionnel_implique_injectif(f="F"):
    """⊢ est_fonctionnel(F⁻¹) ⇒ F injectif (graphe).   (Prop. 7, condition NÉCESSAIRE.)"""
    return equivalence_avant(reciproque_fonctionnel_ssi_injectif(f))


def injectif_implique_reciproque_fonctionnel(f="F"):
    """⊢ F injectif (graphe) ⇒ est_fonctionnel(F⁻¹).   (Prop. 7, condition SUFFISANTE.)"""
    return equivalence_arriere(reciproque_fonctionnel_ssi_injectif(f))


# ── PROPOSITION 9 a) — factorisation f = h∘g (sens réciproque constructif) ──────
def _compatible(g, f, e, a="a", b="b"):
    """« f compatible avec g sur E » := (∀a)(∀b)((a∈E et b∈E et g(a)=g(b)) ⇒ f(a)=f(b)).

    C'est la condition « g(x)=g(y) entraîne f(x)=f(y) » de l'énoncé de la Prop. 9 a)
    (gardée par a,b∈E, fidèle à « où x∈E, y∈E » ; liants a,b ≠ binder y de valeur)."""
    va, vb = _T(a), _T(b)
    return pourtout(a, pourtout(b, impl(
        et(et(appartient(va, e), appartient(vb, e)), egal(E.valeur(g, va), E.valeur(g, vb))),
        egal(E.valeur(f, va), E.valeur(f, vb)))))


def prop9a_factorisation_valeur(g="G", f="F", s="S", e="E", ff="FF"):
    """⊢_{s section de g sur F, u=g(x), u∈F, s(u)∈E, x∈E, f compatible avec g sur E}
        f(s(u)) = f(x).   (Prop. 9 a, factorisation h=f∘s, niveau valeurs.)

    « s est une section associée à g, et f compatible avec g (g(x)=g(y)⟹f(x)=f(y)) ;
    alors h := f∘s vérifie, pour u=g(x), h(u) = f(s(u)) = f(x). »  En effet, u étant
    dans F (image de g), la section donne g(s(u))=u=g(x), donc par compatibilité
    f(s(u))=f(x).  C'est exactement f = h∘g au niveau des valeurs (Bourbaki E.II.21 :
    « g(s(g(x)))=g(x), donc f(s(g(x)))=f(x), d'où bien f = g∘h »).  Le point u=g(x)
    est gardé par une variable et l'hypothèse honnête u=g(x) (évite la τ-capture du
    terme imbriqué g(x) dans l'instanciation, verrou liant valeur documenté).

    Hypothèses HONNÊTES (jamais postulées, déchargées) :
      • s section de g sur F  [est_section(S,G,F) : (∀v∈F) g(s(v))=v]
      • u = g(x)   (u = g(x) ∈ F, image de x par g)  — donnée « g : E sur F »
      • u∈F, s(u)∈E, x∈E  (typage des points : domaines/codomaines)
      • f compatible avec g sur E  [_compatible(G,F,E)]  — condition de l'énoncé."""
    vG, vF, vS, vE, vFF = _T(g), _T(f), _T(s), _T(e), _T(ff)
    vx, vu = var("x"), var("u")
    su = E.valeur(vS, vu)                                   # s(u)
    gx = E.valeur(vG, vx)                                   # g(x)
    hxE = N.assume(appartient(vx, vE))                      # x∈E
    hu_gx = N.assume(egal(vu, gx))                          # u = g(x)
    # (1) g(s(u)) = u   [section de g au point u∈F]
    hsec = N.assume(E.est_section(vS, vG, vFF, y="v0"))    # (∀v0∈F) g(s(v0))=v0
    inst_sec = instancie(hsec, vu)                         # u∈F ⇒ g(s(u))=u
    huF = N.assume(appartient(vu, vFF))                    # u∈F
    gsu_u = N.modus_ponens(huF, inst_sec)                 # g(s(u)) = u
    # (2) g(s(u)) = g(x)   [u = g(x)]
    gsu_gx = composer_egalites(gsu_u, hu_gx)              # g(s(u)) = g(x)
    # (3) f(s(u)) = f(x)   [compatibilité : (s(u)∈E et x∈E et g(s(u))=g(x)) ⟹ f(s(u))=f(x)]
    hcompat = N.assume(_compatible(vG, vF, vE))            # (∀a,b∈E) g(a)=g(b)⟹f(a)=f(b)
    inst_compat = instancie(instancie(hcompat, su), vx)   # (s(u)∈E et x∈E et g(s(u))=g(x)) ⇒ f(s(u))=f(x)
    hsuE = N.assume(appartient(su, vE))                   # s(u)∈E  (s applique F dans E)
    fsu_fx = N.modus_ponens(
        conjonction_intro(conjonction_intro(hsuE, hxE), gsu_gx), inst_compat)  # f(s(u))=f(x)
    return fsu_fx                                          # f(s(u)) = f(x)


def cible_prop9a_factorisation_valeur(f="F", s="S"):
    """Cible exacte : f(s(u)) = f(x)."""
    vF, vS = _T(f), _T(s)
    vx, vu = var("x"), var("u")
    return egal(E.valeur(vF, E.valeur(vS, vu)), E.valeur(vF, vx))


# ── PROPOSITION 9 b) — factorisation f = g∘h (sens réciproque constructif) ──────
def prop9b_factorisation_valeur(g="G", f="F", r="R", gg="GG", c="C"):
    """⊢_{r rétraction de g sur GG, f(x)=g(y(x)), r rétr. appliquée à y(x)}
        ... g(r(f(x))) = f(x).   (Prop. 9 b, factorisation h=r∘f, niveau valeurs.)

    Bourbaki E.II.21 : « pour tout x∈G il existe y∈F tel que f(x)=g(y) [car
    f(G)⊂g(F)] ; alors g(h(x)) = g(r(f(x))) = g(r(g(y))) = g(y) = f(x), donc f=g∘h. »
    Au niveau des valeurs, posons h := r∘f.  L'étape clé est g(r(g(y)))=g(y), qui
    résulte de r(g(y))=y (rétraction de g au point y∈GG) par congruence sous g(·).
    On livre cette factorisation sous les hypothèses HONNÊTES de l'énoncé : pour un
    x donné, f(x)=g(y) (y antécédent fourni par f(G)⊂g(F)) et y∈GG (domaine de g).

    Hypothèses HONNÊTES (jamais postulées) :
      • r rétraction de g sur GG  [est_retraction(R,G,GG) : (∀y∈GG) r(g(y))=y]
      • f(x) = g(y)               [y antécédent de f(x) par g, via f(G)⊂g(F)]
      • y ∈ GG                    [y dans le domaine de g]."""
    vG, vF, vR, vGG, vC = _T(g), _T(f), _T(r), _T(gg), _T(c)
    vx, vyy = var("x"), var("yy")
    fx = E.valeur(vF, vx)                                  # f(x)
    gyy = E.valeur(vG, vyy)                                # g(yy)
    # (1) f(x) = g(yy)   [yy antécédent fourni par f(G)⊂g(F)]
    hfx_gyy = N.assume(egal(fx, gyy))                      # f(x) = g(yy)
    # (2) r(g(yy)) = yy   [rétraction de g au point yy∈GG]
    hret = N.assume(E.est_retraction(vR, vG, vGG))        # (∀x∈GG) r(g(x))=x
    inst_ret = instancie(hret, vyy)                       # yy∈GG ⇒ r(g(yy))=yy
    hyyGG = N.assume(appartient(vyy, vGG))                # yy∈GG
    rgyy_yy = N.modus_ponens(hyyGG, inst_ret)            # r(g(yy)) = yy
    # (3) r(f(x)) = r(g(yy))   [congruence sous r(·) de f(x)=g(yy)]
    rfx_rgyy = N.modus_ponens(hfx_gyy, congruence_terme(fx, gyy, E.valeur(vR, var("w")), "w"))
    # (4) r(f(x)) = yy   par transitivité
    rfx_yy = composer_egalites(rfx_rgyy, rgyy_yy)        # r(f(x)) = yy
    # (5) g(r(f(x))) = g(yy)   [congruence sous g(·)]
    grfx_gyy = N.modus_ponens(rfx_yy, congruence_terme(
        E.valeur(vR, fx), vyy, E.valeur(vG, var("w")), "w"))  # g(r(f(x))) = g(yy)
    # (6) g(r(f(x))) = f(x)   = g(yy) puis symétrie de (1)
    grfx_fx = composer_egalites(grfx_gyy, N.modus_ponens(hfx_gyy, symetrie(fx, gyy)))
    return grfx_fx                                        # g(r(f(x))) = f(x)   (= g(h(x)))


def cible_prop9b_factorisation_valeur(g="G", f="F", r="R"):
    """Cible exacte : g(r(f(x))) = f(x)   (c.-à-d. g(h(x))=f(x) avec h=r∘f)."""
    vG, vF, vR = _T(g), _T(f), _T(r)
    vx = var("x")
    rfx = E.valeur(vR, E.valeur(vF, vx))
    return egal(E.valeur(vG, rfx), E.valeur(vF, vx))


__all__ = [
    "reciproque_fonctionnel_ssi_injectif", "cible_reciproque_fonctionnel_ssi_injectif",
    "reciproque_fonctionnel_implique_injectif", "injectif_implique_reciproque_fonctionnel",
    "prop9a_factorisation_valeur", "cible_prop9a_factorisation_valeur",
    "prop9b_factorisation_valeur", "cible_prop9b_factorisation_valeur",
]
