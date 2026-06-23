"""§III.6 (exercices) + §III.2 — BON ORDRE DE LA CLASSE DES ORDINAUX :
« tout ensemble NON VIDE d'ordinaux ≤ o admet un plus petit ordinal ».

────────────────────────────────────────────────────────────────────────────────
RÔLE — la ROUTE ORDINALE vers ℕ (gate `bon_ordre_intervalle(a)`).

La route Zermelo+segments-de-CARDINAL est MORTE : elle se réduisait à
`hyp_surjection = Card(seg(a,R,x)) = x`, qui est FAUSSE (le cardinal d'un segment
SAUTE — ex. ω+ω).  La route CORRECTE passe par les ORDINAUX, où l'application
t ↦ (type d'ordre du segment seg(o,Ro,t)) est une bijection PROPRE, SANS saut.

CONTENU PROUVÉ ICI (theorie=22, rien postulé) — le cœur du bon ordre des ordinaux :

  Représentation (ensembles_ordinaux.py) : un ordinal ≤ o est REPRÉSENTÉ par un
  SEGMENT INITIAL seg(o,Ro,t) = ]←,t[ d'un ordinal BORNANT (o,Ro) bien ordonné
  (E.III.2.1, Proposition 1 : dans un bon ordre, tout segment propre est un ]←,t[).
  La comparaison des ordinaux ≤ o se lit alors par INCLUSION des segments
  (ordinal_inferieur_ou_egal, E.III.2 Th 3 : « iso à un segment de »).

  Un ENSEMBLE non vide d'ordinaux ≤ o = un ENSEMBLE non vide T de points t∈o
  (chacun indexant le segment seg(o,Ro,t)).

  ✅ `ordinaux_bien_ordonnes` :
        { est_bien_ordonne(Ro,o),  T ⊂ o,  T ≠ ∅ }
            ⊢ (∃m)( m∈T  et  (∀x)( x∈T ⇒ seg(o,Ro,m) ⊂ seg(o,Ro,x) ) ).
     « T a un plus petit ordinal : son représentant seg(o,Ro,m) est INCLUS dans
     (= ≤) tous les autres. »  C'est le BON ORDRE de {ordinaux ≤ o}, lu par
     inclusion des segments.  DÉRIVÉ INCONDITIONNELLEMENT du SEUL bon ordre de (o,Ro)
     (engine plus_petit_de_bon_ordre + monotonie des segments, ensembles_segments_
     construction).  m = le plus petit point de T pour Ro.

  ✅ `seg_est_segment_de_seg` (pont structurel, NOUVEAU, CLOS) :
        { est_bien_ordonne(Ro,o),  seg(o,Ro,m) ⊂ seg(o,Ro,x) }
            ⊢ est_segment( seg(o,Ro,m), Ro, seg(o,Ro,x) ).
     « le représentant du plus petit ordinal est LITTÉRALEMENT un SEGMENT du
     représentant de tout autre. »  C'est la MOITIÉ NON-ISO de la comparaison
     ordinal_inferieur_ou_egal(seg m, seg x) = (∃S)(S segment de seg x ∧ seg m iso S),
     obtenue avec S := seg(o,Ro,m).  Ferme tout SAUF l'iso identité.

  ⚠️ REPORTÉ — précisément (énoncé `ordinaux_bien_ordonnes_ordinal_litteral`,
     hypothèse `iso_reflexif_seg`, JAMAIS postulée) : pour conclure la forme
     LITTÉRALE ordinal_inferieur_ou_egal(seg m, R, seg x, R), il reste UNIQUEMENT
     l'ISOMORPHISME D'ORDRE IDENTITÉ : sont_isomorphes_ordre(seg m, seg m, R, R)
     (« id : seg m → seg m est un iso d'ordre »).  C'est la RÉFLEXIVITÉ de l'ordre
     des ordinaux, REPORTÉE dans ensembles_ordinaux.py (inferieur_ou_egal_reflexif
     y renvoie une FORMULE, pas un théorème) : il faut exhiber le graphe identité
     comme application bijective seg m → seg m ET order-compatible (x≤y ⇔ x≤y,
     trivial une fois id(x)=x établi).  Voir le rapport pour la pièce exacte.

INVARIANT : theorie_ensembles() = 22.  Rien postulé : on RÉUTILISE l'engine déjà
clos (hyp_bon_ordre_seg_reel) et on DÉRIVE le pont segment depuis l'axiome de
segment + propriétés d'ordre.  🚫 jamais tautologie : seg(m)⊂seg(x) et
est_segment(seg m, seg x) ne sont aucune hypothèse.  NE MODIFIE AUCUN fichier.
"""
from __future__ import annotations

from bourbaki.logique.formule import (
    Terme, var, egal, et, non, impl, appartient, inclus,
)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.ordre.iii_6_ordinaux import ensembles_ordinaux as O
from bourbaki.ordre.iii_1_relations_ordre.ordre_treillis import ensembles_ordre_vocab as V
from bourbaki.logique.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    instancie, equivalence_avant, equivalence_arriere,
)
from bourbaki.cardinaux.ensembles_segments_construction import (
    seg, membre_segment, hyp_bon_ordre_seg_reel, hyp_bon_ordre_seg_reel_cible,
    _R_de,
)


def _t(t):
    return t if isinstance(t, Terme) else var(t)


# ════════════════════════════════════════════════════════════════════════════
#  🎯🎯  ordinaux_bien_ordonnes — BON ORDRE de la classe des ordinaux ≤ o.
#  (= hyp_bon_ordre_seg_reel, ré-énoncé comme « plus petit ordinal », CLOS.)
# ════════════════════════════════════════════════════════════════════════════
def ordinaux_bien_ordonnes(o="o", Ro="Ro", T="T", m="ms", x="xs"):
    """⊢ { est_bien_ordonne(Ro, o),  T ⊂ o,  T ≠ ∅ }
            ⊢ (∃m)( m∈T  et  (∀x)( x∈T ⇒ seg(o,Ro,m) ⊂ seg(o,Ro,x) ) ).

    🎯🎯 BON ORDRE DE LA CLASSE DES ORDINAUX ≤ o (E.III.6, exercices ; E.III.2 Th 3).

    Tout ENSEMBLE NON VIDE T d'ordinaux ≤ o admet un PLUS PETIT ordinal.  Un ordinal
    ≤ o est représenté (ensembles_ordinaux.py) par le SEGMENT INITIAL seg(o,Ro,t)=]←,t[
    d'un ordinal bornant (o,Ro) bien ordonné, indexé par t∈o ; la comparaison des
    ordinaux ≤ o est l'INCLUSION des segments (E.III.2 : « iso à un segment de »).
    Le plus petit ordinal de T est seg(o,Ro,m) où m = plus petit point de T pour Ro :
    seg(o,Ro,m) ⊂ seg(o,Ro,x) pour tout x∈T.

    DÉRIVÉ INCONDITIONNELLEMENT du SEUL bon ordre de (o,Ro) : c'est EXACTEMENT
    hyp_bon_ordre_seg_reel (engine plus_petit_de_bon_ordre + seg_strict_monotone),
    ré-énoncé comme « plus petit ORDINAL ».  NON vacueux, theorie=22, rien postulé."""
    return hyp_bon_ordre_seg_reel(Ro, o, T, m, x)


def ordinaux_bien_ordonnes_cible(o="o", Ro="Ro", T="T", m="ms", x="xs"):
    """ÉNONCÉ-cible (test miroir) de ordinaux_bien_ordonnes :

        (∃m)( m∈T et (∀x)( x∈T ⇒ seg(o,Ro,m) ⊂ seg(o,Ro,x) ) )."""
    return hyp_bon_ordre_seg_reel_cible(Ro, o, T, m, x)


# ════════════════════════════════════════════════════════════════════════════
#  Outils — caractérisation membre + propriétés d'ordre depuis est_bien_ordonne.
# ════════════════════════════════════════════════════════════════════════════
def _ordre_props(Ro, o):
    """De ⊢ est_bien_ordonne(Ro,o) [hyp] extrait (h_trans, h_anti) instanciables."""
    Rf = _R_de(Ro)
    Hbo = N.assume(E.est_bien_ordonne(Rf, _t(o)))
    ord_dans = conjonction_elim_gauche(Hbo)
    rel_ordre = conjonction_elim_gauche(ord_dans)
    trans_anti = conjonction_elim_gauche(rel_ordre)
    h_trans = conjonction_elim_gauche(trans_anti)        # ordre_transitif(Ro)
    h_anti = conjonction_elim_droite(trans_anti)         # ordre_antisymetrique(Ro)
    return h_trans, h_anti


_HOLE = "hole_obo"


def _leib(a, b, h_ab, phi_fun, h_phi_a):
    """De ⊢ a=b [h_ab] et ⊢ Φ[a] [h_phi_a] déduit ⊢ Φ[b]  (Leibniz via S6)."""
    va, vb = _t(a), _t(b)
    eqv = N.modus_ponens(h_ab, N.s6(va, vb, _HOLE, phi_fun(var(_HOLE))))
    return N.modus_ponens(h_phi_a, equivalence_avant(eqv))


def _ex_falso(thm_a, thm_na, z):
    a = thm_a.conclusion
    return N.modus_ponens(thm_a, N.modus_ponens(thm_na, N.s2(non(a), z)))


def _refute_self(thm_P_imp_notP):
    from bourbaki.logique.tactiques.tactiques_abrege import antecedent_consequent
    P, notP = antecedent_consequent(thm_P_imp_notP.conclusion)
    return N.modus_ponens(thm_P_imp_notP, N.s1(notP))


# ════════════════════════════════════════════════════════════════════════════
#  🎯 seg_est_segment_de_seg — le représentant du plus petit ordinal est
#     LITTÉRALEMENT un SEGMENT du représentant de tout autre.  (NOUVEAU, CLOS.)
# ════════════════════════════════════════════════════════════════════════════
def seg_est_segment_de_seg(Ro="Ro", o="o", m="m", x="x", u="u", v="v"):
    """⊢ { est_bien_ordonne(Ro, o),  seg(o,Ro,m) ⊂ seg(o,Ro,x) }
            ⊢ est_segment( seg(o,Ro,m), Ro, seg(o,Ro,x) ).

    🎯 La MOITIÉ NON-ISO de la comparaison des ordinaux : seg(o,Ro,m) (représentant
    du plus petit) est un SEGMENT de seg(o,Ro,x) (représentant de tout autre).  Avec
    ce segment S := seg(o,Ro,m), il ne reste à ordinal_inferieur_ou_egal(seg m, seg x)
    que sont_isomorphes_ordre(seg m, seg m, ...) (iso identité, REPORTÉ).

    est_segment(S, Ro, E) = S⊂E et (∀u,v)((u∈S et v∈E et v≤u) ⇒ v∈S).  La 1ʳᵉ
    composante EST l'hypothèse seg(m)⊂seg(x).  PREUVE de la clôture vers le bas :
    soit u∈seg(m) (⇒ u∈o, R{u,m}, u≠m), v∈seg(x) (⇒ v∈o), v≤u (R{v,u}).
      • R{v,m} : R{v,u} et R{u,m} ⇒ R{v,m}  (TRANSITIVITÉ).
      • v≠m : si v=m, de R{v,u} on a R{m,u} ; avec R{u,m} l'ANTISYMÉTRIE donne u=m,
        contredisant u≠m.  Donc v≠m.
      D'où v∈o et R{v,m} et v≠m ⇒ v∈seg(o,Ro,m).
    SEULES hypothèses : bon ordre de (o,Ro) (⊃ transitif/antisym) et seg(m)⊂seg(x).
    NON vacueux : la conclusion est_segment(…) n'est aucune hypothèse, et
    transitivité + antisymétrie sont RÉELLEMENT utilisées."""
    Rf = _R_de(Ro)
    vo, vm, vx = _t(o), _t(m), _t(x)
    Sm, Sx = seg(Ro, o, vm), seg(Ro, o, vx)
    un = u if isinstance(u, str) else u.nom
    vn = v if isinstance(v, str) else v.nom
    vu, vv = var(un), var(vn)

    # propriétés d'ordre depuis est_bien_ordonne(Ro,o)
    h_trans, h_anti = _ordre_props(Ro, o)

    # 1ʳᵉ composante : S⊂E = seg(m)⊂seg(x) — l'hypothèse elle-même.
    Hincl = N.assume(inclus(Sm, Sx))

    # 2ᵉ composante : (∀u)(∀v)((u∈seg m et v∈seg x et v≤u) ⇒ v∈seg m).
    Hu = N.assume(appartient(vu, Sm))                    # u∈seg(m)
    Hv = N.assume(appartient(vv, Sx))                    # v∈seg(x)
    Hvu = N.assume(Rf(vv, vu))                           # v≤u  (R{v,u})

    # u∈seg(m) ⇒ (u∈o et R{u,m}) et u≠m
    corps_u = N.modus_ponens(Hu, equivalence_avant(membre_segment(Ro, o, vm, vu)))
    u_in_o_Rum = conjonction_elim_gauche(corps_u)        # u∈o et R{u,m}
    Rum = conjonction_elim_droite(u_in_o_Rum)            # R{u,m}
    u_ne_m = conjonction_elim_droite(corps_u)            # u≠m
    # v∈seg(x) ⇒ v∈o
    corps_v = N.modus_ponens(Hv, equivalence_avant(membre_segment(Ro, o, vx, vv)))
    v_in_o = conjonction_elim_gauche(conjonction_elim_gauche(corps_v))   # v∈o

    # R{v,m} : (R{v,u} et R{u,m}) ⇒ R{v,m}  (transitivité)
    trans_vum = instancie(instancie(instancie(h_trans, vv), vu), vm)
    Rvm = N.modus_ponens(conjonction_intro(Hvu, Rum), trans_vum)         # R{v,m}

    # v≠m : par l'absurde — supposer v=m
    Hvm = N.assume(egal(vv, vm))                         # v=m
    #   de R{v,u} et v=m : R{m,u}
    Rmu = _leib(vv, vm, Hvm, lambda w: Rf(w, vu), Hvu)   # R{m,u}
    #   antisymétrie : (R{u,m} et R{m,u}) ⇒ u=m
    anti_um = instancie(instancie(h_anti, vu), vm)
    u_eq_m = N.modus_ponens(conjonction_intro(Rum, Rmu), anti_um)        # u=m
    falso = _ex_falso(u_eq_m, u_ne_m, non(egal(vv, vm)))                 # ¬(v=m) [Hvm,…]
    v_ne_m = _refute_self(N.loi_deduction(egal(vv, vm), falso))          # v≠m

    # assembler le corps : (v∈o et R{v,m}) et v≠m ⇒ v∈seg(m)
    corps_seg_v = conjonction_intro(conjonction_intro(v_in_o, Rvm), v_ne_m)
    v_in_Sm = N.modus_ponens(corps_seg_v, equivalence_arriere(membre_segment(Ro, o, vm, vv)))

    # décharger (u∈seg m et v∈seg x et v≤u) ⇒ v∈seg m  (forme de est_segment)
    ante = et(et(appartient(vu, Sm), appartient(vv, Sx)), Rf(vv, vu))
    body = _impl_depuis_conj(ante, v_in_Sm,
                             [appartient(vu, Sm), appartient(vv, Sx), Rf(vv, vu)])
    quant = N.generalisation(un, N.generalisation(vn, body))
    res = conjonction_intro(Hincl, quant)

    cible = E.est_segment(Sm, Rf, Sx, un, vn)
    assert res.conclusion == cible, "conclusion ≠ est_segment(seg m, Ro, seg x)"
    return res


def _impl_depuis_conj(ante, thm_concl, conjoints):
    """De ⊢ C [avec hyps conjoints[0], conjoints[1], …] construit ⊢ ante ⇒ C où
    ante = ((p0 et p1) et p2) (conjonction GAUCHE-associative des conjoints).
    On décharge chaque conjoint depuis la conjonction ante par projections."""
    # ante = ((p0 et p1) et p2)
    p0, p1, p2 = conjoints
    Hante = N.assume(ante)
    g = conjonction_elim_gauche(Hante)          # (p0 et p1)
    Hp0 = conjonction_elim_gauche(g)            # p0
    Hp1 = conjonction_elim_droite(g)            # p1
    Hp2 = conjonction_elim_droite(Hante)        # p2
    th = thm_concl
    # décharger p0, p1, p2 (remplacer les hypothèses par les projections de ante)
    th = N.modus_ponens(Hp0, N.loi_deduction(p0, th))
    th = N.modus_ponens(Hp1, N.loi_deduction(p1, th))
    th = N.modus_ponens(Hp2, N.loi_deduction(p2, th))
    # th : C  [ante, …]  ; décharger ante
    return N.loi_deduction(ante, th)


def seg_est_segment_de_seg_cible(Ro="Ro", o="o", m="m", x="x", u="u", v="v"):
    """ÉNONCÉ-cible (test miroir) de seg_est_segment_de_seg :
        est_segment( seg(o,Ro,m), Ro, seg(o,Ro,x) )."""
    Rf = _R_de(Ro)
    un = u if isinstance(u, str) else u.nom
    vn = v if isinstance(v, str) else v.nom
    return E.est_segment(seg(Ro, o, _t(m)), Rf, seg(Ro, o, _t(x)), un, vn)


# ════════════════════════════════════════════════════════════════════════════
#  ⚠️ REPORT PRÉCIS — la SEULE pièce restante : l'ISOMORPHISME IDENTITÉ.
# ════════════════════════════════════════════════════════════════════════════
def iso_reflexif_seg(Ro="Ro", o="o", m="m", f="f"):
    """ÉNONCÉ du report — la RÉFLEXIVITÉ de l'ordre des ordinaux (iso identité) :

        sont_isomorphes_ordre( seg(o,Ro,m), seg(o,Ro,m), Ro, Ro )
          = (∃f) est_isomorphisme_ordre(f, seg m, seg m, Ro, Ro).

    ⚠️ NON PROUVÉ.  C'est la SEULE pièce manquante pour passer de
    seg_est_segment_de_seg (seg m est un SEGMENT de seg x) à la forme LITTÉRALE
    ordinal_inferieur_ou_egal(seg m, Ro, seg x, Ro) = (∃S)(S segment de seg x ∧
    seg m iso S), via le témoin S := seg m.  Il faut exhiber le GRAPHE IDENTITÉ
    comme application bijective seg m → seg m (est_bijective) ET order-compatible
    (x≤y ⇔ id(x)≤id(y), trivial une fois id(x)=x établi).  Réflexivité REPORTÉE
    dans ensembles_ordinaux.py (inferieur_ou_egal_reflexif y renvoie une FORMULE).

    HYPOTHÈSE explicite, JAMAIS postulée comme théorème.  Binders CANONIQUES (xi, yi)
    = exactement ceux que ordinal_inferieur_ou_egal_litteral injecte dans le 2ᵉ
    conjoint, pour que iso_reflexif_seg COÏNCIDE avec lui (chaînage)."""
    Rf = _R_de(Ro)
    Sm = seg(Ro, o, _t(m))
    return V.sont_isomorphes_ordre(Sm, Sm, Rf, Rf, f, _LIT_X, _LIT_Y)


# binders d'ordre injectés dans ordinal_inferieur_ou_egal pour la forme littérale ;
# CANONIQUES anti-capture (cf. ensembles_iso_ordre_canon : ISO_X='x', ISO_Y='w').
_LIT_S = "Sseg"
_LIT_F = "fseg"
_LIT_X = "x"
_LIT_Y = "w"


def ordinal_inferieur_ou_egal_sous_iso(Ro="Ro", o="o", m="m", x="x"):
    """⊢ { est_bien_ordonne(Ro, o),  seg(o,Ro,m) ⊂ seg(o,Ro,x),
           iso_reflexif_seg(Ro,o,m) }
            ⊢ ordinal_inferieur_ou_egal( seg(o,Ro,m), Ro, seg(o,Ro,x), Ro ).

    🎯 LA FORME LITTÉRALE « seg m ≤ seg x » (au sens des ordinaux), DÉRIVÉE — il ne
    RESTE qu'UNE hypothèse au-delà du bon ordre : iso_reflexif_seg (iso identité,
    REPORTÉE).  On exhibe le témoin S := seg(o,Ro,m) du ∃S :
      • « S est un segment de seg x »  ← seg_est_segment_de_seg  (CLOS, binders x,w).
      • « seg m iso S »               ← iso_reflexif_seg          (hypothèse, REPORTÉE).
    Ceci PROUVE machine-vérifié que le SEUL trou de l'ordinaux_bien_ordonnes LITTÉRAL
    est l'iso identité : sous cette unique hypothèse de plus, la forme ordinale ferme.

    NON vacueux : la conclusion ∃S(…) n'est aucune hypothèse.  theorie=22."""
    Rf = _R_de(Ro)
    vo, vm, vx = _t(o), _t(m), _t(x)
    Sm, Sx = seg(Ro, o, vm), seg(Ro, o, vx)
    # cible = (∃Sseg)( est_segment(Sseg,Rf,Sx,x,w) et iso(Sm,Sseg,Rf,Rf,fseg,x,w) )
    cible = O.ordinal_inferieur_ou_egal(Sm, Rf, Sx, Rf, S=_LIT_S, f=_LIT_F, x=_LIT_X, y=_LIT_Y)
    # corps du ∃Sseg
    body = cible.sous[0]
    # témoin Sseg := Sm  →  corps[Sm]  = ( est_segment(Sm,Rf,Sx,x,w) et iso(Sm,Sm,…) )
    from bourbaki.logique.formule import subst_f
    corps_temoin = subst_f(Sm, _LIT_S, body)
    # pièce 1 : est_segment(Sm, Rf, Sx) binders (x,w) — seg_est_segment_de_seg
    seg_thm = seg_est_segment_de_seg(Ro, o, m, x, u=_LIT_X, v=_LIT_Y)  # [bo, seg m ⊂ seg x]
    # pièce 2 : iso(Sm,Sm,Rf,Rf,fseg,x,w)  — hypothèse iso_reflexif_seg
    iso_hyp_f = iso_reflexif_seg(Ro, o, m, f=_LIT_F)
    Hiso = N.assume(iso_hyp_f)
    conj = conjonction_intro(seg_thm, Hiso)          # est_segment(Sm,…) et iso(Sm,Sm,…)
    assert conj.conclusion == corps_temoin, "conjonction-témoin ≠ corps[Sseg:=Sm]"
    # introduire le ∃Sseg avec témoin Sm  (S5 : φ[Sm] ⇒ (∃Sseg)φ)
    res = N.modus_ponens(conj, N.s5(body, Sm, _LIT_S))
    assert res.conclusion == cible, "conclusion ≠ ordinal_inferieur_ou_egal littéral"
    return res


def ordinal_inferieur_ou_egal_litteral(Ro="Ro", o="o", m="m", x="x"):
    """ÉNONCÉ-cible LITTÉRAL (forme ordinale) du plus petit ordinal :

        ordinal_inferieur_ou_egal( seg(o,Ro,m), Ro, seg(o,Ro,x), Ro )
          = (∃S)( S segment de seg(o,Ro,x)  et  seg(o,Ro,m) iso S ).

    C'est la conclusion VOULUE pour « seg m ≤ seg x » au sens des ordinaux.  Avec
    S := seg(o,Ro,m), seg_est_segment_de_seg ferme « S segment de seg x » ; reste
    UNIQUEMENT iso_reflexif_seg (iso identité), REPORTÉ.  Cette fonction renvoie la
    FORMULE-énoncé (pas un Theoreme)."""
    Rf = _R_de(Ro)
    Sm = seg(Ro, o, _t(m))
    Sx = seg(Ro, o, _t(x))
    # binders d'ordre CANONIQUES (x, w) anti-capture (cf. ensembles_iso_ordre_canon).
    return O.ordinal_inferieur_ou_egal(Sm, Rf, Sx, Rf, S=_LIT_S, f=_LIT_F, x=_LIT_X, y=_LIT_Y)


__all__ = [
    "ordinaux_bien_ordonnes", "ordinaux_bien_ordonnes_cible",
    "seg_est_segment_de_seg", "seg_est_segment_de_seg_cible",
    "iso_reflexif_seg", "ordinal_inferieur_ou_egal_sous_iso",
    "ordinal_inferieur_ou_egal_litteral",
]
