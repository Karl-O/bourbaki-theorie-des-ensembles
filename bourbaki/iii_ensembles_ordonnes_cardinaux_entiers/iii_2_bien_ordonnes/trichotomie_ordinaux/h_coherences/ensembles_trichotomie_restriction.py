"""§III.2 — Théorème 3 (TRICHOTOMIE) : BRIQUES de COHÉRENCE de l'iso maximal h.

────────────────────────────────────────────────────────────────────────────────
RÔLE.  h = h_iso_max = ⋃ (graphes d'iso de couples de segments isomorphes) est le
témoin maximal du Théorème 3 (E.III.2.6).  Pour que h soit une APPLICATION / un ISO
bien définie, il reste EXACTEMENT deux cohérences (cf. memory/n-bien-ordre-route.md,
« COEUR IRRÉDUCTIBLE ») :

  (A) compatibilite_inverse_h : ((u,v)∈h et (u',v)∈h) ⇒ u=u'   [injectivité par couples]
  (B) compatibilite_ordre_h   : ((u,v),(u',v')∈h) ⇒ (R{u,u'} ⇔ Rp{v,v'})  [ordre par couples]

Deux couples (u,v),(u',v')∈h viennent (h_membre_donne_temoin, CLOS) de deux isos de
segments  φ:S≅T  et  φ':S'≅T'.  La preuve fidèle Bourbaki de (A)/(B) repose sur TROIS
briques, livrées ICI (module NEUF — NE MODIFIE AUCUN fichier existant) :

  (1) RESTRICTION d'un iso de segments à un sous-segment est encore compatible avec
      l'ordre :  φ:S≅T iso, S0⊂S  ⇒  φ|S0 respecte l'ordre sur S0 (vers φ⟨S0⟩).
  (2) COMPARABILITÉ des segments témoins :  deux segments seg(R,E,t), seg(R,E,s) d'un
      MÊME bon ordre E sont ⊂-comparables.
  (3) COÏNCIDENCE :  deux isos φ:S≅T, φ':S'≅T' avec S⊂S' coïncident sur S, par UNICITÉ
      (auto_iso_est_identite : φ'⁻¹∘φ = id_S).

────────────────────────────────────────────────────────────────────────────────
CE QUE CE MODULE LIVRE (salvage fort gradué, honnête, theorie=22) :

  ✅ BRIQUE (2) — INCONDITIONNELLE (sur le seul bon ordre + t,s∈E) :
     • `comparabilite_segments_temoins(R,E,t,s)` :
          { est_bien_ordonne(R,E), t∈E, s∈E }
              ⊢ ( seg(R,E,t) ⊂ seg(R,E,s) )  ou  ( seg(R,E,s) ⊂ seg(R,E,t) ).
       Via comparabilite_dans_bon_ordre (R{t,s} ou R{s,t}, CLOS) + seg_strict_monotone_
       de_bon_ordre (CLOS) sur chaque branche.  Forme CLOSE associée.

  ✅ BRIQUE (1) — INCONDITIONNELLE (cœur order-reflecting de la restriction) :
     • `restriction_compatible_ordre(phi,S,S0,R,Rp)` :
          { compatible_ordre(φ,S,R,R'),  S0 ⊂ S }
              ⊢ compatible_ordre(φ,S0,R,R').
       La restriction d'un iso de segments à un SOUS-ensemble S0⊂S préserve la
       compatibilité d'ordre (R{x,y} ⇔ R'{φ(x),φ(y)}) : elle vaut pour tout x,y∈S,
       a fortiori pour x,y∈S0.  C'est le CŒUR « φ|S0 est un iso d'ordre de S0 sur
       φ⟨S0⟩ » ; la bijectivité φ|S0:S0→φ⟨S0⟩ (graphes/codomaine) est REPORTÉE en
       hypothèse explicite là où elle est consommée (B/A).  Forme CLOSE associée.

  ⚠️ BRIQUE (3) — CONDITIONNELLE à la géométrie d'unicité (hyps EXPLICITES, fidèles) :
     • `coincidence_sur_chevauchement(R,S,phi,phip,...)` :
          { est_bien_ordonne(R,S),
            [φ'⁻¹∘φ : S→S et son inverse strict. croissants, rétraction]  ← géométrie
            (∀u)(u∈S ⇒ φ'(φ'⁻¹(φ(u))) = φ(u))                           ← φ'∘φ'⁻¹=id
          }
            ⊢ (∀u)( u∈S ⇒ φ(u) = φ'(u) ).
       Deux isos φ:S≅T, φ':S'≅T' (S⊂S') coïncident sur S : l'automorphisme c:=φ'⁻¹∘φ
       de S est l'IDENTITÉ (auto_iso_est_identite, CLOS), d'où φ(u)=φ'(φ'⁻¹(φ(u)))=φ'(u).
       Les hypothèses GÉOMÉTRIQUES (c et c⁻¹ strict. croissants, rétraction, et
       φ'∘φ'⁻¹=id en φ(u)) sont EXPLICITES dans le séquent — fidèles, non affaiblies,
       jamais postulées.  Le ⋄composition de graphes φ'⁻¹∘φ ⋄ est la même glue
       reportée que dans iso_unicite_finale (capturée ici par les hyps).

INVARIANT : theorie_ensembles() = 22.  Rien postulé : on RÉUTILISE auto_iso_est_identite,
comparabilite_dans_bon_ordre, seg_strict_monotone_de_bon_ordre (tous CLOS/déjà commités).
NON vacueux : aucune conclusion n'est l'une de ses hypothèses.

NE REPROUVE PAS auto_iso_est_identite, ni comparabilite_dans_bon_ordre, ni seg_strict_
monotone_de_bon_ordre : ils sont IMPORTÉS.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, et, ou, non, impl, appartient, pourtout, inclus, equiv,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_1_relations_ordre.ordre_treillis import ensembles_ordre_vocab as V
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege import a_implique_a, syllogisme
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    instancie, equivalence_avant, cas,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.trichotomie_ordinaux.lemme4_segments.ensembles_bien_ordonne_seg_iso import (
    comparabilite_dans_bon_ordre,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.trichotomie_ordinaux.lemme4_segments.ensembles_bien_ordonne_lemme_1_segments import (
    seg, seg_strict_monotone_de_bon_ordre,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.trichotomie_ordinaux.iso_ordre.ensembles_iso_unicite_finale import auto_iso_est_identite
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.trichotomie_ordinaux.iso_ordre.ensembles_iso_unicite_sous_domaine import (
    auto_iso_est_identite_sous_domaine,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.trichotomie_ordinaux.lemme4_segments.ensembles_lemme4_croissante import _val, _R_de


def _t(t):
    return t if isinstance(t, Terme) else var(t)


# ════════════════════════════════════════════════════════════════════════════
#  BRIQUE (2) — COMPARABILITÉ des SEGMENTS TÉMOINS.  INCONDITIONNELLE.
#  Deux segments seg(R,E,t), seg(R,E,s) d'un même bon ordre sont ⊂-comparables.
# ════════════════════════════════════════════════════════════════════════════
# @livre Ch.III §2.5 Demo.3 | E III.21 L.23-33 | PDF p.124  (démonstration du Th. 3 : segments d'extrémité comparables — brique de cohérence de h)
def comparabilite_segments_temoins(R="R", E_set="E", t="t", s="s"):
    """⊢ { est_bien_ordonne(R,E),  t∈E,  s∈E }
            ⊢ ( seg(R,E,t) ⊂ seg(R,E,s) )  ou  ( seg(R,E,s) ⊂ seg(R,E,t) ).

    🎯 BRIQUE (2) du cœur trichotomie : les segments témoins d'un MÊME bon ordre E
    sont emboîtés (l'un inclus dans l'autre).  De la comparabilité R{t,s} ou R{s,t}
    (comparabilite_dans_bon_ordre, CLOS), la monotonie seg_strict_monotone_de_bon_ordre
    (CLOS) transporte chaque branche en une inclusion de segments.

    PREUVE.  Comparabilité : R{t,s} ou R{s,t}.
      • R{t,s} ⇒ seg(t) ⊂ seg(s).
      • R{s,t} ⇒ seg(s) ⊂ seg(t).
    Par `cas`, l'une des deux inclusions tient.  INCONDITIONNEL sous le bon ordre +
    t∈E + s∈E.  NON vacueux : la conclusion (disjonction d'inclusions) n'est aucune
    hypothèse ; la monotonie est réellement consommée."""
    St, Ss = seg(R, E_set, t), seg(R, E_set, s)
    but = ou(inclus(St, Ss), inclus(Ss, St))

    comp = comparabilite_dans_bon_ordre(R, E_set, t, s)   # {bo, t∈E, s∈E} ⊢ R{t,s} ou R{s,t}

    # branche R{t,s} : seg(t)⊂seg(s) ⇒ but
    Rts = _R_de(R)(t, s)
    mono_ts = seg_strict_monotone_de_bon_ordre(R, E_set, t, s)   # {bo, R{t,s}} ⊢ seg(t)⊂seg(s)
    # consomme R{t,s} (assumé) pour produire seg(t)⊂seg(s)
    HRts = N.assume(Rts)
    incl_ts = N.modus_ponens(HRts, N.loi_deduction(Rts, mono_ts))   # seg(t)⊂seg(s)  [bo, R{t,s}]
    # St⊂Ss ⇒ but  (S2)
    or_ts = N.modus_ponens(incl_ts, N.s2(inclus(St, Ss), inclus(Ss, St)))  # but  [bo, R{t,s}]
    brA = N.loi_deduction(Rts, or_ts)                     # R{t,s} ⇒ but  [bo]

    # branche R{s,t} : seg(s)⊂seg(t) ⇒ but
    Rst = _R_de(R)(s, t)
    mono_st = seg_strict_monotone_de_bon_ordre(R, E_set, s, t)   # {bo, R{s,t}} ⊢ seg(s)⊂seg(t)
    HRst = N.assume(Rst)
    incl_st = N.modus_ponens(HRst, N.loi_deduction(Rst, mono_st))   # seg(s)⊂seg(t)  [bo, R{s,t}]
    # Ss⊂St ⇒ but  (S2 puis S3 pour mettre dans le bon ordre de disjonction)
    or_st0 = N.modus_ponens(incl_st, N.s2(inclus(Ss, St), inclus(St, Ss)))  # (Ss⊂St) ou (St⊂Ss)
    or_st = N.modus_ponens(or_st0, N.s3(inclus(Ss, St), inclus(St, Ss)))    # but = (St⊂Ss) ou (Ss⊂St)
    brB = N.loi_deduction(Rst, or_st)                     # R{s,t} ⇒ but  [bo]

    return cas(comp, brA, brB)                            # but  [bo, t∈E, s∈E]


def comparabilite_segments_temoins_cible(R="R", E_set="E", t="t", s="s"):
    """ÉNONCÉ-cible (test miroir) de comparabilite_segments_temoins."""
    St, Ss = seg(R, E_set, t), seg(R, E_set, s)
    return ou(inclus(St, Ss), inclus(Ss, St))


def comparabilite_segments_temoins_clos(R="R", E_set="E", t="t", s="s"):
    """Forme CLOSE (0 hypothèse) : décharge les 3 hypothèses canoniques.

    ⊢ ( est_bien_ordonne(R,E) et t∈E et s∈E ) ⇒
        ( seg(R,E,t) ⊂ seg(R,E,s) ou seg(R,E,s) ⊂ seg(R,E,t) ),
    sous forme d'implications imbriquées (s∈E ⇒ (t∈E ⇒ (bo ⇒ but)))."""
    Rf = _R_de(R)
    vE, vt, vs = _t(E_set), _t(t), _t(s)
    thm = comparabilite_segments_temoins(R, E_set, t, s)
    bo = E.est_bien_ordonne(Rf, vE)
    t_in = appartient(vt, vE)
    s_in = appartient(vs, vE)
    out = thm
    out = N.loi_deduction(bo, out)
    out = N.loi_deduction(t_in, out)
    out = N.loi_deduction(s_in, out)
    return out


# ════════════════════════════════════════════════════════════════════════════
#  BRIQUE (1) — RESTRICTION d'un iso de segments à un SOUS-ensemble S0⊂S préserve
#  la COMPATIBILITÉ D'ORDRE.  INCONDITIONNELLE.
#
#  compatible_ordre(φ,S,R,R') = (∀x)(∀y)((x∈S et y∈S) ⇒ (R{x,y} ⇔ R'{φ(x),φ(y)})).
#  Si S0⊂S, alors x,y∈S0 ⇒ x,y∈S, donc l'équivalence R{x,y}⇔R'{φ(x),φ(y)} tient sur
#  S0 : c'est le CŒUR « φ|S0 est un iso d'ordre de S0 sur φ⟨S0⟩ ».
# ════════════════════════════════════════════════════════════════════════════
def restriction_compatible_ordre(phi="phi", S="S", S0="S0", R="R", Rp="Rp",
                                 x="x", y="y"):
    """⊢ { compatible_ordre(φ,S,R,R'),  S0 ⊂ S }
            ⊢ compatible_ordre(φ,S0,R,R').

    🎯 BRIQUE (1) : la RESTRICTION de l'iso de segments φ à un SOUS-ensemble S0⊂S
    préserve la compatibilité avec l'ordre.  C'est le contenu « φ|S0 : S0 ≅ φ⟨S0⟩ est
    encore un iso d'ordre » (la bijectivité de φ|S0 sur son image φ⟨S0⟩ est portée
    SÉPARÉMENT — REPORTÉE en hypothèse explicite là où A/B la consomment ; ICI on
    livre le cœur ORDRE, qui est le verrou de cohérence).

    PREUVE.  Soit x,y∈S0.  Comme S0⊂S, x∈S et y∈S, donc compatible_ordre(φ,S,R,R')
    donne R{x,y} ⇔ R'{φ(x),φ(y)}.  C'est exactement la clause de compatible_ordre(φ,S0).
    INCONDITIONNEL.  NON vacueux : la clause sur S est réellement instanciée et
    l'inclusion S0⊂S réellement consommée (la conclusion ≠ l'hypothèse car S0≠S)."""
    Rf, Rpf = _R_de(R), _R_de(Rp)
    vphi, vS, vS0 = _t(phi), _t(S), _t(S0)
    vx, vy = var(x), var(y)
    fx, fy = E.valeur(vphi, vx), E.valeur(vphi, vy)

    Hcompat = N.assume(V.compatible_ordre(vphi, vS, Rf, Rpf, x, y))   # clause sur S
    Hincl = N.assume(inclus(vS0, vS))                                 # S0⊂S

    # corps de compatible_ordre(φ,S0) : (x∈S0 et y∈S0) ⇒ (R{x,y} ⇔ R'{φ(x),φ(y)})
    Hpre = N.assume(et(appartient(vx, vS0), appartient(vy, vS0)))
    x_in_S0 = conjonction_elim_gauche(Hpre)
    y_in_S0 = conjonction_elim_droite(Hpre)
    # S0⊂S : x∈S0 ⇒ x∈S, y∈S0 ⇒ y∈S
    x_in_S = N.modus_ponens(x_in_S0, instancie(Hincl, vx))           # x∈S
    y_in_S = N.modus_ponens(y_in_S0, instancie(Hincl, vy))           # y∈S
    # clause sur S instanciée à (x,y) : (x∈S et y∈S) ⇒ (R{x,y} ⇔ R'{φ(x),φ(y)})
    compat_inst = instancie(instancie(Hcompat, vx), vy)
    equiv_xy = N.modus_ponens(conjonction_intro(x_in_S, y_in_S), compat_inst)  # R{x,y} ⇔ R'{φ(x),φ(y)}

    body = N.loi_deduction(et(appartient(vx, vS0), appartient(vy, vS0)), equiv_xy)
    return N.generalisation(x, N.generalisation(y, body))            # compatible_ordre(φ,S0,R,R')


def restriction_compatible_ordre_cible(phi="phi", S="S", S0="S0", R="R", Rp="Rp",
                                       x="x", y="y"):
    """ÉNONCÉ-cible (test miroir) de restriction_compatible_ordre."""
    Rf, Rpf = _R_de(R), _R_de(Rp)
    return V.compatible_ordre(_t(phi), _t(S0), Rf, Rpf, x, y)


def restriction_compatible_ordre_clos(phi="phi", S="S", S0="S0", R="R", Rp="Rp",
                                      x="x", y="y"):
    """Forme CLOSE (0 hypothèse) : décharge les 2 hypothèses.

    ⊢ ( compatible_ordre(φ,S,R,R') et S0⊂S ) ⇒ compatible_ordre(φ,S0,R,R'),
    sous forme d'implications imbriquées (S0⊂S ⇒ (compat_S ⇒ compat_S0))."""
    Rf, Rpf = _R_de(R), _R_de(Rp)
    vphi, vS, vS0 = _t(phi), _t(S), _t(S0)
    thm = restriction_compatible_ordre(phi, S, S0, R, Rp, x, y)
    compat_S = V.compatible_ordre(vphi, vS, Rf, Rpf, x, y)
    incl = inclus(vS0, vS)
    out = thm
    out = N.loi_deduction(compat_S, out)
    out = N.loi_deduction(incl, out)
    return out


# ════════════════════════════════════════════════════════════════════════════
#  BRIQUE (3) — COÏNCIDENCE sur le chevauchement, par UNICITÉ de l'iso de segments.
#  Deux isos φ:S≅T, φ':S'≅T' avec S⊂S' coïncident sur S : c := φ'⁻¹∘φ est un
#  automorphisme de S, donc l'IDENTITÉ (auto_iso_est_identite, CLOS), d'où
#  φ(u) = φ'(φ'⁻¹(φ(u))) = φ'(u).
# ════════════════════════════════════════════════════════════════════════════
def _coincide_concl(R, S, phi, phip, u="u"):
    """(∀u)( u∈S ⇒ φ(u) = φ'(u) )   (conclusion de coincidence_sur_chevauchement)."""
    vS = _t(S)
    vu = var(u)
    return pourtout(u, impl(appartient(vu, vS),
                            egal(_val(phi, vu), _val(phip, vu))))


def _retraction_phip(R, S, phi, phip, c, u="u"):
    """Hypothèse « φ' ∘ (φ'⁻¹∘φ) = φ sur S », i.e. (∀u)(u∈S ⇒ φ'(c(u)) = φ(u)),
    où c := φ'⁻¹∘φ.  (φ' restitue ce que φ'⁻¹ a enlevé : sens « φ'∘φ'⁻¹=id ».)"""
    vS = _t(S)
    vu = var(u)
    cu = _val(c, vu)                                       # c(u) = (φ'⁻¹∘φ)(u)
    return pourtout(u, impl(appartient(vu, vS),
                            egal(_val(phip, cu), _val(phi, vu))))


# @livre Ch.III §2.5 Cor.1 | E III.22 L.15-16 | PDF p.125  (unicité de l'iso : coïncidence de φ et φ' sur le chevauchement, sous géométrie explicite)
def coincidence_sur_chevauchement(R="R", S="S", phi="phi", phip="phip", c="c",
                                  k="k", u="u", E_set="E"):
    """⊢ { est_bien_ordonne(R,E),  inclus(S,E),                   [BON ORDRE AMBIANT]
           (∀t)(t∈S ⇒ c(t)∈S),  c strict. croissante S→S,        [c=φ'⁻¹∘φ : S→S iso]
           (∀t)(t∈S ⇒ k(t)∈S),  k strict. croissante S→S,        [k=c⁻¹ : S→S iso]
           (∀x)(x∈S ⇒ k(c(x))=x),                                [k∘c = id_S]
           (∀u)(u∈S ⇒ φ'(c(u)) = φ(u)) }                         [φ'∘(φ'⁻¹∘φ)=φ sur S]
         ⊢ (∀u)( u∈S ⇒ φ(u) = φ'(u) ).

    🎯 BRIQUE (3) — COÏNCIDENCE de deux isos de segments sur leur CHEVAUCHEMENT (le
    plus petit segment).  c := φ'⁻¹∘φ est un AUTOMORPHISME d'ordre de S, donc, par
    auto_iso_est_identite_sous_domaine (Cor 1 §III.2, variante SOUS-DOMAINE), c = id_S :
    c(u)=u pour tout u∈S.  Avec l'hypothèse de rétraction φ'(c(u))=φ(u) on obtient
    φ'(u)=φ'(c(u))=φ(u).

    🔑 BON ORDRE AMBIANT.  La coïncidence consomme le bon ordre AMBIANT
    est_bien_ordonne(R,E) + inclus(S,E), JAMAIS la formule littérale bo(R,S) (qui est
    FAUSSE pour un segment PROPRE S⊊E — cf. l'en-tête de ensembles_lemme4_sous_domaine).
    C'est crucial pour la fusion : S est un SEGMENT du grand bon ordre (E,R), et bo(R,S)
    ne peut s'y discharger.  On route donc par auto_iso_est_identite_sous_domaine.

    PREUVE.  auto_iso_est_identite_sous_domaine(R,E,S,c,k) donne (∀u)(u∈S ⇒ c(u)=u).
    Sous u∈S :
      • c(u)=u  (point fixe).
      • φ'(c(u)) = φ(u)  (hypothèse de rétraction).
      • transport de c(u)=u dans φ'(c(u)) : φ'(c(u)) = φ'(u).
      • donc φ'(u) = φ'(c(u)) = φ(u), i.e. φ(u) = φ'(u).
    Les hypothèses GÉOMÉTRIQUES (c, k strict. croissantes, rétraction k∘c=id, et la
    rétraction φ'∘φ'⁻¹=id sous la forme φ'(c(u))=φ(u)) sont EXPLICITES dans le séquent —
    fidèles, non affaiblies, jamais postulées.  La ⋄composition de graphes φ'⁻¹∘φ⋄ est
    la même glue reportée que dans iso_unicite_finale ; on la capture par hypothèses.
    NON vacueux : la conclusion φ(u)=φ'(u) n'est aucune hypothèse."""
    vS = _t(S)
    vu = var(u)

    # ── point fixe de c via auto_iso_est_identite_sous_domaine (Cor 1 SOUS-DOMAINE) ──
    pf = auto_iso_est_identite_sous_domaine(R, E_set, S, c, k, x="u")  # (∀u)(u∈S⇒c(u)=u)  [7 hyps]
    Hu = N.assume(appartient(vu, vS))                      # u∈S
    cu_eq_u = N.modus_ponens(Hu, instancie(pf, vu))        # c(u) = u

    # ── hypothèse de rétraction φ' : φ'(c(u)) = φ(u) ───────────────────────────
    Hretr = N.assume(_retraction_phip(R, S, phi, phip, c, u))
    phip_cu_eq_phi_u = N.modus_ponens(Hu, instancie(Hretr, vu))   # φ'(c(u)) = φ(u)

    # ── transport c(u)=u dans φ'(c(u)) : φ'(c(u)) = φ'(u)  (Leibniz S6) ─────────
    cu = _val(c, vu)                                       # c(u)
    phip_cu = _val(phip, cu)                               # φ'(c(u))
    phip_u = _val(phip, vu)                                # φ'(u)
    # de c(u)=u : φ'(c(u)) ⇔-substituable par φ'(u)
    _HOLE = "hole_coinc"
    eqv = N.modus_ponens(cu_eq_u,
                         N.s6(cu, vu, _HOLE, egal(phip_cu, _val(phip, var(_HOLE)))))
    # eqv : (φ'(c(u))=φ'(c(u))) ⇔ (φ'(c(u))=φ'(u))
    refl = N.reflexivite(phip_cu)                          # φ'(c(u)) = φ'(c(u))
    phip_cu_eq_phip_u = N.modus_ponens(refl, equivalence_avant(eqv))   # φ'(c(u)) = φ'(u)

    # ── chaînage : φ(u) = φ'(c(u)) = φ'(u) ─────────────────────────────────────
    phi_u = _val(phi, vu)                                  # φ(u)
    # de φ'(c(u))=φ(u) : φ(u)=φ'(c(u))  (symétrie)
    from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import symetrie
    phi_u_eq_phip_cu = N.modus_ponens(phip_cu_eq_phi_u, symetrie(phip_cu, phi_u))   # φ(u)=φ'(c(u))
    # transport φ'(c(u))=φ'(u) dans le 2ᵉ membre : φ(u)=φ'(u)
    eqv2 = N.modus_ponens(phip_cu_eq_phip_u,
                          N.s6(phip_cu, phip_u, _HOLE, egal(phi_u, var(_HOLE))))
    phi_u_eq_phip_u = N.modus_ponens(phi_u_eq_phip_cu, equivalence_avant(eqv2))     # φ(u)=φ'(u)

    body = N.loi_deduction(appartient(vu, vS), phi_u_eq_phip_u)    # u∈S ⇒ φ(u)=φ'(u)
    return N.generalisation(u, body)                              # (∀u)(u∈S ⇒ φ(u)=φ'(u))


def coincidence_sur_chevauchement_cible(R="R", S="S", phi="phi", phip="phip",
                                        c="c", k="k", u="u", E_set="E"):
    """ÉNONCÉ-cible (test miroir) de coincidence_sur_chevauchement."""
    return _coincide_concl(R, S, phi, phip, u)


__all__ = [
    "comparabilite_segments_temoins", "comparabilite_segments_temoins_cible",
    "comparabilite_segments_temoins_clos",
    "restriction_compatible_ordre", "restriction_compatible_ordre_cible",
    "restriction_compatible_ordre_clos",
    "coincidence_sur_chevauchement", "coincidence_sur_chevauchement_cible",
]
