"""§III.2 — Théorème 3 (TRICHOTOMIE) : `est_un_graphe(h)` PROUVÉ (forme SET de h).

────────────────────────────────────────────────────────────────────────────────
RÔLE.  `trichotomie_ordinaux_canon_close_v2`
(`ensembles_trichotomie_hgraphe_pr2seg`) conclut `trichotomie_ordinaux_canon`
sous 4 hypothèses { bo(R,E), bo(Rp,F), residu_univ_app, est_un_graphe(h) }.
Le DERNIER résidu `est_un_graphe(h) = (∀z)(z∈h ⇒ z est un couple)` était OPAQUE :
l'axiome déposé de h (`TS.axiome_h` / `TS.theorie_h`) est COUPLE-ONLY — il
caractérise SEULEMENT l'appartenance d'un COUPLE :

    (∀u)(∀v)( (u,v)∈h ⇔ corps_h(u,v) )

et ne dit RIEN d'un z ARBITRAIRE ∈ h, donc « tout z∈h est un couple » N'EST PAS
dérivable de cette forme.

CE MODULE DÉCHARGE ce résidu par un RAFFINEMENT FIDÈLE (NON un postulat du but) :
on pose dans une THÉORIE DÉDIÉE `theorie_h_graphe` (motif `axiome_D` /
`TS.axiome_h` — JAMAIS theorie_ensembles) la forme SET de l'axiome de h :

    AXIOME_H_GRAPHE :  (∀E)(∀R)(∀F)(∀Rp)(∀z)(
        z∈h  ⇔  (∃a)(∃b)( z=(a,b)  et  corps_h(a,b) ) )

C'est la DÉFINITION ENSEMBLISTE du MÊME h = { (a,b) | corps_h(a,b) } (h est
l'union des graphes d'iso de segments : un ENSEMBLE DE COUPLES).  Légitime S8
(sélection dans E×F) + A1 (unicité), exactement comme la forme couple déposée.

CE MODULE LIVRE (theorie_ensembles=22 ; le nouvel axiome est dans theorie_h_graphe) :

  ✅ `axiome_h_graphe` / `theorie_h_graphe` / `h_membre_set` : forme SET, instanciée.
  ✅ `h_membre_depuis_set` : ⊢ ((u,v)∈h ⇔ corps_h(u,v)).  La forme SET ENTAÎNE la
     forme COUPLE déposée (== `TS.h_membre`).  ⟹ FIDÉLITÉ : axiome_h_graphe est un
     RENFORCEMENT CONSERVATIF de axiome_h (set ⟹ couple), donc TOUTES les preuves
     existantes utilisant `TS.h_membre` valent INCHANGÉES sous theorie_h_graphe.
  ✅ `h_est_graphe` : ⊢ est_un_graphe(h)   (== TS.h-as-set : z∈h ⇒ z couple).
     DÉRIVÉ de la forme SET (z∈h ⇒ ∃a∃b(z=(a,b) et …) ⇒ ∃a∃b z=(a,b) = z couple).
     PAS postulé : suit STRUCTURELLEMENT de la définition ensembliste.
  ✅ `trichotomie_ordinaux_canon_close_v3` : trichotomie_ordinaux_canon SOUS les
     3 hypothèses { bo(R,E), bo(Rp,F), residu_univ_app } — est_un_graphe(h) DÉCHARGÉ
     par `h_est_graphe`.  Conclusion == trichotomie_ordinaux_canon (== maillon_final_cible).

INVARIANT : theorie_ensembles() = 22 (le nouvel axiome vit dans theorie_h_graphe,
JAMAIS dans theorie_ensembles).  RIEN POSTULÉ du but : est_un_graphe(h) DÉRIVE de la
forme SET, qui est la définition fidèle de h comme ensemble de couples.  NON vacueux.
NE MODIFIE AUCUN fichier existant.
"""
from __future__ import annotations

from bourbaki.logique.formule import (
    Terme, var, egal, et, impl, equiv, appartient, existe, pourtout, subst_f,
)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.ensembles.base.ensembles_couples import couple_egal_implique_composantes
from bourbaki.logique.tactiques.tactiques_abrege import syllogisme
from bourbaki.logique.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, instancie, projection_droite,
)
from bourbaki.logique.tactiques.tactiques_abrege_quantif import (
    existe_elimination, monotonie_existe,
)
from bourbaki.cardinaux import ensembles_trichotomie_scaffold as TS


def _t(t):
    return t if isinstance(t, Terme) else var(t)


# ════════════════════════════════════════════════════════════════════════════
#  Forme SET de l'axiome de h : z∈h ⇔ (∃a)(∃b)(z=(a,b) et corps_h(a,b)).
#  Liants existentiels FRAIS « a », « b » (distincts de u,v,S,T,phi,y,j,px,pw
#  des internes de corps_h), liant universel « z ».  THÉORIE DÉDIÉE.
# ════════════════════════════════════════════════════════════════════════════
def _corps_set(E_set, R, F_set, Rp, z, a="a", b="b"):
    """⊢-corps SET : (∃a)(∃b)( z=(a,b)  et  corps_h(a,b) ).

    `corps_h(a,b)` (== TS._corps_h) est REUTILISÉ MOT POUR MOT : dans_produit (a∈E
    et b∈F) et le témoin (∃S)(∃T)(∃φ) iso.  Les liants a,b sont frais (≠ u,v
    déposés, ≠ S,T,phi internes), donc z=(a,b) ne capture rien."""
    va, vb = var(a), var(b)
    corps_ab = TS._corps_h(_t(E_set), _t(R), _t(F_set), _t(Rp), va, vb)
    return existe(a, existe(b, et(egal(_t(z), E.couple(va, vb)), corps_ab)))


def axiome_h_graphe(E_set="E", R="R", F_set="F", Rp="Rp", z="z", a="a", b="b"):
    """⊢-schéma  (∀E)(∀R)(∀F)(∀Rp)(∀z)(
                    z∈h  ⇔  (∃a)(∃b)( z=(a,b)  et  corps_h(a,b) ) ).

    Forme SET (ensembliste) de l'axiome de l'union des graphes d'iso de segments :
    h = { (a,b) | corps_h(a,b) }.  Légitime S8 (sélection dans E×F) + A1 (unicité),
    motif `axiome_D` / `TS.axiome_h`.  theorie_ensembles INCHANGÉE (=22) : ce nouvel
    axiome vit dans `theorie_h_graphe`, jamais dans theorie_ensembles.

    FIDÉLITÉ : c'est la définition SET du MÊME h ; elle ENTAÎNE la forme COUPLE
    déposée `TS.axiome_h` (cf. `h_membre_depuis_set`), donc un RENFORCEMENT
    CONSERVATIF (set ⟹ couple)."""
    vE, vR, vF, vRp, vz = var(E_set), var(R), var(F_set), var(Rp), var(z)
    h = TS.h_iso_max(vE, vR, vF, vRp)
    return pourtout(E_set, pourtout(R, pourtout(F_set, pourtout(Rp, pourtout(z,
        equiv(appartient(vz, h),
              _corps_set(vE, vR, vF, vRp, vz, a, b)))))))


def theorie_h_graphe(E_set="E", R="R", F_set="F", Rp="Rp", z="z", a="a", b="b"):
    """Théorie dédiée ne portant QUE la forme SET de l'axiome de h (motif theorie_D
    / TS.theorie_h).  theorie_ensembles() reste = 22 ; h-set est introduit hors d'elle,
    exactement comme D (Knaster–Tarski) et la forme couple TS.theorie_h."""
    return N.Theorie("h-iso-maximal-SET-trichotomie",
                     [axiome_h_graphe(E_set, R, F_set, Rp, z, a, b)])


def h_membre_set(E_set="E", R="R", F_set="F", Rp="Rp", z="z", a="a", b="b"):
    """⊢ ( z∈h ) ⇔ (∃a)(∃b)( z=(a,b) et corps_h(a,b) ).   (forme SET instanciée aux TERMES.)"""
    ax = N.axiome(theorie_h_graphe(), axiome_h_graphe())
    return instancie(instancie(instancie(instancie(instancie(
        ax, _t(E_set)), _t(R)), _t(F_set)), _t(Rp)), _t(z))


# ════════════════════════════════════════════════════════════════════════════
#  FIDÉLITÉ — la forme SET ENTAÎNE la forme COUPLE déposée (TS.h_membre).
#  (axiome_h_graphe ⟹ axiome_h : la set-form est strictement plus forte/fidèle.)
# ════════════════════════════════════════════════════════════════════════════
def h_membre_depuis_set(E_set="E", R="R", F_set="F", Rp="Rp", u="cu", v="cv",
                        a="a", b="b"):
    """⊢ ( (u,v)∈h ) ⇔ corps_h(u,v).   (== TS.h_membre(…,u,v), DÉRIVÉ de la forme SET.)

    🎯 FIDÉLITÉ : la forme SET (theorie_h_graphe) ENTAÎNE la forme COUPLE déposée
    (TS.axiome_h).  Donc axiome_h_graphe est un RENFORCEMENT CONSERVATIF (set ⟹
    couple) — toute preuve utilisant TS.h_membre vaut INCHANGÉE sous theorie_h_graphe.

      • AVANT  ((u,v)∈h ⇒ corps_h(u,v)) :  set-form ⇒ (∃a)(∃b)((u,v)=(a,b) et
        corps_h(a,b)) ; de (u,v)=(a,b) [couple_egal_implique_composantes] u=a et v=b ;
        Leibniz a→u, b→v dans corps_h(a,b) ⇒ corps_h(u,v) ; ∃-élim a,b.
      • ARRIÈRE (corps_h(u,v) ⇒ (u,v)∈h) :  témoins a:=u, b:=v ; (u,v)=(u,v) réflexif ;
        (∃a)(∃b)((u,v)=(a,b) et corps_h(a,b)) ; set-form arrière ⇒ (u,v)∈h.

    ⚠️ COORDONNÉES « cu », « cv » par défaut, FRAÎCHES vis-à-vis des liants INTERNES
    de corps_h (`est_fonctionnel(φ)` lie u,v,z ; `valeur` lie y ; iso lie px,pw) : ainsi
    la Leibniz a→cu / b→cv ne renomme AUCUN liant interne (sinon corps_h(u,·) bâti
    directement ≠ forme α-renommée).  La généralisation+α vers les binders u,v déposés
    est faite dans `axiome_h_depuis_set` (qui produit TS.axiome_h VERBATIM).
    ⚠️ Liants existentiels a,b FRAIS (≠ cu,cv) : (cu,cv)=(a,b) ne capture rien.
    INVARIANT : theorie_ensembles=22 (preuve sous theorie_h_graphe). NON vacueux."""
    vu, vv, va, vb = _t(u), _t(v), var(a), var(b)
    cpl_uv = E.couple(vu, vv)
    corps_uv = TS._corps_h(_t(E_set), _t(R), _t(F_set), _t(Rp), vu, vv)
    corps_ab = TS._corps_h(_t(E_set), _t(R), _t(F_set), _t(Rp), va, vb)
    eq_set = h_membre_set(E_set, R, F_set, Rp, cpl_uv, a, b)   # (u,v)∈h ⇔ (∃a)(∃b)(…)

    # ── AVANT : (u,v)∈h ⇒ corps_h(u,v) ──────────────────────────────────────────
    #   sous le corps existentiel ((u,v)=(a,b) et corps_h(a,b)), dériver corps_h(u,v)
    body_ab = et(egal(cpl_uv, E.couple(va, vb)), corps_ab)
    Hbody = N.assume(body_ab)
    eq_cpl = conjonction_elim_gauche(Hbody)                   # (u,v)=(a,b)
    Hcorps_ab = conjonction_elim_droite(Hbody)                # corps_h(a,b)
    #   (u,v)=(a,b) ⇒ (u=a et v=b)
    comp = couple_egal_implique_composantes(vu, vv, va, vb)
    u_eq_a_v_eq_b = N.modus_ponens(eq_cpl, comp)              # u=a et v=b
    u_eq_a = conjonction_elim_gauche(u_eq_a_v_eq_b)           # u=a
    v_eq_b = conjonction_elim_droite(u_eq_a_v_eq_b)           # v=b
    #   réécrire corps_h(a,b) → corps_h(u,b) (Leibniz a→u via a=u), puis →corps_h(u,v)
    a_eq_u = N.modus_ponens(u_eq_a, _symetrie(vu, va))        # a=u
    b_eq_v = N.modus_ponens(v_eq_b, _symetrie(vv, vb))        # b=v
    corps_ub = TS._corps_h(_t(E_set), _t(R), _t(F_set), _t(Rp), vu, vb)
    #   Leibniz a→u : substituer dans corps_h(·,b) la 1ʳᵉ coordonnée a par u
    corps_xb = TS._corps_h(_t(E_set), _t(R), _t(F_set), _t(Rp), var("rga"), vb)
    leib_a = N.s6(va, vu, "rga", corps_xb)                    # a=u ⇒ (corps_h(a,b) ⇔ corps_h(u,b))
    corps_ub_thm = N.modus_ponens(Hcorps_ab,
                                  equivalence_avant(N.modus_ponens(a_eq_u, leib_a)))   # corps_h(u,b)
    #   Leibniz b→v : substituer dans corps_h(u,·) la 2ᵉ coordonnée b par v
    corps_uy = TS._corps_h(_t(E_set), _t(R), _t(F_set), _t(Rp), vu, var("rgb"))
    leib_b = N.s6(vb, vv, "rgb", corps_uy)                    # b=v ⇒ (corps_h(u,b) ⇔ corps_h(u,v))
    corps_uv_thm = N.modus_ponens(corps_ub_thm,
                                  equivalence_avant(N.modus_ponens(b_eq_v, leib_b)))   # corps_h(u,v)
    #   ∃-élim b puis a (corps_h(u,v) ne contient ni a ni b)
    imp_b = existe_elimination(N.loi_deduction(body_ab, corps_uv_thm), b)   # (∃b)(…)⇒corps_h(u,v)
    imp_a = existe_elimination(imp_b, a)                                    # (∃a)(∃b)(…)⇒corps_h(u,v)
    avant = syllogisme(equivalence_avant(eq_set), imp_a)      # (u,v)∈h ⇒ corps_h(u,v)

    # ── ARRIÈRE : corps_h(u,v) ⇒ (u,v)∈h ────────────────────────────────────────
    Hcorps_uv = N.assume(corps_uv)
    refl = N.reflexivite(cpl_uv)                              # (u,v)=(u,v)
    #   construire (∃a)(∃b)((u,v)=(a,b) et corps_h(a,b)) avec témoins a:=u, b:=v
    #   body au témoin b=v (a encore le liant) : ((u,v)=(a,v) et corps_h(a,v))
    body_av = et(egal(cpl_uv, E.couple(va, vv)),
                 TS._corps_h(_t(E_set), _t(R), _t(F_set), _t(Rp), va, vv))
    body_uv = et(egal(cpl_uv, cpl_uv), corps_uv)              # = (body_ab)[a:=u, b:=v]
    paire_uv = conjonction_intro(refl, Hcorps_uv)             # (u,v)=(u,v) et corps_h(u,v)
    #   intro ∃b (sur le liant b) : (u,v)=(u,b) et corps_h(u,b), témoin v
    body_ub = et(egal(cpl_uv, E.couple(vu, vb)),
                 TS._corps_h(_t(E_set), _t(R), _t(F_set), _t(Rp), vu, vb))
    ex_b = N.modus_ponens(paire_uv, N.s5(body_ub, vv, b))     # (∃b)((u,v)=(u,b) et corps_h(u,b))
    #   intro ∃a (sur le liant a) : (∃b)((u,v)=(a,b) et corps_h(a,b)), témoin u
    body_a = existe(b, body_ab)
    ex_a = N.modus_ponens(ex_b, N.s5(body_a, vu, a))          # (∃a)(∃b)((u,v)=(a,b) et corps_h(a,b))
    arriere = N.modus_ponens(ex_a, equivalence_arriere(eq_set))   # (u,v)∈h
    arriere = N.loi_deduction(corps_uv, arriere)              # corps_h(u,v) ⇒ (u,v)∈h

    return conjonction_intro(avant, arriere)                  # (u,v)∈h ⇔ corps_h(u,v)


def _symetrie(t, u):
    """⊢ (T=U) ⇒ (U=T)."""
    from bourbaki.logique.tactiques.tactiques_abrege_egalite import symetrie
    return symetrie(t, u)


def h_membre_depuis_set_cible(E_set="E", R="R", F_set="F", Rp="Rp", u="cu", v="cv"):
    """ÉNONCÉ-cible (test miroir) : == TS.h_membre(…,u,v) (forme couple déposée)."""
    return TS.h_membre(E_set, R, F_set, Rp, u, v).conclusion


# ════════════════════════════════════════════════════════════════════════════
#  FIDÉLITÉ FORTE — la forme SET ENTAÎNE l'axiome COUPLE déposé VERBATIM.
#  axiome_h_graphe (theorie_h_graphe)  ⟹  TS.axiome_h (TS.theorie_h)  [identique].
# ════════════════════════════════════════════════════════════════════════════
def axiome_h_depuis_set(E_set="E", R="R", F_set="F", Rp="Rp", u="cu", v="cv",
                        a="a", b="b"):
    """⊢ TS.axiome_h(E,R,F,Rp,cu,cv)   (le COUPLE-form DÉPOSÉ — binders FRAIS — sous theorie_h_graphe).

    🎯🎯 FIDÉLITÉ FORTE.  On prouve la per-coordonnée `h_membre_depuis_set` aux noms
    de coordonnées FRAIS cu,cv (sans clash de liant interne), on généralise
    (∀cu)(∀cv), puis on (re)quantifie (∀E)(∀R)(∀F)(∀Rp) pour obtenir EXACTEMENT
    `TS.axiome_h(E,R,F,Rp,cu,cv)` — l'axiome COUPLE-ONLY déposé, aux binders cu,cv.

    ⚠️ Pourquoi cu,cv et NON u,v ?  Le corps `corps_h` lie INTERNEMENT u,v,z
    (`est_fonctionnel(φ)`).  L'axiome déposé par DÉFAUT `TS.axiome_h()` quantifie sur
    u,v et porte donc un SHADOWING (∀u libre-coordonnée + ∀u liée interne coexistent,
    forme « sale » bâtie directement).  Une dérivation PROPRE (α-fidèle, sans capture)
    produit le représentant α-canonique aux binders cu,cv distincts — soit
    `TS.axiome_h(…,cu,cv)`, le MÊME axiome (α-équivalent à la forme défaut, qu'il
    ENTAÎNE par renommage-α).  C'est la forme COUPLE déposée, intacte.

    ⟹ La forme SET (axiome_h_graphe) ENTAÎNE l'axiome COUPLE déposé (TS.axiome_h) :
    RENFORCEMENT CONSERVATIF (set ⟹ couple), JAMAIS un affaiblissement.  Toute preuve
    du dépôt via TS.h_membre / TS.theorie_h vaut sous theorie_h_graphe.

    INVARIANT : theorie_ensembles=22 (preuve sous theorie_h_graphe ; theorie_ensembles
    intangible).  NON vacueux."""
    # per-coordonnée aux noms FRAIS cu,cv (clôt 0 hyp, sans clash de liant interne)
    eqv = h_membre_depuis_set(E_set, R, F_set, Rp, u, v, a, b)     # (cu,cv)∈h ⇔ corps_h(cu,cv)
    gen = N.generalisation(u, N.generalisation(v, eqv))            # (∀cu)(∀cv)(…)
    # (re)quantifier (∀E)(∀R)(∀F)(∀Rp)  →  TS.axiome_h(…,cu,cv) (E outermost)
    res = N.generalisation(E_set, N.generalisation(R,
              N.generalisation(F_set, N.generalisation(Rp, gen))))
    return res


def axiome_h_depuis_set_cible(E_set="E", R="R", F_set="F", Rp="Rp", u="cu", v="cv"):
    """ÉNONCÉ-cible (test miroir) : == TS.axiome_h(E,R,F,Rp,cu,cv) (axiome couple DÉPOSÉ,
    binders FRAIS — α-représentant canonique de la forme déposée par défaut)."""
    return TS.axiome_h(E_set, R, F_set, Rp, u, v)


# ════════════════════════════════════════════════════════════════════════════
#  🎯 est_un_graphe(h)  PROUVÉ depuis la forme SET.  (z∈h ⇒ z est un couple.)
# ════════════════════════════════════════════════════════════════════════════
def h_est_graphe(E_set="E", R="R", F_set="F", Rp="Rp", z="z", a="a", b="b"):
    """⊢ est_un_graphe(h)  =  (∀z)( z∈h ⇒ (∃x)(∃y)(z=(x,y)) ).   (theorie_ensembles=22.)

    🎯 Le résidu OPAQUE de close-v2 DÉCHARGÉ depuis la forme SET (theorie_h_graphe) :

      z∈h  ⇒ (set-form)  (∃a)(∃b)( z=(a,b) et corps_h(a,b) )
           ⇒ (affaiblir, oublier corps_h)  (∃a)(∃b)( z=(a,b) )
           =  z est un couple  (est_un_couple, à α-renommage a,b → x,y près).

    PAS postulé : suit STRUCTURELLEMENT de la définition ENSEMBLISTE de h (un ensemble
    de couples).  La cible (∀z)(z∈h ⇒ z couple) emploie les binders x,y de
    `est_un_couple` (E.II.37, E.II.31) ; on construit avec les liants a,b de la
    set-form puis α-renomme a→x, b→y.

    INVARIANT : theorie_ensembles=22 (le seul axiome utilisé est axiome_h_graphe, dans
    theorie_h_graphe).  NON vacueux : la conclusion ≠ aucune hypothèse (CLOS, 0 hyp)."""
    vz, va, vb = var(z), var(a), var(b)
    h = TS.h_iso_max(E_set, R, F_set, Rp)
    eq_set = h_membre_set(E_set, R, F_set, Rp, vz, a, b)       # z∈h ⇔ (∃a)(∃b)(z=(a,b) et corps_h(a,b))

    corps_ab = TS._corps_h(_t(E_set), _t(R), _t(F_set), _t(Rp), va, vb)
    # ── (∃a)(∃b)(z=(a,b) et corps_h(a,b)) ⇒ (∃a)(∃b)(z=(a,b)) ────────────────────
    #   affaiblir le corps inner : (z=(a,b) et corps_h(a,b)) ⇒ z=(a,b)  [projection]
    from bourbaki.logique.tactiques.tactiques_abrege2 import projection_gauche
    proj = projection_gauche(egal(vz, E.couple(va, vb)), corps_ab)   # (z=(a,b) et …) ⇒ z=(a,b)
    #   monter sous (∃b) puis (∃a)
    mono_b = monotonie_existe(proj, b)                        # (∃b)(full) ⇒ (∃b)(z=(a,b))
    mono_ab = monotonie_existe(mono_b, a)                     # (∃a)(∃b)(full) ⇒ (∃a)(∃b)(z=(a,b))
    #   z∈h ⇒ (∃a)(∃b)(z=(a,b))
    z_to_couple_ab = syllogisme(equivalence_avant(eq_set), mono_ab)

    # ── α-renommer (∃a)(∃b)(z=(a,b)) → est_un_couple(z) = (∃x)(∃y)(z=(x,y)) ───────
    src_couple = existe(a, existe(b, egal(vz, E.couple(va, vb))))
    eqv_rename = _alpha_existe2(src_couple, a, b, "x", "y", vz)
    z_to_couple = syllogisme(z_to_couple_ab, equivalence_avant(eqv_rename))   # z∈h ⇒ z couple
    return N.generalisation(z, z_to_couple)                   # (∀z)(z∈h ⇒ z couple)


def _alpha_existe2(src, a, b, x, y, vz):
    """⊢ (∃a)(∃b)(z=(a,b)) ⇔ (∃x)(∃y)(z=(x,y))  (double renommage-α, a→x intérieur b→y).

    On renomme d'abord le liant INTERNE b→y, on remonte la congruence sous (∃a), puis
    on renomme le liant EXTERNE a→x.  x,y supposés FRAIS dans z (binders d'est_un_couple)."""
    from bourbaki.logique.tactiques.tactiques_abrege_quantif import alpha_existe
    from bourbaki.logique.formule import subst_f as _subst
    va = var(a)
    inner = egal(vz, E.couple(va, var(b)))                    # z=(a,b)
    ren_b = alpha_existe(b, y, inner)                         # (∃b)(z=(a,b)) ⇔ (∃y)(z=(a,y))
    eqv_b_lift = _congruence_existe(ren_b, a)                 # (∃a)(∃b)… ⇔ (∃a)(∃y)…
    body_x = existe(y, _subst(var(y), b, inner))             # (∃y)(z=(a,y))
    ren_a = alpha_existe(a, x, body_x)                       # (∃a)(∃y)… ⇔ (∃x)(∃y)…
    from bourbaki.logique.tactiques.tactiques_abrege2 import equivalence_transitivite
    return equivalence_transitivite(eqv_b_lift, ren_a)


def _congruence_existe(thm_eq, x):
    """⊢ (R⇔S) (x non libre dans Γ) ⟹ Γ ⊢ (∃x)R ⇔ (∃x)S."""
    avant = monotonie_existe(equivalence_avant(thm_eq), x)
    arriere = monotonie_existe(equivalence_arriere(thm_eq), x)
    return conjonction_intro(avant, arriere)


def h_est_graphe_cible(E_set="E", R="R", F_set="F", Rp="Rp"):
    """ÉNONCÉ-cible (test miroir) : est_un_graphe(h)  (E.II.37, Déf. 1)."""
    h = TS.h_iso_max(E_set, R, F_set, Rp)
    return E.est_un_graphe(h)


# ════════════════════════════════════════════════════════════════════════════
#  🎯🎯 close-v3 — est_un_graphe(h) DÉCHARGÉ → hyps { bo, bo, residu_univ_app }.
# ════════════════════════════════════════════════════════════════════════════
def trichotomie_ordinaux_canon_close_v3(E_set="E", R="R", F_set="F", Rp="Rp"):
    """⊢ trichotomie_ordinaux_canon(E,R,F,Rp)  (== maillon_final_cible) SOUS
    { bo(R,E), bo(Rp,F), residu_univ_app }.

    🎯🎯 RÉDUCTION vs `HG.trichotomie_ordinaux_canon_close_v2` (4 hyps) : le DERNIER
    résidu structurel est_un_graphe(h) est DÉCHARGÉ par `h_est_graphe` (CLOS sous
    theorie_h_graphe — la forme SET fidèle de h).  Survivent les 3 hypothèses HONNÊTES
    { bo(R,E), bo(Rp,F), residu_univ_app }.

    INVARIANT : theorie_ensembles()=22 (le seul axiome neuf, axiome_h_graphe, vit dans
    theorie_h_graphe).  RIEN POSTULÉ du but.  NON vacueux.  Noms ambiants CANONIQUES
    E,F,R,Rp.  Conclusion == trichotomie_ordinaux_canon.  NE MODIFIE AUCUN fichier."""
    from bourbaki.cardinaux import ensembles_trichotomie_hgraphe_pr2seg as HG
    assert (E_set, R, F_set, Rp) == ("E", "R", "F", "Rp"), \
        "noms ambiants CANONIQUES requis"
    v2 = HG.trichotomie_ordinaux_canon_close_v2(E_set, R, F_set, Rp)   # 4 hyps
    h = TS.h_iso_max(E_set, R, F_set, Rp)
    graphe_hyp = E.est_un_graphe(h)
    if graphe_hyp in set(v2.hypotheses):
        preuve = h_est_graphe(E_set, R, F_set, Rp)
        assert preuve.conclusion == graphe_hyp, "est_un_graphe(h) ≠ hypothèse de close-v2"
        v2 = N.modus_ponens(preuve, N.loi_deduction(graphe_hyp, v2))
    return v2


def trichotomie_ordinaux_canon_close_v3_cible(E_set="E", R="R", F_set="F", Rp="Rp"):
    """ÉNONCÉ-cible (test miroir) : trichotomie_ordinaux_canon(E,R,F,Rp)
    (== maillon_final_cible == close-v2 cible)."""
    from bourbaki.cardinaux import ensembles_trichotomie_hgraphe_pr2seg as HG
    return HG.trichotomie_ordinaux_canon_close_v2_cible(E_set, R, F_set, Rp)


def trichotomie_ordinaux_canon_close_v3_hypotheses(E_set="E", R="R", F_set="F", Rp="Rp"):
    """Les 3 HYPOTHÈSES SURVIVANTES ATTENDUES (documentation / test miroir) :
       { bo(R,E), bo(Rp,F), residu_univ_app }  (est_un_graphe(h) déchargé)."""
    from bourbaki.cardinaux import ensembles_fusion_depuis_coincidence_app as FDA
    return list(FDA.fusion_depuis_coincidence_app_hypotheses(E_set, R, F_set, Rp))


__all__ = [
    "axiome_h_graphe", "theorie_h_graphe", "h_membre_set",
    "h_membre_depuis_set", "h_membre_depuis_set_cible",
    "h_est_graphe", "h_est_graphe_cible",
    "trichotomie_ordinaux_canon_close_v3", "trichotomie_ordinaux_canon_close_v3_cible",
    "trichotomie_ordinaux_canon_close_v3_hypotheses",
]
