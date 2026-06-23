"""§III.2 — Théorème 3 (TRICHOTOMIE) : PONT « valeur d'application » qui DÉCHARGE le
RÉSIDU REPRÉSENTATIONNEL de `coincidence_depuis_isos` (ensembles_coincidence_decharge).

────────────────────────────────────────────────────────────────────────────────
RÔLE.  `coincidence_depuis_isos` (ensembles_coincidence_decharge, CLOS sous 19 hyps)
conclut φ=φ' sur S à partir de DEUX ISOS (φ:S≅T, ψ=φ'⁻¹:T≅S, χ=φ⁻¹:T≅S) ET d'un
RÉSIDU géométrique b="j" porté EXPLICITEMENT sur les NOMS c=ψ∘φ et k=χ∘φ' :

    c,k : S→S,   c,k STRICTEMENT CROISSANTES (τ_j),   k∘c=id,   φ'(c(u))=φ(u).

Les hypothèses des deux isos sont écrites avec la CONVENTION de VALEUR par défaut
τ_y (`compatible_ordre` ⇒ `E.valeur(.,.,"y")`), tandis que la stricte croissance
résiduelle est écrite avec τ_j (`est_strictement_croissante` ⇒ `_val`=`E.valeur(.,.,"j")`).
Le mémo projet documente ce mélange comme le « VERROU LIANT VALEUR b="y" ↔ b="yv/j" ».

CE MODULE FRANCHIT ce verrou pour les conjoints STRICTE CROISSANCE, via le PONT
`valeur_j_egal_y` / `valeur_y_egal_j` (ensembles_valeur_bridge, CLOS) — un α-renommage
du liant τ certifié par `alpha_tau` (CS1).  On RÉCONCILIE ainsi les deux conventions
(Leibniz S6 sur l'égalité des valeurs) et l'on DÉRIVE la stricte croissance τ_j de c et
de k DEPUIS L'ORDRE-COMPATIBILITÉ et l'INJECTIVITÉ d'un ISO — c.-à-d. depuis le contenu
DÉJÀ présent dans `est_isomorphisme_ordre(c,S,S,R,R)`.

────────────────────────────────────────────────────────────────────────────────
CE QUE CE MODULE LIVRE (salvage fort GRADUÉ, honnête, theorie=22) :

  ✅ `compat_y_vers_jv(c,S,R)`  (PONT, CŒUR ROBUSTE) :
        { compatible_ordre(c,S,R,R)  [τ_y, liants frais a,b — bien formé] }
            ⊢ _compat_yv(c,S,R)      [τ_j, la forme consommée par lemme_4/iso_donne_strict].
     CONVERSION de la compatibilité d'ordre de la convention de valeur τ_y vers τ_j,
     par Leibniz (S6) sur les égalités `valeur(c,p,"y") = valeur(c,p,"j")` du pont.
     Une SEULE hypothèse (la compatibilité τ_y) ; rien postulé.

  ✅ `inj_y_vers_jv(c,S)`  (PONT injectivité) :
        { injective_dans(c,S)  [τ_y, liants u,up — bien formé] }
            ⊢ _inj_hyp(c,S)    [τ_j, la forme consommée par iso_donne_strict_croissant].
     Même technique (Leibniz sur les valeurs), une seule hypothèse.

  ✅ `strict_croissante_depuis_iso(c,S,R)`  (CHAÎNAGE — le gain « modulo isos ») :
        { est_isomorphisme_ordre(c,S,S,R,R)  [UNE clean iso, liants a,b] }
            ⊢ est_strictement_croissante(R,R,c,S,S)  [τ_j].
     🎯 La STRICTE CROISSANCE τ_j résiduelle de coincidence est DÉRIVÉE d'UN SEUL
     iso d'ordre de (S,R), via les deux ponts ci-dessus + `iso_donne_strict_croissant`
     (CLOS).  est_isomorphisme_ordre = est_bijective (⇒ injective_dans) ET
     compatible_ordre : exactement les deux entrées des ponts.  RIEN postulé.

  ✅ `coincidence_depuis_isos_compat(...)`  (RÉ-ASSEMBLAGE, résidu strict-croiss. DÉCHARGÉ) :
        comme `coincidence_depuis_isos`, MAIS les deux hyps de STRICTE CROISSANCE τ_j
        (c_scr, k_scr) sont REMPLACÉES par deux hyps d'ISO D'ORDRE
        est_isomorphisme_ordre(c,S,S,R,R), est_isomorphisme_ordre(k,S,S,R,R)  (clean).
        ⊢ (∀u)( u∈S ⇒ φ(u) = φ'(u) ).
     🎯 Le résidu REPRÉSENTATIONNEL « τ_j stricte croissance » de coincidence n'est plus
     une donnée À PART : il est ATTESTÉ depuis le langage UNIFORME des isos d'ordre (le
     même que celui de φ,ψ,χ).  Le séquent parle désormais d'iso(c), iso(k) (ordre-
     compatibilité + bijection), de la même nature que les isos déjà présents — la
     coïncidence est « inconditionnelle-MODULO-ISOS » pour la part stricte croissance.

────────────────────────────────────────────────────────────────────────────────
⚠️ REPORTÉ (résidu HONNÊTE restant, identifié précisément — non franchi sans toucher
   aux fichiers committés) :
     • `c:S→S` et `k:S→S` (les `(∀t)(t∈S⇒c(t)∈S)` τ_j) restent des hyps explicites :
       l'iso fournit `est_surjective` (image=S) et l'injectivité, mais le passage
       `image(c,S)=S` → `(∀t)(t∈S⇒valeur(c,t,"j")∈S)` exige la machinerie
       `valeur_dans_codomaine` (le « pont valeur/codomaine ») + un raccord de liant
       supplémentaire — REPORTÉ.
     • la RÉTRACTION `k∘c=id` (τ_j) et le RACCORD `φ'(c(u))=φ(u)` restent des hyps :
       ils encodent la relation k=c⁻¹ et φ'∘φ'⁻¹=id, dont la dérivation depuis les
       isos est la même glue « composition de graphes » REPORTÉE ailleurs (iso_unicite).
   Ces résidus sont MATHÉMATIQUEMENT des conséquences des isos ; le franchir relève
   de la même machinerie valeur/codomaine — hors périmètre de CE pont (qui cible la
   STRICTE CROISSANCE, le verrou τ_y↔τ_j explicitement nommé dans le mémo).

INVARIANT : theorie_ensembles() = 22 (`alpha_tau` est une primitive justifiée, pas un
axiome).  RÉUTILISE `valeur_j_egal_y`/`valeur_y_egal_j` (ensembles_valeur_bridge, CLOS),
`iso_donne_strict_croissant`/`_compat_yv`/`_inj_hyp` (ensembles_iso_unicite_finale, CLOS),
`coincidence_depuis_isos` (ensembles_coincidence_decharge, CLOS).  NE MODIFIE AUCUN
fichier existant.  Aucune tautologie, aucun affaiblissement, rien postulé ; les
conditionnels portent leurs hypothèses dans le séquent et la conclusion n'y figure pas.
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (
    Terme, var, egal, et, impl, appartient, pourtout, equiv,
)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    instancie, equivalence_avant,
    conjonction_elim_gauche, conjonction_elim_droite,
)
from bourbaki.ordre.iii_1_relations_ordre.isomorphismes_ordre.ensembles_valeur_bridge import valeur_y_egal_j
from bourbaki.ordre.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_vocab import (
    compatible_ordre, est_isomorphisme_ordre,
)
from bourbaki.ordre.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_monotone import est_strictement_croissante
from bourbaki.cardinaux.iii_2_trichotomie_ordinaux.iso_ordre.ensembles_iso_unicite_finale import (
    _compat_yv, _inj_hyp, iso_donne_strict_croissant,
)
from bourbaki.cardinaux.iii_2_trichotomie_ordinaux.lemme4_segments.ensembles_lemme4_croissante import _R_de
from bourbaki.cardinaux.iii_2_trichotomie_ordinaux.coincidence_fusion.ensembles_coincidence_decharge import (
    coincidence_depuis_isos, coincidence_depuis_isos_cible,
)


def _t(t):
    """Coercion nom→terme (accepte un Terme ou un nom de variable)."""
    return t if isinstance(t, Terme) else var(t)


# liants FRAIS pour les points d'instanciation (ne collisionnent NI avec « y »,
# le liant de valeur par défaut de E.valeur, NI avec « j », celui de _val/τ_j).
_P, _Q = "p", "q"


def _leib(hole, a, b, h_ab, phi_fun, h_phi_a):
    """De  ⊢ a=b  et  ⊢ Φ[a]  déduit  ⊢ Φ[b]   (Leibniz via S6, trou `hole`)."""
    eqv = N.modus_ponens(h_ab, N.s6(a, b, hole, phi_fun(var(hole))))
    return N.modus_ponens(h_phi_a, equivalence_avant(eqv))


# ════════════════════════════════════════════════════════════════════════════
#  PONT (1) — compatible_ordre [τ_y] ⊢ _compat_yv [τ_j].
#  Réconcilie la convention de valeur par défaut (τ_y) de compatible_ordre avec
#  la convention τ_j attendue par lemme_4 / iso_donne_strict_croissant, par
#  Leibniz (S6) sur les égalités valeur(c,p,"y")=valeur(c,p,"j") du pont.
# ════════════════════════════════════════════════════════════════════════════
def compat_y_vers_jv(c="c", S="S", R="R", ib_x="a", ib_y="b"):
    """⊢ { compatible_ordre(c,S,R,R)  [liants de quantif. ib_x,ib_y (déf. a,b)] }
            ⊢ _compat_yv(c,S,R)        [liants de quantif. x,y].

    ALIGNEMENT DES LIANTS de quantification.  ⚠️ Depuis que `compatible_ordre` adopte le
    liant-VALEUR « j » (= celui de `_val`, ETAPE binder-j), sa valeur c(x) est écrite
    `τ_j((x,j)∈c)` — EXACTEMENT comme `_compat_yv` (qui emploie `_val`).  L'ancien PONT
    de valeur τ_y→τ_j est donc devenu l'IDENTITÉ ; il ne reste que la renomination des
    LIANTS DE QUANTIFICATION (source a,b ↦ x,y attendus par `_compat_yv`), par
    instanciation/regénéralisation (α-renommage).  UNE seule hypothèse ; rien postulé.

    NON vacueux : la conclusion (liants x,y) DIFFÈRE structurellement de l'hypothèse
    (liants a,b) — `conclusion ∉ hypothèses` (vérifié par test)."""
    Rf = _R_de(R)
    vc, vS = _t(c), _t(S)
    # SOURCE compatible_ordre(c,S,R,R) DÉJÀ en τ_j (liant-valeur « j »), liants quantif ib_x,ib_y.
    co = compatible_ordre(vc, vS, Rf, Rf, x=ib_x, y=ib_y)
    # α-renommage a,b ↦ x,y : instancier le corps à x,y puis regénéraliser.
    co_inst = instancie(instancie(N.assume(co), var("x")), var("y"))
    return N.generalisation("x", N.generalisation("y", co_inst))  # _compat_yv(c,S,R)


def compat_y_vers_jv_cible(c="c", S="S", R="R"):
    """ÉNONCÉ-cible (test miroir) de compat_y_vers_jv : _compat_yv(c,S,R)."""
    return _compat_yv(_t(c), _t(S), _R_de(R))


# ════════════════════════════════════════════════════════════════════════════
#  PONT (2) — injective_dans [τ_y] ⊢ _inj_hyp [τ_j].
# ════════════════════════════════════════════════════════════════════════════
def inj_y_vers_jv(c="c", S="S"):
    """⊢ { injective_dans(c,S)  [τ_y, liants u,up — bien formé] }
            ⊢ _inj_hyp(c,S)      [τ_j].

    PONT « valeur b=y ↔ b=j » sur l'INJECTIVITÉ gardée.  Même technique que
    compat_y_vers_jv : instanciation à des points frais p,q, réécriture des valeurs
    c(p),c(q) de τ_y vers τ_j (Leibniz S6 + valeur_y_egal_j), regénéralisation en (x,y).
    `_inj_hyp` est l'EXACTE forme d'injectivité (τ_j) consommée par
    iso_donne_strict_croissant.  UNE seule hypothèse ; rien postulé.

    NON vacueux : conclusion τ_j ≠ hypothèse τ_y (liant de valeur distinct)."""
    vc, vS = _t(c), _t(S)
    inj = E.injective_dans(vc, vS)                               # τ_y, liants u,up
    vp, vq = var(_P), var(_Q)
    cp_y, cq_y = E.valeur(vc, vp), E.valeur(vc, vq)
    cp_j, cq_j = E.valeur(vc, vp, b="j"), E.valeur(vc, vq, b="j")
    eqp, eqq = valeur_y_egal_j(vc, vp), valeur_y_egal_j(vc, vq)

    inj_inst = instancie(instancie(N.assume(inj), vp), vq)
    base = et(appartient(vp, vS), appartient(vq, vS))
    # corps τ_y : (p∈S et q∈S et c(p)_y=c(q)_y) ⇒ p=q
    s1 = _leib("hole_inj_yjv1", cp_y, cp_j, eqp,
               lambda w: impl(et(base, egal(w, cq_y)), egal(vp, vq)), inj_inst)
    s2 = _leib("hole_inj_yjv2", cq_y, cq_j, eqq,
               lambda w: impl(et(base, egal(cp_j, w)), egal(vp, vq)), s1)
    gen = N.generalisation(_P, N.generalisation(_Q, s2))
    inst_xy = instancie(instancie(gen, var("x")), var("y"))
    return N.generalisation("x", N.generalisation("y", inst_xy))  # _inj_hyp(c,S)


def inj_y_vers_jv_cible(c="c", S="S"):
    """ÉNONCÉ-cible (test miroir) de inj_y_vers_jv : _inj_hyp(c,S)."""
    return _inj_hyp(_t(c), _t(S))


# ════════════════════════════════════════════════════════════════════════════
#  CHAÎNAGE — la STRICTE CROISSANCE τ_j de c est DÉRIVÉE d'UN SEUL iso d'ordre.
#  est_isomorphisme_ordre(c,S,S,R,R) = est_bijective (⇒ injective_dans) ET
#  compatible_ordre : exactement les deux entrées des deux ponts ci-dessus.
# ════════════════════════════════════════════════════════════════════════════
def strict_croissante_depuis_iso(c="c", S="S", R="R", ib_x="a", ib_y="b"):
    """⊢ { est_isomorphisme_ordre(c,S,S,R,R)  [UNE clean iso, liants ib_x,ib_y (déf. a,b)] }
            ⊢ est_strictement_croissante(R,R,c,S,S)  [τ_j].

    ib_x,ib_y = liants de quantif. de l'iso source (défaut a,b ; passer x,x2 pour
    apparier la sortie de composee_isomorphisme_ordre / auto_de_deux_isos).

    🎯 GAIN « MODULO ISOS » : la STRICTE CROISSANCE τ_j résiduelle de la coïncidence
    est DÉRIVÉE depuis UN SEUL iso d'ordre de (S,R) — pas postulée.  De l'iso on extrait
    `compatible_ordre(c,S,R,R)` (2ᵉ conjoint) et `injective_dans(c,S)` (1ᵉ conjoint de
    est_bijective) ; les deux ponts (compat_y_vers_jv, inj_y_vers_jv) les convertissent
    en _compat_yv (τ_j) et _inj_hyp (τ_j) ; `iso_donne_strict_croissant` (CLOS) conclut
    alors est_strictement_croissante(R,R,c,S,S).

    L'iso est écrit avec des liants FRAIS a,b dans compatible_ordre (forme bien formée
    sans capture du « y »).  RIEN postulé ; la conclusion (stricte croissance) n'est pas
    l'hypothèse (un iso).  UNE seule hypothèse : « c est un iso d'ordre de (S,R) »."""
    Rf = _R_de(R)
    vc, vS = _t(c), _t(S)
    iso = est_isomorphisme_ordre(vc, vS, vS, Rf, Rf, x=ib_x, y=ib_y)   # 1 hyp
    Hiso = N.assume(iso)
    bij = conjonction_elim_gauche(Hiso)                              # est_bijective(c,S,S)
    co = conjonction_elim_droite(Hiso)                              # compatible_ordre(c,S,R,R) [ib_x,ib_y]
    inj = conjonction_elim_gauche(bij)                              # injective_dans(c,S)

    # ponts : compat τ_y → τ_j  ;  inj τ_y → τ_j
    compat_jv = N.modus_ponens(
        co, N.loi_deduction(compatible_ordre(vc, vS, Rf, Rf, x=ib_x, y=ib_y),
                            compat_y_vers_jv(c, S, R, ib_x, ib_y)))  # _compat_yv(c,S,R)
    inj_jv = N.modus_ponens(
        inj, N.loi_deduction(E.injective_dans(vc, vS),
                             inj_y_vers_jv(c, S)))                   # _inj_hyp(c,S)

    # iso_donne_strict_croissant consomme _compat_yv + _inj_hyp ⊢ est_strictement_croissante
    idsc = iso_donne_strict_croissant(R, S, c)
    out = N.modus_ponens(compat_jv, N.loi_deduction(_compat_yv(vc, vS, Rf), idsc))
    out = N.modus_ponens(inj_jv, N.loi_deduction(_inj_hyp(vc, vS), out))
    return out                                                      # est_strictement_croissante


def strict_croissante_depuis_iso_cible(c="c", S="S", R="R"):
    """ÉNONCÉ-cible (test miroir) : est_strictement_croissante(R,R,c,S,S)."""
    return est_strictement_croissante(var(R), var(R), _t(c), _t(S), _t(S))


# ════════════════════════════════════════════════════════════════════════════
#  RÉ-ASSEMBLAGE — coïncidence depuis isos, résidu STRICTE CROISSANCE DÉCHARGÉ.
#  Les 2 hyps de stricte croissance τ_j (c_scr, k_scr) de coincidence_depuis_isos
#  sont remplacées par 2 hyps d'iso d'ordre (langage UNIFORME des isos).
# ════════════════════════════════════════════════════════════════════════════
def coincidence_depuis_isos_compat(phi="phi", phip="phip", psi="psi", chi="chi",
                                   S="S", T="T", c="c", k="k", u="u",
                                   G="G", Gp="Gp"):
    """⊢ { … hypothèses de coincidence_depuis_isos SAUF c_scr, k_scr …,
           est_isomorphisme_ordre(c,S,S,R,R),     [au lieu de c strict. croissante τ_j]
           est_isomorphisme_ordre(k,S,S,R,R) }    [au lieu de k strict. croissante τ_j]
         ⊢ (∀u)( u∈S ⇒ φ(u) = φ'(u) ).

    🎯 MAILLON Lemme 1 — coïncidence des deux isos sur leur chevauchement, où le RÉSIDU
    REPRÉSENTATIONNEL « stricte croissance τ_j » est DÉCHARGÉ par le pont.  On part de
    `coincidence_depuis_isos` (CLOS sous 19 hyps, dont c_scr,k_scr écrites avec τ_j) et
    l'on DÉCHARGE les deux conjoints de stricte croissance via
    `strict_croissante_depuis_iso` : chacun est ATTESTÉ depuis UN iso d'ordre de (S,R).

    Le séquent final parle alors d'iso(c,S,S,R,R), iso(k,S,S,R,R) — la MÊME nature
    d'hypothèse que les isos φ,ψ,χ déjà présents : la coïncidence est « inconditionnelle-
    MODULO-ISOS » pour la part STRICTE CROISSANCE, sans rien postuler ni affaiblir.  La
    conclusion φ=φ' sur S est INCHANGÉE (non tautologique : pas une hypothèse).

    ⚠️ Restent en hyps explicites (REPORTÉ documenté en tête de module) : c:S→S, k:S→S
    (machinerie valeur/codomaine), la rétraction k∘c=id et le raccord φ'(c(u))=φ(u)
    (glue « composition de graphes »).  Ce pont cible le verrou NOMMÉ τ_y↔τ_j."""
    base = coincidence_depuis_isos(phi, phip, psi, chi, S, T, c, k, u, G, Gp)

    c_scr = est_strictement_croissante(var("R"), var("R"), _t(c), _t(S), _t(S))
    k_scr = est_strictement_croissante(var("R"), var("R"), _t(k), _t(S), _t(S))
    sc_c = strict_croissante_depuis_iso(c, S, "R")   # iso(c,S,S,R,R) ⊢ c_scr
    sc_k = strict_croissante_depuis_iso(k, S, "R")   # iso(k,S,S,R,R) ⊢ k_scr

    out = N.modus_ponens(sc_c, N.loi_deduction(c_scr, base))   # décharge c_scr
    out = N.modus_ponens(sc_k, N.loi_deduction(k_scr, out))    # décharge k_scr
    return out                                                 # (∀u)(u∈S ⇒ φ(u)=φ'(u))


def coincidence_depuis_isos_compat_cible(phi="phi", phip="phip", psi="psi", chi="chi",
                                         S="S", T="T", c="c", k="k", u="u",
                                         G="G", Gp="Gp"):
    """ÉNONCÉ-cible (test miroir) de coincidence_depuis_isos_compat :
    (∀u)( u∈S ⇒ φ(u) = φ'(u) )  (identique à coincidence_depuis_isos_cible)."""
    return coincidence_depuis_isos_cible(phi, phip, psi, chi, S, T, c, k, u, G, Gp)


__all__ = [
    "compat_y_vers_jv", "compat_y_vers_jv_cible",
    "inj_y_vers_jv", "inj_y_vers_jv_cible",
    "strict_croissante_depuis_iso", "strict_croissante_depuis_iso_cible",
    "coincidence_depuis_isos_compat", "coincidence_depuis_isos_compat_cible",
]
