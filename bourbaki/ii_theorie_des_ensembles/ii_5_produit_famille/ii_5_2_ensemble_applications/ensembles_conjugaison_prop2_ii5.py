"""§II.5.2 — PROPOSITION 2 (E II.31, n° 2), CAS INJECTIF (1°) — forme
rétraction/section, au niveau des GRAPHES fonctionnels.

ÉNONCÉ DE BOURBAKI (E II.31, Prop. 2).  Soient u : E'→E et v : F→F'.  L'application
f ↦ v∘f∘u de 𝓕(E;F) dans 𝓕(E';F') est
  (1°) INJECTIVE  si u est surjective et v injective ;
  (2°) SURJECTIVE si u est injective et v surjective ;
  et bijective (Corollaire) si u et v sont bijectives.
PREUVE de Bourbaki (1°) : « soit s une section de u, r une rétraction de v ; on a
r∘(v∘f∘u)∘s = f », donc deux applications f₁, f₂ de même conjuguée sont égales.

CE QU'ON FORMALISE ICI (cas 1°, honnête et CLOS).  Le VERROU-τ documenté dans
`ensembles_currying_ii5.py` (Prop. 2 REPORTÉE) porte sur la CONSTRUCTION de la
conjugaison f ↦ v∘f∘u comme OBJET-application (graphe-terme emballé) : évaluer ce
composé en un point τ déclenche la capture de liant de `valeur_caracterisation`
(cf. `composee_associee_droite_valeur`).  Le CONTENU d'injectivité, lui, n'a PAS
besoin de l'objet-conjugaison : « f ↦ v∘f∘u injective » signifie extensionnellement

    (v∘f₁∘u = v∘f₂∘u)  ⟹  (f₁ = f₂),

et l'hypothèse « conjuguées égales » se lit ponctuellement (extensionnalité)
    (∀x'∈E')  v(f₁(u(x'))) = v(f₂(u(x'))).
On DÉMONTRE alors f₁ = f₂ EXACTEMENT par la preuve de Bourbaki (s section de u, r
rétraction de v), mais en ÉVITANT le verrou : on n'évalue JAMAIS un composé en un
point-τ.  On quantifie d'abord sur un point GÉNÉRIQUE x' (aucune capture), puis on
INSTANCIE le ∀ obtenu au point-section s(x) (pure substitution capture-évitante) :

  f₁(x) = r(v(f₁(x)))            [r rétraction de v, sur f₁(x)∈F]
        = r(v(f₁(u(s(x)))))      [u(s(x))=x : s section de u ; congruence]
        = r(v(f₂(u(s(x)))))      [hypothèse « conjuguées égales » en x'=s(x)∈E']
        = r(v(f₂(x)))            [u(s(x))=x ; congruence]
        = f₂(x).                 [r rétraction de v, sur f₂(x)∈F]
Donc (∀x∈E) f₁(x)=f₂(x), d'où f₁=f₂ par extensionnalité fonctionnelle
(`graphe_egal_par_valeurs`).  Tout au niveau des VALEURS/GRAPHES : `composition_valeur`
n'est jamais appelée, donc AUCUNE capture de liant.

HYPOTHÈSES (toutes fidèles ; f₁,f₂ « applications » E→F au niveau graphe ; s : E→E'
section de u ; r rétraction de v ; conjuguées ponctuellement égales) — cf. `_hypotheses`.
Résultat CLOS (0 hypothèse non déchargée), rien postulé ; theorie_ensembles INCHANGÉE
(22 axiomes).  Le cas (2°) surjectif est traité (dual) dans
`ensembles_conjugaison_prop2_surj_ii5`.  Reste REPORTÉ : l'objet-conjugaison lui-même
(verrou-τ).  Voir [[bourbaki-fidelite-pdf]], [[bourbaki-verrou-tau-contournement]].
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, et, impl, appartient, pourtout)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, instancie, equivalence_avant)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
    symetrie, composer_egalites, congruence_terme)
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_4_fonctions.ensembles_extensionnalite import (
    graphe_egal_par_valeurs)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def _conj_valeur(vv, vf, vu, pt):
    """v(f(u(pt))) = valeur(v, valeur(f, valeur(u, pt)))  (conjuguée lue en pt)."""
    return E.valeur(vv, E.valeur(vf, E.valeur(vu, pt)))


def _hypotheses(vf1, vf2, vu, vv, vs, vr, vE, vEp, vFs):
    """Les 12 hypothèses ORDONNÉES de la Proposition 2 (1°), forme rétraction/section.

    Ordre (= ordre des antécédents de l'implication close renvoyée) :
      0-1  f₁, f₂ fonctionnels        4-5  dom f₁ = E, dom f₂ = E
      2-3  f₁, f₂ graphes             6-7  (∀x∈E) f₁(x)∈F, f₂(x)∈F   [applications E→F]
      8    est_section(s,u,E)         9    (∀x∈E) s(x)∈E'            [s : E→E']
      10   est_retraction(r,v,F)      11   (∀x'∈E') v(f₁(u(x')))=v(f₂(u(x')))
    """
    x, xp = var("x"), var("xp")
    return [
        E.est_fonctionnel(vf1),
        E.est_fonctionnel(vf2),
        E.est_un_graphe(vf1),
        E.est_un_graphe(vf2),
        egal(E.dom(vf1), vE),
        egal(E.dom(vf2), vE),
        pourtout("x", impl(appartient(x, vE), appartient(E.valeur(vf1, x), vFs))),
        pourtout("x", impl(appartient(x, vE), appartient(E.valeur(vf2, x), vFs))),
        # bound vars "p"/"q" ≠ "y" (le liant-τ interne de valeur) pour éviter la
        # capture de liant dans est_section/est_retraction (valeur(·,z)=τy(...)).
        E.est_section(vs, vu, vE, y="p"),                # (∀p∈E) u(s(p))=p
        pourtout("x", impl(appartient(x, vE), appartient(E.valeur(vs, x), vEp))),
        E.est_retraction(vr, vv, vFs, x="q"),            # (∀q∈F) r(v(q))=q
        pourtout("xp", impl(appartient(xp, vEp),
                            egal(_conj_valeur(vv, vf1, vu, xp),
                                 _conj_valeur(vv, vf2, vu, xp)))),
    ]


def _clore(hyps, concl):
    """⟹-curryfie concl sous les hypothèses hyps (H₀ ⇒ (H₁ ⇒ … ⇒ concl))."""
    for H in reversed(hyps):
        concl = impl(H, concl)
    return concl


# @livre Ch.II §5.2 Prop.2 | E II.31 L.14-33 | PDF p.82
def prop2_conjugaison_injective(f1="f1", f2="f2", u="u", v="v", s="s", r="r",
                                e="E", ep="Ep", but="F"):
    """⊢ (H₀ ⇒ … ⇒ H₁₁ ⇒ (f₁ = f₂)).   (PROPOSITION 2, cas 1° injectif, E II.31.)

    Forme rétraction/section CLOSE : sous les 12 hypothèses de `_hypotheses`
    (f₁,f₂ applications E→F ; s section E→E' de u ; r rétraction de v ; conjuguées
    v∘f₁∘u et v∘f₂∘u ponctuellement égales sur E'), on conclut f₁ = f₂ — l'énoncé
    extensionnel de « f ↦ v∘f∘u injective ».  Preuve de Bourbaki, sans jamais évaluer
    un composé en un point-τ (cf. docstring de module)."""
    vf1, vf2, vu, vv = _t(f1), _t(f2), _t(u), _t(v)
    vs, vr = _t(s), _t(r)
    vE, vEp, vFs = _t(e), _t(ep), _t(but)
    x = var("x")

    (H_fonc1, H_fonc2, H_gr1, H_gr2, H_dom1, H_dom2, H_type1, H_type2,
     H_sec, H_sectype, H_ret, H_conj) = _hypotheses(
        vf1, vf2, vu, vv, vs, vr, vE, vEp, vFs)

    h_fonc1, h_fonc2 = N.assume(H_fonc1), N.assume(H_fonc2)
    h_gr1, h_gr2 = N.assume(H_gr1), N.assume(H_gr2)
    h_dom1, h_dom2 = N.assume(H_dom1), N.assume(H_dom2)
    h_type1, h_type2 = N.assume(H_type1), N.assume(H_type2)
    h_sec, h_sectype = N.assume(H_sec), N.assume(H_sectype)
    h_ret, h_conj = N.assume(H_ret), N.assume(H_conj)

    # ── sous x∈E : établir f₁(x) = f₂(x) ────────────────────────────────────────
    hxE = N.assume(appartient(x, vE))

    sx = E.valeur(vs, x)                                  # s(x)
    sx_in_Ep = N.modus_ponens(hxE, instancie(h_sectype, x))          # s(x) ∈ E'
    # conjuguées égales au point-section : v(f₁(u(s(x)))) = v(f₂(u(s(x))))
    conj_at_sx = N.modus_ponens(sx_in_Ep, instancie(h_conj, sx))
    usx = E.valeur(vu, sx)                                # u(s(x))
    usx_eq_x = N.modus_ponens(hxE, instancie(h_sec, x))              # u(s(x)) = x

    # congruence u(s(x))→x sous v(f_i(·)) :  v(f_i(u(s(x)))) = v(f_i(x))
    cong1 = N.modus_ponens(usx_eq_x, congruence_terme(
        usx, x, E.valeur(vv, E.valeur(vf1, var("w")))))
    cong2 = N.modus_ponens(usx_eq_x, congruence_terme(
        usx, x, E.valeur(vv, E.valeur(vf2, var("w")))))
    v_f1_x = E.valeur(vv, E.valeur(vf1, x))              # v(f₁(x))
    v_f2_x = E.valeur(vv, E.valeur(vf2, x))              # v(f₂(x))
    v_f1_usx = E.valeur(vv, E.valeur(vf1, usx))          # v(f₁(u(s(x))))
    # v(f₁(x)) = v(f₁(u(s(x)))) = v(f₂(u(s(x)))) = v(f₂(x))
    eq_v = composer_egalites(composer_egalites(
        N.modus_ponens(cong1, symetrie(v_f1_usx, v_f1_x)), conj_at_sx), cong2)

    # rétraction : r(v(f_i(x))) = f_i(x)  (sous f_i(x)∈F)
    f1x_in_F = N.modus_ponens(hxE, instancie(h_type1, x))           # f₁(x) ∈ F
    f2x_in_F = N.modus_ponens(hxE, instancie(h_type2, x))           # f₂(x) ∈ F
    ret1 = N.modus_ponens(f1x_in_F, instancie(h_ret, E.valeur(vf1, x)))
    ret2 = N.modus_ponens(f2x_in_F, instancie(h_ret, E.valeur(vf2, x)))
    rv1, rv2 = E.valeur(vr, v_f1_x), E.valeur(vr, v_f2_x)
    f1x, f2x = E.valeur(vf1, x), E.valeur(vf2, x)
    # congruence v(f₁(x))→v(f₂(x)) sous r(·) : r(v(f₁(x))) = r(v(f₂(x)))
    cong_r = N.modus_ponens(eq_v, congruence_terme(v_f1_x, v_f2_x, E.valeur(vr, var("w"))))
    # f₁(x) = r(v(f₁(x))) = r(v(f₂(x))) = f₂(x)
    val_eq_x = composer_egalites(composer_egalites(
        N.modus_ponens(ret1, symetrie(rv1, f1x)), cong_r), ret2)

    imp_x = N.loi_deduction(appartient(x, vE), val_eq_x)            # x∈E ⇒ f₁(x)=f₂(x)
    vals_E = N.generalisation("x", imp_x)

    # ── passage x∈E → x∈dom f₁ (dom f₁ = E) pour graphe_egal_par_valeurs ─────────
    hx_dom = N.assume(appartient(x, E.dom(vf1)))
    leib_dom = N.s6(E.dom(vf1), vE, "w", appartient(x, var("w")))
    x_in_E = N.modus_ponens(hx_dom, equivalence_avant(N.modus_ponens(h_dom1, leib_dom)))
    fx_eq = N.modus_ponens(x_in_E, instancie(vals_E, x))           # f₁(x)=f₂(x)
    vals_dom = N.generalisation("x", N.loi_deduction(appartient(x, E.dom(vf1)), fx_eq))

    # dom f₁ = dom f₂  (= E)
    dom_eq = composer_egalites(h_dom1, N.modus_ponens(h_dom2, symetrie(E.dom(vf2), vE)))

    # extensionnalité fonctionnelle : (fonc,fonc,graphe,graphe,dom=,valeurs) ⇒ f₁=f₂
    hyp_gev = conjonction_intro(conjonction_intro(conjonction_intro(conjonction_intro(
        conjonction_intro(h_fonc1, h_fonc2), h_gr1), h_gr2), dom_eq), vals_dom)
    f1_eq_f2 = N.modus_ponens(hyp_gev, graphe_egal_par_valeurs(vf1, vf2))

    # clôture : décharger les 12 hypothèses (implication curryfiée, 0 hyp restante)
    hyps = _hypotheses(vf1, vf2, vu, vv, vs, vr, vE, vEp, vFs)
    resultat = f1_eq_f2
    for H in reversed(hyps):
        resultat = N.loi_deduction(H, resultat)
    return resultat


def cible_prop2_conjugaison_injective(f1="f1", f2="f2", u="u", v="v", s="s", r="r",
                                      e="E", ep="Ep", but="F"):
    """Conclusion EXACTE attendue de `prop2_conjugaison_injective` (pour les tests)."""
    vf1, vf2, vu, vv = _t(f1), _t(f2), _t(u), _t(v)
    vs, vr = _t(s), _t(r)
    vE, vEp, vFs = _t(e), _t(ep), _t(but)
    hyps = _hypotheses(vf1, vf2, vu, vv, vs, vr, vE, vEp, vFs)
    return _clore(hyps, egal(vf1, vf2))


__all__ = ["prop2_conjugaison_injective", "cible_prop2_conjugaison_injective"]
