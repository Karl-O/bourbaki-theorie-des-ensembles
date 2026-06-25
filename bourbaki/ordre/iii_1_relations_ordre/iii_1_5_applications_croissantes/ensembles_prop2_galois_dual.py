"""§III.1 n°5 — PROPOSITION 2 (E.III.7-8) : connexion de Galois, v∘u∘v = v.

ÉNONCÉ BOURBAKI (verbatim, E.III.7-8, scan p.110-111) :
    PROPOSITION 2. — Soient E, E' deux ensembles ordonnés, u: E→E' et v: E'→E
    deux applications DÉCROISSANTES, telles que pour tout x∈E et tout x'∈E', on ait
    v(u(x)) ≥ x et u(v(x')) ≥ x'.  Alors u∘v∘u = u et v∘u∘v = v.

    Preuve : « v(u(x))≥x entraîne u(v(u(x)))≤u(x) puisque u est décroissante ;
    d'autre part u(v(u(x)))≥u(x) en remplaçant x' par u(x) dans u(v(x'))≥x'.
    D'où la première égalité ; la seconde de même. »  (E.III.8, L.1-7.)

CIBLE FORMALISÉE = la SECONDE égalité v∘u∘v = v, DUALE EXACTE (miroir) de la
première (`galois_uvu_egale_u`) par échange des rôles u↔v, E↔E', G↔G'.  « La
seconde s'établit de même » : on transpose littéralement la preuve de Bourbaki.
On prouve que w (qui REPRÉSENTE le composite v∘u∘v, hyp. de nommage
w(x')=v(u(v(x')))) coïncide avec v sur E'.  Conclusion (clos modulo hypothèses
HONNÊTES) :

    ⊢ (∀x')(x'∈E' ⇒ w(x') = v(x'))

sous des antécédents de Bourbaki (chacun figure dans l'énoncé ; AUCUN n'est la
conclusion) :
    1. est_decroissante(G', G, v, E', E)         v décroissante ;
    2. (∀t)(t∈E   ⇒ u(t)∈E')                       u envoie E dans E' ;
    3. (∀t')(t'∈E' ⇒ v(t')∈E)                      v envoie E' dans E ;
    4. (∀x')(x'∈E' ⇒ (x', u(v(x')))∈G')            u(v(x')) ≥ x' ;
    5. (∀x)(x∈E   ⇒ (x, v(u(x)))∈G)                v(u(x)) ≥ x ;
    6. (∀x')(x'∈E' ⇒ w(x') = v(u(v(x'))))          w = nom du composite v∘u∘v ;
    7. antisymetrie(G)                            l'ordre de E est antisymétrique.

NOTE de FIDÉLITÉ — exactement DUALE de celle du module primal.  La preuve de la
PREMIÈRE égalité u∘v∘u=u consomme la décroissance de U (et l'antisymétrie de ≤').
La SECONDE égalité v∘u∘v=v consomme, par symétrie, la décroissance de V et
l'antisymétrie de ≤ : c'est ELLE qui rend ces deux hypothèses load-bearing (« la
seconde s'établit de même »).  Le théorème certifié ici ne porte donc QUE les 7
hypothèses RÉELLEMENT employées dans la dérivation duale ; ajouter la décroissance
de u eût été du padding malhonnête (non load-bearing ICI).

Le composite v∘u∘v est nommé par défaut « wc » (et non « w ») : les tactiques
égalitaires symetrie/composer_egalites utilisent en interne le trou de substitution
« w » (E.III, S6) ; un symbole d'application réellement nommé « w » serait capturé
par ce trou.  « wc » est un symbole frais, jamais utilisé comme trou ni comme liant.

Convention « graphe » (cf. ensembles_ordre_relation / ensembles_ordre_monotone) :
« a ≤ b sur E » s'écrit (a,b)∈G, « a ≤' b sur E' » s'écrit (a,b)∈G' ; la valeur
f(x) au sens Bourbaki est E.valeur(f,x,b="j").  est_decroissante(G',G,v,E',E)
instanciée en (a,b) donne : (a∈E' et b∈E' et (a,b)∈G') ⇒ (v(b),v(a))∈G.

STRATÉGIE (corps en x', sous x'∈E'), DUALE de galois_uvu_egale_u :
  (A) (v(u(v(x'))), v(x'))∈G : de (x', u(v(x')))∈G' [hyp 4] et v décroissante [hyp 1
      instanciée en (x', u(v(x'))), après x'∈E' et u(v(x'))∈E' via hyps 3 puis 2] ;
  (B) (v(x'), v(u(v(x'))))∈G : de hyp 5 instanciée en x:=v(x')∈E [via hyp 3] ;
  (C) antisymetrie(G) [hyp 7] en (v(u(v(x'))), v(x')) sur la conjonction (A)et(B)
      ⇒ v(u(v(x')))=v(x') ;
  (D) hyp 6 en x' : w(x')=v(u(v(x'))) ; composer_egalites (maillon v(u(v(x')))) avec
      (C) ⇒ w(x')=v(x').
  Décharge de x'∈E' (loi_deduction) puis generalisation(x').

STATUT : CLOS MODULO LES 7 HYPOTHÈSES HONNÊTES (théorème conditionnel certifié par
le noyau LCF ; aucun axiome ajouté, theorie_ensembles == 22).
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (
    Terme, var, egal, impl, appartient, pourtout,
)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_4_egalitaires.tactiques_abrege_egalite import composer_egalites
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    conjonction_intro, instancie,
)
from bourbaki.ordre.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_relation import (
    antisymetrie,
)
from bourbaki.ordre.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_monotone import (
    est_decroissante,
)
# Helpers internes RÉUTILISÉS du module primal (mêmes formules, rôles miroir) :
#   _couple_dans, _val, _envoie_dans, _galois_vu, _galois_uv.
from bourbaki.ordre.iii_1_relations_ordre.iii_1_5_applications_croissantes.ensembles_prop2_galois import (
    _terme, _couple_dans, _val, _envoie_dans, _galois_vu, _galois_uv,
)


def _compose_vuv(w, u, v, Ep_set, x="x"):
    """Hypothèse « w représente v∘u∘v sur E' » := (∀x')(x'∈E'⇒w(x')=v(u(v(x')))).

    DUAL de _compose_uvu (échange u↔v, E↔E')."""
    vx, vEp = var(x), _terme(Ep_set)
    return pourtout(x, impl(appartient(vx, vEp),
                            egal(_val(w, vx), _val(v, _val(u, _val(v, vx))))))


def cible_galois_vuv_egale_v(v="v", w="wc", Ep_set="Ep", x="x"):
    """Conclusion attendue (∀x')(x'∈E' ⇒ w(x')=v(x')), construite indépendamment."""
    vx, vEp = var(x), _terme(Ep_set)
    return pourtout(x, impl(appartient(vx, vEp),
                            egal(_val(w, vx), _val(v, vx))))


def hypotheses_galois_vuv(G="G", Gp="Gp", u="u", v="v", w="wc",
                          E_set="E", Ep_set="Ep", x="x", y="y", t="t"):
    """Les 7 hypothèses honnêtes load-bearing de la duale, en frozenset.

    Miroir de l'énoncé de galois_uvu_egale_u (u↔v, E↔E', G↔G')."""
    return frozenset({
        est_decroissante(Gp, G, v, Ep_set, E_set, x, y),  # 1. v décroissante E'→E
        _envoie_dans(u, E_set, Ep_set, t),                # 2. u envoie E dans E'
        _envoie_dans(v, Ep_set, E_set, t),                # 3. v envoie E' dans E
        _galois_uv(u, v, Ep_set, Gp, x),                  # 4. (x', u(v(x')))∈G'
        _galois_vu(u, v, E_set, G, x),                    # 5. (x, v(u(x)))∈G
        _compose_vuv(w, u, v, Ep_set, x),                 # 6. w(x')=v(u(v(x')))
        antisymetrie(G, x, y),                            # 7. antisymétrie de ≤
    })


# @livre Ch.III §1.5 Prop.2 | E III.8 L.1-7 (preuve commune ; « la seconde s'établit de même ») | PDF p.111
def galois_vuv_egale_v(G="G", Gp="Gp", u="u", v="v", w="wc",
                       E_set="E", Ep_set="Ep", x="x", y="y", t="t"):
    """{ est_decroissante(G',G,v,E',E),
         (∀t)(t∈E⇒u(t)∈E'), (∀t')(t'∈E'⇒v(t')∈E),
         (∀x')(x'∈E'⇒(x',u(v(x')))∈G'), (∀x)(x∈E⇒(x,v(u(x)))∈G),
         (∀x')(x'∈E'⇒w(x')=v(u(v(x')))), antisymetrie(G) }
        ⊢ (∀x')(x'∈E' ⇒ w(x')=v(x')).

    PROPOSITION 2 (E.III.7-8), SECONDE égalité v∘u∘v = v (connexion de Galois),
    DUALE EXACTE de galois_uvu_egale_u par échange des rôles u↔v, E↔E', G↔G'.
    Pour x'∈E' : v(u(v(x')))≤v(x') (v décroissante appliquée à u(v(x'))≥x') et
    v(x')≤v(u(v(x'))) (Galois v(u(x))≥x en x:=v(x')) ; antisymétrie de ≤ ⇒
    v(u(v(x')))=v(x') ; comme w(x')=v(u(v(x'))), on obtient w(x')=v(x').

    7 hypothèses load-bearing (la décroissance de u et l'antisymétrie de ≤' ne
    servent qu'à la PREMIÈRE égalité u∘v∘u=u ; cf. NOTE de fidélité du module —
    ce sont la décroissance de v et l'antisymétrie de ≤ qui sont consommées ICI)."""
    vxp, vEp = var(x), _terme(Ep_set)
    vxp_t = _val(v, vxp)                    # v(x')
    uvxp = _val(u, vxp_t)                   # u(v(x'))
    vuvxp = _val(v, uvxp)                   # v(u(v(x')))

    Hv_dec = N.assume(est_decroissante(Gp, G, v, Ep_set, E_set, x, y))  # v décroissante E'→E
    Hu_but = N.assume(_envoie_dans(u, E_set, Ep_set, t))               # u(t)∈E'
    Hv_but = N.assume(_envoie_dans(v, Ep_set, E_set, t))               # v(t')∈E
    Hg4 = N.assume(_galois_uv(u, v, Ep_set, Gp, x))                    # (x', u(v(x')))∈G'
    Hg5 = N.assume(_galois_vu(u, v, E_set, G, x))                      # (x, v(u(x)))∈G
    Hw = N.assume(_compose_vuv(w, u, v, Ep_set, x))                    # w(x')=v(u(v(x')))
    Has = N.assume(antisymetrie(G, x, y))                             # antisymétrie de ≤

    # corps sous x'∈E'
    Hxp = N.assume(appartient(vxp, vEp))                              # x'∈E'
    vxp_in = N.modus_ponens(Hxp, instancie(Hv_but, vxp))             # v(x')∈E
    uvxp_in = N.modus_ponens(vxp_in, instancie(Hu_but, vxp_t))       # u(v(x'))∈E'

    # (A) (v(u(v(x'))), v(x'))∈G : v décroissante en (x', u(v(x')))
    xp_le_uvxp = N.modus_ponens(Hxp, instancie(Hg4, vxp))           # (x', u(v(x')))∈G'
    dec_inst = instancie(instancie(Hv_dec, vxp), uvxp)             # (x'∈E' et u(v(x'))∈E' et (x',u(v(x')))∈G')⇒(v(u(v(x'))),v(x'))∈G
    hyp_dec = conjonction_intro(conjonction_intro(Hxp, uvxp_in), xp_le_uvxp)
    A = N.modus_ponens(hyp_dec, dec_inst)                          # (v(u(v(x'))), v(x'))∈G

    # (B) (v(x'), v(u(v(x'))))∈G : Galois v(u(x))≥x en x:=v(x')
    B = N.modus_ponens(vxp_in, instancie(Hg5, vxp_t))             # (v(x'), v(u(v(x'))))∈G

    # (C) antisymétrie ⇒ v(u(v(x')))=v(x')
    antisym_inst = instancie(instancie(Has, vuvxp), vxp_t)        # ((vuvxp,vxp')∈G et (vxp',vuvxp)∈G)⇒vuvxp=vxp'
    vuvxp_eq_vxp = N.modus_ponens(conjonction_intro(A, B), antisym_inst)  # v(u(v(x')))=v(x')

    # (D) w(x')=v(u(v(x'))) puis transitivité (maillon v(u(v(x')))) ⇒ w(x')=v(x')
    wxp_eq_vuvxp = N.modus_ponens(Hxp, instancie(Hw, vxp))        # w(x')=v(u(v(x')))
    wxp_eq_vxp = composer_egalites(wxp_eq_vuvxp, vuvxp_eq_vxp)   # w(x')=v(x')

    body = N.loi_deduction(appartient(vxp, vEp), wxp_eq_vxp)     # x'∈E' ⇒ w(x')=v(x')
    return N.generalisation(x, body)                             # (∀x')(x'∈E' ⇒ w(x')=v(x'))


__all__ = ["galois_vuv_egale_v", "cible_galois_vuv_egale_v", "hypotheses_galois_vuv"]
