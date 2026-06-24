"""§III.1 n°5 — PROPOSITION 2 (E.III.7-8) : connexion de Galois, u∘v∘u = u.

ÉNONCÉ BOURBAKI (verbatim, E.III.7-8, scan p.110-111) :
    PROPOSITION 2. — Soient E, E' deux ensembles ordonnés, u: E→E' et v: E'→E
    deux applications DÉCROISSANTES, telles que pour tout x∈E et tout x'∈E', on ait
    v(u(x)) ≥ x et u(v(x')) ≥ x'.  Alors u∘v∘u = u et v∘u∘v = v.

    Preuve : « v(u(x))≥x entraîne u(v(u(x)))≤u(x) puisque u est décroissante ;
    d'autre part u(v(u(x)))≥u(x) en remplaçant x' par u(x) dans u(v(x'))≥x'.
    D'où la première égalité ; la seconde de même. »

CIBLE FORMALISÉE = la PREMIÈRE égalité u∘v∘u = u, au niveau « valeurs » : on prouve
que w (qui REPRÉSENTE le composite u∘v∘u, hyp. de nommage w(x)=u(v(u(x)))) coïncide
avec u sur E.  Conclusion (clos modulo hypothèses HONNÊTES) :

    ⊢ (∀x)(x∈E ⇒ w(x) = u(x))

sous des antécédents de Bourbaki (chacun figure dans l'énoncé ; AUCUN n'est la
conclusion) :
    1. est_decroissante(G, G', u, E, E')        u décroissante ;
    2. (∀t)(t∈E  ⇒ u(t)∈E')                       u envoie E dans E' ;
    3. (∀t')(t'∈E' ⇒ v(t')∈E)                     v envoie E' dans E ;
    4. (∀x)(x∈E  ⇒ (x, v(u(x)))∈G)                v(u(x)) ≥ x ;
    5. (∀x')(x'∈E' ⇒ (x', u(v(x')))∈G')           u(v(x')) ≥ x' ;
    6. (∀x)(x∈E  ⇒ w(x) = u(v(u(x))))             w = nom du composite u∘v∘u ;
    7. antisymetrie(G')                           l'ordre de E' est antisymétrique.

NOTE de FIDÉLITÉ — l'énoncé Bourbaki suppose aussi v DÉCROISSANTE
(est_decroissante(G',G,v,E',E)).  La PREUVE de Bourbaki de la PREMIÈRE égalité
u∘v∘u=u N'UTILISE PAS la décroissance de v (« la seconde [v∘u∘v=v] s'établit de
même » — c'est ELLE qui consomme la décroissance de v, par symétrie des rôles).
Aussi le théorème certifié ici ne porte-t-il QUE les 7 hypothèses RÉELLEMENT
employées : ajouter est_decroissante(G',G,v,…) eût été une hypothèse non
load-bearing (padding malhonnête).  Toutes les hypothèses listées sont vraiment
consommées dans la dérivation LCF.

Le composite u∘v∘u est nommé par défaut « wc » (et non « w ») : les tactiques
égalitaires symetrie/composer_egalites utilisent en interne le trou de substitution
« w » (E.III, S6) ; un symbole d'application réellement nommé « w » serait capturé
par ce trou.  « wc » est un symbole frais, jamais utilisé comme trou ni comme liant.

Convention « graphe » (cf. ensembles_ordre_relation / ensembles_ordre_monotone) :
« a ≤ b sur E » s'écrit (a,b)∈G, « a ≤' b sur E' » s'écrit (a,b)∈G' ; la valeur
f(x) au sens Bourbaki est E.valeur(f,x,b="j").  est_decroissante(G,G',u,E,E')
instanciée en (a,b) donne : (a∈E et b∈E et (a,b)∈G) ⇒ (u(b),u(a))∈G'.

STRATÉGIE (corps en x, sous x∈E), calquée sur composee_croissantes_est_croissante :
  (A) (u(v(u(x))), u(x))∈G' : de (x, v(u(x)))∈G [hyp 5] et u décroissante [hyp 1
      instanciée en (x, v(u(x))), après x∈E et v(u(x))∈E via hyps 3 puis 4] ;
  (B) (u(x), u(v(u(x))))∈G' : de hyp 6 instanciée en x':=u(x)∈E' [via hyp 3] ;
  (C) antisymetrie(G') [hyp 7] en (u(v(u(x))), u(x)) sur la conjonction (A)et(B)
      ⇒ u(v(u(x)))=u(x) ;
  (D) hyp 6 en x : w(x)=u(v(u(x))) ; composer_egalites (maillon u(v(u(x)))) avec
      (C) ⇒ w(x)=u(x).
  Décharge de x∈E (loi_deduction) puis generalisation(x).

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


def _terme(t):
    return t if isinstance(t, Terme) else var(t)


def _couple_dans(t, u, G):
    """Formule « (t,u) ∈ G »  (lecture « t ≤ u » pour l'ordre de graphe G)."""
    return appartient(E.couple(_terme(t), _terme(u)), _terme(G))


def _val(f, x):
    """f(x) au sens Bourbaki (liant frais « j », cf. ensembles_ordre_monotone)."""
    return E.valeur(_terme(f), _terme(x), b="j")


def _envoie_dans(f, A, B, t="t"):
    """Hypothèse « f envoie A dans B » := (∀t)(t∈A ⇒ f(t)∈B)."""
    vt, vA, vB = var(t), _terme(A), _terme(B)
    return pourtout(t, impl(appartient(vt, vA), appartient(_val(f, vt), vB)))


def _galois_vu(u, v, E_set, G, x="x"):
    """Inégalité de Galois v(u(x))≥x := (∀x)(x∈E ⇒ (x, v(u(x)))∈G).  (Hyp 5.)"""
    vx, vE = var(x), _terme(E_set)
    return pourtout(x, impl(appartient(vx, vE),
                            _couple_dans(vx, _val(v, _val(u, vx)), G)))


def _galois_uv(u, v, Ep_set, Gp, x="x"):
    """Inégalité de Galois u(v(x'))≥x' := (∀x')(x'∈E' ⇒ (x', u(v(x')))∈G').  (Hyp 6.)"""
    vx, vEp = var(x), _terme(Ep_set)
    return pourtout(x, impl(appartient(vx, vEp),
                            _couple_dans(vx, _val(u, _val(v, vx)), Gp)))


def _compose_uvu(w, u, v, E_set, x="x"):
    """Hypothèse « w représente u∘v∘u sur E » := (∀x)(x∈E ⇒ w(x)=u(v(u(x))))."""
    vx, vE = var(x), _terme(E_set)
    return pourtout(x, impl(appartient(vx, vE),
                            egal(_val(w, vx), _val(u, _val(v, _val(u, vx))))))


def galois_uvu_egale_u(G="G", Gp="Gp", u="u", v="v", w="wc",
                       E_set="E", Ep_set="Ep", x="x", y="y", t="t"):
    """{ est_decroissante(G,G',u,E,E'),
         (∀t)(t∈E⇒u(t)∈E'), (∀t')(t'∈E'⇒v(t')∈E),
         (∀x)(x∈E⇒(x,v(u(x)))∈G), (∀x')(x'∈E'⇒(x',u(v(x')))∈G'),
         (∀x)(x∈E⇒w(x)=u(v(u(x)))), antisymetrie(G') }
        ⊢ (∀x)(x∈E ⇒ w(x)=u(x)).

    PROPOSITION 2 (E.III.7-8), PREMIÈRE égalité u∘v∘u = u (connexion de Galois).
    Pour x∈E : u(v(u(x)))≤'u(x) (u décroissante appliquée à v(u(x))≥x) et
    u(x)≤'u(v(u(x))) (Galois u(v(x'))≥x' en x':=u(x)) ; antisymétrie de ≤' ⇒
    u(v(u(x)))=u(x) ; comme w(x)=u(v(u(x))), on obtient w(x)=u(x).

    7 hypothèses load-bearing (la décroissance de v ne sert qu'à la DUALE v∘u∘v=v ;
    cf. NOTE de fidélité du module — elle n'est donc pas une hypothèse ici)."""
    vx, vE = var(x), _terme(E_set)
    ux = _val(u, vx)                       # u(x)
    vux = _val(v, ux)                      # v(u(x))
    uvux = _val(u, vux)                    # u(v(u(x)))

    Hu_dec = N.assume(est_decroissante(G, Gp, u, E_set, Ep_set, x, y))   # u décroissante
    Hu_but = N.assume(_envoie_dans(u, E_set, Ep_set, t))                 # u(t)∈E'
    Hv_but = N.assume(_envoie_dans(v, Ep_set, E_set, t))                 # v(t')∈E
    Hg5 = N.assume(_galois_vu(u, v, E_set, G, x))                       # (x, v(u(x)))∈G
    Hg6 = N.assume(_galois_uv(u, v, Ep_set, Gp, x))                     # (x', u(v(x')))∈G'
    Hw = N.assume(_compose_uvu(w, u, v, E_set, x))                       # w(x)=u(v(u(x)))
    Has = N.assume(antisymetrie(Gp, x, y))                              # antisymétrie de ≤'

    # corps sous x∈E
    Hx = N.assume(appartient(vx, vE))                                   # x∈E
    ux_in = N.modus_ponens(Hx, instancie(Hu_but, vx))                   # u(x)∈E'
    vux_in = N.modus_ponens(ux_in, instancie(Hv_but, ux))              # v(u(x))∈E

    # (A) (u(v(u(x))), u(x))∈G' : u décroissante en (x, v(u(x)))
    x_le_vux = N.modus_ponens(Hx, instancie(Hg5, vx))                  # (x, v(u(x)))∈G
    dec_inst = instancie(instancie(Hu_dec, vx), vux)                  # (x∈E et v(u(x))∈E et (x,v(u(x)))∈G)⇒(u(v(u(x))),u(x))∈G'
    hyp_dec = conjonction_intro(conjonction_intro(Hx, vux_in), x_le_vux)
    A = N.modus_ponens(hyp_dec, dec_inst)                             # (u(v(u(x))), u(x))∈G'

    # (B) (u(x), u(v(u(x))))∈G' : Galois u(v(x'))≥x' en x':=u(x)
    B = N.modus_ponens(ux_in, instancie(Hg6, ux))                     # (u(x), u(v(u(x))))∈G'

    # (C) antisymétrie ⇒ u(v(u(x)))=u(x)
    antisym_inst = instancie(instancie(Has, uvux), ux)               # ((uvux,ux)∈G' et (ux,uvux)∈G')⇒uvux=ux
    uvux_eq_ux = N.modus_ponens(conjonction_intro(A, B), antisym_inst)  # u(v(u(x)))=u(x)

    # (D) w(x)=u(v(u(x))) puis transitivité (maillon u(v(u(x)))) ⇒ w(x)=u(x)
    wx_eq_uvux = N.modus_ponens(Hx, instancie(Hw, vx))                # w(x)=u(v(u(x)))
    wx_eq_ux = composer_egalites(wx_eq_uvux, uvux_eq_ux)             # w(x)=u(x)

    body = N.loi_deduction(appartient(vx, vE), wx_eq_ux)             # x∈E ⇒ w(x)=u(x)
    return N.generalisation(x, body)                                 # (∀x)(x∈E ⇒ w(x)=u(x))


__all__ = ["galois_uvu_egale_u"]
