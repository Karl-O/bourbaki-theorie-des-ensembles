"""§III.6.2 — C62, LA FONCTION GLOBALE :  f := ⋃𝔇_tot  (assemblage des essais).

C62 livre, pour chaque n∈ℕ, un ESSAI p_n (fonction partielle solution sur [0,n]) —
c'est `c62_recursion_sur_N`.  Bourbaki conclut « il existe UNE application f de ℕ … » :
il faut ASSEMBLER les essais en une fonction TOTALE.  Ce module construit l'objet :

    𝔇_tot := { p ∈ 𝔓(E×V) | (∃n)( n∈E  ∧  est_essai(p, T, ≤, E, n) ) }
    f     := ⋃𝔇_tot

(𝔇_tot = la famille de TOUS les essais — le sélecteur est « n∈E », là où la famille
par-x `Dfam_real(x)` de la démonstration C60 (hérédité) sélectionne « y∈seg(x) ».
Même motif S8 : sélection dans l'EXISTANT 𝔓(E×V), unicité A1, THÉORIE DÉDIÉE —
theorie_ensembles() reste = 22.)

CE QUI EST CLOS ICI (0 hypothèse, tout DÉRIVÉ) :
  • `membres_fonctionnels_tot`    ⊢ membres_fonctionnels(𝔇_tot)      [CLOS] ;
  • `valeur_membre_egale_regle_tot` {p∈𝔇_tot, a∈dom p} ⊢ valeur(p,a)=T(a)  [2 hyps] ;
  • `coincidence_membres_tot`     ⊢ coincidence_membres(𝔇_tot)       [CLOS]
        (les valeurs de TOUS les essais sont épinglées sur la même règle T par
         l'équation de récursion d'est_essai — la coïncidence est DIRECTE) ;
  • `famille_compatible_tot`      ⊢ famille_compatible(𝔇_tot)        [CLOS] ;
  • 🎯 `fonction_globale_fonctionnelle` ⊢ est_fonctionnel(f)          [CLOS].

La suite de l'assemblage (dom(f)=E, l'équation (∀n∈E) f(n)=T(n), le paquet (∃f))
vit dans `ensembles_c62_fonction_domaine` / `ensembles_c62_fonction_existence`.

NB (motif déposé) : comme pour `Dfam_real`, le TERME index `Dtot(E,V)` ne porte que
E et V — la relation R=(·,·)∈G et la règle T sont CAPTURÉES par le sélecteur de
l'axiome (théorie dédiée paramétrée par vh), pas par le terme.

INVARIANT : theorie_ensembles() = 22.  L'unique axiome introduit est celui de 𝔇_tot
(sélection S8 dans 𝔓(E×V)), dans la THÉORIE DÉDIÉE `theorie_Dtot`.  Rien postulé.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, app, egal, et, impl, equiv, appartient, existe, pourtout,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E

from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_elim_gauche, conjonction_elim_droite, equivalence_avant, instancie,
)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import existe_elimination
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
    symetrie, composer_egalites,
)

from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_recurrence_transfinie import _graphe_R
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_c60_existence_close import est_essai
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_c60_realisation import ambiant
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_c60_coeur import (
    union_famille, famille_compatible, union_famille_fonctionnelle,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_c60_final import (
    membres_fonctionnels, coincidence_membres, famille_compatible_depuis_coincidence,
)


def _t(t):
    """Coercion str/Terme → Terme."""
    return t if isinstance(t, Terme) else var(t)


# ════════════════════════════════════════════════════════════════════════════
#  LA CONSTRUCTION S8 — 𝔇_tot = { p∈𝔓(E×V) | (∃n∈E) est_essai(p,n) }.
#  Terme opaque + axiome DÉFINITIONNEL (motif EXACT de Dfam_real, c60_realisation).
# ════════════════════════════════════════════════════════════════════════════
def Dtot(e="Enat", V="Uval"):
    """𝔇_tot := { p ∈ 𝔓(E×V) | (∃n)( n∈E ∧ est_essai(p, T, ≤, E, n) ) }.

    La famille de TOUS les essais (sélection S8 dans l'EXISTANT 𝔓(E×V)).  Terme
    opaque (motif `Dfam_real`) : la règle T et l'ordre G sont capturés par le
    SÉLECTEUR de l'axiome (théorie dédiée), pas par le terme index."""
    return app("c62_Dtot", _t(e), _t(V))


def _corps_Dtot(vh, e, G, p, V="Uval", n="nDt"):
    """Corps de 𝔇_tot en p :  p∈𝔓(E×V)  et  (∃n)( n∈E ∧ est_essai(p,n) )."""
    R = _graphe_R(G)
    vp, vn = _t(p), var(n)
    amb = appartient(vp, ambiant(e, V))
    sel = existe(n, et(appartient(vn, _t(e)), est_essai(vp, vh, G, _t(e), vn)))
    return et(amb, sel)


def axiome_Dtot(vh, e="Enat", G="Gle", V="Uval", p="pDt", n="nDt"):
    """⊢-schéma  (∀p)( p∈𝔇_tot ⇔ ( p∈𝔓(E×V) ∧ (∃n∈E)( est_essai(p,n) ) ) ).

    Axiome DÉFINITIONNEL de la sélection S8 des essais DANS l'ensemble EXISTANT
    𝔓(E×V) (unicité A1) — motif `axiome_Dfam_real`.  N'altère PAS theorie_ensembles()."""
    vp = var(p)
    return pourtout(p, equiv(appartient(vp, Dtot(e, V)),
                             _corps_Dtot(vh, e, G, vp, V, n)))


def theorie_Dtot(vh, e="Enat", G="Gle", V="Uval", p="pDt", n="nDt"):
    """Théorie DÉDIÉE ne contenant que l'axiome de 𝔇_tot (C62-assemblage, S8)."""
    return N.Theorie("Dtot-C62", [axiome_Dtot(vh, e, G, V, p, n)])


def _inst_Dtot(vh, e, G, p, V="Uval", n="nDt"):
    """⊢ ( p∈𝔇_tot ⇔ (p∈𝔓(E×V) et (∃n∈E)est_essai(p,n)) )  (axiome instancié à p)."""
    ax = N.axiome(theorie_Dtot(vh, e, G, V, n=n), axiome_Dtot(vh, e, G, V, n=n))
    return instancie(ax, _t(p))


def membre_Dtot(vh, e="Enat", G="Gle", p="pDt", V="Uval", n="nDt"):
    """⊢ ( p∈𝔇_tot ) ⇔ ( p∈𝔓(E×V) et (∃n∈E)( est_essai(p,n) ) )."""
    return _inst_Dtot(vh, e, G, var(p), V, n)


def fonction_globale(e="Enat", V="Uval"):
    """f := ⋃𝔇_tot — LE candidat fonction totale de C62 (réunion de tous les essais)."""
    return union_famille(Dtot(e, V))


# ════════════════════════════════════════════════════════════════════════════
#  🎯 membres_fonctionnels(𝔇_tot)  [CLOS — motif membres_fonctionnels_realise].
# ════════════════════════════════════════════════════════════════════════════
def membres_fonctionnels_tot(vh, e="Enat", G="Gle", V="Uval", p="pmf", n="nDt"):
    """⊢ membres_fonctionnels( 𝔇_tot )                                  [CLOS, 0 hyp].

    Tout membre p de 𝔇_tot est FONCTIONNEL : par l'axiome S8, p est un essai d'un
    n∈E, et est_essai(p,n) CONTIENT est_fonctionnel(p) (1er conjoint).  Le témoin n
    est éliminé (existe_elimination, n∉est_fonctionnel(p))."""
    R = _graphe_R(G)
    ve = _t(e)
    Dt = Dtot(e, V)
    vp, vn = var(p), var(n)

    ax = _inst_Dtot(vh, e, G, vp, V, n)                          # p∈𝔇 ⇔ (amb et (∃n∈E)essai)
    h_pin = N.assume(appartient(vp, Dt))                         # p∈𝔇
    corps = N.modus_ponens(h_pin, equivalence_avant(ax))         # amb et (∃n∈E)essai
    sel = conjonction_elim_droite(corps)                         # (∃n)( n∈E et est_essai(p,n) )

    corps_n = et(appartient(vn, ve), est_essai(vp, vh, G, ve, vn))
    h_corps_n = N.assume(corps_n)
    essai_n = conjonction_elim_droite(h_corps_n)                 # est_essai(p,n)
    func_p = conjonction_elim_gauche(conjonction_elim_gauche(essai_n))   # est_fonctionnel(p)
    assert func_p.conclusion == E.est_fonctionnel(vp), \
        "membres_fonctionnels_tot : ≠ est_fonctionnel(p)"

    imp_n = N.loi_deduction(corps_n, func_p)                     # corps_n ⇒ func(p)
    ex_imp = existe_elimination(imp_n, n)                        # (∃n)corps_n ⇒ func(p)
    func_from_sel = N.modus_ponens(sel, ex_imp)                  # func(p)   [p∈𝔇]

    body = N.loi_deduction(appartient(vp, Dt), func_from_sel)    # p∈𝔇 ⇒ func(p)
    res = N.generalisation(p, body)

    cible = membres_fonctionnels(Dt, p)
    assert res.conclusion == cible, "membres_fonctionnels_tot : ≠ membres_fonctionnels(𝔇_tot)"
    assert res.est_clos, "membres_fonctionnels_tot : non clos"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  BRIQUE — l'équation de récursion d'un membre de 𝔇_tot en un antécédent.
# ════════════════════════════════════════════════════════════════════════════
def valeur_membre_egale_regle_tot(vh, e="Enat", G="Gle", V="Uval",
                                  p="pmv", a="amv", n="nDt"):
    """{ p∈𝔇_tot, a∈dom(p) } ⊢ valeur(p,a) = T(a)                     [2 hyps honnêtes].

    Tout membre p de 𝔇_tot est, par l'axiome S8, un essai d'un n∈E : est_essai(p,n)
    CONTIENT l'équation de récursion (∀z)(z∈dom p ⇒ valeur(p,z)=T(z)).  Donc en
    a∈dom(p), valeur(p,a)=T(a).  Le témoin n est ÉLIMINÉ (motif
    `valeur_membre_egale_regle`, c60_clauses)."""
    R = _graphe_R(G)
    ve = _t(e)
    Dt = Dtot(e, V)
    vp, va, vn = var(p), var(a), var(n)

    ax = _inst_Dtot(vh, e, G, vp, V, n)
    h_pin = N.assume(appartient(vp, Dt))                         # p∈𝔇   [HONNÊTE]
    corps = N.modus_ponens(h_pin, equivalence_avant(ax))
    sel = conjonction_elim_droite(corps)                         # (∃n)( n∈E et est_essai(p,n) )

    h_a = N.assume(appartient(va, E.dom(vp)))                    # a∈dom(p)   [HONNÊTE]

    corps_n = et(appartient(vn, ve), est_essai(vp, vh, G, ve, vn))
    h_corps_n = N.assume(corps_n)
    essai_n = conjonction_elim_droite(h_corps_n)                 # est_essai(p,n)
    eq_rec = conjonction_elim_droite(essai_n)                    # (∀z)(z∈dom p ⇒ valeur(p,z)=T(z))
    eq_a = N.modus_ponens(h_a, instancie(eq_rec, va))            # valeur(p,a)=T(a)
    assert eq_a.conclusion == egal(E.valeur(vp, va), vh(va)), \
        "valeur_membre_egale_regle_tot : équation ≠ valeur(p,a)=T(a)"

    imp_n = N.loi_deduction(corps_n, eq_a)
    ex_imp = existe_elimination(imp_n, n)                        # (∃n)corps_n ⇒ valeur(p,a)=T(a)
    res = N.modus_ponens(sel, ex_imp)                            # valeur(p,a)=T(a)  [p∈𝔇, a∈dom p]

    assert res.conclusion == egal(E.valeur(vp, va), vh(va))
    assert appartient(vp, Dt) in res.hypotheses, "valeur_membre_tot : p∈𝔇 absente"
    assert appartient(va, E.dom(vp)) in res.hypotheses, "valeur_membre_tot : a∈dom p absente"
    assert res.conclusion not in res.hypotheses, "valeur_membre_tot : VACUOUS"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  🎯 coincidence_membres(𝔇_tot)  [CLOS — les valeurs sont épinglées sur T].
# ════════════════════════════════════════════════════════════════════════════
def coincidence_membres_tot(vh, e="Enat", G="Gle", V="Uval", n="nDt"):
    """⊢ coincidence_membres( 𝔇_tot )                                   [CLOS, 0 hyp].

    Deux membres p,q de 𝔇_tot COÏNCIDENT en valeur sur tout antécédent commun a :
    valeur(p,a) = T(a) = valeur(q,a) (`valeur_membre_egale_regle_tot` deux fois).
    Motif EXACT de `coincidence_membres_realise` (c60_clauses)."""
    Dt = Dtot(e, V)
    p, q, a = "pcm", "qcm", "acm"                # binders canoniques de coincidence_membres
    vp, vq, va = var(p), var(q), var(a)

    prem_form = et(et(appartient(vp, Dt), appartient(vq, Dt)),
                   et(appartient(va, E.dom(vp)), appartient(va, E.dom(vq))))
    prem = N.assume(prem_form)
    pD = conjonction_elim_gauche(conjonction_elim_gauche(prem))    # p∈𝔇
    qD = conjonction_elim_droite(conjonction_elim_gauche(prem))    # q∈𝔇
    a_dp = conjonction_elim_gauche(conjonction_elim_droite(prem))  # a∈dom p
    a_dq = conjonction_elim_droite(conjonction_elim_droite(prem))  # a∈dom q

    vpa = valeur_membre_egale_regle_tot(vh, e, G, V, p, a, n)
    vpa = N.modus_ponens(pD, N.loi_deduction(appartient(vp, Dt), vpa))
    vpa = N.modus_ponens(a_dp, N.loi_deduction(appartient(va, E.dom(vp)), vpa))   # valeur(p,a)=T(a)
    vqa = valeur_membre_egale_regle_tot(vh, e, G, V, q, a, n)
    vqa = N.modus_ponens(qD, N.loi_deduction(appartient(vq, Dt), vqa))
    vqa = N.modus_ponens(a_dq, N.loi_deduction(appartient(va, E.dom(vq)), vqa))   # valeur(q,a)=T(a)

    vha_eq_vqa = N.modus_ponens(vqa, symetrie(E.valeur(vq, va), vh(va)))  # T(a)=valeur(q,a)
    val_eq = composer_egalites(vpa, vha_eq_vqa)                           # valeur(p,a)=valeur(q,a)

    imp = N.loi_deduction(prem_form, val_eq)
    res = N.generalisation(p, N.generalisation(q, N.generalisation(a, imp)))

    cible = coincidence_membres(Dt, p, q, a)
    assert res.conclusion == cible, "coincidence_membres_tot : ≠ coincidence_membres(𝔇_tot)"
    assert res.est_clos, "coincidence_membres_tot : non clos"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  🎯 famille_compatible(𝔇_tot)  [CLOS — via le pont de c60_final].
# ════════════════════════════════════════════════════════════════════════════
def famille_compatible_tot(vh, e="Enat", G="Gle", V="Uval", n="nDt"):
    """⊢ famille_compatible( 𝔇_tot )                                    [CLOS, 0 hyp].

    Le PONT `famille_compatible_depuis_coincidence` consomme membres_fonctionnels(𝔇)
    et coincidence_membres(𝔇), tous deux CLOS ici pour 𝔇_tot."""
    Dt = Dtot(e, V)
    pont = famille_compatible_depuis_coincidence(Dt)             # {mf, cm} ⊢ compat
    p1 = membres_fonctionnels_tot(vh, e, G, V, n=n)              # CLOS
    p2 = coincidence_membres_tot(vh, e, G, V, n)                 # CLOS
    res = N.modus_ponens(p1, N.loi_deduction(membres_fonctionnels(Dt), pont))
    res = N.modus_ponens(p2, N.loi_deduction(coincidence_membres(Dt), res))

    assert res.conclusion == famille_compatible(Dt), \
        "famille_compatible_tot : ≠ famille_compatible(𝔇_tot)"
    assert res.est_clos, "famille_compatible_tot : non clos"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  🎯🎯 CAPSTONE (fichier 1) — est_fonctionnel( f ),  f = ⋃𝔇_tot   [CLOS].
# ════════════════════════════════════════════════════════════════════════════
# @livre Ch.III §6.2 Demo.C62 | E III.46 L.14-20 | PDF p.149  (« il existe un ensemble U et une application f de ℕ » : assemblage des essais, f=⋃𝔇_tot fonctionnelle)
def fonction_globale_fonctionnelle(vh, e="Enat", G="Gle", V="Uval", n="nDt"):
    """🎯 ⊢ est_fonctionnel( f ),   f := ⋃𝔇_tot                          [CLOS, 0 hyp].

    LA fonction candidate de C62 est FONCTIONNELLE, inconditionnellement :
    `union_famille_fonctionnelle` sous famille_compatible(𝔇_tot), CLOS ci-dessus."""
    Dt = Dtot(e, V)
    uf = union_famille_fonctionnelle(Dt)                         # {compat(𝔇)} ⊢ func(⋃𝔇)
    compat = famille_compatible_tot(vh, e, G, V, n)              # CLOS
    res = N.modus_ponens(compat, N.loi_deduction(famille_compatible(Dt), uf))

    assert res.conclusion == E.est_fonctionnel(fonction_globale(e, V)), \
        "fonction_globale_fonctionnelle : ≠ est_fonctionnel(⋃𝔇_tot)"
    assert res.est_clos, "fonction_globale_fonctionnelle : non clos"
    return res


__all__ = [
    # la construction S8 de la famille TOTALE des essais + le terme f
    "Dtot", "axiome_Dtot", "theorie_Dtot", "membre_Dtot", "fonction_globale",
    # 🎯 briques closes
    "membres_fonctionnels_tot", "valeur_membre_egale_regle_tot",
    "coincidence_membres_tot", "famille_compatible_tot",
    # 🎯🎯 capstone fichier 1 : f est fonctionnelle
    "fonction_globale_fonctionnelle",
]
