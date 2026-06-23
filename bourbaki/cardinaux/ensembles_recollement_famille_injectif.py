"""§III.3 / §III.6.3 — INFRA RECOLLEMENT-INJECTIF en version FAMILLE (chaîne dirigée).

Version FAMILLE de la BINAIRE `reunion_graphes_injective`
(`bourbaki/ensembles/fonctions/ensembles_recollement_bijection.py`) : la réunion
⋃𝔇 d'une famille de graphes INJECTIFS qui est DIRIGÉE (toute paire de membres est
contenue dans un troisième — le cas typique d'une CHAÎNE emboîtée) est elle-même un
graphe INJECTIF.  C'est l'ingrédient « union des ψ = INJECTIVE » manquant de
l'inductivité de Zorn / Hessenberg (`ensembles_hessenberg_inductivite`, RÉSIDU
`enonce_chaine_majoree`), dont seule la FONCTIONNALITÉ (`union_chaine_fonctionnelle`)
et la valeur (`valeur_union_famille`) étaient closes.

ROUTE (miroir de la binaire, mais SANS la machinerie valeur/image-disjointe — on
travaille DIRECTEMENT sur les couples du graphe, ce qui évite le mur de capture de
la variable de valeur) :

  Soit (a,c),(b,c)∈⋃𝔇 (même image c).  Par l'axiome de ⋃𝔇 (C60) :
    (∃p)( p∈𝔇 et (a,c)∈p )   et   (∃q)( q∈𝔇 et (b,c)∈q ).
  On élimine les témoins p, q.  La DIRECTION (famille_dirigee) donne un r∈𝔇 avec
  p⊂r et q⊂r ; donc (a,c)∈r et (b,c)∈r.  r∈𝔇 ⇒ r INJECTIF (membres_injectifs)
  ⇒ a=b.  ∎

THÉORÈME (CLOS, 2 hypothèses HONNÊTES ; theorie=22) :
  • union_famille_injective
      { famille_dirigee(𝔇), membres_injectifs(𝔇) } ⊢ injectif_graphe(⋃𝔇).

RÉUTILISE l'infra FAMILLE de C60 (`membre_union_famille`, `union_famille`) — la même
qui sert à `union_famille_fonctionnelle`.  AUCUN axiome nouveau ; theorie=22.
"""
from __future__ import annotations

from bourbaki.logique.formule import (
    Terme, var, egal, et, impl, existe, pourtout, appartient, inclus,
)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, instancie,
)
from bourbaki.logique.tactiques.tactiques_abrege_quantif import (
    existe_elimination, alpha_existe,
)
from bourbaki.ordre.iii_2_bon_ordre.recurrence_transfinie.ensembles_c60_coeur import (
    union_famille, membre_union_famille, _inst_union_famille,
)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# ════════════════════════════════════════════════════════════════════════════
#  PRÉDICATS de la famille.
# ════════════════════════════════════════════════════════════════════════════
def injectif_graphe(p, a="ainj", b="binj", c="cinj"):
    """« le graphe p est INJECTIF » := (∀a)(∀b)(∀c)( ((a,c)∈p et (b,c)∈p) ⇒ a=b ).

    Injectivité d'un GRAPHE exprimée au niveau des COUPLES (deux antécédents a,b de
    la même image c coïncident).  Forme couple-native, miroir de la fonctionnalité
    `est_fonctionnel` du dépôt."""
    vp, va, vb, vc = _t(p), var(a), var(b), var(c)
    return pourtout(a, pourtout(b, pourtout(c,
        impl(et(appartient(E.couple(va, vc), vp), appartient(E.couple(vb, vc), vp)),
             egal(va, vb)))))


def famille_dirigee(D, p="pdir", q="qdir", r="rdir"):
    """famille_dirigee(𝔇) :=
        (∀p)(∀q)( (p∈𝔇 et q∈𝔇) ⇒ (∃r)( r∈𝔇 et p⊂r et q⊂r ) ).

    « 𝔇 est DIRIGÉE » : toute paire de membres p,q est contenue dans un troisième
    membre r de 𝔇.  C'est exactement la propriété d'une CHAÎNE emboîtée (le plus
    petit des deux est inclus dans le plus grand, qui sert de r) — l'hypothèse
    minimale qui fait passer l'injectivité à la réunion."""
    vD, vp, vq, vr = _t(D), var(p), var(q), var(r)
    return pourtout(p, pourtout(q,
        impl(et(appartient(vp, vD), appartient(vq, vD)),
             existe(r, et(et(appartient(vr, vD), inclus(vp, vr)), inclus(vq, vr))))))


def membres_injectifs(D, p="pmi"):
    """membres_injectifs(𝔇) := (∀p)( p∈𝔇 ⇒ injectif_graphe(p) ).

    « Chaque membre de 𝔇 est un graphe injectif »."""
    vD, vp = _t(D), var(p)
    return pourtout(p, impl(appartient(vp, vD), injectif_graphe(vp)))


# ════════════════════════════════════════════════════════════════════════════
#  🎯 UNION-FAMILLE-INJECTIVE — la réunion d'une famille dirigée de graphes
#     injectifs est un graphe injectif.
# ════════════════════════════════════════════════════════════════════════════
def union_famille_injective(D="Dinj", pp="pwit", qq="qwit", rr="rwit"):
    """{ famille_dirigee(𝔇), membres_injectifs(𝔇) } ⊢ injectif_graphe(⋃𝔇).
                                                              [2 hyps HONNÊTES].

    🎯 Version FAMILLE de `reunion_graphes_injective`.  Pour une famille DIRIGÉE de
    graphes INJECTIFS, la réunion ⋃𝔇 est injective : deux antécédents a,b d'une même
    image c, tirés respectivement d'un membre p et d'un membre q, se retrouvent tous
    deux dans un membre commun r (direction), lequel est injectif, d'où a=b.

    Les DEUX hypothèses sont HONNÊTES (jamais postulées vraies ; conclusion ∉ hyps ;
    theorie=22), déchargées par loi_deduction."""
    vD = _t(D)
    U = union_famille(vD)
    va, vb, vc = var("ainj"), var("binj"), var("cinj")
    cac, cbc = E.couple(va, vc), E.couple(vb, vc)

    hdir = N.assume(famille_dirigee(vD))                  # famille_dirigee(𝔇)   [HONNÊTE]
    hmi = N.assume(membres_injectifs(vD))                 # membres_injectifs(𝔇) [HONNÊTE]

    # hypothèse principale de injectif_graphe(⋃𝔇) : (a,c)∈⋃𝔇 et (b,c)∈⋃𝔇
    hyp = N.assume(et(appartient(cac, U), appartient(cbc, U)))
    in_ac = conjonction_elim_gauche(hyp)
    in_bc = conjonction_elim_droite(hyp)
    cible = egal(va, vb)

    # déplie via l'axiome ⋃𝔇 : (∃p)(p∈𝔇 et (a,c)∈p), (∃q)(q∈𝔇 et (b,c)∈q)
    ex_p0 = N.modus_ponens(in_ac, equivalence_avant(_inst_union_famille(vD, cac)))
    ex_q0 = N.modus_ponens(in_bc, equivalence_avant(_inst_union_famille(vD, cbc)))
    # α-renomme le binder canonique 'punion' vers des témoins frais pwit / qwit
    ex_p = N.modus_ponens(ex_p0, equivalence_avant(alpha_existe(
        "punion", pp, et(appartient(var("punion"), vD), appartient(cac, var("punion"))))))
    ex_q = N.modus_ponens(ex_q0, equivalence_avant(alpha_existe(
        "punion", qq, et(appartient(var("punion"), vD), appartient(cbc, var("punion"))))))

    vpp, vqq, vrr = var(pp), var(qq), var(rr)

    # ── corps des témoins p, q ───────────────────────────────────────────────
    Hp = N.assume(et(appartient(vpp, vD), appartient(cac, vpp)))   # pwit∈𝔇 et (a,c)∈pwit
    Hq = N.assume(et(appartient(vqq, vD), appartient(cbc, vqq)))   # qwit∈𝔇 et (b,c)∈qwit
    pD = conjonction_elim_gauche(Hp)                     # pwit∈𝔇
    ac_p = conjonction_elim_droite(Hp)                   # (a,c)∈pwit
    qD = conjonction_elim_gauche(Hq)                     # qwit∈𝔇
    bc_q = conjonction_elim_droite(Hq)                   # (b,c)∈qwit

    # direction instanciée en (pwit,qwit) : (∃r)(r∈𝔇 et pwit⊂r et qwit⊂r)
    dir_inst = instancie(instancie(hdir, vpp), vqq)
    ex_r = N.modus_ponens(conjonction_intro(pD, qD), dir_inst)
    # α-renomme le binder 'rdir' vers rwit frais
    corps_r_dir = et(et(appartient(var("rdir"), vD), inclus(vpp, var("rdir"))),
                     inclus(vqq, var("rdir")))
    ex_r = N.modus_ponens(ex_r, equivalence_avant(alpha_existe("rdir", rr, corps_r_dir)))

    # ── corps du témoin r ────────────────────────────────────────────────────
    corps_r = et(et(appartient(vrr, vD), inclus(vpp, vrr)), inclus(vqq, vrr))
    Hr = N.assume(corps_r)                               # rwit∈𝔇 et pwit⊂rwit et qwit⊂rwit
    rD = conjonction_elim_gauche(conjonction_elim_gauche(Hr))   # rwit∈𝔇
    p_sub_r = conjonction_elim_droite(conjonction_elim_gauche(Hr))  # pwit⊂rwit
    q_sub_r = conjonction_elim_droite(Hr)                # qwit⊂rwit

    # (a,c)∈rwit  via pwit⊂rwit instancié au couple (a,c)
    ac_r = N.modus_ponens(ac_p, instancie(p_sub_r, cac))    # (a,c)∈rwit
    bc_r = N.modus_ponens(bc_q, instancie(q_sub_r, cbc))    # (b,c)∈rwit

    # rwit∈𝔇 ⇒ injectif_graphe(rwit) ; instancie en (a,b,c) ⇒ a=b
    inj_r = N.modus_ponens(rD, instancie(hmi, vrr))        # injectif_graphe(rwit)
    inj_abc = instancie(instancie(instancie(inj_r, va), vb), vc)
    a_eq_b = N.modus_ponens(conjonction_intro(ac_r, bc_r), inj_abc)  # a=b   [Hr, Hp, Hq, hdir, hmi, hyp]

    # ── élimine les témoins r, q, p ──────────────────────────────────────────
    wit_r = N.loi_deduction(corps_r, a_eq_b)              # corps_r ⇒ a=b
    after_r = N.modus_ponens(ex_r, existe_elimination(wit_r, rr))   # a=b   [Hp, Hq, hdir, hmi, hyp]

    wit_q = N.loi_deduction(et(appartient(vqq, vD), appartient(cbc, vqq)), after_r)
    after_q = N.modus_ponens(ex_q, existe_elimination(wit_q, qq))   # a=b   [Hp, hdir, hmi, hyp]

    wit_p = N.loi_deduction(et(appartient(vpp, vD), appartient(cac, vpp)), after_q)
    after_p = N.modus_ponens(ex_p, existe_elimination(wit_p, pp))   # a=b   [hdir, hmi, hyp]

    impl_abc = N.loi_deduction(et(appartient(cac, U), appartient(cbc, U)), after_p)
    res = N.generalisation("ainj", N.generalisation("binj", N.generalisation("cinj", impl_abc)))

    cible_th = injectif_graphe(U)
    assert res.conclusion == cible_th, "union_famille_injective : ≠ injectif_graphe(⋃𝔇)"
    assert famille_dirigee(vD) in res.hypotheses, "union_famille_injective : direction absente"
    assert membres_injectifs(vD) in res.hypotheses, "union_famille_injective : injectivité membres absente"
    assert res.conclusion not in res.hypotheses, "union_famille_injective : VACUOUS"
    return res


__all__ = [
    "injectif_graphe", "famille_dirigee", "membres_injectifs",
    "union_famille_injective",
]
