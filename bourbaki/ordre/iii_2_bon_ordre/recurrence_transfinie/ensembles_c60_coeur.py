"""§III.2 — DÉFINITION PAR RÉCURRENCE TRANSFINIE (Critère C60), EXISTENCE : LE CŒUR.

Suite DIRECTE de `ensembles_c60_existence_close` (E1–E6) et de
`ensembles_recursion_transfinie_existence` (cohérence `solutions_coincident`,
réunion BINAIRE d'essais).  Ce module CLOSE le CŒUR reporté de la moitié
EXISTENCE de C60 : le RECOLLEMENT D'UNE FAMILLE (non binaire) d'essais en un seul
graphe fonctionnel, et son extension d'un pas.

────────────────────────────────────────────────────────────────────────────────
RAPPEL DE LA FRONTIÈRE (cf. ensembles_c60_existence_close, en bas).

Le pas d'hérédité COMPLET de (E6) — « si tout y<x est couvert, glue leurs essais en
un essai p_x sur seg(R,E,x) puis prolonge d'un pas » — demandait :
  (i)   FAMILY-GLUING : réunir la famille COHÉRENTE {p_y : y<x} en UN graphe
        fonctionnel sur seg(R,E,x).  Les essais coïncident sur les recouvrements
        (⇐ C60-unicité `solutions_coincident`) : c'est la COMPATIBILITÉ PAR PAIRES
        de la famille ⇒ la réunion ⋃𝔇 est fonctionnelle.
  (ii)  COLLECTIVISATION : pouvoir prendre la réunion ⋃𝔇 d'une FAMILLE 𝔇 d'essais
        (quantifier sur les membres) — un terme collectivisant ⋃𝔇 et son axiome de
        membership (S8 sur 𝔓(E×V), motif Zermelo `Union`).
  (iii) VALEUR AU NOUVEAU POINT : prolonger p_x du couple (x, h(x,p_x)) [E5 en donne
        la fonctionnalité], et vérifier l'équation de récursion en x.

────────────────────────────────────────────────────────────────────────────────
CE QUI EST CLOS ICI (theorie_ensembles()=22 intangible ; tout DÉRIVÉ, rien postulé).

  (ii) COLLECTIVISATION — `union_famille` / `axiome_union_famille` / `membre_union_famille` :
        ⋃𝔇 := { w | (∃p)( p∈𝔇 et w∈p ) }  (terme opaque + axiome DÉFINITIONNEL S8+A1
        dans une THÉORIE DÉDIÉE `theorie_union_famille`, motif Zermelo `Union`).
        N'altère PAS theorie_ensembles().  C'est CE QUI permet de quantifier sur les
        membres d'une famille d'essais et d'en prendre la réunion.

  (i)  🎯 FAMILY-UNION-FUNCTIONAL — `union_famille_fonctionnelle` :
        { famille_compatible(𝔇) } ⊢ est_fonctionnel( ⋃𝔇 )                [1 hyp honnête].
        LE CŒUR RÉUTILISABLE.  Si la famille 𝔇 est COMPATIBLE PAR PAIRES (deux
        membres quelconques s'accordent sur tout antécédent commun — exactement la
        cohérence livrée par `solutions_coincident`), alors la réunion ⋃𝔇 est un
        graphe FONCTIONNEL.  Généralise la réunion BINAIRE `reunion_essais_fonctionnelle`
        à une famille NON binaire.  Cœur : pour (u,v),(u,z)∈⋃𝔇, témoins p,q∈𝔇 avec
        (u,v)∈p, (u,z)∈q ; la compatibilité en (p,q,u,v,z) donne v=z.
        [mirroir de la technique Zermelo `_commun_membre` (deux couples de ⋃𝔇 dans des
         membres), SIMPLIFIÉE : la compatibilité est DONNÉE, sans chercher de membre
         commun.]

  (iii) VALEUR AU NOUVEAU POINT — `extension_un_pas_union_fonctionnelle` :
        { famille_compatible(𝔇), dom(⋃𝔇)=seg(R,E,x) }
        ⊢ est_fonctionnel( ⋃𝔇 ∪ {(x,v)} )                                [2 hyps honnêtes].
        🎯 RECOLLEMENT-FAMILLE + EXTENSION D'UN PAS, moitié FONCTIONNALITÉ : on glue
        la famille (i) PUIS on prolonge d'un pas par (E5) — la composition des deux
        cœurs.  L'essai p_x := ⋃𝔇 est fonctionnel (i) ; (E5) le prolonge en x.

────────────────────────────────────────────────────────────────────────────────
LA FRONTIÈRE RÉSIDUELLE (reportée, honnêtement — voir le rapport en bas).

  Ce qui RESTE pour clore C60-existence INCONDITIONNELLEMENT :
    • l'INSTANCIATION de 𝔇 à la famille CONCRÈTE {p_y : y<x} des essais sur les
      segments (qui demande de collectiviser « l'ensemble des essais » et de prouver
      que dom(⋃{p_y}) = seg(R,E,x), i.e. les domaines des p_y RECOUVRENT exactement
      le segment) ;
    • l'ÉQUATION DE RÉCURSION au point x : valeur(p_x∪{(x,v)}, x) = vh(x) avec
      v:=vh(x), et le transfert de l'équation sur le segment (via `valeur_essai_reunion`
      généralisée à la famille) ;
    • la DÉCHARGE de l'hérédité honnête de (E6) par l'assemblage de (i)+(iii) ;
    • le PONT (i') `famille_compatible(𝔇)` ⟸ `solutions_coincident` : NON construit ici.
      `solutions_coincident` prouve la coïncidence au niveau VALEUR (vf,vg : Terme→Terme,
      (∀x∈E) vf(x)=vg(x)) ; `famille_compatible` est au niveau GRAPHE (membres p,q∈𝔇,
      couples (a,b)∈p, (a,c)∈q ⇒ b=c).  Relier les deux exige, pour des graphes p,q
      FONCTIONNELS, le passage (a,b)∈p ⇒ b=valeur(p,a) (valeur_caracterisation/C46) —
      un chunk distinct non clos ici.  C'est pourquoi `famille_compatible` reste une
      HYPOTHÈSE HONNÊTE (la coïncidence-graphe des essais) plutôt qu'un théorème dérivé.

INVARIANT : theorie_ensembles()=22.  Les hypothèses (compatibilité de la famille,
domaine = segment) sont HONNÊTES — la compatibilité EST la cohérence (niveau graphe)
des essais (cf. `solutions_coincident` au niveau valeur), le domaine=segment EST la
couverture des y<x.  Déchargées par loi_deduction.  Aucun axiome nouveau dans
theorie_ensembles : la collectivisation ⋃𝔇 vit dans une THÉORIE DÉDIÉE (motif
Zermelo `Union`).
"""
from __future__ import annotations

from bourbaki.logique.formule import (
    Terme, var, egal, et, non, impl, equiv, appartient, existe, pourtout,
)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E

from bourbaki.logique.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, instancie,
)
from bourbaki.logique.tactiques.tactiques_abrege_quantif import (
    existe_elimination, alpha_existe,
)

from bourbaki.ordre.iii_2_bon_ordre.recurrence_transfinie.ensembles_recurrence_transfinie import _graphe_R
from bourbaki.ordre.iii_2_bon_ordre.recurrence_transfinie.ensembles_c60_existence_close import (
    extension_un_pas_fonctionnelle,
)


def _t(t):
    """Coercion str/Terme → Terme."""
    return t if isinstance(t, Terme) else var(t)


# ════════════════════════════════════════════════════════════════════════════
#  (ii) COLLECTIVISATION — la RÉUNION ⋃𝔇 d'une FAMILLE 𝔇 de graphes-essais.
#  Terme opaque + axiome DÉFINITIONNEL (S8+A1, motif Zermelo `Union`).
#  theorie_ensembles() reste = 22.
# ════════════════════════════════════════════════════════════════════════════
def union_famille(D):
    """⋃𝔇 := { w | (∃p)( p∈𝔇 et w∈p ) }  (réunion d'une famille 𝔇 de graphes-essais).

    Terme collectivisant (S8 sur 𝔓(E×V), unicité A1).  C'est le graphe candidat
    f = ⋃ des essais : un couple appartient à ⋃𝔇 ssi il appartient à L'UN des
    essais de la famille.  Motif EXACT de Zermelo `Union` (réunion d'une chaîne)."""
    return E.app("c60_union_famille", _t(D))


def _corps_union_famille(D, w, p="punion"):
    """Corps de ⋃𝔇 :  (∃p)( p∈𝔇 et w∈p )."""
    vp = var(p)
    return existe(p, et(appartient(vp, _t(D)), appartient(_t(w), vp)))


def axiome_union_famille(D="Df", w="wf", p="punion"):
    """⊢-schéma (∀𝔇 w)( w∈⋃𝔇 ⇔ (∃p)( p∈𝔇 et w∈p ) ).

    Axiome DÉFINITIONNEL de la réunion d'une famille (légitime S8+A1, motif Zermelo
    `Union` / `reunion_famille`).  N'altère PAS theorie_ensembles() (=22)."""
    vD, vw = var(D), var(w)
    return pourtout(D, pourtout(w,
        equiv(appartient(vw, union_famille(vD)), _corps_union_famille(vD, vw, p))))


def theorie_union_famille(D="Df", w="wf", p="punion"):
    """Théorie DÉDIÉE ne contenant que l'axiome de ⋃𝔇 (C60-existence, le cœur)."""
    return N.Theorie("UnionFamille-C60", [axiome_union_famille(D, w, p)])


def _inst_union_famille(D, w):
    """⊢ ( w∈⋃𝔇 ⇔ (∃p)( p∈𝔇 et w∈p ) )   (axiome instancié aux TERMES)."""
    ax = N.axiome(theorie_union_famille(), axiome_union_famille())
    for tm in (D, w):
        ax = instancie(ax, _t(tm))
    return ax


def membre_union_famille(D="Df", w="wf"):
    """⊢ ( w∈⋃𝔇 ) ⇔ ( (∃p)( p∈𝔇 et w∈p ) )."""
    return _inst_union_famille(var(D), var(w))


# ════════════════════════════════════════════════════════════════════════════
#  COMPATIBILITÉ PAR PAIRES d'une famille (la cohérence des essais).
# ════════════════════════════════════════════════════════════════════════════
def famille_compatible(D, p="pcf", q="qcf", a="acf", b="bcf", c="ccf"):
    """famille_compatible(𝔇) :=
        (∀p)(∀q)(∀a)(∀b)(∀c)( ( (p∈𝔇 et q∈𝔇) et ((a,b)∈p et (a,c)∈q) ) ⇒ b=c ).

    « 𝔇 est COMPATIBLE PAR PAIRES » : deux membres quelconques p,q de la famille
    s'accordent sur tout antécédent commun a (même valeur b=c).  C'est EXACTEMENT la
    cohérence des essais livrée par C60-unicité `solutions_coincident` : deux essais
    coïncident sur leur recouvrement.  Note : en prenant p=q on récupère la
    fonctionnalité de CHAQUE membre (cas particulier) — donc cette seule hypothèse
    suffit à la fonctionnalité de la réunion."""
    vD = _t(D)
    vp, vq, va, vb, vc = var(p), var(q), var(a), var(b), var(c)
    return pourtout(p, pourtout(q, pourtout(a, pourtout(b, pourtout(c,
        impl(et(et(appartient(vp, vD), appartient(vq, vD)),
                et(appartient(E.couple(va, vb), vp), appartient(E.couple(va, vc), vq))),
             egal(vb, vc)))))))


# ════════════════════════════════════════════════════════════════════════════
#  (i) 🎯 FAMILY-UNION-FUNCTIONAL — la réunion d'une famille compatible est fonctionnelle.
# ════════════════════════════════════════════════════════════════════════════
def union_famille_fonctionnelle(D="Df", p="pcf", q="qcf",
                                pp="pwit", qq="qwit"):
    """{ famille_compatible(𝔇) } ⊢ est_fonctionnel( ⋃𝔇 )               [1 hyp honnête].

    🎯 LE CŒUR RÉUTILISABLE de la moitié EXISTENCE de C60.  Si la famille 𝔇 est
    COMPATIBLE PAR PAIRES (`famille_compatible`), alors la réunion ⋃𝔇 (terme
    collectivisé (ii)) est un graphe FONCTIONNEL.  Généralise la réunion BINAIRE
    `reunion_essais_fonctionnelle` à une famille NON binaire.

    PREUVE (mirroir simplifié de Zermelo `_commun_membre`) :
      Soit (u,v),(u,z)∈⋃𝔇.  Par l'axiome de ⋃𝔇 :
        (∃p)( p∈𝔇 et (u,v)∈p )   et   (∃q)( q∈𝔇 et (u,z)∈q ).
      On élimine les témoins p (avec (u,v)∈p) puis q (avec (u,z)∈q) ; la
      compatibilité instanciée en (p,q,u,v,z) donne directement v=z.  ∎

    ⚠️ UNE hypothèse HONNÊTE (jamais postulée ; theorie=22), déchargée par
    loi_deduction : famille_compatible(𝔇) — la cohérence des essais
    (`solutions_coincident`).  Conclusion ∉ hypothèses (non vacuous)."""
    vD = _t(D)
    U = union_famille(vD)
    # binders de est_fonctionnel : u, v, z
    vu, vv, vz = var("u"), var("v"), var("z")
    cuv, cuz = E.couple(vu, vv), E.couple(vu, vz)

    hcompat = N.assume(famille_compatible(vD, p, q))     # famille_compatible(𝔇)  [HONNÊTE]

    # hypothèse principale de fonctionnalité : (u,v)∈⋃𝔇 et (u,z)∈⋃𝔇
    hyp = N.assume(et(appartient(cuv, U), appartient(cuz, U)))
    in_uv = conjonction_elim_gauche(hyp)                 # (u,v)∈⋃𝔇
    in_uz = conjonction_elim_droite(hyp)                 # (u,z)∈⋃𝔇

    # déplie via l'axiome : (∃p)(p∈𝔇 et (u,v)∈p), (∃q)(q∈𝔇 et (u,z)∈q)
    ex_p0 = N.modus_ponens(in_uv, equivalence_avant(_inst_union_famille(vD, cuv)))
    ex_q0 = N.modus_ponens(in_uz, equivalence_avant(_inst_union_famille(vD, cuz)))
    # α-renomme le binder du ∃ (canonique 'punion') vers des témoins frais pwit / qwit
    ex_p = N.modus_ponens(ex_p0, equivalence_avant(alpha_existe(
        "punion", pp, et(appartient(var("punion"), vD), appartient(cuv, var("punion"))))))
    ex_q = N.modus_ponens(ex_q0, equivalence_avant(alpha_existe(
        "punion", qq, et(appartient(var("punion"), vD), appartient(cuz, var("punion"))))))

    vpp, vqq = var(pp), var(qq)
    # corps des témoins
    Hp = N.assume(et(appartient(vpp, vD), appartient(cuv, vpp)))   # pwit∈𝔇 et (u,v)∈pwit
    Hq = N.assume(et(appartient(vqq, vD), appartient(cuz, vqq)))   # qwit∈𝔇 et (u,z)∈qwit
    pD = conjonction_elim_gauche(Hp)                     # pwit∈𝔇
    uv_p = conjonction_elim_droite(Hp)                   # (u,v)∈pwit
    qD = conjonction_elim_gauche(Hq)                     # qwit∈𝔇
    uz_q = conjonction_elim_droite(Hq)                   # (u,z)∈qwit

    # compatibilité instanciée en (pwit,qwit,u,v,z)
    compat = hcompat
    for tm in (vpp, vqq, vu, vv, vz):
        compat = instancie(compat, tm)
    # compat : ((pwit∈𝔇 et qwit∈𝔇) et ((u,v)∈pwit et (u,z)∈qwit)) ⇒ v=z
    premisse = conjonction_intro(conjonction_intro(pD, qD),
                                 conjonction_intro(uv_p, uz_q))
    v_eq_z = N.modus_ponens(premisse, compat)            # v=z   [Hp, Hq, hcompat, hyp]

    # élimine le témoin qwit puis pwit (z, et v,u non libres dans v=z ? v,z SONT
    # libres → ce qui compte : qq/pp non libres dans la cible v=z et hors Γ\{Hp,Hq})
    wit_q = N.loi_deduction(et(appartient(vqq, vD), appartient(cuz, vqq)), v_eq_z)
    ex_imp_q = existe_elimination(wit_q, qq)             # (∃qwit)(…) ⇒ v=z   [Hp, hcompat, hyp]
    after_q = N.modus_ponens(ex_q, ex_imp_q)             # v=z   [Hp, hcompat, hyp]
    wit_p = N.loi_deduction(et(appartient(vpp, vD), appartient(cuv, vpp)), after_q)
    ex_imp_p = existe_elimination(wit_p, pp)             # (∃pwit)(…) ⇒ v=z   [hcompat, hyp]
    v_eq_z_final = N.modus_ponens(ex_p, ex_imp_p)        # v=z   [hcompat, hyp]

    impl_uvz = N.loi_deduction(et(appartient(cuv, U), appartient(cuz, U)), v_eq_z_final)
    res = N.generalisation("u", N.generalisation("v", N.generalisation("z", impl_uvz)))

    cible = E.est_fonctionnel(U)
    assert res.conclusion == cible, "union_famille_fonctionnelle : ≠ est_fonctionnel(⋃𝔇)"
    compat_form = famille_compatible(vD, p, q)
    assert compat_form in res.hypotheses, "union_famille_fonctionnelle : compatibilité absente"
    assert res.conclusion not in res.hypotheses, "union_famille_fonctionnelle : VACUOUS"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  TRANSFERT DE VALEUR DANS LA RÉUNION D'UNE FAMILLE  (la version FAMILLE de
#  `valeur_essai_reunion` ; brique de l'équation de récursion au point x).
# ════════════════════════════════════════════════════════════════════════════
def _membre_dans_union(D, p, c, hpD, hcp):
    """De ⊢ p∈𝔇 [hpD] et ⊢ c∈p [hcp] déduit ⊢ c∈⋃𝔇  (introduction réunion-famille).

    Motif Zermelo `_couple_dans_union_intro` : un témoin p∈𝔇 contenant c suffit."""
    vD, vp, vc = _t(D), _t(p), _t(c)
    corps_temoin = conjonction_intro(hpD, hcp)                  # p∈𝔇 et c∈p
    R = et(appartient(var("punion"), vD), appartient(vc, var("punion")))
    ex = N.modus_ponens(corps_temoin, N.s5(R, vp, "punion"))   # (∃p)(p∈𝔇 et c∈p)
    return N.modus_ponens(ex, equivalence_arriere(_inst_union_famille(vD, vc)))  # c∈⋃𝔇


def valeur_union_famille(D="Df", p="pcf", u="u", q="qcf"):
    """{ famille_compatible(𝔇), p∈𝔇, u∈dom(p) }
        ⊢ valeur( ⋃𝔇, u ) = valeur( p, u )                              [3 hyps honnêtes].

    🎯 TRANSFERT DE VALEUR (version FAMILLE de `valeur_essai_reunion`).  La réunion
    ⋃𝔇 d'une famille compatible COÏNCIDE, sur le domaine de chaque membre p, avec p :
    en u∈dom p, ⋃𝔇 rend la même valeur que l'essai p.  DONC l'équation de récursion
    d'un essai PASSE À LA RÉUNION (brique de l'équation au point x du pas (iii)).

    PREUVE : (i) ⋃𝔇 fonctionnel ; (u, valeur(p,u))∈p (valeur_dans_graphe sous u∈dom p) ;
    p∈𝔇 ⇒ (u,valeur(p,u))∈⋃𝔇 (_membre_dans_union) ; valeur_caracterisation(⋃𝔇,u)
    instanciée donne valeur(⋃𝔇,u)=valeur(p,u).

    ⚠️ TROIS hypothèses HONNÊTES (theorie=22), déchargées par loi_deduction :
      famille_compatible(𝔇) (cohérence), p∈𝔇 (p est un essai de la famille), u∈dom p
      (u est dans le domaine de cet essai).  Conclusion ∉ hypothèses (non vacuous)."""
    from bourbaki.ensembles.fonctions.ii_3_4_fonctions_valeur.ensembles_fonctions import (
        valeur_dans_graphe, valeur_caracterisation,
    )
    from bourbaki.logique.tactiques.tactiques_abrege_egalite import symetrie
    vD, vp, vu = _t(D), _t(p), _t(u)
    U = union_famille(vD)
    pu = E.valeur(vp, vu)                                   # valeur(p,u)

    # (i) ⋃𝔇 fonctionnel  (sous famille_compatible(𝔇))
    func_U = union_famille_fonctionnelle(D, p, q)          # [famille_compatible(𝔇)]
    func_U_form = E.est_fonctionnel(U)

    # u∈dom p ⇒ (∃y)((u,y)∈p) ⇒ (u, valeur(p,u))∈p
    h_udomp = N.assume(appartient(vu, E.dom(vp)))          # u∈dom p   [HONNÊTE]
    ax_dom = N.axiome(E.theorie_ensembles(), E.AXIOME_DOM)
    car_dom = instancie(instancie(ax_dom, vp), vu)         # u∈dom p ⇔ (∃y)((u,y)∈p)
    ex_p = N.modus_ponens(h_udomp, equivalence_avant(car_dom))   # (∃y)((u,y)∈p)
    u_pu_p = N.modus_ponens(ex_p, N.loi_deduction(
        existe("y", appartient(E.couple(vu, var("y")), vp)),
        valeur_dans_graphe(vp, vu)))                       # (u, valeur(p,u))∈p

    # p∈𝔇 ⇒ (u,valeur(p,u))∈⋃𝔇
    h_pD = N.assume(appartient(vp, vD))                    # p∈𝔇   [HONNÊTE]
    u_pu_U = _membre_dans_union(vD, vp, E.couple(vu, pu), h_pD, u_pu_p)   # (u,valeur(p,u))∈⋃𝔇

    # valeur_caracterisation(⋃𝔇, u) instancié à y:=valeur(p,u)
    vc = valeur_caracterisation(U, vu)                     # hyps : func(⋃𝔇), (∃y)((u,y)∈⋃𝔇)
    vc_pu = instancie(N.generalisation("y", vc), pu)       # ((u,valeur(p,u))∈⋃𝔇) ⇔ (valeur(p,u)=valeur(⋃𝔇,u))
    pu_eq = N.modus_ponens(u_pu_U, equivalence_avant(vc_pu))   # valeur(p,u)=valeur(⋃𝔇,u)
    res = N.modus_ponens(pu_eq, symetrie(pu, E.valeur(U, vu)))  # valeur(⋃𝔇,u)=valeur(p,u)

    # décharge les hypothèses de valeur_caracterisation : func(⋃𝔇) [par (i)] et
    # (∃y)((u,y)∈⋃𝔇) [par S5 sur u_pu_U].
    ex_U = N.modus_ponens(u_pu_U, N.s5(appartient(E.couple(vu, var("y")), U), pu, "y"))
    res = N.modus_ponens(func_U, N.loi_deduction(func_U_form, res))   # décharge func(⋃𝔇) par (i)
    res = N.modus_ponens(ex_U, N.loi_deduction(
        existe("y", appartient(E.couple(vu, var("y")), U)), res))     # décharge (∃y)((u,y)∈⋃𝔇)

    cible = egal(E.valeur(U, vu), pu)
    assert res.conclusion == cible, "valeur_union_famille : ≠ valeur(⋃𝔇,u)=valeur(p,u)"
    compat_form = famille_compatible(vD, p, q)
    assert compat_form in res.hypotheses, "valeur_union_famille : compatibilité absente"
    assert appartient(vp, vD) in res.hypotheses, "valeur_union_famille : p∈𝔇 absente"
    assert appartient(vu, E.dom(vp)) in res.hypotheses, "valeur_union_famille : u∈dom p absente"
    assert res.conclusion not in res.hypotheses, "valeur_union_famille : VACUOUS"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  (iii) 🎯 RECOLLEMENT-FAMILLE + EXTENSION D'UN PAS, moitié FONCTIONNALITÉ.
#  est_fonctionnel( ⋃𝔇 ∪ {(x,v)} )  sous  { famille_compatible(𝔇), dom(⋃𝔇)=seg(R,E,x) }.
# ════════════════════════════════════════════════════════════════════════════
def extension_un_pas_union_fonctionnelle(D="Df", G="G", e="E", x="x0", v="v0",
                                         p="pcf", q="qcf"):
    """{ famille_compatible(𝔇), dom(⋃𝔇) = seg(R,E,x) }
        ⊢ est_fonctionnel( ⋃𝔇 ∪ {(x,v)} )                             [2 hyps honnêtes].

    🎯 LA COMPOSITION DES DEUX CŒURS : on GLUE la famille compatible 𝔇 en l'essai
    p_x := ⋃𝔇 (i) — FONCTIONNEL — PUIS on le prolonge d'un pas par le couple (x,v)
    via (E5) `extension_un_pas_fonctionnelle`.  Le pas d'hérédité (E6), moitié
    FONCTIONNALITÉ, en sort : l'essai sur seg(R,E,x)∪{x} construit comme la réunion
    des essais des y<x, prolongée en x, est fonctionnel.

    DÉRIVÉ : (E5) demande { est_fonctionnel(p), dom(p)=seg } ; on décharge la
    première par (i) `union_famille_fonctionnelle` (sous famille_compatible(𝔇)) — il
    ne reste que famille_compatible(𝔇) et dom(⋃𝔇)=seg(R,E,x), les deux données
    HONNÊTES (cohérence des essais + couverture des y<x).

    ⚠️ DEUX hypothèses HONNÊTES (theorie=22), déchargées par loi_deduction :
      • famille_compatible(𝔇)        — cohérence des essais (`solutions_coincident`) ;
      • dom(⋃𝔇) = seg(R,E,x)         — les domaines des essais des y<x recouvrent le
        segment (la COUVERTURE des y<x, donnée du pas d'hérédité).
    Conclusion ∉ hypothèses (non vacuous)."""
    vD = _t(D)
    U = union_famille(vD)

    # (E5) sur l'essai p := ⋃𝔇 :  { func(⋃𝔇), dom(⋃𝔇)=seg } ⊢ func(⋃𝔇 ∪ {(x,v)})
    e5 = extension_un_pas_fonctionnelle(U, G, e, x, v)
    func_U_form = E.est_fonctionnel(U)
    # (i) func(⋃𝔇)  sous  famille_compatible(𝔇)
    func_U = union_famille_fonctionnelle(D, p, q)
    assert func_U.conclusion == func_U_form, "extension_un_pas_union : (i) ≠ func(⋃𝔇)"

    # décharge func(⋃𝔇) de (E5) par (i)
    res = N.modus_ponens(func_U, N.loi_deduction(func_U_form, e5))

    seg = E.segment_extremite(_graphe_R(G), _t(e), _t(x))
    cible = E.est_fonctionnel(E.reunion(U, E.singleton(E.couple(_t(x), _t(v)))))
    assert res.conclusion == cible, "extension_un_pas_union : ≠ func(⋃𝔇 ∪ {(x,v)})"
    compat_form = famille_compatible(vD, p, q)
    assert compat_form in res.hypotheses, "extension_un_pas_union : compatibilité absente"
    assert egal(E.dom(U), seg) in res.hypotheses, "extension_un_pas_union : dom(⋃𝔇)=seg absente"
    assert res.conclusion not in res.hypotheses, "extension_un_pas_union : VACUOUS"
    return res


__all__ = [
    # (ii) collectivisation : la réunion ⋃𝔇 d'une famille (théorie DÉDIÉE)
    "union_famille", "axiome_union_famille", "theorie_union_famille",
    "membre_union_famille",
    # compatibilité par paires (la cohérence des essais)
    "famille_compatible",
    # (i) 🎯 family-union-functional (le cœur réutilisable, 1 hyp honnête)
    "union_famille_fonctionnelle",
    # transfert de valeur dans la réunion-famille (3 hyps honnêtes)
    "valeur_union_famille",
    # (iii) 🎯 recollement-famille + extension d'un pas (2 hyps honnêtes)
    "extension_un_pas_union_fonctionnelle",
]
