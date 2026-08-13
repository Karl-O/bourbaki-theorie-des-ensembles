"""§III.7.2 — l'application canonique g de restriction à J, CONSTRUITE.

────────────────────────────────────────────────────────────────────────────────
LE PROBLÈME.  `ensembles_limites_canoniques.application_canonique_g` est un terme
OPAQUE (`app("g_restr_J", …)`) dont la seule caractérisation est un AXIOME
définitionnel, la formule (3) de Bourbaki :

    axiome_canonique_g :  (∀α)(∀x)( (x ∈ lim←_I  et  α ∈ J) ⇒ pr_α(g(x)) = f_α(x) )

posé dans une théorie dédiée (`theorie_canonique_g`).  C'était suffisant pour
démontrer la Prop. 3 en coordonnées — injectivité et surjectivité le sont, sans
axiome du choix — mais PAS pour parler de g comme d'une FONCTION : rien ne donne
`est_fonctionnel(g)` ni `dom(g) = lim←_I`, donc rien ne permet d'atteindre le
vocabulaire `est_bijection_de(g, lim←_I, lim←_J)` du dépôt.  C'était l'unique
écart restant à la Prop. 3.

LA SORTIE : construire au lieu de postuler.  g est la fonction x ↦ (f_α(x))_{α∈J},
et le dépôt sait fabriquer une telle fonction — `graphe_terme(A, T)` = le graphe
de x ↦ T, avec ses trois théorèmes CLOS (fonctionnel, graphe, domaine).  Il suffit
d'emboîter deux `graphe_terme` :

    famille(x) := graphe_terme( J,        f_α(x) )    liant α — la famille (f_α(x))_{α∈J}
    G          := graphe_terme( lim←_I,   famille(x) ) liant x — la fonction g

et TOUT tombe :
  • `g_est_fonctionnelle`, `g_est_un_graphe`, `g_domaine` — CLOS, 0 hypothèse ;
  • `g_formule_3` — la formule (3) elle-même, DÉMONTRÉE sous ses deux prémisses
    exactes (x ∈ lim←_I, α ∈ J), donc l'AXIOME devient dispensable.

Ce que cela change.  On ne retire pas l'axiome du dépôt dans ce module (les
consommateurs actuels l'utilisent et la migration est un chantier à part) ; mais
il est désormais ÉTABLI qu'il n'était pas nécessaire — `g_formule_3_egale_axiome`
asserte que l'énoncé dérivé pour G est mot pour mot le corps de l'axiome, à la
substitution du terme opaque par le terme construit.  Un axiome démontrable est
un axiome de confort, pas une hypothèse sur le monde.

⚠️ LIANTS IMPOSÉS, mesuré.  Le kit C54 (`membre_graphe_terme`,
`couple_egal_implique_composantes`) code en dur les noms « v » et « y » et exige
des NOMS, pas des termes, pour le point d'évaluation : passer `var("p")` au lieu
de `"p"` fait échouer le modus ponens interne.  Les liants du graphe doivent
rester des LETTRES SIMPLES.  D'où « x » (point), « a » (indice), et un point
d'évaluation nommé — le portage vers des termes quelconques se fait ensuite par
`porter_aux_termes`, dont c'est exactement l'office.
⚠️ « w » est interdit comme nom de point : c'est le liant de contexte par défaut
de `congruence_terme`.

⚠️⚠️ PIÈGE MAJEUR, mesuré le 4 août : **`graphe_terme` NE LIE PAS**.  Son
encodage est `app("graphe_terme", A, T)` — le paramètre `x` de la signature est
DOCUMENTAIRE (le commentaire du dépôt le dit : « META : l'assemblage de Bourbaki
lie x ; ici F = app(A, T) est paramétrée par A et le terme T »).  Conséquence :
le terme construit porte ses deux « liants » comme variables **LIBRES** —
`libres(graphe_g()) = {E, J, f, x, a}` avec les noms par défaut.
Donc si l'on branche `graphe_g()` dans une preuve où « a » est l'indice libre
(c'est le cas de toute la chaîne Prop. 3), la substitution de « a » ATTEINT le
terme g, et une hypothèse censée être close en λ se met à porter λ :
`coordonnees_egales_partout` échoue alors sur « prémisse non réduite (2) ».
LE REMÈDE : instancier `graphe_g` / `g_formule_3_quantifiee` avec des noms
FRAIS pour le site d'accueil — p. ex. `pt="s", idx="t"` face à la Prop. 3, qui
utilise a/b/lam/xx/xp.  C'est ce que fait `injectivite_g_construite`.
INVARIANT : theorie_ensembles()=22 ; rien postulé — tout est construit.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, et, impl, appartient, pourtout, subst_t,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
    congruence_terme, composer_egalites,
)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import (
    ensembles_abrege as E,
)
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_6_fonction_terme.ensembles_fonction_terme import (
    graphe_terme_fonctionnel, graphe_terme_est_graphe,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.cantor.ensembles_cantor import (
    graphe_terme_domaine, graphe_terme_valeur,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites import (
    ensembles_limites as L, ensembles_limites_canoniques as C,
)

#: liants imposés par le kit C54 — ne pas changer sans re-mesurer (cf. en-tête).
_PT, _IDX = "x", "a"


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def corps_formule_3(gterme, Efam="E", f="f", J="J", p="p", q="q"):
    """Le corps de la formule (3) POUR UN TERME g QUELCONQUE :
        (∀q)(∀p)( (p ∈ lim←_I et q ∈ J) ⇒ pr_q(g(p)) = f_q(p) ).

    Un SEUL constructeur, deux emplois : appliqué au terme opaque il doit rendre
    exactement `axiome_canonique_g` (c'est le miroir asserté par
    `formule_3_reproduit_l_axiome`), appliqué au terme construit il donne la
    cible de `g_formule_3_quantifiee`.  C'est ce partage qui rend la
    comparaison honnête : sans lui, « même énoncé » ne serait qu'une affirmation
    de docstring."""
    vp, vq = var(p), var(q)
    return pourtout(q, pourtout(p, impl(
        et(appartient(vp, L.lim_proj(_t(Efam), _t(f))), appartient(vq, _t(J))),
        egal(E.projection_indice(E.valeur(gterme, vp), vq),
             C.application_canonique_proj_valeur(_t(Efam), _t(f), vq, vp)))))


def formule_3_reproduit_l_axiome(Efam="E", f="f", J="J", i="I", p="p", q="q"):
    """Vérifie que `corps_formule_3` appliqué au terme OPAQUE rend mot pour mot
    l'axiome du dépôt.  Rend True, ou lève.

    Sans cette vérification, l'affirmation « la formule (3) démontrée pour G est
    l'énoncé de l'axiome » reposerait sur une lecture à l'œil des deux sources."""
    axiome = C.axiome_canonique_g(_t(Efam), _t(f), None, _t(i), _t(J), x=p, a=q)
    reconstruit = corps_formule_3(
        C.application_canonique_g(_t(Efam), _t(f), _t(J)), Efam, f, J, p, q)
    assert reconstruit == axiome, \
        "formule_3_reproduit_l_axiome : corps_formule_3 ≠ axiome_canonique_g"
    return True


def famille_coordonnees(Efam="E", f="f", J="J", pt=_PT, idx=_IDX):
    """Le terme (f_α(x))_{α∈J} : la famille des coordonnées d'un point x.

    `pt` est LIBRE dedans (c'est lui que `graphe_g` liera) ; `idx` est le liant
    de la famille."""
    return E.graphe_terme(_t(J), C.application_canonique_proj_valeur(
        _t(Efam), _t(f), var(idx), var(pt)), idx)


# @livre Ch.III §7.2 Def.- | E III.52 L.27-32 | PDF p.155  (l'application canonique g de la restriction à J, ici CONSTRUITE et non postulée)
def graphe_g(Efam="E", f="f", J="J", pt=_PT, idx=_IDX):
    """Le graphe de g : x ↦ (f_α(x))_{α∈J}, pour x ∈ lim←_I.

    Deux `graphe_terme` emboîtés — c'est toute la construction."""
    return E.graphe_terme(L.lim_proj(_t(Efam), _t(f)),
                          famille_coordonnees(Efam, f, J, pt, idx), pt)


# @livre Ch.III §7.2 Def.- | E III.52 L.27-32 | PDF p.155  (g est fonctionnelle — THÉORÈME, là où le terme opaque ne donnait rien)
def g_est_fonctionnelle(Efam="E", f="f", J="J", pt=_PT, idx=_IDX):
    """⊢ est_fonctionnel(G).                                        [CLOS, 0 hyp].

    Immédiat par `graphe_terme_fonctionnel` (Critère C54) : rien de propre aux
    limites projectives n'intervient — c'est la construction qui donne le fait,
    et c'est précisément ce que le terme opaque ne pouvait pas donner."""
    res = graphe_terme_fonctionnel(
        L.lim_proj(_t(Efam), _t(f)), famille_coordonnees(Efam, f, J, pt, idx),
        pt, "y")
    assert res.conclusion == E.est_fonctionnel(graphe_g(Efam, f, J, pt, idx)), \
        "g_est_fonctionnelle : conclusion ≠ est_fonctionnel(G)"
    assert res.est_clos, "g_est_fonctionnelle : non clos"
    return res


# @livre Ch.III §7.2 Def.- | E III.52 L.27-32 | PDF p.155  (g est un graphe — THÉORÈME)
def g_est_un_graphe(Efam="E", f="f", J="J", pt=_PT, idx=_IDX):
    """⊢ est_un_graphe(G).                                          [CLOS, 0 hyp]."""
    res = graphe_terme_est_graphe(
        L.lim_proj(_t(Efam), _t(f)), famille_coordonnees(Efam, f, J, pt, idx),
        pt, "y")
    assert res.conclusion == E.est_un_graphe(graphe_g(Efam, f, J, pt, idx)), \
        "g_est_un_graphe : conclusion ≠ est_un_graphe(G)"
    assert res.est_clos, "g_est_un_graphe : non clos"
    return res


# @livre Ch.III §7.2 Def.- | E III.52 L.27-32 | PDF p.155  (dom(g) = lim←_I — THÉORÈME : g est bien définie sur TOUTE la limite)
def g_domaine(Efam="E", f="f", J="J", pt=_PT, idx=_IDX):
    """⊢ dom(G) = lim←_I.                                           [CLOS, 0 hyp].

    Avec `g_est_fonctionnelle`, c'est la moitié « (func ∧ dom=X) » du prédicat
    `est_bijection_de` du dépôt — la moitié qui manquait entièrement."""
    lim = L.lim_proj(_t(Efam), _t(f))
    res = graphe_terme_domaine(
        lim, famille_coordonnees(Efam, f, J, pt, idx), pt, "y", "z")
    assert res.conclusion == egal(E.dom(graphe_g(Efam, f, J, pt, idx)), lim), \
        "g_domaine : conclusion ≠ (dom G = lim←_I)"
    assert res.est_clos, "g_domaine : non clos"
    return res


# @livre Ch.III §7.2 Def.- | E III.52 L.27-32 | PDF p.155  (formule (3) : pr_α(g(x))=f_α(x) — DÉMONTRÉE, alors qu'elle était l'AXIOME définitionnel de g)
def g_formule_3(Efam="E", f="f", J="J", p="p", q="q", pt=_PT, idx=_IDX):
    """{ p ∈ lim←_I,  q ∈ J } ⊢ pr_q(G(p)) = f_q(p).                [1 hyp].

    LA FORMULE (3) DE BOURBAKI, démontrée.  Ses deux hypothèses sont exactement
    les deux prémisses de l'axiome qu'elle remplace — rien de plus.

    Trois pas, tous par `graphe_terme_valeur` (la valeur d'un graphe-terme) :
      1. G(p) = famille(p)              [valeur du graphe extérieur, sous p∈lim←_I]
      2. congruence : pr_q(G(p)) = pr_q(famille(p))
      3. pr_q(famille(p)) = f_q(p)      [valeur du graphe intérieur, sous q∈J]
    et `pr_α(z)` n'est autre que `valeur(z, α)` (E.II.5.3), ce qui fait de 2-3 une
    simple composition d'égalités.

    ⚠️ `p` et `q` doivent être des NOMS (le kit C54 échoue sur des termes) ;
    utiliser `porter_aux_termes` pour l'appliquer à des termes construits."""
    vp, vq = var(p), var(q)
    lim = L.lim_proj(_t(Efam), _t(f))
    fam = famille_coordonnees(Efam, f, J, pt, idx)
    G = graphe_g(Efam, f, J, pt, idx)

    val_g = graphe_terme_valeur(lim, fam, p, pt, "y")          # G(p)=famille(p)
    fam_p = subst_t(vp, pt, fam)
    f_idx_p = subst_t(vp, pt, C.application_canonique_proj_valeur(
        _t(Efam), _t(f), var(idx), var(pt)))
    val_fam = graphe_terme_valeur(_t(J), f_idx_p, q, idx, "y")  # famille(p)(q)=f_q(p)
    cong = N.modus_ponens(val_g, congruence_terme(
        E.valeur(G, vp), fam_p, E.valeur(var("w"), vq)))
    res = composer_egalites(cong, val_fam)
    assert res.conclusion == egal(
        E.projection_indice(E.valeur(G, vp), vq),
        C.application_canonique_proj_valeur(_t(Efam), _t(f), vq, vp)), \
        "g_formule_3 : conclusion ≠ pr_q(G(p)) = f_q(p)"
    assert res.hypotheses == frozenset({appartient(vp, lim), appartient(vq, _t(J))}), \
        "g_formule_3 : hypothèses ≠ {p∈lim←_I, q∈J}"
    return res


# @livre Ch.III §7.2 Def.- | E III.52 L.27-32 | PDF p.155  (l'axiome (3) est DÉMONTRABLE pour la g construite : forme quantifiée, mot pour mot le corps de axiome_canonique_g)
def g_formule_3_quantifiee(Efam="E", f="f", J="J", p="p", q="q",
                           pt=_PT, idx=_IDX):
    """⊢ (∀q)(∀p)( (p ∈ lim←_I et q ∈ J) ⇒ pr_q(G(p)) = f_q(p) ).   [CLOS, 0 hyp].

    La forme QUANTIFIÉE — et c'est ici que se lit le résultat : cette formule est
    **mot pour mot le corps de `axiome_canonique_g`**, avec le terme construit G
    à la place du terme opaque.  Elle est CLOSE ; l'axiome était donc superflu.

    Le miroir est asserté ci-dessous : on reconstruit l'énoncé de l'axiome par
    substitution du terme opaque et on exige l'égalité syntaxique — un test qui
    compterait les hypothèses ne prouverait rien de tel."""
    vp, vq = var(p), var(q)
    lim = L.lim_proj(_t(Efam), _t(f))
    th = g_formule_3(Efam, f, J, p, q, pt, idx)
    imp = N.loi_deduction(et(appartient(vp, lim), appartient(vq, _t(J))),
                          _conjonction_en_prémisse(th, vp, lim, vq, _t(J)))
    res = N.generalisation(q, N.generalisation(p, imp))
    assert formule_3_reproduit_l_axiome(Efam, f, J, "I", p, q)
    assert res.conclusion == corps_formule_3(
        graphe_g(Efam, f, J, pt, idx), Efam, f, J, p, q), \
        "g_formule_3_quantifiee : ≠ corps de la formule (3) pour G"
    assert res.est_clos, "g_formule_3_quantifiee : non clos"
    return res


def _conjonction_en_prémisse(th, vp, lim, vq, vJ):
    """Remplace les deux hypothèses séparées par leur CONJONCTION assumée."""
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
        conjonction_elim_gauche, conjonction_elim_droite,
    )
    h = N.assume(et(appartient(vp, lim), appartient(vq, vJ)))
    out = th
    for pr in (conjonction_elim_gauche(h), conjonction_elim_droite(h)):
        out = N.modus_ponens(pr, N.loi_deduction(pr.conclusion, out))
    return out


# @livre Ch.III §7.2 Prop.3 | E III.55 L.6-13 | PDF p.158  (l'injectivité de la Prop. 3, portée sur le g CONSTRUIT : même terme que func/dom)
def injectivite_g_construite(jj="J", i="I", lam="lam", pt="s", idx="t"):
    """⊢ (∀x)(∀x')( (x,x' ∈ lim←_I et G(x)=G(x')) ⇒ x = x' ).          [1 hyp].

    L'injectivité universelle de la Prop. 3, mais énoncée sur le terme
    CONSTRUIT — donc conjoignable avec `g_est_fonctionnelle` et `g_domaine`,
    ce que la version sur terme opaque interdisait.

    Les noms `pt`/`idx` sont FRAIS par rapport à la Prop. 3 (qui utilise a, b,
    lam, xx, xp) : voir le piège « graphe_terme ne lie pas » en tête de module.
    Avec les noms par défaut « x »/« a », la substitution de l'indice atteint le
    terme g et la généralisation sur λ échoue."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites.prop1_proj.ensembles_prop3_injectif_total import (
        prop3_g_injective_universelle,
    )
    G = graphe_g(pt=pt, idx=idx)
    res = prop3_g_injective_universelle(
        jj, i, lam, gterme=G, formule_3=g_formule_3_quantifiee(pt=pt, idx=idx))
    assert len(res.hypotheses) == 1, \
        f"injectivite_g_construite : hyps ≠ 1 ({len(res.hypotheses)})"
    return res


# @livre Ch.III §7.2 Prop.3 | E III.55 L.6-13 | PDF p.158  (l'injectivité sous la forme LITTÉRALE du dépôt : injective_dans(G, lim←_I))
def g_injective_dans(jj="J", i="I", lam="lam", pt="s", idx="t",
                     x="xx", xp="xp"):
    """{ J cofinale, système projectif } ⊢ injective_dans(G, lim←_I).   [1 hyp].

    L'injectivité, non plus « à la forme obtenue » mais dans le VOCABULAIRE du
    dépôt : `E.injective_dans(f, A)` est
        (∀u)(∀u')( ((u∈A et u'∈A) et f(u)=f(u')) ⇒ u=u' ).

    Deux ajustements par rapport à `injectivite_g_construite` :
      • la prémisse doit être une CONJONCTION, pas une cascade d'implications —
        on assume donc la conjonction et on coupe chaque conjoint, au lieu de
        décharger les hypothèses une à une ;
      • l'ordre des ∀ est (u puis u'), donc on généralise x' AVANT x.
    C'est le troisième des quatre conjoints de `est_bijection_de`, désormais
    disponible sur le MÊME terme que `g_est_fonctionnelle` et `g_domaine`."""
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
        conjonction_elim_gauche, conjonction_elim_droite,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites.prop1_proj.ensembles_prop3_injectif_total import (
        prop3_g_injective,
    )
    G = graphe_g(pt=pt, idx=idx)
    lim = L.lim_proj(var("E"), var("f"))
    th = prop3_g_injective(jj, i, lam, gterme=G,
                           formule_3=g_formule_3_quantifiee(pt=pt, idx=idx),
                           x=x, xp=xp)
    vx, vxp = var(x), var(xp)
    prem = et(et(appartient(vx, lim), appartient(vxp, lim)),
              egal(E.valeur(G, vx), E.valeur(G, vxp)))
    h = N.assume(prem)
    gauche = conjonction_elim_gauche(h)
    for pr in (conjonction_elim_gauche(gauche), conjonction_elim_droite(gauche),
               conjonction_elim_droite(h)):
        assert pr.conclusion in th.hypotheses, \
            f"g_injective_dans : conjoint absent des hypothèses — {pr.conclusion}"
        th = N.modus_ponens(pr, N.loi_deduction(pr.conclusion, th))
    # ⚠️ Les liants du dépôt sont « u »/« up », mais on ne PEUT pas prouver
    # directement avec ces noms : « u » est un liant réservé du kit (le modus
    # ponens interne échoue, mesuré).  On démontre donc avec des noms sûrs, puis
    # on RENOMME en α — dans cet ordre : le liant interne avant la
    # généralisation externe, sinon il faudrait travailler sous un ∀.
    corps = N.generalisation(xp, N.loi_deduction(prem, th))
    corps = _alpha(corps, xp, "up")
    res = _alpha(N.generalisation(x, corps), x, "u")
    assert res.conclusion == E.injective_dans(G, lim), \
        "g_injective_dans : conclusion ≠ injective_dans(G, lim←_I) [liants du dépôt]"
    assert len(res.hypotheses) == 1, \
        f"g_injective_dans : hyps ≠ 1 ({len(res.hypotheses)})"
    return res


def _alpha(thm, ancien, neuf):
    """Renomme en α le liant de tête d'un ⊢ (∀ancien)R en (∀neuf)."""
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
        equivalence_avant,
    )
    from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import (
        alpha_pour_tout,
    )
    if ancien == neuf:
        return thm
    # (∀x)R est encodé ¬(∃x)(¬R) : TROIS niveaux à dépiler, pas deux.
    corps = thm.conclusion.sous[0].sous[0].sous[0]
    return N.modus_ponens(thm, equivalence_avant(
        alpha_pour_tout(ancien, neuf, corps)))


# @livre Ch.III §7.2 Prop.3 | E III.55 L.3-13 | PDF p.158  (Prop. 3 en vocabulaire du dépôt : TOUT est_bijection_de sauf la surjectivité, celle-ci restant en PRÉMISSE explicite)
def g_bijection_sous_surjectivite(jj="J", i="I", lam="lam", pt="s", idx="t",
                                  Efam="E", f="f", but=None):
    """{ J cofinale, système projectif }
       ⊢ ( G⟨lim←_I⟩ = lim←_J )  ⇒  est_bijection_de(G, lim←_I, lim←_J).  [1 hyp].

    LA PROPOSITION 3 dans le vocabulaire exact du dépôt, à une prémisse près —
    et cette prémisse est nommée, pas cachée.

    `est_bijection_de(F,X,Y)` = ((est_fonctionnel F et dom F = X) et
    (injective_dans(F,X) et F⟨X⟩ = Y)).  Trois de ses quatre conjoints sont
    ACQUIS sur le terme construit :
      • `g_est_fonctionnelle` — CLOS ;
      • `g_domaine`           — CLOS ;
      • `g_injective_dans`    — 2 hypothèses (celles de la Prop. 3).
    Le quatrième, la SURJECTIVITÉ `G⟨lim←_I⟩ = lim←_J`, est une égalité
    d'ENSEMBLES : les deux inclusions sont déjà démontrées ponctuellement
    (⊆ par `cofinal_canonique_compatible`, ⊇ par `prolongement_restitue` +
    `prolongement_coherent_universel`) mais leur recollement par extension reste
    à écrire — voir REPORTES.  On la porte donc en PRÉMISSE : le théorème est
    complet et vérifié, et le travail restant se lit comme « décharger cette
    unique prémisse », pas comme « démontrer la Prop. 3 ».

    C'est aussi la garantie que les quatre conjoints portent bien sur le MÊME
    terme : la conjonction ne se formerait pas sinon."""
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
        conjonction_intro,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
        est_bijection_de,
    )
    G = graphe_g(Efam, f, pt=pt, idx=idx)
    lim_i = L.lim_proj(_t(Efam), _t(f))
    if but is None:                                   # E' = lim←_J (système restreint)
        but = L.lim_proj(C.restriction_systeme_indices(_t(Efam), _t(f), var("J")),
                         _t(f))
    surj = E.est_surjective(G, lim_i, but)            # G⟨lim←_I⟩ = lim←_J
    bij = conjonction_intro(g_injective_dans(jj, i, lam, pt, idx),
                            N.assume(surj))           # est_bijective(G, X, Y)
    total = conjonction_intro(conjonction_intro(
        g_est_fonctionnelle(Efam, f, pt=pt, idx=idx),
        g_domaine(Efam, f, pt=pt, idx=idx)), bij)
    assert total.conclusion == est_bijection_de(G, lim_i, but), \
        "g_bijection_sous_surjectivite : ≠ est_bijection_de(G, lim←_I, lim←_J)"
    res = N.loi_deduction(surj, total)
    assert len(res.hypotheses) == 1, \
        f"g_bijection_sous_surjectivite : hyps ≠ 1 ({len(res.hypotheses)})"
    return res


REPORTES = [
    "SURJECTIVITÉ ENSEMBLISTE — l'UNIQUE pièce manquante de la Prop. 3 en "
    "vocabulaire du dépôt.  `g_bijection_sous_surjectivite` démontre "
    "est_bijection_de(G, lim←_I, lim←_J) sous la seule prémisse "
    "« G⟨lim←_I⟩ = lim←_J » ; il reste à la décharger.  Les DEUX inclusions "
    "sont déjà acquises ponctuellement : ⊆ par `cofinal_canonique_compatible` "
    "(la valeur g(x) satisfait la condition (1) restreinte à J), ⊇ par "
    "`prolongement_restitue` + `prolongement_coherent_universel` (tout point "
    "de lim←_J a un antécédent).  Ce qui manque est leur RECOLLEMENT en une "
    "égalité d'ensembles, par `egalite_par_extension` sur l'image directe — "
    "chantier d'assemblage, pas de démonstration.",
    "MIGRATION — FAITE pour la chaîne d'INJECTIVITÉ (paramètres gterme/"
    "formule_3 threadés de cofinal_canonique_coordonnee jusqu'à "
    "prop3_g_injective_universelle, tous rétro-compatibles).  RESTE : les deux "
    "sites de `ensembles_limites_prop4plus_iii7` (:136, :151) fixent encore "
    "`application_canonique_g` en dur — sans conséquence pour la Prop. 3, mais "
    "à paramétrer de la même façon pour retirer l'axiome du dépôt.",
]

__all__ = ["famille_coordonnees", "graphe_g", "corps_formule_3",
           "formule_3_reproduit_l_axiome", "g_est_fonctionnelle",
           "g_est_un_graphe", "g_domaine", "g_formule_3",
           "g_formule_3_quantifiee", "injectivite_g_construite",
           "g_injective_dans", "g_bijection_sous_surjectivite", "REPORTES"]
