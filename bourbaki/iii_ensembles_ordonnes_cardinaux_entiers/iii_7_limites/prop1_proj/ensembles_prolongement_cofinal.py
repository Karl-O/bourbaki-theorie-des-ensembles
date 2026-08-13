"""§III.7.2 Prop. 3 — le prolongement cofinal est BIEN DÉFINI.

────────────────────────────────────────────────────────────────────────────────
Pour la SURJECTIVITÉ de la canonique cofinale g : lim←_I → lim←_J (Prop. 3), on
prolonge un point x de lim←_J à tout I en posant

    x̃_α  :=  f_{αβ}( x_β )        pour n'importe quel β ∈ J avec α ≤ β

— le choix de β étant fourni sans axiome du choix par le témoin canonique
(`ensembles_temoin_cofinal`).  Encore faut-il que la valeur NE DÉPENDE PAS du β
choisi : c'est ce que ce module établit.

  { relation (1) sur x (x ∈ lim←),  cocycle LP_I,  α∈I, β,γ,δ∈I,
    α≤β, α≤γ, β≤δ, γ≤δ }   ⊢   f_{αβ}(x_β)  =  f_{αγ}(x_γ)

Preuve (δ = majorant commun de β et γ, fourni par la filtrance de J) :
  f_{αβ}(x_β) = f_{αβ}(f_{βδ}(x_δ))   [relation (1) en (β,δ), congruence]
              = f_{αδ}(x_δ)            [cocycle α≤β≤δ, symétrisé]
et symétriquement pour γ ; les deux membres valent f_{αδ}(x_δ).

⚠️ Le majorant commun δ est ici une HYPOTHÈSE honnête : la filtrance de J le
fournit, et le témoin canonique de `ensembles_temoin_cofinal` le rendra
explicite au moment d'assembler la surjectivité.
INVARIANT : theorie_ensembles()=22 ; rien postulé.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, et, appartient, libres_f,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
    symetrie, composer_egalites, congruence_terme,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites import (
    ensembles_limites as L, ensembles_limites_canoniques as C,
)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def _cut(thm, *preuves):
    for p in preuves:
        c = p.conclusion
        if c in thm.hypotheses:
            thm = N.modus_ponens(p, N.loi_deduction(c, thm))
    return thm


def _via_delta(Efam, f, leq, vi, vx, a, b, d):
    """{…} ⊢ f_{ab}(x_b) = f_{ad}(x_d)   pour a≤b≤d  (une branche du losange).

    Deux briques : la relation (1) sur x en (b,d) — pr_b x = f_{bd}(pr_d x) — puis
    le cocycle LP_I en (a,b,d) — f_{ad}(y) = f_{ab}(f_{bd}(y)) — appliqué en x_d."""
    va, vb, vd = var(a), var(b), var(d)
    fab = L.appl_proj(_t(f), va, vb)
    xb, xd = E.valeur(vx, vb), E.valeur(vx, vd)

    #  x_b = f_{bd}(x_d)                     [relation (1), paramètres BRUTS]
    rel1 = L.limite_projective_relation_1(Efam, f, leq, vi, vx, b, d)
    prem1 = et(et(appartient(vb, vi), appartient(vd, vi)), leq(vb, vd))
    eq_x = N.modus_ponens(N.assume(prem1), rel1)
    #  f_{ab}(x_b) = f_{ab}(f_{bd}(x_d))     [congruence]
    cong = N.modus_ponens(eq_x, congruence_terme(
        xb, E.valeur(L.appl_proj(_t(f), vb, vd), xd),
        E.valeur(fab, var("w6d")), w="w6d"))
    #  f_{ad}(x_d) = f_{ab}(f_{bd}(x_d))     [cocycle], symétrisé
    coc = L.cocycle_valeur_projectif(f, leq, vi, a, b, d, "xco")
    coc = _instancie_en(coc, xd)
    return composer_egalites(cong, N.modus_ponens(coc, symetrie(
        E.valeur(L.appl_proj(_t(f), va, vd), xd),
        E.valeur(fab, E.valeur(L.appl_proj(_t(f), vb, vd), xd)))))


# `porter_aux_termes` est né ici (ev. 166) puis a été PROMU en tactique générique
# (i_2_theoremes/tactiques/outil_portage.py) : il n'appartient à aucune théorie, et
# le laisser ici obligerait le chapitre IV à importer le chapitre III.  Ré-exporté
# pour que les imports existants restent valides.
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.outil_portage import (  # noqa: E402
    porter_aux_termes,
)


def _instancie_en(coc, point, nom="xco"):
    """Cas à un seul nom (le cocycle en son point) — voir `porter_aux_termes`."""
    return porter_aux_termes(coc, {nom: point})


# @livre Ch.III §7.2 Prop.3 | E III.55 L.3-11 | PDF p.158  (le prolongement cofinal ne dépend pas du majorant choisi : deux indices β, γ ≥ α donnent la même valeur)
def prolongement_bien_defini(Efam="Ef", f="ff", leq=None, i="I", x="xf",
                             a="a", b="b", g="g", d="d"):
    """{ relation (1) sur x, cocycle, α≤β, α≤γ, β≤δ, γ≤δ, indices∈I }
        ⊢ f_{αβ}(x_β) = f_{αγ}(x_γ).

    C'est la BONNE DÉFINITION du prolongement x̃_α : la valeur ne dépend pas du
    majorant cofinal choisi.  Les deux branches du losange passent par δ."""
    if leq is None:
        leq = C._gleq()
    vi, vx = _t(i), _t(x)
    va, vd = var(a), var(d)
    gauche = _via_delta(Efam, f, leq, vi, vx, a, b, d)     # f_{αβ}(x_β)=f_{αδ}(x_δ)
    droite = _via_delta(Efam, f, leq, vi, vx, a, g, d)     # f_{αγ}(x_γ)=f_{αδ}(x_δ)
    fad_xd = E.valeur(L.appl_proj(_t(f), va, vd), E.valeur(vx, vd))
    res = composer_egalites(gauche, N.modus_ponens(droite, symetrie(
        E.valeur(L.appl_proj(_t(f), va, var(g)), E.valeur(vx, var(g))), fad_xd)))
    cible = egal(E.valeur(L.appl_proj(_t(f), va, var(b)), E.valeur(vx, var(b))),
                 E.valeur(L.appl_proj(_t(f), va, var(g)), E.valeur(vx, var(g))))
    assert res.conclusion == cible, "prolongement_bien_defini : ≠ cible"
    return res


__all__ = ["porter_aux_termes", "prolongement_bien_defini", "x_tilde",
           "prolongement_coherent", "prolongement_coherent_universel",
           "prolongement_restitue"]


def x_tilde(f, x, jj, a):
    """x̃_α := f_{α,β(α)}( x_{β(α)} )  — le prolongement au témoin canonique."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites.prop1_proj.ensembles_temoin_cofinal import (
        beta_cofinal,
    )
    ba = beta_cofinal(_t(jj), _t(a))
    return E.valeur(L.appl_proj(_t(f), _t(a), ba), E.valeur(_t(x), ba))


# @livre Ch.III §7.2 Prop.3 | E III.55 L.3-11 | PDF p.158  (la famille prolongée est COHÉRENTE : elle satisfait la relation (1), donc appartient à lim←_I)
def prolongement_coherent(f="ff", jj="J", x="xf", i="I", leq=None,
                          a="a", ap="ap", Efam="Ef"):
    """{ … } ⊢ x̃_α = f_{αα'}( x̃_{α'} )   pour α ≤ α'.            [18 hyps].

    C'est la relation (1) pour la famille prolongée — donc x̃ ∈ lim←_I, ce qui
    est le cœur de la SURJECTIVITÉ de la canonique cofinale (Prop. 3).

    Deux pièces, toutes deux portées aux témoins par `porter_aux_termes` :
      • la bonne définition (`prolongement_bien_defini`) en {β(α), β(α')} :
        x̃_α = f_{α,β(α')}(x_{β(α')})  — les deux majorants donnent la même valeur ;
      • le cocycle en (α, α', β(α')) au point x_{β(α')} :
        f_{α,β(α')}(y) = f_{αα'}( f_{α',β(α')}(y) )  — et le membre droit EST
        f_{αα'}(x̃_{α'})."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites.prop1_proj.ensembles_temoin_cofinal import (
        beta_cofinal,
    )
    if leq is None:
        leq = C._gleq()
    vi, vJ, vx, vf = _t(i), _t(jj), _t(x), _t(f)
    va, vap = var(a), var(ap)
    ba, bap = beta_cofinal(vJ, va), beta_cofinal(vJ, vap)

    # ⚠️ `Efam` est threadé depuis le 5 août 2026 : l'UNIQUE hypothèse mentionnant
    # lim← porte sur `lim_proj(Efam, f)`.  Sans ce paramètre, elle restait figée
    # sur la famille « Ef » et ne pouvait donc PAS être fournie par un point de
    # lim←_J (dont la famille est le système restreint construit).  Défaut
    # inchangé — les appels existants voient exactement le même théorème.
    bd = porter_aux_termes(prolongement_bien_defini(Efam, f, leq, i, x),
                           {"b": ba, "g": bap})
    coc = porter_aux_termes(
        L.cocycle_valeur_projectif(f, leq, vi, a, ap, "dco", "xco"),
        {"dco": bap, "xco": E.valeur(vx, bap)})
    res = composer_egalites(bd, coc)
    cible = egal(x_tilde(vf, vx, vJ, va),
                 E.valeur(L.appl_proj(vf, va, vap), x_tilde(vf, vx, vJ, vap)))
    assert res.conclusion == cible, "prolongement_coherent : ≠ relation (1) pour x̃"
    assert len(res.hypotheses) == 18, "prolongement_coherent : hyps ≠ 18"
    return res


# @livre Ch.III §7.2 Prop.3 | E III.55 L.6-13 | PDF p.158  (le prolongement RESTITUE le point de départ sur J : x̃_α = x_α pour α∈J — c'est « g(x̃) = x »)
def prolongement_restitue(f="ff", jj="J", x="xf", i="I", leq=None, a="a"):
    """{ relation (1) sur x, α∈J, β(α)∈J, α≤β(α) } ⊢ x̃_α = x_α  pour α∈J.

    C'est l'autre moitié de la surjectivité : l'antécédent construit se projette
    bien sur le point de départ.  Immédiat — c'est la relation (1) sur x en
    (α, β(α)), le témoin canonique étant dans J et majorant α (ev. 163)."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites.prop1_proj.ensembles_temoin_cofinal import (
        beta_cofinal,
    )
    if leq is None:
        leq = C._gleq()
    vi, vJ, vx, vf = _t(i), _t(jj), _t(x), _t(f)
    va = var(a)
    ba = beta_cofinal(vJ, va)
    #  relation (1) sur x en (α, β(α)) : x_α = f_{α,β(α)}(x_{β(α)}) = x̃_α
    rel1 = L.limite_projective_relation_1(f, f, leq, vJ, vx, a, "dre")
    rel1 = porter_aux_termes(rel1, {"dre": ba})
    prem = rel1.conclusion.sous[0].sous[0] if rel1.conclusion.sous else None
    res = N.modus_ponens(N.assume(prem), rel1) if prem is not None else rel1
    res = N.modus_ponens(res, symetrie(E.valeur(vx, va), x_tilde(vf, vx, vJ, va)))
    assert res.conclusion == egal(x_tilde(vf, vx, vJ, va), E.valeur(vx, va)), \
        "prolongement_restitue : ≠ (x̃_α = x_α)"
    return res


# @livre Ch.III §7.2 Prop.3 | E III.55 L.3-11 | PDF p.158  (forme UNIVERSELLE : la famille prolongée vérifie la relation (1) pour TOUT couple α≤α', donc x̃ ∈ lim←_I)
def prolongement_coherent_universel(f="ff", jj="J", x="xf", i="I", leq=None,
                                    a="a", ap="ap", Efam="Ef"):
    """⊢ (∀α)(∀α')( … ⇒ x̃_α = f_{αα'}(x̃_{α'}) ).                    [4 hyps].

    La version quantifiée de `prolongement_coherent` : les quatorze hypothèses
    qui portent l'un des deux indices sont déchargées en prémisse, puis on
    généralise.  Ne subsistent que quatre hypothèses de contexte, indépendantes
    des indices.  C'est la condition (1) pour la famille prolongée, donc
    **x̃ ∈ lim←_I** — la moitié « existence de l'antécédent » de la
    surjectivité, sous forme universelle."""
    th = prolongement_coherent(f, jj, x, i, leq, a, ap, Efam)
    portantes = [h for h in th.hypotheses
                 if a in libres_f(h) or ap in libres_f(h)]
    imp = th
    for h in portantes:
        imp = N.loi_deduction(h, imp)
    res = N.generalisation(ap, N.generalisation(a, imp))
    assert all(a not in libres_f(h) and ap not in libres_f(h)
               for h in res.hypotheses), \
        "prolongement_coherent_universel : un indice reste libre dans une hypothèse"
    assert len(res.hypotheses) == 4, \
        f"prolongement_coherent_universel : hyps ≠ 4 ({len(res.hypotheses)})"
    return res
