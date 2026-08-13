"""§III.7.2 Prop. 2 — les fibres (u_α)⁻¹(x'_α) forment un SYSTÈME PROJECTIF.

────────────────────────────────────────────────────────────────────────────────
« Soient (u_α) un système projectif d'applications, u = lim← u_α, et
x' = (x'_α) ∈ lim← E'_α.  Alors les M_α := (u_α)⁻¹(x'_α) forment un système
projectif de parties, et u⁻¹(x') = lim← M_α »  (E III.54) — REPORTÉ jusqu'ici.

Ce module établit les deux premiers étages, exactement comme le livre :

  • `membre_fibre` : { u fonctionnel, u total } ⊢ ( z ∈ u⁻¹⟨{b}⟩ ⇔ u(z) = b )
    — le chaînon manquant : passer de l'appartenance à la fibre à l'égalité
    des valeurs (aucun équivalent dans le dépôt) ;
  • `fibres_systeme_projectif` : ⊢ f_αβ⟨M_β⟩ ⊂ M_α
    — la PREMIÈRE ASSERTION de la Prop. 2, preuve du livre telle quelle :
      z∈f_αβ⟨M_β⟩ ⇒ z=f_αβ(x) avec u_β(x)=x'_β ; alors
      u_α(z) = f'_αβ(u_β(x)) [commute_valeur_proj] = f'_αβ(x'_β) = x'_α
      [relation (1) de la limite projective], donc z ∈ M_α.

✅ LE PONT D'ENCODAGE EST FAIT (5 août 2026).  `M_indice` était un accesseur
OPAQUE sans axiome : rien n'était démontrable sur les M_α, et la 2ᵉ assertion
était hors d'atteinte PAR CONSTRUCTION, pas par difficulté.  Rendu transparent
(une famille EST une fonction, donc sa composante EST sa valeur), il donne :

  • `famille_fibres`       : la famille (M_α) = (u_α⁻¹⟨{x'_α}⟩), CONSTRUITE ;
  • `fibre_composante`     : ⊢ M_α = u_α⁻¹⟨{x'_α}⟩                  [1 hyp] ;
  • `coordonnee_dans_fibre`: ⊢ ( pr_α z ∈ M_α ⇔ u_α(pr_α z) = x'_α ) [3 hyps]
    — LE CHAÎNON : il traduit l'appartenance à lim← M_α en l'égalité u(z)=x'
    lue coordonnée par coordonnée.

RESTE pour la 2ᵉ assertion : recoller par extensionnalité.  D'un côté
`appartient_limite_projective` sur la famille CONSTRUITE donne
z ∈ lim← M_α ⇔ (z ∈ ∏ M_α et condition (1)) ; de l'autre `membre_fibre` donne
z ∈ u⁻¹⟨{x'}⟩ ⇔ u(z) = x', et `lim_u_coordonnee` transforme u(z)=x' en
(∀α) pr_α(u(z)) = x'_α, soit (∀α) u_α(pr_α z) = x'_α — que le chaînon convertit
en (∀α) pr_α z ∈ M_α.  Il ne manque que l'assemblage, plus la condition (1) sur
z, commune aux deux côtés.
INVARIANT : theorie_ensembles()=22 ; rien postulé.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, et, equiv, appartient, existe, inclus, pourtout,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, instancie,
)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import (
    existe_elimination, alpha_existe,
)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
    symetrie, composer_egalites, congruence_terme,
)
from bourbaki.ii_theorie_des_ensembles.ii_2_couples.ii_2_1_definition_couples.ensembles_couples import (
    singleton_membre,
)
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_image_famille.ensembles_image_algebre_binaire_ii4 import (
    membre_image, membre_image_reciproque,
)
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_4_fonctions.ensembles_fonctions import (
    valeur_caracterisation,
)
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_2_reciproque.ensembles_reciproque import (
    couple_reciproque,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites.ensembles_limites import (
    limite_projective_relation_1,
)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def _cut(thm, *preuves):
    for p in preuves:
        c = p.conclusion
        if c in thm.hypotheses:
            thm = N.modus_ponens(p, N.loi_deduction(c, thm))
    return thm


# @livre Ch.III §7.2 Prop.2 | E III.54 L.20-23 | PDF p.157  (la famille des fibres (M_α)_{α∈I} = ((u_α)⁻¹⟨{x'_α}⟩)_{α∈I}, CONSTRUITE au lieu d'être une donnée opaque)
def famille_fibres(u="uf", xp="xp", i="I", liant="k"):
    """La famille (M_α)_{α∈I} des fibres, comme TERME : M_α := u_α⁻¹⟨{x'_α}⟩.

    Jusqu'au 5 août 2026 la donnée M était opaque et son accesseur `M_indice`
    aussi — donc rien n'était démontrable sur les M_α, et la 2ᵉ assertion de la
    Prop. 2 (« u⁻¹(x') = lim← M_α ») était hors d'atteinte PAR CONSTRUCTION.
    `M_indice` est devenu transparent (une famille EST une fonction) ; la famille
    peut donc être CONSTRUITE, et ses composantes se calculent."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites import (
        ensembles_limites_canoniques as C,
    )
    vk = var(liant)
    return E.graphe_terme(
        _t(i),
        E.image(E.reciproque(C.u_indice(_t(u), vk)),
                E.singleton(E.valeur(_t(xp), vk))),
        liant)


# @livre Ch.III §7.2 Prop.2 | E III.54 L.20-23 | PDF p.157  (le pont : la composante de la famille construite EST la fibre)
def fibre_composante(u="uf", xp="xp", i="I", liant="k", a="a"):
    """{ α ∈ I } ⊢ M_α = u_α⁻¹⟨{x'_α}⟩.                                [1 hyp].

    LE PONT qui manquait : il dit que la composante d'indice α de la famille
    construite est bien la fibre.  Sans lui, « M_α » et « u_α⁻¹⟨{x'_α}⟩ » sont
    deux termes que rien ne relie — c'est ce qui bloquait le recollement de la
    2ᵉ assertion.

    Immédiat une fois `M_indice` transparent : c'est la valeur d'un graphe-terme.
    Même schéma que `restriction_valeur` pour le système restreint."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.cantor.ensembles_cantor import (
        graphe_terme_valeur,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites import (
        ensembles_limites_canoniques as C,
    )
    vk, va = var(liant), var(a)
    interne = E.image(E.reciproque(C.u_indice(_t(u), vk)),
                      E.singleton(E.valeur(_t(xp), vk)))
    res = graphe_terme_valeur(_t(i), interne, a, liant, "y")
    cible = egal(C.M_indice(famille_fibres(u, xp, i, liant), va),
                 E.image(E.reciproque(C.u_indice(_t(u), va)),
                         E.singleton(E.valeur(_t(xp), va))))
    assert res.conclusion == cible, \
        "fibre_composante : conclusion ≠ (M_α = u_α⁻¹⟨{x'_α}⟩)"
    assert res.hypotheses == frozenset({appartient(va, _t(i))}), \
        "fibre_composante : hypothèse ≠ {α ∈ I}"
    return res


# @livre Ch.III §7.2 Prop.2 | E III.54 L.24-27 | PDF p.157  (le chaînon de la 2ᵉ assertion : « la α-coordonnée est dans la fibre » ⇔ « u_α l'envoie sur x'_α »)
def coordonnee_dans_fibre(u="uf", xp="xp", i="I", liant="k", a="a", z="zf",
                          t="tz"):
    """{ u_α fonctionnel, u_α total, α ∈ I }
        ⊢ ( pr_α z ∈ M_α  ⇔  u_α(pr_α z) = x'_α ).                    [3 hyps].

    LE CHAÎNON de la 2ᵉ assertion de la Prop. 2.  Il traduit l'appartenance
    d'une coordonnée à la fibre en une ÉGALITÉ de valeurs — c'est-à-dire
    exactement ce que la caractérisation de lim← M_α réclame d'un côté et ce que
    « u(z) = x' » donne de l'autre.

    Deux pièces : `membre_fibre_t` (l'appartenance à u_α⁻¹⟨{x'_α}⟩ ÉQUIVAUT à
    u_α(·)=x'_α) et `fibre_composante` (M_α EST cette fibre), recollées par S6
    sur la position ENSEMBLE de l'appartenance.  C'est ce second pont qui
    manquait tant que `M_indice` était opaque."""
    from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
        symetrie,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites import (
        ensembles_limites_canoniques as C,
    )
    va, vz = var(a), _t(z)
    ua = C.u_indice(_t(u), va)
    xpa = E.valeur(_t(xp), va)
    pra = E.projection_indice(vz, va)
    Ma = C.M_indice(famille_fibres(u, xp, i, liant), va)
    fibre = E.image(E.reciproque(ua), E.singleton(xpa))

    # ⚠️ ne PAS nommer cette variable « equiv » : elle masquerait le
    # constructeur importé du même nom (mesuré : « Theoreme object is not
    # callable », erreur opaque loin de sa cause).
    equ_fibre = membre_fibre_t(ua, xpa, pra, t)      # pr_α z ∈ fibre ⇔ u_α(pr_α z)=x'_α
    pont = fibre_composante(u, xp, i, liant, a)      # M_α = fibre
    # transporter l'équivalence de « fibre » vers « M_α » (S6, position ENSEMBLE)
    res = N.modus_ponens(equ_fibre, equivalence_avant(N.modus_ponens(
        N.modus_ponens(pont, symetrie(Ma, fibre)),
        N.s6(fibre, Ma, "hmf",
             equiv(appartient(pra, var("hmf")), egal(E.valeur(ua, pra), xpa))))))
    assert res.conclusion == equiv(appartient(pra, Ma),
                                           egal(E.valeur(ua, pra), xpa)), \
        "coordonnee_dans_fibre : ≠ (pr_α z ∈ M_α ⇔ u_α(pr_α z) = x'_α)"
    assert len(res.hypotheses) == 3, \
        f"coordonnee_dans_fibre : hyps ≠ 3 ({len(res.hypotheses)})"
    return res


# @livre Ch.III §7.2 Prop.2 | E III.54 L.24-27 | PDF p.157  (le chaînon relié à u(z) : « pr_α z ∈ M_α » ⇔ « la α-coordonnée de u(z) est x'_α »)
def coordonnee_de_u_dans_fibre(u="uf", xp="xp", i="I", liant="k", a="a",
                               z="zf", t="tz", EfamE="E", fE="f",
                               EfamF="Ep", fF="fp", leq=None):
    """{ u_α fonctionnel, u_α total, α ∈ I, z ∈ lim←_I }
        ⊢ ( pr_α z ∈ M_α  ⇔  pr_α(u(z)) = x'_α ).                     [4 hyps].

    Le chaînon, exprimé du côté de u(z) plutôt que de u_α.  C'est la forme dont
    les DEUX côtés de la 2ᵉ assertion ont besoin :
      • à gauche, « pr_α z ∈ M_α » est ce que réclame l'appartenance à lim← M_α ;
      • à droite, « pr_α(u(z)) = x'_α » est ce que donne u(z) = x' lu
        coordonnée par coordonnée.
    On compose donc `coordonnee_dans_fibre` avec `lim_u_coordonnee`
    (pr_α(u(z)) = u_α(pr_α z)), transportée par S6 dans le membre DROIT de
    l'équivalence."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites import (
        ensembles_limites_canoniques as C,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites.ensembles_limites_prop2_3_iii7 import (
        lim_proj_u, lim_u_coordonnee,
    )
    va, vz = var(a), _t(z)
    ua = C.u_indice(_t(u), va)
    xpa = E.valeur(_t(xp), va)
    pra = E.projection_indice(vz, va)
    Ma = C.M_indice(famille_fibres(u, xp, i, liant), va)
    uz = E.valeur(lim_proj_u(_t(EfamE), _t(fE), _t(EfamF), _t(fF), _t(u)), vz)
    pra_uz = E.projection_indice(uz, va)

    base = coordonnee_dans_fibre(u, xp, i, liant, a, z, t)   # ⇔ u_α(pr_α z)=x'_α
    coord = lim_u_coordonnee(EfamE, fE, EfamF, fF, u, leq, i, a, z)  # pr_α(u z)=u_α(pr_α z)
    # remplacer u_α(pr_α z) par pr_α(u(z)) DANS le membre droit de l'équivalence.
    # ⚠️ `lim_u_coordonnee` conclut pr_α(u z) = u_α(pr_α z) : c'est le SENS
    # INVERSE de celui qu'attend S6 ici, d'où la symétrisation.
    coord_sym = N.modus_ponens(coord, symetrie(pra_uz, E.valeur(ua, pra)))
    res = N.modus_ponens(base, equivalence_avant(N.modus_ponens(
        coord_sym, N.s6(E.valeur(ua, pra), pra_uz, "hcu",
                        equiv(appartient(pra, Ma), egal(var("hcu"), xpa))))))
    assert res.conclusion == equiv(appartient(pra, Ma), egal(pra_uz, xpa)), \
        "coordonnee_de_u_dans_fibre : ≠ ( pr_α z ∈ M_α ⇔ pr_α(u(z)) = x'_α )"
    assert len(res.hypotheses) == 4, \
        f"coordonnee_de_u_dans_fibre : hyps ≠ 4 ({len(res.hypotheses)})"
    return res


def _equiv_sous_garde(imp, garde):
    """De ⊢ (G ⇒ (P ⇔ Q)), déduire ⊢ ( (G ⇒ P) ⇔ (G ⇒ Q) ).

    Pas propositionnel indispensable pour quantifier une équivalence GARDÉE :
    `congruence_pour_tout` réclame une équivalence, pas une implication vers une
    équivalence.  Les deux sens sont symétriques — sous G on récupère P⇔Q, puis
    on l'utilise dans le bon sens."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
        impl,
    )
    hg = N.assume(garde)
    eq = N.modus_ponens(hg, imp)                       # P ⇔ Q  (sous G)
    avant, arriere = equivalence_avant(eq), equivalence_arriere(eq)
    sens = []
    for direction in (avant, arriere):
        src = direction.conclusion.sous[0].sous[0]     # l'antécédent de P⇒Q
        h_src = N.assume(impl(garde, src))
        got = N.modus_ponens(N.modus_ponens(hg, h_src), direction)
        sens.append(N.loi_deduction(impl(garde, src),
                                    N.loi_deduction(garde, got)))
    return conjonction_intro(sens[0], sens[1])


# @livre Ch.III §7.2 Prop.2 | E III.54 L.24-27 | PDF p.157  (le chaînon QUANTIFIÉ : « toutes les coordonnées sont dans les fibres » ⇔ « u(z) a les coordonnées de x' »)
def fibres_partout(u="uf", xp="xp", i="I", liant="k", a="a", z="zf", t="tz",
                   EfamE="E", fE="f", EfamF="Ep", fF="fp", leq=None):
    """{ (∀α)(α∈I ⇒ (u_α fonctionnel et u_α total)),  z ∈ lim←_I }
        ⊢ ( (∀α)(α∈I ⇒ pr_α z ∈ M_α) ⇔ (∀α)(α∈I ⇒ pr_α(u(z)) = x'_α) ).  [2 hyps].

    LE CŒUR de la 2ᵉ assertion, quantifié.  Le membre gauche est ce que réclame
    l'appartenance à lim← M_α (clause des valeurs) ; le membre droit est ce que
    donne « u(z) = x' » lu coordonnée par coordonnée.  Les relier, c'est relier
    les deux ensembles de l'identité u⁻¹(x') = lim← M_α.

    Les hypothèses ponctuelles (u_α fonctionnel, u_α total) sont remplacées par
    une hypothèse de FAMILLE, comme le fait `prop2_injectivite` pour
    l'injectivité : c'est la forme honnête, et c'est ce qui permet de
    généraliser (rien ne porte plus α)."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
        impl,
    )
    from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import (
        congruence_pour_tout,
    )
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
        libres_f,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites import (
        ensembles_limites_canoniques as C,
    )
    va, vi = var(a), _t(i)
    ua = C.u_indice(_t(u), va)
    base = coordonnee_de_u_dans_fibre(u, xp, i, liant, a, z, t,
                                      EfamE, fE, EfamF, fF, leq)
    h_fam = N.assume(pourtout(a, impl(appartient(va, vi),
                                      et(E.est_fonctionnel(ua), hyp_total(ua, t)))))
    paire = N.modus_ponens(N.assume(appartient(va, vi)), instancie(h_fam, va))
    base = _cut(base, conjonction_elim_gauche(paire), conjonction_elim_droite(paire))
    res = congruence_pour_tout(
        _equiv_sous_garde(N.loi_deduction(appartient(va, vi), base),
                          appartient(va, vi)), a)
    assert all(a not in libres_f(h) for h in res.hypotheses), \
        "fibres_partout : α reste libre dans une hypothèse"
    assert len(res.hypotheses) == 2, \
        f"fibres_partout : hyps ≠ 2 ({len(res.hypotheses)})"
    return res


def hyp_total(u, t="tz"):
    """(∀t)( (∃y)( (t,y) ∈ u ) )  — « u est définie partout » (forme du dépôt)."""
    vu, vt = _t(u), var(t)
    return pourtout(t, existe("y", appartient(E.couple(vt, var("y")), vu)))


# @livre Ch.III §7.2 Prop.2 | E III.54 L.20-23 | PDF p.157  (chaînon : appartenir à la fibre u⁻¹⟨{b}⟩, c'est avoir u(z)=b)
def membre_fibre(u="ua", b="bpt", z="zf", t="tz"):
    """{ u fonctionnel, u total } ⊢ ( z ∈ u⁻¹⟨{b}⟩ ⇔ u(z) = b ).      [2 hyps].

    → : z∈u⁻¹⟨{b}⟩ donne un témoin m∈{b} avec (m,z)∈u⁻¹, i.e. (z,m)∈u ;
        m=b (singleton) et (z,m)∈u donne u(z)=m=b (valeur_caracterisation).
    ← : de u(z)=b, le couple (z,u(z))∈u (totalité) se réécrit (z,b)∈u, d'où
        (b,z)∈u⁻¹ et le témoin b∈{b}."""
    vu, vb, vz = _t(u), _t(b), _t(z)
    hfunc = N.assume(E.est_fonctionnel(vu))
    htot = N.assume(hyp_total(vu, t))
    fib = E.image(E.reciproque(vu), E.singleton(vb))
    uz = E.valeur(vu, vz)

    # (z, u(z)) ∈ u   — de la totalité, par existe_temoin
    r_y = appartient(E.couple(vz, var("y")), vu)
    ex_y = instancie(htot, vz)
    cpl = N.modus_ponens(ex_y, N.existe_temoin(r_y, "y"))       # (z,u(z))∈u

    # ── → ───────────────────────────────────────────────────────────────────
    car = membre_image_reciproque(vu, E.singleton(vb), vz)
    corps = et(appartient(var("m"), E.singleton(vb)),
               appartient(E.couple(var("m"), vz), E.reciproque(vu)))
    hb = N.assume(corps)
    m_eq_b = N.modus_ponens(conjonction_elim_gauche(hb),
                            equivalence_avant(singleton_membre(var("m"), vb)))
    zm_u = N.modus_ponens(conjonction_elim_droite(hb),
                          equivalence_avant(couple_reciproque(vu, var("m"), vz)))
    vc = _cut(instancie(N.generalisation("y", valeur_caracterisation(vu, vz)),
                        var("m")), ex_y)
    m_uz = N.modus_ponens(zm_u, equivalence_avant(vc))          # m = u(z)
    uz_b = composer_egalites(N.modus_ponens(m_uz, symetrie(var("m"), uz)), m_eq_b)
    fwd_imp = existe_elimination(N.loi_deduction(corps, uz_b), "m")
    hz = N.assume(appartient(vz, fib))
    corps_x = et(appartient(var("x"), E.singleton(vb)),
                 appartient(E.couple(var("x"), vz), E.reciproque(vu)))
    ex_m = N.modus_ponens(N.modus_ponens(hz, equivalence_avant(car)),
                          equivalence_avant(alpha_existe("x", "m", corps_x)))
    fwd = N.loi_deduction(appartient(vz, fib),
                          N.modus_ponens(ex_m, fwd_imp))

    # ── ← ───────────────────────────────────────────────────────────────────
    heq = N.assume(egal(uz, vb))
    zb_u = N.modus_ponens(cpl, equivalence_avant(N.modus_ponens(
        heq, N.s6(uz, vb, "w6f", appartient(E.couple(vz, var("w6f")), vu)))))
    bz_r = N.modus_ponens(zb_u, equivalence_arriere(
        couple_reciproque(vu, vb, vz)))                          # (b,z)∈u⁻¹
    b_in = N.modus_ponens(N.reflexivite(vb), equivalence_arriere(
        singleton_membre(vb, vb)))
    ex_b = N.modus_ponens(conjonction_intro(b_in, bz_r), N.s5(corps_x, vb, "x"))
    bwd = N.loi_deduction(egal(uz, vb),
                          N.modus_ponens(ex_b, equivalence_arriere(car)))

    res = conjonction_intro(fwd, bwd)
    assert set(res.hypotheses) <= {hfunc.conclusion, htot.conclusion}, \
        "membre_fibre : hyps non honnêtes"
    return res





# @livre Ch.III §7.2 Prop.2 | E III.54 L.20-23 | PDF p.157  (membre_fibre aux TERMES : relais noms→termes, les hypothèses étant déchargées en antécédents avant généralisation)
def membre_fibre_t(u, b, z, t="tz"):
    """{ u fonctionnel, u total } ⊢ ( z ∈ u⁻¹⟨{b}⟩ ⇔ u(z) = b ), u/b/z TERMES.

    `membre_fibre` se prouve aux NOMS (le kit C46/images exige des noms) ; on
    décharge ses deux hypothèses en antécédents, on généralise, on instancie
    aux termes, puis on ré-assume — motif _cva_t (ev. 126).

    ⚠️ PIÈGE VÉRIFIÉ (4 août) : le terme `u` passé ici ne doit contenir AUCUNE
    variable libre nommée « u », « v » ou « z » — ce sont les liants de
    `est_fonctionnel`.  Une famille notée u (u_indice(u,β) contient « u »
    libre) fait renommer le liant à la substitution, et l'hypothèse ré-assumée
    ne s'apparie plus : mesuré, u → ÉCHEC, uf → OK (2 hyps)."""
    vu, vb, vz = _t(u), _t(b), _t(z)
    base = membre_fibre("ua", "bpt", "zf", t)
    h1 = E.est_fonctionnel(var("ua"))
    h2 = hyp_total(var("ua"), t)
    imp = N.loi_deduction(h2, N.loi_deduction(h1, base))          # 0 hyp
    gen = N.generalisation("ua", N.generalisation(
        "bpt", N.generalisation("zf", imp)))
    inst = instancie(instancie(instancie(gen, vu), vb), vz)
    #   ré-assumer les deux hypothèses, aux termes
    return N.modus_ponens(N.assume(E.est_fonctionnel(vu)),
                          N.modus_ponens(N.assume(hyp_total(vu, t)), inst))


# @livre Ch.III §7.2 Prop.2 | E III.54 L.20-27 | PDF p.157  (Prop. 2, 1ʳᵉ assertion : les fibres M_α = (u_α)⁻¹(x'_α) forment un SYSTÈME PROJECTIF de parties — f_αβ⟨M_β⟩ ⊂ M_α)
def fibres_systeme_projectif(u="uf", f="ff", g="gg", Efamp="Ep", xp="xp",
                             i="I", leq=None, a="a", b="b", z="zf", x="xw"):
    """{ α,β∈I et α≤β ; x'∈lim← ; commute_valeur_proj ; f_αβ, u_α, u_β
        fonctionnels et totaux } ⊢ f_αβ⟨M_β⟩ ⊂ M_α.            [8 hyps].

    Preuve du livre, telle quelle : z∈f_αβ⟨M_β⟩ donne un témoin x∈M_β avec
    z=f_αβ(x) ; alors u_α(z) = u_α(f_αβ(x)) = g_αβ(u_β(x)) [commute]
    = g_αβ(x'_β) [x∈M_β, membre_fibre] = x'_α [relation (1)] ; donc z∈M_α.

    ⚠️ Objets nommés « uf »/« ff »/« gg », témoin « xw » : les lettres u, v, z
    sont les liants de est_fonctionnel et casseraient l'appariement (cf.
    membre_fibre_t).  `limite_projective_relation_1` reçoit ses paramètres
    BRUTS (elle fait var() en interne).  L'hypothèse de domaine de C46 est
    déchargée AVANT l'élimination du témoin (sinon « xw libre »)."""
    from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_image_famille.ensembles_image_algebre_binaire_ii4 import (
        membre_image,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites import (
        ensembles_limites as L, ensembles_limites_canoniques as C,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites.ensembles_limites_props import (
        commute_valeur_proj,
    )
    if leq is None:
        leq = C._gleq()
    vi, va, vb, vz, vx = _t(i), var(a), var(b), var(z), var(x)
    vu, vf, vg, vxp = _t(u), _t(f), _t(g), _t(xp)
    ua, ub = C.u_indice(vu, va), C.u_indice(vu, vb)
    fab, gab = L.appl_proj(vf, va, vb), L.appl_proj(vg, va, vb)
    xpa, xpb = E.valeur(vxp, va), E.valeur(vxp, vb)
    Ma = E.image(E.reciproque(ua), E.singleton(xpa))
    Mb = E.image(E.reciproque(ub), E.singleton(xpb))

    prem = et(et(appartient(va, vi), appartient(vb, vi)), leq(va, vb))
    Hp = N.assume(prem)
    eq_x = N.modus_ponens(Hp, L.limite_projective_relation_1(
        Efamp, g, leq, vi, vxp, a, b))               # x'_α = g_αβ(x'_β)
    comm = N.modus_ponens(Hp, instancie(instancie(instancie(N.assume(
        commute_valeur_proj(vu, vf, vg, leq, vi, a, b, x)), va), vb), vx))
    mf_b, mf_a = membre_fibre_t(ub, xpb, vx), membre_fibre_t(ua, xpa, vz)

    corps = et(appartient(vx, Mb), appartient(E.couple(vx, vz), fab))
    hb = N.assume(corps)
    ub_x = N.modus_ponens(conjonction_elim_gauche(hb), equivalence_avant(mf_b))
    vc = instancie(N.generalisation("y", valeur_caracterisation(fab, vx)), vz)
    ex_y = N.modus_ponens(conjonction_elim_droite(hb), N.s5(
        appartient(E.couple(vx, var("y")), fab), vz, "y"))
    vc = _cut(vc, ex_y)
    z_eq = N.modus_ponens(conjonction_elim_droite(hb), equivalence_avant(vc))
    cong_z = N.modus_ponens(z_eq, congruence_terme(
        vz, E.valeur(fab, vx), E.valeur(ua, var("w6p")), w="w6p"))
    cong_u = N.modus_ponens(ub_x, congruence_terme(
        E.valeur(ub, vx), xpb, E.valeur(gab, var("w6q")), w="w6q"))
    ua_z = composer_egalites(composer_egalites(composer_egalites(
        cong_z, comm), cong_u),
        N.modus_ponens(eq_x, symetrie(xpa, E.valeur(gab, xpb))))
    z_in_Ma = N.modus_ponens(ua_z, equivalence_arriere(mf_a))
    imp = existe_elimination(N.loi_deduction(corps, z_in_Ma), x)

    hz = N.assume(appartient(vz, E.image(fab, Mb)))
    corps_x = et(appartient(var("x"), Mb), appartient(E.couple(var("x"), vz), fab))
    ex = N.modus_ponens(N.modus_ponens(hz, equivalence_avant(
        membre_image(fab, Mb, vz))),
        equivalence_avant(alpha_existe("x", x, corps_x)))
    res = N.generalisation(z, N.loi_deduction(
        appartient(vz, E.image(fab, Mb)), N.modus_ponens(ex, imp)))
    assert res.conclusion == inclus(E.image(fab, Mb), Ma, z=z), \
        "fibres_systeme_projectif : ≠ f_αβ⟨M_β⟩ ⊂ M_α"
    assert len(res.hypotheses) == 8, "fibres_systeme_projectif : hyps ≠ 8"
    return res


REPORTES = [
    "Prop. 2 §III.7.2, 2ᵉ assertion (u⁻¹(x') = lim← M_α) — la 1ʳᵉ assertion est "
    "FAITE ci-dessus ; la seconde exige le pont d'encodage « famille de parties » "
    "(M_indice) pour parler de lim← M_α.",
]

