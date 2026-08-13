"""§II.6.5 / E.R.23 item 3 — la bijection induite b est SURJECTIVE sur f⟨E⟩
(niveau valeurs) ; assemblage bijection = injectivité + surjectivité.

Complète `ensembles_decomposition_effective` (le CŒUR passage_quotient_Rf et
l'injectivité de b via le PONT y sont FAITS — lire d'abord).  Ici, le volet
SURJECTIVITÉ réclamé par E.R.23 item 3 (« l'application bijective de E/R sur
f(E) », PDF p.326 vérifié en PNG ; texte principal E II.44 L.25-28) :

  • `b_surjective_valeurs(f,b,e)` — SURJECTIVITÉ de b sur l'image f⟨E⟩, au
    niveau des VALEURS et via le PONT :
        { pont, Hf1 } ⊢ (∀z)( z ∈ f⟨E⟩ ⇒ (∃x)( x∈E  et  b(θ(x)) = z ) )
    « tout point de f⟨E⟩ est valeur de b en une classe θ(x), x∈E ».
    Preuve : z∈f⟨E⟩ ⇔ (∃x)(x∈E et (x,z)∈f)  (AXIOME_IMAGE, un des 22) ; sous le
    corps (point exotique xdb) : z = f(xdb)[_vf] par le MOTIF C46 redéroulé
    DIRECTEMENT au liant de valeur « _vf » du pont (existe_temoin + S5 +
    fonctionnalité Hf1, domaine DÉRIVÉ du (xdb,z)∈f lui-même — alpha_tau est
    INTERDIT sur « _vf », pas une lettre simple : piège τ-liant) ; le pont donne
    b(θ(xdb)) = f(xdb) = z ; ∃-intro (témoin xdb, liant « x ») puis élimination.

  • `b_bijective_valeurs(f,b,e)` — ASSEMBLAGE au niveau valeurs :
        { pont, Hf1 } ⊢ injective (forme b_injective_via_pont)  ET  surjective.

HYPOTHÈSES HONNÊTES (2, jamais postulées) :
  pont = (∀x)(x∈E ⇒ b(θ_{R_f}(x)) = f(x))   (pont_valeurs_b, la relation
         caractéristique de la bijection induite) ;
  Hf1  = est_fonctionnel(f)                  (f graphe fonctionnel).

REPORTÉ (théorèmes durs, jamais postulés) : la forme GRAPHE
est_bijection_de(b, E/R_f, f⟨E⟩) et l'équipotence Eq(E/R_f, f⟨E⟩) — elles
exigent la construction effective du graphe de b depuis son axiome de
membership (`membre_bijection_induite`, théorie dédiée S8) : fonctionnalité de
b (via C55 classes égales ⇒ R_f), dom b = E/R_f (AXIOME_DOM + membre_quotient)
et image(b, E/R_f) = f⟨E⟩ — session dédiée (motif : decomposition_fibres_bij).

Liants : « z » (point de f⟨E⟩), « xdb » (point exotique d'élimination), « x »
(liant ∃ de la conclusion et du pont), « w » (classe θ), « _vf »/« _vb »
(liants de valeur frais de decomposition_effective), « y » (liant C46).
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, et, impl, appartient, existe, pourtout, subst_f)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege import syllogisme
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_transitivite, instancie)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
    symetrie, composer_egalites)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import (
    existe_elimination, alpha_existe)
from bourbaki.ii_theorie_des_ensembles.ii_6_relations_equivalence.ii_6_5_decomposition.ensembles_decomposition_effective import (
    _VF, _VB, _valf, _valb, classe_objets_Rf, pont_valeurs_b, b_injective_via_pont)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# ── Cible (reconstruction de la conclusion attendue, pour vérification ==) ─────
def b_surjective_valeurs_cible(f="f", b="b", e=None, z="z", x="x", w="w"):
    """(∀z)( z ∈ f⟨E⟩ ⇒ (∃x)( x∈E et b(θ(x)) = z ) )."""
    vf, vb = _t(f), _t(b)
    ve = E.dom(vf) if e is None else _t(e)
    vz, vx = var(z), var(x)
    corps = et(appartient(vx, ve),
               egal(_valb(vb, classe_objets_Rf(vf, vx, e=ve, w=w)), vz))
    return pourtout(z, impl(appartient(vz, E.image(vf, ve)), existe(x, corps)))


# ═══════════════════════════════════════════════════════════════════════════════
# 1.  SURJECTIVITÉ de b sur f⟨E⟩  (niveau valeurs, via le PONT)
# ═══════════════════════════════════════════════════════════════════════════════
# @livre Ch.II §6.5 Prop.- | E II.44 L.25-28 | PDF p.95
# @livre Ch.R §5 Prop.- | E.R.23 item 3 (application bijective de E/R sur f(E) : surjectivité) | PDF p.326
def b_surjective_valeurs(f="f", b="b", e=None, z="z", x="x", w="w"):
    """🎯 { pont, Hf1 } ⊢ (∀z)( z ∈ f⟨E⟩ ⇒ (∃x)( x∈E et b(θ(x)) = z ) ).

    SURJECTIVITÉ de la bijection induite b sur l'image f⟨E⟩, au niveau des
    valeurs : tout z de f⟨E⟩ est atteint par b en une classe θ(x), x∈E.
    Hypothèses exactes {pont_valeurs_b, est_fonctionnel(f)} (docstring module)."""
    vf, vb = _t(f), _t(b)
    ve = E.dom(vf) if e is None else _t(e)
    vz, vxdb = var(z), var("xdb")

    # (0) AXIOME_IMAGE (un des 22) : z∈f⟨E⟩ ⇔ (∃x)(x∈E et (x,z)∈f), liant α→xdb
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_IMAGE)
    inst = instancie(instancie(instancie(ax, vf), ve), vz)
    corps_img = et(appartient(var("x"), ve),
                   appartient(E.couple(var("x"), vz), vf))
    ren = alpha_existe("x", "xdb", corps_img)
    img_car = equivalence_transitivite(inst, ren)    # z∈f⟨E⟩ ⇔ (∃xdb)B

    # (1) sous le corps B (point exotique xdb) : z = f(xdb)[_vf]  (motif C46,
    #     redéroulé AU LIANT DE VALEUR _vf du pont — alpha_tau est interdit ici,
    #     « _vf » n'est pas une lettre simple ; existe_temoin/S5 y suffisent)
    B = et(appartient(vxdb, ve), appartient(E.couple(vxdb, vz), vf))
    hB = N.assume(B)
    h_xE = conjonction_elim_gauche(hB)               # xdb∈E
    h_xzF = conjonction_elim_droite(hB)              # (xdb,z)∈f
    r_vf = appartient(E.couple(vxdb, var(_VF)), vf)  # (xdb,_vf)∈f  (_vf libre)
    fx = _valf(vf, vxdb)                             # f(xdb)[_vf] = τ__vf(r_vf)
    dom_ex = N.modus_ponens(h_xzF, N.s5(r_vf, vz, _VF))          # (∃_vf)((xdb,_vf)∈f)
    xfx = N.modus_ponens(dom_ex, N.existe_temoin(r_vf, _VF))     # (xdb, f(xdb))∈f
    hfunc = N.assume(E.est_fonctionnel(vf))          # Hf1
    # fonctionnalité instanciée (u,v,z) := (xdb, vdb, f(xdb)) — « vdb » exotique
    # (le liant interne « z » d'est_fonctionnel capturerait le point z), puis
    # ∀-clôture/ré-instanciation de vdb en z.
    func_v = instancie(instancie(instancie(hfunc, vxdb), var("vdb")), fx)
    func_z = instancie(N.generalisation("vdb", func_v), vz)
    eq_z = N.modus_ponens(conjonction_intro(h_xzF, xfx), func_z)  # z = f(xdb)[_vf]

    # (3) le PONT en xdb : b(θ(xdb)) = f(xdb)[_vf], d'où b(θ(xdb)) = z
    pont = pont_valeurs_b(vf, vb, ve, x=x, w=w)
    h_pont = N.assume(pont)
    val_b = N.modus_ponens(h_xE, instancie(h_pont, vxdb))    # b(θ(xdb)) = f(xdb)[_vf]
    fz = N.modus_ponens(eq_z, symetrie(vz, _valf(vf, vxdb)))  # f(xdb)[_vf] = z
    b_eq_z = composer_egalites(val_b, fz)            # b(θ(xdb)) = z   [pont, Hf1, B]

    # (4) ∃-intro (témoin xdb, liant « x ») puis élimination du point exotique
    corps_sur = et(appartient(var(x), ve),
                   egal(_valb(vb, classe_objets_Rf(vf, var(x), e=ve, w=w)), vz))
    temoin = conjonction_intro(h_xE, b_eq_z)
    assert temoin.conclusion == subst_f(vxdb, x, corps_sur), "témoin ≠ (xdb|x)corps"
    Cn = N.modus_ponens(temoin, N.s5(corps_sur, vxdb, x))    # (∃x)(x∈E et b(θx)=z)
    imp = existe_elimination(N.loi_deduction(B, Cn), "xdb")  # (∃xdb)B ⇒ (∃x)(…)
    res0 = syllogisme(equivalence_avant(img_car), imp)       # z∈f⟨E⟩ ⇒ (∃x)(…)
    res = N.generalisation(z, res0)

    assert res.conclusion == b_surjective_valeurs_cible(vf, vb, ve, z, x, w), \
        "surjectivité : conclusion inattendue"
    assert res.hypotheses == frozenset({pont, E.est_fonctionnel(vf)}), \
        "surjectivité : hypothèses ≠ {pont, Hf1}"
    return res


# ═══════════════════════════════════════════════════════════════════════════════
# 2.  ASSEMBLAGE : b bijective au niveau valeurs (injectivité + surjectivité)
# ═══════════════════════════════════════════════════════════════════════════════
# @livre Ch.II §6.5 Prop.- | E II.44 L.25-28 | PDF p.95
# @livre Ch.R §5 Prop.- | E.R.23 item 3 (application bijective de E/R sur f(E)) | PDF p.326
def b_bijective_valeurs(f="f", b="b", e=None, x="x", y="y", z="z", w="w"):
    """🎯 { pont, Hf1 } ⊢ (∀x)(∀y)( … ⇒ θx=θy )  ET  (∀z)( z∈f⟨E⟩ ⇒ (∃x)(…) ).

    L'application induite b est BIJECTIVE de E/R_f (système des classes θ(x),
    x∈E) sur f⟨E⟩, au niveau des valeurs : conjonction de l'injectivité
    (`b_injective_via_pont`, hyp {pont}) et de la surjectivité
    (`b_surjective_valeurs`, hyps {pont, Hf1}).  Hypothèses {pont, Hf1}.
    La forme graphe est_bijection_de + Eq(E/R_f, f⟨E⟩) : REPORTÉE (module)."""
    inj = b_injective_via_pont(f, b, e, x, y, w)
    surj = b_surjective_valeurs(f, b, e, z, x, w)
    return conjonction_intro(inj, surj)


__all__ = ["b_surjective_valeurs", "b_surjective_valeurs_cible",
           "b_bijective_valeurs"]
