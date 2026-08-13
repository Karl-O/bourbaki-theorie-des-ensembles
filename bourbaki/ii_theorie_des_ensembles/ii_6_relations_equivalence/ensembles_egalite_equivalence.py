"""Résumé §5, EXEMPLES de relations d'équivalence : l'ÉGALITÉ (item 2) et la
RELATION D'UNE PARTITION (item 1).

I. Bourbaki (Résumé, E.R.23 item 2) : « la relation x = y est une relation
d'équivalence » — et l'application canonique associée x ↦ {x} envoie E sur
l'ensemble des classes (les singletons).

DÉRIVÉ :  ⊢ est_relation_equivalence(=)   (prédicat E.II.6.1 du dépôt :
symétrie ET transitivité), à partir des Théorèmes 2 et 3 de la théorie
égalitaire (E I.40, `symetrie`/`transitivite`, CLOS), par généralisation puis
conjonction.  THÉORÈME CLOS, 0 hypothèse ; theorie_ensembles = 22.

L'APPLICATION CANONIQUE x ↦ {x} : le terme-classe de x pour l'égalité est le
singleton E.singleton(x) (déposé) ; la bijection E ≅ (ensemble des singletons)
= la décomposition canonique de l'identité — volet quotient listé à part dans
CAMPAGNE_DEMOS (T3, quotients du Résumé §5).

II. Bourbaki (Résumé, E.R.22 item 1, PDF p.325, vérifié en PNG) : « Soit
(A_ι)_{ι∈I} une partition d'un ensemble E ; la relation R{x,y} entre deux
éléments x, y de E  “il existe ι∈I tel que x∈A_ι et y∈A_ι”  satisfait aux
conditions suivantes : a) R{x,x} est une identité (réflexivité) ; b) R{x,y}
et R{y,x} sont équivalentes (symétrie) [; c) transitivité]. »

DÉRIVÉ (`relation_partition` = la relation verbatim, liant ∃ « i ») :
  • `relation_partition_symetrique`      ⊢ est_symetrique(R)   (b ; CLOS, 0 hyp) ;
  • `relation_partition_reflexive_dans`  {H_rec, H_parties} ⊢ est_reflexive_dans(R, E)
        (a, forme E.II.6.1 (∀x)(R{x,x} ⇔ x∈E) ; clos modulo 2 hyps honnêtes) :
        H_rec     = (∀x)(x∈E ⇒ (∃i)(i∈I et x∈A_i))   [recouvrement AU NIVEAU DES POINTS]
        H_parties = (∀i)(i∈I ⇒ A_i ⊂ E)               [famille de PARTIES de E]
  • `relation_partition_reflexive_symetrique` — conjonction a) et b).

NB `est_partition`/`est_recouvrement` EXISTENT (`ensembles_abrege.py`) — toute
checklist « pas de est_partition » est STALE.  Le pont est_recouvrement (E ⊂ ⋃X_ι)
⇒ H_rec exige la caractérisation d'appartenance z∈⋃_{ι∈I}X_ι ⇔ (∃ι)(ι∈I et z∈X_ι),
ABSENTE (reunion_famille est un app opaque, chantier ⋃-famille) : H_rec est la
lecture ponctuelle honnête, jamais postulée dans le noyau.  RESTE (reporté) :
c) la transitivité — exige famille_disjointe + cas ι=κ / ι≠κ (¬¬-élim).
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, impl, appartient, existe, pourtout, inclus, subst_f)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import et as et_f
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege import (
    syllogisme)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, instancie)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import (
    existe_elimination, alpha_existe)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
    symetrie, composer_egalites)
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E


def egalite_equivalence_enonce(x: str = "x", y: str = "y", z: str = "z"):
    """L'énoncé-cible :  est_relation_equivalence(=)  (symétrie ET transitivité,
    déf. E.II.6.1, avec = comme relation R{x,y})."""
    return E.est_relation_equivalence(egal, x, y, z)


# @livre Ch.R §5 Prop.- | E.R.23 item 2 | PDF p.326  (« x=y est une relation d'équivalence » — DÉRIVÉ)
# @livre Ch.R §5 Demo.- | E.R.23 item 2 | PDF p.326  (démo : Théorèmes 2-3 égalitaires E I.40 + généralisation + conjonction)
def egalite_est_equivalence(x: str = "x", y: str = "y", z: str = "z"):
    """🎯 ⊢ est_relation_equivalence(=).   (THÉORÈME CLOS, 0 hyp.)

    • symétrie   : Théorème 2 (E I.40)  ⊢ (x=y) ⇒ (y=x), généralisé en
                   (∀x)(∀y)((x=y) ⇒ (y=x)) = est_symetrique(=) ;
    • transitivité : Théorème 3 (E I.40)  ⊢ ((x=y) et (y=z)) ⇒ (x=z),
                   généralisé en est_transitive(=) ;
    • conjonction des deux = est_relation_equivalence(=)."""
    vx, vy, vz = var(x), var(y), var(z)

    sym = symetrie(vx, vy)                          # ⊢ (x=y) ⇒ (y=x)   CLOS
    sym_gen = N.generalisation(x, N.generalisation(y, sym))
    assert sym_gen.conclusion == E.est_symetrique(egal, x, y), \
        "symétrie généralisée ≠ est_symetrique(=)"

    # transitivité en forme conjonctive : on décharge nous-mêmes
    hconj = N.assume(et_f(egal(vx, vy), egal(vy, vz)))
    xz = composer_egalites(conjonction_elim_gauche(hconj),
                           conjonction_elim_droite(hconj))     # {h} ⊢ x=z
    trans = N.loi_deduction(et_f(egal(vx, vy), egal(vy, vz)), xz)
    trans_gen = N.generalisation(x, N.generalisation(y, N.generalisation(z, trans)))
    assert trans_gen.conclusion == E.est_transitive(egal, x, y, z), \
        "transitivité généralisée ≠ est_transitive(=)"

    res = conjonction_intro(sym_gen, trans_gen)
    assert res.conclusion == egalite_equivalence_enonce(x, y, z), \
        "égalité-équivalence : conclusion ≠ énoncé"
    assert not res.hypotheses, "égalité-équivalence : hypothèses non déchargées"
    return res                                      # CLOS, 0 hyp


def classe_de_x_pour_egalite(x: str = "x"):
    """Le terme-classe de x pour l'égalité : {x} (l'application canonique
    x ↦ {x} du Résumé, au niveau terme — le singleton déposé du chap. II)."""
    return E.singleton(var(x))


# ════════════════════════════════════════════════════════════════════════════
# II.  La relation d'une partition  (E.R.22 item 1)
# ════════════════════════════════════════════════════════════════════════════
def _tv(t):
    return t if isinstance(t, Terme) else var(t)


# @livre Ch.R §5 Def.- | E.R.22 item 1 (relation « il existe ι∈I tel que x∈A_ι et y∈A_ι ») | PDF p.325
def relation_partition(f, i_set, i: str = "i"):
    """R{x,y} := (∃i)( i∈I  et  (x∈A_i et y∈A_i) )   (E.R.22 item 1, verbatim).

    f : la famille (A_ι)_{ι∈I} (fonction ι ↦ A_ι, `valeur_famille`) ; i_set : I.
    Renvoie une fonction (Terme, Terme) → Formule (liant ∃ « i », comme
    `est_partition`/`plus_fin` d'ensembles_abrege)."""
    vf, viset = _tv(f), _tv(i_set)

    def rel(a, b):
        vi = var(i)
        Ai = E.valeur_famille(vf, vi)
        return existe(i, et_f(appartient(vi, viset),
                              et_f(appartient(a, Ai), appartient(b, Ai))))
    return rel


def recouvrement_points(f, i_set, e, x: str = "x", i: str = "i"):
    """H_rec := (∀x)( x∈E ⇒ (∃i)(i∈I et x∈A_i) )   (recouvrement AU NIVEAU DES POINTS).

    Lecture ponctuelle d'`est_recouvrement` (E ⊂ ⋃_{ι∈I}A_ι, Déf. 5 E.II.4.6) : le
    maillon z∈⋃X_ι ⇔ (∃ι)(…) est ABSENT (⋃-famille opaque), d'où cette hypothèse
    honnête — c'est exactement ce que le ⊂ SIGNIFIE, points déroulés."""
    vf, viset, ve = _tv(f), _tv(i_set), _tv(e)
    vx, vi = var(x), var(i)
    return pourtout(x, impl(appartient(vx, ve),
                            existe(i, et_f(appartient(vi, viset),
                                           appartient(vx, E.valeur_famille(vf, vi))))))


def parties_points(f, i_set, e, i: str = "i"):
    """H_parties := (∀i)( i∈I ⇒ A_i ⊂ E )   (les A_ι sont des PARTIES de E).

    L'hypothèse de cadre de E.R.22 item 1 (« (A_ι)_{ι∈I} une partition d'UN
    ENSEMBLE E ») ; ⊂ est l'inclus du dépôt ((∀z)(z∈A_i ⇒ z∈E))."""
    vf, viset, ve = _tv(f), _tv(i_set), _tv(e)
    vi = var(i)
    return pourtout(i, impl(appartient(vi, viset),
                            inclus(E.valeur_famille(vf, vi), ve)))


# @livre Ch.R §5 Prop.- | E.R.22 item 1 b (symétrie de la relation R) | PDF p.325
def relation_partition_symetrique(f="f", i_set="I", x: str = "x", y: str = "y"):
    """🎯 ⊢ est_symetrique(R)   (E.R.22 item 1 b ; CLOS, 0 hypothèse).

    Sous le corps existentiel (point exotique « ipr ») : i∈I, x∈A_i, y∈A_i ; on
    échange les deux appartenances et on ré-introduit le ∃ au liant « i » du
    livre (témoin ipr), puis α-pont (∃i ⇔ ∃ipr) et généralisation x, y."""
    vf, viset = _tv(f), _tv(i_set)
    rel = relation_partition(vf, viset)
    vx, vy, vi = var(x), var(y), var("ipr")
    Ai = E.valeur_famille(vf, vi)

    corps_xy = et_f(appartient(var("i"), viset),
                    et_f(appartient(vx, E.valeur_famille(vf, var("i"))),
                         appartient(vy, E.valeur_famille(vf, var("i")))))
    corps_yx = et_f(appartient(var("i"), viset),
                    et_f(appartient(vy, E.valeur_famille(vf, var("i"))),
                         appartient(vx, E.valeur_famille(vf, var("i")))))

    B = et_f(appartient(vi, viset), et_f(appartient(vx, Ai), appartient(vy, Ai)))
    h = N.assume(B)
    hi = conjonction_elim_gauche(h)                          # ipr∈I
    hxy = conjonction_elim_droite(h)                         # x∈A_ipr et y∈A_ipr
    but = conjonction_intro(hi, conjonction_intro(conjonction_elim_droite(hxy),
                                                  conjonction_elim_gauche(hxy)))
    assert but.conclusion == subst_f(vi, "i", corps_yx), "témoin ≠ (ipr|i)corps"
    Ryx = N.modus_ponens(but, N.s5(corps_yx, vi, "i"))       # R{y,x}   [B]
    assert Ryx.conclusion == rel(vy, vx), "∃-intro : cible R{y,x}"

    imp = existe_elimination(N.loi_deduction(B, Ryx), "ipr")  # (∃ipr)B ⇒ R{y,x}
    alpha = alpha_existe("i", "ipr", corps_xy)                # R{x,y} ⇔ (∃ipr)B
    res0 = syllogisme(equivalence_avant(alpha), imp)          # R{x,y} ⇒ R{y,x}
    res = N.generalisation(x, N.generalisation(y, res0))
    assert res.conclusion == E.est_symetrique(rel, x, y), "cible est_symetrique"
    assert res.est_clos, "symétrie : non close"
    return res


# @livre Ch.R §5 Prop.- | E.R.22 item 1 a (réflexivité de la relation R) | PDF p.325
def relation_partition_reflexive_dans(f="f", i_set="I", e="E", x: str = "x"):
    """🎯 {H_rec, H_parties} ⊢ est_reflexive_dans(R, E)   (E.R.22 item 1 a ;
    forme E.II.6.1 : (∀x)(R{x,x} ⇔ x∈E) ; clos modulo les 2 hyps honnêtes).

    ⇐ (x∈E ⇒ R{x,x}) : H_rec donne (∃i)(i∈I et x∈A_i) ; sous le corps (point
      exotique ipr) on double x∈A_ipr et on ré-introduit le ∃ au liant « i ».
    ⇒ (R{x,x} ⇒ x∈E) : sous le corps, H_parties (instanciée en ipr) donne
      A_ipr ⊂ E, dont l'instance en x conclut x∈E.
    Hypothèses restantes EXACTEMENT {H_rec, H_parties} (docstring module)."""
    vf, viset, ve = _tv(f), _tv(i_set), _tv(e)
    rel = relation_partition(vf, viset)
    vx, vi = var(x), var("ipr")
    Ai = E.valeur_famille(vf, vi)

    corps_rec = et_f(appartient(var("i"), viset),
                     appartient(vx, E.valeur_famille(vf, var("i"))))
    corps_xx = et_f(appartient(var("i"), viset),
                    et_f(appartient(vx, E.valeur_famille(vf, var("i"))),
                         appartient(vx, E.valeur_famille(vf, var("i")))))

    h_rec = N.assume(recouvrement_points(vf, viset, ve, x=x, i="i"))
    h_par = N.assume(parties_points(vf, viset, ve, i="i"))

    # ── ⇐ : x∈E ⇒ R{x,x} ────────────────────────────────────────────────────
    hx = N.assume(appartient(vx, ve))
    ex_rec = N.modus_ponens(hx, instancie(h_rec, vx))        # (∃i)(i∈I et x∈A_i)
    B0 = et_f(appartient(vi, viset), appartient(vx, Ai))     # corps au point ipr
    h0 = N.assume(B0)
    but = conjonction_intro(conjonction_elim_gauche(h0),
                            conjonction_intro(conjonction_elim_droite(h0),
                                              conjonction_elim_droite(h0)))
    assert but.conclusion == subst_f(vi, "i", corps_xx), "témoin ⇐ ≠ (ipr|i)corps"
    Rxx = N.modus_ponens(but, N.s5(corps_xx, vi, "i"))       # R{x,x}   [B0]
    imp0 = existe_elimination(N.loi_deduction(B0, Rxx), "ipr")
    alpha_rec = alpha_existe("i", "ipr", corps_rec)          # (∃i) ⇔ (∃ipr)
    Rxx_de_E = N.modus_ponens(N.modus_ponens(ex_rec, equivalence_avant(alpha_rec)),
                              imp0)                          # R{x,x}   [H_rec, x∈E]
    bwd = N.loi_deduction(appartient(vx, ve), Rxx_de_E)      # x∈E ⇒ R{x,x}   [H_rec]

    # ── ⇒ : R{x,x} ⇒ x∈E ────────────────────────────────────────────────────
    B1 = et_f(appartient(vi, viset), et_f(appartient(vx, Ai), appartient(vx, Ai)))
    h1 = N.assume(B1)
    hi = conjonction_elim_gauche(h1)                         # ipr∈I
    hxA = conjonction_elim_gauche(conjonction_elim_droite(h1))   # x∈A_ipr
    incl = N.modus_ponens(hi, instancie(h_par, vi))          # A_ipr ⊂ E
    xE = N.modus_ponens(hxA, instancie(incl, vx))            # x∈E   [H_parties, B1]
    imp1 = existe_elimination(N.loi_deduction(B1, xE), "ipr")    # (∃ipr)B1 ⇒ x∈E
    alpha_xx = alpha_existe("i", "ipr", corps_xx)
    fwd = syllogisme(equivalence_avant(alpha_xx), imp1)      # R{x,x} ⇒ x∈E   [H_parties]

    eqv = conjonction_intro(fwd, bwd)                        # R{x,x} ⇔ x∈E
    res = N.generalisation(x, eqv)
    assert res.conclusion == E.est_reflexive_dans(rel, ve, x), "cible est_reflexive_dans"
    assert res.hypotheses == frozenset({recouvrement_points(vf, viset, ve, x=x, i="i"),
                                        parties_points(vf, viset, ve, i="i")}), \
        "hypothèses ≠ {H_rec, H_parties}"
    return res


# @livre Ch.R §5 Prop.- | E.R.22 item 1 a-b (R réflexive et symétrique) | PDF p.325
def relation_partition_reflexive_symetrique(f="f", i_set="I", e="E",
                                            x: str = "x", y: str = "y"):
    """{H_rec, H_parties} ⊢ est_reflexive_dans(R, E)  et  est_symetrique(R)
    (conditions a et b de E.R.22 item 1, dans l'ordre du livre ; clos mod. hyps).

    RESTE (reporté, docstring module) : c) la transitivité (famille_disjointe)."""
    refl = relation_partition_reflexive_dans(f, i_set, e, x)
    sym = relation_partition_symetrique(f, i_set, x, y)
    return conjonction_intro(refl, sym)


__all__ = ["egalite_equivalence_enonce", "egalite_est_equivalence",
           "classe_de_x_pour_egalite",
           "relation_partition", "recouvrement_points", "parties_points",
           "relation_partition_symetrique", "relation_partition_reflexive_dans",
           "relation_partition_reflexive_symetrique"]
