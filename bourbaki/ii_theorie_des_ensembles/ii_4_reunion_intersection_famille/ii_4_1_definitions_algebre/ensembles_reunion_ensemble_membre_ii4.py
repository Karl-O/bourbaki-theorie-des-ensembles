"""§R n°67 — « 𝔉 a un plus petit (resp. plus grand) élément ⇔ ⋂𝔉 (resp. ⋃𝔉) ∈ 𝔉 ».

CONSOMMATEUR de la famille identité déchargée (ensembles_famille_identite_ii4.py) :
c'est le premier résultat du livre qui EXPLOITE ⋂𝔊/⋃𝔊 pour un ENSEMBLE 𝔊 de parties,
et non plus seulement une famille indexée.

Énoncé du livre, VÉRIFIÉ AU PDF (Résumé, E.R.27 = PDF p.330, L.34-39) : « Dans
l'ensemble des parties 𝔓(E) d'un ensemble quelconque, ordonné par la relation
d'inclusion, pour qu'une partie 𝔉 (ensemble de parties de E) possède un plus petit
élément, il faut et il suffit que l'intersection des ensembles de 𝔉 appartienne à
𝔉, dont cette intersection est alors le plus petit élément ; de même, pour que 𝔉
ait un plus grand élément, il faut et il suffit que la réunion des ensembles de 𝔉
appartienne à 𝔉, dont cette réunion est alors le plus grand élément. »  Les DEUX
moitiés (⋂ et ⋃) sont formalisées ici.

FIDÉLITÉ — formulation au niveau des INCLUSIONS PURES.  Le livre parle de « plus
petit élément pour ⊂ », donc de l'ordre-OBJET (le graphe d'inclusion sur 𝔓(E)).
Cet ordre-objet n'existe pas encore comme terme au §II.4 (plus_petit_element(G,A,m)
vit en III.1 et exige un graphe d'ordre G).  On formalise donc la relation « être le
plus petit » *directement par les inclusions*, ce qui est sa DÉFINITION dépliée :

    a_plus_petit_pour_inclusion(𝔉) := (∃A)( A∈𝔉  et  (∀B)(B∈𝔉 ⇒ A⊂B) )

L'hypothèse « 𝔉 ⊂ 𝔓(E) » du livre n'est PAS nécessaire à la démonstration (elle ne
sert dans le livre qu'à garantir que ⋂𝔉 a un sens comme partie de E) : on ne
l'ajoute pas, l'énoncé formalisé est donc strictement PLUS FORT que celui du livre.

Résultats certifiés :
  · plus_petit_est_inter        {PONT,𝔉≠∅} ⊢ (A∈𝔉 et (∀B)(B∈𝔉⇒A⊂B)) ⇒ A = ⋂𝔉
  · plus_petit_ssi_inter_membre {PONT,𝔉≠∅} ⊢ (∃A)(A∈𝔉 et (∀B)(B∈𝔉⇒A⊂B)) ⇔ (⋂𝔉∈𝔉)
  · plus_grand_est_reunion      {PONT}      ⊢ (A∈𝔉 et (∀B)(B∈𝔉⇒B⊂A)) ⇒ A = ⋃𝔉
  · plus_grand_ssi_reunion_membre {PONT}    ⊢ (∃A)(A∈𝔉 et (∀B)(B∈𝔉⇒B⊂A)) ⇔ (⋃𝔉∈𝔉)
(les lemmes *_est_* sont le « et alors c'est ⋂𝔉 / ⋃𝔉 » du livre, extraits comme
lemmes réutilisables.)  Le côté ⋃ ne requiert PAS 𝔉≠∅ : ⋃ est inconditionnelle
chez Bourbaki (Déf. 1), seule ⋂ exige I≠∅ (Déf. 2).

Hypothèses honnêtes (héritées de ensembles_famille_identite_ii4.py, aucune neuve) :
  · PONT(𝔉) = (∀X)(X∈𝔉 ⇒ valeur_famille(G,X) = valeur(G,X))  — pont notationnel
    fam↔valeur sur la famille identité concrète G := graphe_terme(𝔉, ι, ι).
    Mur structurel documenté : valeur_famille est un symbole libre qu'aucun des
    22 axiomes ne relie à valeur.
  · 𝔉≠∅ — fidélité de la Déf. 2 (E II.22 : ⋂ exige I≠∅).

Démonstration (côté ⋂ ; le côté ⋃ est exactement dual).
  (⇐) A := ⋂𝔉 convient : ⋂𝔉∈𝔉 est l'hypothèse, et (∀B)(B∈𝔉 ⇒ ⋂𝔉⊂B) est la
      ∀-clôture de inter_incluse_partie_parties ; on conclut par C-S5 (∃-intro).
  (⇒) Soit A un tel plus petit élément.  ⋂𝔉⊂A car A∈𝔉 ; et A⊂⋂𝔉 car pour z∈A et
      i∈𝔉 on a A⊂i donc z∈i, d'où z∈⋂𝔉 par membre_inter_parties.  Double inclusion
      + A1 (extensionnalité) donne A=⋂𝔉, puis S6 transporte A∈𝔉 en ⋂𝔉∈𝔉.
      ∃-élimination sur le liant EXOTIQUE « app ».
  Côté ⋃ : le sens (⇒) passe par une ∃-élimination SUPPLÉMENTAIRE (le témoin i de
  z∈⋃𝔉 fourni par membre_reunion_parties), sur le liant « i » de cet énoncé.

theorie_ensembles() == 22 (asserté en test) ; rien postulé.  Liants exotiques :
« app » (le plus petit/grand élément), « bpp » (le ∀ interne), « wpp » (le trou de
S6) ; « z » et « i » sont IMPOSÉS (binder par défaut de outil_formule.inclus, et
binder des énoncés membre_inter_parties/membre_reunion_parties) — pas des choix.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, et, non, impl, appartient, existe, pourtout, equiv, inclus)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_theoremes import (
    extensionnalite_appliquee)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege import syllogisme
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, instancie)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import (
    existe_elimination)
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_1_definitions_algebre.ensembles_famille_identite_ii4 import (
    IOTA, famille_identite, pont_fam_valeur, membre_inter_parties,
    inter_incluse_partie_parties, membre_reunion_parties,
    partie_incluse_reunion_parties)

APP = "app"        # liant EXOTIQUE : le « plus petit élément » existentiel
BPP = "bpp"        # liant EXOTIQUE : le ∀ interne (« pour tout B de 𝔉 »)
WPP = "wpp"        # liant EXOTIQUE : le trou de S6 (Leibniz)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def inter_parties(u="F", iota=IOTA):
    """⋂𝔉 — intersection de l'ENSEMBLE de parties 𝔉 (via sa famille identité G)."""
    return E.inter_famille(famille_identite(u, iota), _t(u))


# ── La relation « 𝔉 a un plus petit élément pour ⊂ », dépliée ────────────────
# @livre Ch.R §2.5 Prop.67 | E.R.27 L.34-37 | PDF p.330  (plus petit élément d'un ensemble de parties, pour ⊂)
def a_plus_petit_pour_inclusion(u="F", a=APP, b=BPP):
    """« 𝔉 a un plus petit élément pour ⊂ » := (∃A)(A∈𝔉 et (∀B)(B∈𝔉 ⇒ A⊂B))."""
    vu = _t(u)
    return existe(a, _corps_plus_petit(var(a), vu, b))


def _corps_plus_petit(ta, vu, b=BPP):
    """A∈𝔉 et (∀B)(B∈𝔉 ⇒ A⊂B)   — A = TERME quelconque (le corps de l'∃)."""
    return et(appartient(ta, vu),
              pourtout(b, impl(appartient(var(b), vu), inclus(ta, var(b)))))


# ── Lemme : un plus petit élément EST ⋂𝔉 ─────────────────────────────────────
def enonce_plus_petit_est_inter(u="F", iota=IOTA, a=APP, b=BPP):
    vu, va = _t(u), var(a)
    return impl(_corps_plus_petit(va, vu, b), egal(va, inter_parties(u, iota)))


# @livre Ch.R §2.5 Prop.67 | E.R.27 L.36-37 | PDF p.330  (« dont cette intersection est alors le plus petit élément »)
def plus_petit_est_inter(u="F", iota=IOTA, a=APP, b=BPP):
    """{PONT(𝔉), 𝔉≠∅} ⊢ (A∈𝔉 et (∀B)(B∈𝔉⇒A⊂B)) ⇒ A = ⋂𝔉.

    Double inclusion + axiome A1 (extensionnalité).  « z » est le liant imposé par
    outil_formule.inclus, « i » celui de l'énoncé de membre_inter_parties."""
    vu, va = _t(u), var(a)
    INT = inter_parties(u, iota)
    vz, vi = var("z"), var("i")

    hbody = N.assume(_corps_plus_petit(va, vu, b))
    hA = conjonction_elim_gauche(hbody)                      # A∈𝔉
    hall = conjonction_elim_droite(hbody)                    # (∀B)(B∈𝔉 ⇒ A⊂B)

    # (i) ⋂𝔉 ⊂ A   — A est un élément de 𝔉
    inc_int_a = N.modus_ponens(hA, inter_incluse_partie_parties(u, a, iota))

    # (ii) A ⊂ ⋂𝔉  — A est minorant : z∈A ⇒ (∀i∈𝔉) z∈i ⇒ z∈⋂𝔉
    hz = N.assume(appartient(vz, va))                        # z∈A
    hi = N.assume(appartient(vi, vu))                        # i∈𝔉
    incl_a_i = N.modus_ponens(hi, instancie(hall, vi))       # A ⊂ i
    z_in_i = N.modus_ponens(hz, instancie(incl_a_i, vz))     # z∈i
    tous_i = N.generalisation("i", N.loi_deduction(appartient(vi, vu), z_in_i))
    z_in_int = N.modus_ponens(                               # z ∈ ⋂𝔉
        tous_i, equivalence_arriere(membre_inter_parties(u, "z", iota)))
    inc_a_int = N.generalisation("z", N.loi_deduction(appartient(vz, va), z_in_int))
    assert inc_a_int.conclusion == inclus(va, INT), \
        "plus_petit_est_inter : (ii) conclusion ≠ (A ⊂ ⋂𝔉)"

    # (iii) A1 : (A⊂⋂𝔉 et ⋂𝔉⊂A) ⇒ A=⋂𝔉
    eq = N.modus_ponens(conjonction_intro(inc_a_int, inc_int_a),
                        extensionnalite_appliquee(va, INT))
    res = N.loi_deduction(_corps_plus_petit(va, vu, b), eq)
    assert res.conclusion == enonce_plus_petit_est_inter(u, iota, a, b), \
        "plus_petit_est_inter : conclusion ≠ énoncé attendu"
    assert res.hypotheses == frozenset({pont_fam_valeur(u, iota),
                                        non(egal(_t(u), E.VIDE))}), \
        "plus_petit_est_inter : hypothèses ≠ {PONT, 𝔉≠∅}"
    return res


# ── n°67 : équivalence ────────────────────────────────────────────────────────
def enonce_plus_petit_ssi_inter_membre(u="F", iota=IOTA, a=APP, b=BPP):
    vu = _t(u)
    return equiv(a_plus_petit_pour_inclusion(u, a, b),
                 appartient(inter_parties(u, iota), vu))


# @livre Ch.R §2.5 Prop.67 | E.R.27 L.34-37 | PDF p.330  (𝔉 a un plus petit élément pour ⊂ ⇔ ⋂𝔉 ∈ 𝔉)
def plus_petit_ssi_inter_membre(u="F", iota=IOTA, a=APP, b=BPP):
    """{PONT(𝔉), 𝔉≠∅} ⊢ (∃A)(A∈𝔉 et (∀B)(B∈𝔉⇒A⊂B))  ⇔  (⋂𝔉 ∈ 𝔉).

    (⇐) témoin A := ⋂𝔉 (C-S5) ;  (⇒) plus_petit_est_inter + S6, ∃-élimination."""
    vu, va = _t(u), var(a)
    INT = inter_parties(u, iota)
    corps = _corps_plus_petit(va, vu, b)

    # ── sens ⇒ : le plus petit élément vaut ⋂𝔉, donc ⋂𝔉 ∈ 𝔉 ────────────────
    hbody = N.assume(corps)
    hA = conjonction_elim_gauche(hbody)                      # A∈𝔉
    eq = N.modus_ponens(hbody, plus_petit_est_inter(u, iota, a, b))   # A = ⋂𝔉
    # S6 : (A=⋂𝔉) ⇒ ((A∈𝔉) ⇔ (⋂𝔉∈𝔉))
    leibniz = N.modus_ponens(eq, N.s6(va, INT, WPP, appartient(var(WPP), vu)))
    int_membre = N.modus_ponens(hA, equivalence_avant(leibniz))       # ⋂𝔉 ∈ 𝔉
    imp_fwd = existe_elimination(N.loi_deduction(corps, int_membre), a)

    # ── sens ⇐ : ⋂𝔉 est lui-même le plus petit élément ─────────────────────
    hm = N.assume(appartient(INT, vu))                       # ⋂𝔉 ∈ 𝔉
    gen_b = N.generalisation(b, inter_incluse_partie_parties(u, b, iota))
    temoin = conjonction_intro(hm, gen_b)                    # corps[A := ⋂𝔉]
    assert temoin.conclusion == _corps_plus_petit(INT, vu, b), \
        "plus_petit_ssi_inter_membre : témoin ≠ corps[A:=⋂𝔉] (substitution)"
    ex = N.modus_ponens(temoin, N.s5(corps, INT, a))         # (∃A) corps
    imp_bwd = N.loi_deduction(appartient(INT, vu), ex)

    res = conjonction_intro(imp_fwd, imp_bwd)
    assert res.conclusion == enonce_plus_petit_ssi_inter_membre(u, iota, a, b), \
        "plus_petit_ssi_inter_membre : conclusion ≠ énoncé attendu"
    assert res.hypotheses == frozenset({pont_fam_valeur(u, iota),
                                        non(egal(_t(u), E.VIDE))}), \
        "plus_petit_ssi_inter_membre : hypothèses ≠ {PONT, 𝔉≠∅}"
    return res

# ═════════════════════════ DUAL : plus GRAND élément et ⋃𝔉 ═══════════════════
def reunion_parties(u="F", iota=IOTA):
    """⋃𝔉 — réunion de l'ENSEMBLE de parties 𝔉 (via sa famille identité G)."""
    return E.reunion_famille(famille_identite(u, iota), _t(u))


def _corps_plus_grand(ta, vu, b=BPP):
    """A∈𝔉 et (∀B)(B∈𝔉 ⇒ B⊂A)   — A = TERME quelconque (corps de l'∃, dual)."""
    return et(appartient(ta, vu),
              pourtout(b, impl(appartient(var(b), vu), inclus(var(b), ta))))


# @livre Ch.R §2.5 Prop.67 | E.R.27 L.37-39 | PDF p.330  (plus grand élément d'un ensemble de parties, pour ⊂)
def a_plus_grand_pour_inclusion(u="F", a=APP, b=BPP):
    """« 𝔉 a un plus grand élément pour ⊂ » := (∃A)(A∈𝔉 et (∀B)(B∈𝔉 ⇒ B⊂A))."""
    return existe(a, _corps_plus_grand(var(a), _t(u), b))


def enonce_plus_grand_est_reunion(u="F", iota=IOTA, a=APP, b=BPP):
    vu, va = _t(u), var(a)
    return impl(_corps_plus_grand(va, vu, b), egal(va, reunion_parties(u, iota)))


# @livre Ch.R §2.5 Prop.67 | E.R.27 L.38-39 | PDF p.330  (« dont cette réunion est alors le plus grand élément »)
def plus_grand_est_reunion(u="F", iota=IOTA, a=APP, b=BPP):
    """{PONT(𝔉)} ⊢ (A∈𝔉 et (∀B)(B∈𝔉⇒B⊂A)) ⇒ A = ⋃𝔉.   (pas besoin de 𝔉≠∅.)

    Dual de plus_petit_est_inter, avec une ∃-élimination de plus : le témoin i
    donné par membre_reunion_parties (liant « i », imposé par cet énoncé)."""
    vu, va = _t(u), var(a)
    REU = reunion_parties(u, iota)
    vz, vi = var("z"), var("i")

    hbody = N.assume(_corps_plus_grand(va, vu, b))
    hA = conjonction_elim_gauche(hbody)                      # A∈𝔉
    hall = conjonction_elim_droite(hbody)                    # (∀B)(B∈𝔉 ⇒ B⊂A)

    # (i) A ⊂ ⋃𝔉   — A est un élément de 𝔉
    inc_a_reu = N.modus_ponens(hA, partie_incluse_reunion_parties(u, a, iota))

    # (ii) ⋃𝔉 ⊂ A  — A majore : z∈⋃𝔉 donne un i∈𝔉 avec z∈i, et i⊂A
    interne = et(appartient(vi, vu), appartient(vz, vi))     # i∈𝔉 et z∈i
    hin = N.assume(interne)
    incl_i_a = N.modus_ponens(conjonction_elim_gauche(hin),
                              instancie(hall, vi))           # i ⊂ A
    z_in_a = N.modus_ponens(conjonction_elim_droite(hin),
                            instancie(incl_i_a, vz))         # z∈A
    ex_imp = existe_elimination(N.loi_deduction(interne, z_in_a), "i")
    inc_reu_a = N.generalisation("z", syllogisme(
        equivalence_avant(membre_reunion_parties(u, "z", iota)), ex_imp))
    assert inc_reu_a.conclusion == inclus(REU, va), \
        "plus_grand_est_reunion : (ii) conclusion ≠ (⋃𝔉 ⊂ A)"

    eq = N.modus_ponens(conjonction_intro(inc_a_reu, inc_reu_a),
                        extensionnalite_appliquee(va, REU))  # A = ⋃𝔉
    res = N.loi_deduction(_corps_plus_grand(va, vu, b), eq)
    assert res.conclusion == enonce_plus_grand_est_reunion(u, iota, a, b), \
        "plus_grand_est_reunion : conclusion ≠ énoncé attendu"
    assert res.hypotheses == frozenset({pont_fam_valeur(u, iota)}), \
        "plus_grand_est_reunion : hypothèses ≠ {PONT}"
    return res


def enonce_plus_grand_ssi_reunion_membre(u="F", iota=IOTA, a=APP, b=BPP):
    return equiv(a_plus_grand_pour_inclusion(u, a, b),
                 appartient(reunion_parties(u, iota), _t(u)))


# @livre Ch.R §2.5 Prop.67 | E.R.27 L.37-39 | PDF p.330  (𝔉 a un plus grand élément pour ⊂ ⇔ ⋃𝔉 ∈ 𝔉)
def plus_grand_ssi_reunion_membre(u="F", iota=IOTA, a=APP, b=BPP):
    """{PONT(𝔉)} ⊢ (∃A)(A∈𝔉 et (∀B)(B∈𝔉⇒B⊂A))  ⇔  (⋃𝔉 ∈ 𝔉)."""
    vu, va = _t(u), var(a)
    REU = reunion_parties(u, iota)
    corps = _corps_plus_grand(va, vu, b)

    # ── sens ⇒ ────────────────────────────────────────────────────────────────
    hbody = N.assume(corps)
    hA = conjonction_elim_gauche(hbody)
    eq = N.modus_ponens(hbody, plus_grand_est_reunion(u, iota, a, b))   # A = ⋃𝔉
    leibniz = N.modus_ponens(eq, N.s6(va, REU, WPP, appartient(var(WPP), vu)))
    reu_membre = N.modus_ponens(hA, equivalence_avant(leibniz))         # ⋃𝔉 ∈ 𝔉
    imp_fwd = existe_elimination(N.loi_deduction(corps, reu_membre), a)

    # ── sens ⇐ : ⋃𝔉 est lui-même le plus grand élément ───────────────────────
    hm = N.assume(appartient(REU, vu))
    gen_b = N.generalisation(b, partie_incluse_reunion_parties(u, b, iota))
    temoin = conjonction_intro(hm, gen_b)
    assert temoin.conclusion == _corps_plus_grand(REU, vu, b), \
        "plus_grand_ssi_reunion_membre : témoin ≠ corps[A:=⋃𝔉] (substitution)"
    ex = N.modus_ponens(temoin, N.s5(corps, REU, a))
    imp_bwd = N.loi_deduction(appartient(REU, vu), ex)

    res = conjonction_intro(imp_fwd, imp_bwd)
    assert res.conclusion == enonce_plus_grand_ssi_reunion_membre(u, iota, a, b), \
        "plus_grand_ssi_reunion_membre : conclusion ≠ énoncé attendu"
    assert res.hypotheses == frozenset({pont_fam_valeur(u, iota)}), \
        "plus_grand_ssi_reunion_membre : hypothèses ≠ {PONT}"
    return res


__all__ = ["APP", "BPP", "WPP", "inter_parties", "reunion_parties",
           "a_plus_petit_pour_inclusion", "a_plus_grand_pour_inclusion",
           "enonce_plus_petit_est_inter", "plus_petit_est_inter",
           "enonce_plus_petit_ssi_inter_membre", "plus_petit_ssi_inter_membre",
           "enonce_plus_grand_est_reunion", "plus_grand_est_reunion",
           "enonce_plus_grand_ssi_reunion_membre", "plus_grand_ssi_reunion_membre"]
