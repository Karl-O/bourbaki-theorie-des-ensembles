"""§II.6.4 — Parties saturées : l'image réciproque p⁻¹⟨B⟩ est saturée pour R.

Module NEUF (vague II — saturation).  On NE MODIFIE AUCUN fichier existant ;
on RECOLLE des lemmes DÉJÀ CLOS (modulo hypothèses) et les axiomes de la théorie
des ensembles (theorie_ensembles() reste à 22 axiomes — AUCUN axiome neuf).

ÉNONCÉ (Bourbaki E.II.6.4).  Le saturé d'une partie A pour R est Ã = p⁻¹⟨p⟨A⟩⟩ ;
c'est la plus petite partie saturée contenant A.  Le point clé est que TOUTE image
réciproque p⁻¹⟨B⟩ d'une partie B ⊂ E/R par l'application canonique p : E → E/R est
saturée pour R — d'où Ã = p⁻¹⟨B⟩ avec B = p⟨A⟩ l'est en particulier.

Ce module établit la FORME FIDÈLE FAIBLE-RISQUE, sur l'écriture Ã = p⁻¹⟨B⟩ d'une
partie B QUELCONQUE du quotient (image réciproque PURE — on NE déplie PAS p⟨A⟩) :

  `sature_partie_saturee`  {R sym, R trans, G relation dans E}
        ⊢ est_saturee( p⁻¹⟨B⟩, G )
        = (∀x)(∀y)( (x ∈ p⁻¹⟨B⟩  et  (x,y)∈G) ⇒ y ∈ p⁻¹⟨B⟩ ).

« Tout sur-ensemble image réciproque d'une partie du quotient est saturé. »  La
preuve est PUREMENT ENSEMBLISTE (relations d'équivalence + image réciproque) — aucun
Card profond.

STRATÉGIE (calquée sur `saturee_implique_classe_incluse` pour le squelette).
On déplie est_saturee(p⁻¹⟨B⟩,G) = est_compatible(t↦t∈p⁻¹⟨B⟩, rel_graphe G) et on
prouve le corps instancié en deux points x, y.  Sous (x∈p⁻¹⟨B⟩ et (x,y)∈G) :

  1. MEMBERSHIP image réciproque (mem_cform).  x∈p⁻¹⟨B⟩ ⇔ (∃c)(c∈B et (x,c)∈p) :
        membre_image_reciproque : x∈p⁻¹⟨B⟩ ⇔ (∃c)(c∈B et (c,x)∈p⁻¹) ; puis
        couple_reciproque réécrit (c,x)∈p⁻¹ en (x,c)∈p (α-renommage du témoin → « c »).
     On obtient un témoin c : c∈B et (x,c)∈p.
  2. TRANSPORT (x,c)∈p ⟹ (y,c)∈p, sous (x,y)∈G :
        • AXIOME_APPCANON (sens ⇒) : (x,c)∈p ⇒ (∃u)(u∈E et (x,c)=(u,Cl_R(u))) ;
          Proposition 1 (couple_egal_implique_composantes) ⇒ x=u et c=Cl_R(u),
          d'où c=Cl_R(x) (Leibniz) ;
        • relation_implique_classe_egale (mod {sym,trans}) : (x,y)∈G ⇒ Cl_R(x)=Cl_R(y),
          d'où c=Cl_R(y) ;
        • « G relation dans E » donne y∈E ; AXIOME_APPCANON (sens ⇐) avec le témoin
          u:=y et (y,c)=(y,Cl_R(y)) reconstruit (y,c)∈p.
  3. RETOUR membership : c∈B et (y,c)∈p ⇒ (∃c)(…) ⇒ y∈p⁻¹⟨B⟩ (mem_cform en y).
  4. loi_deduction (décharge x∈p⁻¹⟨B⟩ et (x,y)∈G), puis double généralisation.

La preuve interne universalise sur les points frais « s »,« t » (≠ témoin « x » de
AXIOME_IMAGE/AXIOME_APPCANON, ≠ « c » du témoin de valeur), puis `bridge_equiv`
α-transporte la conclusion sur la forme canonique est_saturee(…) (liants x, y).
SOUND : bridge_equiv est dérivé des seules primitives S5 / témoin-∃ / élimination.

HYPOTHÈSES HONNÊTES (load-bearing, exactement dans le séquent — rien postulé, aucune
tautologie, conclusion ∉ hypothèses) :
  • R symétrique, R transitive    — consommées par relation_implique_classe_egale ;
  • « G relation dans E » : (∀a)(∀b)((a,b)∈G ⇒ b∈E)   — donne y∈E, requis par le sens
    ⇐ de AXIOME_APPCANON (l'application canonique n'est définie que sur E).  C'est la
    propriété « R est une relation DANS E » (E.II.6.1), honnête pour une saturation.
Les « relations de valeur de p » sont ici PORTÉES par AXIOME_APPCANON (membership du
graphe de p) — aucune hypothèse de valeur supplémentaire n'est nécessaire.

g : graphe de R ; e = E (support) ; b = B (partie du quotient).  Liants : « s »,« t »
(points universels) ; « c » (témoin de valeur) ; « x » (témoin de AXIOME_IMAGE /
AXIOME_APPCANON) ; « z » (liant interne de relation_implique_classe_egale) ; « w »
(trou de congruence) ; « a »,« b » (liants de l'hypothèse « G relation dans E »).
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (
    Terme, var, egal, et, impl, appartient, pourtout)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, equivalence_transitivite,
    et_congruence_droite, instancie)
from bourbaki.logique.i_3_quantifies.tactiques_abrege_quantif import (
    congruence_existe, existe_elimination, alpha_existe)
from bourbaki.logique.i_4_egalitaires.tactiques_abrege_egalite import (
    symetrie, composer_egalites, congruence_terme)
from bourbaki.logique.i_3_quantifies.ensembles_alpha_bridge import bridge_equiv
from bourbaki.ensembles.familles.ii_4_reunion_intersection_familles.ii_4_image_famille.ensembles_image_algebre_binaire_ii4 import (
    membre_image_reciproque)
from bourbaki.ensembles.fonctions.ii_3_2_reciproque.ensembles_reciproque import (
    couple_reciproque)
from bourbaki.ensembles.ii_6_equivalence.ensembles_quotient_props_graphe import (
    relation_implique_classe_egale)
from bourbaki.ensembles.ii_2_couples_produit.ensembles_couples import (
    couple_egal_implique_composantes)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def relation_dans(g, e):
    """« G relation dans E » := (∀a)(∀b)((a,b)∈G ⇒ b∈E)  (E.II.6.1 ; pr₂G ⊂ E).

    Hypothèse honnête : les seconds membres de R sont dans E.  Donne y∈E à partir
    de (x,y)∈G, ce qu'exige le sens ⇐ de AXIOME_APPCANON (p défini sur E)."""
    vg, ve = _t(g), _t(e)
    va, vb = var("a"), var("b")
    return pourtout("a", pourtout("b",
        impl(appartient(E.couple(va, vb), vg), appartient(vb, ve))))


def cible_sature_partie_saturee(g="G", e="E", b="B"):
    """Cible Bourbaki : est_saturee( p⁻¹⟨B⟩, G )  (forme dépliée, liants x, y).

    p = application_canonique(g,e) ; p⁻¹⟨B⟩ = image(reciproque(p), B).  Renvoie la
    FORMULE attendue (∀x)(∀y)((x∈p⁻¹⟨B⟩ et (x,y)∈G) ⇒ y∈p⁻¹⟨B⟩)."""
    vg, ve, vb = _t(g), _t(e), _t(b)
    p = E.application_canonique(vg, ve)
    prB = E.image(E.reciproque(p), vb)
    return E.est_saturee(prB, vg, prB, x="x")


def _mem_cform(p, b, pt):
    """⊢ (pt ∈ p⁻¹⟨B⟩) ⇔ (∃c)(c∈B et (pt,c)∈p).

    membre_image_reciproque donne (∃x)(x∈B et (x,pt)∈p⁻¹) ; couple_reciproque
    réécrit (x,pt)∈p⁻¹ en (pt,x)∈p ; on α-renomme le témoin « x » → « c »
    (uniformité, ≠ témoin « x » de AXIOME_APPCANON utilisé par le transport)."""
    vb = _t(b)
    m = membre_image_reciproque(p, vb, pt)                 # ⇔ (∃x)(x∈B et (x,pt)∈p⁻¹)
    cr = couple_reciproque(p, "x", pt.nom)                 # (x,pt)∈p⁻¹ ⇔ (pt,x)∈p
    body_eq = et_congruence_droite(appartient(var("x"), vb), cr)
    m2 = equivalence_transitivite(m, congruence_existe(body_eq, "x"))   # ⇔ (∃x)(x∈B et (pt,x)∈p)
    ren = alpha_existe("x", "c",
                       et(appartient(var("x"), vb), appartient(E.couple(pt, var("x")), p)))
    return equivalence_transitivite(m2, ren)               # ⇔ (∃c)(c∈B et (pt,c)∈p)


# @livre Ch.II §6.4 Def.- | E II.43 L.27-29 | PDF p.94
def sature_partie_saturee(g="G", e="E", b="B"):
    """{R sym, R trans, G relation dans E} ⊢ est_saturee( p⁻¹⟨B⟩, G )
    (E.II.6.4 ; clos mod. hyp.).

    « Toute image réciproque p⁻¹⟨B⟩ d'une partie B du quotient E/R par l'application
    canonique p est saturée pour R » — d'où le saturé Ã = p⁻¹⟨p⟨A⟩⟩ est saturé (cas
    B = p⟨A⟩).  Forme fidèle faible-risque : B est une partie QUELCONQUE du quotient
    (on ne déplie pas p⟨A⟩).  Preuve : membership de l'image réciproque + transport
    du témoin de valeur via AXIOME_APPCANON et Cl_R(x)=Cl_R(y) (cf. en-tête du module).

    g : graphe de R ; e = E (support) ; b = B (partie du quotient).  Clos modulo
    {R symétrique, R transitive, G relation dans E}."""
    vg, ve, vb = _t(g), _t(e), _t(b)
    p = E.application_canonique(vg, ve)
    prB = E.image(E.reciproque(p), vb)
    vs, vt, vc, vw = var("s"), var("t"), var("c"), var("w")

    axac = N.axiome(E.theorie_ensembles(), E.AXIOME_APPCANON)

    def appcanon_membre(u, v):
        """⊢ (u,v)∈p ⇔ (∃x)(x∈E et (u,v)=(x,Cl_R(x)))  (instance de AXIOME_APPCANON)."""
        return instancie(instancie(instancie(axac, vg), ve), E.couple(u, v))

    # ── antécédent du corps : (s∈p⁻¹⟨B⟩ et (s,t)∈G) ──────────────────────────────
    antec = et(appartient(vs, prB), appartient(E.couple(vs, vt), vg))
    h_assoc = N.assume(antec)
    h_sin = conjonction_elim_gauche(h_assoc)               # s∈p⁻¹⟨B⟩
    h_st = conjonction_elim_droite(h_assoc)                # (s,t)∈G
    h_GE = N.assume(relation_dans(vg, ve))                 # (∀a)(∀b)((a,b)∈G ⇒ b∈E)

    # ── 1. membership : s∈p⁻¹⟨B⟩ ⇒ (∃c)(c∈B et (s,c)∈p) ──────────────────────────
    exC = N.modus_ponens(h_sin, equivalence_avant(_mem_cform(p, vb, vs)))

    # corps du témoin c : on dérive t∈p⁻¹⟨B⟩ (∌ c), puis on élimine c.
    bodyc = et(appartient(vc, vb), appartient(E.couple(vs, vc), p))   # c∈B et (s,c)∈p
    hbc = N.assume(bodyc)
    c_in_B = conjonction_elim_gauche(hbc)                  # c∈B
    sc = conjonction_elim_droite(hbc)                      # (s,c)∈p

    # ── 2. transport (s,c)∈p ⟹ (t,c)∈p sous (s,t)∈G ──────────────────────────────
    t_in_E = N.modus_ponens(h_st, instancie(instancie(h_GE, vs), vt))      # t∈E
    Cls_eq_Clt = N.modus_ponens(h_st,
                                relation_implique_classe_egale(g, "s", "t", "z"))  # Cl(s)=Cl(t)
    fwd = N.modus_ponens(sc, equivalence_avant(appcanon_membre(vs, vc)))
    #     (∃x)(x∈E et (s,c)=(x,Cl(x)))
    body_x = et(appartient(var("x"), ve),
                egal(E.couple(vs, vc), E.couple(var("x"), E.classe(vg, var("x")))))
    hb = N.assume(body_x)
    comps = N.modus_ponens(conjonction_elim_droite(hb),
                           couple_egal_implique_composantes(vs, vc, "x", E.classe(vg, var("x"))))
    #     s=x  et  c=Cl(x)
    x_eq_s = N.modus_ponens(conjonction_elim_gauche(comps), symetrie(vs, var("x")))   # x=s
    Clx_eq_Cls = N.modus_ponens(x_eq_s, congruence_terme(var("x"), vs, E.classe(vg, vw)))  # Cl(x)=Cl(s)
    c_eq_Cls = composer_egalites(conjonction_elim_droite(comps), Clx_eq_Cls)          # c=Cl(s)
    c_eq_Clt = composer_egalites(c_eq_Cls, Cls_eq_Clt)                                # c=Cl(t)
    tc_eq = N.modus_ponens(c_eq_Clt,
                           congruence_terme(vc, E.classe(vg, vt), E.couple(vt, vw)))  # (t,c)=(t,Cl(t))
    wit = conjonction_intro(t_in_E, tc_eq)                 # t∈E et (t,c)=(t,Cl(t))
    bodyX = et(appartient(var("x"), ve),
               egal(E.couple(vt, vc), E.couple(var("x"), E.classe(vg, var("x")))))
    ex_intro = N.modus_ponens(wit, N.s5(bodyX, vt, "x"))   # (∃x)(x∈E et (t,c)=(x,Cl(x)))
    tc_in_p = N.modus_ponens(ex_intro, equivalence_arriere(appcanon_membre(vt, vc)))  # (t,c)∈p
    tc = N.modus_ponens(fwd, existe_elimination(N.loi_deduction(body_x, tc_in_p), "x"))

    # ── 3. retour membership : c∈B et (t,c)∈p ⇒ t∈p⁻¹⟨B⟩ ─────────────────────────
    new_body = conjonction_intro(c_in_B, tc)               # c∈B et (t,c)∈p
    bodyc_t = et(appartient(vc, vb), appartient(E.couple(vt, vc), p))
    ex_t = N.modus_ponens(new_body, N.s5(bodyc_t, vc, "c"))           # (∃c)(c∈B et (t,c)∈p)
    t_in_prB = N.modus_ponens(ex_t, equivalence_arriere(_mem_cform(p, vb, vt)))   # t∈p⁻¹⟨B⟩
    conc = N.modus_ponens(exC, existe_elimination(N.loi_deduction(bodyc, t_in_prB), "c"))

    # ── 4. loi_deduction + double généralisation, puis pont α vers la forme canonique
    body_imp = N.loi_deduction(antec, conc)                # (s∈p⁻¹⟨B⟩ et (s,t)∈G) ⇒ t∈p⁻¹⟨B⟩
    res = N.generalisation("s", N.generalisation("t", body_imp))     # (∀s)(∀t)(…)
    cible = cible_sature_partie_saturee(g, e, b)           # forme canonique (liants x, y)
    pont = bridge_equiv(res.conclusion, cible)             # (∀s)(∀t)(…) ⇔ est_saturee(…)
    return N.modus_ponens(res, equivalence_avant(pont))    # est_saturee( p⁻¹⟨B⟩, G )


__all__ = [
    "relation_dans",
    "cible_sature_partie_saturee",
    "sature_partie_saturee",
]
