"""§II.6 — Propriétés ENSEMBLISTES des relations d'équivalence et classes (graphe G).

Module NEUF (campagne vague II-C).  On NE MODIFIE AUCUN fichier existant ; on
RÉUTILISE strictement les NOTIONS déjà définies :
  • `est_symetrique` / `est_transitive` / `est_reflexive_dans`
    / `est_relation_equivalence` / `est_relation_equivalence_dans`  (ensembles_abrege, II.6.1) ;
  • `classe(g,x) = Cl_R(x) = G⟨{x}⟩`  (ensembles_abrege, II.6.2) ;
  • `classe_membre(g,a)` ⊢ (y∈Cl_R(a)) ⇔ ((a,y)∈G)  (ensembles_equivalence, II.6.2) ;
  • `application_canonique(g,e)` = p : E→E/R, p(x)=Cl_R(x)  (ensembles_abrege, II.6.2) ;
  • `est_saturee(a,g,e)`  (ensembles_abrege, II.6.4) ;
  • `extensionnalite_appliquee(A,B)` ⊢ (A⊂B et B⊂A)⇒A=B  (ensembles_theoremes, A1).

DISTINCT des modules quotient existants : `cardinaux/ensembles_equivalence` (réflexivité
partielle, classe_membre, membre_quotient), `ensembles/relations/ensembles_quotient_props`
(produit R×R', induite R_A, plus_fine, saturation→close), `…/ensembles_quotient_complements`
(systèmes de représentants, image réciproque, classes d'objets θ), `…/ensembles_decomposition_quotient`
(R_f, décomposition canonique, quotient R/S), `…/ensembles_decomposition_effective`
(b injective via θ).  Ici on travaille sur la CLASSE-GRAPHE Cl_R(x)=G⟨{x}⟩ (et NON la
classe d'objets θ), pour démontrer les propriétés ENSEMBLISTES manquantes :

  §6.2 — Classes d'équivalence et leur caractérisation :
    • `appartient_classe`              {R réflexive dans E, x∈E} ⊢ x ∈ Cl_R(x)
          (« x∈classe(x) » ; les classes sont NON VIDES).
    • `relation_implique_classe_egale` {R sym, R trans} ⊢ R{x,y} ⇒ Cl_R(x)=Cl_R(y).
    • `classe_egale_implique_relation` {R réflexive dans E, y∈E}
                                       ⊢ Cl_R(x)=Cl_R(y) ⇒ R{x,y}
          (seul y∈E suffit : on lit R{x,y} en réécrivant y∈Cl_R(y) en y∈Cl_R(x)).
    • `relation_ssi_classe_egale`      {R réflexive dans E, R sym, R trans, y∈E}
                                       ⊢ R{x,y} ⇔ Cl_R(x)=Cl_R(y)  (E.II.6.2).

  PARTITION (E.II.6.2 : les classes partitionnent E) :
    • `classes_se_rencontrent_egales`  {R sym, R trans}
                                       ⊢ (∃z)(z∈Cl_R(x) et z∈Cl_R(y)) ⇒ Cl_R(x)=Cl_R(y).
          « deux classes qui se rencontrent sont égales » — donc deux classes sont
          ÉGALES OU DISJOINTES (forme contrapositive : non égales ⇒ disjointes).

  PROJECTION CANONIQUE p : E→E/R (E.II.6.2) :
    • `projection_valeur_classe`       {p(x)=Cl_R(x) [valeur de l'appli canonique]}
                                       ⊢ p(x)=p(y) ⇔ Cl_R(x)=Cl_R(y).
          Relie l'égalité des p-valeurs à l'égalité des classes (socle de
          « p(x)=p(y) ⇔ x R y », combiné à relation_ssi_classe_egale).

  §6.8 — Intersection de relations d'équivalence (E.II.6, « l'intersection de deux
         relations d'équivalence est une relation d'équivalence ») :
    • `intersection_symetrique`        {R sym, R' sym} ⊢ (R∩R') symétrique.
    • `intersection_transitive`        {R trans, R' trans} ⊢ (R∩R') transitive.
    • `intersection_relation_equivalence` {R éq., R' éq.} ⊢ (R∩R') éq.

theorie_ensembles() RESTE à 22 axiomes (AUCUN axiome neuf).  Toutes les preuves
sortent du noyau abrégé.  Les hypothèses (réflexivité/symétrie/transitivité,
appartenances, valeur de p) sont laissées EXPLICITEMENT dans le séquent — rien
postulé, aucune tautologie (conclusion ∉ hypothèses), aucun affaibli.

Liants : « a »,« b » (points des classes, distincts du liant interne « x » et de la
lettre libre « y » de classe_membre/coupe_membre) ; « z » (élément générique, liant
de `inclus`) ; « p »,« q »,« r » (liants des hypothèses sym/trans, frais).
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (Terme, var, egal, et, impl, equiv,
                                       appartient, existe, pourtout, inclus)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, equivalence_symetrie,
    equivalence_transitivite, instancie)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import existe_elimination
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.equipotence.ensembles_equivalence import classe_membre
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_theoremes import extensionnalite_appliquee


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# ─────────────────────────────────────────────────────────────────────────────
# helpers internes
# ─────────────────────────────────────────────────────────────────────────────
def _classe_membre_universel(g, a, z="z"):
    """⊢ (∀z)( (z∈Cl_R(a)) ⇔ ((a,z)∈G) )  (classe_membre, généralisé+renommé en z).

    `classe_membre(g,a)` a pour conclusion l'équivalence (y∈Cl_R(a))⇔((a,y)∈G) à
    lettre LIBRE y.  On la généralise sur y puis on ré-instancie en z (liant de
    `inclus`), pour produire la forme universelle au liant z partagé avec
    l'extensionnalité.  g : graphe ; a : point (≠ liant interne « x »)."""
    cm = classe_membre(g, a)                       # (y∈Cl(a)) ⇔ ((a,y)∈G)
    gen_y = N.generalisation("y", cm)              # (∀y)( … )
    return gen_y


def _egal_classes_depuis_equiv(eqv_z, A, B, z="z"):
    """De ⊢ (z∈A ⇔ z∈B) [z libre] déduire ⊢ A = B  (extensionnalité A1).

    On généralise sur z, on extrait les deux inclusions A⊂B et B⊂A (mêmes liant z
    que `inclus`), et on applique `extensionnalite_appliquee`.  A, B : termes."""
    vA, vB = _t(A), _t(B)
    incl_AB = N.generalisation(z, equivalence_avant(eqv_z))   # (∀z)(z∈A⇒z∈B) = A⊂B
    incl_BA = N.generalisation(z, equivalence_arriere(eqv_z)) # B⊂A
    ext = extensionnalite_appliquee(vA, vB)                   # (A⊂B et B⊂A)⇒A=B
    return N.modus_ponens(conjonction_intro(incl_AB, incl_BA), ext)


# ═════════════════════════════════════════════════════════════════════════════
# §6.2 — Classes d'équivalence : x∈Cl(x), et x R y ⇔ Cl(x)=Cl(y)
# ═════════════════════════════════════════════════════════════════════════════
# @livre Ch.II §6.2 Rem.- | E II.41 L.25-25 | PDF p.92
def appartient_classe(g="G", a="a", e="E", x="x"):
    """{R réflexive dans E, a∈E} ⊢ a ∈ Cl_R(a)   (E.II.6.2 ; clos mod. hyp.).

    « Tout élément appartient à sa propre classe d'équivalence » — donc les classes
    sont NON VIDES.  Cl_R(a)=G⟨{a}⟩ ; par classe_membre, a∈Cl_R(a) ⇔ (a,a)∈G = R{a,a} ;
    la réflexivité de R dans E donne R{a,a} ⇔ a∈E, d'où sous a∈E on a R{a,a} puis
    a∈Cl_R(a).  R = rel_graphe(g) ; a : point (≠ « x »).  Clos modulo {R réflexive
    dans E, a∈E}."""
    R = E.rel_graphe(g)
    va, ve = _t(a), _t(e)
    # (a∈Cl(a)) ⇔ ((a,a)∈G)   par classe_membre généralisé+instancié en a
    cm_a = instancie(_classe_membre_universel(g, a), va)      # (a∈Cl(a)) ⇔ (a,a)∈G
    href = N.assume(E.est_reflexive_dans(R, ve, x))           # (∀x)(R{x,x} ⇔ x∈E)
    ref_a = instancie(href, va)                               # R{a,a} ⇔ a∈E
    h_aE = N.assume(appartient(va, ve))                       # a∈E
    raa = N.modus_ponens(h_aE, equivalence_arriere(ref_a))    # R{a,a} = (a,a)∈G
    return N.modus_ponens(raa, equivalence_arriere(cm_a))     # a∈Cl(a)


# @livre Ch.II §6.2 Crit.C55 | E II.41 L.34-36 | PDF p.92
def relation_implique_classe_egale(g="G", a="a", b="b", z="z"):
    """{R symétrique, R transitive} ⊢ R{a,b} ⇒ Cl_R(a)=Cl_R(b)   (E.II.6.2 ; clos mod. hyp.).

    « Si a et b sont équivalents, leurs classes sont égales ».  Sous R{a,b}, pour tout
    z : (a,z)∈G ⇔ (b,z)∈G (par symétrie+transitivité : R{b,a} et R{a,z} ⇒ R{b,z}, et
    R{a,b} et R{b,z} ⇒ R{a,z}) ; via classe_membre, z∈Cl_R(a) ⇔ (a,z)∈G ⇔ (b,z)∈G
    ⇔ z∈Cl_R(b) ; extensionnalité ⇒ Cl_R(a)=Cl_R(b).  R = rel_graphe(g) ; a, b : points.
    Clos modulo {R symétrique, R transitive, R{a,b}}."""
    R = E.rel_graphe(g)
    va, vb, vz = _t(a), _t(b), var(z)
    # membership equivalences instanciées en z
    cma_z = instancie(_classe_membre_universel(g, a), vz)     # (z∈Cl(a)) ⇔ (a,z)∈G
    cmb_z = instancie(_classe_membre_universel(g, b), vz)     # (z∈Cl(b)) ⇔ (b,z)∈G
    # hypothèses
    hsym = N.assume(E.est_symetrique(R, "p", "q"))            # (∀p)(∀q)(R{p,q}⇒R{q,p})
    htr = N.assume(E.est_transitive(R, "p", "q", "r"))        # transitivité
    hab = N.assume(R(va, vb))                                 # R{a,b} = (a,b)∈G
    hba = N.modus_ponens(hab, instancie(instancie(hsym, va), vb))   # R{b,a}
    # ⇒ : (a,z)∈G ⇒ (b,z)∈G   via R{b,a} et R{a,z} ⇒ R{b,z}
    h_az = N.assume(R(va, vz))
    tr1 = instancie(instancie(instancie(htr, vb), va), vz)    # (R{b,a}et R{a,z})⇒R{b,z}
    r_bz = N.modus_ponens(conjonction_intro(hba, h_az), tr1)  # R{b,z}
    imp_fwd_g = N.loi_deduction(R(va, vz), r_bz)              # (a,z)∈G ⇒ (b,z)∈G
    # ⇐ : (b,z)∈G ⇒ (a,z)∈G   via R{a,b} et R{b,z} ⇒ R{a,z}
    h_bz = N.assume(R(vb, vz))
    tr2 = instancie(instancie(instancie(htr, va), vb), vz)    # (R{a,b}et R{b,z})⇒R{a,z}
    r_az = N.modus_ponens(conjonction_intro(hab, h_bz), tr2)  # R{a,z}
    imp_bwd_g = N.loi_deduction(R(vb, vz), r_az)              # (b,z)∈G ⇒ (a,z)∈G
    eq_g = conjonction_intro(imp_fwd_g, imp_bwd_g)            # (a,z)∈G ⇔ (b,z)∈G
    # z∈Cl(a) ⇔ (a,z)∈G ⇔ (b,z)∈G ⇔ z∈Cl(b)
    eqv_z = equivalence_transitivite(cma_z,
                equivalence_transitivite(eq_g, equivalence_symetrie(cmb_z)))
    eq_cl = _egal_classes_depuis_equiv(eqv_z, E.classe(_t(g), va),
                                       E.classe(_t(g), vb), z=z)   # Cl(a)=Cl(b)
    return N.loi_deduction(R(va, vb), eq_cl)                  # R{a,b} ⇒ Cl(a)=Cl(b)


# @livre Ch.II §6.2 Crit.C55 | E II.41 L.34-36 | PDF p.92
def classe_egale_implique_relation(g="G", a="a", b="b", e="E", x="x"):
    """{R réflexive dans E, b∈E} ⊢ Cl_R(a)=Cl_R(b) ⇒ R{a,b}   (E.II.6.2 ; clos mod. hyp.).

    Réciproque ENSEMBLISTE : « si les classes sont égales, les éléments sont
    équivalents ».  De b∈E et la réflexivité, b∈Cl_R(b) (appartient_classe) ; sous
    Cl_R(a)=Cl_R(b), Leibniz (S6) réécrit b∈Cl_R(b) en b∈Cl_R(a) ; classe_membre donne
    b∈Cl_R(a) ⇔ (a,b)∈G, d'où R{a,b}.  Seul b∈E est requis (a∈E n'intervient pas : la
    classe de b suffit).  R = rel_graphe(g) ; a, b : points.  Clos modulo {R réflexive
    dans E, b∈E}."""
    va, vb = _t(a), _t(b)
    vg = _t(g)
    cla, clb = E.classe(vg, va), E.classe(vg, vb)
    # b∈Cl(b)   (depuis réflexivité et b∈E)   — hyps {R réfl dans E, b∈E}
    b_in_clb = appartient_classe(g, b, e, x)                  # b∈Cl(b)
    # sous Cl(a)=Cl(b) : Leibniz S6 réécrit b∈Cl(b) → b∈Cl(a)
    h_eq = N.assume(egal(cla, clb))                           # Cl(a)=Cl(b)
    # S6 : (Cl(a)=Cl(b)) ⇒ ( (b∈Cl(a)) ⇔ (b∈Cl(b)) )    [trou « w » = Cl(·)]
    leib = N.s6(cla, clb, "w", appartient(vb, var("w")))
    eqv_in = N.modus_ponens(h_eq, leib)                      # (b∈Cl(a)) ⇔ (b∈Cl(b))
    b_in_cla = N.modus_ponens(b_in_clb, equivalence_arriere(eqv_in))   # b∈Cl(a)
    # classe_membre : (b∈Cl(a)) ⇔ (a,b)∈G   (instancié en b)
    cma_b = instancie(_classe_membre_universel(g, a), vb)    # (b∈Cl(a)) ⇔ (a,b)∈G
    rab = N.modus_ponens(b_in_cla, equivalence_avant(cma_b)) # (a,b)∈G = R{a,b}
    return N.loi_deduction(egal(cla, clb), rab)              # Cl(a)=Cl(b) ⇒ R{a,b}


# @livre Ch.II §6.2 Crit.C55 | E II.41 L.34-36 | PDF p.92
# @livre Ch.R §5 Prop.- | E.R.23 item 4 (R{x,y} équivalente à C(x)=C(y)) | PDF p.326
def relation_ssi_classe_egale(g="G", a="a", b="b", e="E", x="x", z="z"):
    """{R réflexive dans E, R sym, R trans, b∈E} ⊢ R{a,b} ⇔ Cl_R(a)=Cl_R(b)
    (E.II.6.2 ; clos mod. hyp.).

    Caractérisation centrale de la classe d'équivalence : « a R b si et seulement si
    Cl_R(a)=Cl_R(b) ».  Assemble relation_implique_classe_egale (sens ⇒, mod.
    {sym,trans}) et classe_egale_implique_relation (sens ⇐, mod. {réfl, b∈E}).
    R = rel_graphe(g) ; a, b : points.  Clos modulo {R réfl dans E, R sym, R trans,
    b∈E}."""
    fwd = relation_implique_classe_egale(g, a, b, z)         # R{a,b} ⇒ Cl(a)=Cl(b)
    bwd = classe_egale_implique_relation(g, a, b, e, x)      # Cl(a)=Cl(b) ⇒ R{a,b}
    return conjonction_intro(fwd, bwd)                       # R{a,b} ⇔ Cl(a)=Cl(b)


# ═════════════════════════════════════════════════════════════════════════════
# PARTITION : deux classes qui se rencontrent sont égales (donc égales ou disjointes)
# ═════════════════════════════════════════════════════════════════════════════
# @livre Ch.II §6.2 Rem.- | E II.42 L.17-23 | PDF p.93
# @livre Ch.R §5 Prop.- | E.R.23 item 2 (deux classes qui se rencontrent sont égales : partition de E) | PDF p.326
def classes_se_rencontrent_egales(g="G", a="a", b="b", z="z", w="wc"):
    """{R symétrique, R transitive}
       ⊢ (∃z)( z∈Cl_R(a) et z∈Cl_R(b) ) ⇒ Cl_R(a)=Cl_R(b)   (E.II.6.2 ; clos mod. hyp.).

    PARTITION (cœur) : « deux classes qui se rencontrent sont égales » — équivalent,
    par contraposée, à « deux classes distinctes sont DISJOINTES ».  Si un z appartient
    à Cl_R(a) et Cl_R(b), alors (a,z)∈G et (b,z)∈G (classe_membre) ; par symétrie
    (z,b)∈G puis transitivité (a,z) et (z,b) ⇒ (a,b)∈G = R{a,b} ; d'où
    Cl_R(a)=Cl_R(b) (relation_implique_classe_egale).  Le témoin z est ÉLIMINÉ
    (existe_elimination) car la conclusion Cl(a)=Cl(b) ne le contient pas.
    R = rel_graphe(g) ; a, b : points.  Clos modulo {R symétrique, R transitive}."""
    R = E.rel_graphe(g)
    va, vb, vz = _t(a), _t(b), var(z)
    # sous z∈Cl(a) et z∈Cl(b) : déduire R{a,b}
    cma_z = instancie(_classe_membre_universel(g, a), vz)    # (z∈Cl(a)) ⇔ (a,z)∈G
    cmb_z = instancie(_classe_membre_universel(g, b), vz)    # (z∈Cl(b)) ⇔ (b,z)∈G
    hsym = N.assume(E.est_symetrique(R, "p", "q"))
    htr = N.assume(E.est_transitive(R, "p", "q", "r"))
    body = et(appartient(vz, E.classe(_t(g), va)),
              appartient(vz, E.classe(_t(g), vb)))            # z∈Cl(a) et z∈Cl(b)
    hbody = N.assume(body)
    r_az = N.modus_ponens(conjonction_elim_gauche(hbody), equivalence_avant(cma_z))  # (a,z)∈G
    r_bz = N.modus_ponens(conjonction_elim_droite(hbody), equivalence_avant(cmb_z))  # (b,z)∈G
    r_zb = N.modus_ponens(r_bz, instancie(instancie(hsym, vb), vz))   # (z,b)∈G  [sym]
    tr = instancie(instancie(instancie(htr, va), vz), vb)    # (R{a,z}et R{z,b})⇒R{a,b}
    rab = N.modus_ponens(conjonction_intro(r_az, r_zb), tr)  # R{a,b} = (a,b)∈G
    # R{a,b} ⇒ Cl(a)=Cl(b)   (relation_implique_classe_egale, mod {sym,trans})
    eq_cl = N.modus_ponens(rab, relation_implique_classe_egale(g, a, b, "z"))  # Cl(a)=Cl(b)
    imp_body = N.loi_deduction(body, eq_cl)                  # (z∈Cl(a)et z∈Cl(b)) ⇒ Cl(a)=Cl(b)
    return existe_elimination(imp_body, z)                   # (∃z)(…) ⇒ Cl(a)=Cl(b)


# ═════════════════════════════════════════════════════════════════════════════
# PROJECTION CANONIQUE p : E→E/R,  p(x)=Cl_R(x)
# ═════════════════════════════════════════════════════════════════════════════
# @livre Ch.II §6.2 Crit.C55 | E II.41 L.34-36 | PDF p.92
def projection_valeur_classe(g="G", e="E", a="a", b="b"):
    """{p(a)=Cl_R(a), p(b)=Cl_R(b)} ⊢ ( p(a)=p(b) ) ⇔ ( Cl_R(a)=Cl_R(b) )
    (E.II.6.2 ; clos mod. hyp.).

    La projection canonique p : E→E/R envoie x sur sa classe Cl_R(x) ; donc ses
    valeurs coïncident exactement quand les classes coïncident.  Sous les deux
    relations de valeur p(a)=Cl_R(a) et p(b)=Cl_R(b) (caractéristiques de
    l'application canonique) :
      ⇒ : p(a)=p(b) chaîne Cl(a)=p(a)=p(b)=Cl(b) ;
      ⇐ : Cl(a)=Cl(b) chaîne p(a)=Cl(a)=Cl(b)=Cl(b)…=p(b).
    Combiné à relation_ssi_classe_egale, c'est « p(x)=p(y) ⇔ x R y » (surjection
    canonique).  p = application_canonique(g,e) ; a, b : points.  Clos modulo
    {p(a)=Cl_R(a), p(b)=Cl_R(b)}."""
    from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
        symetrie, composer_egalites)
    vg, ve = _t(g), _t(e)
    va, vb = _t(a), _t(b)
    p = E.application_canonique(vg, ve)
    pa, pb = E.valeur(p, va), E.valeur(p, vb)
    cla, clb = E.classe(vg, va), E.classe(vg, vb)
    h_pa = N.assume(egal(pa, cla))                           # p(a)=Cl(a)
    h_pb = N.assume(egal(pb, clb))                           # p(b)=Cl(b)
    # ⇒ : p(a)=p(b) ⇒ Cl(a)=Cl(b)
    h_pab = N.assume(egal(pa, pb))                           # p(a)=p(b)
    cla_pa = N.modus_ponens(h_pa, symetrie(pa, cla))         # Cl(a)=p(a)
    cla_pb = composer_egalites(cla_pa, h_pab)                # Cl(a)=p(b)
    cla_clb = composer_egalites(cla_pb, h_pb)                # Cl(a)=Cl(b)
    imp_fwd = N.loi_deduction(egal(pa, pb), cla_clb)         # p(a)=p(b) ⇒ Cl(a)=Cl(b)
    # ⇐ : Cl(a)=Cl(b) ⇒ p(a)=p(b)
    h_clab = N.assume(egal(cla, clb))                        # Cl(a)=Cl(b)
    pa_cla_clb = composer_egalites(h_pa, h_clab)             # p(a)=Cl(b)
    clb_pb = N.modus_ponens(h_pb, symetrie(pb, clb))         # Cl(b)=p(b)
    pa_pb = composer_egalites(pa_cla_clb, clb_pb)            # p(a)=p(b)
    imp_bwd = N.loi_deduction(egal(cla, clb), pa_pb)         # Cl(a)=Cl(b) ⇒ p(a)=p(b)
    return conjonction_intro(imp_fwd, imp_bwd)               # p(a)=p(b) ⇔ Cl(a)=Cl(b)


# ═════════════════════════════════════════════════════════════════════════════
# §6.8 — Intersection de deux relations d'équivalence
# ═════════════════════════════════════════════════════════════════════════════
# (R ∩ R'){x,y} := R{x,y} et R'{x,y}.  L'intersection de deux relations
# d'équivalence est une relation d'équivalence (Bourbaki, §II.6).

def relation_intersection(R, Rp):
    """(R ∩ R'){x,y} := R{x,y} et R'{x,y}  (intersection de relations).

    R, R' : relations (fonctions (Terme,Terme)→Formule).  Renvoie une fonction
    (Terme,Terme)→Formule, utilisable comme R{·,·}."""
    def S(a, b):
        return et(R(a, b), Rp(a, b))
    return S


# @livre Ch.II §6.1 Rem.- | E II.40 L.5-6 | PDF p.91
def intersection_symetrique(R=None, Rp=None, x="x", y="y"):
    """{R symétrique, R' symétrique} ⊢ (R∩R') symétrique   (§II.6 ; clos mod. hyp.).

    (R∩R'){x,y} = R{x,y} et R'{x,y} ; par symétrie de R et de R', R{y,x} et R'{y,x}
    = (R∩R'){y,x}.  L'intersection hérite de la symétrie.  R, R' à graphe par défaut ;
    clos modulo {R sym, R' sym}."""
    if R is None:
        R = E.rel_graphe("GR")
    if Rp is None:
        Rp = E.rel_graphe("GRp")
    vx, vy = var(x), var(y)
    S = relation_intersection(R, Rp)
    hsR = N.assume(E.est_symetrique(R, "a", "b"))            # (∀a)(∀b)(R{a,b}⇒R{b,a})
    hsRp = N.assume(E.est_symetrique(Rp, "a", "b"))          # idem R'
    h = N.assume(S(vx, vy))                                  # R{x,y} et R'{x,y}
    rR = conjonction_elim_gauche(h)                          # R{x,y}
    rRp = conjonction_elim_droite(h)                         # R'{x,y}
    swR = N.modus_ponens(rR, instancie(instancie(hsR, vx), vy))    # R{y,x}
    swRp = N.modus_ponens(rRp, instancie(instancie(hsRp, vx), vy)) # R'{y,x}
    but = conjonction_intro(swR, swRp)                       # (R∩R'){y,x}
    imp = N.loi_deduction(S(vx, vy), but)
    return N.generalisation(x, N.generalisation(y, imp))


# @livre Ch.II §6.1 Rem.- | E II.40 L.5-6 | PDF p.91
def intersection_transitive(R=None, Rp=None, x="x", y="y", z="z"):
    """{R transitive, R' transitive} ⊢ (R∩R') transitive   (§II.6 ; clos mod. hyp.).

    ((R∩R'){x,y} et (R∩R'){y,z}) = (R{x,y}et R'{x,y}) et (R{y,z}et R'{y,z}).
    Transitivité de R donne R{x,z}, de R' donne R'{x,z}, d'où (R∩R'){x,z}.  R, R' à
    graphe par défaut ; clos modulo {R trans, R' trans}."""
    if R is None:
        R = E.rel_graphe("GR")
    if Rp is None:
        Rp = E.rel_graphe("GRp")
    vx, vy, vz = var(x), var(y), var(z)
    S = relation_intersection(R, Rp)
    htR = N.assume(E.est_transitive(R, "a", "b", "c"))       # transitivité de R
    htRp = N.assume(E.est_transitive(Rp, "a", "b", "c"))     # transitivité de R'
    h = N.assume(et(S(vx, vy), S(vy, vz)))                   # S{x,y} et S{y,z}
    h_xy = conjonction_elim_gauche(h)                        # R{x,y} et R'{x,y}
    h_yz = conjonction_elim_droite(h)                        # R{y,z} et R'{y,z}
    rR_xy = conjonction_elim_gauche(h_xy)                    # R{x,y}
    rRp_xy = conjonction_elim_droite(h_xy)                   # R'{x,y}
    rR_yz = conjonction_elim_gauche(h_yz)                    # R{y,z}
    rRp_yz = conjonction_elim_droite(h_yz)                   # R'{y,z}
    trR = instancie(instancie(instancie(htR, vx), vy), vz)   # (R{x,y}et R{y,z})⇒R{x,z}
    rR_xz = N.modus_ponens(conjonction_intro(rR_xy, rR_yz), trR)    # R{x,z}
    trRp = instancie(instancie(instancie(htRp, vx), vy), vz) # (R'{x,y}et R'{y,z})⇒R'{x,z}
    rRp_xz = N.modus_ponens(conjonction_intro(rRp_xy, rRp_yz), trRp)  # R'{x,z}
    but = conjonction_intro(rR_xz, rRp_xz)                   # (R∩R'){x,z}
    imp = N.loi_deduction(et(S(vx, vy), S(vy, vz)), but)
    return N.generalisation(x, N.generalisation(y, N.generalisation(z, imp)))


# @livre Ch.II §6.1 Rem.- | E II.40 L.5-6 | PDF p.91
def intersection_relation_equivalence(R=None, Rp=None, x="x", y="y", z="z"):
    """{R éq., R' éq.} ⊢ (R∩R') relation d'équivalence   (§II.6 ; clos mod. hyp.).

    « L'intersection de deux relations d'équivalence est une relation d'équivalence » :
    on assemble la symétrie (intersection_symetrique) et la transitivité
    (intersection_transitive) héritées.  Conclusion LITTÉRALEMENT
    `est_relation_equivalence(R∩R')` (symétrie ET transitivité).  Clos modulo
    {R sym, R trans, R' sym, R' trans}."""
    if R is None:
        R = E.rel_graphe("GR")
    if Rp is None:
        Rp = E.rel_graphe("GRp")
    sym = intersection_symetrique(R, Rp, x, y)
    trans = intersection_transitive(R, Rp, x, y, z)
    return conjonction_intro(sym, trans)


__all__ = [
    # §6.2 — classes : x∈Cl(x), x R y ⇔ Cl(x)=Cl(y)
    "appartient_classe",
    "relation_implique_classe_egale", "classe_egale_implique_relation",
    "relation_ssi_classe_egale",
    # partition
    "classes_se_rencontrent_egales",
    # projection canonique
    "projection_valeur_classe",
    # §6.8 — intersection de relations d'équivalence
    "relation_intersection",
    "intersection_symetrique", "intersection_transitive",
    "intersection_relation_equivalence",
]
