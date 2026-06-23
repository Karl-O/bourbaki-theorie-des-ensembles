"""§III.3.5 — EXPONENTIATION CARDINALE  1^a = 1   (Proposition 11, E.III.3.5).

THÉORÈME (CLOS, rien postulé) :

    ⊢ exposant_cardinal_un_base(A) = Card({∅})      (= 1^a = 1, où 1 = {∅})
    ⊢ exposant_cardinal_binaire(Card {∅}, A) = Card({∅})

  1^a = Card(𝓕(A; {∅})) = Card({∅}) = 1 car il y a EXACTEMENT UNE application de A
  dans le singleton {∅} : tout x∈A n'a qu'une image possible (la 2ᵉ coordonnée d'un
  couple est dans {∅}, donc vaut ∅), donc l'unique graphe fonctionnel de domaine A
  à valeurs dans {∅} est M := A×{∅} = { (x, ∅) | x∈A }.

VOIE FIDÈLE.  On part de la DÉFINITION GÉNÉRALE (E.II.5.2, axiomes de membership
`axiome_exposant`/`axiome_applications`, déjà dans ensembles_abrege) :
    • exposant(A, {∅}) = {∅}^A = { G ⊂ A×{∅} | G fonctionnel ∧ dom G = A } ;
    • applications(A, {∅}) = 𝓕(A; {∅}) = { ((G,A),{∅}) | G ∈ {∅}^A }.

PALIERS (tous CLOS) :
  (1) M := A×{∅} fonctionnel (mm_fonctionnel : la 2ᵉ coord ∈{∅}⇒=∅, donc v=z=∅),
      dom M = A (mm_domaine), M ⊂ A×{∅} (mm_inclus_produit), d'où M ∈ {∅}^A
      (mm_dans_exposant) ;
  (2) CŒUR : tout G ∈ {∅}^A est M — UNICITÉ du graphe fonctionnel de domaine A à
      valeurs dans {∅} (exposant_egal_mm) ; d'où G∈{∅}^A ⇔ G=M (exposant_un_base_caracterise) ;
  (3) donc 𝓕(A;{∅}) = { ((M,A),{∅}) } (applications_un_base_singleton, DÉRIVÉ) ;
  (4) Card(𝓕(A;{∅})) = Card({∅}) = 1 (exposant_un_base_egale) via la Proposition 1
      (sens direct, version TERME _prop1_direct_t) et l'équipotence de deux singletons.
"""
from __future__ import annotations

from bourbaki.logique.formule import (Terme, var, egal, et, appartient, existe, inclus)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.logique.tactiques.tactiques_abrege import a_implique_a, syllogisme
from bourbaki.logique.tactiques.tactiques_abrege2 import (conjonction_intro, conjonction_elim_gauche,
                               conjonction_elim_droite, equivalence_avant,
                               equivalence_arriere, equivalence_transitivite,
                               instancie)
from bourbaki.logique.tactiques.tactiques_abrege_egalite import symetrie, composer_egalites, congruence_terme
from bourbaki.logique.tactiques.tactiques_abrege_quantif import existe_elimination, alpha_existe
from bourbaki.ensembles.ensembles_theoremes import egalite_par_extension
from bourbaki.ensembles.base.ensembles_couples import (singleton_membre, membre_paire_gauche,
                                  couple_egal_implique_composantes)
from bourbaki.ensembles.familles.ensembles_produit import (_instance_produit,
                                  couple_dans_produit_ssi)
from bourbaki.ensembles.fonctions.ii_3_4_fonctions_valeur.ensembles_fonctions import valeur_dans_graphe
from bourbaki.cardinaux.ensembles_cardinaux import cardinal


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def UN_BUT():
    """1 := {∅}  (le singleton servant de BUT de l'application dans 1^a)."""
    return E.singleton(E.VIDE)


def _MM(a):
    """M := A×{∅}  =  { (x, ∅) | x∈A }  (l'UNIQUE graphe fonctionnel A→{∅})."""
    return E.produit(_t(a), UN_BUT())


# ═══════════════════════════════════════════════════════════════════════════════
# Le cardinal 1^a := Card(𝓕(A; {∅}))   (E.III.3.5)
# ═══════════════════════════════════════════════════════════════════════════════
def exposant_cardinal_un_base(a):
    """1 ^ a := Card(𝓕(A; {∅}))   (base 1={∅} ; exponentiation cardinale, Déf. 4)."""
    from bourbaki.cardinaux.arithmetique.ensembles_exposant_cardinal import exposant_cardinal_binaire
    return exposant_cardinal_binaire(UN_BUT(), _t(a))


# ═══════════════════════════════════════════════════════════════════════════════
# PALIER 1.a : M = A×{∅} fonctionnel
# ═══════════════════════════════════════════════════════════════════════════════
def mm_fonctionnel(a="A"):
    """⊢ est_fonctionnel(A×{∅}).   (la 2ᵉ coordonnée d'un couple de A×{∅} est dans
    {∅} donc vaut ∅ ; deux valeurs pour un même antécédent sont toutes deux ∅.)

    est_fonctionnel(M)=(∀u)(∀v)(∀z)(((u,v)∈M et (u,z)∈M)⇒v=z).  De (u,v)∈A×{∅} on
    tire v∈{∅}⇒v=∅ (couple_dans_produit_ssi + singleton_membre) ; de même z=∅ ;
    donc v=∅=z (transitivité de l'égalité)."""
    vA = _t(a)
    one = UN_BUT()
    M = _MM(a)
    vu, vv, vz = var("u"), var("v"), var("z")
    hyp = et(appartient(E.couple(vu, vv), M), appartient(E.couple(vu, vz), M))
    h = N.assume(hyp)
    uv_in = conjonction_elim_gauche(h)                 # (u,v)∈A×{∅}
    uz_in = conjonction_elim_droite(h)                 # (u,z)∈A×{∅}
    # v∈{∅} et z∈{∅}  (2ᵉ projection via couple_dans_produit_ssi)
    ssi_v = couple_dans_produit_ssi(vu, vv, vA, one)   # (u,v)∈A×{∅} ⇔ (u∈A et v∈{∅})
    v_in = conjonction_elim_droite(N.modus_ponens(uv_in, equivalence_avant(ssi_v)))   # v∈{∅}
    ssi_z = couple_dans_produit_ssi(vu, vz, vA, one)   # (u,z)∈A×{∅} ⇔ (u∈A et z∈{∅})
    z_in = conjonction_elim_droite(N.modus_ponens(uz_in, equivalence_avant(ssi_z)))   # z∈{∅}
    v_vide = N.modus_ponens(v_in, equivalence_avant(singleton_membre(vv, E.VIDE)))    # v=∅
    z_vide = N.modus_ponens(z_in, equivalence_avant(singleton_membre(vz, E.VIDE)))    # z=∅
    # v=∅ et z=∅ ⇒ v=z  (v=∅, ∅=z par symétrie de z=∅, transitivité)
    vide_eq_z = N.modus_ponens(z_vide, symetrie(vz, E.VIDE))   # ∅=z
    v_eq_z = composer_egalites(v_vide, vide_eq_z)              # v=z
    body = N.loi_deduction(hyp, v_eq_z)
    return N.generalisation("u", N.generalisation("v", N.generalisation("z", body)))


# ═══════════════════════════════════════════════════════════════════════════════
# PALIER 1.b : dom(A×{∅}) = A
# ═══════════════════════════════════════════════════════════════════════════════
def mm_domaine(a="A"):
    """⊢ dom(A×{∅}) = A.   (chaque x∈A est défini, d'image ∅ ; aucun autre point.)

    x∈dom M ⇔ (∃y)((x,y)∈M)  [AXIOME_DOM].
      ⇒ : (x,y)∈A×{∅} ⇒ x∈A (1ʳᵉ projection) ; ∃-élim.
      ⇐ : x∈A ⇒ (x,∅)∈A×{∅} (∅∈{∅}, couple_dans_produit) ⇒ (∃y)((x,y)∈M) ⇒ x∈dom M.
    Par extension (A1, liant z)."""
    vA = _t(a)
    one = UN_BUT()
    M = _MM(a)
    vz, vy = var("z"), var("y")
    ax_dom = N.axiome(E.theorie_ensembles(), E.AXIOME_DOM)
    dom_car = instancie(instancie(ax_dom, M), vz)      # z∈dom M ⇔ (∃y)((z,y)∈M)
    czy = E.couple(vz, vy)
    # ⇒ : (∃y)((z,y)∈M) ⇒ z∈A
    hb = N.assume(appartient(czy, M))                  # (z,y)∈A×{∅}
    ssi = couple_dans_produit_ssi(vz, vy, vA, one)     # (z,y)∈A×{∅} ⇔ (z∈A et y∈{∅})
    z_in_A = conjonction_elim_gauche(N.modus_ponens(hb, equivalence_avant(ssi)))   # z∈A
    fwd_inner = existe_elimination(N.loi_deduction(appartient(czy, M), z_in_A), "y")
    fwd = syllogisme(equivalence_avant(dom_car), fwd_inner)   # z∈dom M ⇒ z∈A
    # ⇐ : z∈A ⇒ z∈dom M  via témoin y:=∅ ((z,∅)∈A×{∅})
    hz = N.assume(appartient(vz, vA))                  # z∈A
    vide_in_one = membre_paire_gauche(E.VIDE, E.VIDE)  # ∅∈{∅}
    ssi0 = couple_dans_produit_ssi(vz, E.VIDE, vA, one)  # (z,∅)∈A×{∅} ⇔ (z∈A et ∅∈{∅})
    z0_in = N.modus_ponens(conjonction_intro(hz, vide_in_one),
                           equivalence_arriere(ssi0))   # (z,∅)∈A×{∅}
    # (∃y)((z,y)∈M)  via S5 (témoin ∅)
    ry = appartient(E.couple(vz, vy), M)               # (z,y)∈M
    ex_y = N.modus_ponens(z0_in, N.s5(ry, E.VIDE, "y"))   # (∃y)((z,y)∈M)
    z_in_dom = N.modus_ponens(ex_y, equivalence_arriere(dom_car))   # z∈dom M
    bwd = N.loi_deduction(appartient(vz, vA), z_in_dom)   # z∈A ⇒ z∈dom M
    equiv_z = conjonction_intro(fwd, bwd)              # z∈dom M ⇔ z∈A
    char = N.generalisation("z", equiv_z)
    self_A = N.generalisation("z", conjonction_intro(
        a_implique_a(appartient(vz, vA)), a_implique_a(appartient(vz, vA))))
    return egalite_par_extension(char, self_A, E.dom(M), vA, "z")


# ═══════════════════════════════════════════════════════════════════════════════
# PALIER 1.c : M ⊂ A×{∅}   (trivial : M = A×{∅})
# ═══════════════════════════════════════════════════════════════════════════════
def _inclus_reflexif_t(t, z="z"):
    """⊢ T ⊂ T  pour un TERME T quelconque.   (= (∀z)(z∈T ⇒ z∈T).)"""
    vz = var(z)
    return N.generalisation(z, a_implique_a(appartient(vz, _t(t))))


def mm_inclus_produit(a="A"):
    """⊢ (A×{∅}) ⊂ (A×{∅}).   (M est trivialement inclus dans A×{∅} car M = A×{∅}.)"""
    return _inclus_reflexif_t(_MM(a))


# ═══════════════════════════════════════════════════════════════════════════════
# PALIER 1.d : M ∈ {∅}^A   (forward de la caractérisation)
# ═══════════════════════════════════════════════════════════════════════════════
def mm_dans_exposant(a="A"):
    """⊢ (A×{∅}) ∈ exposant(A, {∅}).   (M = A×{∅} est un graphe fonctionnel A→{∅}.)

    AXIOME_EXPOSANT (E=A, F={∅}) : G∈{∅}^A ⇔ (G⊂A×{∅} et G fonctionnel et dom G=A).
    Trois conjoints pour G=M : M⊂A×{∅} (mm_inclus_produit), est_fonctionnel(M)
    (mm_fonctionnel), dom M=A (mm_domaine)."""
    vA = _t(a)
    one = UN_BUT()
    M = _MM(a)
    ax = N.axiome(E.theorie_exposant(vA, one), E.axiome_exposant(vA, one))
    car = instancie(ax, M)        # M∈{∅}^A ⇔ (M⊂A×{∅} et M fonct et dom M=A)
    incl = mm_inclus_produit(a)    # M⊂A×{∅}
    func = mm_fonctionnel(a)       # est_fonctionnel(M)
    domeq = mm_domaine(a)          # dom M=A
    corps = conjonction_intro(conjonction_intro(incl, func), domeq)
    return N.modus_ponens(corps, equivalence_arriere(car))   # M∈{∅}^A


# ═══════════════════════════════════════════════════════════════════════════════
# PALIER 2 (CŒUR) : tout G ∈ {∅}^A est M = A×{∅}
# ═══════════════════════════════════════════════════════════════════════════════
def _exposant_conjoints(g, a):
    """Renvoie (h, incl, func, domeq) où h = assume(G∈{∅}^A) et les 3 conjoints
    G⊂A×{∅}, est_fonctionnel(G), dom G=A extraits via l'axiome (sous h)."""
    vG, vA = _t(g), _t(a)
    one = UN_BUT()
    ax = N.axiome(E.theorie_exposant(vA, one), E.axiome_exposant(vA, one))
    car = instancie(ax, vG)                     # G∈{∅}^A ⇔ ((G⊂A×{∅} et G fonct) et dom G=A)
    h = N.assume(appartient(vG, E.exposant(vA, one)))
    corps = N.modus_ponens(h, equivalence_avant(car))
    incl = conjonction_elim_gauche(conjonction_elim_gauche(corps))   # G⊂A×{∅}
    func = conjonction_elim_droite(conjonction_elim_gauche(corps))   # est_fonctionnel(G)
    domeq = conjonction_elim_droite(corps)                          # dom G=A
    return h, incl, func, domeq


def exposant_membre_implique_couple(g="G", a="A"):
    """{G ∈ {∅}^A} ⊢ (z ∈ (A×{∅})) ⇒ (z ∈ G).   (tout point de M = A×{∅} est dans G :
    z=(pp,∅), pp∈A=dom G donne (pp,G(pp))∈G⊂A×{∅} donc G(pp)=∅, donc (pp,∅)=z∈G.)

    z∈A×{∅} ⇒ (∃pp)(∃qq)(z=(pp,qq) et pp∈A et qq∈{∅}) ; qq=∅ ; z=(pp,∅) ; pp∈A=dom G
    donne (pp,G(pp))∈G ; (pp,G(pp))∈G⊂A×{∅} ⇒ G(pp)∈{∅} ⇒ G(pp)=∅ ; donc (pp,∅)∈G ;
    z=(pp,∅)∈G.  ⚠️ binders de décomposition « pp », « qq » (≠ p,q internes de
    couple_dans_produit_ssi) pour que la 2ᵉ projection sur (pp, G(pp)) — terme
    contenant pp — reste sûre."""
    from bourbaki.logique.tactiques.tactiques_abrege_quantif import congruence_existe
    vG, vA = _t(g), _t(a)
    one = UN_BUT()
    M = _MM(a)
    vz, vp, vq = var("z"), var("pp"), var("qq")
    h, incl, func, domeq = _exposant_conjoints(g, a)
    hz = N.assume(appartient(vz, M))            # z∈A×{∅}
    # z∈A×{∅} ⇔ (∃p)(∃q)(...)  [AXIOME_PRODUIT], puis α-renommage p→pp, q→qq (sûr car
    # z, A, {∅} ne contiennent pas p,q libres).
    prod_car0 = _instance_produit(vA, one, vz)
    body_p = et(et(egal(vz, E.couple(var("p"), var("q"))), appartient(var("p"), vA)),
                appartient(var("q"), one))
    ren_p = alpha_existe("p", "pp", existe("q", body_p))   # (∃p)(∃q)body_p ⇔ (∃pp)(∃q)...
    inner_pp = et(et(egal(vz, E.couple(vp, var("q"))), appartient(vp, vA)),
                  appartient(var("q"), one))
    ren_q = congruence_existe(alpha_existe("q", "qq", inner_pp), "pp")   # (∃pp)(∃q)... ⇔ (∃pp)(∃qq)...
    ren = equivalence_transitivite(ren_p, ren_q)           # (∃p)(∃q)body_p ⇔ (∃pp)(∃qq)body
    prod_car = equivalence_transitivite(prod_car0, ren)    # z∈A×{∅} ⇔ (∃pp)(∃qq)body
    body = et(et(egal(vz, E.couple(vp, vq)), appartient(vp, vA)), appartient(vq, one))
    # sous body : conclure z∈G
    hb = N.assume(body)
    z_pq = conjonction_elim_gauche(conjonction_elim_gauche(hb))   # z=(p,q)
    p_in = conjonction_elim_droite(conjonction_elim_gauche(hb))   # p∈A
    q_in = conjonction_elim_droite(hb)                           # q∈{∅}
    q_vide = N.modus_ponens(q_in, equivalence_avant(singleton_membre(vq, E.VIDE)))   # q=∅
    # z=(p,q)=(p,∅)  (congruence sur 2ᵉ coordonnée)
    pq_p0 = N.modus_ponens(q_vide, congruence_terme(vq, E.VIDE, E.couple(vp, var("w"))))
    z_p0 = composer_egalites(z_pq, pq_p0)       # z=(p,∅)
    # p∈A=dom G : p∈dom G   (Leibniz S6 sur 2ᵉ arg de ∈, via dom G=A)
    A_eq_dom = N.modus_ponens(domeq, symetrie(E.dom(vG), vA))       # A=dom G  (de dom G=A)
    leib_dom = N.s6(vA, E.dom(vG), "w", appartient(vp, var("w")))   # (A=dom G)⇒(p∈A⇔p∈dom G)
    p_in_dom = N.modus_ponens(p_in, equivalence_avant(
        N.modus_ponens(A_eq_dom, leib_dom)))   # p∈dom G
    # p∈dom G ⇔ (∃y)((p,y)∈G)  [AXIOME_DOM] ; donc (p,G(p))∈G
    ax_dom = N.axiome(E.theorie_ensembles(), E.AXIOME_DOM)
    dom_car = instancie(instancie(ax_dom, vG), vp)            # p∈dom G ⇔ (∃y)((p,y)∈G)
    ex_y = N.modus_ponens(p_in_dom, equivalence_avant(dom_car))   # (∃y)((p,y)∈G)
    cpl = valeur_dans_graphe(vG, vp)            # {(∃y)((p,y)∈G)} ⊢ (p, G(p))∈G
    p_fp_in_G = N.modus_ponens(ex_y, N.loi_deduction(
        existe("y", appartient(E.couple(vp, var("y")), vG)), cpl))   # (p,G(p))∈G
    # (p,G(p))∈G⊂A×{∅} ⇒ (p,G(p))∈A×{∅} ⇒ G(p)∈{∅} ⇒ G(p)=∅
    fp = E.valeur(vG, vp)                       # G(p)
    incl_inst = instancie(incl, E.couple(vp, fp))   # (p,G(p))∈G ⇒ (p,G(p))∈A×{∅}
    p_fp_in_prod = N.modus_ponens(p_fp_in_G, incl_inst)   # (pp,G(pp))∈A×{∅}
    # G(pp)∈{∅}  (2ᵉ projection ; sûr car pp≠p,q internes de couple_dans_produit_ssi)
    ssi_fp = couple_dans_produit_ssi(vp, fp, vA, one)   # (pp,G(pp))∈A×{∅} ⇔ (pp∈A et G(pp)∈{∅})
    fp_in = conjonction_elim_droite(N.modus_ponens(p_fp_in_prod, equivalence_avant(ssi_fp)))  # G(pp)∈{∅}
    fp_vide = N.modus_ponens(fp_in, equivalence_avant(singleton_membre(fp, E.VIDE)))   # G(p)=∅
    # (p,G(p))∈G et G(p)=∅ ⇒ (p,∅)∈G   (Leibniz S6 sur G(p)→∅ dans le 1ᵉʳ arg de ∈)
    leib_fp = N.s6(fp, E.VIDE, "w", appartient(E.couple(vp, var("w")), vG))   # (G(p)=∅)⇒((p,G(p))∈G⇔(p,∅)∈G)
    p0_in_G = N.modus_ponens(p_fp_in_G, equivalence_avant(N.modus_ponens(fp_vide, leib_fp)))   # (p,∅)∈G
    # z=(p,∅) et (p,∅)∈G ⇒ z∈G   (Leibniz S6 sur 1ᵉʳ arg de ∈)
    leib_z = N.s6(vz, E.couple(vp, E.VIDE), "w", appartient(var("w"), vG))   # (z=(p,∅))⇒(z∈G⇔(p,∅)∈G)
    z_in_G = N.modus_ponens(p0_in_G, equivalence_arriere(N.modus_ponens(z_p0, leib_z)))   # z∈G
    inner = existe_elimination(existe_elimination(
        N.loi_deduction(body, z_in_G), "qq"), "pp")    # (∃pp)(∃qq)body ⇒ z∈G
    z_imp = syllogisme(equivalence_avant(prod_car), inner)   # z∈A×{∅} ⇒ z∈G
    concl = N.modus_ponens(hz, z_imp)           # z∈G   [sous z∈A×{∅}, h]
    return N.loi_deduction(appartient(vz, M), concl)   # (z∈A×{∅}) ⇒ z∈G   [sous h]


def exposant_egal_mm(g="G", a="A"):
    """{G ∈ {∅}^A} ⊢ G = A×{∅}.   (UNICITÉ du graphe fonctionnel de domaine A à
    valeurs dans {∅} : G est exactement M = A×{∅}.)

    Par extension (liant z) : z∈G ⇔ z∈A×{∅}.
      ⇒ : z∈G ⊂ A×{∅} ⇒ z∈A×{∅}  (le conjoint d'inclusion de l'axiome).
      ⇐ : z∈A×{∅} ⇒ z∈G  (exposant_membre_implique_couple)."""
    vG, vA = _t(g), _t(a)
    one = UN_BUT()
    M = _MM(a)
    vz = var("z")
    h, incl, func, domeq = _exposant_conjoints(g, a)
    # ⇒ : z∈G ⇒ z∈A×{∅}  (instancier l'inclusion G⊂A×{∅} à z)
    fwd = instancie(incl, vz)                   # z∈G ⇒ z∈A×{∅}
    # ⇐ : z∈A×{∅} ⇒ z∈G
    bwd = exposant_membre_implique_couple(g, a) # (z∈A×{∅}) ⇒ z∈G   [sous h]
    equiv_z = conjonction_intro(fwd, bwd)       # z∈G ⇔ z∈A×{∅}
    char = N.generalisation("z", equiv_z)
    self_M = N.generalisation("z", conjonction_intro(
        a_implique_a(appartient(vz, M)), a_implique_a(appartient(vz, M))))
    return egalite_par_extension(char, self_M, vG, M, "z")   # G = A×{∅}   [sous h]


def exposant_un_base_caracterise(g="G", a="A"):
    """⊢ (G ∈ {∅}^A) ⇔ (G = A×{∅}).   (caractérisation COMPLÈTE de {∅}^A : son
    UNIQUE élément est le graphe M = A×{∅}.)

    ⇒ : exposant_egal_mm (G∈{∅}^A ⇒ G=M) déchargé en implication.
    ⇐ : G=M ⇒ G∈{∅}^A car M∈{∅}^A (mm_dans_exposant) transporté par Leibniz."""
    vG, vA = _t(g), _t(a)
    one = UN_BUT()
    M = _MM(a)
    # ⇒
    fwd = N.loi_deduction(appartient(vG, E.exposant(vA, one)), exposant_egal_mm(g, a))
    # ⇐ : G=M ⇒ G∈{∅}^A
    hG = N.assume(egal(vG, M))                  # G=M
    M_in = mm_dans_exposant(a)                  # M∈{∅}^A
    # (G=M) ⇒ (G∈{∅}^A ⇔ M∈{∅}^A)   (Leibniz S6 sur 1ᵉʳ arg de ∈)
    leib = N.s6(vG, M, "w", appartient(var("w"), E.exposant(vA, one)))
    G_in = N.modus_ponens(M_in, equivalence_arriere(N.modus_ponens(hG, leib)))   # G∈{∅}^A
    bwd = N.loi_deduction(egal(vG, M), G_in)    # G=M ⇒ G∈{∅}^A
    return conjonction_intro(fwd, bwd)


# ═══════════════════════════════════════════════════════════════════════════════
# PALIER 3 : 𝓕(A;{∅}) = { ((A×{∅},A),{∅}) }   (l'unique application A→{∅})
# ═══════════════════════════════════════════════════════════════════════════════
def _omega(a):
    """ω_A := ((A×{∅}, A), {∅})  =  l'unique application de A dans {∅}."""
    return E.couple(E.couple(_MM(a), _t(a)), UN_BUT())


def applications_un_base_singleton(a="A"):
    """⊢ 𝓕(A; {∅}) = { ((A×{∅},A),{∅}) }.   (l'UNIQUE application de A dans {∅} est
    ω = ((M,A),{∅}) où M = A×{∅}.  DÉRIVÉ, pas postulé.)

    AXIOME_APPLICATIONS : z∈𝓕(A;{∅}) ⇔ (∃G)(z=((G,A),{∅}) et G∈{∅}^A).
      ⇒ : G∈{∅}^A ⇒ G=M (exposant_egal_mm), donc z=((G,A),{∅})=((M,A),{∅})=ω ; ∃-élim.
      ⇐ : z=ω ⇒ témoin G:=M (M∈{∅}^A par mm_dans_exposant, ω=((M,A),{∅})).
    Donc z∈𝓕(A;{∅}) ⇔ z=ω ⇔ z∈{ω}.  Par extension (A1, liant z)."""
    vA = _t(a)
    one = UN_BUT()
    M = _MM(a)
    omega = _omega(a)
    s_omega = E.singleton(omega)
    vz, vG = var("z"), var("G")
    ax = N.axiome(E.theorie_applications(vA, one), E.axiome_applications(vA, one))
    app_car = instancie(ax, vz)                 # z∈𝓕(A;{∅}) ⇔ (∃G)(z=((G,A),{∅}) et G∈{∅}^A)
    triple = E.couple(E.couple(vG, vA), one)    # ((G,A),{∅})
    body = et(egal(vz, triple), appartient(vG, E.exposant(vA, one)))
    # ── ⇒ : (∃G)body ⇒ z=ω ──────────────────────────────────────────────────────
    hb = N.assume(body)
    z_eq_triple = conjonction_elim_gauche(hb)   # z=((G,A),{∅})
    G_in = conjonction_elim_droite(hb)          # G∈{∅}^A
    G_eq_M = N.modus_ponens(G_in, N.loi_deduction(
        appartient(vG, E.exposant(vA, one)), exposant_egal_mm("G", a)))   # G=M
    # ((G,A),{∅})=((M,A),{∅})=ω  via congruence sur le coin G (trou w)
    triple_eq_omega = N.modus_ponens(G_eq_M,
        congruence_terme(vG, M, E.couple(E.couple(var("w"), vA), one)))   # ((G,A),{∅})=ω
    z_eq_omega = composer_egalites(z_eq_triple, triple_eq_omega)   # z=ω
    fwd_inner = existe_elimination(N.loi_deduction(body, z_eq_omega), "G")   # (∃G)body ⇒ z=ω
    fwd = syllogisme(equivalence_avant(app_car), fwd_inner)        # z∈𝓕 ⇒ z=ω
    # ── ⇐ : z=ω ⇒ (∃G)body  via témoin G:=M ─────────────────────────────────────
    z_eq_omega_hyp = N.assume(egal(vz, omega))  # z=ω
    M_in_exp = mm_dans_exposant(a)              # M∈{∅}^A
    wit = conjonction_intro(z_eq_omega_hyp, M_in_exp)   # (G|→M)body = (z=ω et M∈{∅}^A)
    ex_G = N.modus_ponens(wit, N.s5(body, M, "G"))      # (∃G)body
    in_app = N.modus_ponens(ex_G, equivalence_arriere(app_car))   # z∈𝓕  [sous z=ω]
    bwd = N.loi_deduction(egal(vz, omega), in_app)      # z=ω ⇒ z∈𝓕
    eq_z_omega = conjonction_intro(fwd, bwd)    # z∈𝓕 ⇔ z=ω
    # ── z=ω ⇔ z∈{ω} ────────────────────────────────────────────────────────────
    s_mem = singleton_membre(vz, omega)         # z∈{ω} ⇔ z=ω
    z_omega_z_s = conjonction_intro(equivalence_arriere(s_mem), equivalence_avant(s_mem))  # z=ω ⇔ z∈{ω}
    chain = equivalence_transitivite(eq_z_omega, z_omega_z_s)   # z∈𝓕 ⇔ z∈{ω}
    char = N.generalisation("z", chain)
    self_s = N.generalisation("z", conjonction_intro(
        a_implique_a(appartient(vz, s_omega)), a_implique_a(appartient(vz, s_omega))))
    return egalite_par_extension(char, self_s, E.applications(vA, one), s_omega, "z")


# ═══════════════════════════════════════════════════════════════════════════════
# PALIER 4 : 1^a = 1   (Proposition 11, E.III.3.5)
# ═══════════════════════════════════════════════════════════════════════════════
def eq_applications_un_base_singleton(a="A"):
    """⊢ Eq(𝓕(A; {∅}), {∅}).   (l'ensemble des applications de A dans {∅} est
    équipotent au singleton {∅} = 1 : c'est lui-même un singleton.)

    𝓕(A;{∅}) = {ω} (applications_un_base_singleton) ; Eq({ω}, {∅}) (eq_singletons) ;
    on transporte le 1ᵉʳ argument de Eq par l'égalité d'ensembles via S6 (Leibniz).

    NB : le paramètre A ne doit PAS être nommé « F » — la relation Eq(·,·) lie
    elle-même « F » (Eq(X,Y) := (∃F)bij).  Le défaut « A » et tout nom ≠ F,x,y,z
    conviennent."""
    from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_zero_plus_un import eq_singletons
    from bourbaki.cardinaux.ensembles_cardinaux import equipotent
    vA = _t(a)
    one = UN_BUT()
    omega = _omega(a)
    s_omega = E.singleton(omega)
    AF = E.applications(vA, one)                # 𝓕(A;{∅})
    eq_set = applications_un_base_singleton(a)  # 𝓕(A;{∅}) = {ω}
    eq_sing = eq_singletons(omega, E.VIDE)      # Eq({ω}, {∅})
    leib = N.s6(AF, s_omega, "w", equipotent(var("w"), one))   # (𝓕={ω}) ⇒ (Eq(𝓕,{∅}) ⇔ Eq({ω},{∅}))
    equiv_eq = N.modus_ponens(eq_set, leib)
    return N.modus_ponens(eq_sing, equivalence_arriere(equiv_eq))   # Eq(𝓕(A;{∅}), {∅})


def exposant_un_base_egale(a="A"):
    """⊢ Card(𝓕(A; {∅})) = Card({∅}).   (= 1^a = 1 ; PROPOSITION 11, E.III.3.5, CLOS.)

    1^a = exposant_cardinal_binaire(Card {∅}, A) = Card(𝓕(A; {∅})).  Eq(𝓕(A;{∅}),{∅})
    (eq_applications_un_base_singleton) ; la Proposition 1 (sens direct, version TERME
    _prop1_direct_t) conclut Card(𝓕(A;{∅})) = Card({∅}) = 1.  Paramètre A ≠ « F »."""
    from bourbaki.cardinaux.arithmetique.ensembles_arith_cardinale import _prop1_direct_t
    vA = _t(a)
    one = UN_BUT()
    AF = E.applications(vA, one)                # 𝓕(A;{∅})  (support de 1^a)
    eq = eq_applications_un_base_singleton(a)   # Eq(𝓕(A;{∅}), {∅})
    prop1 = _prop1_direct_t(AF, one)            # Eq(𝓕(A;{∅}),{∅}) ⇒ Card(𝓕)=Card({∅})
    return N.modus_ponens(eq, prop1)            # Card(𝓕(A;{∅})) = Card({∅}) = 1^a = 1


def exposant_cardinal_un_base_egale(a="A"):
    """⊢ 1 ^ a = Card({∅}).   (= 1 ; PROPOSITION 11, 1^a = 1, sur l'OPÉRATEUR
    exposant_cardinal_un_base pour A quelconque.  CLOS.)

    Par définition exposant_cardinal_un_base(A) = exposant_cardinal_binaire(Card {∅}, A)
    = Card(𝓕(A; {∅})).  exposant_un_base_egale(A) : Card(𝓕(A;{∅})) = Card({∅}) = 1.
    La conclusion est LITTÉRALEMENT exposant_cardinal_un_base(A) = Card({∅}) = 1."""
    return exposant_un_base_egale(_t(a))


__all__ = ["exposant_cardinal_un_base", "UN_BUT",
           "mm_fonctionnel", "mm_domaine", "mm_inclus_produit", "mm_dans_exposant",
           "exposant_membre_implique_couple", "exposant_egal_mm",
           "exposant_un_base_caracterise",
           "applications_un_base_singleton",
           "eq_applications_un_base_singleton", "exposant_un_base_egale",
           "exposant_cardinal_un_base_egale"]
