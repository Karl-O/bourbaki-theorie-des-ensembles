"""§III.3.5 — a^1 = a, PARTIE 1 : le graphe constant G_v et la réciproque η.

Sous-module de `ensembles_exposant_un` (cf. __init__.py pour la vue d'ensemble et
le théorème a^1 = a complet).  Ici : helpers, PALIER 1 (G_v = {(∅,v)} : fonctionnel,
domaine {∅}, ⊂ {∅}×A, ∈ A^{∅}, déterminé par v), caractérisation z∈G_v ⇔ z=(∅,v),
et PALIER 2 (η : A → 𝓕({∅};A), v ↦ ((G_v,{∅}),A) : fonctionnelle, dom=A, injective).

⚠️ PIÈGE CAPTURE : la valeur du graphe constant est libre ; son nom (« c » par
défaut) doit éviter les liants internes {u,v,z,x,y,w} de la machinerie graphe-terme,
sinon elle est CAPTURÉE.  De même les coordonnées internes (cu,cy,cw) sont choisies
pour rester sûres quand v est var("u")/var("up") (cf. eta_injective).
"""
from __future__ import annotations

from bourbaki.logique.formule import (Terme, var, egal, et, non, ou, impl, appartient,
                     existe, pourtout, inclus, subst_t, subst_f)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.logique.tactiques.tactiques_abrege import a_implique_a, syllogisme
from bourbaki.logique.tactiques.tactiques_abrege2 import (conjonction_intro, conjonction_elim_gauche,
                               conjonction_elim_droite, equivalence_avant,
                               equivalence_arriere, equivalence_transitivite,
                               instancie, projection_gauche, projection_droite)
from bourbaki.logique.tactiques.tactiques_abrege_egalite import symetrie, composer_egalites, congruence_terme
from bourbaki.logique.tactiques.tactiques_abrege_quantif import existe_elimination, alpha_existe
from bourbaki.ensembles.ensembles_theoremes import egalite_par_extension
from bourbaki.ensembles.base.ensembles_couples import (singleton_membre, membre_paire_gauche,
                                  singleton_injectif, couple_egal_implique_composantes)
from bourbaki.ensembles.fonctions.ii_3_6_fonction_terme.ensembles_fonction_terme import (membre_graphe_terme,
                                       graphe_terme_fonctionnel)
from bourbaki.cardinaux.ensembles_cantor import (graphe_terme_domaine, graphe_terme_valeur,
                            graphe_terme_couple_dans)
from bourbaki.cardinaux.ensembles_cardinaux import cardinal



def _t(v):
    return v if isinstance(v, Terme) else var(v)


# Le marqueur 1 = {∅} (l'ensemble à un élément, ici la source de l'application).
def UN_SOURCE():
    """1 := {∅}  (l'ensemble à un élément servant de source dans a^1)."""
    return E.singleton(E.VIDE)


# ═══════════════════════════════════════════════════════════════════════════════
# Le cardinal a^1 := Card(𝓕({∅}; A))   (E.III.3.5)
# ═══════════════════════════════════════════════════════════════════════════════
def exposant_cardinal_un(a):
    """a ^ 1 := Card(𝓕({∅}; a))   (a, b=1={∅} ; exponentiation cardinale, Déf. 4)."""
    from bourbaki.cardinaux.arithmetique.ensembles_exposant_cardinal import exposant_cardinal_binaire
    return exposant_cardinal_binaire(_t(a), UN_SOURCE())


# ═══════════════════════════════════════════════════════════════════════════════
# Le graphe CONSTANT  G_v := graphe_terme({∅}, v, "x") = {(∅, v)}
#   (l'application {∅} → A qui envoie l'unique point ∅ sur v)
# ═══════════════════════════════════════════════════════════════════════════════
def _gv(v):
    """G_v := graphe_terme({∅}, v, "x")  = graphe constant x↦v sur {∅}.

    Le terme v ne contient pas la variable liée "x", donc T[x]=v ; le support de
    G_v est exactement {(∅, v)}.  ⚠️ le nom de la VALEUR doit éviter les liants
    internes {u, v, z, x, y, w} de la machinerie graphe-terme (sinon capture) ;
    on utilise « c » par défaut (cf. gv_fonctionnel)."""
    return E.graphe_terme(UN_SOURCE(), _t(v), "x")


# ── PALIER 1.a : G_v fonctionnel ──────────────────────────────────────────────
def gv_fonctionnel(v="c"):
    """⊢ est_fonctionnel(G_v),  G_v = graphe constant x↦v sur {∅}.   (cas T=v de C54.)

    ⚠️ la valeur v est libre ; son nom doit éviter les liants u,v,z de
    est_fonctionnel (défaut « c »), sinon elle serait CAPTURÉE."""
    return graphe_terme_fonctionnel(UN_SOURCE(), _t(v), "x", "y")


# ── PALIER 1.b : dom G_v = {∅} ────────────────────────────────────────────────
def gv_domaine(v="c"):
    """⊢ dom(G_v) = {∅}.   (la fonction constante est définie sur tout {∅} ; clos.)"""
    return graphe_terme_domaine(UN_SOURCE(), _t(v), "x", "y", "z")


# ── PALIER 1.c : (∅, v) ∈ G_v ─────────────────────────────────────────────────
def gv_couple_dans(v="c", cu="cu", cy="cy"):
    """⊢ (∅, v) ∈ G_v.   (le couple (∅,v) est dans le graphe constant ; T[∅]=v car
    v sans x.)  Via membre_graphe_terme (coordonnées libres cu,cy) instanciée à
    cu:=∅, cy:=v : ((∅,v)∈G_v) ⇔ (∅∈{∅} et v=v) ; ∅∈{∅} (réflexivité) et v=v donnent
    le sens ⇐.

    ⚠️ les noms de coordonnées cu, cy doivent éviter les variables libres de v
    (sinon capture par membre_graphe_terme) — défaut « cu », « cy » sûrs même quand
    v = var(\"u\")/var(\"up\") (cf. eta_injective)."""
    vv = _t(v)
    one = UN_SOURCE()
    # ((cu,cy)∈G_v) ⇔ (cu∈{∅} et cy=T[cu]=v)   [T=v sans x ⇒ T[cu]=v]
    mem = membre_graphe_terme(one, vv, cu, cy, "x", "yb")     # liants libres cu,cy
    mem_all = N.generalisation(cu, N.generalisation(cy, mem))
    mem_inst = instancie(instancie(mem_all, E.VIDE), vv)      # ((∅,v)∈G_v) ⇔ (∅∈{∅} et v=v)
    vide_in = membre_paire_gauche(E.VIDE, E.VIDE)             # ∅∈{∅,∅}={∅}
    wit = conjonction_intro(vide_in, N.reflexivite(vv))      # ∅∈{∅} et v=v
    return N.modus_ponens(wit, equivalence_arriere(mem_inst))  # (∅,v)∈G_v


# ═══════════════════════════════════════════════════════════════════════════════
# PALIER 1.d : G_v ⊂ {∅}×A   (sous v∈A)
# ═══════════════════════════════════════════════════════════════════════════════
def gv_inclus_produit(v="c", a="A"):
    """{v ∈ A} ⊢ G_v ⊂ {∅}×A.   (le graphe constant est inclus dans {∅}×A.)

    G_v ⊂ {∅}×A = (∀z)(z∈G_v ⇒ z∈{∅}×A).  z∈G_v ⇔ (∃p)(∃q)(z=(p,q) et p∈{∅} et
    q=v) [membre du graphe-terme via ses 2 coordonnées].  Plus simplement on passe
    par : z∈G_v ⇒ z=(pr₁z, pr₂z) avec pr₁z∈{∅}, pr₂z=v∈A.  Ici on REDUIT z à un
    couple (u, T[u]) via membre_graphe_terme appliqué aux coordonnées libres."""
    vv, vA = _t(v), _t(a)
    one = UN_SOURCE()
    G = _gv(v)
    vz, vu, vy = var("z"), var("u"), var("y")
    # On caractérise (u, y)∈G_v ⇔ (u∈{∅} et y=v), puis on montre (u,y)∈{∅}×A.
    # Mais z∈G_v est quelconque ; on a besoin de la forme couple. membre_graphe_terme
    # est sur (u,y).  On utilise donc l'axiome du graphe-terme sur z directement :
    #   z∈G_v ⇔ (∃u)(∃y)(z=(u,y) et u∈{∅} et y=v).
    from bourbaki.ensembles.fonctions.ii_3_6_fonction_terme.ensembles_fonction_terme import _inst_axiome
    inst = _inst_axiome(one, vv, vz, "u", "y")        # z∈G_v ⇔ (∃u)(∃y)(z=(u,y) et u∈{∅} et y=v)
    body = et(et(egal(vz, E.couple(vu, vy)), appartient(vu, one)), egal(vy, vv))
    h_vA = N.assume(appartient(vv, vA))               # v∈A
    # corps ⇒ z∈{∅}×A : de z=(u,y), u∈{∅}, y=v∈A → (u,y)∈{∅}×A → z∈{∅}×A
    from bourbaki.ensembles.familles.ensembles_produit import couple_dans_produit
    hb = N.assume(body)
    z_uy = conjonction_elim_gauche(conjonction_elim_gauche(hb))   # z=(u,y)
    u_in = conjonction_elim_droite(conjonction_elim_gauche(hb))   # u∈{∅}
    y_v = conjonction_elim_droite(hb)                            # y=v
    # y∈A : y=v et v∈A → y∈A (Leibniz)
    y_in_A = N.modus_ponens(h_vA, equivalence_arriere(
        N.modus_ponens(y_v, N.s6(vy, vv, "w", appartient(var("w"), vA)))))   # y∈A
    uy_in = N.modus_ponens(conjonction_intro(u_in, y_in_A),
                           _couple_dans_produit_t(vu, vy, one, vA))   # (u,y)∈{∅}×A
    # z∈{∅}×A : z=(u,y) et (u,y)∈{∅}×A → z∈{∅}×A (Leibniz)
    z_in = N.modus_ponens(uy_in, equivalence_arriere(
        N.modus_ponens(z_uy, N.s6(vz, E.couple(vu, vy), "w",
                                  appartient(var("w"), E.produit(one, vA))))))   # z∈{∅}×A
    inner = existe_elimination(existe_elimination(
        N.loi_deduction(body, z_in), "y"), "u")       # (∃u)(∃y)body ⇒ z∈{∅}×A
    imp = syllogisme(equivalence_avant(inst), inner)  # z∈G_v ⇒ z∈{∅}×A
    incl = N.generalisation("z", imp)                 # G_v ⊂ {∅}×A
    return N.loi_deduction(appartient(vv, vA), incl)  # {v∈A} ⊢ G_v ⊂ {∅}×A


def _couple_dans_produit_t(u, v, a, b):
    """⊢ (u∈A et v∈B) ⇒ ((u,v)∈A×B), version TERMES (u,v,a,b termes), appliquée :
    renvoie le théorème (u,v)∈A×B sous l'hypothèse déjà fournie en conjonction."""
    # implémentation directe (évite la dépendance aux noms de couple_dans_produit)
    from bourbaki.ensembles.familles.ensembles_produit import _instance_produit
    vu, vv, vA, vB = _t(u), _t(v), _t(a), _t(b)
    inst = _instance_produit(vA, vB, E.couple(vu, vv))
    pinner = et(et(egal(E.couple(vu, vv), E.couple(var("p"), var("q"))),
                   appartient(var("p"), vA)), appartient(var("q"), vB))
    h = N.assume(et(appartient(vu, vA), appartient(vv, vB)))
    temoin = conjonction_intro(conjonction_intro(N.reflexivite(E.couple(vu, vv)),
                                                 conjonction_elim_gauche(h)),
                               conjonction_elim_droite(h))
    gbody = subst_f(vu, "p", pinner)
    qq = N.modus_ponens(temoin, N.s5(gbody, vv, "q"))
    full = N.modus_ponens(qq, N.s5(existe("q", pinner), vu, "p"))
    dans = N.modus_ponens(full, equivalence_arriere(inst))
    imp = N.loi_deduction(et(appartient(vu, vA), appartient(vv, vB)), dans)
    return imp  # renvoie l'IMPLICATION ; l'appelant fait modus_ponens avec la conjonction


# ═══════════════════════════════════════════════════════════════════════════════
# PALIER 1.e : G_v ∈ A^{∅}   (sous v∈A)  — forward de la caractérisation
# ═══════════════════════════════════════════════════════════════════════════════
def gv_dans_exposant(v="c", a="A"):
    """{v ∈ A} ⊢ G_v ∈ exposant({∅}, A).   (le graphe constant {(∅,v)} est un
    élément de A^{∅} = l'ensemble des graphes fonctionnels {∅}→A.)

    AXIOME_EXPOSANT (E={∅}, F=A) : G∈A^{∅} ⇔ (G⊂{∅}×A et G fonctionnel et dom G={∅}).
    On vérifie les trois conjoints pour G=G_v : G_v⊂{∅}×A (gv_inclus_produit, sous
    v∈A), est_fonctionnel(G_v) (gv_fonctionnel), dom G_v={∅} (gv_domaine)."""
    vv, vA = _t(v), _t(a)
    one = UN_SOURCE()
    G = _gv(v)
    ax = N.axiome(E.theorie_exposant(one, vA), E.axiome_exposant(one, vA))
    car = instancie(ax, G)        # G_v∈A^{∅} ⇔ (G_v⊂{∅}×A et G_v fonct et dom G_v={∅})
    incl = gv_inclus_produit(v, a)   # {v∈A} ⊢ G_v⊂{∅}×A   (implication v∈A ⇒ ...)
    func = gv_fonctionnel(v)          # est_fonctionnel(G_v)
    domeq = gv_domaine(v)             # dom G_v={∅}
    h_vA = N.assume(appartient(vv, vA))
    incl_app = N.modus_ponens(h_vA, incl)        # G_v⊂{∅}×A  [sous v∈A]
    corps = conjonction_intro(conjonction_intro(incl_app, func), domeq)
    g_in = N.modus_ponens(corps, equivalence_arriere(car))   # G_v∈A^{∅}  [sous v∈A]
    return N.loi_deduction(appartient(vv, vA), g_in)


# ═══════════════════════════════════════════════════════════════════════════════
# PALIER 1.f : G_v déterminé par v   —   G_v = G_{v'} ⇒ v = v'
# ═══════════════════════════════════════════════════════════════════════════════
def gv_injectif(v="c", vp="cp", w="cw", cu="cu", cy="cy"):
    """⊢ (G_v = G_{v'}) ⇒ (v = v').   (le graphe constant détermine sa valeur.)

    (∅,v)∈G_v (gv_couple_dans) ; G_v=G_{v'} transporte (Leibniz) à (∅,v)∈G_{v'} ;
    membre_graphe_terme sur G_{v'} donne (∅∈{∅} et v=T'[∅]=v'), d'où v=v'.

    ⚠️ noms internes (w trou Leibniz, cu/cy coordonnées) sûrs même quand v,v' sont
    des variables liées (var(\"u\"),var(\"up\")) — cf. eta_injective."""
    vv, vvp = _t(v), _t(vp)
    one = UN_SOURCE()
    Gv, Gvp = _gv(v), _gv(vp)
    h = N.assume(egal(Gv, Gvp))                          # G_v = G_{v'}
    cpl_v = gv_couple_dans(v, cu, cy)                    # (∅,v)∈G_v
    # (∅,v)∈G_v ⇒ (∅,v)∈G_{v'}  via Leibniz S6 sur le 2ᵉ argument de ∈
    leib = N.s6(Gv, Gvp, w, appartient(E.couple(E.VIDE, vv), var(w)))
    cpl_vp = N.modus_ponens(cpl_v, equivalence_avant(N.modus_ponens(h, leib)))   # (∅,v)∈G_{v'}
    # ((∅,v)∈G_{v'}) ⇔ (∅∈{∅} et v=T'[∅]=v')   (membre_graphe_terme sur G_{v'})
    mem = membre_graphe_terme(one, vvp, cu, cy, "x", "yb")    # ((cu,cy)∈G_{v'}) ⇔ (cu∈{∅} et cy=v')
    mem_all = N.generalisation(cu, N.generalisation(cy, mem))
    mem_inst = instancie(instancie(mem_all, E.VIDE), vv)      # ((∅,v)∈G_{v'}) ⇔ (∅∈{∅} et v=v')
    v_eq_vp = conjonction_elim_droite(
        N.modus_ponens(cpl_vp, equivalence_avant(mem_inst)))  # v=v'
    return N.loi_deduction(egal(Gv, Gvp), v_eq_vp)            # (G_v=G_{v'}) ⇒ (v=v')


# ═══════════════════════════════════════════════════════════════════════════════
# PALIER 2 : la RÉCIPROQUE de l'évaluation   η : A → 𝓕({∅}; A),  v ↦ ((G_v,{∅}),A)
# ═══════════════════════════════════════════════════════════════════════════════
def _eta_triple_A(v, a):
    """ω_A(v) := ((G_v, {∅}), A)  =  l'application ∅... pardon {∅}→A de valeur v.

    C'est le triple de 𝓕({∅};A) image de v par η.  Variable de fonction = « c »
    (le nom de v) ; A est un paramètre libre."""
    return E.couple(E.couple(_gv(v), UN_SOURCE()), _t(a))


def _eta(a):
    """η := graphe_terme(A, ((G_c,{∅}),A), "c")  = graphe de v ↦ ((G_v,{∅}),A).

    Variable de fonction « c » ; le terme-valeur ne contient pas les liants
    internes u,v,z,x,y,w (G_c utilise « x », et « c » est la variable de fonction)."""
    va = _t(a)
    return E.graphe_terme(va, _eta_triple_A(var("c"), va), "c")


# ── PALIER 2.a : η fonctionnel ────────────────────────────────────────────────
def eta_fonctionnel(a="A"):
    """⊢ est_fonctionnel(η),  η = v↦((G_v,{∅}),A).   (cas C54, valeur = triple.)"""
    va = _t(a)
    return graphe_terme_fonctionnel(va, _eta_triple_A(var("c"), va), "c", "y")


# ── PALIER 2.b : dom η = A ────────────────────────────────────────────────────
def eta_domaine(a="A"):
    """⊢ dom(η) = A.   (η est définie sur tout A ; clos.)"""
    va = _t(a)
    return graphe_terme_domaine(va, _eta_triple_A(var("c"), va), "c", "y", "z")


# ── PALIER 2.c : η(u) = ((G_u,{∅}),A)  pour u∈A ───────────────────────────────
def eta_valeur(a="A", u="u"):
    """{u ∈ A} ⊢ η(u) = ((G_u,{∅}),A).   (la valeur de η en u est le triple image.)"""
    va = _t(a)
    return graphe_terme_valeur(va, _eta_triple_A(var("c"), va), u, "c", "y")


# ── PALIER 2.d : η injectif sur A ─────────────────────────────────────────────
def eta_injective(a="A"):
    """⊢ injective_dans(η, A).   (η est injective : η(u)=η(u') ⇒ u=u'.)

    η(u)=((G_u,{∅}),A), η(u')=((G_{u'},{∅}),A) (eta_valeur).  De η(u)=η(u') :
    ((G_u,{∅}),A)=((G_{u'},{∅}),A) ⇒ (G_u,{∅})=(G_{u'},{∅}) [composantes]
    ⇒ G_u=G_{u'} [composantes] ⇒ u=u' [gv_injectif]."""
    va = _t(a)
    vu, vup = var("u"), var("up")
    eta = _eta(a)
    one = UN_SOURCE()
    Gu, Gup = _gv(vu), _gv(vup)
    tu = _eta_triple_A(vu, va)        # ((G_u,{∅}),A)
    tup = _eta_triple_A(vup, va)      # ((G_{u'},{∅}),A)
    hyp = et(et(appartient(vu, va), appartient(vup, va)),
             egal(E.valeur(eta, vu), E.valeur(eta, vup)))
    h = N.assume(hyp)
    uinA = conjonction_elim_gauche(conjonction_elim_gauche(h))    # u∈A
    upinA = conjonction_elim_droite(conjonction_elim_gauche(h))   # u'∈A
    val_eq = conjonction_elim_droite(h)                          # η(u)=η(u')
    # η(u)=((G_u,{∅}),A) et η(u')=((G_{u'},{∅}),A)  (décharger u∈A / u'∈A)
    eu = N.modus_ponens(uinA, N.loi_deduction(appartient(vu, va), eta_valeur(a, "u")))
    eup = N.modus_ponens(upinA, N.loi_deduction(appartient(vup, va), eta_valeur(a, "up")))
    # ((G_u,{∅}),A) = η(u) = η(u') = ((G_{u'},{∅}),A)
    tu_eu = N.modus_ponens(eu, symetrie(E.valeur(eta, vu), tu))   # tu=η(u)
    tu_tup = composer_egalites(composer_egalites(tu_eu, val_eq), eup)   # tu=tup
    # tu=tup ⇒ (G_u,{∅})=(G_{u'},{∅}) et A=A   [couple_egal_implique_composantes]
    comps1 = N.modus_ponens(tu_tup,
        couple_egal_implique_composantes(E.couple(Gu, one), va, E.couple(Gup, one), va))
    pair_eq = conjonction_elim_gauche(comps1)                    # (G_u,{∅})=(G_{u'},{∅})
    # (G_u,{∅})=(G_{u'},{∅}) ⇒ G_u=G_{u'} et {∅}={∅}
    comps2 = N.modus_ponens(pair_eq,
        couple_egal_implique_composantes(Gu, one, Gup, one))
    Gu_eq = conjonction_elim_gauche(comps2)                      # G_u=G_{u'}
    u_up = N.modus_ponens(Gu_eq, gv_injectif(vu, vup))           # u=u'
    inner = N.loi_deduction(hyp, u_up)
    return N.generalisation("u", N.generalisation("up", inner))  # injective_dans(η, A)


# ═══════════════════════════════════════════════════════════════════════════════
# PALIER 3 (préparation) :  caractérisation du support de G_v
#   z ∈ G_v ⇔ z = (∅, v)
# ═══════════════════════════════════════════════════════════════════════════════
def gv_membre(v="c", z="z", cu="cu", cy="cy"):
    """⊢ (z ∈ G_v) ⇔ (z = (∅, v)).   (le graphe constant a pour seul élément (∅,v).)

    z∈G_v ⇔ (∃cu)(∃cy)(z=(cu,cy) et cu∈{∅} et cy=v)  [axiome graphe-terme].
      ⇒ : du corps, cu∈{∅} ⇒ cu=∅, cy=v, donc z=(cu,cy)=(∅,v) ; ∃-élim.
      ⇐ : z=(∅,v) ⇒ témoins cu:=∅ (∈{∅}), cy:=v (=v)."""
    vv, vz = _t(v), _t(z)
    one = UN_SOURCE()
    G = _gv(v)
    vcu, vcy = var(cu), var(cy)
    from bourbaki.ensembles.fonctions.ii_3_6_fonction_terme.ensembles_fonction_terme import _inst_axiome
    inst = _inst_axiome(one, vv, vz, cu, cy)    # z∈G_v ⇔ (∃cu)(∃cy)(z=(cu,cy) et cu∈{∅} et cy=v)
    body = et(et(egal(vz, E.couple(vcu, vcy)), appartient(vcu, one)), egal(vcy, vv))
    z_eq = egal(vz, E.couple(E.VIDE, vv))       # z=(∅,v)
    # ── ⇒ : (∃cu)(∃cy)body ⇒ z=(∅,v) ───────────────────────────────────────────
    hb = N.assume(body)
    z_cucy = conjonction_elim_gauche(conjonction_elim_gauche(hb))   # z=(cu,cy)
    cu_in = conjonction_elim_droite(conjonction_elim_gauche(hb))    # cu∈{∅}
    cy_v = conjonction_elim_droite(hb)                             # cy=v
    cu_vide = N.modus_ponens(cu_in, equivalence_avant(singleton_membre(vcu, E.VIDE)))  # cu=∅
    # (cu,cy)=(∅,cy)  (congruence sur 1ʳᵉ coordonnée, trou w)
    cucy_0cy = N.modus_ponens(cu_vide, congruence_terme(vcu, E.VIDE, E.couple(var("w"), vcy)))
    # (∅,cy)=(∅,v)  (congruence sur 2ᵉ coordonnée)
    z0cy_0v = N.modus_ponens(cy_v, congruence_terme(vcy, vv, E.couple(E.VIDE, var("w"))))
    z_0v = composer_egalites(z_cucy, composer_egalites(cucy_0cy, z0cy_0v))   # z=(∅,v)
    fwd = existe_elimination(existe_elimination(
        N.loi_deduction(body, z_0v), cy), cu)    # (∃cu)(∃cy)body ⇒ z=(∅,v)
    fwd2 = syllogisme(equivalence_avant(inst), fwd)                # z∈G_v ⇒ z=(∅,v)
    # ── ⇐ : z=(∅,v) ⇒ z∈G_v  via témoins cu:=∅, cy:=v ───────────────────────────
    hz = N.assume(z_eq)
    vide_in = membre_paire_gauche(E.VIDE, E.VIDE)                 # ∅∈{∅}
    # corps témoin (cu:=∅, cy:=v) : (z=(∅,v) et ∅∈{∅} et v=v)
    wit = conjonction_intro(conjonction_intro(hz, vide_in), N.reflexivite(vv))
    body_cuvide = subst_f(E.VIDE, cu, body)      # (cu:=∅) body  (libre cy)
    ex_cy = N.modus_ponens(wit, N.s5(body_cuvide, vv, cy))       # (∃cy)(cu:=∅)body
    ex_all = N.modus_ponens(ex_cy, N.s5(existe(cy, body), E.VIDE, cu))   # (∃cu)(∃cy)body
    in_G = N.modus_ponens(ex_all, equivalence_arriere(inst))     # z∈G_v
    bwd = N.loi_deduction(z_eq, in_G)                            # z=(∅,v) ⇒ z∈G_v
    return conjonction_intro(fwd2, bwd)                         # z∈G_v ⇔ z=(∅,v)

