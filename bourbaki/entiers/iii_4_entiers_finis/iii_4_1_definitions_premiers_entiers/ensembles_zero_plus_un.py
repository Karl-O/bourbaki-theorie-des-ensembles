"""§III.3 / §III.4 — VERS « 0 + 1 = 1 » au niveau ENSEMBLISTE puis CARDINAL.

Objectif (E.III.4.1, premiers entiers) : justifier  1 = 0 + 1  au niveau des
ensembles et des cardinaux, en RESTANT au plus près de Bourbaki et sans rien
postuler (PROUVE == certifié noyau).  Brique de base réutilisable, puis la somme
0 ⊔ 1 = ∅ ⊔ {∅}.

────────────────────────────────────────────────────────────────────────────────
LEMME GÉNÉRIQUE (réutilisable) — DEUX SINGLETONS SONT ÉQUIPOTENTS :

        ⊢ Eq({a}, {b})        (a, b termes quelconques).

Témoin = le graphe de la fonction CONSTANTE  C := graphe_terme({a}, b, "x")  qui
envoie l'unique élément a de {a} sur b (T(x) = b ne dépend pas de x).  Les 4
conjoints de est_bijection_de(C, {a}, {b}) :
  • const_graphe_fonctionnel   (clos)  — C fonctionnel (graphe d'un terme) ;
  • const_graphe_domaine       (clos)  — dom C = {a} ;
  • const_graphe_valeur        {u∈{a}} — C(u) = b ;
  • const_graphe_injective     (clos)  — injective_dans(C, {a}) [domaine singleton :
        u, u'∈{a} ⇒ u=a=u' ⇒ u=u', sans même utiliser la valeur] ;
  • const_graphe_image         (clos)  — image(C, {a}) = {b}  [z∈C⟨{a}⟩ ⇔ (∃t)(t∈{a}
        et z=b) ⇔ z=b ⇔ z∈{b}, car {a}≠∅ a le témoin a] ;
  • eq_singletons              (clos)  — Eq({a}, {b})  (S5 sur est_bijection_de).

────────────────────────────────────────────────────────────────────────────────
APPLICATION — « 0 + 1 = 1 » :

  • somme_zero_un_egale_singleton (clos) — ∅ ⊔ {∅} = {(∅, 1)}  [égalité d'ENSEMBLES,
        par extension : z∈∅⊔{∅} ⇔ (z=(∅,1)) ⇔ z∈{(∅,1)} ; la copie gauche ∅×{0} est
        vide, la copie droite {∅}×{1} se réduit à {(∅,1)}] ;
  • eq_somme_zero_un              (clos) — Eq(∅ ⊔ {∅}, {∅})  [transport de
        somme_zero_un_egale_singleton + eq_singletons({(∅,1)},∅) puis Eq réflexive] ;
  • card_somme_zero_un           (clos) — Card(∅ ⊔ {∅}) = Card({∅})
        = somme_cardinale_binaire(∅, {∅}) = Card({∅})   [Proposition 1, sens direct].

C'est « 0 + 1 = 1 » comme CARDINAUX des ensembles ∅ ⊔ {∅} et {∅}.

────────────────────────────────────────────────────────────────────────────────
PONT VERS Fini(0) — RÉSOLU (round 13, ensembles_fini_zero.py) :

  Le successeur est désormais DÉFINI FIDÈLEMENT comme la somme cardinale
  successeur(𝔞) := 𝔞 + 1 := somme_cardinale_binaire(𝔞, {∅}) = Card(𝔞 ⊔ {∅})
  (ensembles_entiers.py, plus de terme opaque app("succ",·)).  Combiné au lemme
  card_somme_zero_un (Card(∅⊔{∅}) = Card({∅})) ci-dessous et à Card(∅) = ∅
  (cardinal_vide_egale_vide, ensembles_fini_zero), cela donne :

        successeur(0) = Card(Card∅ ⊔ {∅}) = Card(∅ ⊔ {∅}) = Card({∅}) = 1,

  d'où 0 ≠ 0+1 (Card∅ ≠ Card{∅}, via vide_non_equipotent_singleton + Prop. 1) et
  Fini(0) (0 EST UN ENTIER NATUREL).  Voir ensembles_fini_zero.py.
"""
from __future__ import annotations

from bourbaki.logique.formule import (Terme, var, egal, et, non, appartient, existe, subst_t, subst_f)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.logique.tactiques.tactiques_abrege import a_implique_a, syllogisme
from bourbaki.logique.tactiques.tactiques_abrege2 import (conjonction_intro, conjonction_elim_gauche,
                               conjonction_elim_droite, equivalence_avant,
                               equivalence_arriere, equivalence_transitivite,
                               instancie)
from bourbaki.logique.tactiques.tactiques_abrege_egalite import symetrie, composer_egalites, congruence_terme
from bourbaki.logique.tactiques.tactiques_abrege_quantif import existe_elimination, alpha_existe
from bourbaki.ensembles.fonctions.ii_3_6_fonction_terme.ensembles_fonction_terme import membre_graphe_terme, graphe_terme_fonctionnel
from bourbaki.cardinaux.ensembles_cantor import graphe_terme_domaine, graphe_terme_valeur
from bourbaki.ensembles.base.ensembles_couples import singleton_membre
from bourbaki.ensembles.ensembles_theoremes import egalite_par_extension
from bourbaki.cardinaux.ensembles_cardinaux import est_bijection_de, equipotent, cardinal


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# ═══════════════════════════════════════════════════════════════════════════════
# Le graphe de la fonction CONSTANTE  C : {a} → b,  x ↦ b
# ═══════════════════════════════════════════════════════════════════════════════
def _const_graphe(a, b):
    """C := graphe_terme({a}, b, "x")  = graphe de la fonction constante x ↦ b sur {a}."""
    return E.graphe_terme(E.singleton(_t(a)), _t(b), "x")


# ── Conjoint 1 : C fonctionnel ────────────────────────────────────────────────
def const_graphe_fonctionnel(a="a", b="b"):
    """⊢ C est fonctionnel,  C = graphe de x↦b sur {a}.   (cas T=b de C54, clos.)"""
    return graphe_terme_fonctionnel(E.singleton(_t(a)), _t(b), "x", "y")


# ── Conjoint 2 : dom C = {a} ──────────────────────────────────────────────────
def const_graphe_domaine(a="a", b="b"):
    """⊢ dom(C) = {a}.   (la fonction constante est définie sur tout {a} ; clos.)"""
    return graphe_terme_domaine(E.singleton(_t(a)), _t(b), "x", "y", "z")


# ── Valeur : C(u) = b pour u∈{a} ──────────────────────────────────────────────
def const_graphe_valeur(a="a", b="b", u="u"):
    """{u ∈ {a}} ⊢ C(u) = b.   (T[u] = (u|x)b = b car b sans x ; clos sous u∈{a}.)"""
    return graphe_terme_valeur(E.singleton(_t(a)), _t(b), u, "x", "y")


# ── Conjoint 3 : injective_dans(C, {a})  (domaine singleton) ──────────────────
def const_graphe_injective(a="a", b="b"):
    """⊢ injective_dans(C, {a}).   (domaine SINGLETON : tout u∈{a} vaut a, donc u=u'.)

    injective_dans(C,{a}) = (∀u)(∀u')((u∈{a} et u'∈{a} et C(u)=C(u')) ⇒ u=u').
    De u∈{a} on tire u=a (singleton_membre), de u'∈{a} on tire u'=a, d'où u=a=u'.
    (La valeur C(u)=C(u') n'est même pas nécessaire : un singleton est trivialement
    le domaine d'une application injective.)"""
    va = _t(a)
    C = _const_graphe(a, b)
    vu, vup = var("u"), var("up")
    sa = E.singleton(va)
    hyp = et(et(appartient(vu, sa), appartient(vup, sa)),
             egal(E.valeur(C, vu), E.valeur(C, vup)))
    h = N.assume(hyp)
    uin = conjonction_elim_gauche(conjonction_elim_gauche(h))      # u∈{a}
    upin = conjonction_elim_droite(conjonction_elim_gauche(h))     # u'∈{a}
    u_eq_a = N.modus_ponens(uin, equivalence_avant(singleton_membre(vu, va)))    # u=a
    up_eq_a = N.modus_ponens(upin, equivalence_avant(singleton_membre(vup, va))) # u'=a
    a_eq_up = N.modus_ponens(up_eq_a, symetrie(vup, va))          # a=u'
    u_eq_up = composer_egalites(u_eq_a, a_eq_up)                  # u=a=u'
    inner = N.loi_deduction(hyp, u_eq_up)
    return N.generalisation("u", N.generalisation("up", inner))   # injective_dans(C,{a})


# ── Conjoint 4 : image(C, {a}) = {b}  (surjectivité sur {b}) ──────────────────
def const_graphe_image(a="a", b="b"):
    """⊢ image(C, {a}) = {b}.   (l'image de la fonction constante x↦b sur {a} est {b}.)

    z∈C⟨{a}⟩ ⇔ (∃t)(t∈{a} et (t,z)∈C)  [AXIOME_IMAGE, liant interne renommé t]
            ⇔ (∃t)(t∈{a} et (t∈{a} et z=b))  [membre_graphe_terme : (t,z)∈C ⇔ (t∈{a}
                                                et z=T[t]=b)]
            ⇔ z=b   [⇒ : projeter z=b ; ⇐ : témoin t:=a∈{a} (réflexivité)]
            ⇔ z∈{b} [singleton_membre].  Par extension (liant z, A1)."""
    va, vb = _t(a), _t(b)
    C = _const_graphe(a, b)
    sa, sb = E.singleton(va), E.singleton(vb)
    vz, vt = var("z"), var("t")
    # ── z∈C⟨{a}⟩ ⇔ (∃t)(t∈{a} et (t,z)∈C) ─────────────────────────────────────
    ax_img = N.axiome(E.theorie_ensembles(), E.AXIOME_IMAGE)
    img_car0 = instancie(instancie(instancie(ax_img, C), sa), vz)   # z∈C⟨{a}⟩ ⇔ (∃x)(x∈{a} et (x,z)∈C)
    inner_x = et(appartient(var("x"), sa), appartient(E.couple(var("x"), vz), C))
    ren = alpha_existe("x", "t", inner_x)
    img_car = equivalence_transitivite(img_car0, ren)              # z∈C⟨{a}⟩ ⇔ (∃t)(t∈{a} et (t,z)∈C)
    # ── (t,z)∈C ⇔ (t∈{a} et z=b)  [T[t]=b car b sans x] ───────────────────────
    mem = membre_graphe_terme(sa, vb, "t", "z", "x", "yb")         # ((t,z)∈C) ⇔ (t∈{a} et z=b)
    # body : t∈{a} et (t,z)∈C  ;  full : t∈{a} et (t∈{a} et z=b)
    body = et(appartient(vt, sa), appartient(E.couple(vt, vz), C))
    from bourbaki.logique.tactiques.tactiques_abrege2 import et_congruence_droite
    body_eq = et_congruence_droite(appartient(vt, sa), mem)        # body ⇔ (t∈{a} et (t∈{a} et z=b))
    from bourbaki.logique.tactiques.tactiques_abrege_quantif import congruence_existe
    ex_body = congruence_existe(body_eq, "t")                      # (∃t)body ⇔ (∃t)full
    full = et(appartient(vt, sa), et(appartient(vt, sa), egal(vz, vb)))
    # ── (∃t)full ⇔ (z=b) ──────────────────────────────────────────────────────
    z_eq_b = egal(vz, vb)
    # ⇒ : full ⇒ z=b (projection), puis ∃-élim
    hf = N.assume(full)
    z_b = conjonction_elim_droite(conjonction_elim_droite(hf))     # z=b
    fwd = existe_elimination(N.loi_deduction(full, z_b), "t")      # (∃t)full ⇒ z=b
    # ⇐ : z=b ⇒ (∃t)full  via témoin t:=a (a∈{a} par réflexivité)
    from bourbaki.ensembles.base.ensembles_couples import membre_paire_gauche
    a_in_sa = membre_paire_gauche(va, va)                         # a∈{a,a}={a}
    hzb = N.assume(z_eq_b)
    wit = conjonction_intro(a_in_sa, conjonction_intro(a_in_sa, hzb))  # (a|t)full
    full_a = subst_f(va, "t", full)                              # (t|→a)full
    bwd = N.loi_deduction(z_eq_b, N.modus_ponens(wit, N.s5(full, va, "t")))  # z=b ⇒ (∃t)full
    ex_zb = conjonction_intro(fwd, bwd)                          # (∃t)full ⇔ z=b
    # ── z=b ⇔ z∈{b} ───────────────────────────────────────────────────────────
    sb_mem = singleton_membre(vz, vb)                            # z∈{b} ⇔ z=b
    zb_zsb = conjonction_intro(equivalence_arriere(sb_mem), equivalence_avant(sb_mem))  # z=b ⇔ z∈{b}
    # ── chaîne complète : z∈C⟨{a}⟩ ⇔ z∈{b} ────────────────────────────────────
    chain = equivalence_transitivite(img_car,
              equivalence_transitivite(ex_body,
                equivalence_transitivite(ex_zb, zb_zsb)))         # z∈C⟨{a}⟩ ⇔ z∈{b}
    char_img = N.generalisation("z", chain)
    inzsb = appartient(vz, sb)
    selfsb = N.generalisation("z", conjonction_intro(a_implique_a(inzsb), a_implique_a(inzsb)))
    return egalite_par_extension(char_img, selfsb, E.image(C, sa), sb, "z")


# ── est_bijection_de(C, {a}, {b})  puis  Eq({a}, {b}) ─────────────────────────
def const_est_bijection(a="a", b="b"):
    """⊢ est_bijection_de(C, {a}, {b}).   (C = x↦b est une bijection {a}→{b}.)"""
    func = const_graphe_fonctionnel(a, b)
    dom = const_graphe_domaine(a, b)
    inj = const_graphe_injective(a, b)
    img = const_graphe_image(a, b)
    return conjonction_intro(conjonction_intro(func, dom),
                             conjonction_intro(inj, img))


def eq_singletons(a="a", b="b"):
    """⊢ Eq({a}, {b}).   (DEUX SINGLETONS SONT ÉQUIPOTENTS, a, b termes quelconques.)

    Témoin = le graphe constant C : {a}→{b}, x↦b ; S5 sur est_bijection_de(F,{a},{b})
    donne (∃F)bij = Eq({a},{b})."""
    va, vb = _t(a), _t(b)
    sa, sb = E.singleton(va), E.singleton(vb)
    C = _const_graphe(a, b)
    bij = const_est_bijection(a, b)
    return N.modus_ponens(bij, N.s5(est_bijection_de(var("F"), sa, sb), C, "F"))


# ═══════════════════════════════════════════════════════════════════════════════
# « 0 + 1 = 1 » — somme disjointe ∅ ⊔ {∅} = {(∅, 1)}  puis cardinaux
# ═══════════════════════════════════════════════════════════════════════════════
def somme_zero_un_egale_singleton():
    """⊢ (∅ ⊔ {∅}) = {(∅, 1)}.   (la somme 0 ⊔ 1 est le singleton de (∅,1) ; égalité
    d'ENSEMBLES, par extension.)

    z∈∅⊔{∅} ⇔ ((∃u)(u∈∅ et z=(u,0)) ou (∃v)(v∈{∅} et z=(v,1)))
            [membre_somme_caracterise].  Le disjoint GAUCHE est toujours faux (u∈∅
    impossible, AXIOME_VIDE).  Le disjoint DROIT (∃v)(v∈{∅} et z=(v,1)) équivaut à
    z=(∅,1) : v∈{∅} ⇔ v=∅ (singleton_membre), d'où z=(v,1)=(∅,1) ; réciproquement
    le témoin v:=∅.  Donc z∈∅⊔{∅} ⇔ z=(∅,1) ⇔ z∈{(∅,1)}."""
    from bourbaki.ensembles.familles.ensembles_somme_disjointe import (somme_disjointe, membre_somme_caracterise,
                                           ZERO, UN)
    vide = E.VIDE
    sing = E.singleton(vide)                 # {∅} = 1 (marqueur ensembliste)
    AB = somme_disjointe(vide, sing)         # ∅ ⊔ {∅}
    cpl = E.couple(vide, UN)                 # (∅, 1)
    scpl = E.singleton(cpl)                  # {(∅, 1)}
    from bourbaki.logique.formule import ou
    vz, vu, vv = var("z"), var("u"), var("v")
    car = membre_somme_caracterise(vide, sing, vz)   # z∈∅⊔{∅} ⇔ (exG ou exD)
    # disjonction caractérisante (construite EXPLICITEMENT, mêmes liants u/v que le lemme)
    exG = existe("u", et(appartient(vu, vide), egal(vz, E.couple(vu, ZERO))))   # (∃u)(u∈∅ et z=(u,0))
    exD = existe("v", et(appartient(vv, sing), egal(vz, E.couple(vv, UN))))     # (∃v)(v∈{∅} et z=(v,1))
    disj = ou(exG, exD)
    z_eq_cpl = egal(vz, cpl)                          # z=(∅,1)

    # ── (exG ou exD) ⇔ z=(∅,1) ────────────────────────────────────────────────
    # ⇒ : cas. exG ⇒ z=(∅,1) par ex falso (u∈∅ impossible) ; exD ⇒ z=(∅,1).
    ax_vide = N.axiome(E.theorie_ensembles(), E.AXIOME_VIDE)      # (∀z)¬(z∈∅)
    # branche GAUCHE : (u∈∅ et z=(u,0)) ⇒ z=(∅,1)  par ex falso
    bodyG = et(appartient(vu, vide), egal(vz, E.couple(vu, ZERO)))
    hbG = N.assume(bodyG)
    u_in_vide = conjonction_elim_gauche(hbG)                      # u∈∅
    nu = instancie(ax_vide, vu)                                  # ¬(u∈∅)
    falsoG = N.modus_ponens(u_in_vide, N.modus_ponens(nu, N.s2(non(appartient(vu, vide)), z_eq_cpl)))
    impG = existe_elimination(N.loi_deduction(bodyG, falsoG), "u")   # exG ⇒ z=(∅,1)
    # branche DROITE : (v∈{∅} et z=(v,1)) ⇒ z=(∅,1)
    bodyD = et(appartient(vv, sing), egal(vz, E.couple(vv, UN)))
    hbD = N.assume(bodyD)
    v_in = conjonction_elim_gauche(hbD)                          # v∈{∅}
    z_eq_v1 = conjonction_elim_droite(hbD)                       # z=(v,1)
    v_eq_vide = N.modus_ponens(v_in, equivalence_avant(singleton_membre(vv, vide)))  # v=∅
    # (v,1)=(∅,1)  via congruence (trou w sur la 1ʳᵉ coordonnée)
    v1_eq_01 = N.modus_ponens(v_eq_vide, congruence_terme(vv, vide, E.couple(var("w"), UN)))
    z_eq_01 = composer_egalites(z_eq_v1, v1_eq_01)               # z=(∅,1)
    impD = existe_elimination(N.loi_deduction(bodyD, z_eq_01), "v")  # exD ⇒ z=(∅,1)
    from bourbaki.logique.tactiques.tactiques_abrege2 import cas
    h_disj = N.assume(disj)                                      # (exG ou exD)
    fwd = N.loi_deduction(disj, cas(h_disj, impG, impD))        # (exG ou exD) ⇒ z=(∅,1)
    # ⇐ : z=(∅,1) ⇒ (exG ou exD)  via le disjoint DROIT, témoin v:=∅
    hz = N.assume(z_eq_cpl)                                      # z=(∅,1)
    vide_in_sing = membre_singleton_vide()                      # ∅∈{∅}
    wit_v = conjonction_intro(vide_in_sing, hz)                 # ∅∈{∅} et z=(∅,1) = (v|→∅)bodyD
    ex_v = N.modus_ponens(wit_v, N.s5(bodyD, vide, "v"))        # (∃v)bodyD = exD
    bwd = N.loi_deduction(z_eq_cpl, _disj_droite_intro(ex_v, exG, exD))
    eq_disj = conjonction_intro(fwd, bwd)                       # (exG ou exD) ⇔ z=(∅,1)
    # ── z∈∅⊔{∅} ⇔ z=(∅,1) ⇔ z∈{(∅,1)} ─────────────────────────────────────────
    z_in_eq = equivalence_transitivite(car, eq_disj)           # z∈∅⊔{∅} ⇔ z=(∅,1)
    scpl_mem = singleton_membre(vz, cpl)                       # z∈{(∅,1)} ⇔ z=(∅,1)
    z_in_scpl = equivalence_transitivite(z_in_eq,
        conjonction_intro(equivalence_arriere(scpl_mem), equivalence_avant(scpl_mem)))  # z∈∅⊔{∅} ⇔ z∈{(∅,1)}
    char = N.generalisation("z", z_in_scpl)
    in_scpl = appartient(vz, scpl)
    self_scpl = N.generalisation("z", conjonction_intro(a_implique_a(in_scpl), a_implique_a(in_scpl)))
    return egalite_par_extension(char, self_scpl, AB, scpl, "z")


def _disj_droite_intro(thm_right, left, right):
    """⊢ R ⟹ ⊢ (L ou R).   (introduction du disjoint droit : S2 puis S3.)"""
    or_rl = N.modus_ponens(thm_right, N.s2(right, left))        # R ⇒ (R ou L), appliqué : (R ou L)
    return N.modus_ponens(or_rl, N.s3(right, left))            # (L ou R)


def membre_singleton_vide():
    """⊢ ∅ ∈ {∅}.   (l'élément ∅ appartient à son singleton, réflexivité.)"""
    from bourbaki.ensembles.base.ensembles_couples import membre_paire_gauche
    return membre_paire_gauche(E.VIDE, E.VIDE)                  # ∅∈{∅,∅}={∅}


# ── Eq(∅ ⊔ {∅}, {∅}) ──────────────────────────────────────────────────────────
def eq_somme_zero_un():
    """⊢ Eq(∅ ⊔ {∅}, {∅}).   (« 0 + 1 = 1 » au niveau ENSEMBLISTE, à équipotence près.)

    ∅⊔{∅} = {(∅,1)} (somme_zero_un_egale_singleton) ; Eq({(∅,1)}, {∅}) (eq_singletons,
    deux singletons équipotents) ; on transporte le 1ᵉʳ argument de Eq par l'égalité
    d'ensembles via S6 (Leibniz)."""
    from bourbaki.ensembles.familles.ensembles_somme_disjointe import somme_disjointe, UN
    vide = E.VIDE
    sing = E.singleton(vide)                 # {∅}
    AB = somme_disjointe(vide, sing)         # ∅ ⊔ {∅}
    cpl = E.couple(vide, UN)                 # (∅, 1)
    scpl = E.singleton(cpl)                  # {(∅, 1)}
    eq_set = somme_zero_un_egale_singleton()             # ∅⊔{∅} = {(∅,1)}
    eq_sing = eq_singletons(cpl, vide)                   # Eq({(∅,1)}, {∅})
    # Eq(∅⊔{∅}, {∅})  via Leibniz : (∅⊔{∅}={(∅,1)}) ⇒ (Eq(∅⊔{∅},{∅}) ⇔ Eq({(∅,1)},{∅}))
    leib = N.s6(AB, scpl, "w", equipotent(var("w"), sing))
    equiv_eq = N.modus_ponens(eq_set, leib)              # Eq(∅⊔{∅},{∅}) ⇔ Eq({(∅,1)},{∅})
    return N.modus_ponens(eq_sing, equivalence_arriere(equiv_eq))   # Eq(∅⊔{∅}, {∅})


# ── Card(∅ ⊔ {∅}) = Card({∅})  =  0 + 1 = 1  (niveau CARDINAL) ─────────────────
def card_somme_zero_un():
    """⊢ Card(∅ ⊔ {∅}) = Card({∅}).   (« 0 + 1 = 1 » au niveau CARDINAL.)

    Card(∅⊔{∅}) = somme_cardinale_binaire(∅, {∅}) = « 0 + 1 », et Card({∅}) = « 1 ».
    Eq(∅⊔{∅}, {∅}) (eq_somme_zero_un) ; la Proposition 1 (sens direct, version TERME
    _prop1_direct_t) conclut Card(∅⊔{∅}) = Card({∅})."""
    from bourbaki.ensembles.familles.ensembles_somme_disjointe import somme_disjointe
    from bourbaki.cardinaux.arithmetique.ensembles_arith_cardinale import _prop1_direct_t
    vide = E.VIDE
    sing = E.singleton(vide)                 # {∅}
    AB = somme_disjointe(vide, sing)         # ∅ ⊔ {∅}
    eq = eq_somme_zero_un()                              # Eq(∅⊔{∅}, {∅})
    prop1 = _prop1_direct_t(AB, sing)                   # Eq(∅⊔{∅},{∅}) ⇒ Card(∅⊔{∅})=Card({∅})
    return N.modus_ponens(eq, prop1)                    # Card(∅⊔{∅}) = Card({∅})


__all__ = ["const_graphe_fonctionnel", "const_graphe_domaine", "const_graphe_valeur",
           "const_graphe_injective", "const_graphe_image", "const_est_bijection",
           "eq_singletons",
           "somme_zero_un_egale_singleton", "membre_singleton_vide",
           "eq_somme_zero_un", "card_somme_zero_un"]
