"""§III.3.3 — Équipotence canonique d'un ensemble avec sa COPIE MARQUÉE  A ≅ A×{m}.

Brique RÉUTILISABLE sur le chemin de la Proposition 8 (§III.3.4, le successeur
cardinal est injectif).  La somme disjointe est  A ⊔ B := (A×{0}) ∪ (B×{1})
(ensembles_somme_disjointe), donc l'argument « back-and-forth » de la Prop. 8
manipule sans cesse les copies marquées A×{0}, B×{1}.  Le pont élémentaire dont
il a besoin est l'équipotence CANONIQUE

        Eq(A, A×{m})        (m = marqueur quelconque, en pratique 0 = ∅, 1 = {∅}),

réalisée par l'application  a ↦ (a, m)  (un plongement bijectif de A sur la copie
A×{m}).  Son graphe est le GRAPHE DE TERME (clos, AUCUN axiome nouveau)

        Δ_m := graphe_terme(A, (a, m), "a") = { (a, (a,m)) | a ∈ A }.

C'est un graphe de terme PROPRE (valeur fermée (a,m), sans sélecteur ni
marqueur-disjonction), donc beaucoup plus simple que la bijection-somme K de
ensembles_somme_equipotence : les quatre conjoints (fonctionnel, domaine,
injectif, image) se prouvent directement par la machinerie graphe_terme_*
(ensembles_cantor / ensembles_fonction_terme) + la caractérisation de
l'appartenance au produit (couple_dans_produit_ssi).

──────────────────────────────────────────────────────────────────────────────
THÉORÈMES CERTIFIÉS (chacun testé, cf. test_copie_marquee.py) :
  • copie_graphe_fonctionnel(A,m)  (clos)        — Δ_m est fonctionnel           ;
  • copie_graphe_domaine(A,m)      (clos)        — dom Δ_m = A                    ;
  • copie_graphe_valeur(A,m,a)     {a∈A}         — Δ_m(a) = (a,m)                 ;
  • copie_graphe_injective(A,m)    (clos)        — injective_dans(Δ_m, A)         ;
  • copie_graphe_image(A,m)        (clos)        — image(Δ_m, A) = A×{m}          ;
  • copie_est_bijection(A,m)       (clos)        — est_bijection_de(Δ_m,A,A×{m})  ;
  • eq_copie_marquee(A,m)          (clos)        — Eq(A, A×{m})                   ;
  • eq_copie_gauche(A)             (clos)        — Eq(A, A×{0})  (copie de gauche);
  • eq_copie_droite(B)             (clos)        — Eq(B, B×{1})  (copie de droite).

Ces équipotences sont EXACTEMENT le pont dont le cœur back-and-forth de la
Proposition 8 a besoin (« CAS 1 », où la bijection h envoie le marqueur sur le
marqueur : on restreint h aux copies de gauche A×{0}→B×{0} puis on transporte par
Eq(A,A×{0}) et Eq(B,B×{0})).  Le recollement complet par cas (CAS 1 + CAS 2 avec
échange a₀↦b₀, surgery de graphe sur un témoin ABSTRAIT h) reste REPORTÉ — c'est
la partie la plus dure, hors budget de cet agent (cf. note finale).
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (Terme, var, egal, et, appartient, existe, subst_t)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege import a_implique_a, syllogisme
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (conjonction_intro, conjonction_elim_gauche,
                               conjonction_elim_droite, equivalence_avant,
                               equivalence_arriere, equivalence_transitivite,
                               instancie)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (symetrie, composer_egalites,
                                          congruence_terme)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import (existe_elimination, alpha_existe)
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_6_fonction_terme.ensembles_fonction_terme import (membre_graphe_terme,
                                          graphe_terme_fonctionnel)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.cantor.ensembles_cantor import (graphe_terme_domaine, graphe_terme_valeur)
from bourbaki.ii_theorie_des_ensembles.ii_2_couples.ii_2_2_produit_deux_ensembles.ensembles_produit import couple_dans_produit_ssi
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_recollement_somme.ensembles_somme_disjointe import ZERO, UN, _dans_singleton
from bourbaki.ii_theorie_des_ensembles.ii_2_couples.ii_2_1_definition_couples.ensembles_couples import couple_egal_implique_composantes
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_theoremes import egalite_par_extension


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# ── Le terme « copie marquée » T(e) = (e, m) et son graphe Δ_m ────────────────
# Liant interne « e » (≠ des points u, up, t, p, q, z passés par les paliers et
# par membre_graphe_terme : évite toute capture quand un point se nomme « a »).
_BND = "e"


def _copie_terme(m, e=_BND):
    """T(e) := (e, m)   (valeur de l'application de copie e ↦ (e,m) ; liant « e »)."""
    return E.couple(var(e), _t(m))


def _copie_graphe(a_set, m):
    """Δ_m := graphe_terme(A, (e,m), "e") = { (e,(e,m)) | e ∈ A }."""
    return E.graphe_terme(_t(a_set), _copie_terme(m, _BND), _BND)


# ── PALIER 1 : Δ_m est fonctionnel  (clos) ────────────────────────────────────
def copie_graphe_fonctionnel(a_set="A", m=ZERO):
    """⊢ est_fonctionnel(Δ_m),  Δ_m = graphe de a↦(a,m).   (cas C54, clos.)

    Application directe de graphe_terme_fonctionnel : un graphe défini par un terme
    n'a qu'une valeur (e,m) par antécédent e."""
    return graphe_terme_fonctionnel(_t(a_set), _copie_terme(m, _BND), _BND, "y")


# ── PALIER 2 : dom Δ_m = A  (clos) ────────────────────────────────────────────
def copie_graphe_domaine(a_set="A", m=ZERO):
    """⊢ dom(Δ_m) = A.   (la copie est définie sur tout A ; clos.)

    Application directe de graphe_terme_domaine : a∈dom Δ_m ⇔ (∃y)((a,y)∈Δ_m) ⇔ a∈A."""
    return graphe_terme_domaine(_t(a_set), _copie_terme(m, _BND), _BND, "y", "z")


# ── PALIER 3 : Δ_m(a) = (a, m)  pour a∈A  (hyp a∈A) ───────────────────────────
def copie_graphe_valeur(a_set="A", m=ZERO, a="a"):
    """{a ∈ A} ⊢ Δ_m(a) = (a, m).   (la copie envoie a sur (a,m).)

    Application directe de graphe_terme_valeur : Δ_m(a)=T[a]=(a,m)."""
    return graphe_terme_valeur(_t(a_set), _copie_terme(m, _BND), a, _BND, "y")


# ── PALIER 4 : injective_dans(Δ_m, A)  (clos) ─────────────────────────────────
def copie_graphe_injective(a_set="A", m=ZERO):
    """⊢ injective_dans(Δ_m, A).   (la copie a↦(a,m) est injective sur A ; clos.)

    Sous {u∈A, u'∈A, Δ_m(u)=Δ_m(u')} : Δ_m(u)=(u,m), Δ_m(u')=(u',m) (palier valeur),
    donc (u,m)=(u',m) ; la Proposition 1 sur les couples
    (couple_egal_implique_composantes) en tire u=u'.  Liants u, up (forme défaut de
    injective_dans)."""
    va, vm = _t(a_set), _t(m)
    DX = _copie_graphe(a_set, m)
    vu, vup = var("u"), var("up")
    hyp = et(et(appartient(vu, va), appartient(vup, va)),
             egal(E.valeur(DX, vu), E.valeur(DX, vup)))
    h = N.assume(hyp)
    uinA = conjonction_elim_gauche(conjonction_elim_gauche(h))     # u∈A
    upinA = conjonction_elim_droite(conjonction_elim_gauche(h))    # u'∈A
    val_eq = conjonction_elim_droite(h)                            # Δ_m(u)=Δ_m(u')
    # Δ_m(u)=(u,m),  Δ_m(u')=(u',m)
    du = N.modus_ponens(uinA, N.loi_deduction(appartient(vu, va),
                                              copie_graphe_valeur(a_set, m, "u")))
    dup = N.modus_ponens(upinA, N.loi_deduction(appartient(vup, va),
                                                copie_graphe_valeur(a_set, m, "up")))
    cu, cup = E.couple(vu, vm), E.couple(vup, vm)
    # (u,m)=Δ_m(u)=Δ_m(u')=(u',m)
    cu_eq = composer_egalites(composer_egalites(
        N.modus_ponens(du, symetrie(E.valeur(DX, vu), cu)),        # (u,m)=Δ_m(u)
        val_eq), dup)                                              # (u,m)=(u',m)
    comps = N.modus_ponens(cu_eq, couple_egal_implique_composantes(vu, vm, vup, vm))
    u_eq_up = conjonction_elim_gauche(comps)                       # u=u'
    inner = N.loi_deduction(hyp, u_eq_up)
    return N.generalisation("u", N.generalisation("up", inner))    # injective_dans(Δ_m, A)


# ── PALIER 5 : image(Δ_m, A) = A×{m}  (surjectivité ; clos) ───────────────────
def copie_graphe_image(a_set="A", m=ZERO):
    """⊢ image(Δ_m, A) = A×{m}.   (la copie est surjective sur A×{m} ; clos.)

    z∈Δ_m⟨A⟩ ⇔ (∃t)(t∈A et (t,z)∈Δ_m) ⇔ (∃t)(t∈A et z=(t,m)) ⇔ z∈A×{m}.
    ⇒ : témoin t∈A, z=(t,m) ⇒ t∈A et m∈{m} ⇒ (t,m)∈A×{m} ⇒ z∈A×{m}.
    ⇐ : z∈A×{m} ⇒ z=(c,d), c∈A, d∈{m} ⇒ d=m ⇒ z=(c,m)=Δ_m(c) avec c∈A ⇒ z∈image."""
    va, vm = _t(a_set), _t(m)
    DX = _copie_graphe(a_set, m)
    AM = E.produit(va, E.singleton(vm))            # A×{m}
    T = _copie_terme(m, _BND)
    vz = var("z")
    # caractérisation de l'image (liant interne « x » de AXIOME_IMAGE → renommé « t »)
    ax_img = N.axiome(E.theorie_ensembles(), E.AXIOME_IMAGE)
    img_car0 = instancie(instancie(instancie(ax_img, DX), va), vz)
    inner_x = et(appartient(var("x"), va), appartient(E.couple(var("x"), vz), DX))
    ren = alpha_existe("x", "t", inner_x)
    img_car = equivalence_transitivite(img_car0, ren)   # z∈Δ_m⟨A⟩ ⇔ (∃t)(t∈A et (t,z)∈Δ_m)
    vt = var("t")
    # (t,z)∈Δ_m ⇔ (t∈A et z=T[t])=(t∈A et z=(t,m))  (membre_graphe_terme, corps « yb »)
    mem = membre_graphe_terme(va, T, "t", "z", _BND, "yb")   # ((t,z)∈Δ_m) ⇔ (t∈A et z=(t,m))
    Tt = subst_t(vt, _BND, T)                       # (t,m)

    # ── ⇒ : (∃t)(t∈A et (t,z)∈Δ_m) ⇒ z∈A×{m} ──────────────────────────────────
    bodyR = et(appartient(vt, va), appartient(E.couple(vt, vz), DX))
    hbR = N.assume(bodyR)
    t_in = conjonction_elim_gauche(hbR)             # t∈A
    cpl_in = conjonction_elim_droite(hbR)           # (t,z)∈Δ_m
    z_eq_Tt = conjonction_elim_droite(N.modus_ponens(cpl_in, equivalence_avant(mem)))  # z=(t,m)
    # (t,m)∈A×{m}  via couple_dans_produit_ssi  (t∈A et m∈{m})
    tm_in_prod = N.modus_ponens(conjonction_intro(t_in, _dans_singleton(vm)),
        equivalence_arriere(couple_dans_produit_ssi(vt, vm, va, E.singleton(vm))))   # (t,m)∈A×{m}
    # z∈A×{m} via Leibniz z=(t,m)
    z_in = N.modus_ponens(tm_in_prod, equivalence_arriere(N.modus_ponens(
        z_eq_Tt, N.s6(vz, Tt, "w", appartient(var("w"), AM)))))   # z∈A×{m}
    fwd_inner = existe_elimination(N.loi_deduction(bodyR, z_in), "t")  # (∃t)body ⇒ z∈A×{m}
    fwd = syllogisme(equivalence_avant(img_car), fwd_inner)      # z∈Δ_m⟨A⟩ ⇒ z∈A×{m}

    # ── ⇐ : z∈A×{m} ⇒ z∈Δ_m⟨A⟩ ────────────────────────────────────────────────
    # z∈A×{m} ⇔ (∃p)(∃q)(z=(p,q) et p∈A et q∈{m})  (AXIOME_PRODUIT)
    ax_prod = N.axiome(E.theorie_ensembles(), E.AXIOME_PRODUIT)
    prod_car = instancie(instancie(instancie(ax_prod, va), E.singleton(vm)), vz)
    vp, vq = var("p"), var("q")
    bodyP = et(et(egal(vz, E.couple(vp, vq)), appartient(vp, va)),
               appartient(vq, E.singleton(vm)))
    hbP = N.assume(bodyP)
    z_pq = conjonction_elim_gauche(conjonction_elim_gauche(hbP))   # z=(p,q)
    p_in = conjonction_elim_droite(conjonction_elim_gauche(hbP))   # p∈A
    q_in = conjonction_elim_droite(hbP)                            # q∈{m}
    # q∈{m} ⇒ q=m  (AXIOME_PAIRE : q∈{m,m} ⇔ (q=m ou q=m))
    ax_p = N.axiome(E.theorie_ensembles(), E.AXIOME_PAIRE)
    car_q = instancie(instancie(instancie(ax_p, vm), vm), vq)      # q∈{m,m} ⇔ (q=m ou q=m)
    q_or = N.modus_ponens(q_in, equivalence_avant(car_q))         # q=m ou q=m
    from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_recollement_somme.ensembles_somme_disjointe import _ou_idem
    q_eq_m = _ou_idem(q_or, egal(vq, vm))                         # q=m
    # z=(p,q)=(p,m)  (Leibniz q→m dans (p,·))
    pq_pm = N.modus_ponens(q_eq_m, congruence_terme(vq, vm, E.couple(vp, var("w"))))  # (p,q)=(p,m)
    z_pm = composer_egalites(z_pq, pq_pm)                         # z=(p,m)
    # (p,z)∈Δ_m  via membre_graphe_terme ⇐ : (p∈A et z=(p,m))=(p∈A et z=T[p])
    Tp = subst_t(vp, _BND, T)                                     # (p,m)
    mem_p = membre_graphe_terme(va, T, "p", "z", _BND, "yb")       # ((p,z)∈Δ_m) ⇔ (p∈A et z=(p,m))
    pz_in = N.modus_ponens(conjonction_intro(p_in, z_pm), equivalence_arriere(mem_p))  # (p,z)∈Δ_m
    # z∈Δ_m⟨A⟩  via img_car ⇐ : (∃t)(t∈A et (t,z)∈Δ_m), témoin t:=p
    wit = conjonction_intro(p_in, pz_in)                          # p∈A et (p,z)∈Δ_m
    ex_t = N.modus_ponens(wit, N.s5(et(appartient(vt, va),
                                       appartient(E.couple(vt, vz), DX)), vp, "t"))
    z_in_img = N.modus_ponens(ex_t, equivalence_arriere(img_car))  # z∈Δ_m⟨A⟩
    bwd_inner = existe_elimination(existe_elimination(
        N.loi_deduction(bodyP, z_in_img), "q"), "p")              # (∃p)(∃q)body ⇒ z∈Δ_m⟨A⟩
    bwd = syllogisme(equivalence_avant(prod_car), bwd_inner)      # z∈A×{m} ⇒ z∈Δ_m⟨A⟩

    equiv_z = conjonction_intro(fwd, bwd)                         # z∈Δ_m⟨A⟩ ⇔ z∈A×{m}
    char = N.generalisation("z", equiv_z)
    selfAM = N.generalisation("z", conjonction_intro(
        a_implique_a(appartient(vz, AM)), a_implique_a(appartient(vz, AM))))
    return egalite_par_extension(char, selfAM, E.image(DX, va), AM, "z")


# ── PALIER 6 : est_bijection_de(Δ_m, A, A×{m})  puis  Eq(A, A×{m}) ─────────────
def copie_est_bijection(a_set="A", m=ZERO):
    """⊢ est_bijection_de(Δ_m, A, A×{m}).   (la copie a↦(a,m) est une bijection ; clos.)

    Les 4 conjoints — fonctionnel (palier 1), domaine (palier 2), injectif (palier 4),
    image (palier 5) — sont tous INCONDITIONNELS pour un graphe de terme (aucune
    hypothèse à couper), d'où la conjonction directe."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import est_bijection_de  # noqa: F401 (doc)
    c1 = copie_graphe_fonctionnel(a_set, m)
    c2 = copie_graphe_domaine(a_set, m)
    c3 = copie_graphe_injective(a_set, m)
    c4 = copie_graphe_image(a_set, m)
    return conjonction_intro(conjonction_intro(c1, c2), conjonction_intro(c3, c4))


# (Eq(A, A×{m}) : les « parties A, B de X, de cardinaux a et b » de la démo de la
#  Prop.8 sont les copies marquées de la somme disjointe du projet.)
# @livre Ch.III §3.4 Demo.8 | E III.28 L.6-7 | PDF p.131
def eq_copie_marquee(a_set="A", m=ZERO):
    """⊢ Eq(A, A×{m}).   (A est équipotent à sa copie marquée A×{m} ; clos.)

    Témoin = le graphe de copie Δ_m ; S5 sur est_bijection_de(F,A,A×{m}) donne
    (∃F)bij = Eq(A, A×{m})."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import est_bijection_de
    va, vm = _t(a_set), _t(m)
    DX = _copie_graphe(a_set, m)
    AM = E.produit(va, E.singleton(vm))
    bij = copie_est_bijection(a_set, m)                           # bij(Δ_m, A, A×{m})
    return N.modus_ponens(bij, N.s5(est_bijection_de(var("F"), va, AM), DX, "F"))


# ── Cas particuliers : copies de GAUCHE (marqueur 0) et de DROITE (marqueur 1) ─
def eq_copie_gauche(a_set="A"):
    """⊢ Eq(A, A×{0}).   (A équipotent à sa copie de GAUCHE, marqueur 0 = ∅ ; clos.)"""
    return eq_copie_marquee(a_set, ZERO)


def eq_copie_droite(b_set="B"):
    """⊢ Eq(B, B×{1}).   (B équipotent à sa copie de DROITE, marqueur 1 = {∅} ; clos.)"""
    return eq_copie_marquee(b_set, UN)


# ── Symétrie / transitivité de l'équipotence, version TERME (miroir _prop1_*_t) ─
def _eq_sym_t(tX, tY):
    """⊢ Eq(X, Y) ⇒ Eq(Y, X)  pour des TERMES X, Y.   (symétrie de Eq, term-tolérante.)

    equipotence_symetrique n'accepte que des NOMS ; on la généralise en X, Y puis on
    instancie aux termes (robuste, renommage déterministe), comme _prop1_direct_t."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.equipotence.ensembles_bijection import equipotence_symetrique
    gen = N.generalisation("X", N.generalisation("Y", equipotence_symetrique("F", "X", "Y")))
    return instancie(instancie(gen, _t(tX)), _t(tY))


def _eq_trans_t(tX, tY, tZ):
    """⊢ (Eq(X,Y) et Eq(Y,Z)) ⇒ Eq(X,Z)  pour des TERMES X, Y, Z.   (transitivité de Eq.)"""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.equipotence.ensembles_bijection import equipotence_transitive
    gen = N.generalisation("X", N.generalisation("Y", N.generalisation("Z",
        equipotence_transitive("F", "G", "X", "Y", "Z"))))
    return instancie(instancie(instancie(gen, _t(tX)), _t(tY)), _t(tZ))


# ── TRANSPORT par les copies : Eq(A×{0}, B×{0}) ⇒ Eq(A, B)  (CLOS) ────────────
def eq_copies_gauches_implique_eq(a_set="A", b_set="B"):
    """⊢ Eq(A×{0}, B×{0}) ⇒ Eq(A, B).   (transport par les copies de gauche ; clos.)

    Moitié RÉDUCTIBLE du CAS 1 du cœur back-and-forth de la Proposition 8 : une fois
    qu'on a une équipotence ENTRE LES COPIES DE GAUCHE A×{0} et B×{0}, on la
    transporte vers Eq(A, B) par les équipotences canoniques A ≅ A×{0} et B ≅ B×{0}
    (eq_copie_marquee, marqueur 0) :

        Eq(A, A×{0})  ∘  Eq(A×{0}, B×{0})  ∘  Eq(B×{0}, B)   ⟹   Eq(A, B),

    où Eq(B×{0}, B) = symétrie de Eq(B, B×{0}).  Deux applications de la transitivité
    de l'équipotence.  AUCUNE surgery de graphe sur le témoin h (c'est exactement la
    part de la construction qui NE nécessite PAS de manipuler la bijection abstraite) ;
    il ne reste, pour finir le CAS 1, qu'à établir l'hypothèse Eq(A×{0}, B×{0}) à
    partir de Eq(A⊔{∅}, B⊔{∅}) ∧ (h fixe le marqueur) — la restriction de h aux
    copies de gauche, REPORTÉE (cf. note finale)."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import equipotent
    va, vb = _t(a_set), _t(b_set)
    A0 = E.produit(va, E.singleton(ZERO))          # A×{0}
    B0 = E.produit(vb, E.singleton(ZERO))          # B×{0}
    h = N.assume(equipotent(A0, B0))               # Eq(A×{0}, B×{0})   [hyp]
    eq_A_A0 = eq_copie_marquee(a_set, ZERO)        # Eq(A, A×{0})
    eq_B_B0 = eq_copie_marquee(b_set, ZERO)        # Eq(B, B×{0})
    eq_B0_B = N.modus_ponens(eq_B_B0, _eq_sym_t(vb, B0))   # Eq(B×{0}, B)
    # Eq(A, A×{0}) et Eq(A×{0}, B×{0})  ⇒  Eq(A, B×{0})
    eq_A_B0 = N.modus_ponens(conjonction_intro(eq_A_A0, h),
                             _eq_trans_t(va, A0, B0))      # Eq(A, B×{0})
    # Eq(A, B×{0}) et Eq(B×{0}, B)  ⇒  Eq(A, B)
    eq_A_B = N.modus_ponens(conjonction_intro(eq_A_B0, eq_B0_B),
                            _eq_trans_t(va, B0, vb))        # Eq(A, B)
    return N.loi_deduction(equipotent(A0, B0), eq_A_B)


__all__ = ["copie_graphe_fonctionnel", "copie_graphe_domaine", "copie_graphe_valeur",
           "copie_graphe_injective", "copie_graphe_image", "copie_est_bijection",
           "eq_copie_marquee", "eq_copie_gauche", "eq_copie_droite",
           "eq_copies_gauches_implique_eq"]
