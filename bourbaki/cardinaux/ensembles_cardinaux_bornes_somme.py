"""§III.3.2 — Bornes de la SOMME et du PRODUIT cardinal :  a ≤ a+b,  b ≤ a+b,
et  a ≤ a·b  (si b ≠ 0).  Versions SYMBOLIQUES (A, B cardinaux/ensembles).

Généralisation directe de `ensembles_cardinaux_bornes.inf_egal_successeur` (qui
fait DÉJÀ  a ≤ a+1 = a ≤ a⊔{∅}, injection canonique gauche u↦(u,0)) en remplaçant
le second sommant {∅} par un ensemble GÉNÉRIQUE B :

  (1) `inf_egal_somme_gauche`  ⊢ A ≤ A⊔B   (= a ≤ a+b).
      Témoin = l'INJECTION CANONIQUE GAUCHE  u ↦ (u,0)  de A dans A⊔B, dont le
      graphe est la COPIE MARQUÉE  Δ_0 := graphe_terme(A, (e,0))  (E.III.3.3 ;
      ensembles_copie_marquee).  On certifie est_injection_de(Δ_0, A, A⊔B) :
        • Δ_0 fonctionnel        (copie_graphe_fonctionnel, m=0) ;
        • dom Δ_0 = A            (copie_graphe_domaine, m=0) ;
        • Δ_0 injective sur A    (copie_graphe_injective, m=0) ;
        • image(Δ_0, A) ⊂ A⊔B    (chaque (u,0), u∈A, est dans A⊔B par
                                  injection_gauche_dans_somme).
      S5 (témoin Δ_0) → A ≤ A⊔B.  `cardinal_inf_egal_somme_gauche` instancie au
      TERME Card(A) : Card(A) ≤ Card(A)⊔B.

  (2) `inf_egal_somme_droite`  ⊢ B ≤ A⊔B   (= b ≤ a+b).
      Témoin = l'INJECTION CANONIQUE DROITE  v ↦ (v,1)  de B dans A⊔B, graphe
      Δ_1 := graphe_terme(B, (e,1)).  Mêmes quatre conjoints (m=1), image incluse
      via injection_droite_dans_somme.  `cardinal_inf_egal_somme_droite` idem.

  (3) `inf_egal_produit`  ⊢ ¬(B = ∅) ⇒ (A ≤ A×B)   (= a ≤ a·b si b ≠ 0).
      De ¬(B=∅) on extrait (non_vide_ssi_element) un témoin e∈B ; l'injection
      x ↦ (x,e) de A dans A×B a pour graphe la copie marquée Δ_e := graphe_terme(
      A, (a,e)).  fonctionnel/domaine/injectif sont INCONDITIONNELS (paramétrés
      par le marqueur e) ; image(Δ_e, A) = A×{e} ⊂ A×B car {e}⊂B (e∈B), via
      produit_inclusion_facile.  S5 (témoin Δ_e) → A ≤ A×B ; ∃-élim du témoin e
      puis décharge donnent ¬(B=∅) ⇒ A ≤ A×B.

RIEN POSTULÉ : chaque injection est exhibée et vérifiée conjoint par conjoint,
en réutilisant la machinerie graphe-terme/copie-marquée déjà certifiée.  Ce sont
les bornes de Bourbaki E.III.3.2 (« a ≤ a+b », « a ≤ a·b si b≠0 »).
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (Terme, var, egal, et, non, appartient, existe,
                                       inclus, subst_t)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege import syllogisme, a_implique_a
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (conjonction_intro,
                               conjonction_elim_gauche, conjonction_elim_droite,
                               equivalence_avant, equivalence_arriere, instancie)
from bourbaki.logique.i_4_egalitaires.tactiques_abrege_egalite import symetrie
from bourbaki.logique.i_3_quantifies.tactiques_abrege_quantif import existe_elimination
from bourbaki.cardinaux.ensembles_cardinaux import (est_injection_de, inf_egal_card,
                               cardinal)
from bourbaki.cardinaux.arithmetique.iii_3_4_prop8_successeur.ensembles_copie_marquee import (
                               _copie_graphe, _copie_terme, _BND,
                               copie_graphe_fonctionnel, copie_graphe_domaine,
                               copie_graphe_injective, copie_graphe_image)
from bourbaki.ensembles.familles.ii_4_reunion_intersection_familles.ii_4_recollement_somme.ensembles_somme_disjointe import (somme_disjointe,
                               ZERO, UN, injection_gauche_dans_somme,
                               injection_droite_dans_somme)
from bourbaki.ensembles.fonctions.ii_3_6_fonction_terme.ensembles_fonction_terme import membre_graphe_terme
from bourbaki.ensembles.familles.ii_2_produit_deux_ensembles.ensembles_produit import produit_inclusion_facile
from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_vide import non_vide_ssi_element


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# ═══════════════════════════════════════════════════════════════════════════════
# Brique commune : image(Δ_m, A) ⊂ S, où S contient toutes les copies (u,m), u∈A.
# Δ_m = graphe_terme(A,(e,m)).  On décline le pont « (u,m)∈S » par le côté.
# ═══════════════════════════════════════════════════════════════════════════════
def _image_marquee_incluse(a_set, m, S, pont):
    """⊢ image(Δ_m, A) ⊂ S,  Δ_m = graphe de a↦(a,m),  `pont(t)` : (t∈A) ⊢ (t,m)∈S.

    z∈Δ_m⟨A⟩ ⇔ (∃x)(x∈A et (x,z)∈Δ_m) [AXIOME_IMAGE].  Sous le corps, (x,z)∈Δ_m
    donne (x∈A et z=(x,m)) (membre_graphe_terme), et x∈A donne (x,m)∈S (`pont(x)`) ;
    Leibniz z=(x,m) ↦ z donne z∈S.  ∃-élim → Δ_m⟨A⟩ ⊂ S.  Liant z, témoin « x ».

    `pont` est une FONCTION du terme-témoin (≠ pré-construit) pour que l'antécédent
    de l'injection canonique soit bien « x∈A » (= le témoin d'AXIOME_IMAGE)."""
    va, vm = _t(a_set), _t(m)
    DX = _copie_graphe(a_set, m)
    T = _copie_terme(m, _BND)                    # (e,m)
    vz, vx = var("z"), var("x")
    ax_img = N.axiome(E.theorie_ensembles(), E.AXIOME_IMAGE)
    img_car = instancie(instancie(instancie(ax_img, DX), va), vz)  # z∈Δ_m⟨A⟩ ⇔ (∃x)(x∈A et (x,z)∈Δ_m)
    vu = vx                                       # témoin = « x » (≠ liant « e » de Δ_m)
    body = et(appartient(vu, va), appartient(E.couple(vu, vz), DX))
    hb = N.assume(body)
    u_inA = conjonction_elim_gauche(hb)          # x∈A
    uz_inDX = conjonction_elim_droite(hb)        # (x,z)∈Δ_m
    mem = membre_graphe_terme(va, T, "x", "z", _BND, "yb")  # ((x,z)∈Δ_m) ⇔ (x∈A et z=(x,m))
    z_eq_Tu = conjonction_elim_droite(N.modus_ponens(uz_inDX, equivalence_avant(mem)))  # z=(x,m)
    Tu = subst_t(vu, _BND, T)                     # (x,m)
    Tu_inS = N.modus_ponens(u_inA, pont(vx))     # (x,m)∈S   (pont instancié au témoin x)
    Tu_eq_z = N.modus_ponens(z_eq_Tu, symetrie(vz, Tu))           # (u,m)=z
    z_inS = N.modus_ponens(Tu_inS, equivalence_avant(N.modus_ponens(
        Tu_eq_z, N.s6(Tu, vz, "w", appartient(var("w"), S)))))    # z∈S
    inner = existe_elimination(N.loi_deduction(body, z_inS), "x")  # (∃x)body ⇒ z∈S
    z_imp = syllogisme(equivalence_avant(img_car), inner)          # z∈Δ_m⟨A⟩ ⇒ z∈S
    return N.generalisation("z", z_imp)          # image(Δ_m,A) ⊂ S


def _injection_marquee(a_set, m, S, pont):
    """⊢ est_injection_de(Δ_m, A, S).   (les 4 conjoints, Δ_m = graphe a↦(a,m).)"""
    func = copie_graphe_fonctionnel(a_set, m)             # fonctionnel
    domeq = copie_graphe_domaine(a_set, m)                # dom = A
    inj = copie_graphe_injective(a_set, m)                # injective_dans
    img = _image_marquee_incluse(a_set, m, S, pont)       # image ⊂ S
    return conjonction_intro(conjonction_intro(conjonction_intro(func, domeq), inj), img)


# ═══════════════════════════════════════════════════════════════════════════════
# (1)  a ≤ a+b   —   injection canonique GAUCHE  u ↦ (u,0)  de A dans A⊔B
# ═══════════════════════════════════════════════════════════════════════════════
def somme_gauche_injection(a="A", b="B"):
    """⊢ est_injection_de(Δ_0, A, A⊔B),  Δ_0 = graphe de u↦(u,0).   (clos.)

    Le pont d'image est injection_gauche_dans_somme : (u∈A) ⇒ (u,0)∈A⊔B."""
    va, vb = _t(a), _t(b)
    S = somme_disjointe(va, vb)                  # A⊔B
    pont = lambda tx: injection_gauche_dans_somme(tx, va, vb)   # (x∈A) ⇒ (x,0)∈A⊔B
    return _injection_marquee(a, ZERO, S, pont)


def inf_egal_somme_gauche(a="A", b="B"):
    """⊢ A ≤ A⊔B.   (« a ≤ a+b », E.III.3.2 ; injection gauche u↦(u,0).)

    Témoin = Δ_0 = graphe_terme(A,(e,0)) ; S5 sur est_injection_de(F,A,A⊔B)."""
    va, vb = _t(a), _t(b)
    S = somme_disjointe(va, vb)
    DX = _copie_graphe(a, ZERO)
    injection = somme_gauche_injection(a, b)
    return N.modus_ponens(injection,
        N.s5(est_injection_de(var("F"), va, S), DX, "F"))   # A ≤ A⊔B


def cardinal_inf_egal_somme_gauche(a="A", b="B"):
    """⊢ Card(A) ≤ Card(A)⊔B.   (= a ≤ a+b sur les cardinaux ; E.III.3.2.)

    On généralise A ≤ A⊔B en (∀A)(A ≤ A⊔B) puis on INSTANCIE au TERME Card(A)."""
    va = _t(a)
    gen = N.generalisation("A", inf_egal_somme_gauche("A", b))   # (∀A)(A ≤ A⊔B)
    return instancie(gen, cardinal(va))                         # Card(A) ≤ Card(A)⊔B


# ═══════════════════════════════════════════════════════════════════════════════
# (2)  b ≤ a+b   —   injection canonique DROITE  v ↦ (v,1)  de B dans A⊔B
# ═══════════════════════════════════════════════════════════════════════════════
def somme_droite_injection(a="A", b="B"):
    """⊢ est_injection_de(Δ_1, B, A⊔B),  Δ_1 = graphe de v↦(v,1).   (clos.)

    Le pont d'image est injection_droite_dans_somme : (v∈B) ⇒ (v,1)∈A⊔B."""
    va, vb = _t(a), _t(b)
    S = somme_disjointe(va, vb)                  # A⊔B
    pont = lambda tx: injection_droite_dans_somme(tx, va, vb)   # (x∈B) ⇒ (x,1)∈A⊔B
    return _injection_marquee(b, UN, S, pont)


def inf_egal_somme_droite(a="A", b="B"):
    """⊢ B ≤ A⊔B.   (« b ≤ a+b », E.III.3.2 ; injection droite v↦(v,1).)

    Témoin = Δ_1 = graphe_terme(B,(e,1)) ; S5 sur est_injection_de(F,B,A⊔B)."""
    va, vb = _t(a), _t(b)
    S = somme_disjointe(va, vb)
    DX = _copie_graphe(b, UN)
    injection = somme_droite_injection(a, b)
    return N.modus_ponens(injection,
        N.s5(est_injection_de(var("F"), vb, S), DX, "F"))   # B ≤ A⊔B


def cardinal_inf_egal_somme_droite(a="A", b="B"):
    """⊢ Card(B) ≤ A⊔Card(B).   (= b ≤ a+b sur les cardinaux ; E.III.3.2.)

    On généralise B ≤ A⊔B en (∀B)(B ≤ A⊔B) puis on INSTANCIE au TERME Card(B)."""
    vb = _t(b)
    gen = N.generalisation("B", inf_egal_somme_droite(a, "B"))   # (∀B)(B ≤ A⊔B)
    return instancie(gen, cardinal(vb))                         # Card(B) ≤ A⊔Card(B)


# ═══════════════════════════════════════════════════════════════════════════════
# (3)  a ≤ a·b  (si b ≠ 0)   —   injection  x ↦ (x,e)  de A dans A×B,  e∈B fixé
# ═══════════════════════════════════════════════════════════════════════════════
def _produit_inclusion_singleton(a_set, e_pt, b_set):
    """{e∈B} ⊢ A×{e} ⊂ A×B.   (de {e}⊂B (e∈B) et A⊂A (réflexif), Proposition 2.)

    produit_inclusion_facile : ((A⊂A) et ({e}⊂B)) ⇒ (A×{e} ⊂ A×B)."""
    va, ve, vb = _t(a_set), _t(e_pt), _t(b_set)
    # {e}⊂B  ⇐  e∈B :  (∀z)(z∈{e} ⇒ z∈B), où z∈{e} ⇒ z=e ⇒ z∈B
    vz = var("z")
    ax_p = N.axiome(E.theorie_ensembles(), E.AXIOME_PAIRE)
    car_z = instancie(instancie(instancie(ax_p, ve), ve), vz)   # z∈{e,e} ⇔ (z=e ou z=e)
    from bourbaki.ensembles.familles.ii_4_reunion_intersection_familles.ii_4_recollement_somme.ensembles_somme_disjointe import _ou_idem
    hz = N.assume(appartient(vz, E.singleton(ve)))             # z∈{e}
    z_eq_e = _ou_idem(N.modus_ponens(hz, equivalence_avant(car_z)), egal(vz, ve))  # z=e
    he = N.assume(appartient(ve, vb))                          # e∈B
    z_inB = N.modus_ponens(he, equivalence_arriere(N.modus_ponens(
        z_eq_e, N.s6(vz, ve, "w", appartient(var("w"), vb)))))  # z∈B  [hyps z∈{e}, e∈B]
    z_imp = N.loi_deduction(appartient(vz, E.singleton(ve)), z_inB)  # z∈{e} ⇒ z∈B  [hyp e∈B]
    e_sub_B = N.generalisation("z", z_imp)                     # {e}⊂B  [hyp e∈B]
    # A⊂A (réflexif)
    a_sub_a = N.generalisation("z", a_implique_a(appartient(vz, va)))   # A⊂A
    # instancier produit_inclusion_facile aux termes A, B, A, {e}
    gen = N.generalisation("A", N.generalisation("B", N.generalisation("Ap",
        N.generalisation("Bp", produit_inclusion_facile()))))
    inst = instancie(instancie(instancie(instancie(gen, va), vb), va), E.singleton(ve))
    #  ((A⊂A) et ({e}⊂B)) ⇒ (A×{e} ⊂ A×B)
    return N.modus_ponens(conjonction_intro(a_sub_a, e_sub_B), inst)   # A×{e}⊂A×B  [hyp e∈B]


def produit_injection_temoin(a_set="A", e_pt="m", b_set="B"):
    """{e∈B} ⊢ est_injection_de(Δ_e, A, A×B),  Δ_e = graphe de x↦(x,e).

    fonctionnel/domaine/injectif : INCONDITIONNELS (copie marquée, marqueur e).
    image(Δ_e, A) = A×{e} (copie_graphe_image) ⊂ A×B (sous e∈B) ; Leibniz réécrit
    l'image A×{e} ↦ image(Δ_e,A) dans l'inclusion."""
    va, ve, vb = _t(a_set), _t(e_pt), _t(b_set)
    DX = _copie_graphe(a_set, ve)
    AB = E.produit(va, vb)                        # A×B
    AE = E.produit(va, E.singleton(ve))           # A×{e}
    func = copie_graphe_fonctionnel(a_set, ve)
    domeq = copie_graphe_domaine(a_set, ve)
    inj = copie_graphe_injective(a_set, ve)
    img_eq = copie_graphe_image(a_set, ve)        # image(Δ_e,A) = A×{e}
    ae_sub_ab = _produit_inclusion_singleton(va, ve, vb)   # A×{e} ⊂ A×B  [hyp e∈B]
    # image(Δ_e,A) ⊂ A×B  via Leibniz  image(Δ_e,A) = A×{e}
    img_eq_sym = N.modus_ponens(img_eq, symetrie(E.image(DX, va), AE))  # A×{e}=image(Δ_e,A)
    img_sub = N.modus_ponens(ae_sub_ab, equivalence_avant(N.modus_ponens(
        img_eq_sym, N.s6(AE, E.image(DX, va), "w", inclus(var("w"), AB)))))   # image⊂A×B
    return conjonction_intro(conjonction_intro(conjonction_intro(func, domeq), inj), img_sub)


def inf_egal_produit(a_set="A", b_set="B"):
    """⊢ ¬(B = ∅) ⇒ (A ≤ A×B).   (« a ≤ a·b si b ≠ 0 », E.III.3.2.)

    De ¬(B=∅) on tire (∃e)(e∈B) (non_vide_ssi_element) ; sous un témoin e∈B,
    l'injection x↦(x,e) (graphe Δ_e) certifie A ≤ A×B (produit_injection_temoin
    + S5 témoin Δ_e) ; ∃-élim du témoin e, puis décharge de ¬(B=∅)."""
    va, vb = _t(a_set), _t(b_set)
    ve = var("m")                                 # témoin e∈B (nommé « m » : « e » est le liant interne de Δ)
    AB = E.produit(va, vb)                        # A×B
    DX = _copie_graphe(a_set, ve)
    # sous m∈B : A ≤ A×B
    inj = produit_injection_temoin(a_set, "m", b_set)         # {m∈B} ⊢ est_injection_de(Δ_m,A,A×B)
    le = N.modus_ponens(inj, N.s5(est_injection_de(var("F"), va, AB), DX, "F"))  # {m∈B} ⊢ A≤A×B
    # (∃m)(m∈B) ⇒ A≤A×B   (∃-élim : m n'est pas libre dans A≤A×B)
    ex_imp = existe_elimination(N.loi_deduction(appartient(ve, vb), le), "m")
    # ¬(B=∅) ⇒ (∃m)(m∈B)
    nonvide = non_vide_ssi_element(vb)            # ¬(B=∅) ⇔ (∃z)(z∈B)
    # renommer le liant z↦m pour apparier ex_imp
    from bourbaki.logique.i_3_quantifies.tactiques_abrege_quantif import alpha_existe
    ren = alpha_existe("z", "m", appartient(var("z"), vb))    # (∃z)(z∈B) ⇔ (∃m)(m∈B)
    nv_e = syllogisme(equivalence_avant(nonvide), equivalence_avant(ren))  # ¬(B=∅) ⇒ (∃m)(m∈B)
    return syllogisme(nv_e, ex_imp)              # ¬(B=∅) ⇒ A≤A×B


def cardinal_inf_egal_produit(a_set="A", b_set="B"):
    """⊢ ¬(B = ∅) ⇒ (Card(A) ≤ Card(A)×B).   (= a ≤ a·b si b≠0, sur les cardinaux.)

    Généralise A en (∀A)(¬(B=∅) ⇒ A≤A×B) puis instancie au TERME Card(A)."""
    va = _t(a_set)
    gen = N.generalisation("A", inf_egal_produit("A", b_set))
    return instancie(gen, cardinal(va))


__all__ = [
    "somme_gauche_injection", "inf_egal_somme_gauche", "cardinal_inf_egal_somme_gauche",
    "somme_droite_injection", "inf_egal_somme_droite", "cardinal_inf_egal_somme_droite",
    "produit_injection_temoin", "inf_egal_produit", "cardinal_inf_egal_produit",
]
