"""§III.3.3 / §III.3.4 — 0 ÉLÉMENT NEUTRE de la somme cardinale : Eq(∅⊔B, B),
puis Card(∅⊔B) = Card(B)  (Cor. 1 de la Proposition 6 : a + 0 = a, ici 0 + b = b).

La somme disjointe  ∅ ⊔ B := (∅×{0}) ∪ (B×{1})  a sa copie GAUCHE ∅×{0} vide
(∅ n'a aucun élément, AXIOME_VIDE), donc tout z∈∅⊔B est dans la copie DROITE B×{1},
i.e. z=(v,1) avec v∈B.  L'application témoin est l'INJECTION DROITE vue comme
bijection  K : B → ∅⊔B,  v ↦ (v, 1),  de graphe  K := graphe_terme(B, (k,1), "k").

ÉTAT — THÉORÈME COMPLET, tout CERTIFIÉ et TESTÉ (test_somme_zero.py) :
  • neutre_graphe_fonctionnel  (clos)        — K fonctionnel ;
  • neutre_graphe_domaine      (clos)        — dom K = B ;
  • neutre_graphe_valeur       {v∈B}         — K(v) = (v,1) ;
  • neutre_graphe_injective    (clos)        — injective_dans(K, B) ;
  • neutre_graphe_image        (clos)        — image(K, B) = ∅⊔B ;
  • neutre_est_bijection       (clos)        — est_bijection_de(K, B, ∅⊔B) ;
  • eq_somme_zero_neutre       (clos)        — Eq(∅⊔B, B)  [symétrie de Eq(B, ∅⊔B)] ;
  • card_somme_zero_neutre     (clos)        — Card(∅⊔B) = Card(B)  (Proposition 1).
"""
from __future__ import annotations

from bourbaki.logique.formule import (Terme, var, egal, et, non, appartient, existe, subst_t, subst_f)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.tactiques.tactiques_abrege import a_implique_a, syllogisme
from bourbaki.logique.tactiques.tactiques_abrege2 import (conjonction_intro, conjonction_elim_gauche,
                               conjonction_elim_droite, equivalence_avant,
                               equivalence_arriere, equivalence_transitivite,
                               instancie, cas)
from bourbaki.logique.tactiques.tactiques_abrege_egalite import (symetrie, composer_egalites, congruence_terme)
from bourbaki.logique.tactiques.tactiques_abrege_quantif import (existe_elimination, alpha_existe)
from bourbaki.ensembles.fonctions.ii_3_6_fonction_terme.ensembles_fonction_terme import (membre_graphe_terme, graphe_terme_fonctionnel)
from bourbaki.cardinaux.ensembles_cantor import (graphe_terme_domaine, graphe_terme_valeur)
from bourbaki.ensembles.ii_2_couples_produit.ensembles_couples import couple_egal_implique_composantes
from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_theoremes import egalite_par_extension
from bourbaki.cardinaux.ensembles_cardinaux import est_bijection_de, equipotent, cardinal
from bourbaki.ensembles.familles.ii_4_reunion_intersection_familles.ii_4_recollement_somme.ensembles_somme_disjointe import (somme_disjointe, ZERO, UN,
                                       injection_droite_dans_somme,
                                       membre_somme_caracterise, _ou_congruence)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# ── Le terme  T(k) = (k, 1)  (marque tout élément de B dans la copie droite) ──
def _neutre_terme(k="k"):
    """T(k) = (k, 1)   (injection droite : v ↦ (v, 1))."""
    return E.couple(var(k), UN)


def _neutre_graphe(b, k="k"):
    """K := graphe_terme(B, (k,1), "k")  (graphe de l'injection droite v↦(v,1))."""
    return E.graphe_terme(_t(b), _neutre_terme(k), k)


# ── PALIER 1 : K fonctionnel ──────────────────────────────────────────────────
def neutre_graphe_fonctionnel(b="B"):
    """⊢ K est fonctionnel,  K = graphe de v↦(v,1).   (cas C54, clos.)"""
    return graphe_terme_fonctionnel(_t(b), _neutre_terme("k"), "k", "y")


# ── PALIER 2 : dom K = B ──────────────────────────────────────────────────────
def neutre_graphe_domaine(b="B"):
    """⊢ dom(K) = B.   (l'injection droite est définie sur tout B ; clos.)"""
    return graphe_terme_domaine(_t(b), _neutre_terme("k"), "k", "y", "z")


# ── PALIER 3 : K(v) = (v,1) pour v∈B ──────────────────────────────────────────
def neutre_graphe_valeur(b="B", v="u"):
    """{u ∈ B} ⊢ K(u) = (u, 1).   (T[u] = (u|k)(k,1) = (u,1) ; clos sous u∈B.)

    NB élément « u » (et non « v » ni « w ») : le binder INTERNE de coordonnée de
    graphe_terme_couple_dans est nommé « v », et le trou Leibniz de
    couple_egal_implique_composantes est nommé « w » — collisions à éviter."""
    return graphe_terme_valeur(_t(b), _neutre_terme("k"), v, "k", "y")


# ── PALIER 4 : injective_dans(K, B) ───────────────────────────────────────────
def neutre_graphe_injective(b="B"):
    """⊢ injective_dans(K, B).   (v↦(v,1) injectif : (v,1)=(v',1) ⇒ v=v'.)"""
    vb = _t(b)
    K = _neutre_graphe(b, "k")
    vu, vup = var("u"), var("up")
    hyp = et(et(appartient(vu, vb), appartient(vup, vb)),
             egal(E.valeur(K, vu), E.valeur(K, vup)))
    h = N.assume(hyp)
    uin = conjonction_elim_gauche(conjonction_elim_gauche(h))      # u∈B
    upin = conjonction_elim_droite(conjonction_elim_gauche(h))     # u'∈B
    val_eq = conjonction_elim_droite(h)                            # K(u)=K(u')
    Ku = N.modus_ponens(uin, N.loi_deduction(appartient(vu, vb),
                                             neutre_graphe_valeur(b, "u")))   # K(u)=(u,1)
    Kup = N.modus_ponens(upin, N.loi_deduction(appartient(vup, vb),
                                               neutre_graphe_valeur(b, "up")))  # K(u')=(u',1)
    # (u,1)=(u',1) ⇒ u=u'
    lhs_eq = composer_egalites(N.modus_ponens(Ku, symetrie(E.valeur(K, vu), E.couple(vu, UN))),
                               composer_egalites(val_eq, Kup))     # (u,1)=(u',1)
    comps = N.modus_ponens(lhs_eq, couple_egal_implique_composantes(vu, UN, vup, UN))
    u_eq = conjonction_elim_gauche(comps)                          # u=u'
    inner = N.loi_deduction(hyp, u_eq)
    return N.generalisation("u", N.generalisation("up", inner))   # injective_dans(K, B)


# ── PALIER 5 : image(K, B) = ∅⊔B  (surjectivité) ──────────────────────────────
def neutre_graphe_image(b="B"):
    """⊢ image(K, B) = ∅⊔B.   (l'image de v↦(v,1) sur B est toute la somme ∅⊔B.)

    z∈K⟨B⟩ ⇔ (∃t)(t∈B et z=T[t]=(t,1)).
    ⇒ : t∈B ⇒ (t,1)∈∅⊔B (injection_droite_dans_somme avec copie gauche ∅) ;
    ⇐ : z∈∅⊔B ⇔ ((∃u)(u∈∅ et z=(u,0)) ou (∃v)(v∈B et z=(v,1)))
        [membre_somme_caracterise].  Le disjoint gauche est faux (u∈∅ impossible) ;
        le disjoint droit donne z=(v,1) avec v∈B, antécédent t:=v."""
    vb = _t(b)
    vide = E.VIDE
    AB = somme_disjointe(vide, vb)             # ∅ ⊔ B
    T = _neutre_terme("k")
    K = E.graphe_terme(vb, T, "k")
    vz = var("z")
    ax_img = N.axiome(E.theorie_ensembles(), E.AXIOME_IMAGE)
    img_car0 = instancie(instancie(instancie(ax_img, K), vb), vz)
    inner_x = et(appartient(var("x"), vb), appartient(E.couple(var("x"), vz), K))
    ren = alpha_existe("x", "t", inner_x)
    img_car = equivalence_transitivite(img_car0, ren)      # z∈K⟨B⟩ ⇔ (∃t)(t∈B et (t,z)∈K)
    vt = var("t")

    # ── ⇒ : z∈K⟨B⟩ ⇒ z∈∅⊔B ────────────────────────────────────────────────────
    bodyR = et(appartient(vt, vb), appartient(E.couple(vt, vz), K))
    hbR = N.assume(bodyR)
    t_in = conjonction_elim_gauche(hbR)                    # t∈B
    cpl_in = conjonction_elim_droite(hbR)                  # (t,z)∈K
    mem = membre_graphe_terme(vb, T, "t", "m", "k", "yb")  # ((t,m)∈K)⇔(t∈B et m=(t,1))
    mem_z = instancie(N.generalisation("m", mem), vz)      # ((t,z)∈K)⇔(t∈B et z=(t,1))
    z_eq_t1 = conjonction_elim_droite(N.modus_ponens(cpl_in, equivalence_avant(mem_z)))  # z=(t,1)
    # (t,1)∈∅⊔B  via injection droite
    t1_in = N.modus_ponens(t_in, injection_droite_dans_somme(vt, vide, vb))  # (t,1)∈∅⊔B
    z_in = N.modus_ponens(t1_in, equivalence_arriere(N.modus_ponens(
        z_eq_t1, N.s6(vz, E.couple(vt, UN), "w", appartient(var("w"), AB)))))   # z∈∅⊔B
    fwd = existe_elimination(N.loi_deduction(bodyR, z_in), "t")
    fwd_full = syllogisme(equivalence_avant(img_car), fwd)  # z∈K⟨B⟩ ⇒ z∈∅⊔B

    # ── ⇐ : z∈∅⊔B ⇒ z∈K⟨B⟩ ────────────────────────────────────────────────────
    from bourbaki.logique.formule import ou
    dec_z0 = N.modus_ponens(N.assume(appartient(vz, AB)),
                            equivalence_avant(membre_somme_caracterise(vide, vb, vz)))
    exG0, exD0 = dec_z0.conclusion.sous[0], dec_z0.conclusion.sous[1]
    renG = alpha_existe(exG0.lieur, "n1", exG0.sous[0])
    renD = alpha_existe(exD0.lieur, "n2", exD0.sous[0])
    dec_z = N.modus_ponens(dec_z0, equivalence_avant(_ou_congruence(renG, renD)))
    exG, exD = dec_z.conclusion.sous[0], dec_z.conclusion.sous[1]
    nG, bG = exG.lieur, exG.sous[0]        # n1 ; (n1∈∅ et z=(n1,0))
    nD, bD = exD.lieur, exD.sous[0]        # n2 ; (n2∈B et z=(n2,1))
    vc, vd = var(nG), var(nD)
    cible_img = appartient(vz, E.image(K, vb))

    # branche GAUCHE : (c∈∅ et z=(c,0)) ⇒ z∈K⟨B⟩  par ex falso (c∈∅ impossible)
    def back_gauche():
        hc = N.assume(bG)
        c_in_vide = conjonction_elim_gauche(hc)            # c∈∅
        ax_vide = N.axiome(E.theorie_ensembles(), E.AXIOME_VIDE)
        nc = instancie(ax_vide, vc)                        # ¬(c∈∅)
        falso = N.modus_ponens(c_in_vide, N.modus_ponens(nc, N.s2(non(appartient(vc, vide)), cible_img)))
        return N.loi_deduction(bG, falso)                  # bG ⇒ z∈K⟨B⟩

    # branche DROITE : (d∈B et z=(d,1)) ⇒ z∈K⟨B⟩  antécédent t:=d
    def back_droite():
        hd = N.assume(bD)
        d_in = conjonction_elim_gauche(hd)                 # d∈B
        z_eq = conjonction_elim_droite(hd)                 # z=(d,1)
        # (d,z)∈K  via membre_graphe_terme ⇐ (d∈B et z=T[d]=(d,1))
        Td = subst_t(vd, "k", T)                           # (d,1)
        # z=(d,1)=T[d]
        z_eq_Td = z_eq                                     # T[d]=(d,1) littéralement
        mem_d = membre_graphe_terme(vb, T, "td", "z", "k", "yb")   # ((td,z)∈K)⇔(td∈B et z=T[td])
        from bourbaki.logique.tactiques.tactiques_abrege2 import instancie as _inst
        mem_dd = _inst(N.generalisation("td", mem_d), vd)  # ((d,z)∈K)⇔(d∈B et z=(d,1))
        dz_in_K = N.modus_ponens(conjonction_intro(d_in, z_eq_Td),
                                 equivalence_arriere(mem_dd))   # (d,z)∈K
        wit = conjonction_intro(d_in, dz_in_K)             # d∈B et (d,z)∈K
        ex_t = N.modus_ponens(wit, N.s5(et(appartient(vt, vb),
                                           appartient(E.couple(vt, vz), K)), vd, "t"))
        z_in_img = N.modus_ponens(ex_t, equivalence_arriere(img_car))   # z∈K⟨B⟩
        return N.loi_deduction(bD, z_in_img)

    impG = existe_elimination(back_gauche(), nG)
    impD = existe_elimination(back_droite(), nD)
    z_in_img = cas(dec_z, impG, impD)
    bwd_full = N.loi_deduction(appartient(vz, AB), z_in_img)   # z∈∅⊔B ⇒ z∈K⟨B⟩

    equiv_z = conjonction_intro(fwd_full, bwd_full)
    char_u = N.generalisation("z", equiv_z)
    selfAB = N.generalisation("z", conjonction_intro(
        a_implique_a(appartient(vz, AB)), a_implique_a(appartient(vz, AB))))
    return egalite_par_extension(char_u, selfAB, E.image(K, vb), AB, "z")


# ── PALIER 6 : est_bijection_de(K, B, ∅⊔B) puis Eq(∅⊔B, B) ────────────────────
def neutre_est_bijection(b="B"):
    """⊢ est_bijection_de(K, B, ∅⊔B).   (v↦(v,1) est une bijection B → ∅⊔B.)"""
    func = neutre_graphe_fonctionnel(b)
    dom = neutre_graphe_domaine(b)
    inj = neutre_graphe_injective(b)
    img = neutre_graphe_image(b)
    return conjonction_intro(conjonction_intro(func, dom),
                             conjonction_intro(inj, img))


def eq_somme_zero_neutre(b="B"):
    """⊢ Eq(∅⊔B, B).   (0 ÉLÉMENT NEUTRE de la somme à équipotence près : 0 + b ≈ b.)

    K : B → ∅⊔B bijection (v↦(v,1)) ⇒ Eq(B, ∅⊔B) (S5) ; symétrie de Eq donne
    Eq(∅⊔B, B)."""
    vb = _t(b)
    AB = somme_disjointe(E.VIDE, vb)           # ∅ ⊔ B
    K = _neutre_graphe(b, "k")
    bij = neutre_est_bijection(b)              # est_bijection_de(K, B, ∅⊔B)
    eqB = N.modus_ponens(bij, N.s5(est_bijection_de(var("F"), vb, AB), K, "F"))  # Eq(B, ∅⊔B)
    # Eq(∅⊔B, B)  par symétrie de l'équipotence : Eq(B,∅⊔B) ⇒ Eq(∅⊔B,B)
    from bourbaki.cardinaux.ensembles_bijection import equipotence_symetrique
    sym = equipotence_symetrique("F", vb, AB)  # Eq(B, ∅⊔B) ⇒ Eq(∅⊔B, B)
    return N.modus_ponens(eqB, sym)            # Eq(∅⊔B, B)


# ── Card(∅⊔B) = Card(B)  =  0 + b = b  (niveau CARDINAL) ──────────────────────
def card_somme_zero_neutre(b="B"):
    """⊢ Card(∅⊔B) = Card(B).   (0 ÉLÉMENT NEUTRE de la somme cardinale : 0 + b = b.)

    Card(∅⊔B) = somme_cardinale_binaire(∅, B) = « 0 + b », et Card(B) = « b ».
    Eq(∅⊔B, B) (eq_somme_zero_neutre) ; la Proposition 1 (sens direct, version TERME
    _prop1_direct_t) conclut Card(∅⊔B) = Card(B).  (Cor. 1 de Prop. 6, E.III.3.4.)"""
    from bourbaki.cardinaux.arithmetique.ensembles_arith_cardinale import _prop1_direct_t
    vb = _t(b)
    AB = somme_disjointe(E.VIDE, vb)           # ∅ ⊔ B
    eq = eq_somme_zero_neutre(b)               # Eq(∅⊔B, B)
    prop1 = _prop1_direct_t(AB, vb)            # Eq(∅⊔B, B) ⇒ Card(∅⊔B)=Card(B)
    return N.modus_ponens(eq, prop1)           # Card(∅⊔B) = Card(B)


__all__ = ["neutre_graphe_fonctionnel", "neutre_graphe_domaine",
           "neutre_graphe_valeur", "neutre_graphe_injective",
           "neutre_graphe_image", "neutre_est_bijection",
           "eq_somme_zero_neutre", "card_somme_zero_neutre"]
