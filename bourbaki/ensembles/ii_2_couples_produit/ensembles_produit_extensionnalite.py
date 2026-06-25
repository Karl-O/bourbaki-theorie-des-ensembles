"""§II.2 — EXTENSIONNALITÉ DES PRODUITS : brique réutilisable pour passer de
l'appartenance d'un COUPLE à l'ÉGALITÉ D'ENSEMBLES PLEINE (fidélité Bourbaki).

Bourbaki (Résumé E.R.12) pose en tête « x=pr₁(z) et y=pr₂(z) équivaut à z=(x,y) » PUIS
énonce les égalités d'ensembles (22) (X×Y)∪(X'×Y)=(X∪X')×Y, (23)…  Le dépôt ne prouvait
ces formules qu'au niveau APPARTENANCE D'UN COUPLE (cf. ANOMALIES « écart de portée
systématique »).  Ce module comble le trou : extensionnalité des parties d'un produit,
puis la formule (22) en ÉGALITÉ D'ENSEMBLES (==).

Trois résultats (tous certifiés par le noyau abrégé, primitives N.* uniquement) :

  1. `couple_decomposition`  ⊢ (z ∈ X×Y) ⇒ z = (pr₁z, pr₂z)  (en-tête E.R.12 sur un
     produit).  PREUVE : AXIOME_PRODUIT donne (∃p)(∃q)(z=(p,q) ∧ p∈X ∧ q∈Y) ; sous
     témoins p,q, de z=(p,q) on tire pr₁z=p, pr₂z=q (projection_premiere/seconde +
     Leibniz), d'où (pr₁z,pr₂z)=(p,q)=z ; élimination des témoins p,q.

  2. `produit_egalite_par_couples`  ⊢
       ( A⊂E×F ∧ B⊂E×F ∧ (∀u)(∀v)((u,v)∈A ⇔ (u,v)∈B) )  ⇒  A=B.
     EXTENSIONNALITÉ DES PARTIES D'UN PRODUIT (la brique réutilisable).  PREUVE par
     A1 : pour A⊂B, soit z∈A ; A⊂E×F donne z∈E×F, donc (couple_decomposition)
     z=(pr₁z,pr₂z) ; l'hyp. couples instanciée en (pr₁z,pr₂z) + Leibniz donnent z∈B.

  3. `produit_distrib_reunion_premier_facteur_ensembliste`  ⊢
       ( X⊂E ∧ X'⊂E ∧ Y⊂F )  ⇒  (X×Y)∪(X'×Y) = (X∪X')×Y   [FORMULE (22), ÉGALITÉ ==].
     PREUVE : les deux membres sont ⊂ E×F (sous les ambiants) ; on applique
     produit_egalite_par_couples avec la composante couple déjà prouvée
     (couple_dans_produit_distrib_reunion_premier_facteur).

theorie_ensembles() INCHANGÉE (= 22) : aucun axiome ajouté (recollement pur).

Liants : pr₁/pr₂ τ-lient x,y ; témoins de AXIOME_PRODUIT = p,q (≠ x,y) ; trou de
congruence choisi FRAIS (`_hole`).  « w » reste réservé aux tactiques composer/symetrie.
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (Terme, var, egal, et, impl,
                                       appartient, inclus, pourtout, equiv)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_theoremes import extensionnalite_appliquee
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, instancie)
from bourbaki.logique.i_3_quantifies.tactiques_abrege_quantif import existe_elimination
from bourbaki.logique.i_4_egalitaires.tactiques_abrege_egalite import (
    symetrie, composer_egalites, congruence_terme)
from bourbaki.ensembles.familles.ii_2_produit_deux_ensembles.ensembles_produit import _instance_produit
from bourbaki.ensembles.fonctions.hors_ii_3.ii_2_projections.ensembles_projections import (
    projection_premiere, projection_seconde)
from bourbaki.ensembles.ii_2_couples_produit.ensembles_produit_distrib_reunion_gauche import (
    couple_dans_produit_distrib_reunion_premier_facteur)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def _hole(*termes):
    """Nom de trou de congruence FRAIS, distinct des variables libres des `termes`
    et des liants x, y, p, q.  Évite la capture quand z est lui-même nommé « w »."""
    from bourbaki.logique.i_1_termes_relations.formule import libres_t
    interdits = {"x", "y", "p", "q"}
    for t in termes:
        interdits |= libres_t(t)
    for cand in ("w", "w0", "w1", "w2", "w3"):
        if cand not in interdits:
            return cand
    return "w_frais"


# ── 1. Identité « z est un couple » sur un produit ────────────────────────────
# @livre Ch.II §R.3 Prop.26 | E.R.12 L.28-29 | PDF p.315
def couple_decomposition(a="X", b="Y", z="z"):
    """⊢ (z ∈ X×Y) ⇒ z = (pr₁z, pr₂z).

    L'en-tête de E.R.12 (z=(pr₁z,pr₂z)) restreinte aux éléments d'un produit.
    a, b : facteurs (noms OU termes) ; z : nom OU terme sans p, q libres et ≠ « w »
    (lettre réservée au trou de congruence par les tactiques composer/symetrie)."""
    vX, vY, vz = _t(a), _t(b), _t(z)
    vp, vq = var("p"), var("q")
    cpq = E.couple(vp, vq)

    inst = _instance_produit(vX, vY, vz)    # (z∈X×Y) ⇔ (∃p)(∃q)(z=(p,q) ∧ p∈X ∧ q∈Y)
    ante = et(et(egal(vz, cpq), appartient(vp, vX)), appartient(vq, vY))

    # trou de congruence frais (≠ x,y,p,q et ≠ nom de z) — évite la capture si z=« w »
    h = _hole(vz, vX, vY)
    vh = var(h)
    # ── sous témoins p, q et l'antécédent : déduire z = (pr₁z, pr₂z) ─────────────
    ha = N.assume(ante)
    zpq = conjonction_elim_gauche(conjonction_elim_gauche(ha))     # z = (p,q)
    # pr₁z = pr₁((p,q)) = p  et  pr₂z = q   (Leibniz sur z=(p,q) + projection_premiere/seconde)
    pr1z_p = composer_egalites(
        N.modus_ponens(zpq, congruence_terme(vz, cpq, E.pr1(vh), w=h)),
        projection_premiere("p", "q"))                            # pr₁z = p
    pr2z_q = composer_egalites(
        N.modus_ponens(zpq, congruence_terme(vz, cpq, E.pr2(vh), w=h)),
        projection_seconde("p", "q"))                            # pr₂z = q
    # (pr₁z,pr₂z) = (p,pr₂z) = (p,q) = z   (congruences sur les coordonnées, transitivité)
    c1 = N.modus_ponens(pr1z_p, congruence_terme(
        E.pr1(vz), vp, E.couple(vh, E.pr2(vz)), w=h))            # (pr₁z,pr₂z)=(p,pr₂z)
    c2 = N.modus_ponens(pr2z_q, congruence_terme(
        E.pr2(vz), vq, E.couple(vp, vh), w=h))                  # (p,pr₂z)=(p,q)
    cpq_eq_z = N.modus_ponens(zpq, symetrie(vz, cpq))           # (p,q)=z
    cpr_eq_z = composer_egalites(composer_egalites(c1, c2), cpq_eq_z)   # (pr₁z,pr₂z)=z
    z_eq_cpr = N.modus_ponens(cpr_eq_z, symetrie(
        E.couple(E.pr1(vz), E.pr2(vz)), vz))                    # z=(pr₁z,pr₂z)

    # décharger l'antécédent, éliminer les témoins q puis p (conclusion sans p,q libres)
    imp = N.loi_deduction(ante, z_eq_cpr)                       # ante ⇒ z=(pr₁z,pr₂z)
    elim = existe_elimination(existe_elimination(imp, "q"), "p")   # (∃p)(∃q)ante ⇒ …
    hz = N.assume(appartient(vz, E.produit(vX, vY)))
    exists_pq = N.modus_ponens(hz, equivalence_avant(inst))     # (∃p)(∃q)ante
    concl = N.modus_ponens(exists_pq, elim)                     # z=(pr₁z,pr₂z)
    return N.loi_deduction(appartient(vz, E.produit(vX, vY)), concl)


def couple_decomposition_cible(a="X", b="Y", z="z"):
    """Énoncé visé de couple_decomposition (pour vérification stricte)."""
    vX, vY, vz = _t(a), _t(b), _t(z)
    return impl(appartient(vz, E.produit(vX, vY)),
                egal(vz, E.couple(E.pr1(vz), E.pr2(vz))))


# ── 2. Extensionnalité des parties d'un produit (brique réutilisable) ─────────
def _memes_couples(va, vb, u="u", v="v"):
    """(∀u)(∀v)((u,v)∈A ⇔ (u,v)∈B)  (les deux parties ont les mêmes couples)."""
    vu, vv = var(u), var(v)
    c = E.couple(vu, vv)
    return pourtout(u, pourtout(v, equiv(appartient(c, va), appartient(c, vb))))


def _inclusion_par_couples(src, tgt, ve, vf, h_src_amb, h_couples):
    """src ⊂ tgt sous : src⊂E×F et (∀u,v)((u,v)∈src ⇔ (u,v)∈tgt).

    Renvoie Γ ⊢ src⊂tgt avec Γ = {h_src_amb.hyp, h_couples.hyp} (théorèmes
    portant ces hypothèses, pour pouvoir décharger ensemble dans l'appelant)."""
    vS, vT = _t(src), _t(tgt)
    vz = var("z")
    h = _hole(vS, vT, _t(ve), _t(vf), vz)                      # trou de Leibniz frais
    vh = var(h)
    hz = N.assume(appartient(vz, vS))                          # z∈src
    z_in_amb = N.modus_ponens(hz, instancie(h_src_amb, vz))    # z∈E×F
    z_eq = N.modus_ponens(z_in_amb, couple_decomposition(ve, vf, vz))   # z=(pr₁z,pr₂z)
    cpr = E.couple(E.pr1(vz), E.pr2(vz))
    # (pr₁z,pr₂z)∈src  (réécriture z→(pr₁z,pr₂z) dans z∈src, Leibniz S6)
    pair_in_src = N.modus_ponens(hz, equivalence_avant(N.modus_ponens(
        z_eq, N.s6(vz, cpr, h, appartient(vh, vS)))))
    # (pr₁z,pr₂z)∈tgt  (hyp. des couples instanciée en pr₁z, pr₂z)
    equ = instancie(instancie(h_couples, E.pr1(vz)), E.pr2(vz))
    pair_in_tgt = N.modus_ponens(pair_in_src, equivalence_avant(equ))
    # z∈tgt  (réécriture (pr₁z,pr₂z)→z)
    cpr_eq_z = N.modus_ponens(z_eq, symetrie(vz, cpr))
    z_in_tgt = N.modus_ponens(pair_in_tgt, equivalence_avant(N.modus_ponens(
        cpr_eq_z, N.s6(cpr, vz, h, appartient(vh, vT)))))
    return N.generalisation("z", N.loi_deduction(appartient(vz, vS), z_in_tgt))


# @livre Ch.II §R.3 Rem.- | E.R.12 L.13-14 | PDF p.315
def produit_egalite_par_couples(a="A", b="B", e="E", f="F", u="u", v="v"):
    """⊢ ( A⊂E×F ∧ B⊂E×F ∧ (∀u)(∀v)((u,v)∈A ⇔ (u,v)∈B) ) ⇒ A=B.

    EXTENSIONNALITÉ DES PARTIES D'UN PRODUIT (brique réutilisable, E.R.12) : deux
    parties d'un même produit qui contiennent les mêmes couples sont égales.
    Preuve par A1 (extensionnalité) : A⊂B et B⊂A via couple_decomposition."""
    vA, vB, vE, vF = _t(a), _t(b), _t(e), _t(f)
    amb = E.produit(vE, vF)
    couples = _memes_couples(vA, vB, u, v)
    hyp = et(et(inclus(vA, amb), inclus(vB, amb)), couples)
    h = N.assume(hyp)
    p_A_amb = conjonction_elim_gauche(conjonction_elim_gauche(h))   # A⊂E×F
    p_B_amb = conjonction_elim_droite(conjonction_elim_gauche(h))   # B⊂E×F
    p_couples = conjonction_elim_droite(h)                          # (∀u,v)((u,v)∈A⇔…∈B)
    # couples symétrisé pour B⊂A : (∀u,v)((u,v)∈B ⇔ (u,v)∈A)
    p_couples_sym = _memes_couples_symetrise(vA, vB, p_couples, u, v)

    incl_AB = _inclusion_par_couples(vA, vB, vE, vF, p_A_amb, p_couples)
    incl_BA = _inclusion_par_couples(vB, vA, vE, vF, p_B_amb, p_couples_sym)
    ext = extensionnalite_appliquee(vA, vB)                        # (A⊂B et B⊂A) ⇒ A=B
    egal_AB = N.modus_ponens(conjonction_intro(incl_AB, incl_BA), ext)   # {hyp} ⊢ A=B
    return N.loi_deduction(hyp, egal_AB)                           # ⊢ HYP ⇒ A=B


def _memes_couples_symetrise(vA, vB, p_couples, u="u", v="v"):
    """De {hyp}⊢(∀u)(∀v)((u,v)∈A⇔(u,v)∈B), déduire (∀u)(∀v)((u,v)∈B⇔(u,v)∈A)."""
    vu, vv = var(u), var(v)
    equ = instancie(instancie(p_couples, vu), vv)                 # ((u,v)∈A)⇔((u,v)∈B)
    sym = conjonction_intro(equivalence_arriere(equ), equivalence_avant(equ))
    return N.generalisation(u, N.generalisation(v, sym))


def produit_egalite_par_couples_cible(a="A", b="B", e="E", f="F", u="u", v="v"):
    """Énoncé visé de produit_egalite_par_couples."""
    vA, vB, vE, vF = _t(a), _t(b), _t(e), _t(f)
    amb = E.produit(vE, vF)
    hyp = et(et(inclus(vA, amb), inclus(vB, amb)), _memes_couples(vA, vB, u, v))
    return impl(hyp, egal(vA, vB))


# ── 3. Formule (22) en ÉGALITÉ D'ENSEMBLES ────────────────────────────────────
# @livre Ch.II §R.3 Prop.22 | E.R.12 L.20-21 | PDF p.315
def produit_distrib_reunion_premier_facteur_ensembliste(
        a="X", b="Xp", c="Y", e="E", f="F"):
    """⊢ ( X⊂E ∧ X'⊂E ∧ Y⊂F ) ⇒ (X×Y)∪(X'×Y) = (X∪X')×Y.

    FORMULE (22) du Résumé E.R.12 en ÉGALITÉ D'ENSEMBLES PLEINE.  Les deux membres
    sont ⊂ E×F sous les ambiants (X,X'⊂E, Y⊂F) ; on applique l'extensionnalité des
    parties d'un produit (produit_egalite_par_couples) avec la composante couple
    déjà prouvée (couple_dans_produit_distrib_reunion_premier_facteur)."""
    vX, vXp, vY, vE, vF = _t(a), _t(b), _t(c), _t(e), _t(f)
    A = E.reunion(E.produit(vX, vY), E.produit(vXp, vY))   # (X×Y)∪(X'×Y)
    B = E.produit(E.reunion(vX, vXp), vY)                  # (X∪X')×Y
    amb = E.produit(vE, vF)
    hyp = et(et(inclus(vX, vE), inclus(vXp, vE)), inclus(vY, vF))
    h = N.assume(hyp)
    pXE = conjonction_elim_gauche(conjonction_elim_gauche(h))   # X⊂E
    pXpE = conjonction_elim_droite(conjonction_elim_gauche(h))  # X'⊂E
    pYF = conjonction_elim_droite(h)                           # Y⊂F

    # A,B ⊂ E×F (sous les ambiants) + cœur couple-level (∀u,v)((u,v)∈A⇔(u,v)∈B)
    A_amb = _membre_gauche_inclus(vX, vXp, vY, vE, vF, pXE, pXpE, pYF)
    B_amb = _membre_droit_inclus(vX, vXp, vY, vE, vF, pXE, pXpE, pYF)
    couples = _memes_couples_22(vX, vXp, vY)
    egal_AB = N.modus_ponens(                                  # extensionnalité ⇒ A=B
        conjonction_intro(conjonction_intro(A_amb, B_amb), couples),
        produit_egalite_par_couples(A, B, vE, vF))
    return N.loi_deduction(hyp, egal_AB)


def _memes_couples_22(vX, vXp, vY, u="u", v="v"):
    """⊢ (∀u)(∀v)((u,v)∈(X×Y)∪(X'×Y) ⇔ (u,v)∈(X∪X')×Y)  (cœur couple-level, CLOS)."""
    eq = couple_dans_produit_distrib_reunion_premier_facteur(u, v, vX, vXp, vY)
    return N.generalisation(u, N.generalisation(v, eq))


def _produit_monotone(vAp, vBp, vA, vB, h_a, h_b):
    """{A'⊂A, B'⊂B} ⊢ A'×B' ⊂ A×B  (monotonie du produit ; A',B',A,B termes, h_a/h_b
    théorèmes Γ-portés).  Calque de produit_inclusion_facile, mais en TERMES (non en
    noms) et avec les inclusions fournies comme théorèmes (donc ambiants honnêtes)."""
    from bourbaki.logique.i_3_quantifies.tactiques_abrege_quantif import monotonie_existe
    from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege import syllogisme
    vp, vq, vz = var("p"), var("q"), var("z")
    pap_pa = instancie(h_a, vp)                                # p∈A' ⇒ p∈A
    qbp_qb = instancie(h_b, vq)                                # q∈B' ⇒ q∈B
    eq = egal(vz, E.couple(vp, vq))
    ante = et(et(eq, appartient(vp, vAp)), appartient(vq, vBp))
    ha = N.assume(ante)
    eq_thm = conjonction_elim_gauche(conjonction_elim_gauche(ha))   # z=(p,q)
    pap = conjonction_elim_droite(conjonction_elim_gauche(ha))      # p∈A'
    qbp = conjonction_elim_droite(ha)                              # q∈B'
    conc = conjonction_intro(conjonction_intro(eq_thm, N.modus_ponens(pap, pap_pa)),
                             N.modus_ponens(qbp, qbp_qb))           # z=(p,q) et p∈A et q∈B
    mono = monotonie_existe(monotonie_existe(N.loi_deduction(ante, conc), "q"), "p")
    z_imp = syllogisme(equivalence_avant(_instance_produit(vAp, vBp, vz)),
                       syllogisme(mono, equivalence_arriere(_instance_produit(vA, vB, vz))))
    return N.generalisation("z", z_imp)                            # A'×B' ⊂ A×B


def _membre_gauche_inclus(vX, vXp, vY, vE, vF, pXE, pXpE, pYF):
    """{X⊂E,X'⊂E,Y⊂F} ⊢ (X×Y)∪(X'×Y) ⊂ E×F."""
    XY_amb = _produit_monotone(vX, vY, vE, vF, pXE, pYF)      # X×Y⊂E×F
    XpY_amb = _produit_monotone(vXp, vY, vE, vF, pXpE, pYF)   # X'×Y⊂E×F
    return _reunion_inclus(E.produit(vX, vY), E.produit(vXp, vY),
                           E.produit(vE, vF), XY_amb, XpY_amb)


def _membre_droit_inclus(vX, vXp, vY, vE, vF, pXE, pXpE, pYF):
    """{X⊂E,X'⊂E,Y⊂F} ⊢ (X∪X')×Y ⊂ E×F."""
    XXp_E = _reunion_inclus(vX, vXp, vE, pXE, pXpE)           # X∪X'⊂E
    return _produit_monotone(E.reunion(vX, vXp), vY, vE, vF, XXp_E, pYF)


def _reunion_inclus(va, vb, vc, h_a_c, h_b_c):
    """{a⊂c, b⊂c} ⊢ a∪b ⊂ c  (la réunion de deux parties de c est ⊂ c)."""
    from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_theoremes import _instance_reunion
    from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import cas
    vz = var("z")
    inst = _instance_reunion(va, vb, vz)                      # z∈a∪b ⇔ (z∈a ∨ z∈b)
    brA = N.loi_deduction(appartient(vz, va),
                          N.modus_ponens(N.assume(appartient(vz, va)), instancie(h_a_c, vz)))
    brB = N.loi_deduction(appartient(vz, vb),
                          N.modus_ponens(N.assume(appartient(vz, vb)), instancie(h_b_c, vz)))
    hz = N.assume(appartient(vz, E.reunion(va, vb)))
    disj = N.modus_ponens(hz, equivalence_avant(inst))       # z∈a ∨ z∈b
    z_in_c = cas(disj, brA, brB)                             # z∈c
    return N.generalisation("z", N.loi_deduction(appartient(vz, E.reunion(va, vb)), z_in_c))


def produit_distrib_reunion_premier_facteur_ensembliste_cible(
        a="X", b="Xp", c="Y", e="E", f="F"):
    """Énoncé visé : l'ÉGALITÉ D'ENSEMBLES (22) sous les ambiants."""
    vX, vXp, vY, vE, vF = _t(a), _t(b), _t(c), _t(e), _t(f)
    A = E.reunion(E.produit(vX, vY), E.produit(vXp, vY))
    B = E.produit(E.reunion(vX, vXp), vY)
    hyp = et(et(inclus(vX, vE), inclus(vXp, vE)), inclus(vY, vF))
    return impl(hyp, egal(A, B))


__all__ = [
    "couple_decomposition", "couple_decomposition_cible",
    "produit_egalite_par_couples", "produit_egalite_par_couples_cible",
    "produit_distrib_reunion_premier_facteur_ensembliste",
    "produit_distrib_reunion_premier_facteur_ensembliste_cible"]
