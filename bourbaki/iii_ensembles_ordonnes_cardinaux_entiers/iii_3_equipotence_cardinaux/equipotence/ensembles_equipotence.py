"""§III.3.1 — Ensembles équipotents : théorèmes directs certifiés par le noyau.

Les DÉFINITIONS (Eq(X,Y), Card(X), ≤, somme/produit/exposant) sont dans
ensembles_cardinaux.py (lues verbatim dans le Texte.tex §III.3.1-3.6).  Ici, les
théorèmes DIRECTS atteignables au niveau abrégé :

  • Lemme du graphe identité (diagonale) : ((u,v) ∈ Δ_X) ⇔ (u∈X et u=v).  C'est le
    cœur du « Δ_X est le graphe de l'application identique de X » (E.III.3.1).
  • Δ_X est un graphe fonctionnel ;  dom(Δ_X) = X ;  image(Δ_X, X) = X
    (= est_surjective(Δ_X, X, X)).  (Δ_X est donc un graphe fonctionnel, partout
    défini sur X et surjectif sur X — TROIS des quatre conjoints de
    « Δ_X est le graphe d'une bijection de X sur X » témoin de Eq(X, X).)

Ces résultats établissent rigoureusement la majeure partie structurelle de la
réflexivité Eq(X, X) (Déf. 1 : Eq(X,X) vraie).

REPORTÉ honnêtement (anti-faux-résultat ; voir le rapport) :
  • le 4ᵉ conjoint, est_injective(Δ_X) : la définition du projet `est_injective(f)`
    = (∀u)(∀u')(f(u)=f(u') ⇒ u=u') est INCONDITIONNELLE (sans garde u∈X) et passe
    par les VALEURS f(u)=τy((u,y)∈F).  Pour u∉X, Δ_X(u)=τy(faux) est un objet
    indéterminé ; l'énoncé n'est donc PAS un théorème sous cette définition (deux
    points hors de X pourraient avoir la même valeur-τ).  L'injectivité ne tient
    que GARDÉE sur le graphe ((u,y)∈Δ et (u',y)∈Δ ⇒ u=u'), forme non égale au
    `est_injective` requis par `est_bijection_de`.  D'où la conjonction COMPLÈTE
    Eq(X, X) (constructible mais bloquée par ce mismatch de définition) est reportée.
  • symétrie Eq(X,Y)⇒Eq(Y,X) (réciproque d'une bijection : G⁻¹ bijection Y→X) et
    transitivité (composée de bijections : machinerie image/composée + injectivité
    par valeurs) — multi-étapes, mêmes verrous (injectivité-valeurs, capture de
    liants), reportées.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, egal, et, appartient, existe, pourtout
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege import syllogisme
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (conjonction_intro, conjonction_elim_gauche,
                               conjonction_elim_droite, equivalence_avant,
                               equivalence_arriere, equivalence_transitivite,
                               equivalence_symetrie, instancie)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import existe_elimination
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import symetrie as eg_symetrie, composer_egalites
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_theoremes import egalite_par_extension


def _inst_diag(x, z):
    """⊢ (z ∈ Δ_X) ⇔ (∃d0)(d0∈X et z=(d0,d0))   (instance de AXIOME_DIAGONALE)."""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_DIAGONALE)
    return instancie(instancie(ax, x), z)


# ── Lemme : appartenance au graphe identité Δ_X ───────────────────────────────
def diagonale_membre(x="X", u="u", v="v"):
    """⊢ ((u,v) ∈ Δ_X) ⇔ (u∈X et u=v).   (E.III.3.1 : Δ_X graphe de l'identité.)

    Δ_X = {z | (∃d0)(d0∈X et z=(d0,d0))}.  Pour z=(u,v) :  (u,v)=(d0,d0) équivaut à
    u=d0 et v=d0, donc (par Proposition 1 sur les couples) à u=v=d0, d'où la
    réduction à « u∈X et u=v ».  Liants u, v, témoin interne d0 (≠ u,v,w)."""
    vX, vu, vv = var(x), var(u), var(v)
    z = E.couple(vu, vv)
    inst = _inst_diag(vX, z)                  # (u,v)∈Δ ⇔ (∃d0)(d0∈X et (u,v)=(d0,d0))
    d0 = var("d0")
    body = et(appartient(d0, vX), egal(z, E.couple(d0, d0)))   # d0∈X et (u,v)=(d0,d0)
    cible = et(appartient(vu, vX), egal(vu, vv))               # u∈X et u=v

    # ── sens ⇒ : (∃d0)(d0∈X et (u,v)=(d0,d0)) ⇒ (u∈X et u=v) ──────────────────
    hb = N.assume(body)
    d0_in = conjonction_elim_gauche(hb)                        # d0∈X
    cpl_eq = conjonction_elim_droite(hb)                       # (u,v)=(d0,d0)
    # Proposition 1 (couples) : (u,v)=(d0,d0) ⇒ (u=d0 et v=d0)
    from bourbaki.ii_theorie_des_ensembles.ii_2_couples.ii_2_1_definition_couples.ensembles_couples import couple_egal_implique_composantes
    comp = couple_egal_implique_composantes(u, v, "d0", "d0")  # ⇒ (u=d0 et v=d0)
    uv_eq = N.modus_ponens(cpl_eq, comp)
    u_eq_d0 = conjonction_elim_gauche(uv_eq)                   # u=d0
    v_eq_d0 = conjonction_elim_droite(uv_eq)                   # v=d0
    # u∈X : de d0∈X et u=d0  (Leibniz : d0=u puis substitution)
    d0_eq_u = N.modus_ponens(u_eq_d0, eg_symetrie(vu, d0))     # d0=u
    leib_in = N.modus_ponens(d0_eq_u,
        N.s6(d0, vu, "w", appartient(var("w"), vX)))           # (d0∈X)⇔(u∈X)
    u_in = N.modus_ponens(d0_in, equivalence_avant(leib_in))   # u∈X
    # u=v : u=d0 et d0=v (=symétrie de v=d0), composer
    d0_eq_v = N.modus_ponens(v_eq_d0, eg_symetrie(vv, d0))     # d0=v
    u_eq_v = composer_egalites(u_eq_d0, d0_eq_v)               # u=v
    avant = existe_elimination(
        N.loi_deduction(body, conjonction_intro(u_in, u_eq_v)), "d0")

    # ── sens ⇐ : (u∈X et u=v) ⇒ (∃d0)(d0∈X et (u,v)=(d0,d0)) ──────────────────
    hc = N.assume(cible)
    u_inX = conjonction_elim_gauche(hc)                        # u∈X
    u_v = conjonction_elim_droite(hc)                          # u=v
    # témoin d0:=u :  u∈X  et  (u,v)=(u,u)   [car v=u ⇒ (u,v)=(u,u)]
    v_eq_u = N.modus_ponens(u_v, eg_symetrie(vu, vv))          # v=u
    # (u,v)=(u,u) : congruence sur le 2e argument du couple (trou w en 2e position)
    from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import congruence_terme
    cpl_vu = N.modus_ponens(v_eq_u, congruence_terme(vv, vu, E.couple(vu, var("w"))))
    #   v=u ⇒ (u,v)=(u,u)
    wit = conjonction_intro(u_inX, cpl_vu)                     # (u|d0)body
    arriere = N.loi_deduction(cible, N.modus_ponens(wit, N.s5(body, vu, "d0")))

    eq_red = conjonction_intro(avant, arriere)                # (∃d0)… ⇔ (u∈X et u=v)
    return equivalence_transitivite(inst, eq_red)


# ── Δ_X est un graphe fonctionnel ─────────────────────────────────────────────
def diagonale_fonctionnelle(x="X"):
    """⊢ est_fonctionnel(Δ_X).   (Δ_X est le graphe d'une application, E.III.3.1.)

    (u,v)∈Δ_X ⇒ u=v et (u,z)∈Δ_X ⇒ u=z, donc v=u=z : au plus une valeur par
    antécédent.  Conclusion == E.est_fonctionnel(Δ_X) (liants u,v,z)."""
    vX, vu, vv, vz = var(x), var("u"), var("v"), var("z")
    DX = E.diagonale(vX)
    ante = et(appartient(E.couple(vu, vv), DX), appartient(E.couple(vu, vz), DX))
    ha = N.assume(ante)
    # (u,v)∈Δ ⇒ (u∈X et u=v) ⇒ u=v
    uv = N.modus_ponens(conjonction_elim_gauche(ha),
                        equivalence_avant(diagonale_membre(x, "u", "v")))
    u_eq_v = conjonction_elim_droite(uv)                       # u=v
    uz = N.modus_ponens(conjonction_elim_droite(ha),
                        equivalence_avant(diagonale_membre(x, "u", "z")))
    u_eq_z = conjonction_elim_droite(uz)                       # u=z
    # v=z : v=u (symétrie de u=v) puis u=z
    v_eq_u = N.modus_ponens(u_eq_v, eg_symetrie(vu, vv))       # v=u
    v_eq_z = composer_egalites(v_eq_u, u_eq_z)                 # v=z
    inner = N.loi_deduction(ante, v_eq_z)                      # (…)⇒v=z
    return N.generalisation("u", N.generalisation("v", N.generalisation("z", inner)))


# ── dom(Δ_X) = X ──────────────────────────────────────────────────────────────
def diagonale_domaine(x="X"):
    """⊢ dom(Δ_X) = X.   (le graphe identité de X est défini exactement sur X.)

    z∈dom Δ_X ⇔ (∃y)((z,y)∈Δ_X) ⇔ (∃y)(z∈X et z=y) ⇔ z∈X.  Par extension (liant z,
    cohérent avec inclus/A1)."""
    vX, vz, vy = var(x), var("z"), var("y")
    # caractérisation de dom(Δ_X) : (∀z)(z∈dom Δ_X ⇔ (∃y)((z,y)∈Δ_X))
    ax_dom = N.axiome(E.theorie_ensembles(), E.AXIOME_DOM)
    DX = E.diagonale(vX)
    dom_car = instancie(instancie(ax_dom, DX), vz)            # z∈dom Δ ⇔ (∃y)((z,y)∈Δ)
    # (z,y)∈Δ_X ⇔ (z∈X et z=y)
    mem = diagonale_membre(x, "z", "y")
    # (∃y)((z,y)∈Δ) ⇔ (∃y)(z∈X et z=y)
    from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import congruence_existe
    ex_eq = congruence_existe(mem, "y")
    inX = appartient(vz, vX)
    body = et(inX, egal(vz, vy))
    # ⇒ : (∃y)(z∈X et z=y) ⇒ z∈X  (z∈X ne dépend pas de y)
    fwd = existe_elimination(
        N.loi_deduction(body, conjonction_elim_gauche(N.assume(body))), "y")
    # ⇐ : z∈X ⇒ (∃y)(z∈X et z=y)  via témoin y:=z
    h_inX = N.assume(inX)
    wit = conjonction_intro(h_inX, N.reflexivite(vz))         # z∈X et z=z = (z|y)body
    bwd = N.loi_deduction(inX, N.modus_ponens(wit, N.s5(body, vz, "y")))
    ex_inX = conjonction_intro(fwd, bwd)                      # (∃y)(z∈X et z=y) ⇔ z∈X
    # chaîner : z∈dom Δ ⇔ (∃y)((z,y)∈Δ) ⇔ (∃y)(z∈X et z=y) ⇔ z∈X
    chain = equivalence_transitivite(dom_car,
              equivalence_transitivite(ex_eq, ex_inX))         # z∈dom Δ ⇔ z∈X
    # caractérisation de X par lui-même : (∀z)(z∈X ⇔ z∈X)  (réflexivité de ⇔)
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege import a_implique_a
    selfX = N.generalisation("z", conjonction_intro(a_implique_a(inX), a_implique_a(inX)))
    char_dom = N.generalisation("z", chain)
    return egalite_par_extension(char_dom, selfX, E.dom(DX), vX)


# ── image(Δ_X, X) = X  (Δ_X surjective sur X) ─────────────────────────────────
def diagonale_image(x="X"):
    """⊢ image(Δ_X, X) = X.   (= est_surjective(Δ_X, X, X), E.III.3.1.)

    z∈Δ_X⟨X⟩ ⇔ (∃t)(t∈X et (t,z)∈Δ_X) ⇔ (∃t)(t∈X et (t∈X et t=z)) ⇔ z∈X.
    Liant z (élément, cohérent inclus/A1), témoin interne t (≠ d0 de Δ)."""
    vX, vz, vt = var(x), var("z"), var("t")
    DX = E.diagonale(vX)
    # caractérisation de l'image directe : (∀z)(z∈Δ⟨X⟩ ⇔ (∃t)(t∈X et (t,z)∈Δ))
    ax_img = N.axiome(E.theorie_ensembles(), E.AXIOME_IMAGE)
    img_car0 = instancie(instancie(instancie(ax_img, DX), vX), vz)
    # l'axiome IMAGE a son liant interne « x » ; renommer en « t » pour éviter capture
    from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import alpha_existe
    # img_car0 : z∈Δ⟨X⟩ ⇔ (∃x)(x∈X et (x,z)∈Δ)
    inner_x = et(appartient(var("x"), vX), appartient(E.couple(var("x"), vz), DX))
    ren = alpha_existe("x", "t", inner_x)                     # (∃x)…x… ⇔ (∃t)…t…
    img_car = equivalence_transitivite(img_car0, ren)        # z∈Δ⟨X⟩ ⇔ (∃t)(t∈X et (t,z)∈Δ)
    # (t,z)∈Δ ⇔ (t∈X et t=z)   →  (t∈X et (t,z)∈Δ) ⇔ (t∈X et (t∈X et t=z))
    mem = diagonale_membre(x, "t", "z")
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import et_congruence_droite
    body_eq = et_congruence_droite(appartient(vt, vX), mem)
    from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import congruence_existe
    ex_eq = congruence_existe(body_eq, "t")                   # (∃t)(t∈X et (t,z)∈Δ) ⇔ (∃t)(t∈X et (t∈X et t=z))
    # (∃t)(t∈X et (t∈X et t=z)) ⇔ z∈X
    full = et(appartient(vt, vX), et(appartient(vt, vX), egal(vt, vz)))
    # ⇒ : extraire t=z et t∈X, Leibniz → z∈X
    hf = N.assume(full)
    t_inX = conjonction_elim_gauche(hf)                       # t∈X
    t_eq_z = conjonction_elim_droite(conjonction_elim_droite(hf))   # t=z
    z_inX = N.modus_ponens(t_inX, equivalence_avant(
        N.modus_ponens(t_eq_z, N.s6(vt, vz, "w", appartient(var("w"), vX)))))  # z∈X
    fwd = existe_elimination(N.loi_deduction(full, z_inX), "t")
    # ⇐ : z∈X ⇒ (∃t)(t∈X et (t∈X et t=z))  via témoin t:=z
    inXz = appartient(vz, vX)
    h_z = N.assume(inXz)
    wit = conjonction_intro(h_z, conjonction_intro(h_z, N.reflexivite(vz)))   # (z|t)full
    bwd = N.loi_deduction(inXz, N.modus_ponens(wit, N.s5(full, vz, "t")))
    ex_inX = conjonction_intro(fwd, bwd)                     # (∃t)…full… ⇔ z∈X
    chain = equivalence_transitivite(img_car,
              equivalence_transitivite(ex_eq, ex_inX))        # z∈Δ⟨X⟩ ⇔ z∈X
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege import a_implique_a
    selfX = N.generalisation("z", conjonction_intro(a_implique_a(inXz), a_implique_a(inXz)))
    char_img = N.generalisation("z", chain)
    return egalite_par_extension(char_img, selfX, E.image(DX, vX), vX)


# ── Δ_X(u) = u  (valeur de l'application identique) ───────────────────────────
def diagonale_valeur(x="X", u="u"):
    """{u ∈ X} ⊢ Δ_X(u) = u.   (l'application identique vaut u en u, pour u∈X.)"""
    from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_4_fonctions.ensembles_fonctions import valeur_caracterisation
    vX, vu, vy = var(x), var(u), var("y")
    DX = E.diagonale(vX)
    h_inX = N.assume(appartient(vu, vX))
    uu_in = N.modus_ponens(conjonction_intro(h_inX, N.reflexivite(vu)),
                           equivalence_arriere(diagonale_membre(x, u, u)))   # (u,u)∈Δ_X
    dom_hyp = N.modus_ponens(uu_in, N.s5(appartient(E.couple(vu, vy), DX), vu, "y"))
    vc_u = instancie(N.generalisation("y", valeur_caracterisation(DX, vu)), vu)  # ((u,u)∈Δ⇔u=Δ(u))
    u_eq = N.modus_ponens(uu_in, equivalence_avant(vc_u))                    # u=Δ(u)
    step1 = N.modus_ponens(dom_hyp, N.loi_deduction(
        existe("y", appartient(E.couple(vu, vy), DX)), u_eq))               # u=Δ(u) [hyps u∈X, Δ func]
    step2 = N.modus_ponens(diagonale_fonctionnelle(x),
                           N.loi_deduction(E.est_fonctionnel(DX), step1))   # u=Δ(u) [hyp u∈X]
    return N.modus_ponens(step2, eg_symetrie(vu, E.valeur(DX, vu)))         # Δ_X(u)=u


# ── injectivité (gardée) de Δ_X ───────────────────────────────────────────────
def diagonale_injective(x="X"):
    """⊢ injective_dans(Δ_X, X).   (l'application identique est injective sur X.)"""
    vX, vu, vup = var(x), var("u"), var("up")
    DX = E.diagonale(vX)
    hyp = et(et(appartient(vu, vX), appartient(vup, vX)),
             egal(E.valeur(DX, vu), E.valeur(DX, vup)))
    h = N.assume(hyp)
    uinX = conjonction_elim_gauche(conjonction_elim_gauche(h))
    upinX = conjonction_elim_droite(conjonction_elim_gauche(h))
    val_eq = conjonction_elim_droite(h)                                     # Δ(u)=Δ(u')
    du = N.modus_ponens(uinX, N.loi_deduction(appartient(vu, vX), diagonale_valeur(x, "u")))   # Δ(u)=u
    dup = N.modus_ponens(upinX, N.loi_deduction(appartient(vup, vX), diagonale_valeur(x, "up")))  # Δ(u')=u'
    u_eq_du = N.modus_ponens(du, eg_symetrie(E.valeur(DX, vu), vu))         # u=Δ(u)
    u_eq_up = composer_egalites(composer_egalites(u_eq_du, val_eq), dup)    # u=u'
    inner = N.loi_deduction(hyp, u_eq_up)
    return N.generalisation("u", N.generalisation("up", inner))            # injective_dans(Δ_X, X)


# ── Réflexivité de l'équipotence : Eq(X, X) ───────────────────────────────────
# @livre Ch.III §3.1 Rem.- | E III.23 L.20-20 | PDF p.126
#   (« D'autre part, Eq(X, X) est vraie. » — témoin Δ_X, formalisé ici.)
def equipotence_reflexive(x="X"):
    """⊢ Eq(X, X).   (RÉFLEXIVITÉ de l'équipotence, E.III.3.1 — Δ_X est une bijection X→X.)"""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import est_bijection_de
    vX = var(x)
    DX = E.diagonale(vX)
    bij = conjonction_intro(
        conjonction_intro(diagonale_fonctionnelle(x), diagonale_domaine(x)),
        conjonction_intro(diagonale_injective(x), diagonale_image(x)))     # est_bijection_de(Δ_X,X,X)
    return N.modus_ponens(bij, N.s5(est_bijection_de(var("F"), vX, vX), DX, "F"))   # (∃F)… = Eq(X,X)


__all__ = ["diagonale_membre", "diagonale_fonctionnelle", "diagonale_domaine",
           "diagonale_image", "diagonale_valeur", "diagonale_injective",
           "equipotence_reflexive"]
