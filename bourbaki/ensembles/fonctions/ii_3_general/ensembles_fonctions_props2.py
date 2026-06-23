"""§II.3 — Composition : propositions restantes (mission II3-fonctions-restant).

Module NEUF, complémentaire de l'existant (NE DUPLIQUE PAS) :
  • associativité de la composée de GRAPHES  → déjà clos `ensembles_composee_assoc.composee_associative`
  • Théorème 1 a) injection (f''=f'∘f injection)  → déjà clos `ensembles_retractions_props.theoreme1_a_injective`
  • composée de deux BIJECTIONS (au sens §III.3 `est_bijection_de`)  → déjà clos
        `ensembles_composee_bijection.composee_bijection`
  • image directe d'une composée (ÉGALITÉ ensembliste (G'∘G)⟨A⟩=G'⟨G⟨A⟩⟩)  → déjà
        clos `ensembles_composee.image_composee`

Ce module fournit les « directes » RESTANTES, au niveau VOCABULAIRE §II.3.8 (Déf. 10)
et CORRESPONDANCES (§II.3.3), chacune NON présente ailleurs :

  • THÉORÈME 1 b) — la composée de deux SURJECTIONS est une surjection
      (`composee_surjections`) : ⊢ (f surj. X→Y et f' surj. Y→Z) ⇒ (f'∘f surj. X→Z),
      où « surjective » est la Déf. 10 du projet `est_surjective(F,A,B) := F⟨A⟩=B`.
      CLOS, implicatif (réutilise `composee_image`, Prop. 5, dont les deux hyps SONT
      exactement les deux surjectivités).

  • THÉORÈME 1 a+b) — la composée de deux bijections est bijective AU SENS §II.49
      (`composee_bijectives`) : ⊢_{f:X→Y, f':Y→Z applications}
      (est_bijective(F,X,Y) et est_bijective(G,Y,Z)) ⇒ est_bijective(G∘F,X,Z).
      `est_bijective` (E.II.49, Déf. 10) = injective_dans ∧ surjective — DISTINCT du
      prédicat `est_bijection_de` de §III.3 qu'emploie `composee_bijection` (qui
      empile en plus « fonctionnel ∧ dom=X »).  On reste dans le vocabulaire §II.3 et
      on RECOLLE Théorème 1 a (injection) + Théorème 1 b (surjection).

  • §II.3.3 — IMAGE directe par une composée de CORRESPONDANCES, forme PONCTUELLE
      (`image_composee_membre`) : ⊢ (z ∈ (G'∘G)⟨A⟩) ⇔ (∃y)(y∈G⟨A⟩ et (y,z)∈G').
      INCONDITIONNEL.  Complète l'égalité ensembliste `image_composee` par la
      caractérisation « élément par élément » du chaînage G→G'.

  • §II.3 — LIEN fonction de deux arguments ↔ application partielle (VALEUR)
      (`coupe_couple_membre`, `valeur_deux_arguments`) : pour un graphe G de couples
      (((a,b),z)) — « fonction des deux arguments a,b » —
        ⊢ (z ∈ G⟨{(a,b)}⟩) ⇔ (((a,b),z) ∈ G)   [coupe = application partielle],
        ⊢_{G fonctionnel, (a,b)∈dom G}  (((a,b),z) ∈ G) ⇔ (z = G((a,b)))
                                        [la VALEUR G(a,b) est « le » correspondant].

Conventions :  E.composee(Gp, G) = G'∘G (Déf. 6) ; E.image(G, A) = G⟨A⟩ (Déf. 3) ;
est_surjective(F,A,B) = (F⟨A⟩=B), est_bijective(F,A,B) = injective_dans(F,A) ∧ surj.
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (Terme, var, egal, et, impl, appartient,
                                       existe, equiv)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (conjonction_intro,
                               conjonction_elim_gauche, conjonction_elim_droite,
                               equivalence_transitivite, equivalence_symetrie,
                               equivalence_avant, et_congruence_droite,
                               et_congruence_gauche, assoc_et, instancie)
from bourbaki.logique.i_3_quantifies.tactiques_abrege_quantif import (congruence_existe,
                               et_existe_droite, et_existe_gauche, existe_commute,
                               existe_elimination)
from bourbaki.ensembles.ii_3_correspondances.ensembles_correspondances import _inst_image
from bourbaki.ensembles.ii_2_couples_produit.ensembles_couples import membre_paire_gauche, singleton_membre
from bourbaki.ensembles.fonctions.ii_3_3_composee_graphes.ensembles_composee import couple_composee
from bourbaki.ensembles.fonctions.ii_3_4_fonctions_valeur.ensembles_fonctions import valeur_caracterisation


def _T(v):
    """Coercion nom→terme (accepte un Terme ou un nom de variable)."""
    return v if isinstance(v, Terme) else var(v)


def _decharge(thm, paires):
    """Décharge une liste d'hypothèses (formule, preuve) du séquent de `thm`
    par loi de déduction + modus ponens (cut)."""
    for phi, preuve in paires:
        thm = N.modus_ponens(preuve, N.loi_deduction(phi, thm))
    return thm


# ── THÉORÈME 1 b) — la composée de deux surjections est une surjection ─────────
def composee_surjections(f="F", g="G", x="X", y="Y", z="Z"):
    """⊢ (est_surjective(F,X,Y) et est_surjective(G,Y,Z)) ⇒ est_surjective(G∘F,X,Z).

    THÉORÈME 1 b) : « si f et f' sont des surjections, f'' = f'∘f est une
    surjection. »  Au niveau Déf. 10 (E.II.49) : est_surjective(F,A,B) := F⟨A⟩=B.
    Les deux hypothèses sont EXACTEMENT image(F,X)=Y et image(G,Y)=Z, qui sont les
    deux hypothèses de `composee_image` (Prop. 5) ; on en décharge la conclusion
    image(G∘F,X)=Z = est_surjective(G∘F,X,Z).  CLOS, implicatif.

    NB : `composee_image(g,f,x,y,z)` suit composee(G,F)=G∘F, donc la composée
    surjective y est E.composee(G,F) de X vers Z (f:X→Y puis g:Y→Z)."""
    from bourbaki.cardinaux.iii_3_equipotence_cardinaux.equipotence.ensembles_bijection import composee_image
    vF, vG, vX, vY, vZ = _T(f), _T(g), _T(x), _T(y), _T(z)
    surjF = E.est_surjective(vF, vX, vY)          # image(F,X) = Y
    surjG = E.est_surjective(vG, vY, vZ)          # image(G,Y) = Z
    ci = composee_image(g, f, x, y, z)            # hyps {surjF, surjG} ⊢ image(G∘F,X)=Z
    imp1 = N.loi_deduction(surjF, N.loi_deduction(surjG, ci))   # surjF ⇒ (surjG ⇒ surj(G∘F))
    hab = N.assume(et(surjF, surjG))
    inner = N.modus_ponens(conjonction_elim_droite(hab),
                           N.modus_ponens(conjonction_elim_gauche(hab), imp1))
    return N.loi_deduction(et(surjF, surjG), inner)


def cible_composee_surjections(f="F", g="G", x="X", y="Y", z="Z"):
    """Cible exacte : (est_surjective(F,X,Y) et est_surjective(G,Y,Z)) ⇒ est_surjective(G∘F,X,Z)."""
    vF, vG, vX, vY, vZ = _T(f), _T(g), _T(x), _T(y), _T(z)
    comp = E.composee(vG, vF)
    return impl(et(E.est_surjective(vF, vX, vY), E.est_surjective(vG, vY, vZ)),
                E.est_surjective(comp, vX, vZ))


# ── THÉORÈME 1 a+b) — la composée de deux bijections (au sens §II.49) ──────────
def composee_bijectives(f="F", g="G", x="X", y="Y", z="Z"):
    """⊢_{F,G func, dom F=X, dom G=Y}
       (est_bijective(F,X,Y) et est_bijective(G,Y,Z)) ⇒ est_bijective(G∘F, X, Z).

    THÉORÈME 1 a+b combiné, au VOCABULAIRE §II.49 (Déf. 10) :
    `est_bijective(F,A,B)` = injective_dans(F,A) ∧ est_surjective(F,A,B).  On RECOLLE
    le Théorème 1 a (composée d'injections, via `composee_injective`) et le Théorème
    1 b (composée de surjections, ci-dessus).  Le prédicat `est_bijective` est
    DISTINCT de `est_bijection_de` (§III.3) traité par `composee_bijection` (qui
    ajoute fonctionnel ∧ dom=X).

    Hypothèses STRUCTURELLES laissées explicites (jamais postulées : données « f:X→Y,
    f':Y→Z applications » du Théorème 1, requises par `composee_injective`) : F,G
    fonctionnels, dom F=X, dom G=Y.  (image(F,X)=Y est la surjectivité de F, donc PAS
    répétée.)"""
    from bourbaki.cardinaux.iii_3_equipotence_cardinaux.equipotence.ensembles_bijection import composee_injective
    vF, vG, vX, vY, vZ = _T(f), _T(g), _T(x), _T(y), _T(z)
    comp = E.composee(vG, vF)
    bijF = E.est_bijective(vF, vX, vY)            # inj/X ∧ image(F,X)=Y
    bijG = E.est_bijective(vG, vY, vZ)            # inj/Y ∧ image(G,Y)=Z
    hF, hG = N.assume(bijF), N.assume(bijG)
    Finj = conjonction_elim_gauche(hF)            # injective_dans(F,X)
    Fimg = conjonction_elim_droite(hF)            # image(F,X) = Y    (= surjectivité de F)
    Ginj = conjonction_elim_gauche(hG)            # injective_dans(G,Y)
    Gimg = conjonction_elim_droite(hG)            # image(G,Y) = Z    (= surjectivité de G)
    hFfunc = N.assume(E.est_fonctionnel(vF)); hGfunc = N.assume(E.est_fonctionnel(vG))
    hdomF = N.assume(egal(E.dom(vF), vX)); hdomG = N.assume(egal(E.dom(vG), vY))

    # ── Théorème 1 a : injectivité de la composée (composee_injective) ─────────
    #   hyps : F,G func, dom F=X, image(F,X)=Y, dom G=Y, F inj/X, G inj/Y
    ci = composee_injective(g, f, x, y)
    inj_comp = _decharge(ci, [
        (E.est_fonctionnel(vF), hFfunc), (E.est_fonctionnel(vG), hGfunc),
        (egal(E.dom(vF), vX), hdomF), (egal(E.image(vF, vX), vY), Fimg),
        (egal(E.dom(vG), vY), hdomG),
        (E.injective_dans(vF, vX), Finj), (E.injective_dans(vG, vY), Ginj)])

    # ── Théorème 1 b : surjectivité de la composée ─────────────────────────────
    surj_imp = composee_surjections(f, g, x, y, z)        # (surjF et surjG) ⇒ surj(G∘F)
    surj_comp = N.modus_ponens(conjonction_intro(Fimg, Gimg), surj_imp)   # image(G∘F,X)=Z

    bij_comp = conjonction_intro(inj_comp, surj_comp)     # est_bijective(G∘F,X,Z)
    imp1 = N.loi_deduction(bijF, N.loi_deduction(bijG, bij_comp))
    hab = N.assume(et(bijF, bijG))
    inner = N.modus_ponens(conjonction_elim_droite(hab),
                           N.modus_ponens(conjonction_elim_gauche(hab), imp1))
    return N.loi_deduction(et(bijF, bijG), inner)


def cible_composee_bijectives(f="F", g="G", x="X", y="Y", z="Z"):
    """Cible : (est_bijective(F,X,Y) et est_bijective(G,Y,Z)) ⇒ est_bijective(G∘F,X,Z)."""
    vF, vG, vX, vY, vZ = _T(f), _T(g), _T(x), _T(y), _T(z)
    comp = E.composee(vG, vF)
    return impl(et(E.est_bijective(vF, vX, vY), E.est_bijective(vG, vY, vZ)),
                E.est_bijective(comp, vX, vZ))


def hypotheses_composee_bijectives(f="F", g="G", x="X", y="Y"):
    """Les 4 hypothèses structurelles attendues (données « applications » du Th. 1)."""
    vF, vG, vX, vY = _T(f), _T(g), _T(x), _T(y)
    return {E.est_fonctionnel(vF), E.est_fonctionnel(vG),
            egal(E.dom(vF), vX), egal(E.dom(vG), vY)}


# ── §II.3.3 — image directe par une composée de correspondances (PONCTUEL) ─────
def image_composee_membre(gp="Gp", g="G", aa="A"):
    """⊢ (z ∈ (G'∘G)⟨A⟩) ⇔ (∃y)(y ∈ G⟨A⟩ et (y,z) ∈ G').   (§II.3.3, forme ponctuelle.)

    IMAGE directe par une COMPOSÉE de correspondances, lue « élément par élément » :
    z est atteint par G'∘G depuis A ssi il existe un maillon intermédiaire y, image
    d'un point de A par G, que G' envoie sur z.  INCONDITIONNEL.  Complète l'égalité
    ensembliste `image_composee` ((G'∘G)⟨A⟩ = G'⟨G⟨A⟩⟩) par sa caractérisation
    pointwise du chaînage G→G'.

    Preuve (réagencement C33, miroir interne de `image_composee`) :
      z∈(G'∘G)⟨A⟩ ⇔ (∃x)(x∈A et (x,z)∈G'∘G)            [axiome image]
                  ⇔ (∃x)(x∈A et (∃y)((x,y)∈G et (y,z)∈G'))   [couple_composee]
                  ⇔ (∃x)(∃y)((x∈A et (x,y)∈G) et (y,z)∈G')   [et_existe_droite + assoc_et]
                  ⇔ (∃y)(∃x)((x∈A et (x,y)∈G) et (y,z)∈G')   [existe_commute]
                  ⇔ (∃y)((∃x)(x∈A et (x,y)∈G) et (y,z)∈G')   [et_existe_gauche, ∃x rentre]
                  ⇔ (∃y)(y∈G⟨A⟩ et (y,z)∈G').                 [axiome image, sens ⇐]"""
    vGp, vG, vA = _T(gp), _T(g), _T(aa)
    vx, vy, vz = var("x"), var("y"), var("z")
    comp = E.composee(vGp, vG)
    xA = appartient(vx, vA)                                  # x∈A
    phiG = appartient(E.couple(vx, vy), vG)                  # (x,y)∈G
    phiGp = appartient(E.couple(vy, vz), vGp)                # (y,z)∈G'

    # 1) axiome image : z∈(G'∘G)⟨A⟩ ⇔ (∃x)(x∈A et (x,z)∈G'∘G)
    e1 = _inst_image(comp, vA, vz)
    # 2) déplie (x,z)∈G'∘G  → (∃y)((x,y)∈G et (y,z)∈G')   sous (∃x)(x∈A et ·)
    e2 = congruence_existe(et_congruence_droite(xA, couple_composee(gp, g, "x", "z")), "x")
    # 3) sort le ∃y :  (∃x)(x∈A et (∃y)(…)) ⇔ (∃x)(∃y)(x∈A et ((x,y)∈G et (y,z)∈G'))
    e3 = congruence_existe(et_existe_droite(xA, "y", et(phiG, phiGp)), "x")
    # 4) réassocie  x∈A et ((x,y)∈G et (y,z)∈G')  ⇔  (x∈A et (x,y)∈G) et (y,z)∈G'
    e4 = congruence_existe(congruence_existe(
        assoc_et(xA, phiG, phiGp), "y"), "x")
    # 5) commute (∃x)(∃y) ⇔ (∃y)(∃x)
    e5 = existe_commute("x", "y", et(et(xA, phiG), phiGp))
    # 6) le ∃x interne rentre dans la conjonction gauche :
    #    (∃x)((x∈A et (x,y)∈G) et (y,z)∈G') ⇔ ((∃x)(x∈A et (x,y)∈G) et (y,z)∈G')
    e6 = congruence_existe(equivalence_symetrie(
        et_existe_gauche("x", et(xA, phiG), phiGp)), "y")
    # 7) replie (∃x)(x∈A et (x,y)∈G) en y∈G⟨A⟩  (axiome image, sens inverse)
    e7 = congruence_existe(et_congruence_gauche(
        equivalence_symetrie(_inst_image(vG, vA, vy)), phiGp), "y")

    return equivalence_transitivite(e1, equivalence_transitivite(
        e2, equivalence_transitivite(e3, equivalence_transitivite(
            e4, equivalence_transitivite(e5, equivalence_transitivite(e6, e7))))))


def cible_image_composee_membre(gp="Gp", g="G", aa="A"):
    """Cible : (z ∈ (G'∘G)⟨A⟩) ⇔ (∃y)(y ∈ G⟨A⟩ et (y,z) ∈ G')."""
    vGp, vG, vA = _T(gp), _T(g), _T(aa)
    vy, vz = var("y"), var("z")
    comp = E.composee(vGp, vG)
    return equiv(appartient(vz, E.image(comp, vA)),
                 existe("y", et(appartient(vy, E.image(vG, vA)),
                                appartient(E.couple(vy, vz), vGp))))


# ── §II.3 — Lien fonction de deux arguments ↔ application partielle (VALEUR) ────
def coupe_couple_membre(g="G", a="a", b="b"):
    """⊢ (z ∈ G⟨{(a,b)}⟩) ⇔ (((a,b),z) ∈ G).   (coupe en le COUPLE (a,b), §II.3.)

    Pour un graphe G de couples (((a,b),z)) — « fonction des deux arguments a, b » —
    la COUPE suivant le point composé (a,b) caractérise l'application partielle : z
    est atteint par G en (a,b) ssi le triplet ((a,b),z) ∈ G.  INCONDITIONNEL.

    Preuve à la `coupe_membre`, mais le point est ICI un couple (a,b) (termes), d'où
    une preuve auto-portée via `singleton_membre`/`membre_paire_gauche` qui acceptent
    des termes (coupe_membre n'accepte qu'un NOM)."""
    vG, va, vb, vx, vz = _T(g), _T(a), _T(b), var("x"), var("z")
    pair = E.couple(va, vb)                                  # (a,b)
    sing = E.singleton(pair)                                 # {(a,b)}
    inst = _inst_image(vG, sing, vz)                         # z∈G⟨{(a,b)}⟩ ⇔ (∃x)(x∈{(a,b)} et (x,z)∈G)
    body = et(appartient(vx, sing), appartient(E.couple(vx, vz), vG))
    # ── ⇒ : (∃x)(x∈{(a,b)} et (x,z)∈G) ⇒ ((a,b),z)∈G ───────────────────────────
    hb = N.assume(body)
    xeq = N.modus_ponens(conjonction_elim_gauche(hb),
                         equivalence_avant(singleton_membre(vx, pair)))   # x = (a,b)
    pz_in = N.modus_ponens(conjonction_elim_droite(hb), equivalence_avant(N.modus_ponens(
        xeq, N.s6(vx, pair, "w", appartient(E.couple(var("w"), vz), vG)))))  # ((a,b),z)∈G
    avant = existe_elimination(N.loi_deduction(body, pz_in), "x")
    # ── ⇐ : ((a,b),z)∈G ⇒ (∃x)(x∈{(a,b)} et (x,z)∈G) ──────────────────────────
    h = N.assume(appartient(E.couple(pair, vz), vG))
    pair_in_sing = membre_paire_gauche(pair, pair)          # (a,b) ∈ {(a,b),(a,b)} = {(a,b)}
    wit = conjonction_intro(pair_in_sing, h)                # (a,b)∈{(a,b)} et ((a,b),z)∈G  = ((a,b)|x)body
    arriere = N.loi_deduction(appartient(E.couple(pair, vz), vG),
                              N.modus_ponens(wit, N.s5(body, pair, "x")))
    return equivalence_transitivite(inst, conjonction_intro(avant, arriere))


def cible_coupe_couple_membre(g="G", a="a", b="b"):
    """Cible : (z ∈ G⟨{(a,b)}⟩) ⇔ (((a,b),z) ∈ G).   (z = var('z').)"""
    vG, va, vb, vz = _T(g), _T(a), _T(b), var("z")
    pair = E.couple(va, vb)
    return equiv(appartient(vz, E.image(vG, E.singleton(pair))),
                 appartient(E.couple(pair, vz), vG))


def valeur_deux_arguments(g="G", a="a", b="b"):
    """⊢_{G fonctionnel, (a,b)∈dom G}  (((a,b),z) ∈ G) ⇔ (z = G((a,b))).   (§II.3, valeur.)

    LIEN « fonction de deux arguments ↔ application (valeur) » : pour un graphe G
    fonctionnel de couples (((a,b),z)), G((a,b)) = valeur(G,(a,b)) est « le »
    correspondant du couple (a,b) — l'évaluation au point composé.  C'est
    `valeur_caracterisation` instanciée au point (a,b) : la fonction de deux
    arguments rend une valeur unique G(a,b).

    Hypothèses (jamais postulées) : G fonctionnel, (a,b) dans le domaine
    [(∃y)(((a,b),y)∈G)] — exactement les conditions C46 de l'évaluation."""
    va, vb = _T(a), _T(b)
    return valeur_caracterisation(g, E.couple(va, vb))   # f,x : noms OU termes


def cible_valeur_deux_arguments(g="G", a="a", b="b"):
    """Cible : (((a,b),y) ∈ G) ⇔ (y = G((a,b))).   (y = var('y'), liant de valeur_caracterisation.)"""
    vG, va, vb, vy = _T(g), _T(a), _T(b), var("y")
    pair = E.couple(va, vb)
    return equiv(appartient(E.couple(pair, vy), vG),
                 egal(vy, E.valeur(vG, pair)))


__all__ = [
    "composee_surjections", "cible_composee_surjections",
    "composee_bijectives", "cible_composee_bijectives", "hypotheses_composee_bijectives",
    "image_composee_membre", "cible_image_composee_membre",
    "coupe_couple_membre", "cible_coupe_couple_membre",
    "valeur_deux_arguments", "cible_valeur_deux_arguments",
]
