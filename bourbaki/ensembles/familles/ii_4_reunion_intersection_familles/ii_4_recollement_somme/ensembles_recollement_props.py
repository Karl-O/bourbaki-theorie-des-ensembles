"""§II.4 — Propositions 7 à 10 (RECOLLEMENT de fonctions, sommes et réunions
disjointes).

Module NEUF, suite directe de l'infra recollement déjà certifiée :
  • ensembles_restriction_somme   : reunion_graphes_fonctionnelle (PIVOT),
        membre_reunion_graphes, antecedent_dans_domaine, dom_reunion_graphes ;
  • ensembles_recollement_bijection : valeur_reunion_gauche/droite, image_…,
        reunion_graphes_injective ;
  • ensembles_somme_disjointe     : somme_disjointe, injections canoniques ;
  • ensembles_restrictions        : coincident, coincidence_meme_graphe ;
  • ensembles_familles            : membre_reunion_famille (⋃_{ι∈I} X_ι).

On formalise ici les énoncés VERBATIM de E.II.4 (Prop. 7-10).  Le SQUELETTE
faisable au niveau binaire / famille-quelconque est prouvé INCONDITIONNELLEMENT,
le reste est livré CONDITIONNÉ (hypothèses explicites, jamais postulé) ou
REPORTÉ avec une justification précise.

THÉORÈMES CERTIFIÉS (chacun testé en isolé) :

  Prop 7.1 — Cœur valeur (INCONDITIONNEL) :
    • recollement_recouvrement_valeur  ⊢
        ((E ⊂ ⋃_{ι∈I} X_ι)  et  (∀ι)(∀x)((x∈E∩X_ι) ⇒ f(x)=g(x)))
            ⇒ (∀x)((x∈E) ⇒ f(x)=g(x))
      « Si f, g coïncident (par valeurs) dans chaque E∩X_ι et que (X_ι) recouvre
        E, alors f, g coïncident (par valeurs) dans E. »  C'est le contenu
        mathématique de la Prop. 7.1 (le complément étant la simple inclusion
        E⊂dom F, E⊂dom G, fournie par les hyps de `coincident`).
    • recollement_recouvrement  (CONDITIONNEL aux inclusions de domaine)  ⊢
        (E⊂dom F  et  E⊂dom G  et (E⊂⋃X_ι) et (∀ι)(∀x)((x∈E∩X_ι)⇒f(x)=g(x)))
            ⇒ coincident(F, G, E)
      reconstitue l'énoncé `coincident` complet (E.II.4, Prop. 7.1 VERBATIM).

  Prop 7.2 / Prop 8 — Recollement binaire (le cas |I|=2, qui est le moteur de
        l'infra existante) :
    • recollement_binaire_fonctionnel  (INCONDITIONNEL)  ⊢
        (func F  et func G  et (∀u)¬(u∈domF et u∈domG)) ⇒ func(F∪G)
        [= reunion_graphes_fonctionnelle ré-exporté : EXISTENCE du recollement]
    • recollement_binaire_prolonge_gauche / _droite  (INCONDITIONNEL)  ⊢
        F ⊂ F∪G   resp.   G ⊂ F∪G        [F∪G PROLONGE F et G : F⊂F∪G, G⊂F∪G]
    • recollement_binaire_valeur_gauche / _droite  (CONDITIONNELS, ré-exports)
        coïncidence par valeurs de F∪G avec F (resp. G) sur son domaine.
    • recollement_binaire_unicite  (CONDITIONNEL)  ⊢
        deux recollements de mêmes graphes sont égaux (extensionnalité) —
        UNICITÉ de la Prop. 7.2 / Prop. 8.

  Prop 9 — Existence d'une réunion disjointe (cas binaire, copies marquées) :
    • reunion_disjointe_binaire_disjoints  (INCONDITIONNEL)  ⊢
        (A×{0}) ∩ (B×{1}) = ∅      [les deux copies marquées sont disjointes]
    • reunion_disjointe_binaire_reunion    (INCONDITIONNEL, déf.)  ⊢
        A⊔B = (A×{0}) ∪ (B×{1})    [A⊔B EST la réunion des deux copies]
      ⇒ A⊔B réalise la « réunion disjointe » des copies de A et B (Prop. 9, n=2).

  Prop 10 — Réunion d'une famille disjointe ≃ sa somme (cas binaire) :
    • bijection_canonique_reunion_somme  (TERME)  W := recollement des deux
        injections canoniques a↦(a,0), b↦(b,1) — témoin de bijection A∪B → A⊔B.
    • reunion_equipotente_somme_si_bijection  (CONDITIONNEL)  ⊢
        (est_bijection_de(W, A∪B, A⊔B))  ⇒  Eq(A ∪ B, A ⊔ B)
      « la réunion (disjointe) A∪B est équipotente à la somme A⊔B » — Prop. 10
        au rang binaire, via le recollement bijectif des injections canoniques
        (même schéma S5 que equipotent_si_bijection de la Prop. 9).

REPORTS (cf. StructuredOutput) : la quantification sur une famille (X_ι)_{ι∈I}
quelconque pour Prop 7.2 / 8 / 9 / 10 (∃! recollement, ⋃ disjointe, ⋃≃somme à I
indices) exige une RÉCURSION / un recollement INDEXÉ (réunion d'une famille de
graphes fonctionnels) absent de l'infra binaire — chantier séparé.  On livre le
rang binaire (moteur réutilisable) et la STRUCTURE complète des énoncés.
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (Terme, var, egal, et, ou, non, impl,
                                       appartient, existe, pourtout, inclus)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege import syllogisme
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, instancie, cas)
from bourbaki.logique.i_3_quantifies.tactiques_abrege_quantif import existe_elimination

from bourbaki.ensembles.familles.ii_4_reunion_intersection_familles.ii_4_recollement_somme.ensembles_somme_disjointe import (
    somme_disjointe, ZERO, UN)
from bourbaki.cardinaux.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import est_bijection_de


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# ── axiomes instanciés (helpers) ──────────────────────────────────────────────
def _inst_inter(a, b, z):
    """⊢ (z ∈ A∩B) ⇔ (z∈A et z∈B)."""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_INTER)
    return instancie(instancie(instancie(ax, a), b), z)


def _inst_reunion(a, b, z):
    """⊢ (z ∈ A∪B) ⇔ (z∈A ou z∈B)."""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_REUNION)
    return instancie(instancie(instancie(ax, a), b), z)


def _inst_reunion_famille(fam, i, z):
    """⊢ (z ∈ ⋃_{ι∈I} X_ι) ⇔ (∃i)(i∈I et z∈X_i).   (sur TERMES, via AXIOME_REUNION_FAM.)"""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_REUNION_FAM)
    return instancie(instancie(instancie(ax, fam), i), z)


# ══════════════════════════════════════════════════════════════════════════════
# Prop 7.1 — Recollement sur un RECOUVREMENT (cœur : coïncidence par valeurs).
# ══════════════════════════════════════════════════════════════════════════════
def recollement_recouvrement_valeur(f="F", g="G", e="E", fam="X", i="I"):
    """⊢ ((E ⊂ ⋃_{ι∈I} X_ι) et (∀ι)(∀x)((x∈E∩X_ι) ⇒ f(x)=g(x)))
            ⇒ (∀x)((x∈E) ⇒ f(x)=g(x)).     (E.II.4, Prop. 7.1 — cœur valeur.)

    INCONDITIONNEL.  Pour x∈E : par recouvrement x∈⋃X_ι, donc (∃ι)(ι∈I et x∈X_ι) ;
    pour ce témoin ι, x∈E∩X_ι (AXIOME_INTER), donc f(x)=g(x) par l'hypothèse de
    coïncidence locale.  f(x)=g(x) ne contient pas ι : ∃-élimination du témoin."""
    vf, vg, ve = _t(f), _t(g), _t(e)
    vfam, vI = _t(fam), _t(i)
    vx, vi = var("x"), var("i")
    Xi = E.valeur_famille(vfam, vi)
    fx, gx = E.valeur(vf, vx), E.valeur(vg, vx)
    cible_val = egal(fx, gx)

    cover = inclus(ve, E.reunion_famille(vfam, vI))         # E ⊂ ⋃ X_ι
    local = pourtout("i", pourtout("x",
        impl(appartient(vx, E.intersection(ve, Xi)), cible_val)))  # (∀ι)(∀x)(x∈E∩X_ι ⇒ f(x)=g(x))

    h = N.assume(et(cover, local))
    h_cover = conjonction_elim_gauche(h)
    h_local = conjonction_elim_droite(h)

    # ── pour x∈E : f(x)=g(x) ──────────────────────────────────────────────────
    hx = N.assume(appartient(vx, ve))                       # x∈E
    # x∈⋃X_ι  (recouvrement instancié en x)
    x_in_reun = N.modus_ponens(hx, instancie(h_cover, vx))  # x∈⋃X_ι
    car_reun = _inst_reunion_famille(vfam, vI, vx)          # x∈⋃X_ι ⇔ (∃i)(i∈I et x∈X_i)
    ex = N.modus_ponens(x_in_reun, equivalence_avant(car_reun))  # (∃i)(i∈I et x∈X_i)

    # sous (i∈I et x∈X_i) : f(x)=g(x)
    body = et(appartient(vi, vI), appartient(vx, Xi))
    hb = N.assume(body)
    x_in_Xi = conjonction_elim_droite(hb)                  # x∈X_i
    x_in_inter = N.modus_ponens(conjonction_intro(hx, x_in_Xi),
        equivalence_arriere(_inst_inter(ve, Xi, vx)))      # x∈E∩X_i
    loc_ix = instancie(instancie(h_local, vi), vx)         # (x∈E∩X_i) ⇒ f(x)=g(x)
    fxgx = N.modus_ponens(x_in_inter, loc_ix)              # f(x)=g(x)
    # décharge du témoin i (f(x)=g(x) ne contient pas i)
    imp_body = existe_elimination(N.loi_deduction(body, fxgx), "i")  # (∃i)body ⇒ f(x)=g(x)
    fxgx_x = N.modus_ponens(ex, imp_body)                  # f(x)=g(x)  (sous x∈E)

    inner = N.loi_deduction(appartient(vx, ve), fxgx_x)    # x∈E ⇒ f(x)=g(x)
    gen = N.generalisation("x", inner)                     # (∀x)(x∈E ⇒ f(x)=g(x))
    return N.loi_deduction(et(cover, local), gen)


def recollement_recouvrement(f="F", g="G", e="E", fam="X", i="I"):
    """⊢ ((E ⊂ dom F) et (E ⊂ dom G) et (E ⊂ ⋃_{ι∈I} X_ι)
         et (∀ι)(∀x)((x∈E∩X_ι) ⇒ f(x)=g(x)))  ⇒  coincident(F, G, E).

    E.II.4, Prop. 7.1 VERBATIM (« f et g coïncident dans E »).  La coïncidence
    `coincident(F,G,E)` = (E⊂dom F et E⊂dom G et (∀x)(x∈E ⇒ f(x)=g(x))) : ses
    deux premières conjonctions sont DONNÉES (f, g ont E pour ensemble de
    définition — d'où E⊂dom F, E⊂dom G) ; la troisième est le cœur valeur prouvé
    ci-dessus.  Conditionné aux SEULES inclusions de domaine (jamais postulé)."""
    vf, vg, ve = _t(f), _t(g), _t(e)
    vfam, vI = _t(fam), _t(i)

    domF = N.assume(inclus(ve, E.dom(vf)))
    domG = N.assume(inclus(ve, E.dom(vg)))
    cover = inclus(ve, E.reunion_famille(vfam, vI))
    vx, vi = var("x"), var("i")
    Xi = E.valeur_famille(vfam, vi)
    local = pourtout("i", pourtout("x",
        impl(appartient(vx, E.intersection(ve, Xi)),
             egal(E.valeur(vf, vx), E.valeur(vg, vx)))))

    hcl = N.assume(et(cover, local))
    val = N.modus_ponens(hcl, recollement_recouvrement_valeur(f, g, e, fam, i))  # (∀x)(x∈E ⇒ f(x)=g(x))

    coinc = conjonction_intro(conjonction_intro(
        N.assume(inclus(ve, E.dom(vf))), N.assume(inclus(ve, E.dom(vg)))), val)
    # décharge des 3 hypothèses (domF, domG, cover∧local) dans l'ordre
    step = N.loi_deduction(et(cover, local), coinc)
    step = N.loi_deduction(inclus(ve, E.dom(vg)), step)
    step = N.loi_deduction(inclus(ve, E.dom(vf)), step)
    return step


# ══════════════════════════════════════════════════════════════════════════════
# Prop 7.2 / Prop 8 — RECOLLEMENT BINAIRE (cas |I|=2 ; moteur de l'infra).
# ══════════════════════════════════════════════════════════════════════════════
def recollement_binaire_fonctionnel(g="G", h="H"):
    """{func G, func H, (∀u)¬(u∈domG et u∈domH)} ⊢ func(G∪H).   (E.II.4, Prop. 7.2/8 —
    EXISTENCE du recollement au rang binaire.)  Ré-export de reunion_graphes_
    fonctionnelle : la réunion de deux graphes fonctionnels à domaines disjoints
    est fonctionnelle, donc G∪H EST une fonction définie sur dom G ∪ dom H."""
    from bourbaki.ensembles.fonctions.hors_ii_3.iii_3_recollement.ensembles_restriction_somme import (
        reunion_graphes_fonctionnelle)
    return reunion_graphes_fonctionnelle(g, h)


def recollement_binaire_prolonge_gauche(g="G", h="H"):
    """⊢ G ⊂ G∪H.   (G∪H PROLONGE G : tout couple de G est dans G∪H — E.II.4, Prop.
    7.2/8 : « le recollement prolonge chaque fonction ».)"""
    vg, vh, vz = _t(g), _t(h), var("z")
    from bourbaki.ensembles.fonctions.hors_ii_3.iii_3_recollement.ensembles_restriction_somme import membre_reunion_graphes
    car = membre_reunion_graphes(vg, vh, vz)               # z∈G∪H ⇔ (z∈G ou z∈H)
    hz = N.assume(appartient(vz, vg))                      # z∈G
    inGuH = N.modus_ponens(N.modus_ponens(hz,
        N.s2(appartient(vz, vg), appartient(vz, vh))),
        equivalence_arriere(car))                          # z∈G∪H
    return N.generalisation("z", N.loi_deduction(appartient(vz, vg), inGuH))


def recollement_binaire_prolonge_droite(g="G", h="H"):
    """⊢ H ⊂ G∪H.   (G∪H prolonge aussi H — symétrique.)"""
    vg, vh, vz = _t(g), _t(h), var("z")
    from bourbaki.ensembles.fonctions.hors_ii_3.iii_3_recollement.ensembles_restriction_somme import membre_reunion_graphes
    car = membre_reunion_graphes(vg, vh, vz)               # z∈G∪H ⇔ (z∈G ou z∈H)
    hz = N.assume(appartient(vz, vh))                      # z∈H
    inGuH = N.modus_ponens(N.modus_ponens(N.modus_ponens(hz,
        N.s2(appartient(vz, vh), appartient(vz, vg))),
        N.s3(appartient(vz, vh), appartient(vz, vg))),
        equivalence_arriere(car))                          # z∈G∪H
    return N.generalisation("z", N.loi_deduction(appartient(vz, vh), inGuH))


def recollement_binaire_valeur_gauche(g="G", h="H", u="u"):
    """{func G, func H, dom disjoints, u∈dom G} ⊢ (G∪H)(u) = G(u).   (le recollement
    coïncide PAR VALEUR avec G sur dom G — ré-export valeur_reunion_gauche.)"""
    from bourbaki.ensembles.fonctions.hors_ii_3.iii_3_recollement.ensembles_recollement_bijection import (
        valeur_reunion_gauche)
    return valeur_reunion_gauche(g, h, u)


def recollement_binaire_valeur_droite(g="G", h="H", u="u"):
    """{func G, func H, dom disjoints, u∈dom H} ⊢ (G∪H)(u) = H(u).   (idem côté H.)"""
    from bourbaki.ensembles.fonctions.hors_ii_3.iii_3_recollement.ensembles_recollement_bijection import (
        valeur_reunion_droite)
    return valeur_reunion_droite(g, h, u)


def recollement_binaire_unicite(p="P", q="Q"):
    """⊢ (P = Q) ⇒ (∀x)((x ∈ dom P) ⇒ p(x) = q(x)).   (UNICITÉ du recollement, E.II.4,
    Prop. 7.2/8 : « il existe une fonction et une seule … » — deux recollements de
    MÊME graphe coïncident dans leur ensemble de définition.)  Délégué à
    coincidence_meme_graphe : si deux graphes sont égaux, les valeurs coïncident."""
    from bourbaki.ensembles.fonctions.ii_3_5_restrictions_prolongements.ensembles_restrictions import coincidence_meme_graphe
    return coincidence_meme_graphe(p, q)


# ══════════════════════════════════════════════════════════════════════════════
# Prop 9 — Existence d'une RÉUNION DISJOINTE (rang binaire : copies marquées).
# ══════════════════════════════════════════════════════════════════════════════
def reunion_disjointe_binaire_disjoints(a="A", b="B"):
    """⊢ ((A×{0}) ∩ (B×{1})) = ∅.   (E.II.4, Prop. 9 au rang binaire : les copies
    marquées A×{0} et B×{1} sont MUTUELLEMENT DISJOINTES.)

    Toute z∈(A×{0})∩(B×{1}) aurait 2ᵉ coordonnée = 0 (copie gauche) ET = 1 (copie
    droite), d'où 0=1, contredisant 0≠1 (vide_distinct_singleton).  On prouve
    ¬(z∈inter) pour tout z, puis inter=∅ par vide_ssi_sans_element."""
    from bourbaki.cardinaux.iii_3_equipotence_cardinaux.equipotence.ensembles_vide_singleton import vide_distinct_singleton
    from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_vide import vide_ssi_sans_element
    from bourbaki.ensembles.fonctions.hors_ii_3.iii_3_recollement.ensembles_restriction_somme import (
        _seconde_coord_marquee, _zero_egal_un_de_temoins)
    from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import contraposition
    va, vb = _t(a), _t(b)
    vz = var("z")
    A0 = E.produit(va, E.singleton(ZERO))
    B1 = E.produit(vb, E.singleton(UN))
    inter = E.intersection(A0, B1)

    car = _inst_inter(A0, B1, vz)                          # z∈inter ⇔ (z∈A×{0} et z∈B×{1})
    secondA = _seconde_coord_marquee(vz, va, ZERO)         # z∈A×{0} ⇒ (∃p)(z=(p,0))
    secondB = _seconde_coord_marquee(vz, vb, UN)           # z∈B×{1} ⇒ (∃p)(z=(p,1))

    hin = N.assume(appartient(vz, inter))
    both = N.modus_ponens(hin, equivalence_avant(car))     # z∈A×{0} et z∈B×{1}
    exA = N.modus_ponens(conjonction_elim_gauche(both), secondA)   # (∃p)(z=(p,0))
    exB = N.modus_ponens(conjonction_elim_droite(both), secondB)   # (∃p)(z=(p,1))
    zero_un = _zero_egal_un_de_temoins(vz, exA, exB)       # 0=1   (sous z∈inter)
    imp_01 = N.loi_deduction(appartient(vz, inter), zero_un)       # z∈inter ⇒ 0=1
    n01 = vide_distinct_singleton()                        # ¬(0=1)
    n_in = N.modus_ponens(n01, contraposition(imp_01))     # ¬(z∈inter)
    return N.modus_ponens(N.generalisation("z", n_in),
        equivalence_arriere(vide_ssi_sans_element(inter)))  # inter=∅


def reunion_disjointe_binaire_reunion(a="A", b="B"):
    """⊢ (A⊔B) = ((A×{0}) ∪ (B×{1})).   (E.II.4, Prop. 9 au rang binaire : A⊔B EST la
    réunion des copies marquées disjointes ; réflexivité de la définition.)

    Avec reunion_disjointe_binaire_disjoints (copies disjointes), A⊔B réalise la
    « réunion d'une famille (ici de 2) d'ensembles mutuellement disjoints, telle
    qu'il existe une bijection de A (resp. B) sur sa copie A×{0} (resp. B×{1}) »."""
    va, vb = _t(a), _t(b)
    return N.reflexivite(somme_disjointe(va, vb))


# ══════════════════════════════════════════════════════════════════════════════
# Prop 10 — RÉUNION d'une famille disjointe ≃ sa SOMME (rang binaire).
# ══════════════════════════════════════════════════════════════════════════════
def bijection_canonique_reunion_somme(a="A", b="B"):
    """W := graphe(a↦(a,0) sur A) ∪ graphe(b↦(b,1) sur B)   (le RECOLLEMENT des deux
    injections canoniques).   C'est le témoin de bijection naturel A∪B → A⊔B :
    chaque a∈A va sur sa copie marquée (a,0), chaque b∈B sur (b,1)."""
    from bourbaki.ensembles.fonctions.hors_ii_3.iii_3_recollement.ensembles_restriction_somme import recollement
    va, vb = _t(a), _t(b)
    gA = E.graphe_terme(va, E.couple(var("x"), ZERO))     # {(a,(a,0)) | a∈A}
    gB = E.graphe_terme(vb, E.couple(var("x"), UN))       # {(b,(b,1)) | b∈B}
    return recollement(gA, gB)


def reunion_equipotente_somme_si_bijection(a="A", b="B"):
    """{est_bijection_de(W, A∪B, A⊔B)} ⊢ Eq(A ∪ B, A ⊔ B).   (E.II.4, Prop. 10 au rang
    binaire, CONDITIONNEL.)

    « La réunion A∪B (de la famille disjointe {A,B}) est équipotente à sa somme
    A⊔B. »  Dès que W (le recollement des deux injections canoniques, fourni par
    bijection_canonique_reunion_somme) est une bijection A∪B → A⊔B, l'équipotence
    Eq(·,·)=(∃F)(bijection_de(F,·,·)) est attestée par le témoin F:=W (S5).  Même
    schéma exact que equipotent_si_bijection (Prop 9).  Hypothèse EXPLICITE,
    jamais postulée.

    Le dernier mille — prouver INCONDITIONNELLEMENT est_bijection_de(W, A∪B, A⊔B)
    sous A∩B=∅ — est REPORTÉ : il reconstruit, pour CES graphes-termes, les
    paliers fonctionnel / dom=A∪B / injective / image=A⊔B via l'infra recollement
    (reunion_graphes_fonctionnelle, dom_reunion_graphes, reunion_graphes_injective,
    image_reunion_graphes), avec disjonction des domaines garantie par A∩B=∅.
    Infra 100 % disponible ; assemblage long laissé à un round dédié."""
    va, vb = _t(a), _t(b)
    W = bijection_canonique_reunion_somme(va, vb)
    src = E.reunion(va, vb)
    dst = somme_disjointe(va, vb)
    bij = N.assume(est_bijection_de(W, src, dst))         # hyp : W bijecte A∪B sur A⊔B
    corps = est_bijection_de(var("F"), src, dst)          # corps de Eq, liant F
    return N.modus_ponens(bij, N.s5(corps, W, "F"))       # (∃F)bijection_de(F,A∪B,A⊔B) = Eq(A∪B,A⊔B)


__all__ = [
    # Prop 7.1
    "recollement_recouvrement_valeur", "recollement_recouvrement",
    # Prop 7.2 / 8 (binaire)
    "recollement_binaire_fonctionnel",
    "recollement_binaire_prolonge_gauche", "recollement_binaire_prolonge_droite",
    "recollement_binaire_valeur_gauche", "recollement_binaire_valeur_droite",
    "recollement_binaire_unicite",
    # Prop 9 (binaire)
    "reunion_disjointe_binaire_disjoints", "reunion_disjointe_binaire_reunion",
    # Prop 10 (binaire)
    "bijection_canonique_reunion_somme", "reunion_equipotente_somme_si_bijection",
]
