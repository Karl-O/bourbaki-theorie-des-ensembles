"""§II.3.6 — Projections de la fonction x↦T  (Critère C54, E.II.46).

Pour  F = graphe_terme(A,T)  (le graphe de la fonction x↦T, x∈A) :

  • PREMIÈRE PROJECTION  pr₁F = A :  c'est exactement
        ensembles_cantor.graphe_terme_domaine  (⊢ dom(F) = A).
    Réexporté ici sous le nom `projection_premiere` pour le §3.6.

  • SECONDE PROJECTION  pr₂F = « l'ensemble B des objets de la forme T
    pour x∈A ».  Bourbaki (note du §3.6) :  « Si C est un ensemble contenant
    l'ensemble B des objets de la forme T pour x∈A, la fonction (F,A,C) se
    désigne par x↦T (x∈A, T∈C) ».  Le TERME COLLECTIVISANT B (= {T | x∈A})
    exige le schéma S8 (sélection-réunion) appliqué au terme T quelconque, ce
    qui dépasse l'infrastructure abrégée disponible → REPORTÉ (cf. note finale).

    PROPRIÉTÉ ATTEIGNABLE (et c'est exactement la forme sous laquelle Bourbaki
    utilise B) :  pour tout ensemble C contenant toutes les valeurs T[u] (u∈A),
    l'image  F⟨A⟩  est incluse dans C :

        `image_terme_incluse`  {(∀u)(u∈A ⇒ T[u]∈C)} ⊢ image(graphe_terme(A,T), A) ⊂ C.

    En particulier, sous la même hypothèse, l'ENSEMBLE DES VALEURS  pr₂F = img(F)
    est inclus dans C :

        `img_terme_incluse`    {(∀u)(u∈A ⇒ T[u]∈C)} ⊢ img(graphe_terme(A,T)) ⊂ C.

    C'est la caractérisation universelle de B comme PLUS PETIT tel C (B ⊂ C
    pour tout C admissible) — le contenu vérifiable de « pr₂F = B » sans le
    terme collectivisant.

Lemmes-valeur déjà certifiés (ensembles_cantor, réexportés) :
  • graphe_terme_couple_dans   {u∈A} ⊢ (u,T[u]) ∈ F ;
  • graphe_terme_valeur        {u∈A} ⊢ F(u) = T[u].

Liants : x,y = liants du corps de F (assemblage sans x ni y, fidèle à C54) ;
t = coordonnée-témoin de l'image ; z = élément courant ; w = trou de Leibniz.
"""
from __future__ import annotations

from bourbaki.logique.formule import Terme, var, egal, et, impl, appartient, pourtout, subst_t
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.logique.tactiques.tactiques_abrege2 import (conjonction_elim_gauche, conjonction_elim_droite,
                               equivalence_avant, equivalence_arriere,
                               equivalence_transitivite, instancie)
from bourbaki.logique.tactiques.tactiques_abrege_quantif import existe_elimination, alpha_existe
from bourbaki.ensembles.fonctions.ii_3_6_fonction_terme.ensembles_fonction_terme import membre_graphe_terme
# réexports §3.6
from bourbaki.cardinaux.ensembles_cantor import (graphe_terme_domaine, graphe_terme_couple_dans,
                              graphe_terme_valeur)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# ── PREMIÈRE PROJECTION : pr₁F = A ────────────────────────────────────────────
def projection_premiere(a="A", t=None, x="x", y="y", z="z"):
    """⊢ dom(graphe_terme(A,T)) = A.   (pr₁F = A, première moitié de C54.)

    Alias §3.6 de graphe_terme_domaine : la première projection du graphe de
    x↦T est son ensemble de définition A."""
    if t is None:
        t = E.singleton(var(x))
    return graphe_terme_domaine(_t(a), t, x, y, z)


# ── SECONDE PROJECTION : image(F,A) ⊂ C  pour C contenant les T[u] ────────────
def image_terme_incluse(a="A", t=None, c="C", x="x", y="y"):
    """{(∀u)(u∈A ⇒ T[u]∈C)} ⊢ image(graphe_terme(A,T), A) ⊂ C.

    Si C contient toutes les valeurs T[u] (u∈A), l'image F⟨A⟩ est incluse dans C
    (la « deuxième projection » de C54 est faite des objets de la forme T).

    z∈F⟨A⟩ ⇔ (∃t)(t∈A et (t,z)∈F)  (AXIOME_IMAGE) ;  (t,z)∈F ⇔ (t∈A et z=T[t])
    (membre_graphe_terme), donc z=T[t] avec t∈A ; l'hypothèse donne T[t]∈C, d'où
    z∈C par Leibniz.  Conclusion = (∀z)(z∈F⟨A⟩ ⇒ z∈C) = F⟨A⟩ ⊂ C."""
    vA, vC = _t(a), _t(c)
    if t is None:
        t = E.singleton(var(x))
    vz, vt = var(z := "z"), var("t")
    F = E.graphe_terme(vA, t, x)
    imgFA = E.image(F, vA)

    # Hypothèse : (∀u)(u∈A ⇒ T[u]∈C).
    Tu = subst_t(var("u"), x, t)                                # T[u]
    hyp_all = N.assume(pourtout("u", impl(appartient(var("u"), vA),
                                              appartient(Tu, vC))))
    Tt = subst_t(vt, x, t)                                       # T[t]
    hyp_t = instancie(hyp_all, vt)                               # t∈A ⇒ T[t]∈C

    # caractérisation de l'image directe : z∈F⟨A⟩ ⇔ (∃·)(·∈A et (·,z)∈F).
    # F contient « x » LIBRE → l'instanciation de AXIOME_IMAGE α-renomme son
    # liant interne « x » en un nom frais ; on le récupère et le renomme en « t ».
    ax_img = N.axiome(E.theorie_ensembles(), E.AXIOME_IMAGE)
    img_car0 = instancie(instancie(instancie(ax_img, F), vA), vz)
    impl_LtoEX = img_car0.conclusion.sous[0].sous[0].sous[0]     # ou(¬L, EX) = impl(L, EX)
    rhs_ex = impl_LtoEX.sous[1]                                  # EX = (∃·)(·∈A et (·,z)∈F)
    assert rhs_ex.tag == "exists"
    nom_lie = rhs_ex.lieur
    inner_x = et(appartient(var(nom_lie), vA),
                 appartient(E.couple(var(nom_lie), vz), F))
    ren = alpha_existe(nom_lie, "t", inner_x)                    # (∃·)…·… ⇔ (∃t)…t…
    img_car = equivalence_transitivite(img_car0, ren)           # z∈F⟨A⟩ ⇔ (∃t)(t∈A et (t,z)∈F)

    # (t,z)∈F ⇔ (t∈A et z=T[t])   (membre_graphe_terme, coordonnées t,z ;
    # nom interne du corps « yb » ≠ y pour ne pas collisionner).
    mem = membre_graphe_terme(vA, t, "t", "z", x, "yb")

    # corps existentiel : (t∈A et (t,z)∈F) ⇒ z∈C
    body = et(appartient(vt, vA), appartient(E.couple(vt, vz), F))
    hb = N.assume(body)
    t_inA = conjonction_elim_gauche(hb)                         # t∈A
    cond = N.modus_ponens(conjonction_elim_droite(hb), equivalence_avant(mem))  # t∈A et z=T[t]
    z_eq_Tt = conjonction_elim_droite(cond)                     # z=T[t]
    Tt_inC = N.modus_ponens(t_inA, hyp_t)                       # T[t]∈C
    # Leibniz : z=T[t] et T[t]∈C ⇒ z∈C  (S6 sur w∈C, sens z↦T[t] inversé)
    z_inC = N.modus_ponens(Tt_inC, equivalence_arriere(
        N.modus_ponens(z_eq_Tt, N.s6(vz, Tt, "w", appartient(var("w"), vC)))))  # z∈C
    ex_imp = existe_elimination(N.loi_deduction(body, z_inC), "t")  # (∃t)(t∈A et (t,z)∈F) ⇒ z∈C

    # z∈F⟨A⟩ ⇒ z∈C  via img_car
    z_in_img = N.assume(appartient(vz, imgFA))
    ex = N.modus_ponens(z_in_img, equivalence_avant(img_car))  # (∃t)(t∈A et (t,z)∈F)
    z_inC2 = N.modus_ponens(ex, ex_imp)                        # z∈C
    imp = N.loi_deduction(appartient(vz, imgFA), z_inC2)
    return N.generalisation("z", imp)                          # image(F,A) ⊂ C   [hyp ∀u…]


def img_terme_incluse(a="A", t=None, c="C", x="x", y="y"):
    """{(∀u)(u∈A ⇒ T[u]∈C)} ⊢ img(graphe_terme(A,T)) ⊂ C.

    L'ENSEMBLE DES VALEURS pr₂F = img(F) est inclus dans tout C contenant les
    T[u].  z∈img(F) ⇔ (∃t)((t,z)∈F)  (AXIOME_IMG) ;  (t,z)∈F ⇔ (t∈A et z=T[t])
    donc z=T[t] avec t∈A, d'où z∈C par l'hypothèse + Leibniz, comme ci-dessus.
    (Variante de image_terme_incluse sans le « t∈A » sous le ∃ — il est
    récupéré du membre du graphe.)"""
    vA, vC = _t(a), _t(c)
    if t is None:
        t = E.singleton(var(x))
    vz, vt = var("z"), var("t")
    F = E.graphe_terme(vA, t, x)
    imgF = E.img(F)

    Tu = subst_t(var("u"), x, t)
    hyp_all = N.assume(pourtout("u", impl(appartient(var("u"), vA),
                                              appartient(Tu, vC))))
    Tt = subst_t(vt, x, t)
    hyp_t = instancie(hyp_all, vt)                              # t∈A ⇒ T[t]∈C

    # z∈img(F) ⇔ (∃·)((·,z)∈F)   (AXIOME_IMG ; liant interne « x » → frais → t)
    ax_img = N.axiome(E.theorie_ensembles(), E.AXIOME_IMG)
    img_car0 = instancie(instancie(ax_img, F), vz)
    impl_LtoEX = img_car0.conclusion.sous[0].sous[0].sous[0]
    rhs_ex = impl_LtoEX.sous[1]
    assert rhs_ex.tag == "exists"
    nom_lie = rhs_ex.lieur
    inner_x = appartient(E.couple(var(nom_lie), vz), F)
    ren = alpha_existe(nom_lie, "t", inner_x)
    img_car = equivalence_transitivite(img_car0, ren)          # z∈img F ⇔ (∃t)((t,z)∈F)

    mem = membre_graphe_terme(vA, t, "t", "z", x, "yb")        # ((t,z)∈F) ⇔ (t∈A et z=T[t])

    body = appartient(E.couple(vt, vz), F)
    hb = N.assume(body)
    cond = N.modus_ponens(hb, equivalence_avant(mem))          # t∈A et z=T[t]
    t_inA = conjonction_elim_gauche(cond)                      # t∈A
    z_eq_Tt = conjonction_elim_droite(cond)                    # z=T[t]
    Tt_inC = N.modus_ponens(t_inA, hyp_t)                      # T[t]∈C
    z_inC = N.modus_ponens(Tt_inC, equivalence_arriere(
        N.modus_ponens(z_eq_Tt, N.s6(vz, Tt, "w", appartient(var("w"), vC)))))
    ex_imp = existe_elimination(N.loi_deduction(body, z_inC), "t")  # (∃t)((t,z)∈F) ⇒ z∈C

    z_in_img = N.assume(appartient(vz, imgF))
    ex = N.modus_ponens(z_in_img, equivalence_avant(img_car))
    z_inC2 = N.modus_ponens(ex, ex_imp)
    imp = N.loi_deduction(appartient(vz, imgF), z_inC2)
    return N.generalisation("z", imp)                          # img(F) ⊂ C   [hyp ∀u…]


__all__ = ["projection_premiere", "image_terme_incluse", "img_terme_incluse",
           "graphe_terme_domaine", "graphe_terme_couple_dans", "graphe_terme_valeur"]
