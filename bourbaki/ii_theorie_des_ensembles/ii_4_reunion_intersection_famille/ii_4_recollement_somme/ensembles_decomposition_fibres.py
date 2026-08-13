"""§II.4.8 — LE MARQUAGE Φ : x ↦ (x, f(x)) vers la somme des fibres (P3-P4 de S3).

La bijection-témoin de  E ≅ ⊔_{y∈F} f⁻¹⟨{y}⟩  est le MARQUAGE de chaque point
par sa valeur, de graphe (C54)

    Φ := graphe_terme( E ,  (xfb, valeur(f, xfb, b="c")) ,  "xfb" ).

LIANTS (levée du verrou liant-valeur, motif T1b-2/prop2_conjugaison) : liant de
graphe « xfb » (exotique) ; τ-liant de la valeur f(x) DANS le terme « c » (lettre SIMPLE, exigence tau_x)
(frais ≠ « y » de la machinerie graphe_terme/AXIOME_DOM) ; le pont
valeur_y_egal_cfb (alpha_tau/CS1) recolle les deux écritures de f(x).

PALIERS (un test chacun) :
  P3a marquage_fonctionnel                  ⊢ est_fonctionnel(Φ)          [CLOS]
  P3b marquage_domaine                      ⊢ dom Φ = E                   [CLOS]
  P3c marquage_valeur       {g∈E}           ⊢ Φ(g) = (g, f(g)[τc])      [1 hyp]
  P4  marque_dans_somme  {Hf2, Hf3, HF, t∈E} ⊢ T[t] ∈ ⊔(Xfib, F)
      — chaque point marqué tombe dans la somme : t ∈ fibre(f(t)) (P2), la
      fibre EST fam(Xfib, f(t)) (P1c au terme f(t)), le marqueur f(t)[c]
      est dans {f(t)} (pont α-τ), témoin i := f(t) dans AXIOME_SOMME_FAM.

Hypothèses honnêtes : cf. ensembles_fibres_famille (Hf1-Hf3, HF).
theorie_ensembles()==22 ; noyau/subst intouchés ; rien postulé.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, egal, et, appartient, subst_t, subst_f)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, equivalence_arriere, instancie)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
    symetrie)
from bourbaki.ii_theorie_des_ensembles.ii_2_couples.ii_2_1_definition_couples.ensembles_couples import (
    singleton_membre)
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_recollement_somme.ensembles_somme_indexee import (
    membre_somme_famille)
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_recollement_somme.ensembles_fibres_famille import (
    _t, _dech, fibre, famille_fibres, somme_fibres, hypothese_domaine,
    hypothese_valeurs, hypothese_pont_fam, fam_fibre_egale,
    membre_fibre_de_sa_valeur)

XB = "xfb"     # liant (C54) du graphe-terme du marquage — exotique
VC = "c"       # τ-liant de la valeur f(x) DANS le terme — LETTRE SIMPLE OBLIGÉE
#              (tau_x du niveau assemblage exige une lettre : c'est la raison du
#               « lettre simple » de T1b-2 ; « c » ne heurte aucun liant traversé
#               {x,y,z,u,v,w,p,q,i} ni les exotiques du chantier).


# ── Termes de l'énoncé ────────────────────────────────────────────────────────
def terme_marquage(f="ffb"):
    """T := (xfb, valeur(f, xfb, b="c"))  — le terme C54 de x ↦ (x, f(x))."""
    return E.couple(var(XB), E.valeur(_t(f), var(XB), b=VC))


# @livre Ch.II §4.8 Rem.- | E II.30 L.11-14 | PDF p.81
#   (« on dit qu'un ensemble E est somme d'une famille d'ensembles (X_ι)_{ι∈I}
#    lorsqu'il existe une bijection de E sur la somme de cette famille » — le
#    témoin canonique pour la famille des fibres est CE marquage x ↦ (x, f(x)).)
def graphe_marquage(f="ffb", e="Efb"):
    """Φ := graphe_terme(E, T, "xfb")   (le graphe du marquage, C54)."""
    return E.graphe_terme(_t(e), terme_marquage(f), XB)


def valeur_y_egal_cfb(f, x):
    """⊢ valeur(f,x) = valeur(f,x,b="c")   (pont α-τ y→cfb, CS1 ; f, x termes)."""
    res = N.alpha_tau(appartient(E.couple(_t(x), var("y")), _t(f)), "y", VC)
    assert res.conclusion == egal(E.valeur(_t(f), _t(x)),
                                  E.valeur(_t(f), _t(x), b=VC)), "pont α-τ : forme"
    return res


# ── P3 : Φ est une fonction définie sur tout E ────────────────────────────────
def marquage_fonctionnel(f="ffb", e="Efb"):
    """P3a ⊢ est_fonctionnel(Φ).   (C54, graphe_terme_fonctionnel ; CLOS.)"""
    from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_6_fonction_terme.ensembles_fonction_terme import (
        graphe_terme_fonctionnel)
    res = graphe_terme_fonctionnel(_t(e), terme_marquage(f), XB, "y")
    assert res.conclusion == E.est_fonctionnel(graphe_marquage(f, e)), "P3a : forme"
    assert res.est_clos, "P3a : non clos"
    return res


def marquage_domaine(f="ffb", e="Efb"):
    """P3b ⊢ dom Φ = E.   (graphe_terme_domaine ; CLOS.)"""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.cantor.ensembles_cantor import (
        graphe_terme_domaine)
    res = graphe_terme_domaine(_t(e), terme_marquage(f), XB, "y", "z")
    assert res.conclusion == egal(E.dom(graphe_marquage(f, e)), _t(e)), "P3b : forme"
    assert res.est_clos, "P3b : non clos"
    return res


def marquage_valeur(g="gfb", f="ffb", e="Efb"):
    """P3c {g ∈ E} ⊢ Φ(g) = (g, valeur(f, g, b="c")).   (g : NOM exotique.)"""
    assert isinstance(g, str), "marquage_valeur : g doit être un NOM"
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.cantor.ensembles_cantor import (
        graphe_terme_valeur)
    res = graphe_terme_valeur(_t(e), terme_marquage(f), g, XB)
    vg = var(g)
    cible = egal(E.valeur(graphe_marquage(f, e), vg),
                 subst_t(vg, XB, terme_marquage(f)))
    assert res.conclusion == cible, "P3c : forme"
    assert res.hypotheses == frozenset({appartient(vg, _t(e))}), "P3c : hyps"
    return res


# ── P4 (pointwise) : le point marqué tombe dans la somme ──────────────────────
# @livre Ch.II §4.8 Def.8 | E II.30 L.1-3 | PDF p.81
#   (chaque (t, f(t)) appartient à la réunion des copies marquées X_y×{y} — le
#    témoin est y := f(t), la copie étant fam(Xfib, f(t)) × {f(t)}.)
def marque_dans_somme(t0="tfb", f="ffb", e="Efb", b="Ffb"):
    """P4 {Hf2, Hf3, HF, t∈E} ⊢ T[t] ∈ ⊔(Xfib, F).   (t : nom exotique ou terme
    sans liant réservé ; T[t] = (t, f(t)[τc]).)

    (α) f(t)∈F [Hf3 en t] ;  (β) t ∈ fibre(f(t)) [P2] = fam(Xfib, f(t))
    [P1c au terme f(t), Leibniz arrière trou « wfb »] ;  (γ) f(t)[c] ∈ {f(t)}
    [pont α-τ + singleton_membre] ;  (δ) copie marquée [_couple_dans_produit_t] ;
    (ε) témoin i := f(t) dans AXIOME_SOMME_FAM."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_produit.ensembles_produit_commute import (
        _couple_dans_produit_t)
    vf, ve, vb, vt = _t(f), _t(e), _t(b), _t(t0)
    X = famille_fibres(f, b)
    fx = E.valeur(vf, vt)                                   # f(t)      [τ y]
    fxc = E.valeur(vf, vt, b=VC)                            # f(t)[c] [τ cfb]
    Tt = subst_t(vt, XB, terme_marquage(f))
    assert Tt == E.couple(vt, fxc), "P4 : T[t] ≠ (t, f(t)[c])"

    ht = N.assume(appartient(vt, ve))                       # t ∈ E
    # (α) f(t) ∈ F
    h3 = N.assume(hypothese_valeurs(f, e, b))
    fx_in_F = N.modus_ponens(ht, instancie(h3, vt))         # f(t) ∈ F
    # (β) t ∈ fam(Xfib, f(t))
    p2 = membre_fibre_de_sa_valeur(vt, f, e)                # {Hf2, t∈E} ⊢ t∈fibre(f(t))
    fam_eq = fam_fibre_egale(fx_in_F, fx, f, b)             # {HF,…} ⊢ fam=fibre en f(t)
    leib = N.modus_ponens(fam_eq,
        N.s6(E.valeur_famille(X, fx), fibre(f, fx), "wfb",
             appartient(vt, var("wfb"))))
    t_in_fam = N.modus_ponens(p2, equivalence_arriere(leib))    # t ∈ fam(Xfib, f(t))
    # (γ) f(t)[c] ∈ {f(t)}
    pont = valeur_y_egal_cfb(f, vt)                         # f(t) = f(t)[c]
    fxc_eq_fx = N.modus_ponens(pont, symetrie(fx, fxc))     # f(t)[c] = f(t)
    fxc_in = N.modus_ponens(fxc_eq_fx,
        equivalence_arriere(singleton_membre(fxc, fx)))     # f(t)[c] ∈ {f(t)}
    # (δ) T[t] ∈ fam(Xfib, f(t)) × {f(t)}
    prod_in = N.modus_ponens(conjonction_intro(t_in_fam, fxc_in),
        _couple_dans_produit_t(vt, fxc, E.valeur_famille(X, fx), E.singleton(fx)))
    # (ε) témoin i := f(t) dans le corps de l'axiome-somme
    corps = et(appartient(var("i"), vb),
               appartient(Tt, E.produit(E.valeur_famille(X, var("i")),
                                        E.singleton(var("i")))))
    wit = conjonction_intro(fx_in_F, prod_in)
    assert wit.conclusion == subst_f(fx, "i", corps), "P4 : témoin ≠ (f(t)|i)corps"
    ex = N.modus_ponens(wit, N.s5(corps, fx, "i"))
    res = N.modus_ponens(ex, equivalence_arriere(membre_somme_famille(X, vb, Tt)))
    assert res.conclusion == appartient(Tt, somme_fibres(f, b)), "P4 : forme"
    assert res.hypotheses == frozenset({
        hypothese_domaine(f, e), hypothese_valeurs(f, e, b),
        hypothese_pont_fam(f, b), appartient(vt, ve)}), "P4 : hyps"
    return res


__all__ = ["XB", "VC", "terme_marquage", "graphe_marquage", "valeur_y_egal_cfb",
           "marquage_fonctionnel", "marquage_domaine", "marquage_valeur",
           "marque_dans_somme"]
