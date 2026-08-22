# -*- coding: utf-8 -*-
"""§III.6.3 — K6e : L'ITÉRÉE EST UNE BIJECTION DE ℕ SUR SON IMAGE.

🎯 CIBLE (g := le témoin gcap, hypothétique via le corps FORT ; D := g⟨ℕ⟩) :

    equipotence_iteree :
        { corps_c63_fort(S_c, x0),  x0∈E,  u⊂E×E,  dom u=E,  hors,  inj }
            ⊢ Eq( ℕ, g⟨ℕ⟩ )                                        [6 hyps]

Le témoin de l'équipotence est g LUI-MÊME : fonctionnel et dom g=ℕ viennent
du corps fort ; l'injectivité gardée sur ℕ est la conversion de K6d
(injectivite_iteree, forme curryfiée → injective_dans) ; la surjectivité sur
D := g⟨ℕ⟩ est une RÉFLEXIVITÉ (image(g,ℕ) = image(g,ℕ)) — la surjectivité
sur l'image est gratuite par définition.  S5 au témoin g referme l'∃F.

theorie_ensembles() INCHANGÉE (22).  Noyau INTACT.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, et, appartient,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E

from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    instancie,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    equipotent, est_bijection_de,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_1_n_objet_existence.ensembles_ensemble_NN import (
    ensemble_NN,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.couverture_rec.capstone.ensembles_c63_vrai import (
    corps_c63, corps_c63_fort,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_3_infinis_denombrables.lemme1_denombrable.ensembles_regle_clampee import (
    regle_clampee,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_3_infinis_denombrables.lemme1_denombrable.ensembles_valeurs_iteration import (
    _cut,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_3_infinis_denombrables.lemme1_denombrable.ensembles_injectivite_finale import (
    injectivite_iteree,
)


def _t(t):
    """Coercion str/Terme → Terme."""
    return t if isinstance(t, Terme) else var(t)


def injective_dans_iteree(u, x0, e, g="gcap", zname="zcl", yname="ycl"):
    """{6 hyps de injectivite_iteree} ⊢ injective_dans(g, ℕ)  (conversion de forme).

    De la curryfiée (∀n∈ℕ)(∀m∈ℕ)(g(m)=g(n)⇒m=n) vers la gardée
    (∀u)(∀u')((u∈ℕ ∧ u'∈ℕ ∧ g(u)=g(u')) ⇒ u=u')."""
    vg = _t(g)
    NN = ensemble_NN()
    inj = injectivite_iteree(u, x0, e, g)
    vu_, vup = var("u"), var("up")
    ant = et(et(appartient(vu_, NN), appartient(vup, NN)),
             egal(E.valeur(vg, vu_), E.valeur(vg, vup)))
    h_ant = N.assume(ant)
    u_in = conjonction_elim_gauche(conjonction_elim_gauche(h_ant))
    up_in = conjonction_elim_droite(conjonction_elim_gauche(h_ant))
    eq = conjonction_elim_droite(h_ant)                     # g(u)=g(up)
    #   instancier n:=up puis m:=u dans la curryfiée
    ligne = N.modus_ponens(u_in, instancie(
        N.modus_ponens(up_in, instancie(inj, vup)), vu_))
    res = N.generalisation("u", N.generalisation("up",
        N.loi_deduction(ant, N.modus_ponens(eq, ligne))))
    assert res.conclusion == E.injective_dans(vg, NN), \
        "injective_dans_iteree : forme"
    return res


def equipotence_iteree(u, x0, e, g="gcap", zname="zcl", yname="ycl"):
    """🎯 K6e : { corps_c63_fort(S_c,x0), x0∈E, u⊂E×E, dom u=E, hors, inj }
       ⊢ Eq( ℕ, g⟨ℕ⟩ )   [6 hyps — le corps FORT remplace le corps faible].

    Témoin : g lui-même.  func/dom du corps fort ; injectivité K6d convertie
    (le corps faible déchargé par coupure depuis le fort) ; surjectivité sur
    D := g⟨ℕ⟩ par réflexivité ; S5 au témoin g."""
    vu, vx0, ve, vg = _t(u), _t(x0), _t(e), _t(g)
    NN = ensemble_NN()
    _, S_c = regle_clampee(u, x0, e, zname, yname)
    D = E.image(vg, NN)

    h_fort = N.assume(corps_c63_fort(S_c, vx0, g=g))        # corps FORT [HONNÊTE]
    func = conjonction_elim_gauche(conjonction_elim_gauche(h_fort))
    dom = conjonction_elim_droite(conjonction_elim_gauche(h_fort))
    corps_faible = conjonction_elim_droite(h_fort)          # corps_c63
    inj_dans = _cut(corps_faible, corps_c63(S_c, vx0, g=g),
                    injective_dans_iteree(u, x0, e, g, zname, yname))
    surj = N.reflexivite(D)                                 # g⟨ℕ⟩ = g⟨ℕ⟩ (gratuit)
    bij = conjonction_intro(inj_dans, surj)                 # est_bijective(g,ℕ,D)
    bijde = conjonction_intro(conjonction_intro(func, dom), bij)
    assert bijde.conclusion == est_bijection_de(vg, NN, D), \
        "equipotence_iteree : bijection_de mal formée"
    res = N.modus_ponens(bijde,
        N.s5(est_bijection_de(var("F"), NN, D), vg, "F"))   # (∃F)…
    assert res.conclusion == equipotent(NN, D), "equipotence_iteree : forme"
    assert len(res.hypotheses) == 6, "equipotence_iteree : hyps ≠ 6"
    return res


__all__ = ["injective_dans_iteree", "equipotence_iteree"]
