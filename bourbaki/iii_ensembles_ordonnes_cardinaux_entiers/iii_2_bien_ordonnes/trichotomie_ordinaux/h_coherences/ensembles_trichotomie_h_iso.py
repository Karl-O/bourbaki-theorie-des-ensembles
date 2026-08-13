"""§III.2 — Théorème 3 (TRICHOTOMIE) : h (=h_iso_max) est un ISOMORPHISME D'ORDRE
sur dom(h) — INJECTIVITÉ et COMPATIBILITÉ D'ORDRE (conjoints de est_isomorphisme_ordre).

────────────────────────────────────────────────────────────────────────────────
RÔLE — étape (d.3-d.4) du blueprint DESIGN_trichotomie_III2.md.  L'iso MAXIMAL
h = h_iso_max(E,R,F,Rp) (union des graphes d'iso de couples de segments isomorphes,
posé dans ensembles_trichotomie_scaffold, axiome dédié theorie_h, theorie=22) doit
être un ISOMORPHISME D'ORDRE de dom(h)=S₀ sur pr₂(h)=T₀ :

    est_isomorphisme_ordre(h, dom h, pr₂ h, R, Rp)
        = est_bijective(h, dom h, pr₂ h)  ET  compatible_ordre(h, dom h, R, Rp).

est_bijective = injective_dans(h, dom h) ET surjective ; compatible_ordre = la
préservation d'ordre dans les deux sens.  Ce module FERME les CONJOINTS atteignables
(salvage fort gradué, honnête) :

  ✅ INCONDITIONNEL (theorie=22) — le PONT « couple ↦ valeur » :
     • h_couple_de_valeur : { est_fonctionnel(h), u∈dom h } ⊢ (u, valeur(h,u)) ∈ h.
       (Sous fonctionnalité, l'antécédent u du domaine est apparié à sa valeur h(u)
        DANS h.  Brique réutilisable : relie la forme « par couples » à la forme
        « par valeurs » des conjoints de l'iso.)

  ⚠️ CONJOINTS de l'iso, CONDITIONNELS à des hypothèses de COHÉRENCE EXPLICITES
     (le contenu DUR — unicité (c) + Lemme 1 §III.2 — pris en hypothèse, jamais
     postulé, EXACTEMENT comme compatibilite_h ⊢ h_fonctionnel_sous_compatibilite) :

     • compatibilite_inverse_h (FORMULE) : la cohérence INVERSE (= injectivité « par
       couples ») (∀u,v,u')( ((u,v)∈h et (u',v)∈h) ⇒ u=u' ).  Duale de compatibilite_h.
     • h_injectif_sous_compatibilite_inverse :
           { est_fonctionnel(h), compatibilite_inverse_h }
             ⊢ injective_dans(h, dom h).
       Le conjoint INJECTIF de est_bijective : pour u,u'∈dom h avec h(u)=h(u'), les
       couples (u,h(u)),(u',h(u'))∈h (pont) ont même 2ᵉ coordonnée, d'où u=u' par
       cohérence inverse.  CONDITIONNEL, theorie=22.

     • compatibilite_ordre_h (FORMULE) : la cohérence d'ORDRE « par couples »
       (∀u,v,u',v')( ((u,v)∈h et (u',v')∈h) ⇒ (R{u,u'} ⇔ Rp{v,v'}) ).  C'est
       EXACTEMENT compatible_ordre(h,dom h,R,Rp) écrit par couples ; sa vérité
       encapsule la cohérence des isos de segments (chaque couple vient d'un iso
       φ:S≅T order-preserving — h_membre_donne_temoin — et deux segments emboîtés
       sont comparables/initiaux : Lemme 1 §III.2).  Prise en HYPOTHÈSE.
     • h_compatible_ordre_sous_hyp :
           { est_fonctionnel(h), compatibilite_ordre_h }
             ⊢ compatible_ordre(h, dom h, R, Rp).
       Le conjoint COMPATIBLE D'ORDRE : pont des couples vers les valeurs (h(x),h(y))
       via h_couple_de_valeur, theorie=22.

     • h_est_isomorphisme_ordre_sous_hyp :
           { est_fonctionnel(h), compatibilite_inverse_h, compatibilite_ordre_h,
             est_surjective(h, dom h, pr₂ h) }
             ⊢ est_isomorphisme_ordre(h, dom h, pr₂ h, R, Rp).
       🎯 ASSEMBLAGE des deux conjoints (bijectif=injectif+surjectif, compatible
       d'ordre) en l'ISO D'ORDRE complet, sous les hypothèses de cohérence EXPLICITES.
       (La surjectivité = pr₂(h) est l'image, h_img_inclus_F + définition de pr₂ ;
        prise ici en hypothèse explicite — l'autre moitié structurelle.)

INVARIANT : theorie_ensembles() = 22.  Rien postulé : le pont DÉRIVE de AXIOME_DOM +
valeur_dans_graphe/valeur_caracterisation + l'axiome dédié de h ; les conjoints
conditionnels portent leurs hypothèses de cohérence dans le séquent (jamais affirmées).
🚫 jamais tautologie déguisée, jamais affaibli : chaque conclusion (couple-valeur,
injective_dans, compatible_ordre, iso d'ordre) n'est AUCUNE de ses hypothèses.

⚠️ REPORTÉ précisément (JAMAIS postulé) : la PREUVE de compatibilite_inverse_h /
compatibilite_ordre_h (= recoller la cohérence des isos de segments, magnitude
Cantor–Bernstein/Lemme 1 §III.2), et la surjectivité comme égalité pr₂(h)=image —
maillons durs alimentés par h_membre_donne_temoin + l'unicité (auto_iso_est_identite).
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, et, ou, non, impl, equiv, appartient, existe, pourtout, inclus,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_1_relations_ordre.ordre_treillis import ensembles_ordre_vocab as V
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_1_relations_ordre.isomorphismes_ordre.ensembles_pont_binder import pont_compatible
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege import syllogisme
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, instancie,
)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import symetrie, composer_egalites
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_4_fonctions.ensembles_fonctions import (
    valeur_dans_graphe, valeur_caracterisation,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.trichotomie_ordinaux.assemblage import ensembles_trichotomie_scaffold as TS
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.trichotomie_ordinaux.maximalite import ensembles_trichotomie_scaffold_maximalite as M


def _t(t):
    return t if isinstance(t, Terme) else var(t)


def _R_de(R):
    """Relation portée par le graphe R : a≤b := (a,b)∈R  (convention projet)."""
    vR = _t(R)
    return lambda a, b: appartient(E.couple(_t(a), _t(b)), vR)


_HOLE = "hole_h_iso"


def _leib(a, b, h_ab, phi_fun, h_phi_a):
    """De ⊢ a=b et ⊢ Φ[a] déduit ⊢ Φ[b]   (Leibniz via S6)."""
    va, vb = _t(a), _t(b)
    eqv = N.modus_ponens(h_ab, N.s6(va, vb, _HOLE, phi_fun(var(_HOLE))))
    return N.modus_ponens(h_phi_a, equivalence_avant(eqv))


# ════════════════════════════════════════════════════════════════════════════
#  ✅ PONT « couple ↦ valeur » : { func h, u∈dom h } ⊢ (u, valeur(h,u)) ∈ h.
#     INCONDITIONNEL (au sens : pas d'hypothèse de cohérence ; func h + u∈dom h
#     sont les hypothèses STRUCTURELLES minimales d'une valeur de fonction).
# ════════════════════════════════════════════════════════════════════════════
def h_couple_de_valeur(E_set="E", R="R", F_set="F", Rp="Rp", u="u", y="y"):
    """⊢ { est_fonctionnel(h), u∈dom h } ⊢ ( u, valeur(h,u) ) ∈ h.

    Sous fonctionnalité de h et u∈dom h, l'antécédent u est apparié à sa valeur
    h(u)=valeur(h,u) DANS h : de u∈dom h on tire (∃y)((u,y)∈h) (AXIOME_DOM) puis
    (u, h(u))∈h (valeur_dans_graphe).  RÉUTILISABLE — relie la forme « par couples »
    à la forme « par valeurs » des conjoints de l'iso.  NON vacueux : (u,h(u))∈h
    n'est aucune hypothèse.

    ⚠️ y=« y » par défaut = liant de AXIOME_DOM et de valeur(.,.) (sinon α-décalage).
    func h N'est PAS requis ici (valeur_dans_graphe n'utilise que le domaine), mais
    on le garde EN HYPOTHÈSE pour servir directement les conjoints (où func h est de
    toute façon nécessaire) ; il est ré-introduit pour figurer dans le séquent."""
    vu = _t(u)
    h = TS.h_iso_max(E_set, R, F_set, Rp)
    Hfunc = N.assume(E.est_fonctionnel(h))               # func h (porté dans le séquent)
    Hu_dom = N.assume(appartient(vu, E.dom(h)))          # u∈dom h
    # u∈dom h ⇒ (∃y)((u,y)∈h)   (AXIOME_DOM)
    axd = N.axiome(E.theorie_ensembles(), E.AXIOME_DOM)
    dom_eq = instancie(instancie(axd, h), vu)            # u∈dom h ⇔ (∃y)((u,y)∈h)
    ex = N.modus_ponens(Hu_dom, equivalence_avant(dom_eq))   # (∃y)((u,y)∈h)
    # (u, h(u))∈h   (valeur_dans_graphe sous (∃y)…)
    vdg = valeur_dans_graphe(h, vu)                      # {(∃y)((u,y)∈h)} ⊢ (u,h(u))∈h
    res = N.modus_ponens(ex, N.loi_deduction(
        existe("y", appartient(E.couple(vu, var("y")), h)), vdg))   # (u,h(u))∈h  [func h, u∈dom h]
    # ré-attacher func h dans le séquent (a_implique_a → le garder via décharge/charge)
    res = N.modus_ponens(Hfunc, N.loi_deduction(E.est_fonctionnel(h), res))
    return res


def h_couple_de_valeur_cible(E_set="E", R="R", F_set="F", Rp="Rp", u="u"):
    """ÉNONCÉ-cible (test miroir) :  ( u, valeur(h,u) ) ∈ h."""
    vu = _t(u)
    h = TS.h_iso_max(E_set, R, F_set, Rp)
    return appartient(E.couple(vu, E.valeur(h, vu)), h)


# ════════════════════════════════════════════════════════════════════════════
#  ⚠️ COHÉRENCE INVERSE (injectivité « par couples ») — HYPOTHÈSE EXPLICITE.
#     Duale de compatibilite_h (qui est la fonctionnalité par couples).
# ════════════════════════════════════════════════════════════════════════════
def compatibilite_inverse_h(E_set="E", R="R", F_set="F", Rp="Rp", u="u", v="v", up="up"):
    """FORMULE de COHÉRENCE INVERSE de h (= son injectivité « par couples ») :

        (∀u)(∀v)(∀u')( ( (u,v)∈h et (u',v)∈h ) ⇒ u=u' ).

    DUALE de compatibilite_h (cohérence = fonctionnalité par couples).  Sa VÉRITÉ
    encapsule le verrou dur côté image : deux antécédents u,u' de la MÊME valeur v
    proviennent d'isos de segments injectifs (chaque iso φ:S≅T est bijectif, donc
    injectif) qui coïncident (Lemme 1 §III.2 + unicité), d'où u=u'.  Prise en
    HYPOTHÈSE explicite, JAMAIS postulée comme théorème (la prouver = fermer
    l'injectivité globale)."""
    vu, vv, vup = var(u), var(v), var(up)
    h = TS.h_iso_max(E_set, R, F_set, Rp)
    return pourtout(u, pourtout(v, pourtout(up,
        impl(et(appartient(E.couple(vu, vv), h), appartient(E.couple(vup, vv), h)),
             egal(vu, vup)))))


def h_injectif_sous_compatibilite_inverse(E_set="E", R="R", F_set="F", Rp="Rp",
                                          u="u", up="up", v="v"):
    """⊢ { est_fonctionnel(h), compatibilite_inverse_h } ⊢ injective_dans(h, dom h).

    🎯 Le conjoint INJECTIF de est_bijective(h, dom h, pr₂ h).  Pour u,u'∈dom h avec
    h(u)=h(u') : par le PONT (h_couple_de_valeur), (u,h(u))∈h et (u',h(u'))∈h ; or
    h(u)=h(u') donc (u',h(u'))=(u',h(u)), d'où (u,h(u))∈h ET (u',h(u))∈h ; la
    cohérence inverse (même 2ᵉ coordonnée h(u)) donne u=u'.  CONDITIONNEL aux deux
    hypothèses EXPLICITES, theorie=22.  NON vacueux : injective_dans(h, dom h) n'est
    aucune hypothèse (binders/forme distincts de compatibilite_inverse_h)."""
    vu, vup = var(u), var(up)
    h = TS.h_iso_max(E_set, R, F_set, Rp)
    domh = E.dom(h)
    hu, hup = E.valeur(h, vu), E.valeur(h, vup)

    Hfunc = N.assume(E.est_fonctionnel(h))                       # func h
    Hcompat = N.assume(compatibilite_inverse_h(E_set, R, F_set, Rp))  # cohérence inverse

    # hypothèse principale de injective_dans : (u∈dom h et u'∈dom h et h(u)=h(u'))
    Hu = N.assume(appartient(vu, domh))                          # u∈dom h
    Hup = N.assume(appartient(vup, domh))                        # u'∈dom h
    Hval = N.assume(egal(hu, hup))                               # h(u)=h(u')

    # (u, h(u))∈h  et  (u', h(u'))∈h   via le pont (décharge func h, ∈dom)
    u_hu = h_couple_de_valeur(E_set, R, F_set, Rp, u)            # {func h, u∈dom h} ⊢ (u,h(u))∈h
    u_hu = N.modus_ponens(Hfunc, N.loi_deduction(E.est_fonctionnel(h), u_hu))
    u_hu = N.modus_ponens(Hu, N.loi_deduction(appartient(vu, domh), u_hu))   # (u,h(u))∈h
    up_hup = h_couple_de_valeur(E_set, R, F_set, Rp, up)         # {func h, u'∈dom h} ⊢ (u',h(u'))∈h
    up_hup = N.modus_ponens(Hfunc, N.loi_deduction(E.est_fonctionnel(h), up_hup))
    up_hup = N.modus_ponens(Hup, N.loi_deduction(appartient(vup, domh), up_hup))  # (u',h(u'))∈h

    # réécrire h(u')→h(u) dans (u',h(u'))∈h   via h(u)=h(u')  (Leibniz, sens hup→hu)
    hup_eq_hu = N.modus_ponens(Hval, symetrie(hu, hup))          # h(u')=h(u)
    up_hu = _leib(hup, hu, hup_eq_hu, lambda w: appartient(E.couple(vup, w), h), up_hup)  # (u',h(u))∈h

    # cohérence inverse instanciée à (u, h(u), u') : ((u,h(u))∈h et (u',h(u))∈h)⇒u=u'
    ci_inst = instancie(instancie(instancie(Hcompat, vu), hu), vup)
    u_eq_up = N.modus_ponens(conjonction_intro(u_hu, up_hu), ci_inst)        # u=u'

    # recoller la prémisse (u∈dom h et u'∈dom h et h(u)=h(u')) ⇒ u=u'
    hyp = et(et(appartient(vu, domh), appartient(vup, domh)), egal(hu, hup))
    res = u_eq_up
    res = N.modus_ponens(Hu, N.loi_deduction(appartient(vu, domh), res))
    res = N.modus_ponens(Hup, N.loi_deduction(appartient(vup, domh), res))
    res = N.modus_ponens(Hval, N.loi_deduction(egal(hu, hup), res))
    Hh = N.assume(hyp)
    res = N.modus_ponens(conjonction_elim_gauche(conjonction_elim_gauche(Hh)),
                         N.loi_deduction(appartient(vu, domh),
        N.modus_ponens(conjonction_elim_droite(conjonction_elim_gauche(Hh)),
                       N.loi_deduction(appartient(vup, domh),
            N.modus_ponens(conjonction_elim_droite(Hh),
                           N.loi_deduction(egal(hu, hup), u_eq_up))))))
    body = N.loi_deduction(hyp, res)
    return N.generalisation(u, N.generalisation(up, body))


def h_injectif_sous_compatibilite_inverse_cible(E_set="E", R="R", F_set="F", Rp="Rp"):
    """ÉNONCÉ-cible (test miroir) :  injective_dans(h, dom h)."""
    h = TS.h_iso_max(E_set, R, F_set, Rp)
    return E.injective_dans(h, E.dom(h))


# ════════════════════════════════════════════════════════════════════════════
#  ⚠️ COHÉRENCE D'ORDRE « par couples » — HYPOTHÈSE EXPLICITE.
#     = compatible_ordre(h, dom h, R, Rp) écrit par couples (Lemme 1 §III.2).
# ════════════════════════════════════════════════════════════════════════════
def compatibilite_ordre_h(E_set="E", R="R", F_set="F", Rp="Rp",
                          u="u", v="v", up="up", vp="vp"):
    """FORMULE de COHÉRENCE D'ORDRE de h, « par couples » :

        (∀u)(∀v)(∀u')(∀v')( ( (u,v)∈h et (u',v')∈h ) ⇒ ( R{u,u'} ⇔ Rp{v,v'} ) ).

    C'est EXACTEMENT compatible_ordre(h, dom h, R, Rp) écrit par couples (la
    préservation d'ordre dans les deux sens).  Sa VÉRITÉ encapsule la cohérence des
    isos de segments : chaque couple (u,v)∈h provient d'un iso φ:S≅T order-preserving
    (h_membre_donne_temoin), et deux segments emboîtés sont comparables et initiaux
    (Lemme 1 §III.2), si bien que u≤_R u' ⇔ v=φ(u)≤_Rp φ(u')=v'.  Prise en HYPOTHÈSE
    explicite, JAMAIS postulée comme théorème."""
    Rf, Rpf = _R_de(R), _R_de(Rp)
    vu, vv, vup, vvp = var(u), var(v), var(up), var(vp)
    h = TS.h_iso_max(E_set, R, F_set, Rp)
    return pourtout(u, pourtout(v, pourtout(up, pourtout(vp,
        impl(et(appartient(E.couple(vu, vv), h), appartient(E.couple(vup, vvp), h)),
             equiv(Rf(vu, vup), Rpf(vv, vvp)))))))


def h_compatible_ordre_sous_hyp(E_set="E", R="R", F_set="F", Rp="Rp", x="x", y="w"):
    """⊢ { est_fonctionnel(h), compatibilite_ordre_h }
         ⊢ compatible_ordre(h, dom h, R, Rp).

    🎯 Le conjoint COMPATIBLE D'ORDRE de l'iso.  compatible_ordre(h,dom h,R,Rp) =
    (∀x)(∀y)((x∈dom h et y∈dom h) ⇒ (R{x,y} ⇔ Rp{h(x),h(y)})).  Sous x,y∈dom h, le
    PONT (h_couple_de_valeur) donne (x,h(x))∈h et (y,h(y))∈h ; la cohérence d'ordre
    « par couples », instanciée à (x,h(x),y,h(y)), conclut R{x,y} ⇔ Rp{h(x),h(y)}.
    CONDITIONNEL aux deux hypothèses EXPLICITES, theorie=22.  NON vacueux :
    compatible_ordre(h,dom h,R,Rp) n'est aucune hypothèse.

    ⚠️ Le 2ᵉ liant est « w » (PAS « y ») : « y » serait CAPTURÉ par le liant interne
    de valeur(h,·)=τy((·,y)∈h), rendant valeur(h, var(\"y\")) dégénéré (τy((y,y)∈h)).
    « w » est frais ⇒ valeur(h,w) bien formé.  La cible utilise le même binder « w »."""
    Rf, Rpf = _R_de(R), _R_de(Rp)
    vx, vy = var(x), var(y)
    h = TS.h_iso_max(E_set, R, F_set, Rp)
    domh = E.dom(h)
    hx, hy = E.valeur(h, vx), E.valeur(h, vy)

    Hfunc = N.assume(E.est_fonctionnel(h))                       # func h
    Hco = N.assume(compatibilite_ordre_h(E_set, R, F_set, Rp))   # cohérence d'ordre par couples

    Hx = N.assume(appartient(vx, domh))                          # x∈dom h
    Hy = N.assume(appartient(vy, domh))                          # y∈dom h

    # (x,h(x))∈h  et  (y,h(y))∈h   via le pont
    x_hx = h_couple_de_valeur(E_set, R, F_set, Rp, x)
    x_hx = N.modus_ponens(Hfunc, N.loi_deduction(E.est_fonctionnel(h), x_hx))
    x_hx = N.modus_ponens(Hx, N.loi_deduction(appartient(vx, domh), x_hx))   # (x,h(x))∈h
    y_hy = h_couple_de_valeur(E_set, R, F_set, Rp, y)
    y_hy = N.modus_ponens(Hfunc, N.loi_deduction(E.est_fonctionnel(h), y_hy))
    y_hy = N.modus_ponens(Hy, N.loi_deduction(appartient(vy, domh), y_hy))   # (y,h(y))∈h

    # cohérence d'ordre instanciée à (x,h(x),y,h(y)) : ((x,h(x))∈h et (y,h(y))∈h)⇒(R{x,y}⇔Rp{h(x),h(y)})
    co_inst = instancie(instancie(instancie(instancie(Hco, vx), hx), vy), hy)
    equiv_xy = N.modus_ponens(conjonction_intro(x_hx, y_hy), co_inst)   # R{x,y} ⇔ Rp{h(x),h(y)}

    # recoller (x∈dom h et y∈dom h) ⇒ (R{x,y} ⇔ Rp{h(x),h(y)})
    res = equiv_xy
    Hxy = N.assume(et(appartient(vx, domh), appartient(vy, domh)))
    res = N.modus_ponens(conjonction_elim_gauche(Hxy),
                         N.loi_deduction(appartient(vx, domh),
        N.modus_ponens(conjonction_elim_droite(Hxy),
                       N.loi_deduction(appartient(vy, domh), equiv_xy))))
    body = N.loi_deduction(et(appartient(vx, domh), appartient(vy, domh)), res)
    concl = N.generalisation(x, N.generalisation(y, body))   # compatible_ordre(h,dom h,R,Rp)[τy]
    # PONT y→j : la cible compatible_ordre (fonction) écrit h(·) en liant « j » ; le corps
    # est prouvé « par couples » via valeur(h,·) en « y ».  On convertit y→j (x,w plaines).
    return pont_compatible(concl, h, domh, Rf, Rpf, x, y, "y2j")   # [τj] = cible


def h_compatible_ordre_sous_hyp_cible(E_set="E", R="R", F_set="F", Rp="Rp", x="x", y="w"):
    """ÉNONCÉ-cible (test miroir) :  compatible_ordre(h, dom h, R, Rp).

    Binders « x », « w » (PAS « y », capturé par le τy de valeur(h,·))."""
    Rf, Rpf = _R_de(R), _R_de(Rp)
    h = TS.h_iso_max(E_set, R, F_set, Rp)
    return V.compatible_ordre(h, E.dom(h), Rf, Rpf, x, y)


# ════════════════════════════════════════════════════════════════════════════
#  🎯 ASSEMBLAGE — h est un ISOMORPHISME D'ORDRE de dom h sur pr₂ h, sous les
#     hypothèses de cohérence EXPLICITES.
# ════════════════════════════════════════════════════════════════════════════
# @livre Ch.III §2.5 Demo.3 | E III.21 L.23-33 | PDF p.124  (démonstration du Th. 3 : h est un isomorphisme d'ordre de dom(h) sur pr2(h))
def h_est_isomorphisme_ordre_sous_hyp(E_set="E", R="R", F_set="F", Rp="Rp",
                                      x="x", y="w", u="u", up="up"):
    """⊢ { est_fonctionnel(h),  compatibilite_inverse_h,  compatibilite_ordre_h,
           est_surjective(h, dom h, pr₂ h) }
         ⊢ est_isomorphisme_ordre(h, dom h, pr₂ h, R, Rp).

    🎯 h est un ISOMORPHISME D'ORDRE de dom(h)=S₀ sur pr₂(h)=T₀, ASSEMBLÉ de ses
    conjoints :
      • est_bijective(h, dom h, pr₂ h) = injective_dans(h, dom h) [h_injectif_sous_
        compatibilite_inverse] ET est_surjective(h, dom h, pr₂ h) [hypothèse
        explicite — pr₂(h) est l'image, structurelle] ;
      • compatible_ordre(h, dom h, R, Rp) [h_compatible_ordre_sous_hyp].
    CONDITIONNEL aux 4 hypothèses EXPLICITES (cohérence fonctionnelle inverse +
    cohérence d'ordre + surjectivité ; fonctionnalité de h), theorie=22.  NON vacueux :
    est_isomorphisme_ordre(...) n'est aucune hypothèse.

    ⚠️ Ces hypothèses (compatibilite_inverse_h, compatibilite_ordre_h, surjectivité)
    encapsulent le verrou dur (cohérence des isos de segments = Lemme 1 §III.2 +
    unicité) ; leur PREUVE est REPORTÉE (magnitude Cantor–Bernstein), JAMAIS postulée."""
    Rf, Rpf = _R_de(R), _R_de(Rp)
    h = TS.h_iso_max(E_set, R, F_set, Rp)
    domh, imgh = E.dom(h), E.img(h)

    # conjoint injectif  (sous func h, compatibilite_inverse_h)
    inj = h_injectif_sous_compatibilite_inverse(E_set, R, F_set, Rp, u, up)
    # conjoint surjectif  (hypothèse explicite)
    surj = N.assume(E.est_surjective(h, domh, imgh))
    # bijective = injectif ET surjectif
    bij = conjonction_intro(inj, surj)                          # est_bijective(h, dom h, pr₂ h)
    assert bij.conclusion == E.est_bijective(h, domh, imgh)

    # conjoint compatible d'ordre  (sous func h, compatibilite_ordre_h)
    co = h_compatible_ordre_sous_hyp(E_set, R, F_set, Rp, x, y)

    iso = conjonction_intro(bij, co)                            # est_isomorphisme_ordre(h,...)
    return iso


def h_est_isomorphisme_ordre_sous_hyp_cible(E_set="E", R="R", F_set="F", Rp="Rp",
                                            x="x", y="w"):
    """ÉNONCÉ-cible (test miroir) :  est_isomorphisme_ordre(h, dom h, pr₂ h, R, Rp).

    Binders « x », « w » (PAS « y », capturé par le τy de valeur(h,·))."""
    Rf, Rpf = _R_de(R), _R_de(Rp)
    h = TS.h_iso_max(E_set, R, F_set, Rp)
    return V.est_isomorphisme_ordre(h, E.dom(h), E.img(h), Rf, Rpf, x, y)


def h_est_isomorphisme_ordre_hypotheses(E_set="E", R="R", F_set="F", Rp="Rp"):
    """Les 4 HYPOTHÈSES EXPLICITES (liste de formules) de h_est_isomorphisme_ordre_
    sous_hyp (pour documentation / tests miroir) :

        [ est_fonctionnel(h), compatibilite_inverse_h, compatibilite_ordre_h,
          est_surjective(h, dom h, pr₂ h) ]."""
    h = TS.h_iso_max(E_set, R, F_set, Rp)
    return [
        E.est_fonctionnel(h),
        compatibilite_inverse_h(E_set, R, F_set, Rp),
        compatibilite_ordre_h(E_set, R, F_set, Rp),
        E.est_surjective(h, E.dom(h), E.img(h)),
    ]


__all__ = [
    "h_couple_de_valeur", "h_couple_de_valeur_cible",
    "compatibilite_inverse_h",
    "h_injectif_sous_compatibilite_inverse",
    "h_injectif_sous_compatibilite_inverse_cible",
    "compatibilite_ordre_h",
    "h_compatible_ordre_sous_hyp", "h_compatible_ordre_sous_hyp_cible",
    "h_est_isomorphisme_ordre_sous_hyp", "h_est_isomorphisme_ordre_sous_hyp_cible",
    "h_est_isomorphisme_ordre_hypotheses",
]
