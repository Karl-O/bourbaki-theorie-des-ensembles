"""§III.2 — LEMME 4 généralisé à un SOUS-DOMAINE.

    { est_bien_ordonne(R,E),  inclus(S,E),  (∀t)(t∈S ⇒ f(t)∈S),
      f strictement croissante S→S }
        ⊢  (∀x)( x∈S ⇒ R{x, f(x)} ).

C'est la version de Lemme 4 §III.2 (Bourbaki, E.III.2.6) qui consomme le bon ordre
AMBIANT est_bien_ordonne(R,E) plus inclus(S,E), JAMAIS la formule literal bo(R,S)
(qui est FAUSSE pour un segment PROPRE S⊊E : est_reflexive_dans_ordre(R,S) est un
BICONDITIONNEL (∀x)(R{x,x}⇔x∈S) — pour x∈E∖S on aurait besoin de R{x,x}∧¬(x∈S),
impossible puisque bo(R,E) donne R{x,x}⇔x∈E).

La preuve de lemme_4 n'utilise que l'ANTISYMÉTRIE, la clause de PLUS PETIT ÉLÉMENT
et la TOTALITÉ du bon ordre — toutes vraies pour les sous-ensembles de E.  Cette
généralisation est donc directe : on remplace E par S dans le « mauvais ensemble »
A = { x∈S | f(x) <_R x } ⊆ S ⊆ E, et CHAQUE usage de « bon ordre » route par
est_bien_ordonne(R,E) + appartenance-à-E (via inclus(S,E)) :

  • plus petit de A : bon_ordre_donne_clause_plus_petit(R,E) instanciée au TERME A,
    avec A ⊆ E obtenu via A ⊆ S (A_inclus_S) et S ⊆ E (inclus(S,E)) ;
  • totalité de x,y∈S : bon_ordre_est_total(R,E) après x∈E, y∈E (de inclus(S,E)) ;
  • antisymétrie : _antisym_de_bo(bo(R,E)) (relation-level, ambiant).

A est construit par un AXIOME DÉFINITIONNEL (S8+A1) dans une THÉORIE DÉDIÉE (motif
`axiome_A`/`theorie_A` de ensembles_lemme4_croissante) ; theorie_ensembles() = 22.
f(x) est manipulé comme TERME OPAQUE (_val(f,x)=valeur(f,x,b="j")).
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, et, non, impl, appartient, pourtout, equiv, inclus,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as _ENS  # alias sûr quand le param E="E" masque E
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import tau
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    instancie, equivalence_avant, equivalence_arriere, projection_gauche,
    cas, tiers_exclu,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege import (
    a_implique_a, syllogisme,
)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import symetrie
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.ordinal_cardinal.ordinal_cardinal_correspondance.ensembles_ordinal_cardinal_bon_ordre import (
    bon_ordre_donne_clause_plus_petit,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_monotone import est_strictement_croissante
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.trichotomie_ordinaux.lemme4_segments.ensembles_bien_ordonne_total import bon_ordre_est_total
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.trichotomie_ordinaux.lemme4_segments.ensembles_segments_construction import (
    seg as _seg, membre_segment as _membre_seg,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.trichotomie_ordinaux.lemme4_segments.ensembles_lemme4_croissante import (
    _t, _R_de, _decharge, _leib, _ex_falso, _refute_self, _antisym_de_bo,
    _val, _coup, _strict,
)


# ════════════════════════════════════════════════════════════════════════════
#  Le « mauvais ensemble »  A = { x∈S | f(x) <_R x }  (axiome définitionnel S8+A1).
#  (S = sous-domaine ; A ⊆ S ⊆ E.)
# ════════════════════════════════════════════════════════════════════════════
def A_bad(R="R", S="S", f="f"):
    """Terme opaque A = { x∈S | f(x) <_R x }  (points décroissants du sous-domaine S)."""
    return E.app("A_lemme4_sd_bad", _t(R), _t(S), _t(f))


def _corps_A(R, S, f, u):
    """φ(u) := u∈S et f(u) <_R u."""
    return et(appartient(_t(u), _t(S)), _strict(_val(f, u), u, R))


def axiome_A(R="R", S="S", f="f", u="u"):
    """⊢-schéma (∀R)(∀S)(∀f)(∀u)( u∈A ⇔ (u∈S et f(u)<_R u) ).

    Axiome DÉFINITIONNEL du mauvais ensemble (S8 sélection dans S + A1 unicité)."""
    vR, vS, vf, vu = var(R), var(S), var(f), var(u)
    return pourtout(R, pourtout(S, pourtout(f, pourtout(u,
        equiv(appartient(vu, A_bad(vR, vS, vf)),
              _corps_A(vR, vS, vf, vu))))))


def theorie_A(R="R", S="S", f="f", u="u"):
    """Théorie dédiée ne contenant que l'axiome de A (motif axiome_D ; NON ajouté à
    theorie_ensembles, qui reste = 22)."""
    return N.Theorie("A-lemme4-sd-mauvais-ensemble", [axiome_A(R, S, f, u)])


def A_membre(R="R", S="S", f="f", u="u"):
    """⊢ ( u∈A ) ⇔ ( u∈S et f(u) <_R u ).   (axiome instancié aux TERMES.)"""
    ax = N.axiome(theorie_A(), axiome_A())
    return instancie(instancie(instancie(instancie(ax, _t(R)), _t(S)), _t(f)), _t(u))


def A_inclus_S(R="R", S="S", f="f", z="z"):
    """⊢ A ⊂ S.   (φ(z) ⇒ z∈S par projection gauche.)"""
    vz = var(z)
    eq = A_membre(R, S, f, vz)                            # z∈A ⇔ (z∈S et f(z)<z)
    z_imp = syllogisme(equivalence_avant(eq),
                       projection_gauche(appartient(vz, _t(S)),
                                         _strict(_val(f, vz), vz, R)))
    return N.generalisation(z, z_imp)                    # (∀z)(z∈A ⇒ z∈S) = A⊂S


def A_inclus_E(R="R", S="S", E_set="E", f="f", z="z"):
    """⊢ { inclus(S,E) } ⊢ A ⊂ E.   (z∈A ⇒ z∈S (A_inclus_S) ⇒ z∈E (inclus(S,E)).)"""
    vS, vE, vz = _t(S), _t(E_set), var(z)
    a_inc_s = A_inclus_S(R, S, f, z)                     # (∀z)(z∈A ⇒ z∈S)
    z_in_A_imp_S = instancie(a_inc_s, vz)                # z∈A ⇒ z∈S
    Hsincl = N.assume(inclus(vS, vE))                    # S⊂E = (∀z)(z∈S ⇒ z∈E)
    z_in_S_imp_E = instancie(Hsincl, vz)                 # z∈S ⇒ z∈E
    z_imp = syllogisme(z_in_A_imp_S, z_in_S_imp_E)       # z∈A ⇒ z∈E
    return N.generalisation(z, z_imp)                    # A⊂E  [inclus(S,E)]


# ════════════════════════════════════════════════════════════════════════════
#  STAGE 2 — le mauvais ensemble est VIDE :
#     {bo(R,E), inclus(S,E), f:S→S, f strict crois. S→S} ⊢ A=∅.
# ════════════════════════════════════════════════════════════════════════════
def _f_dans_S(f, S_set, t="t"):
    """(∀t)(t∈S ⇒ f(t)∈S)."""
    vS = _t(S_set)
    return pourtout(t, impl(appartient(var(t), vS), appartient(_val(f, var(t)), vS)))


def A_vide(R="R", E_set="E", S="S", f="f"):
    """⊢ { est_bien_ordonne(R,E), inclus(S,E), (∀t)(t∈S⇒f(t)∈S), f strict crois. S→S }
            ⊢ A = ∅.

    Cœur par minimalité (identique à lemme_4 originel, mais le mauvais ensemble vit
    dans S ⊆ E) : si A≠∅, m=min(A) — extrait via la clause de PLUS PETIT ÉLÉMENT du
    bon ordre AMBIANT (R,E) appliquée à A ⊆ E — donne f(m)<m, donc f(f(m))<f(m)
    (f strict croissante sur S, et m∈S, f(m)∈S), donc f(m)∈A ; mais m=min(A) force
    R{m,f(m)}, et l'antisymétrie AMBIANTE avec R{f(m),m} donne m=f(m), contredisant
    f(m)≠m."""
    vR, vE, vS, vf = var(R), _t(E_set), _t(S), _t(f)
    Rf = _R_de(R)
    A = A_bad(vR, vS, vf)
    Hfdans = N.assume(_f_dans_S(vf, vS))
    Hscr = N.assume(est_strictement_croissante(vR, vR, vf, vS, vS))  # f strict crois. S→S

    # plus petit élément de A — via la clause CANONIQUE du bon ordre AMBIANT (R,E),
    # instanciée au TERME A.  A ⊆ E (via A⊆S et inclus(S,E)), JAMAIS bo(R,S).
    Ane = non(egal(A, E.VIDE))
    bo = E.est_bien_ordonne(Rf, vE)                            # est_bien_ordonne(R,E) AMBIANT
    clause = N.modus_ponens(N.assume(bo), bon_ordre_donne_clause_plus_petit(Rf, E_set))
    inst = instancie(clause, A)                                # (A⊂E et A≠∅) ⇒ ∃a(...)
    prem = conjonction_intro(A_inclus_E(R, S, E_set, f), N.assume(Ane))
    pp = N.modus_ponens(prem, inst)                            # {bo, inclus(S,E), A≠∅} ⊢ ∃a(...)

    # témoin m = min(A)
    va = var("a")
    corps = et(appartient(va, A),
               pourtout("w", impl(appartient(var("w"), A), Rf(va, var("w")))))
    m = tau("a", corps)
    temoin = N.modus_ponens(pp, N.existe_temoin(corps, "a"))    # corps[a:=m]
    m_in_A = conjonction_elim_gauche(temoin)
    forall_w = conjonction_elim_droite(temoin)
    # m∈A ⇒ m∈S et f(m)<m
    mbody = N.modus_ponens(m_in_A, equivalence_avant(A_membre(vR, vS, vf, m)))
    m_in_S = conjonction_elim_gauche(mbody)
    fm_lt_m = conjonction_elim_droite(mbody)                    # _strict(f(m),m,R)
    coup_fm_m = conjonction_elim_gauche(fm_lt_m)                # (f(m),m)∈R
    fm_ne_m = conjonction_elim_droite(fm_lt_m)                  # f(m)≠m
    fm = _val(vf, m)
    fm_in_S = N.modus_ponens(m_in_S, instancie(Hfdans, m))      # f(m)∈S
    # f strict croissante en (f(m), m) : f(f(m)) < f(m)  (les deux dans S)
    prem2 = conjonction_intro(conjonction_intro(fm_in_S, m_in_S), fm_lt_m)
    scr_inst = instancie(instancie(Hscr, fm), m)
    ffm_lt_fm = N.modus_ponens(prem2, scr_inst)                 # _strict(f(f(m)),f(m),R)
    # donc f(m) ∈ A
    fm_in_A = N.modus_ponens(conjonction_intro(fm_in_S, ffm_lt_fm),
                             equivalence_arriere(A_membre(vR, vS, vf, fm)))
    # m=min(A) ⇒ R{m,f(m)}
    Rm_fm = N.modus_ponens(fm_in_A, instancie(forall_w, fm))    # (m,f(m))∈R
    # antisymétrie AMBIANTE : R{m,f(m)} et R{f(m),m} ⇒ m=f(m)
    anti = _antisym_de_bo(bo)
    anti_inst = instancie(instancie(anti, m), fm)
    m_eq_fm = N.modus_ponens(conjonction_intro(Rm_fm, coup_fm_m), anti_inst)  # m=f(m)
    fm_eq_m = N.modus_ponens(m_eq_fm, symetrie(m, fm))          # f(m)=m
    # contradiction avec f(m)≠m → A=∅
    A_eq_vide = _ex_falso(fm_eq_m, fm_ne_m, egal(A, E.VIDE))    # A=∅  [bo,incl,A≠∅,fdans,scr]
    imp = N.loi_deduction(Ane, A_eq_vide)                       # (A≠∅) ⇒ (A=∅)  [bo,incl,fdans,scr]
    te = tiers_exclu(egal(A, E.VIDE))                          # (A=∅) ou (A≠∅)
    return cas(te, a_implique_a(egal(A, E.VIDE)), imp)          # A=∅  [bo,incl,fdans,scr]


# ════════════════════════════════════════════════════════════════════════════
#  STAGE 3 — LEMME 4 (sous-domaine) :  x∈S ⇒ R{x, f(x)}.
# ════════════════════════════════════════════════════════════════════════════
# @livre Ch.III §2.5 Lem.4 | E III.22 L.5-7 | PDF p.125
def lemme_4_sous_domaine(R="R", E="E", S="S", f="f", x="x"):
    """⊢ { est_bien_ordonne(R,E), inclus(S,E), (∀t)(t∈S⇒f(t)∈S), f strict crois. S→S }
            ⊢ (∀x)( x∈S ⇒ R{x, f(x)} ).

    De A=∅ (A_vide) : x∈S impose, par TOTALITÉ du bon ordre AMBIANT (x,f(x)∈S⊆E),
    R{x,f(x)} ou R{f(x),x} ; le 2ᵉ cas force f(x)=x (sinon x∈A=∅), d'où R{x,f(x)}."""
    E_set = E
    vR, vE, vS, vf = var(R), _t(E_set), _t(S), _t(f)
    Rf = _R_de(R)
    A = A_bad(vR, vS, vf)
    vx = var(x)
    fx = _val(vf, vx)

    A_eq_vide = A_vide(R, E_set, S, f)                        # {bo,incl,fdans,scr} ⊢ A=∅
    Hfdans = N.assume(_f_dans_S(vf, vS))
    Hsincl = N.assume(inclus(vS, vE))                          # S⊂E
    Hx = N.assume(appartient(vx, vS))                          # x∈S

    # ¬( f(x) <_R x )   (sinon x∈A=∅ ⇒ x∈∅, absurde)
    Hlt = N.assume(_strict(fx, vx, vR))                        # f(x)<x
    x_in_A = N.modus_ponens(conjonction_intro(Hx, Hlt),
                            equivalence_arriere(A_membre(vR, vS, vf, vx)))  # x∈A
    x_in_vide = _leib(A, _ENS.VIDE, A_eq_vide, lambda w: appartient(vx, w), x_in_A)  # x∈∅
    notx = instancie(N.axiome(_ENS.theorie_ensembles(), _ENS.AXIOME_VIDE), vx)  # ¬(x∈∅)
    notlt = _refute_self(N.loi_deduction(_strict(fx, vx, vR),
                                         _ex_falso(x_in_vide, notx, non(_strict(fx, vx, vR)))))
    #   notlt : ¬(f(x)<x)   [bo,incl,fdans,scr,x∈S]

    # totalité du bon ordre AMBIANT : R{x,f(x)} ou R{f(x),x}, où x,f(x)∈E (via S⊆E)
    tot = bon_ordre_est_total(R, E_set)                        # {bo} ⊢ ∀x∀y((x∈E et y∈E)⇒…)
    fx_in_S = N.modus_ponens(Hx, instancie(Hfdans, vx))        # f(x)∈S
    x_in_E = N.modus_ponens(Hx, instancie(Hsincl, vx))         # x∈E   (via S⊆E)
    fx_in_E = N.modus_ponens(fx_in_S, instancie(Hsincl, fx))   # f(x)∈E (via S⊆E)
    disj = N.modus_ponens(conjonction_intro(x_in_E, fx_in_E),
                          instancie(instancie(tot, vx), fx))   # R{x,f(x)} ou R{f(x),x}

    but = Rf(vx, fx)                                           # R{x,f(x)}
    # cas A : R{x,f(x)} ⇒ but
    brA = a_implique_a(but)
    # cas B : R{f(x),x} ⇒ but   (force f(x)=x puis transporte)
    HRfx = N.assume(Rf(fx, vx))                               # R{f(x),x}
    #   f(x)=x : ¬(f(x)≠x) car (R{f(x),x} et f(x)≠x)=f(x)<x contredit notlt
    Hne = N.assume(non(egal(fx, vx)))
    lt_again = conjonction_intro(HRfx, Hne)                    # f(x)<x
    fx_eq_x_0 = _ex_falso(lt_again, notlt, egal(fx, vx))       # f(x)=x  [Hne,…]
    imp_ne = N.loi_deduction(non(egal(fx, vx)), fx_eq_x_0)     # (f(x)≠x) ⇒ f(x)=x
    te2 = tiers_exclu(egal(fx, vx))                           # (f(x)=x) ou (f(x)≠x)
    fx_eq_x = cas(te2, a_implique_a(egal(fx, vx)), imp_ne)     # f(x)=x
    #   R{x,f(x)} depuis R{f(x),x} et f(x)=x
    Rxx = _leib(fx, vx, fx_eq_x, lambda w: Rf(w, vx), HRfx)    # R{x,x}
    x_eq_fx = N.modus_ponens(fx_eq_x, symetrie(fx, vx))       # x=f(x)
    Rxfx = _leib(vx, fx, x_eq_fx, lambda w: Rf(vx, w), Rxx)    # R{x,f(x)}
    brB = N.loi_deduction(Rf(fx, vx), Rxfx)                    # R{f(x),x} ⇒ R{x,f(x)}

    res = cas(disj, brA, brB)                                  # R{x,f(x)}  [bo,incl,fdans,scr,x∈S,…]
    body = N.loi_deduction(appartient(vx, vS), res)           # x∈S ⇒ R{x,f(x)}
    return N.generalisation(x, body)                          # (∀x)(x∈S ⇒ R{x,f(x)})


def lemme_4_sous_domaine_cible(R="R", E="E", S="S", f="f", x="x"):
    """ÉNONCÉ-cible (test miroir) de la conclusion de lemme_4_sous_domaine."""
    Rf = _R_de(R)
    vS, vx = var(S), var(x)
    return pourtout(x, impl(appartient(vx, vS), Rf(vx, _val(f, vx))))


# ════════════════════════════════════════════════════════════════════════════
#  COROLLAIRE 1 (sous-domaine) — aucune application strictement croissante de S
#  DANS S n'envoie S dans un SEGMENT PROPRE ]←,a[ de S  (extrémité a∈S).
# ════════════════════════════════════════════════════════════════════════════
def cor1_sous_domaine(R="R", E="E", S="S", a="a", g="g", t="t"):
    """⊢ { est_bien_ordonne(R,E), inclus(S,E), a∈S, (∀t)(t∈S⇒g(t)∈S),
           g strict crois. S→S }
            ⊢ ¬ (∀t)( t∈S ⇒ g(t) ∈ seg(R,S,a) ).

    🎯 COR 1 §III.2 (sous-domaine) : g (strict. croissante S→S) ne peut envoyer S dans
    le segment PROPRE ]←,a[ de S.  Sinon g(a)∈]←,a[ donne g(a) <_R a, mais
    lemme_4_sous_domaine donne a ≤_R g(a), et l'antisymétrie AMBIANTE force a=g(a),
    contredisant g(a)≠a.  (Le bon ordre consommé est bo(R,E), JAMAIS bo(R,S).)"""
    E_set = E
    vR, vE, vS, vg, va = var(R), var(E_set), var(S), var(g), var(a)
    Rf = _R_de(R)
    Sa = _seg(R, S, va)                                        # ]←,a[ = {u∈S | R{u,a} et u≠a}
    vt = var(t)
    Hmap_f = pourtout(t, impl(appartient(vt, vS), appartient(_val(vg, vt), Sa)))
    Hmap = N.assume(Hmap_f)
    Ha = N.assume(appartient(va, vS))                          # a∈S
    Hfdans = N.assume(_f_dans_S(vg, vS))                       # (∀t)(t∈S ⇒ g(t)∈S)

    # lemme_4_sous_domaine (f:=g) : a∈S ⇒ R{a,g(a)}
    l4 = lemme_4_sous_domaine(R, E_set, S, g)
    l4 = _decharge(l4, _f_dans_S(vg, vS), Hfdans)              # garder fdans en hypothèse
    ga = _val(vg, va)
    Rag = N.modus_ponens(Ha, instancie(l4, va))                # R{a, g(a)}

    # g(a)∈]←,a[ ⇒ R{g(a),a} et g(a)≠a   (ground set S de seg)
    ga_in_Sa = N.modus_ponens(Ha, instancie(Hmap, va))
    ga_unpack = N.modus_ponens(ga_in_Sa,
                               equivalence_avant(_membre_seg(R, S, va, ga)))
    Rga = conjonction_elim_droite(conjonction_elim_gauche(ga_unpack))       # R{g(a),a}
    ga_ne_a = conjonction_elim_droite(ga_unpack)                            # g(a)≠a

    # antisymétrie AMBIANTE : a=g(a) ; contradiction avec g(a)≠a
    anti = _antisym_de_bo(_ENS.est_bien_ordonne(Rf, vE))
    anti_inst = instancie(instancie(anti, va), ga)
    a_eq_ga = N.modus_ponens(conjonction_intro(Rag, Rga), anti_inst)        # a=g(a)
    ga_eq_a = N.modus_ponens(a_eq_ga, symetrie(va, ga))                     # g(a)=a
    contra = _ex_falso(ga_eq_a, ga_ne_a, non(Hmap_f))                       # ¬Hmap  [Hmap,…]
    return _refute_self(N.loi_deduction(Hmap_f, contra))                    # ¬Hmap  [bo,incl,a∈S,fdans,scr]


def cor1_sous_domaine_cible(R="R", E="E", S="S", a="a", g="g", t="t"):
    """ÉNONCÉ-cible (test miroir) de cor1_sous_domaine."""
    vS, vt, va = var(S), var(t), var(a)
    Sa = _seg(R, S, va)
    return non(pourtout(t, impl(appartient(vt, vS), appartient(_val(g, vt), Sa))))


__all__ = [
    "A_bad", "axiome_A", "theorie_A", "A_membre", "A_inclus_S", "A_inclus_E",
    "A_vide", "lemme_4_sous_domaine", "lemme_4_sous_domaine_cible",
    "cor1_sous_domaine", "cor1_sous_domaine_cible",
]
