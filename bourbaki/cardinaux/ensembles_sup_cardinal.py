"""§III.3.2 — PROPOSITION 2 (forme ENSEMBLISTE) : tout ensemble non vide de cardinaux
MAJORÉ admet une BORNE SUPÉRIEURE (plus petit majorant cardinal).

────────────────────────────────────────────────────────────────────────────────
Bourbaki, E.III.3.2, Proposition 2 :
  « Soit (a_ι)_{ι∈I} une famille de cardinaux.  S'il existe un cardinal b tel que
    a_ι ≤ b pour tout ι, alors il existe un PLUS PETIT cardinal b₀ tel que a_ι ≤ b₀
    pour tout ι (la borne supérieure sup_ι a_ι). »

Le module déposé `ensembles_cardinaux_borne_sup` introduit la notion FAMILIALE
`est_borne_superieure_cardinaux(b, f, I)` et reporte l'EXISTENCE (Prop 2) « Th. 1,
≤ bon ordre ».  Ce théorème de bon ordre est désormais CLOS :
`ensembles_gate_onto_top.cardinaux_bien_ordonnes_close(a)` ⊢
  (∀S)( ( S ⊂ [0,a] et S ≠ ∅ ) ⇒ (∃m)( m∈S et (∀x)(x∈S ⇒ m ≤ x) ) )  [0 hyp].

On PROUVE ici l'EXISTENCE de la borne supérieure, dans sa forme ENSEMBLISTE (la
borne supérieure d'un ENSEMBLE de cardinaux ; le sup d'une famille est le sup de
son image, ensemble de cardinaux — cf. la note de raccord en fin de fichier).

────────────────────────────────────────────────────────────────────────────────
ÉNONCÉ ENSEMBLISTE — `est_borne_superieure_ensemble(s, F, a)` :
  s est un cardinal, s majore F (∀c∈F, c≤s), et s est le PLUS PETIT majorant cardinal
  (∀c)( ( c cardinal et (∀d∈F) d≤c ) ⇒ s≤c ).  [clauses VERBATIM de Prop 2.]

PREUVE (via le BON ORDRE des cardinaux ≤ a) :
  • F⊂[0,a] (F ensemble de cardinaux majoré par a), F≠∅, a cardinal.
  • U := { m∈[0,a] | (∀c)(c∈F ⇒ c≤m) } = l'ensemble des MAJORANTS de F dans [0,a]
    (collectivisé par une théorie DÉDIÉE `theorie_majorants_F` — S8+A1, comme
    l'intervalle [a,b], les parties, l'image… ; theorie_ensembles() reste à 22).
  • a∈U  (a majore F : c∈F⊂[0,a] ⇒ c≤a ; et a∈[0,a]) ⇒ U≠∅.  U⊂[0,a].
  • `cardinaux_bien_ordonnes_close(a)` appliqué à S:=U ⇒ U a un ≤-PLUS PETIT élément s.
  • s est la borne supérieure :
      1° est_cardinal(s)   (s∈U⊂[0,a] ⇒ s cardinal) ;
      2° s majore F        (clause de U) ;
      3° plus petit majorant : pour c cardinal majorant F, par COMPARABILITÉ des
         cardinaux (`comparabilite_cardinaux`, INCONDITIONNEL) c≤a OU a≤c :
           • c≤a : c∈[0,a] (c cardinal, 0≤c, c≤a) et c majore F ⇒ c∈U ⇒ s≤c (s min) ;
           • a≤c : s≤a (s∈[0,a]) et a≤c ⇒ s≤c (TRANSITIVITÉ).

INVARIANT : theorie_ensembles() = 22 (la théorie DÉDIÉE `theorie_majorants_F` est
SÉPARÉE, comme theorie_intervalle_entiers).  RIEN POSTULÉ : le bon ordre est CLOS,
la comparabilité est CLOSE (Zorn) ; l'existence de la borne supérieure est DÉRIVÉE.
HYPOTHÈSES INTENDUES (honnêtes, NON vacuux) : est_cardinal(a), F⊂[0,a].

⚠️ `F≠∅` n'est PAS requis : le majorant a∈U suffit à rendre U≠∅ (a majore F même
vide).  Si F=∅, U=[0,a] tout entier et sup(∅)=0=Card(∅) (le ≤-min de [0,a]).  Le
résultat est donc PLUS GÉNÉRAL que Prop 2 (qui suppose la famille non vide).
"""
from __future__ import annotations

from bourbaki.logique.formule import (
    Terme, var, app, egal, et, ou, non, impl, equiv, appartient, existe, pourtout,
    inclus,
)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.logique.tactiques.tactiques_abrege import a_implique_a, syllogisme
from bourbaki.logique.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite, instancie,
    equivalence_avant, equivalence_arriere, cas,
)
from bourbaki.logique.tactiques.tactiques_abrege_quantif import existe_elimination
from bourbaki.logique.tactiques.ensembles_alpha_bridge import alpha_bridge

from bourbaki.cardinaux.ensembles_cardinaux import est_cardinal, inf_egal_card
from bourbaki.cardinaux.ensembles_cardinaux_theoremes import inf_egal_reflexif
from bourbaki.cardinaux.ensembles_cardinaux_ordre import inf_egal_transitive
from bourbaki.cardinaux.ensembles_comparabilite import comparabilite_cardinaux
from bourbaki.entiers.ensembles_entiers import ZERO
from bourbaki.entiers.ensembles_entiers_theoremes import (
    membre_intervalle_entiers, intervalle_implique_cardinal,
)
from bourbaki.entiers.ensembles_N_collectivise import zero_inf_egal_cardinal
from bourbaki.cardinaux.ensembles_ordinal_cardinal_correspondance import intervalle_0a
from bourbaki.cardinaux.ensembles_gate_onto_top import cardinaux_bien_ordonnes_close


def _t(s):
    return var(s) if isinstance(s, str) else s


def _le(u, v):
    return inf_egal_card(_t(u), _t(v))


# ═══════════════════════════════════════════════════════════════════════════════
# §III.3.2 — ENSEMBLE DES MAJORANTS de F dans [0,a]  (collectivisé, théorie DÉDIÉE)
# ═══════════════════════════════════════════════════════════════════════════════
def majore_clause(F, m, c="cmaj"):
    """« m majore l'ensemble F » := (∀c)( c∈F ⇒ c ≤ m )  (E.III.3.2)."""
    vF, vm, vc = _t(F), _t(m), var(c)
    return pourtout(c, impl(appartient(vc, vF), inf_egal_card(vc, vm)))


def relation_majorant(F, a, m, c="cmaj"):
    """Relation caractéristique « m∈[0,a] et m majore F »  (le corps de l'ensemble U)."""
    vm = _t(m)
    return et(appartient(vm, intervalle_0a(a)), majore_clause(F, m, c))


def ensemble_majorants(F, a):
    """U := { m | m∈[0,a] et (∀c∈F) c≤m } — l'ensemble des MAJORANTS de F dans [0,a].

    Terme collectivisant (Remarque III.25 : « m∈[0,a] et … » est collectivisante),
    représenté par app("majorants_card", F, a) ; sa caractérisation est l'axiome
    `axiome_majorants_F` (théorie DÉDIÉE, légitime S8 + A1, comme [a,b])."""
    return app("majorants_card", _t(F), _t(a))


def axiome_majorants_F(F="Fsup", a="a", m="m", c="cmaj"):
    """⊢-schéma  (∀m)( m∈U ⇔ ( m∈[0,a] et (∀c∈F) c≤m ) )   où U=ensemble_majorants(F,a).

    Axiome caractérisant l'ensemble des majorants de F dans [0,a] (légitime S8+A1 :
    « m∈[0,a] et (∀c∈F) c≤m » est collectivisante en m, sous-ensemble de [0,a]).
    Liants externes m ; c lié à l'INTÉRIEUR (∀c), F, a externes."""
    vF, va, vm = var(F), var(a), var(m)
    return pourtout(m, equiv(appartient(vm, ensemble_majorants(vF, va)),
                             relation_majorant(vF, va, vm, c)))


def theorie_majorants_F(F="Fsup", a="a", m="m", c="cmaj"):
    """Théorie ne contenant QUE l'axiome de l'ensemble des majorants de F dans [0,a].

    SÉPARÉE de theorie_ensembles() (qui reste à 22), même schéma que
    theorie_intervalle_entiers / theorie_graphe_terme."""
    return N.Theorie("Majorants-F", [axiome_majorants_F(F, a, m, c)])


def membre_majorants(F, a, m, c="cmaj", binder="m"):
    """⊢ ( m∈U ⇔ ( m∈[0,a] et (∀c∈F) c≤m ) )   où U=ensemble_majorants(F,a).

    THÉORÈME DIRECT : instance (sur m) de l'axiome `axiome_majorants_F`.  F et a sont
    les VARIABLES LIBRES de la théorie dédiée ; on instancie le SEUL ∀ externe au terme
    demandé.  Analogue de membre_intervalle_entiers.

    ⚠️ `binder` = le NOM du liant ∀ de l'axiome (défaut 'm').  Pour obtenir la
    caractérisation à la VARIABLE z SANS renommer le liant interne « z » de 0=Card(∅)
    (qui figure dans [0,a]), on construit l'axiome avec liant = 'z' puis on instancie à
    var('z') (substitution z→z IDENTITÉ ⇒ aucun capture-évitement ⇒ [0,a] PROPRE) :
    c'est le cas binder='z', m=var('z'), nécessaire pour que `z∈[0,a]` coïncide
    STRUCTURELLEMENT avec l'antécédent `inclus(U,[0,a])` du bon ordre (liant 'z')."""
    Fn = F if isinstance(F, str) else F.nom
    an = a if isinstance(a, str) else a.nom
    ax = N.axiome(theorie_majorants_F(Fn, an, binder, c), axiome_majorants_F(Fn, an, binder, c))
    return instancie(ax, _t(m))


# ═══════════════════════════════════════════════════════════════════════════════
# §III.3.2 — BORNE SUPÉRIEURE d'un ENSEMBLE de cardinaux (notion ensembliste)
# ═══════════════════════════════════════════════════════════════════════════════
def majore_famille_ensemble(s, F, c="cmaj"):
    """« s majore l'ensemble F » := (∀c)( c∈F ⇒ c ≤ s )  (clause 2° de Prop 2)."""
    return majore_clause(F, s, c)


def plus_petit_majorant_ensemble(s, F, c="csup"):
    """« s est le PLUS PETIT majorant cardinal de F » (clause 3° de Prop 2) :
        (∀c)( ( c cardinal et (∀d∈F) d≤c ) ⇒ s≤c )."""
    vs, vc = _t(s), var(c)
    hyp = et(est_cardinal(vc), majore_clause(F, vc, "dsup"))
    return pourtout(c, impl(hyp, inf_egal_card(vs, vc)))


def est_borne_superieure_ensemble(s, F, a=None, c="cmaj", d="csup"):
    """« s = sup F » : s est la borne supérieure de l'ENSEMBLE de cardinaux F
    (E.III.3.2, Prop 2, forme ensembliste).

    Conjonction des trois clauses de Prop 2 :
      1° s est un cardinal ;
      2° s majore F      (∀c∈F, c≤s) ;
      3° s est le plus petit cardinal majorant  (s≤c pour tout majorant cardinal c).
    Le paramètre `a` est ignoré (la borne supérieure ne dépend pas du majorant a
    servant à la prouver) ; gardé pour symétrie d'appel."""
    vs = _t(s)
    return et(et(est_cardinal(vs), majore_famille_ensemble(s, F, c)),
              plus_petit_majorant_ensemble(s, F, d))


# ═══════════════════════════════════════════════════════════════════════════════
#  helpers TERME-niveau (lemmes clos généralisés puis instanciés aux termes)
# ═══════════════════════════════════════════════════════════════════════════════
def _zero_le(c_terme):
    """⊢ ( est_cardinal(c) ⇒ 0 ≤ c )   (aux TERMES ; implication universelle instanciée)."""
    # zero_inf_egal_cardinal = {est_cardinal(x)} ⊢ 0≤x ; décharger en implication AVANT généraliser.
    imp = N.loi_deduction(est_cardinal(var("xz0")), zero_inf_egal_cardinal("xz0"))  # est_cardinal(xz0)⇒0≤xz0
    g = N.generalisation("xz0", imp)
    return instancie(g, _t(c_terme))


def _refl(c_terme):
    """⊢ c ≤ c   (aux TERMES, réflexivité de ≤)."""
    g = N.generalisation("xrf", inf_egal_reflexif("xrf"))
    return instancie(g, _t(c_terme))


def _trans(u, v, w):
    """⊢ ( u≤v et v≤w ) ⇒ u≤w   (aux TERMES, transitivité de ≤)."""
    g = inf_egal_transitive()                                    # CLOS, liants X,Y,Z (défauts)
    g = N.generalisation("X", g)
    g = N.generalisation("Y", g)
    g = N.generalisation("Z", g)
    # dernier généralisé = extérieur : (∀Z)(∀Y)(∀X)…  → instancie Z, puis Y, puis X
    return instancie(instancie(instancie(g, _t(w)), _t(v)), _t(u))


def _membre_interv(a, x):
    """⊢ ( x∈[0,a] ⇔ ( x cardinal et 0≤x et x≤a ) )   (aux TERMES x, a)."""
    g = membre_intervalle_entiers("a0mi", "b0mi", "x0mi")        # liants a,b,x
    g = N.generalisation("x0mi", g)
    g = N.generalisation("b0mi", g)
    g = N.generalisation("a0mi", g)
    return instancie(instancie(instancie(g, ZERO), _t(a)), _t(x))


def _interv_implique_cardinal(a, x):
    """⊢ ( x∈[0,a] ) ⇒ ( x cardinal )   (aux TERMES)."""
    g = intervalle_implique_cardinal("a0ic", "b0ic", "x0ic")
    g = N.generalisation("x0ic", g)
    g = N.generalisation("b0ic", g)
    g = N.generalisation("a0ic", g)
    return instancie(instancie(instancie(g, ZERO), _t(a)), _t(x))


# ═══════════════════════════════════════════════════════════════════════════════
#  a ∈ U  (a majore F et a∈[0,a])  ⇒  U ≠ ∅  ;  U ⊂ [0,a]
# ═══════════════════════════════════════════════════════════════════════════════
def a_dans_majorants(F="Fsup", a="a"):
    """⊢ { est_cardinal(a),  F⊂[0,a] }  ⊢  a ∈ U   où U=ensemble_majorants(F,a).

    a majore F : tout c∈F⊂[0,a] vérifie c≤a (intervalle_implique_borne_sup).  a∈[0,a]
    car a cardinal, 0≤a, a≤a (réflexivité).  Donc a satisfait la relation de U."""
    vF, va = _t(F), _t(a)
    interv = intervalle_0a(a)

    # ── a ∈ [0,a]  (a cardinal, 0≤a, a≤a)
    H_card = N.assume(est_cardinal(va))
    zero_le_a = N.modus_ponens(H_card, _zero_le(va))             # 0 ≤ a
    a_le_a = _refl(va)                                           # a ≤ a
    corps_a = conjonction_intro(conjonction_intro(H_card, zero_le_a), a_le_a)  # a card et 0≤a et a≤a
    a_in_interv = N.modus_ponens(corps_a, equivalence_arriere(_membre_interv(va, va)))  # a∈[0,a]

    # ── a majore F : (∀c)( c∈F ⇒ c≤a )
    vc = var("cmaj")
    H_sub = N.assume(inclus(vF, interv))                        # F ⊂ [0,a]
    Hc = N.assume(appartient(vc, vF))                           # c∈F
    c_in_interv = N.modus_ponens(Hc, instancie(H_sub, vc))      # c∈[0,a]
    # c∈[0,a] ⇒ c≤a (3ᵉ conjoint du corps)
    c_corps = N.modus_ponens(c_in_interv, equivalence_avant(_membre_interv(va, vc)))
    c_le_a = conjonction_elim_droite(c_corps)                   # c ≤ a
    body_c = N.loi_deduction(appartient(vc, vF), c_le_a)        # c∈F ⇒ c≤a
    a_majore = N.generalisation("cmaj", body_c)                 # (∀c)(c∈F ⇒ c≤a)

    # ── a ∈ U  via membre_majorants
    rel_a = conjonction_intro(a_in_interv, a_majore)            # a∈[0,a] et a majore F
    assert rel_a.conclusion == relation_majorant(vF, va, va, "cmaj"), \
        "relation_majorant(a) mal formée"
    a_in_U = N.modus_ponens(rel_a, equivalence_arriere(membre_majorants(vF, va, va)))
    return a_in_U


def majorants_non_vide(F="Fsup", a="a"):
    """⊢ { est_cardinal(a),  F⊂[0,a] }  ⊢  ¬( U = ∅ )   où U=ensemble_majorants(F,a).

    a∈U (a_dans_majorants) ⇒ (∃z) z∈U ⇒ U≠∅ (non_vide_ssi_element)."""
    from bourbaki.ensembles.base.ensembles_vide import non_vide_ssi_element
    vF, va = _t(F), _t(a)
    U = ensemble_majorants(vF, va)
    a_in_U = a_dans_majorants(F, a)                             # a∈U
    ex_z = N.modus_ponens(a_in_U, N.s5(appartient(var("z"), U), va, "z"))  # (∃z) z∈U
    return N.modus_ponens(ex_z, equivalence_arriere(non_vide_ssi_element(U)))


def majorants_inclus_interv(F="Fsup", a="a"):
    """⊢  U ⊂ [0,a]   où U=ensemble_majorants(F,a).   CLOS.

    w∈U ⇒ (w∈[0,a] et …) ⇒ w∈[0,a]  (membre_majorants, projection gauche)."""
    vF, va = _t(F), _t(a)
    U = ensemble_majorants(vF, va)
    interv = intervalle_0a(a)
    zsub = "z"                                                  # binder de inclus (défaut 'z') — DOIT
    vw = var(zsub)                                              # coïncider avec l'antécédent du bon ordre
    # z∈U ⇒ z∈[0,a] : axiome construit avec liant 'z', instancié à var('z') (IDENTITÉ ⇒ [0,a] PROPRE,
    # non renommé malgré le ∃z interne de 0=Card∅) ⇒ z∈[0,a] STRUCTURELLEMENT propre.
    Hw = N.assume(appartient(vw, U))
    rel = N.modus_ponens(Hw, equivalence_avant(membre_majorants(vF, va, vw, binder=zsub)))
    w_in_interv = conjonction_elim_gauche(rel)                  # z∈[0,a]  (propre)
    body = N.loi_deduction(appartient(vw, U), w_in_interv)
    res = N.generalisation(zsub, body)                          # (∀z)(z∈U ⇒ z∈[0,a]) = U⊂[0,a]
    assert res.conclusion == inclus(U, interv, z=zsub), "U⊂[0,a] mal formé"
    return res


# ═══════════════════════════════════════════════════════════════════════════════
#  LE THÉORÈME — existence de la borne supérieure (Prop 2, forme ensembliste)
# ═══════════════════════════════════════════════════════════════════════════════
def borne_superieure_existe(F="Fsup", a="a"):
    """⊢ { est_cardinal(a),  F⊂[0,a] }  ⊢  (∃s) est_borne_superieure_ensemble(s,F,a).

    🎯🎯 PROPOSITION 2 §III.3.2 (forme ENSEMBLISTE) : tout ensemble F de cardinaux
    MAJORÉ (par a) admet une BORNE SUPÉRIEURE.  L'ensemble U des majorants de F dans
    [0,a] est non vide (a∈U) et ⊂[0,a] ; par le BON ORDRE des cardinaux ≤ a
    (`cardinaux_bien_ordonnes_close`, CLOS), U a un ≤-plus petit élément s, qui est la
    borne supérieure (majorant minimal, via COMPARABILITÉ pour les majorants > a).

    HYPOTHÈSES INTENDUES (honnêtes, NON vacuux) : est_cardinal(a), F⊂[0,a] (F ensemble
    de cardinaux majoré par a).  `F≠∅` SUPERFLU (cf. docstring module).  theorie=22.

    ⚠️ COÛTEUX (~5 min) : `cardinaux_bien_ordonnes_close` (bon ordre, CLOS) est lourd
    (τ-cardinaux imbriqués) ; mémoïsé 1×/session via son lru_cache interne."""
    vF, va = _t(F), _t(a)
    interv = intervalle_0a(a)
    U = ensemble_majorants(vF, va)

    # ── U⊂[0,a] (CLOS), U≠∅ (sous est_cardinal(a), F⊂[0,a])
    U_sub = majorants_inclus_interv(F, a)                       # U⊂[0,a]
    U_ne = majorants_non_vide(F, a)                             # ¬(U=∅)   [card a, F⊂[0,a]]

    # ── bon ordre : (U⊂[0,a] et U≠∅) ⇒ (∃m)( m∈U et (∀x)(x∈U ⇒ m≤x) )
    bo = cardinaux_bien_ordonnes_close(a)                       # CLOS, (∀S)(...)
    bo_U = instancie(bo, U)                                     # (U⊂[0,a] et U≠∅) ⇒ (∃m)…
    hyp_bo = conjonction_intro(U_sub, U_ne)
    ex_m = N.modus_ponens(hyp_bo, bo_U)                         # (∃m)( m∈U et (∀x∈U) m≤x )

    # ── per-témoin m=s : corps_min ⊢ est_borne_superieure_ensemble(s,F,a)
    vs = var("m")                                               # binder de cardinaux_bien_ordonnes
    corps_min = et(appartient(vs, U),
                   pourtout("x", impl(appartient(var("x"), U), inf_egal_card(vs, var("x")))))
    Hmin = N.assume(corps_min)
    s_in_U = conjonction_elim_gauche(Hmin)                      # s∈U
    s_min = conjonction_elim_droite(Hmin)                       # (∀x)(x∈U ⇒ s≤x)

    # relation de s : s∈[0,a] et (∀c∈F) c≤s
    rel_s = N.modus_ponens(s_in_U, equivalence_avant(membre_majorants(vF, va, vs)))
    s_in_interv = conjonction_elim_gauche(rel_s)                # s∈[0,a]
    s_majore = conjonction_elim_droite(rel_s)                   # (∀c∈F) c≤s    [clause 2°]

    # 1° est_cardinal(s)
    est_card_s = N.modus_ponens(s_in_interv, _interv_implique_cardinal(va, vs))

    # s ≤ a  (de s∈[0,a])
    s_corps = N.modus_ponens(s_in_interv, equivalence_avant(_membre_interv(va, vs)))
    s_le_a = conjonction_elim_droite(s_corps)                   # s ≤ a

    # 3° plus petit majorant : (∀c)( ( c card et (∀d∈F) d≤c ) ⇒ s≤c )
    vc = var("csup")
    hyp_c = et(est_cardinal(vc), majore_clause(F, vc, "dsup"))
    Hc = N.assume(hyp_c)
    c_card = conjonction_elim_gauche(Hc)                        # c cardinal
    c_majore_dsup = conjonction_elim_droite(Hc)                 # (∀dsup∈F) dsup≤c
    # α-renomme le liant 'dsup' → 'cmaj' (liant de la clause-majore de U) : pur renommage ∀
    # (F, c plats, AUCUN τ-sous-atome) — pour matcher relation_majorant(...,'cmaj').
    c_majore = alpha_bridge(c_majore_dsup, majore_clause(F, vc, "cmaj"))

    #   COMPARABILITÉ : c≤a OU a≤c
    comp = comparabilite_cardinaux_terme(vc, va)               # c≤a ou a≤c

    #   BRANCHE c≤a : c∈[0,a] (c card, 0≤c, c≤a) et c majore F ⇒ c∈U ⇒ s≤c
    H_cle_a = N.assume(inf_egal_card(vc, va))                   # c ≤ a
    zero_le_c = N.modus_ponens(c_card, _zero_le(vc))           # 0 ≤ c
    c_corps_interv = conjonction_intro(conjonction_intro(c_card, zero_le_c), H_cle_a)
    c_in_interv = N.modus_ponens(c_corps_interv, equivalence_arriere(_membre_interv(va, vc)))
    rel_c = conjonction_intro(c_in_interv, c_majore)           # c∈[0,a] et c majore F
    assert rel_c.conclusion == relation_majorant(vF, va, vc, "cmaj"), \
        "relation_majorant(c) mal formée (branche c≤a)"
    c_in_U = N.modus_ponens(rel_c, equivalence_arriere(membre_majorants(vF, va, vc)))  # c∈U
    s_le_c_A = N.modus_ponens(c_in_U, instancie(s_min, vc))    # s ≤ c   (s min de U)
    brA = N.loi_deduction(inf_egal_card(vc, va), s_le_c_A)     # c≤a ⇒ s≤c

    #   BRANCHE a≤c : s≤a et a≤c ⇒ s≤c (transitivité)
    H_ale_c = N.assume(inf_egal_card(va, vc))                  # a ≤ c
    s_le_c_B = N.modus_ponens(conjonction_intro(s_le_a, H_ale_c), _trans(vs, va, vc))  # s≤c
    brB = N.loi_deduction(inf_egal_card(va, vc), s_le_c_B)     # a≤c ⇒ s≤c

    s_le_c = cas(comp, brA, brB)                               # s ≤ c
    body_ppm = N.loi_deduction(hyp_c, s_le_c)                  # (c card et c maj) ⇒ s≤c
    s_ppm = N.generalisation("csup", body_ppm)                 # plus_petit_majorant_ensemble(s,F)
    assert s_ppm.conclusion == plus_petit_majorant_ensemble(vs, F, "csup"), \
        "plus_petit_majorant_ensemble mal formé"

    # ── conjonction des 3 clauses = est_borne_superieure_ensemble(s,F,a)
    bsup_s = conjonction_intro(conjonction_intro(est_card_s, s_majore), s_ppm)
    assert bsup_s.conclusion == est_borne_superieure_ensemble(vs, F, a, "cmaj", "csup"), \
        "est_borne_superieure_ensemble(s) mal formé"

    # ── (∃s) est_borne_superieure_ensemble(s,F,a)  [témoin s='m']
    but = est_borne_superieure_ensemble(var("s"), F, a, "cmaj", "csup")
    # réintroduire (∃s) avec le binder 's' (≠ binders internes), témoin = var("m")
    ex_intro = N.modus_ponens(bsup_s, N.s5(but, vs, "s"))      # (∃s) bsup(s)
    wit_imp = N.loi_deduction(corps_min, ex_intro)
    res = N.modus_ponens(ex_m, existe_elimination(wit_imp, "m"))
    return res


def comparabilite_cardinaux_terme(u, v):
    """⊢ ( u ≤ v ) OU ( v ≤ u )   (aux TERMES u, v ; COMPARABILITÉ, INCONDITIONNEL).

    comparabilite_cardinaux aux NOMS PAR DÉFAUT (X,Y) — ses renommages-α internes
    supposent ces noms ; on généralise sur X,Y (absents des hyps, CLOS) puis instancie."""
    g = comparabilite_cardinaux()                                # X≤Y ou Y≤X, liants X,Y (défauts)
    g = N.generalisation("X", g)
    g = N.generalisation("Y", g)
    # dernier généralisé = extérieur : (∀Y)(∀X)… → instancie Y:=v, puis X:=u
    return instancie(instancie(g, _t(v)), _t(u))


# ── cible (test miroir) ─────────────────────────────────────────────────────────
def borne_superieure_existe_cible(F="Fsup", a="a"):
    """ÉNONCÉ-cible : (∃s) est_borne_superieure_ensemble(s, F, a)."""
    return existe("s", est_borne_superieure_ensemble(var("s"), F, a, "cmaj", "csup"))


__all__ = [
    "majore_clause", "relation_majorant", "ensemble_majorants",
    "axiome_majorants_F", "theorie_majorants_F", "membre_majorants",
    "majore_famille_ensemble", "plus_petit_majorant_ensemble",
    "est_borne_superieure_ensemble",
    "a_dans_majorants", "majorants_non_vide", "majorants_inclus_interv",
    "comparabilite_cardinaux_terme",
    "borne_superieure_existe", "borne_superieure_existe_cible",
]
