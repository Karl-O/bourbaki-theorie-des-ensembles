"""Chapitre III §2 — LEMME 3 (BOURBAKI–WITT) et chemin vers ZORN.

KEYSTONE.  On vise le THÉORÈME DE POINT FIXE DE BOURBAKI–WITT, *sans* axiome du
choix : si (E,≤) est un ensemble ordonné CHAÎNE-COMPLET (toute chaîne possède une
borne supérieure dans E) et p : E → E une application INFLATIONNAIRE
(p(x) ≥ x pour tout x), alors p admet un POINT FIXE  (∃s) p(s)=s.

RECETTE — calque EXACT de Knaster–Tarski / Cantor–Bernstein
(`ensembles_cantor_bernstein.py`, motif D=⋂{S φ-clos}, `phi_point_fixe`).

On fixe un point de base a∈E (typiquement le PLUS PETIT élément de E).  On appelle
« TOUR » (admissible) toute partie S⊂E qui
    (T1) contient a,                                   [a ∈ S]
    (T2) est close par p,         p(x)∈S pour x∈S      [clos par p]
    (T3) est close par sup de chaîne                   [clos par sup de chaîne].
On pose le PLUS PETIT TOUR
    M(G,E,p,a) := ⋂ { S⊂E | S est une tour admissible }
introduit comme TERME + axiome DÉFINITIONNEL `axiome_M` dans une théorie DÉDIÉE
`theorie_M` (légitime S8+A1, motif `axiome_D`).  theorie_ensembles() reste = 22.

LEMMES DIRECTS livrés ici (calque des lemmes D_inclus_A / D_inclus / phi_D_inclus_D) :
  • M_membre        : caractérisation membre de M (axiome instancié).
  • M_inclus_E      : M ⊂ E.
  • M_inclus        : (S tour admissible) ⇒ M ⊂ S.
  • a_dans_M        : a ∈ M  (M contient le point de base).
  • M_clos_p        : (x∈M) ⇒ p(x)∈M  (M close par p).
  • M_clos_sup      : (C chaîne ⊂ M, s borne sup de C dans E) ⇒ s∈M.
  • ps_minore_par_s / p_de_sup_inferieur : si s = sup(M) ∈ M alors p(s) ≤ s
                      (s majore M ⊇ {p(s)}), donc avec inflationnaire p(s) ≥ s
                      l'antisymétrie donne p(s) = s — voir `point_fixe_de_sup`.
  • point_fixe_de_sup : { antisym, p inflat., s = plus grand élément de M } ⊢ p(s)=s.

ÉNONCÉS (définitions d'énoncés, PAS des preuves) :
  • bourbaki_witt(G,E,p,a) : (est_ordre ∧ chaîne-complet ∧ p:E→E ∧ p inflationnaire
       ∧ a plus petit élt de E) ⇒ (∃s) p(s)=s.
  • zorn_via_bw(G,E)       : redite de l'énoncé de Zorn, obtenu de Bourbaki–Witt :
       E inductif sans maximal ⇒ τ donne p(x) majorant STRICT de x, p inflat.,
       Bourbaki–Witt p(s)=s, or p(s)>s — contradiction ⇒ (∃m) maximal.

🔒 REPORTÉ (le VERROU, multi-rounds) : « M est une CHAÎNE » (M totalement ordonné).
   C'est le cœur dur de Bourbaki–Witt (récurrence sur l'admissibilité / éléments
   « extrêmes » de Bourbaki–Witt).  On l'EXPOSE comme énoncé `M_est_une_chaine`
   et `bourbaki_witt_si_M_chaine` (preuve conditionnée à ce verrou) — JAMAIS postulé.

On réutilise INTÉGRALEMENT `ensembles_ordre_relation` (est_ordre, antisymetrie,
totalement_ordonne, majorant, borne_superieure, plus_grand_element, …) et
`ensembles_zorn` (chaine, est_inductif, enonce_non_vide, zorn).
"""
from __future__ import annotations

from bourbaki.logique.formule import (
    Terme, var, egal, et, ou, non, impl, equiv, appartient, existe, pourtout, inclus,
)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.logique.tactiques.tactiques_abrege import syllogisme
from bourbaki.logique.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    projection_gauche, projection_droite,
    equivalence_avant, equivalence_arriere, instancie, instanciation_en_x,
)
from bourbaki.ordre.ensembles_ordre_relation import (
    est_ordre, antisymetrie, totalement_ordonne, majorant, borne_superieure,
    plus_grand_element, plus_petit_element,
)
from bourbaki.ordre.ensembles_zorn import (
    chaine, est_inductif, enonce_non_vide,
)


def _terme(t):
    return t if isinstance(t, Terme) else var(t)


def _couple_dans(t, u, G):
    """Formule « (t,u) ∈ G »  (i.e. « t ≤ u » pour le graphe d'ordre G)."""
    return appartient(E.couple(_terme(t), _terme(u)), _terme(G))


def _cut(thm, hyp, preuve_hyp):
    """De  Γ∪{H} ⊢ C  et  Δ ⊢ H  on déduit  Γ∪Δ ⊢ C  (décharge de H puis MP)."""
    return N.modus_ponens(preuve_hyp, N.loi_deduction(hyp, thm))


def pval(p, x):
    """p(x) := valeur de l'application inflationnaire p en x  (terme opaque).

    On garde p ABSTRAIT (opérateur inflationnaire général d'un ensemble ordonné),
    via un terme fonctionnel dédié `bw_p` (motif `D = app("D_kt",…)`), de sorte
    que la clôture « p(x)∈S » et l'inflation « (x,p(x))∈G » aient un sens
    purement ordinal, sans présupposer que p soit un graphe-fonction."""
    return E.app("bw_p", _terme(p), _terme(x))


# ════════════════════════════════════════════════════════════════════════════
#  DÉFINITIONS FIDÈLES — inflationnaire, chaîne-complet  (E.III.2, Lemme 3)
# ════════════════════════════════════════════════════════════════════════════
def inflationnaire(G, E_set, p, x="x"):
    """inflationnaire(G,E,p) := (∀x)( x∈E ⇒ (x, p(x))∈G ).

    « p est INFLATIONNAIRE (extensive) » : p(x) ≥ x pour tout x∈E.  Hypothèse
    centrale du Lemme 3 de Bourbaki–Witt."""
    vE, vx = _terme(E_set), var(x)
    return pourtout(x, impl(appartient(vx, vE), _couple_dans(vx, pval(p, vx), G)))


def application_dans(E_set, p, x="x"):
    """application_dans(E,p) := (∀x)( x∈E ⇒ p(x)∈E ).   « p : E → E »
    (p envoie E dans E ; condition de bonne définition de la clôture par p)."""
    vE, vx = _terme(E_set), var(x)
    return pourtout(x, impl(appartient(vx, vE), appartient(pval(p, vx), vE)))


def chaine_complet(G, E_set, C="C", s="s", x="x", y="y", z="z"):
    """chaine_complet(G,E) := est_ordre(G,E) et
        (∀C)( chaine(G,E,C) ⇒ (∃s) borne_superieure(G,C,s,E) ).

    « (E,≤) est CHAÎNE-COMPLET » : toute chaîne (partie totalement ordonnée) de E
    possède une BORNE SUPÉRIEURE dans E.  (Hypothèse du Lemme 3 de Bourbaki–Witt ;
    forme fidèle, calquée sur `est_inductif` mais avec borne_sup à la place de
    majorant.)"""
    vC = var(C)
    corps = impl(chaine(G, E_set, vC, x, y, z),
                 existe(s, borne_superieure(G, vC, var(s), E_set, x, y)))
    return et(est_ordre(G, E_set, x, y, z), pourtout(C, corps))


# ════════════════════════════════════════════════════════════════════════════
#  LA TOUR M = ⋂ { S⊂E | a∈S, S clos par p, S clos par sup de chaîne }
#  Terme + axiome DÉFINITIONNEL (S8+A1) dans une théorie DÉDIÉE — motif axiome_D.
#  theorie_ensembles() reste INCHANGÉE = 22 axiomes.
# ════════════════════════════════════════════════════════════════════════════
def M(G, E_set, p, a):
    """M := ⋂ { S⊂E | S tour admissible }  (le plus petit tour de Bourbaki–Witt)."""
    return E.app("bw_M", _terme(G), _terme(E_set), _terme(p), _terme(a))


def _clos_par_p(E_set, p, s, x="x"):
    """« S est close par p » := (∀x)( x∈S ⇒ p(x)∈S )."""
    vS, vx = _terme(s), var(x)
    return pourtout(x, impl(appartient(vx, vS), appartient(pval(p, vx), vS)))


def _clos_par_sup(G, E_set, s, c="C", w="w", x="x", y="y", z="z"):
    """« S est close par sup de chaîne » :=
        (∀C)( (C⊂S et chaine(G,E,C)) ⇒ (∀w)( borne_superieure(G,C,w,E) ⇒ w∈S ) ).

    Toute borne supérieure (dans E) d'une chaîne incluse dans S appartient à S."""
    vS, vC, vw = _terme(s), var(c), var(w)
    corps = impl(et(inclus(vC, vS), chaine(G, E_set, vC, x, y, z)),
                 pourtout(w, impl(borne_superieure(G, vC, vw, E_set, x, y),
                                  appartient(vw, vS))))
    return pourtout(c, corps)


def est_tour(G, E_set, p, a, s, x="x", y="y", z="z", c="C", w="w"):
    """est_tour(G,E,p,a,S) := (S⊂E) et (a∈S) et (S clos par p) et (S clos par sup).

    « S est un TOUR admissible » de Bourbaki–Witt (relativement au point de base a)."""
    vS, va = _terme(s), _terme(a)
    return et(et(et(inclus(vS, _terme(E_set)), appartient(va, vS)),
                 _clos_par_p(E_set, p, vS, x)),
              _clos_par_sup(G, E_set, vS, c, w, x, y, z))


def _corps_M(G, E_set, p, a, z, x="x", y="y", zz="z", c="C", w="w"):
    """Corps de M :  z∈E et (∀S)( S tour admissible ⇒ z∈S )."""
    vz, vE = _terme(z), _terme(E_set)
    allS = pourtout("S", impl(est_tour(G, E_set, p, a, var("S"), x, y, zz, c, w),
                              appartient(vz, var("S"))))
    return et(appartient(vz, vE), allS)


def axiome_M(G="G", E_set="E", p="p", a="a", z="z"):
    """⊢-schéma  (∀G)(∀E)(∀p)(∀a)(∀z)( z∈M ⇔ (z∈E et (∀S)(S tour ⇒ z∈S)) ).

    Axiome DÉFINITIONNEL du plus petit tour (intersection des tours admissibles ;
    légitime S8+A1, motif `axiome_D` de Cantor–Bernstein).  N'altère PAS
    theorie_ensembles()."""
    vG, vE, vp, va, vz = var(G), var(E_set), var(p), var(a), var(z)
    return pourtout(G, pourtout(E_set, pourtout(p, pourtout(a, pourtout(z,
        equiv(appartient(vz, M(vG, vE, vp, va)),
              _corps_M(vG, vE, vp, va, vz)))))))


def theorie_M(G="G", E_set="E", p="p", a="a", z="z"):
    """Théorie DÉDIÉE ne contenant que l'axiome de M (E.III.2, Bourbaki–Witt)."""
    return N.Theorie("M-Bourbaki-Witt", [axiome_M(G, E_set, p, a, z)])


def _inst_M(G, E_set, p, a, z):
    """⊢ ( z∈M ⇔ (z∈E et (∀S)(S tour ⇒ z∈S)) )   (axiome instancié aux TERMES)."""
    ax = N.axiome(theorie_M(), axiome_M())
    return instancie(instancie(instancie(instancie(instancie(ax, G), E_set), p), a), z)


# ════════════════════════════════════════════════════════════════════════════
#  LEMMES DIRECTS sur M  (calque de D_membre / D_inclus_A / D_inclus)
# ════════════════════════════════════════════════════════════════════════════
def M_membre(G="G", E_set="E", p="p", a="a", z="z"):
    """⊢ ( z∈M ) ⇔ ( z∈E et (∀S)( S tour admissible ⇒ z∈S ) )."""
    return _inst_M(var(G), var(E_set), var(p), var(a), var(z))


def M_inclus_E(G="G", E_set="E", p="p", a="a"):
    """⊢ M ⊂ E.   (le plus petit tour est inclus dans E.)"""
    vG, vE, vp, va, vz = var(G), var(E_set), var(p), var(a), var("z")
    eq = _inst_M(vG, vE, vp, va, vz)                    # z∈M ⇔ (z∈E et ∀S…)
    z_imp = syllogisme(equivalence_avant(eq),
                       projection_gauche(appartient(vz, vE),
                                         _allS_form(vG, vE, vp, va, vz)))
    return N.generalisation("z", z_imp)                 # (∀z)(z∈M⇒z∈E) = M⊂E


def M_inclus(G="G", E_set="E", p="p", a="a", s="S"):
    """⊢ ( S tour admissible ) ⇒ ( M ⊂ S ).

    M est inclus dans CHAQUE tour admissible (c'est leur intersection)."""
    vG, vE, vp, va, vS, vz = var(G), var(E_set), var(p), var(a), var(s), var("z")
    tour = est_tour(vG, vE, vp, va, vS)
    h = N.assume(tour)
    eq = _inst_M(vG, vE, vp, va, vz)
    z_to_all = syllogisme(equivalence_avant(eq),
                          projection_droite(appartient(vz, vE),
                                            _allS_form(vG, vE, vp, va, vz)))
    hz = N.assume(appartient(vz, M(vG, vE, vp, va)))    # z∈M
    all_from_z = N.modus_ponens(hz, z_to_all)           # (∀S)(S tour⇒z∈S)  [z∈M]
    inst_from_z = instancie(all_from_z, vS)             # (S tour ⇒ z∈S)    [z∈M]
    zS = N.modus_ponens(h, inst_from_z)                 # z∈S  [z∈M, tour]
    z_imp = N.loi_deduction(appartient(vz, M(vG, vE, vp, va)), zS)   # (z∈M⇒z∈S) [tour]
    incl = N.generalisation("z", z_imp)                 # M⊂S  [tour]
    return N.loi_deduction(tour, incl)                  # ⊢ (S tour) ⇒ (M⊂S)


def _allS_form(G, E_set, p, a, z, x="x", y="y", zz="z", c="C", w="w"):
    """(∀S)( S tour admissible ⇒ z∈S )   (2e conjoint du corps de M)."""
    return pourtout("S", impl(est_tour(G, E_set, p, a, var("S"), x, y, zz, c, w),
                              appartient(_terme(z), var("S"))))


# ── a∈M, M close par p, M close par sup : « M est lui-même un tour » ──────────
#
# Cœur de la stratégie (calque de phi_D_inclus_D : « D est φ-close ») : on montre
# que M satisfait (T1)(T2)(T3), donc M est le PLUS PETIT tour.  Ces lemmes
# DÉCOULENT du fait que CHAQUE tour S vérifie (T1)(T2)(T3) et que M⊂S.

def a_dans_M(G="G", E_set="E", p="p", a="a"):
    """⊢ { a∈E } ⊢ a ∈ M.   (M contient le point de base a.)

    a∈S pour chaque tour S (T1), donc a appartient à l'intersection M ; et a∈E
    par hypothèse, donc a vérifie le corps de M."""
    vG, vE, vp, va = var(G), var(E_set), var(p), var(a)
    ha = N.assume(appartient(va, vE))                   # a∈E
    # (∀S)( S tour ⇒ a∈S )  : de la déf est_tour, a∈S est le 2e conjoint (T1).
    tourS = est_tour(vG, vE, vp, va, var("S"))
    htour = N.assume(tourS)
    # est_tour = ((S⊂E et a∈S) et clos_p) et clos_sup ; a∈S = proj droite du bloc gauche-gauche
    a_in_S = conjonction_elim_droite(
        conjonction_elim_gauche(conjonction_elim_gauche(htour)))   # a∈S  [tour]
    S_imp = N.loi_deduction(tourS, a_in_S)              # (S tour ⇒ a∈S)
    allS = N.generalisation("S", S_imp)                 # (∀S)(S tour ⇒ a∈S)
    corps = conjonction_intro(ha, allS)                 # a∈E et (∀S)…   [a∈E]
    return N.modus_ponens(corps, equivalence_arriere(_inst_M(vG, vE, vp, va, va)))  # a∈M


def M_clos_p(G="G", E_set="E", p="p", a="a", x="u"):
    """⊢ ( x∈M ) ⇒ ( p(x) ∈ M ).   (M est close par p — propriété (T2) de M.)

    Le paramètre `x` (la variable d'élément) vaut « u » par défaut, lettre FRAÎCHE
    distincte du liant interne « x » de la clôture (∀x)(x∈S⇒p(x)∈S) : sans cela la
    substitution z:=p(x) dans l'axiome de M renommerait ce liant en @0 et
    casserait l'égalité structurelle au modus ponens final.

    Pour chaque tour S : x∈M ⇒ x∈S (M⊂S) ⇒ p(x)∈S (S close par p).  Comme p(x)∈S
    pour TOUT tour S, et p(x)∈E (car p(x)∈S⊂E pour un S quelconque), p(x)∈M."""
    vG, vE, vp, va, vx = var(G), var(E_set), var(p), var(a), var(x)
    Mt = M(vG, vE, vp, va)
    hx = N.assume(appartient(vx, Mt))                   # x∈M
    # pour S tour : x∈S (M_inclus) et S close par p → p(x)∈S
    tourS = est_tour(vG, vE, vp, va, var("S"))
    htour = N.assume(tourS)
    MS = N.modus_ponens(htour, M_inclus_terme(vG, vE, vp, va, var("S")))   # M⊂S  [tour]
    # M⊂S = (∀z)(z∈M⇒z∈S) ; instancier en x
    MS_x = instancie(MS, vx)                            # x∈M ⇒ x∈S   [tour]
    xS = N.modus_ponens(hx, MS_x)                       # x∈S  [x∈M, tour]
    clos_p = conjonction_elim_droite(conjonction_elim_gauche(htour))      # (∀x)(x∈S⇒p(x)∈S) [tour]
    clos_p_x = instancie(clos_p, vx)                    # x∈S ⇒ p(x)∈S  [tour]
    pxS = N.modus_ponens(xS, clos_p_x)                  # p(x)∈S  [x∈M, tour]
    S_imp = N.loi_deduction(tourS, pxS)                 # (S tour ⇒ p(x)∈S)  [x∈M]
    allS = N.generalisation("S", S_imp)                 # (∀S)(S tour ⇒ p(x)∈S)  [x∈M]
    # p(x)∈E : M⊂E donne x∈E ; mais on veut p(x)∈E. On le tire de application_dans
    # n'étant PAS dispo ici, on utilise : pour tout tour S, p(x)∈S⊂E.  On choisit
    # de conclure p(x)∈M via le corps (z∈E et ∀S…) — z∈E sera fourni par S⊂E.
    # Dérivation de p(x)∈E à partir de allS + (S⊂E) : reportée à l'assemblage
    # (nécessite l'existence d'au moins un tour, p.ex. E lui-même). On EXPOSE donc
    # ce lemme sous la forme conditionnelle « p(x)∈M dès que p(x)∈E ».
    hpxE = N.assume(appartient(pval(vp, vx), vE))       # p(x)∈E  (hyp explicite)
    corps = conjonction_intro(hpxE, allS)               # p(x)∈E et (∀S)…   [x∈M, p(x)∈E]
    pxM = N.modus_ponens(corps,
                         equivalence_arriere(_inst_M(vG, vE, vp, va, pval(vp, vx))))  # p(x)∈M
    return N.loi_deduction(appartient(vx, Mt), pxM)     # (x∈M ⇒ p(x)∈M)  [p(x)∈E]


def M_clos_sup(G="G", E_set="E", p="p", a="a", c="C", s="s", x="x", y="y", z="z", w="w"):
    """⊢ ( (C⊂M et chaine(G,E,C)) et borne_superieure(G,C,s,E) ) ⇒ ( s∈M ).

    (M close par sup de chaîne — propriété (T3) de M.)  Pour chaque tour S : C⊂M⊂S,
    donc C est une chaîne ⊂ S, et S close par sup ⇒ s∈S.  s∈S pour tout tour S, et
    s∈E (s borne sup dans E), donc s∈M."""
    vG, vE, vp, va = var(G), var(E_set), var(p), var(a)
    vC, vs = var(c), var(s)
    Mt = M(vG, vE, vp, va)
    hyp = et(et(inclus(vC, Mt), chaine(vG, vE, vC, x, y, z)),
             borne_superieure(vG, vC, vs, vE, x, y))
    hh = N.assume(hyp)
    CM = conjonction_elim_gauche(conjonction_elim_gauche(hh))   # C⊂M
    chaineC = conjonction_elim_droite(conjonction_elim_gauche(hh))  # chaine(G,E,C)
    bsup = conjonction_elim_droite(hh)                  # borne_superieure(G,C,s,E)
    # s∈E : borne_superieure(G,C,s,E) = majorant(G,C,s,E) et … ; majorant ⇒ s∈E
    maj_s = conjonction_elim_gauche(bsup)               # majorant(G,C,s,E)
    s_in_E = conjonction_elim_gauche(maj_s)             # s∈E
    # pour S tour : C⊂S (C⊂M⊂S), donc (C⊂S et chaine) ⇒ (∀w)(bsup(w)⇒w∈S) ; w:=s
    tourS = est_tour(vG, vE, vp, va, var("S"))
    htour = N.assume(tourS)
    MS = N.modus_ponens(htour, M_inclus_terme(vG, vE, vp, va, var("S")))   # M⊂S  [tour]
    # C⊂S : transitivité C⊂M, M⊂S
    CS = _inclusion_trans(vC, Mt, var("S"), CM, MS)     # C⊂S  [tour]
    clos_sup = conjonction_elim_droite(htour)           # (∀C)((C⊂S et chaine)⇒(∀w)(bsup⇒w∈S)) [tour]
    clos_sup_C = instancie(clos_sup, vC)                # (C⊂S et chaine)⇒(∀w)(bsup⇒w∈S)  [tour]
    all_w = N.modus_ponens(conjonction_intro(CS, chaineC), clos_sup_C)   # (∀w)(bsup⇒w∈S) [tour]
    sup_to_S = instancie(all_w, vs)                     # bsup(G,C,s,E) ⇒ s∈S  [tour]
    sS = N.modus_ponens(bsup, sup_to_S)                 # s∈S  [hyp, tour]
    S_imp = N.loi_deduction(tourS, sS)                  # (S tour ⇒ s∈S)  [hyp]
    allS = N.generalisation("S", S_imp)                 # (∀S)(S tour ⇒ s∈S)  [hyp]
    corps = conjonction_intro(s_in_E, allS)             # s∈E et (∀S)…  [hyp]
    sM = N.modus_ponens(corps, equivalence_arriere(_inst_M(vG, vE, vp, va, vs)))  # s∈M
    return N.loi_deduction(hyp, sM)                     # ⊢ hyp ⇒ s∈M


# ── helpers TERME (instanciation des lemmes-lettres à des termes) ─────────────
def M_inclus_terme(G, E_set, p, a, s):
    """⊢ ( S tour admissible ) ⇒ ( M ⊂ S )  pour des TERMES quelconques."""
    th = M_inclus("G", "E", "p", "a", "S")
    for nm, tm in (("G", G), ("E", E_set), ("p", p), ("a", a), ("S", s)):
        th = instancie(N.generalisation(nm, th), tm)
    return th


def _inclusion_trans(a, b, c, ab, bc):
    """De ⊢ a⊂b et ⊢ b⊂c, déduit ⊢ a⊂c (sous les mêmes hypothèses)."""
    from bourbaki.logique.tactiques.tactiques_abrege2 import inclusion_transitive
    th = inclusion_transitive("a", "b", "c")            # ((a⊂b)et(b⊂c))⇒(a⊂c)
    for nm, tm in (("a", a), ("b", b), ("c", c)):
        th = instancie(N.generalisation(nm, th), tm)
    return N.modus_ponens(conjonction_intro(ab, bc), th)


# ════════════════════════════════════════════════════════════════════════════
#  CŒUR DE BOURBAKI–WITT — p(s) ≤ s puis p(s)=s (l'antisymétrie ferme le point fixe)
# ════════════════════════════════════════════════════════════════════════════
def p_de_sup_inferieur(G="G", E_set="E", p="p", a="a", s="s", x="x"):
    """⊢ { p(s)∈M, plus_grand_element(G,M,s) } ⊢ ( p(s), s )∈G.   i.e.  p(s) ≤ s.

    Si s est le PLUS GRAND élément de M (la borne sup de M, qui est dans M par
    clôture sup) et si p(s)∈M (clôture par p), alors s MAJORE p(s) : (p(s),s)∈G.
    C'est l'inégalité « p(s) ≤ s » — moitié facile du point fixe."""
    vG, vE, vp, va, vs = var(G), var(E_set), var(p), var(a), var(s)
    Mt = M(vG, vE, vp, va)
    ps = pval(vp, vs)
    Hps = N.assume(appartient(ps, Mt))                  # p(s)∈M
    Hpge = N.assume(plus_grand_element(vG, Mt, vs, x))   # s∈M et (∀x)(x∈M⇒(x,s)∈G)
    s_maj = conjonction_elim_droite(Hpge)               # (∀x)(x∈M⇒(x,s)∈G)
    s_maj_ps = instancie(s_maj, ps)                     # p(s)∈M ⇒ (p(s),s)∈G
    return N.modus_ponens(Hps, s_maj_ps)                # (p(s),s)∈G   [p(s)∈M, s pge]


def point_fixe_de_sup(G="G", E_set="E", p="p", a="a", s="s", x="x", y="y"):
    """⊢ { antisymetrie(G), inflationnaire(G,E,p), s∈E, p(s)∈M,
           plus_grand_element(G,M,s) } ⊢ p(s) = s.

    POINT FIXE de Bourbaki–Witt, ÉTAGE FINAL (l'antisymétrie ferme).  s majore M
    qui contient p(s) (clôture) ⇒ (p(s),s)∈G ; p inflationnaire ⇒ (s,p(s))∈G ;
    antisymétrie ⇒ p(s)=s.  (Reste à fournir « p(s)∈M » et « s = plus grand élt
    de M » depuis la construction — voir M_clos_p / M_clos_sup ; le verrou « M
    chaîne » sert à garantir que M a une borne sup = plus grand élément.)"""
    vG, vE, vp, va, vs = var(G), var(E_set), var(p), var(a), var(s)
    ps = pval(vp, vs)
    Has = N.assume(antisymetrie(vG, x, y))               # (∀x∀y)(((x,y)et(y,x))⇒x=y)
    Hinf = N.assume(inflationnaire(vG, vE, vp, x))        # (∀x)(x∈E⇒(x,p(x))∈G)
    Hs_E = N.assume(appartient(vs, vE))                  # s∈E
    # (1) (p(s),s)∈G   via p_de_sup_inferieur  (hyps p(s)∈M, s plus grand élt de M)
    ps_le_s = p_de_sup_inferieur(G, E_set, p, a, s, x)   # ⊢ (p(s),s)∈G  [p(s)∈M, s pge]
    # (2) (s,p(s))∈G   via inflationnaire en s
    inf_s = instancie(Hinf, vs)                          # s∈E ⇒ (s,p(s))∈G
    s_le_ps = N.modus_ponens(Hs_E, inf_s)                # (s,p(s))∈G   [s∈E]
    # (3) antisymétrie en (p(s), s) : ((p(s),s) et (s,p(s))) ⇒ p(s)=s
    antisym_ps_s = instancie(instancie(Has, ps), vs)     # ((p(s),s)∈G et (s,p(s))∈G)⇒p(s)=s
    return N.modus_ponens(conjonction_intro(ps_le_s, s_le_ps), antisym_ps_s)  # p(s)=s


# ════════════════════════════════════════════════════════════════════════════
#  ÉNONCÉS — Bourbaki–Witt et Zorn  (DÉFINITIONS d'énoncés, PAS des preuves)
# ════════════════════════════════════════════════════════════════════════════
def bourbaki_witt(G, E_set, p, a, s="s", x="x", y="y", z="z"):
    """bourbaki_witt(G,E,p,a) :=
        ( est_ordre(G,E) ∧ chaine_complet(G,E) ∧ application_dans(E,p)
          ∧ inflationnaire(G,E,p) ∧ plus_petit_element(G,E,a) )
        ⇒ (∃s) ( p(s) = s ).

    ÉNONCÉ du LEMME 3 §III.2 (THÉORÈME DE POINT FIXE DE BOURBAKI–WITT), SANS choix.
    ⚠ DÉFINITION de l'énoncé — la preuve repose sur « M est une chaîne » (verrou
    reporté) ; JAMAIS postulée."""
    vE, vp, vs = _terme(E_set), _terme(p), var(s)
    hyp = et(et(et(et(est_ordre(G, vE, x, y, z),
                      chaine_complet(G, vE, "C", s, x, y, z)),
                   application_dans(vE, vp, x)),
                inflationnaire(G, vE, vp, x)),
             plus_petit_element(G, vE, _terme(a), x))
    return impl(hyp, existe(s, egal(pval(vp, vs), vs)))


def M_est_une_chaine(G, E_set, p, a, x="x", y="y", z="z"):
    """M_est_une_chaine(G,E,p,a) := totalement_ordonne(G, M(G,E,p,a)).

    ÉNONCÉ du VERROU de Bourbaki–Witt : le plus petit tour M est TOTALEMENT
    ORDONNÉ (une chaîne).  C'est le cœur dur du Lemme 3 (récurrence sur
    l'admissibilité / comparabilité des éléments « extrêmes » de Bourbaki–Witt).
    🔒 REPORTÉ — exposé comme énoncé, JAMAIS prouvé ni postulé ici."""
    return totalement_ordonne(G, M(_terme(G), _terme(E_set), _terme(p), _terme(a)),
                              x, y, z)


def zorn_via_bw(G, E_set, m="m", C="C", x="x", y="y", z="z"):
    """zorn_via_bw(G,E) := ( est_ordre(G,E) ∧ est_inductif(G,E) ∧ E≠∅ )
        ⇒ (∃m) element_maximal(G,E,m).

    ÉNONCÉ du THÉORÈME 2 (ZORN) §III.2, dans la VOIE Bourbaki–Witt : si E inductif
    n'avait PAS d'élément maximal, le signe τ fournirait p:E→E avec p(x) majorant
    STRICT de x (donc p inflationnaire), Bourbaki–Witt donnerait p(s)=s, or p(s)>s
    — contradiction.  D'où l'existence d'un maximal.
    ⚠ DÉFINITION d'énoncé, IDENTIQUE à `ensembles_zorn.zorn` ; rappelée ici pour
    documenter la réduction Zorn ⇐ Bourbaki–Witt.  JAMAIS prouvée (verrou M chaîne
    + signe τ)."""
    from bourbaki.ordre.ensembles_zorn import zorn
    return zorn(G, E_set, m, C, x, y, z)


def bourbaki_witt_si_M_chaine(G, E_set, p, a, s="s", x="x", y="y", z="z"):
    """bourbaki_witt_si_M_chaine(G,E,p,a) :=
        M_est_une_chaine(G,E,p,a) ⇒ bourbaki_witt(G,E,p,a).

    ÉNONCÉ de la preuve CONDITIONNELLE de Bourbaki–Witt : une fois le verrou « M
    est une chaîne » établi, M a une borne sup s∈M (clôture sup), s est le plus
    grand élément de M, p(s)∈M (clôture p) et p(s)≤s (s majore M) tandis que
    p(s)≥s (inflationnaire) — d'où p(s)=s par `point_fixe_de_sup`.  L'assemblage
    effectif (existentiel sur s) est livré dès que `M_est_une_chaine` est prouvé.
    ⚠ DÉFINITION d'énoncé conditionnel — PAS une preuve (le verrou reste ouvert)."""
    return impl(M_est_une_chaine(G, E_set, p, a, x, y, z),
                bourbaki_witt(G, E_set, p, a, s, x, y, z))


__all__ = [
    # valeur de p
    "pval",
    # définitions fidèles
    "inflationnaire", "application_dans", "chaine_complet", "est_tour",
    # tour M + axiome dédié
    "M", "axiome_M", "theorie_M", "M_membre",
    # lemmes directs sur M
    "M_inclus_E", "M_inclus", "a_dans_M", "M_clos_p", "M_clos_sup",
    # cœur point fixe
    "p_de_sup_inferieur", "point_fixe_de_sup",
    # énoncés (définitions d'énoncés, non prouvés)
    "bourbaki_witt", "M_est_une_chaine", "zorn_via_bw", "bourbaki_witt_si_M_chaine",
    # helpers terme
    "M_inclus_terme",
]
