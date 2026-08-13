"""§III.1.7 — LE TERME « plus grand élément » :  M_R(A) := τ_m( m plus grand élt de A ).

🎯 `terme_plus_grand_vaut` : { est_plus_grand_element(R,A,a), antisymetrie_sur(R,A) }
                              ⊢  M_R(A) = a.                              [2 hyps]

LA BRIQUE MANQUANTE, NOMMÉE.  Le dépôt possédait le PRÉDICAT « a est le plus grand
élément de A » (`ensembles_abrege.est_plus_grand_element`, §III.1.7 Déf. 4) mais
AUCUN TERME le désignant : impossible d'écrire « le plus grand élément de A » dans
une formule.  C'est ce terme que Bourbaki note M(u) en E III.46 (« Soit M(u) la
borne supérieure de D(u) dans N »), brique de la déduction de C63 depuis C62.

CODAGE — τ, exactement comme le livre l'autorise.  La NOTE 2 de E III.46 dit que la
définition de la borne supérieure (III, p. 10) « peut être formulée de telle sorte
qu'elle garde un sens même pour un ensemble non majoré (elle désigne un terme du
langage formalisé de la forme τ_x(R{x}), que le lecteur explicitera sans peine) ».
On explicite donc :

    M_R(A) := τ_m ( est_plus_grand_element(R, A, m) ).

Ce terme est TOTAL (τ dénote toujours) ; il ne dénote le plus grand élément QUE
lorsqu'il en existe un — ce que dit précisément le théorème ci-dessous.

────────────────────────────────────────────────────────────────────────────────
ÉCART DE FIDÉLITÉ ASSUMÉ ET NOMMÉ.  Bourbaki écrit « la BORNE SUPÉRIEURE de D(u)
dans N » (sup = plus petit des majorants, §III.1.9 Déf. 6), pas « le PLUS GRAND
ÉLÉMENT ».  Mathématiquement les deux coïncident dès que le plus grand élément
existe — et c'est le seul cas dont C63 se sert (D(u) = [0,n[ est un intervalle
d'entiers, qui a un plus grand élément).  Ce module code donc le PLUS GRAND
ÉLÉMENT.  Deux réserves, mesurées, à ne pas gommer :
  (a) `plus_grand_est_borne_superieure` EXISTE bien au dépôt (§III.1.9,
      `ordre_treillis/ensembles_ordre_relation.py`, 2 hypothèses { A⊂E, m plus
      grand élt }) — mais dans la convention GRAPHE G ((x,m)∈G), alors qu'ici on
      est en convention RELATION R.  Le pont R↔G N'EST PAS câblé : la coïncidence
      « plus grand élément = sup » n'est donc PAS disponible comme théorème sur
      les termes de ce module.  Ne pas la citer comme acquise.
  (b) Le sup GÉNÉRAL (partie majorée SANS plus grand élément, où les τ-termes des
      deux notions DIFFÈRENT) reste NON couvert — et hors de portée d'un τ sur
      « plus grand élément ».

────────────────────────────────────────────────────────────────────────────────
ROUTE (order-théorique pure, aucun axiome, < 0,1 s) :
  1. H₁ : a est le plus grand élément de A.
  2. S5 (témoin a) : (∃m)( m plus grand élt de A ).
  3. `existe_temoin` (réciproque de S5 pour le témoin canonique τ) :
        M_R(A) est un plus grand élément de A.
  4. a majore A, instancié en M ∈ A  →  R{M, a} ;
     M majore A, instancié en a ∈ A  →  R{a, M}.
  5. H₂ (antisymétrie de R SUR A), instanciée en (M, a) : M = a.
L'antisymétrie est REQUISE et n'est pas gratuite : sans elle deux « plus grands
éléments » distincts se majorant mutuellement resteraient possibles.  Elle est
demandée SUR A seulement (pas globalement) — hypothèse la plus faible qui conclut.

⚠️ LIANTS.  `est_plus_grand_element` lie « x » ; `antisymetrie_sur` lie « u »,« v » ;
le τ lie « m ».  Beaucoup de relations concrètes lient EN INTERNE des noms banals :
mesuré ce jour, `inf_egal_card` (l'ordre des cardinaux) lie {F, u, up, v, y, z} —
les défauts « u »/« v » y ENTRENT EN COLLISION.  D'où les défauts « u1 »/« v1 » et
le garde-fou `verifie_liants_frais`, qui REFUSE explicitement au lieu de laisser le
noyau échouer plus loin sur un « modus ponens : mineure ≠ antécédent » opaque.

INVARIANT : theorie_ensembles() = 22.  Noyau et subst INTOUCHÉS.  Rien postulé.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, Formule, var, egal, et, impl, appartient, pourtout, tau, libres_t,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite, instancie,
)

#: Liants par défaut. « u »/« v » sont PROSCRITS : `inf_egal_card` les lie en interne.
LIANT_TAU = "m"
LIANT_MAJORE = "x"
LIANT_ANTISYM = ("u1", "v1")


def _terme(t):
    return t if isinstance(t, Terme) else var(t)


def liants_de(objet, acc=None):
    """Ensemble des noms de variables LIÉES apparaissant dans une formule/terme.

    Sert au garde-fou : un liant externe qui coïncide avec un liant INTERNE de la
    relation R produit une capture silencieuse à l'instanciation."""
    acc = set() if acc is None else acc
    if isinstance(objet, (Formule, Terme)):
        if objet.lieur:
            acc.add(objet.lieur)
        for s in getattr(objet, "sous", ()):
            liants_de(s, acc)
        for t in getattr(objet, "termes", ()):
            liants_de(t, acc)
        for a in getattr(objet, "args", ()):
            liants_de(a, acc)
    return acc


def verifie_liants_frais(R, A, a=None, m=LIANT_TAU, x=LIANT_MAJORE,
                         u=LIANT_ANTISYM[0], v=LIANT_ANTISYM[1]):
    """Refuse tout liant externe capturé par R, par A ou par a.  Lève ValueError.

    Trois sources de capture, toutes constatées en pratique :
      • un liant INTERNE de R portant le même nom (ex. `inf_egal_card` lie u, v) ;
      • une variable LIBRE de A portant le même nom (A est sous les liants) ;
      • idem pour le témoin a."""
    demandes = {"m": m, "x": x, "u": u, "v": v}
    internes = liants_de(R(var("_sonde1"), var("_sonde2")))
    fautes = [f"{cle}={nom!r} est lié À L'INTÉRIEUR de R"
              for cle, nom in demandes.items() if nom in internes]
    libres = libres_t(_terme(A)) | (libres_t(_terme(a)) if a is not None else set())
    fautes += [f"{cle}={nom!r} est libre dans A (ou dans a)"
               for cle, nom in demandes.items() if nom in libres]
    if fautes:
        raise ValueError("liants non frais — capture garantie : " + " ; ".join(fautes)
                         + f".  Liants internes de R mesurés : {sorted(internes)}.")


# @livre Ch.III §1.7 Def.4 | E III.8 L.26-27 | PDF p.111   (L.30-32 était FAUX, recompté le 27 juil.)
# @livre Ch.III §6.2 Rem.- | E III.46 L.36-38 | PDF p.149  (note 2 : « La définition de la borne supérieure (III, p. 10) peut être formulée de telle sorte qu'elle garde un sens même pour un ensemble non majoré (elle désigne un terme du langage formalisé de la forme τ_x(R{x}), que le lecteur explicitera sans peine) » — ICI le τ-terme explicité)
def terme_plus_grand(R, A, m=LIANT_TAU, x=LIANT_MAJORE):
    """M_R(A) := τ_m ( est_plus_grand_element(R, A, m) ).

    Le TERME « le plus grand élément de A ».  Total (τ dénote toujours) ; il ne
    désigne le plus grand élément que si A en possède un (cf.
    `terme_plus_grand_vaut`).  C'est le M(·) de Bourbaki E III.46, explicité au
    sens de la note 2 de cette page."""
    return tau(m, E.est_plus_grand_element(R, _terme(A), var(m), x))


def antisymetrie_sur(R, A, u=LIANT_ANTISYM[0], v=LIANT_ANTISYM[1]):
    """« R est antisymétrique SUR A » :=

        (∀u)(∀v)( ((u∈A et v∈A) et (R{u,v} et R{v,u})) ⇒ u=v ).

    Restriction à A de l'antisymétrie (E.III.1.1, Déf. 1) : c'est l'hypothèse la
    plus faible qui donne l'unicité du plus grand élément DE A."""
    vA, vu, vv = _terme(A), var(u), var(v)
    return pourtout(u, pourtout(v, impl(
        et(et(appartient(vu, vA), appartient(vv, vA)), et(R(vu, vv), R(vv, vu))),
        egal(vu, vv))))


def cible_terme_plus_grand_vaut(R, A, a, m=LIANT_TAU, x=LIANT_MAJORE):
    """ÉNONCÉ-cible (test miroir) :  M_R(A) = a."""
    return egal(terme_plus_grand(R, A, m, x), _terme(a))


# @livre Ch.III §1.7 Def.4 | E III.8 L.26-27 | PDF p.111   (L.30-32 était FAUX, recompté le 27 juil.)
# @livre Ch.III §6.2 Demo.C63 | E III.46 L.28-29 | PDF p.149  (« Soit M(u) la borne supérieure de D(u) dans N » — LE terme M ; citation FINE à l'intérieur du L.25-33 déjà posé par ensembles_recursion_hygienic, qu'elle raffine sans le contredire)
def terme_plus_grand_vaut(R, A, a, m=LIANT_TAU, x=LIANT_MAJORE,
                          u=LIANT_ANTISYM[0], v=LIANT_ANTISYM[1]):
    """🎯 { est_plus_grand_element(R,A,a), antisymetrie_sur(R,A) } ⊢ M_R(A) = a.

    LE TERME DÉNOTE.  Dès que A possède un plus grand élément a — et que R est
    antisymétrique sur A — le τ-terme M_R(A) EST cet élément.  C'est ce qui fait
    de M(·) un opérateur légitime et non un simple τ décoratif.

    Preuve : S5 au témoin a donne l'existence, `existe_temoin` la transporte au
    témoin canonique τ (M est donc lui-même un plus grand élément), puis M et a se
    majorent mutuellement et l'antisymétrie sur A les identifie.

    HONNÊTETÉ.  Aucune existence n'est postulée : l'hypothèse
    `est_plus_grand_element(R,A,a)` la porte.  Rien n'est affirmé lorsque A n'a pas
    de plus grand élément (le τ dénote alors un objet non spécifié) — c'est
    exactement la portée de la note 2 de E III.46."""
    verifie_liants_frais(R, A, a, m, x, u, v)
    vA, va = _terme(A), _terme(a)
    corps = E.est_plus_grand_element(R, vA, var(m), x)
    M = tau(m, corps)
    # (1) a est le plus grand élément de A
    H1 = N.assume(E.est_plus_grand_element(R, vA, va, x))
    a_in = conjonction_elim_gauche(H1)                     # a ∈ A
    a_maj = conjonction_elim_droite(H1)                    # (∀x)(x∈A ⇒ R{x,a})
    # (2) le témoin canonique τ est LUI AUSSI un plus grand élément
    ex = N.modus_ponens(H1, N.s5(corps, va, m))            # (∃m)( m plus grand élt )
    pgeM = N.modus_ponens(ex, N.existe_temoin(corps, m))   # M est plus grand élt de A
    M_in = conjonction_elim_gauche(pgeM)                   # M ∈ A
    M_maj = conjonction_elim_droite(pgeM)                  # (∀x)(x∈A ⇒ R{x,M})
    # (3) M et a se majorent mutuellement
    R_aM = N.modus_ponens(a_in, instancie(M_maj, va))      # R{a, M}
    R_Ma = N.modus_ponens(M_in, instancie(a_maj, M))       # R{M, a}
    # (4) antisymétrie sur A, instanciée en (M, a)
    H2 = N.assume(antisymetrie_sur(R, vA, u, v))
    anti = instancie(instancie(H2, M), va)
    prem = conjonction_intro(conjonction_intro(M_in, a_in),
                             conjonction_intro(R_Ma, R_aM))
    res = N.modus_ponens(prem, anti)                       # M = a
    assert res.conclusion == cible_terme_plus_grand_vaut(R, vA, va, m, x), \
        "terme_plus_grand_vaut : conclusion ≠ M_R(A) = a"
    assert res.hypotheses == frozenset({
        E.est_plus_grand_element(R, vA, va, x), antisymetrie_sur(R, vA, u, v)}), \
        "terme_plus_grand_vaut : hypothèses ≠ { plus grand élt, antisymétrie sur A }"
    return res


__all__ = ["LIANT_TAU", "LIANT_MAJORE", "LIANT_ANTISYM",
           "liants_de", "verifie_liants_frais",
           "terme_plus_grand", "antisymetrie_sur",
           "cible_terme_plus_grand_vaut", "terme_plus_grand_vaut"]
