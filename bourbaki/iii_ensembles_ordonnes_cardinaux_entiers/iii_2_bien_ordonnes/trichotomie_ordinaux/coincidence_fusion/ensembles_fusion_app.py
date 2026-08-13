"""§III.2 — Consommation de `coincidence_univ_app` (CLOSE) du côté FUSION.

────────────────────────────────────────────────────────────────────────────────
RÔLE.  `coincidence_univ_app` (ensembles_coincidence_univ_app) est un THÉORÈME CLOS :
    ⊢ (∀S1,T1,φ1,S2,T2,φ2)( PRÉMISSE_APPLICATIONS ⇒ (∀w)(w∈S1 ⇒ φ1(w)=φ2(w)) ).
La PRÉMISSE témoigne φ1,φ2 comme APPLICATIONS (iso + func + dom + graphe⊂S×T) + segments
+ bons ordres.  Ce module en DÉRIVE la coïncidence ponctuelle utilisée par la fusion :

    `coincidence_point_app` :  { PRÉMISSE_APPLICATIONS(petit, grand) , p∈S_petit }
                                ⊢  φ_petit(p) = φ_grand(p).

C'est l'analogue de `_coinc_point` (ensembles_fusion_assemblage) MAIS qui consomme la
coïncidence PROUVÉE (coincidence_univ_app, sans hypothèse) au lieu de la `coincidence_univ`
POSTULÉE.  La coïncidence du Lemme 1 §III.2 n'est donc PLUS un report : elle est ici
DÉRIVÉE, conditionnée UNIQUEMENT aux données « applications » des deux segments-témoins.

RESTE pour brancher entièrement la fusion : RENFORCER le témoin de h (`axiome_h` /
`_coeur1`) pour porter func/dom/graphe (φ APPLICATION — fidèle : h = union de GRAPHES
d'isos), afin que les cœurs fournissent cette PRÉMISSE.  Cf. [[n-bien-ordre-route]].

INVARIANT : theorie_ensembles() = 22.  Rien postulé (coincidence_univ_app est CLOS).
NON vacueux.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import Terme, var, appartient, egal
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import instancie, conjonction_intro
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.trichotomie_ordinaux.coincidence_fusion.ensembles_coincidence_univ_app import (
    coincidence_univ_app, _premisse_liste, coincidence_univ_app_point_cible,
)


def _t(x):
    return x if isinstance(x, Terme) else var(x)


# @livre Ch.III §2.5 Demo.3 | E III.21 L.26-33 | PDF p.124  (démonstration du Th. 3 : recollement des isos — coïncidence ponctuelle consommée par la fusion)
def coincidence_point_app(phip="phip", phig="phig", Sp="Sp", Tp="Tp",
                          Sg="Sg", Tg="Tg", F="F", R="R", Rp="Rp", p="p"):
    """⊢ { PRÉMISSE_APPLICATIONS(φ_petit:Sp≅Tp, φ_grand:Sg≅Tg ; Sp⊂Sg ; …) , p∈Sp }
          ⊢ φ_petit(p) = φ_grand(p)   [liant « j »].

    Instancie `coincidence_univ_app` (CLOS) aux 6 témoins (Sp,Tp,φ_petit,Sg,Tg,φ_grand),
    décharge sa PRÉMISSE (13 formules-applications, conjointes ; bons ordres AMBIANTS
    bo(R,Sg)+bo(R',F)) depuis les hypothèses, puis spécialise au point p∈Sp.  La coïncidence
    ponctuelle est ainsi PROUVÉE (coincidence_univ_app n'apporte AUCUNE hypothèse — clos)."""
    thm = coincidence_univ_app()                            # ⊢ (∀6 témoins)(prém ⇒ coïncidence)
    inst = thm
    for w in (_t(Sp), _t(Tp), _t(phip), _t(Sg), _t(Tg), _t(phig)):   # ordre ∀ : S1,T1,φ1,S2,T2,φ2
        inst = instancie(inst, w)                           # ⊢ prém(témoins) ⇒ (∀w)(w∈Sp ⇒ φp(w)=φg(w))
    # prouver la PRÉMISSE (conjonction left-nested) à partir de ses 13 conjoints assumés
    prem = _premisse_liste(phip, phig, Sp, Tp, Sg, Tg, F, R, Rp)
    acc = N.assume(prem[0])
    for pi in prem[1:]:
        acc = conjonction_intro(acc, N.assume(pi))          # ⊢_{13} conjonction = PRÉMISSE
    forall_w = N.modus_ponens(acc, inst)                    # ⊢_{13} (∀w)(w∈Sp ⇒ φp(w)=φg(w))
    imp_p = instancie(forall_w, _t(p))                      # p∈Sp ⇒ φp(p)=φg(p)
    Hp = N.assume(appartient(_t(p), _t(Sp)))
    return N.modus_ponens(Hp, imp_p)                        # ⊢_{15, p∈Sp} φp(p)=φg(p)


def coincidence_point_app_cible(phip="phip", phig="phig", p="p"):
    """ÉNONCÉ-cible (test miroir) : φ_petit(p) = φ_grand(p)  (liant « j »)."""
    return egal(E.valeur(_t(phip), _t(p), b="j"), E.valeur(_t(phig), _t(p), b="j"))


__all__ = ["coincidence_point_app", "coincidence_point_app_cible"]
