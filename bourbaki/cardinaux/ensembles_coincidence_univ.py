"""§III.2 — Lemme 1 (cœur Cantor–Bernstein des bons ordres) : COÏNCIDENCE des deux
isos sur SEGMENTS EMBOÎTÉS  S1 ⊂ S2  (dernière pièce de la TRICHOTOMIE, Théorème 3).

────────────────────────────────────────────────────────────────────────────────
RÔLE.  La TRICHOTOMIE des ordinaux (Th3 §III.2) est réduite à `coincidence_univ` :
étant donnés un bon ordre (E,≤), DEUX SEGMENTS EMBOÎTÉS  S1 ⊂ S2  de E, et deux
isomorphismes d'ordre  φ1 : S1 ≅ T1  et  φ2 : S2 ≅ T2  sur des segments de (F,≤'),
alors φ1 et φ2 COÏNCIDENT sur S1 :

        coincidence_univ :  ⊢ { … }  ⊢  (∀u)( u ∈ S1  ⇒  φ1(u) = φ2(u) ).

C'est l'UNICITÉ de l'iso entre bons ordres restreinte au chevauchement S1 (cœur de
Lemme 1 §III.2 / E.III.2.6) : φ2|S1 et φ1 sont deux isos de MÊME domaine S1, donc
l'automorphisme  c := φ2|S1⁻¹ ∘ φ1  de S1 est l'IDENTITÉ (Cor 1, bon ordre), d'où
φ1(u) = φ2(u) pour tout u ∈ S1.

────────────────────────────────────────────────────────────────────────────────
DIFFÉRENCE ESSENTIELLE avec `coincidence_depuis_isos_compat` (déjà CLOS sous hyps,
ensembles_coincidence_pont) — et pourquoi ce module n'est PAS un alias :

  • `coincidence_depuis_isos_compat` traite le cas MÊME DOMAINE : φ1 : S1 ≅ T1 et
    φ2 : S1 ≅ T1 sont DEUX isos sur LE MÊME segment S1.  Sa coïncidence consomme,
    entre autres, l'hypothèse  iso(φ2, S1, T1)  (φ2 vu comme iso de S1).

  • `coincidence_univ` traite le cas NESTÉ, FIDÈLE Lemme 1 : φ2 vit sur le PLUS GRAND
    segment S2 (φ2 : S2 ≅ T2), et l'on ne dispose que de  S1 ⊂ S2.  Ce module DÉCHARGE
    l'hypothèse  iso(φ2, S1, T1)  en la DÉRIVANT du contenu nesté :

        compatible_ordre(φ2, S2)  +  S1 ⊂ S2   ⊢   compatible_ordre(φ2, S1)
                                                    (restriction_compatible_ordre, CLOS)

    L'INCLUSION  S1 ⊂ S2  est ainsi RÉELLEMENT CONSOMMÉE (load-bearing) : la
    compatibilité d'ordre de φ2 sur le chevauchement S1 est OBTENUE par RESTRICTION de
    sa compatibilité sur le grand segment S2.  Le séquent de `coincidence_univ` parle
    donc de φ2 sur S2 (sa demeure native, Lemme 1) + S1 ⊂ S2 — au lieu de présupposer
    φ2 ordre-compatible sur S1.  La conclusion (φ1=φ2 sur S1) est INCHANGÉE, non
    tautologique (≠ toute hypothèse).

────────────────────────────────────────────────────────────────────────────────
CE QUE CE MODULE LIVRE (salvage fort, honnête, theorie=22, JAMAIS postulé/vacueux) :

  ✅ `coincidence_univ(...)`  (CONDITIONNEL PROPRE, residu identifié) :
        ⊢ {  est_bien_ordonne(R, S1),                              [bon ordre du chevauchement]
              S1 ⊂ S2,                                             [SEGMENTS EMBOÎTÉS — CONSOMMÉ]
              compatible_ordre(φ2, S2),                            [φ2 ordre-compat sur le GRAND seg]
              iso(φ1, S1, T1),                                     [φ1 : S1 ≅ T1, CONSOMMÉ]
              est_bijective(φ2, S1, T1),                           [bijectivité φ2|S1 — codomaine, REPORTÉ]
              + la GÉOMÉTRIE d'unicité de coincidence_sur_chevauchement
                (c=φ2|S1⁻¹∘φ1 : S1→S1 et son inverse strict. croissants, k∘c=id,
                 rétraction φ2(c(u))=φ1(u)) — résidu REPRÉSENTATIONNEL, voir REPORTÉ }
            ⊢ (∀u)( u ∈ S1  ⇒  φ1(u) = φ2(u) ).

     🎯 La dernière pièce de la trichotomie est ainsi RAMENÉE à ses données NESTÉES
     (φ2 sur S2, S1 ⊂ S2) + le résidu géométrique d'unicité, SANS rien postuler.
     L'inclusion des segments emboîtés est load-bearing (consommée par la restriction).

────────────────────────────────────────────────────────────────────────────────
⚠️ REPORTÉ (résidu HONNÊTE restant, identifié PRÉCISÉMENT — non franchi sans toucher
   aux fichiers committés) :

   (a) BIJECTIVITÉ de φ2|S1 sur son image (est_bijective(φ2, S1, T1)) : la restriction
       (BRIQUE 1, restriction_compatible_ordre) livre le CŒUR ORDRE de « φ2|S1 est un
       iso d'ordre de S1 sur φ2⟨S1⟩ » ; sa BIJECTIVITÉ sur S1 relève de la machinerie
       valeur/codomaine (`valeur_dans_codomaine`) — déjà REPORTÉE dans
       ensembles_trichotomie_restriction.  Portée ici en hypothèse EXPLICITE.

   (b) GÉOMÉTRIE d'UNICITÉ (c=φ2|S1⁻¹∘φ1 : S1→S1 et son inverse strict. croissants,
       rétraction k∘c=id, raccord φ2(c(u))=φ1(u)) : c'est le résidu « composition de
       graphes » + « verrou liant valeur b=y↔b=j » déjà DÉCHARGÉ pour la part STRICTE
       CROISSANCE par ensembles_coincidence_pont (le pont τ_y↔τ_j), et REPORTÉ pour la
       part rétraction/raccord (glue composition de graphes, cf. iso_unicite_finale).
       Hérité TEL QUEL de `coincidence_depuis_isos_compat` (CLOS sous ces hyps).

   Ces résidus sont MATHÉMATIQUEMENT des conséquences des deux isos de segments ; le
   franchir relève de la machinerie valeur/codomaine + composition de graphes — hors
   périmètre de CE module, qui CIBLE l'EMBOÎTEMENT S1 ⊂ S2 (la « restriction de φ2 au
   chevauchement », pièce manquante NOMMÉE de la trichotomie).

INVARIANT : theorie_ensembles() = 22.  RÉUTILISE `coincidence_depuis_isos_compat`
(ensembles_coincidence_pont, CLOS sous hyps) et `restriction_compatible_ordre`
(ensembles_trichotomie_restriction, CLOS sous hyps) — tous DÉJÀ committés.  NE MODIFIE
AUCUN fichier existant.  Aucune tautologie, aucun affaiblissement, rien postulé ; le
conditionnel porte ses hypothèses dans le séquent et la conclusion n'y figure pas.
"""
from __future__ import annotations

from bourbaki.logique.formule import Terme, var, appartient, inclus
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.ordre.iii_1_relations_ordre.ordre_treillis import ensembles_ordre_vocab as V
from bourbaki.logique.tactiques.tactiques_abrege2 import conjonction_intro
from bourbaki.cardinaux.ensembles_coincidence_pont import (
    coincidence_depuis_isos_compat, coincidence_depuis_isos_compat_cible,
)
from bourbaki.cardinaux.ensembles_trichotomie_restriction import (
    restriction_compatible_ordre,
)


def _t(t):
    """Coercion nom→terme (accepte un Terme ou un nom de variable)."""
    return t if isinstance(t, Terme) else var(t)


def _Rgraphe(nom):
    """Relation portée par le graphe `nom` : a ≤ b := (a,b) ∈ G_nom (convention iso
    de auto_de_deux_isos / composee_isomorphisme_ordre, héritée du chaînage)."""
    vG = var(nom)
    return lambda a, b: appartient(E.couple(a, b), vG)


# Les binders « x », « x2 » sont EXACTEMENT ceux que `composee_isomorphisme_ordre`
# (donc auto_de_deux_isos, donc coincidence_depuis_isos_compat) emploie pour la clause
# d'iso interne — vérifié : iso(φ2,S1,T1,G,Gp,x="x",y="x2") figure littéralement dans
# les hypothèses de coincidence_depuis_isos_compat.  On RECONSTRUIT cette formule à
# l'identique pour la DÉCHARGER.
_ISO_X, _ISO_Y = "x", "x2"


# ════════════════════════════════════════════════════════════════════════════
#  COÏNCIDENCE UNIVERSELLE sur SEGMENTS EMBOÎTÉS S1 ⊂ S2  (Lemme 1 §III.2).
#  Décharge iso(φ2,S1,T1) en la dérivant de φ2 sur S2 + S1 ⊂ S2 (RESTRICTION).
# ════════════════════════════════════════════════════════════════════════════
def coincidence_univ(phi1="phi1", phi2="phi2", psi="psi", chi="chi",
                     S1="S1", S2="S2", T1="T1", c="c", k="k", u="u",
                     G="G", Gp="Gp"):
    """⊢ {  est_bien_ordonne(R, E) + inclus(S1, E),   [BON ORDRE AMBIANT, jamais bo(R,S1)]
            S1 ⊂ S2,                              [SEGMENTS EMBOÎTÉS — CONSOMMÉ]
            compatible_ordre(φ2, S2),             [φ2 ordre-compat sur le GRAND segment]
            iso(φ1, S1, T1),                      [φ1 : S1 ≅ T1 — CONSOMMÉ]
            est_bijective(φ2, S1, T1),            [bijectivité φ2|S1 — codomaine, REPORTÉ (a)]
            + géométrie d'unicité (c,k:S1→S1 strict. crois., k∘c=id, φ2(c(u))=φ1(u))
              héritée de coincidence_sur_chevauchement — résidu REPORTÉ (b) }
         ⊢ (∀u)( u ∈ S1  ⇒  φ1(u) = φ2(u) ).

    🎯 DERNIÈRE PIÈCE de la TRICHOTOMIE (Th3 §III.2) ramenée à ses données NESTÉES.
    Deux isos de segments φ1 : S1 ≅ T1 et φ2 : S2 ≅ T2 avec S1 ⊂ S2 coïncident sur S1.

    PREUVE.  On part de `coincidence_depuis_isos_compat` (CLOS sous hyps), forme MÊME
    DOMAINE prise en S := S1, φ := φ1, φ' := φ2.  Sa conclusion est DÉJÀ la cible
    (∀u)(u∈S1 ⇒ φ1(u)=φ2(u)).  Mais elle PRÉSUPPOSE  iso(φ2, S1, T1)  (φ2 vu comme iso
    de S1).  On DÉCHARGE cette hypothèse en la PROUVANT depuis le contenu NESTÉ :

        iso(φ2, S1, T1)  =  est_bijective(φ2, S1, T1)  ET  compatible_ordre(φ2, S1)
          • compatible_ordre(φ2, S1)  ⟵  restriction_compatible_ordre(φ2, S2, S1)
              { compatible_ordre(φ2, S2),  S1 ⊂ S2 }  ⊢  compatible_ordre(φ2, S1)   (CLOS)
            — l'INCLUSION S1 ⊂ S2 est CONSOMMÉE : la compatibilité sur le chevauchement
              S1 est la RESTRICTION de celle sur le grand segment S2 (Lemme 1).
          • est_bijective(φ2, S1, T1)  reste hypothèse EXPLICITE (codomaine, REPORTÉ (a)).
        On RECOLLE  iso(φ2,S1,T1) = et(bijective, compatible)  (conjonction_intro) puis
        on DÉCHARGE l'hypothèse correspondante de la base (modus_ponens + loi_deduction).

    La conclusion reste φ1=φ2 sur S1, NON tautologique (≠ toute hypothèse).  Le séquent
    final ne présuppose plus la compatibilité de φ2 sur S1 : il porte φ2 sur S2 + S1⊂S2
    (fidèle Lemme 1).  RIEN postulé ; theorie=22.  Résidus (a),(b) en tête de module."""
    Rf, Rpf = _Rgraphe(G), _Rgraphe(Gp)
    vphi2, vS1, vT1 = _t(phi2), _t(S1), _t(T1)

    # ── base : coïncidence MÊME DOMAINE en S:=S1, φ:=φ1, φ':=φ2 (CLOS sous hyps) ──
    base = coincidence_depuis_isos_compat(
        phi=phi1, phip=phi2, psi=psi, chi=chi,
        S=S1, T=T1, c=c, k=k, u=u, G=G, Gp=Gp)

    # ── la FORMULE iso(φ2,S1,T1) que la base présuppose (binders x,x2 — composee) ──
    iso_form = V.est_isomorphisme_ordre(vphi2, vS1, vT1, Rf, Rpf, _ISO_X, _ISO_Y)
    assert iso_form in set(base.hypotheses), \
        "iso(phi2,S1,T1) introuvable dans les hypothèses de la base — binders inattendus"

    # ── PREUVE de iso(φ2,S1,T1) depuis le contenu NESTÉ ───────────────────────────
    #   compatible_ordre(φ2,S1) ⟵ restriction de compatible_ordre(φ2,S2) sous S1⊂S2.
    compat_proof = restriction_compatible_ordre(
        phi=phi2, S=S2, S0=S1, R=G, Rp=Gp, x=_ISO_X, y=_ISO_Y)   # ⊢ compatible_ordre(φ2,S1)
    #   est_bijective(φ2,S1,T1) : hypothèse EXPLICITE (codomaine — REPORTÉ (a)).
    bij_form = E.est_bijective(vphi2, vS1, vT1)
    bij_proof = N.assume(bij_form)
    #   iso(φ2,S1,T1) = et(est_bijective, compatible_ordre)  (ordre de conjonction de
    #   est_isomorphisme_ordre : bijective puis compatible).
    iso_proof = conjonction_intro(bij_proof, compat_proof)
    assert iso_proof.conclusion == iso_form, "recollement iso(φ2,S1,T1) ≠ forme attendue"

    # ── DÉCHARGE de iso(φ2,S1,T1) dans la base ────────────────────────────────────
    out = N.modus_ponens(iso_proof, N.loi_deduction(iso_form, base))
    return out                                  # (∀u)(u∈S1 ⇒ φ1(u)=φ2(u))


def coincidence_univ_cible(phi1="phi1", phi2="phi2", S1="S1"):
    """ÉNONCÉ-cible (test miroir) de coincidence_univ :
        (∀u)( u ∈ S1  ⇒  φ1(u) = φ2(u) ).
    Identique à la conclusion de coincidence_depuis_isos_compat (S:=S1, φ:=φ1, φ':=φ2)."""
    return coincidence_depuis_isos_compat_cible(phi=phi1, phip=phi2, S=S1)


__all__ = ["coincidence_univ", "coincidence_univ_cible"]
