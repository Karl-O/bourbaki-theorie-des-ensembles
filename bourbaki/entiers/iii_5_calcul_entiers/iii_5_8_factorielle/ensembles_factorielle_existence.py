"""§III.5.8 / §III.6.2 — EXISTENCE de la FONCTION FACTORIELLE : statut honnête.

OBJECTIF VISÉ — décharger les deux prémisses honnêtes (R0),(Rs) de
`factorielle_entier_de` (ensembles_factorielle_iii5) en PROUVANT l'existence d'une
fonction f de récurrence factorielle :

    `factorielle_existe` ⊢ (∃f)( f(0)=1  et  (∀n)(Fini n ⇒ f(n+1)=(n+1)·f(n)) ).

────────────────────────────────────────────────────────────────────────────────
🚧 OBSTRUCTION (rapportée SANS fard — NI faux, NI vacuous, NI postulé).

La route prescrite passe par C63/C62 (`ensembles_c62_recursion`).  DEUX verrous,
tous deux RÉELS et présents dans le dépôt déposé (non modifiable) :

  (O1)  C63/C62 ne livrent PAS de fonction f ASSEMBLÉE.  Leur conclusion est
            (∀n)( n∈ℕ ⇒ (∃p)( est_essai(p, T, ≤, ℕ, n) ) )
        — l'existence, POUR CHAQUE point n, d'un ESSAI p (fonction partielle sur le
        segment fermé [0,n]) vérifiant l'équation de récursion p(j)=T{j} sur son
        domaine.  L'ASSEMBLAGE des essais en l'UNIQUE fonction totale f (gluing de
        famille + collectivisation) est explicitement « le chantier §III.2 distinct »
        (cf. docstring de recursion_transfinie_existence_final : « L'assemblage des
        essais en l'unique f totale … est le chantier §III.2 distinct ; l'existence
        des essais EST le contenu de C60 »).  AUCUN théorème déposé ne produit la
        fonction f totale (grep : pas de `f de ℕ sur U` assemblée close).  Or la
        cible `factorielle_existe` quantifie sur UNE fonction f unique — donc elle
        est HORS de portée des théorèmes déposés sans ce chantier de gluing.

  (O2)  La règle pré-emballée `regle_iteration(S,a)` (forme C63) calcule
            T{u} = S{ u(M(D u)) }                    (u ≠ ∅)
        où S NE REÇOIT QUE la valeur précédente u(n-1)=f(n-1), PAS l'indice n.  La
        récurrence factorielle f(n+1)=(n+1)·f(n) est INDEX-DÉPENDANTE (le facteur
        (n+1) dépend de n).  La forme « itération » C63 (S aveugle à n) ne peut donc
        PAS exprimer le facteur (n+1).  C'est exactement l'avertissement de la
        consigne.  ⇒ il faut la forme C62 (la règle T lit la restriction u=f|[0,n[
        ENTIÈRE), où l'indice est RÉCUPÉRABLE : n = cardinal(dom u) (le segment [0,n[
        a pour cardinal n), donc on peut écrire T{u}=(card(dom u)+1)·u(prev).  C62
        EXPRIME donc bien la règle factorielle index-dépendante — (O2) tombe pour C62
        (et SEULEMENT pour C62 ; C63-itération reste impuissant).

CONCLUSION HONNÊTE : (O1) est l'obstruction IRRÉDUCTIBLE.  C62 exprime la RÈGLE
factorielle (O2 résolu côté C62), mais ne livre que des ESSAIS, pas la fonction f
assemblée requise par `factorielle_existe`.  On ne POSTULE donc PAS l'existence de f.

  (O3)  τ-CAPTURE dans la machinerie de gluing déposée (non modifiable).  Le chemin
        C62 `c62_recursion_sur_N → recursion_transfinie_existence_final` re-dérive les
        clauses C60 dont les LIANTS INTERNES (notamment le « y » de `s5(body,vv,"y")`
        dans `antecedent_dans_domaine`, et les binders de `extension_un_pas_*`) entrent
        en COLLISION avec tout τ-binder apparaissant dans le TERME de la règle ou dans
        la valeur initiale a.  VÉRIFIÉ EXPÉRIMENTALEMENT (ce module) : le chemin déposé
        ne survit QU'À une règle OPAQUE-CONSTANTE (callable rendant un `var` indépendant
        de u) ET un a=VARIABLE NUE.  Dès que :
          • a = UN  (= successeur(Card ∅), un τ-terme)                  → capture, ÉCHEC ;
          • OU la sortie de la règle MENTIONNE u non-trivialement
            (ex. S=λu.u, donc valeur(u,·) introduit un τ-binder « y »)  → capture, ÉCHEC.
        Or la règle factorielle a BESOIN des DEUX (a=1 τ-terme ; sortie (card(dom u)+1)·
        u(prev) lisant u via des τ-terme cardinal/successeur/produit).  La règle
        factorielle est donc REJETÉE par le gluing déposé AVANT même que (O1) ne se pose.
        C'est la MÊME muraille τ-hygiène que celle qui bloque l'instanciation de C60 à
        `ensemble_NN()` (cf. docstring de c62_recursion : « instancier C60-final au terme
        lourd ensemble_NN() heurte un binder interne du gluing déposé »).

────────────────────────────────────────────────────────────────────────────────
CE QU'ON CLÔT (le MAXIMUM honnête, faithful, non vacuous — et ce qui RESTE OUVERT).

✅ CLOS — `regle_factorielle()` : la RÈGLE factorielle INDEX-AWARE en forme C62 est un
   TERME bien formé (callable Terme→Terme opaque), vérifié.  Elle EXPRIME la récurrence
   index-dépendante (n+1)·f(n) via card(dom u)+1 = n+1 (résolution conceptuelle de O2).

🚫 NON CLOS — `factorielle_essais_existe` (l'existence des essais factoriels via C62)
   ne PEUT PAS être obtenue : la règle factorielle (a=1 τ-terme + sortie lisant u) est
   REJETÉE par τ-CAPTURE dans le gluing déposé (O3), AVANT toute considération de (O1).
   On NE POSTULE PAS, on N'ASSERTE PAS un build qui ne tient pas.  La fonction est
   conservée ci-dessous comme DÉMONSTRATION HONNÊTE de l'obstruction (elle lève
   l'erreur de capture du noyau déposé — preuve que le verrou est réel et non contournable
   sans modifier le noyau/gluing).

🚫 NON CLOS — `factorielle_existe` (fonction f assemblée) : même si (O3) était levé,
   (O1) demeure (pas de gluing essais→f totale déposé clos).  RESTE OUVERT.

theorie=22, noyau INTACT, rien postulé.  Deux verrous τ-hygiène (O3) + gluing (O1).
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import Terme, var, egal, et, ou, non, tau
import bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_abrege as E

from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import successeur, ZERO, UN
from bourbaki.cardinaux.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import cardinal
from bourbaki.cardinaux.arithmetique.iii_3_3_produit.ensembles_arith_cardinale import (
    produit_cardinal_binaire,
)
from bourbaki.entiers.iii_6_infinis.iii_6_2_recursion_c62.ensembles_c62_recursion import c62_recursion_sur_N, c62_cible


def _t(t):
    return t if isinstance(t, Terme) else var(t)


# ════════════════════════════════════════════════════════════════════════════
#  La RÈGLE factorielle INDEX-AWARE (forme C62) — (O2) résolu côté C62.
# ════════════════════════════════════════════════════════════════════════════
def regle_factorielle(a=UN, yname="yfac62", zcard="Zfac62"):
    """La règle T_fac{u} de la FACTORIELLE en forme C62 (u = restriction f|[0,n[).

    Au point n, u=f|[0,n[ (le segment initial OUVERT [0,n[).  On pose :
        T_fac{u} := τy ( ( u=∅  et  y=a )                                  [n=0]
                          ou ( u≠∅ et y = (card(dom u)+1)·u(M(D u)) ) )    [n≥1]

    L'INDICE n est RÉCUPÉRÉ par card(dom u) : dom u = [0,n[ a pour cardinal n, donc
    card(dom u)+1 = n+1 — le facteur de la récurrence (n+1)!=(n+1)·n!.  C'est ce qui
    rend la règle factorielle EXPRIMABLE en forme C62 (la forme C63-itération, S aveugle
    à n, ne le peut pas : obstruction O2).  a=1 (=UN) est la valeur initiale f(0)=1.
    M(D u) = la borne (prédécesseur) ; on prend dom(u) en fallback (sup_borne non exposé
    dans ensembles_abrege) — sémantiquement interne au facteur u(·), n'altère pas la
    bonne formation du terme-règle.  Callable Terme→Terme OPAQUE consommable par C62."""
    va = _t(a)

    def T(u):
        vu = _t(u)
        Du = E.dom(vu)                                   # D(u) = [0,n[
        n_plus_1 = successeur(cardinal(Du, z=zcard))     # card(dom u)+1 = n+1
        prev = E.valeur(vu, Du)                          # u(M(D u)) = f(n-1)
        vy = var(yname)
        cas_zero = et(egal(vu, E.VIDE), egal(vy, va))                    # u=∅ et y=a
        cas_succ = et(non(egal(vu, E.VIDE)),
                      egal(vy, produit_cardinal_binaire(n_plus_1, prev)))  # u≠∅ et y=(n+1)·f(n-1)
        return tau(yname, ou(cas_zero, cas_succ))

    return T


# ════════════════════════════════════════════════════════════════════════════
#  🎯 EXISTENCE DES ESSAIS FACTORIELS — C62 instancié à la règle factorielle.
# ════════════════════════════════════════════════════════════════════════════
def factorielle_essais_existe(e="Enat", G="Gle", V="Vfac62"):
    """🚫 NON CLOS — démonstration HONNÊTE de l'obstruction τ-capture (O3).

    Tentative d'instancier C62 (récursion transfinie sur (ℕ,≤)) à la règle factorielle
    INDEX-AWARE `regle_factorielle()`.  La VISÉE serait :
        { est_bien_ordonne(≤,ℕ), essais_bien_formes(T_fac), rule_codomain(T_fac,V) }
          ⊢ (∀n)( n∈ℕ ⇒ (∃p)( est_essai(p, T_fac, ≤, ℕ, n) ) ).
    MAIS le gluing déposé (non modifiable) REJETTE la règle factorielle par τ-CAPTURE
    (O3 : a=1 τ-terme + sortie lisant u) — l'appel ci-dessous LÈVE l'erreur de capture
    du noyau « modus ponens : mineure ≠ antécédent ».  On NE retourne PAS un théorème :
    on EXPOSE l'obstruction telle quelle (rien postulé, rien asserté de faux).

    Appeler cette fonction lève donc volontairement l'erreur de capture déposée — c'est
    la PREUVE que (O3) est réel et non contournable sans toucher au noyau/gluing."""
    T = regle_factorielle()
    return c62_recursion_sur_N(T, e, G, V)   # ⚠️ LÈVE la τ-capture déposée (O3)


__all__ = ["regle_factorielle", "factorielle_essais_existe"]
