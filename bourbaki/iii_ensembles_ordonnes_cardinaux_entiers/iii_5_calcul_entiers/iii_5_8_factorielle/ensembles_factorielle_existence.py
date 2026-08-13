"""§III.5.8 / §III.6.2 — EXISTENCE de la FONCTION FACTORIELLE : statut honnête.

OBJECTIF VISÉ — décharger les deux prémisses honnêtes (R0),(Rs) de
`factorielle_entier_de` (ensembles_factorielle_iii5) en PROUVANT l'existence d'une
fonction f de récurrence factorielle :

    `factorielle_existe` ⊢ (∃f)( f(0)=1  et  (∀n)(Fini n ⇒ f(n+1)=(n+1)·f(n)) ).

────────────────────────────────────────────────────────────────────────────────
⚠️ HISTORIQUE — CE QUI SUIT ((O1) et (O3)) EST PÉRIMÉ.  Mesuré le 26 juil. 2026 :
les deux « verrous » sont MORTS, et le mot « non modifiable » était la consigne d'une
SESSION ANTÉRIEURE (seuls le noyau `i_2_theoremes/noyau` et `subst` sont intouchables).
Le texte est conservé — expurgé de ses conclusions fausses — parce qu'il documente le
RAISONNEMENT qui a semblé juste pendant des semaines ; le verdict courant est en tête
des fonctions, pas ici.  (O2), lui, reste VRAI et utile.

  ✗ (O1) RÉFUTÉ le 25 juil. — l'assemblage essais→f EXISTE :
        `ensembles_factorielle_fonction.factorielle_fonction_existe` (3 hyps, 12,6 s)
        et `…factorielle_equation_restriction` (4 hyps, la forme du LIVRE).  Puis
        `ensembles_factorielle_zero.factorielle_zero` (0!=1) et
        `ensembles_factorielle_succ.factorielle_succ_fallback` ((n+1)!), joints par
        `ensembles_factorielle_existence_vrai.factorielle_caracterisation` (10 hyps).
  ✗ (O3) RÉFUTÉ le 24 juil. — ce n'était PAS une capture mais un renommage GRATUIT de
        `subst` (liant homonyme renommé sans que la variable substituée soit libre
        dessous) ; le court-circuit CS l'a supprimé.  `diagnostiquer_capture()` → {}.
  ✓ (O2) TOUJOURS VRAI et load-bearing : la forme C63-itération ne peut pas exprimer
        une récurrence INDEX-DÉPENDANTE ; c'est bien C62 qu'il faut.

────────────────────────────────────────────────────────────────────────────────
LE RAISONNEMENT D'ÉPOQUE (conservé pour mémoire — conclusions barrées ci-dessus).

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

CONCLUSION D'ÉPOQUE (RÉFUTÉE, cf. l'encadré en tête) : « (O1) est l'obstruction
IRRÉDUCTIBLE ».  Elle ne l'était pas : la fonction assemblée existe depuis le 25 juil.
Leçon transférable : « aucun théorème déposé ne produit X » ne se conclut pas d'un grep
— on avait greppé « f de ℕ sur U », pas le CAPSTONE.

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
   index-dépendante z·f(z-1) via card(dom u) = z (résolution conceptuelle de O2 ;
   recâblée le 2 août 2026 : facteur Déf.2 + M(D u) réel, cf. docstring de la règle).

✅ CLOS MODULO 3 RÉSIDUS C62 — `factorielle_essais_existe` : 3 hypothèses honnêtes
   { bo(≤,E), essais_bien_formes(T_fac), rule_codomain(T_fac,V) }, non vacuous,
   mesuré 1,6 s le 26 juil.  Ce bloc a dit « ne PEUT PAS être obtenue … elle lève
   l'erreur de capture » : c'était faux dès le fix `subst` du 24 juil.

⚠️ `zcard` (liant du `cardinal` interne) est LOAD-BEARING pour tout RECOLLEMENT : deux
   valeurs différentes donnent des `essais_bien_formes` / `rule_codomain` /
   `essais_restriction` α-ÉQUIVALENTS mais PAS `==` (mesuré) — et le noyau n'identifie
   pas les α-variants, donc les théorèmes ne se JOIGNENT pas.  Le défaut "Zfac62" est un
   vestige défensif du verrou-τ mort ; le liant CANONIQUE de `cardinal` est "Z" et c'est
   lui qu'exige le raccord arithmétique (prop5).  Cf.
   `ensembles_factorielle_existence_vrai.factorielle_caracterisation`.

theorie=22, noyau INTACT, rien postulé.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import Terme, var, egal, et, ou, non, tau
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E

from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import successeur, ZERO, UN
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import cardinal, inf_egal_card
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_1_relations_ordre.iii_1_7_plus_grand_plus_petit.ensembles_terme_plus_grand import terme_plus_grand
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_produit.ensembles_arith_cardinale import (
    produit_cardinal_binaire,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_2_recursion_c62.ensembles_c62_recursion import c62_recursion_sur_N, c62_cible


def _t(t):
    return t if isinstance(t, Terme) else var(t)


# ════════════════════════════════════════════════════════════════════════════
#  La RÈGLE factorielle INDEX-AWARE (forme C62) — (O2) résolu côté C62.
# ════════════════════════════════════════════════════════════════════════════
# @livre Ch.III §5.8 Def.2 | E III.41 L.28-29 | PDF p.144
# @livre Ch.III §5.8 Rem.- | E III.41 L.30-32 | PDF p.144
def regle_factorielle(a=UN, yname="yfac62", zcard="Zfac62"):
    """La règle T_fac{u} de la FACTORIELLE en forme C62 (u = restriction f|[0,n[).

    Au point n, u=f|[0,n[ (le segment initial OUVERT [0,n[).  On pose :
        T_fac{u} := τy ( ( u=∅  et  y=a )                                  [n=0]
                          ou ( u≠∅ et y = (card(dom u)+1)·u(M(D u)) ) )    [n≥1]

    L'INDICE n est RÉCUPÉRÉ par card(dom u) : dom u = [0,n[ a pour cardinal n.  C'est ce
    qui rend la règle factorielle EXPRIMABLE en forme C62 (la forme C63-itération, S
    aveugle à n, ne le peut pas : obstruction O2).  a=1 (=UN) est la valeur initiale.

    ✅ RECÂBLÉE LE 2 AOÛT 2026 — les deux défauts documentés ici sont morts :
      • DÉCALAGE D'UN CRAN (mesuré le 26 juil.) : le facteur est `cardinal(Du)`, celui
        que demande la Déf.2 (n! = ∏_{i<n}(i+1) ⇒ f(z) = z·f(z-1), E III.41) — et NON
        `successeur(cardinal(Du))`, qui encodait f(z) = (z+1)!.
      • M(D u) RÉEL : prev = u( M(D u) ) avec M = `terme_plus_grand` (§III.1.7, le
        τ-terme de E III.46 note 2), ordre `inf_egal_card`, liants "m"/"x" — choisis
        HORS de {F,u,up,v,y,z} liés dans `inf_egal_card` (piège payé le 27 juil., cf.
        `ensembles_max_intervalle_iii5`).  L'ancien fallback prev = u(D u) est mort ;
        sur D u = [0,n-1], `max_intervalle_vaut_n_entier` donne M(D u) = n-1 et
        l'équation lit f(z) = z·f(z-1), la récursion du livre.
    Callable Terme→Terme OPAQUE consommable par C62."""
    va = _t(a)

    def T(u):
        vu = _t(u)
        Du = E.dom(vu)                                   # D(u) = [0,n[
        n_fac = cardinal(Du, z=zcard)                    # card(dom u) = n  (Déf.2)
        prev = E.valeur(vu, terme_plus_grand(inf_egal_card, Du, "m", "x"))  # u(M(D u)) = f(n-1)
        vy = var(yname)
        cas_zero = et(egal(vu, E.VIDE), egal(vy, va))                    # u=∅ et y=a
        cas_succ = et(non(egal(vu, E.VIDE)),
                      egal(vy, produit_cardinal_binaire(n_fac, prev)))   # u≠∅ et y=n·f(n-1)
        return tau(yname, ou(cas_zero, cas_succ))

    return T


# ════════════════════════════════════════════════════════════════════════════
#  🎯 EXISTENCE DES ESSAIS FACTORIELS — C62 instancié à la règle factorielle.
# ════════════════════════════════════════════════════════════════════════════
def factorielle_essais_existe(e="Enat", G="Gle", V="Vfac62"):
    """✅ EXISTENCE DES ESSAIS FACTORIELS (O3 LEVÉE par le fix subst du 2026-07-24).

    C62 (récursion transfinie sur (ℕ,≤)) instancié à la règle factorielle INDEX-AWARE
    `regle_factorielle()` :
        { est_bien_ordonne(≤,ℕ), essais_bien_formes(T_fac), rule_codomain(T_fac,V) }
          ⊢ (∀n)( n∈ℕ ⇒ (∃p)( est_essai(p, T_fac, ≤, ℕ, n) ) ).
    L'ancienne obstruction (O3) — « modus ponens : mineure ≠ antécédent » dans le gluing
    déposé — n'était PAS une capture réelle : c'était un renommage GRATUIT de la
    substitution (liant homonyme renommé sans que la variable substituée soit libre
    dessous), qui faisait α-diverger les deux chemins de construction.  Depuis le
    court-circuit CS de subst_t/subst_f (outil_formule.py), le build passe tel quel :
    3 hypothèses = les résidus C62 honnêtes ci-dessus, rien postulé, theorie == 22."""
    T = regle_factorielle()
    return c62_recursion_sur_N(T, e, G, V)


__all__ = ["regle_factorielle", "factorielle_essais_existe"]
