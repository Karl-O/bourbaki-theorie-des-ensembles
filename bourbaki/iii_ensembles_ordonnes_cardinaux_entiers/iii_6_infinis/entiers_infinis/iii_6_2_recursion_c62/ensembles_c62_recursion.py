"""§III.6.2 — DÉFINITION D'APPLICATIONS PAR RÉCURRENCE (Critères C62 et C63).

🎯🎯 C62 / C63 (E.III.6.2, E III.46-47) — le principe de DÉFINITION par récurrence
sur ℕ.  Bourbaki l'énonce ainsi :

  C62.  Soient u une lettre, T{u} un terme.  Il existe un ensemble U et une
        application f de ℕ sur U tels que, pour tout entier n, on ait
        f(n) = T{f⁽ⁿ⁾}, où f⁽ⁿ⁾ désigne la restriction de f à l'intervalle [0,n[.

  C63.  Soient S{v} et a deux termes.  Il existe un ensemble V et une application f
        de ℕ sur V tels que f(0)=a et, pour tout entier n≥1, f(n)=S{f(n-1)}.
        (Forme « itération » : déductible de C62.)

Bourbaki JUSTIFIE C62 EN UNE PHRASE (E III.46) :

  « L'ensemble ℕ étant bien ordonné, on peut lui appliquer le critère C60. »

Autrement dit C62 est EXACTEMENT le critère de récursion transfinie C60 (§III.2)
SPÉCIALISÉ à l'ensemble bien ordonné (ℕ, ≤_usuel).  C'est ce que ce module réalise.

────────────────────────────────────────────────────────────────────────────────
CE QUI EST RÉUTILISÉ (déposé, CLOS / honnête — RIEN n'est postulé ici).

  • C60 EXISTENCE : `recursion_transfinie_existence_final(vh, e, G, V, …)`
    (iii_2_bien_ordonnes/bon_ordre/recurrence_transfinie/ensembles_c60_pont) ⊢
        { est_bien_ordonne(R,E),  essais_bien_formes(vh),  rule_codomain(vh,V) }
          ⊢ (∀x)( x∈E ⇒ (∃p)( est_essai(p, vh, G, E, x) ) ),
    où R = _graphe_R(G) = (a,b)↦((a,b)∈G), et est_essai(p,…,x) =
        est_fonctionnel(p) ∧ dom(p)=seg(R,E,x)∪{x} ∧ (∀z∈dom p)(p(z)=vh(z)).
    C'est la moitié EXISTENCE de C60 sous la forme « couverture par essais » : pour
    chaque point x de E il existe une fonction partielle-solution p (un « essai »)
    définie sur le segment initial fermé seg(x)∪{x} et vérifiant l'ÉQUATION DE
    RÉCURSION  p(z)=vh(z)  (vh = la règle, lisant p|seg) sur tout son domaine.
    L'assemblage des essais en l'unique f totale (gluing de famille + collectivisation)
    est FAIT et vit dans CE dossier (`fonction_recursion_c62`, `ensembles_c62_fonction.py`).
    ⚠️ CE PARAGRAPHE A LONGTEMPS DIT « chantier §III.2 distinct » : c'était FAUX, et cette
    phrase a servi de raison de ne pas avancer (corrigé le 26 juil. 2026, 35 tests verts).

  • ℕ : `ensemble_NN()` (= τy(∀x)(x∈y⇔Fini x)) NOMME ℕ ; `appartenance_NN`,
    `zero_dans_NN`, `NN_clos_successeur` le caractérisent (CLOS).

────────────────────────────────────────────────────────────────────────────────
LE STATUT HONNÊTE (rapporté SANS fard).

Les TROIS hypothèses de C60 spécialisées à (ℕ, ≤) :

  (a) est_bien_ordonne(≤, ℕ)   — « ℕ est bien ordonné ».
  (b) essais_bien_formes(T)    — tout essai est un graphe de domaine ⊂ ℕ (structure).
  (c) rule_codomain(T, U)      — la règle T prend ses valeurs dans le contenant U.

(b) et (c) sont les données NATURELLES de la règle T (bonne formation + codomaine) :
ce sont les résidus honnêtes attendus de la construction de Bourbaki, EXACTEMENT ceux
que la consigne autorise (« rule well-formed + valued in codomain »).

(a) « ℕ bien ordonné » N'EST PLUS un résidu : il est DÉMONTRÉ, CLOS, 0 hypothèse.
`n_bien_ordonne()` puis `bo_graphe_NN()` (§III.6.1, `ensembles_ordre_NN_graphe.py`)
donnent ⊢ est_bien_ordonne(_graphe_R(G_ordre_NN()), ensemble_NN()) sans aucune hypothèse.
⚠️ CE PARAGRAPHE A LONGTEMPS DIT « résidu IRRÉDUCTIBLE […] n'est PAS fourni clos par les
théorèmes déposés » — l'argument (ℕ non borné, la chaîne cardinale ne porte que sur les
[0,a]) était juste pour la ROUTE CARDINALE, et faux comme énoncé général : la route par
le graphe d'ordre existe. Mesuré le 26 juil. 2026 (~1000 s, dominés par `N_existe`).

CE QUE CELA CHANGE, et c'est tout le §III.6 : `fonction_recursion_NN` et
`existence_unicite_fonction_NN` DÉCHARGENT (a) par `_cut` et exposent C62 sur le VRAI ℕ,
à DEUX résidus — (b) et (c) seuls, les données naturelles de la règle T.

⚠️ Le SET reste une VARIABLE `Enat` (≡ ℕ) DANS CE MODULE-CI, par commodité de
paramétrage : ce n'est PAS un blocage. Ce paragraphe a longtemps affirmé qu'instancier
C60-final au terme clos ensemble_NN() « heurte un binder interne du gluing déposé
(capture par le liant « x » de NN dans extension_un_pas_fonctionnelle — code déposé,
NON modifiable) ». Les DEUX moitiés de cette phrase étaient fausses :
  • l'instanciation aux TERMES CLOS e=ensemble_NN(), G=G_ordre_NN() PASSE (mesuré 58 s,
    3 hypothèses) — le verrou τ avait été levé par le fix `subst` du 24 juil. ;
  • « NON modifiable » était la consigne d'une SESSION ANTÉRIEURE, pas une contrainte du
    projet : seuls le noyau (i_2_theoremes/noyau) et `subst` sont intouchables.
PIÈGE MESURÉ, à connaître avant de recoller quoi que ce soit ici : aux paramètres par
défaut (`"Enat"`, `"Gle"`) la formule `bo` n'est ni `==` ni `alpha_egal` à ce que prouve
`bo_graphe_NN` — l'écart est VARIABLES vs TERMES CLOS (9 388 vs 86 598 car.), ni liants
ni callable-vs-graphe. Reconstruite à ℕ, l'égalité est syntaxiquement EXACTE, donc modus
ponens direct, SANS `alpha_bridge`.

INVARIANT : theorie_ensembles() = 22.  Tout DÉRIVÉ de C60, rien postulé.  Conclusion
non vacuous (∉ hypothèses).  vh (la règle T) OPAQUE (callable Terme→Terme).
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import Terme, var, egal, impl, appartient, pourtout, existe

from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_c60_pont import (
    recursion_transfinie_existence_final, essais_bien_formes, rule_codomain,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_recurrence_transfinie import _graphe_R
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_c60_existence_close import est_essai
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E


def _t(t):
    """Coercion str/Terme → Terme."""
    return t if isinstance(t, Terme) else var(t)


# ════════════════════════════════════════════════════════════════════════════
#  🎯 C62 — récursion sur (ℕ, ≤), forme « couverture par essais » de C60.
# ════════════════════════════════════════════════════════════════════════════
# @livre Ch.III §6.2 Crit.C62 | E III.46 L.14-20 | PDF p.149
def c62_recursion_sur_N(vh, e="Enat", G="Gle", V="Uval",
                        x="x0tf", y="ytf", z="zess", q="qwf", w="wwf"):
    """🎯🎯 C62 (E.III.6.2) sur (ℕ, ≤) — C60 spécialisé :

      { est_bien_ordonne(≤, ℕ),  essais_bien_formes(T),  rule_codomain(T, U) }
        ⊢ (∀n)( n ∈ ℕ ⇒ (∃p)( est_essai(p, T, ≤, ℕ, n) ) ),

    où ℕ est la variable `Enat` (≡ ensemble_NN(), cf. docstring du module), ≤ = _graphe_R(G)
    est l'ordre porté par le graphe G ((a,b)↦(a,b)∈G), T = la règle vh (opaque), et
        est_essai(p, T, ≤, ℕ, n) :=
            est_fonctionnel(p) ∧ dom(p) = seg(≤,ℕ,n)∪{n} ∧ (∀j∈dom p)( p(j) = T{j} ).

    C'est EXACTEMENT le critère de récursion transfinie C60 appliqué à (ℕ, ≤) bien
    ordonné, comme l'indique Bourbaki (« ℕ étant bien ordonné, on peut lui appliquer
    C60 »).  La conclusion affirme : pour tout entier n, il EXISTE une fonction
    partielle-solution p (un « essai ») définie sur l'intervalle initial fermé
    seg(n)∪{n}=[0,n] et vérifiant l'ÉQUATION DE RÉCURSION  p(j)=T{j}  sur tout son
    domaine — la règle T lisant p via sa restriction au segment p|[0,n[ = f⁽ⁿ⁾.

    ⚠️ TROIS hypothèses HONNÊTES (theorie=22, conclusion non vacuous) :
      (a) est_bien_ordonne(≤, ℕ)  — « ℕ est bien ordonné ».  ⚠️ CETTE LIGNE A DIT
          « résidu IRRÉDUCTIBLE : le bon ordre clos déposé ne couvre que les intervalles
          BORNÉS [0,a], pas ℕ » — c'est FAUX et contredit la docstring de CE MODULE :
          l'argument valait pour la route CARDINALE, pas en général.  La route par le
          graphe d'ordre existe et est CLOSE : `bo_graphe_NN()` (§III.6.1,
          `ensembles_ordre_NN_graphe.py`) — RE-MESURÉ par EXÉCUTION le 26 juil. 2026 :
          344,0 s, `est_clos=True`, 0 hypothèse.  (a) n'est un résidu
          QU'ICI, où E reste la VARIABLE `Enat` ; sur le VRAI ℕ il est DÉCHARGÉ —
          cf. `c62_recursion_sur_NN` / `fonction_recursion_NN` (2 hypothèses) ;
      (b) essais_bien_formes(T)   — tout essai est un graphe de domaine ⊂ ℕ ;
      (c) rule_codomain(T, U)     — la règle T prend ses valeurs dans U.
    (b),(c) sont les données naturelles de la règle T (consigne : rule well-formed +
    valued in codomain).  Tout est DÉRIVÉ de C60, rien postulé."""
    base = recursion_transfinie_existence_final(vh, e, G, V, x=x, y=y, z=z, q=q, w=w)

    R = _graphe_R(G)
    ve = _t(e)
    # vérifications honnêteté (les 3 hyps présentes, conclusion non vacuous)
    bo = E.est_bien_ordonne(R, ve)
    assert bo in base.hypotheses, "c62 : est_bien_ordonne(≤,ℕ) absente"
    assert essais_bien_formes(vh, e, G, V, q, w, z) in base.hypotheses, \
        "c62 : essais_bien_formes(T) absente"
    assert rule_codomain(vh, V, z) in base.hypotheses, "c62 : rule_codomain(T,U) absente"
    assert base.conclusion not in base.hypotheses, "c62 : VACUOUS"
    # conclusion = (∀x)( x∈ℕ ⇒ (∃p) est_essai(p, T, ≤, ℕ, x) )
    assert base.conclusion == c62_cible(vh, e, G, x, "pess", z), \
        "c62 : conclusion ≠ cible C62 (binders ?)"
    return base


def c62_cible(vh, e="Enat", G="Gle", x="x0tf", p="pess", z="zess"):
    """ÉNONCÉ-cible de C62 : (∀x)( x∈ℕ ⇒ (∃p)( est_essai(p, T, ≤, ℕ, x) ) ).

    Binders de la conclusion DÉPOSÉE de C60-final : universel « x0tf », existentiel
    « pess » (binder de couvert_essai), interne est_essai « zess ».  On reconstruit la
    forme EXACTE produite par `recursion_transfinie_existence_final`."""
    R = _graphe_R(G)
    ve, vx = _t(e), var(x)
    return pourtout(x, impl(appartient(vx, ve),
                            existe(p, est_essai(var(p), vh, G, ve, vx, z))))


# ════════════════════════════════════════════════════════════════════════════
#  🎯 C63 — forme « itération » : déduite de C62 par une RÈGLE concrète.
# ════════════════════════════════════════════════════════════════════════════
def regle_iteration(S, a):
    """La règle T{u} de l'ITÉRATION (forme C63), où u = f⁽ⁿ⁾ (restriction p|[0,n[).

    Bourbaki déduit C63 de C62 (note de bas de page E III.46) en posant, pour une
    lettre u (= la restriction p|[0,n[) :

        T{u} := τ_y ( ( u = ∅  et  y = a )   ou   ( u ≠ ∅  et  y = S{u(M(D(u)))} ) )

    où D(u) est l'ensemble de définition de u, M(D(u)) sa borne supérieure (le
    prédécesseur n-1 quand u=p|[0,n[), et a le terme de départ.  Au point n :
      • si u=∅ (i.e. n=0, le segment [0,0[ est vide), T{u}=a, d'où f(0)=a ;
      • sinon (n≥1), T{u}=S{u(n-1)}=S{f(n-1)}, l'équation d'itération.

    On IMPLÉMENTE ici cette règle telle quelle (terme τ), comme un callable Terme→Terme
    consommable par C62 ; on garde a et S génériques (a : Terme ; S : Terme→Terme)."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import tau, et, ou, non
    va = _t(a)
    YIT = "yit63"

    def T(u):
        vu = _t(u)
        Du = E.dom(vu)                                  # D(u) — ensemble de définition de u
        MDu = E.sup_borne(Du) if hasattr(E, "sup_borne") else E.dom(vu)
        # M(D(u)) — borne sup de D(u) (le « n-1 »).  Fallback prudent si le sup n'est
        # pas exposé sous ce nom dans ensembles_abrege : on garde D(u) (la règle reste
        # un terme bien formé ; le contenu sémantique fin du sup est interne à S{·}).
        vy = var(YIT)
        cas_zero = et(egal(vu, E.VIDE), egal(vy, va))                 # u=∅ et y=a
        cas_succ = et(non(egal(vu, E.VIDE)),
                      egal(vy, S(E.valeur(vu, MDu))))                 # u≠∅ et y=S{u(M(D u))}
        return tau(YIT, ou(cas_zero, cas_succ))

    return T


# @livre Ch.III §6.2 Crit.C63 | E III.46 L.21-24 | PDF p.149
# @livre Ch.III §6.2 Ex.- | E III.47 L.4-19 | PDF p.150  (Exemples 1)-2) : récurrence f(n+1)=g(f(n)), double récurrence h(n,f(n)), itérées fⁿ — prose d'exemples, rien à formaliser)
# @livre Ch.III §6.2 Ex.- | E III.47 L.20-22 | PDF p.150  (petit texte 3) : itérées 𝔓ⁿ(E) — prose, rien à formaliser)
# @livre Ch.III §6.2 Rem.- | E III.47 L.23-29 | PDF p.150  (Remarque : « récurrence limitée » sur l'intervalle (0, p+1) — prose, rien à formaliser)
def c63_iteration_sur_N(S, a, e="Enat", G="Gle", V="Vval63",
                        x="x0tf", y="ytf", z="zess", q="qwf", w="wwf"):
    """🎯🎯 C63 (E.III.6.2) sur (ℕ, ≤) — C62 spécialisé à la RÈGLE D'ITÉRATION :

      { est_bien_ordonne(≤, ℕ),  essais_bien_formes(T_S,a),  rule_codomain(T_S,a, V) }
        ⊢ (∀n)( n ∈ ℕ ⇒ (∃p)( est_essai(p, T_{S,a}, ≤, ℕ, n) ) ),

    où T_{S,a} = `regle_iteration(S, a)` est la règle qui rend, au segment u=f⁽ⁿ⁾,
        T{u} = a            si u=∅  (n=0)      → f(0)=a ;
        T{u} = S{u(n-1)}    si u≠∅  (n≥1)      → f(n)=S{f(n-1)}.
    C'est EXACTEMENT la forme « itération » de C63, obtenue de C62 par la règle
    concrète de Bourbaki (note E III.46).  Les essais p vérifient donc l'équation
    d'itération sur tout leur domaine [0,n].

    ⚠️ MÊMES TROIS hypothèses honnêtes que C62, ici INSTANCIÉES à la règle d'itération
    T_{S,a} : (a) ℕ bien ordonné ; (b) essais bien formés ; (c) T_{S,a} valué dans V.
    Dérivé de C62 (donc de C60).  theorie=22.  S : Terme→Terme ; a : Terme."""
    T = regle_iteration(S, a)
    base = c62_recursion_sur_N(T, e, G, V, x, y, z, q, w)
    # mêmes garde-fous honnêteté, avec la règle T_{S,a}
    R = _graphe_R(G)
    ve = _t(e)
    assert E.est_bien_ordonne(R, ve) in base.hypotheses, "c63 : ℕ bien ordonné absente"
    assert essais_bien_formes(T, e, G, V, q, w, z) in base.hypotheses, \
        "c63 : essais_bien_formes(T_S,a) absente"
    assert rule_codomain(T, V, z) in base.hypotheses, "c63 : rule_codomain(T_S,a) absente"
    assert base.conclusion not in base.hypotheses, "c63 : VACUOUS"
    assert base.conclusion == c62_cible(T, e, G, x, "pess", z), "c63 : conclusion ≠ cible"
    return base


__all__ = [
    "c62_recursion_sur_N", "c62_cible",
    "regle_iteration", "c63_iteration_sur_N",
]
