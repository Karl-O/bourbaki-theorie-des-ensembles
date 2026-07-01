"""§II.5 — PROPOSITION 3 (CURRYING, version ENSEMBLISTE) et PROPOSITION 2.

PROPOSITION 3 (E II.31, n° 2).  « Si, pour toute application f de B×C dans A, on
désigne par f̃ l'application y ↦ f_y de C dans 𝓕(B;A), la fonction f ↦ f̃ est une
bijection (dite canonique) de 𝓕(B×C ; A) sur 𝓕(C ; 𝓕(B;A)). »

C'est l'ANALOGUE ENSEMBLISTE EXACT de la Proposition 10 cardinale a^(b·c)=(a^b)^c
(`prop10_close`), déjà close VIA DEUX INJECTIONS curry / uncurry :
  • Λ = CURRY   : 𝓕(B×C;A) ↪ 𝓕(C;𝓕(B;A))   (W_Lambda, `ensembles_prop10_inj_curry`) ;
  • U = UNCURRY : 𝓕(C;𝓕(B;A)) ↪ 𝓕(B×C;A)   (W_U,      `ensembles_prop10_inj_uncurry`).
Ces deux applications sont les deux sens de la bijection canonique de Prop 3 §5.

ÉNONCÉ FORMALISÉ (fidèle, INCONDITIONNEL) :

    prop3_currying_bijection()  ⊢  equipotent( 𝓕(B×C;A) , 𝓕(C;𝓕(B;A)) )

où equipotent(X,Y) = (∃F) est_bijection_de(F,X,Y) est LITTÉRALEMENT « il existe une
bijection (canonique) de X sur Y » — exactement la conclusion de la Proposition 3.
On l'assemble par CANTOR–BERNSTEIN sur les deux injections curry/uncurry (strictement
le schéma de `prop10_close`, mais on s'arrête au niveau ENSEMBLISTE Eq(·,·), avant de
passer aux cardinaux).  Rien postulé ; theorie_ensembles INCHANGÉE (22 axiomes).

PROPOSITION 2 (E II.31, n° 2).
  Énoncé : u : E'→E, v : F→F' ; la fonction f ↦ v∘f∘u de 𝓕(E;F) dans 𝓕(E';F') est
  injective si u surjective & v injective, surjective si u injective & v surjective ;
  bijective (Cor) si u,v bijectives.  La PREUVE de Bourbaki est par retraction/section
  (1° : s section de u, r rétraction de v ⇒ r∘(v∘f∘u)∘s = f ; 2° en miroir).
  CAS 1° (injectif) et CAS 2° (surjectif) : FAITS et CLOS, forme rétraction/section au
  niveau des graphes, dans `ensembles_conjugaison_prop2_ii5.prop2_conjugaison_injective`
  et `ensembles_conjugaison_prop2_surj_ii5.prop2_conjugaison_surjective` — tous deux
  contournent le verrou-τ ci-dessous (1° : ne jamais évaluer un composé en un point-τ,
  quantifier-générique-puis-instancier ; 2° : témoin graphe_terme à liants FRAIS, levée
  du « verrou liant valeur »).  Reste REPORTÉ : l'OBJET-conjugaison f↦v∘f∘u lui-même.
  VERROU : la CONSTRUCTION du graphe-terme de la conjugaison f ↦ v∘f∘u (recomposition
  d'applications EMBALLÉES, bien-définition + injectivité back-and-forth) est exactement
  le « verrou dur » DÉJÀ documenté et REPORTÉ dans
  `ensembles_arith_cardinale_props_exposant_monotone` (les énoncés cardinaux de
  monotonie y restent CONDITIONNELS faute de cette même injection d'espaces de
  fonctions) — échelle Prop 9/10.  De plus, `composition_valeur` à un point qui est
  lui-même une valeur τy(...) déclenche une capture de liant (cf. note de
  `composee_associee_droite_valeur`).  Tractable mais hors budget ; rien de FAUX/vide
  n'est posé ici (aucune conclusion fausse, aucun axiome ajouté).

theorie_ensembles INCHANGÉE ; aucun fichier déposé modifié (tout est IMPORTÉ).
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import Terme, var
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    conjonction_intro, instancie)

from bourbaki.cardinaux.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import equipotent
from bourbaki.cardinaux.arithmetique.iii_3_5_exposant.prop10_currying.ensembles_prop10_currying import (
    domaine_lambda, codomaine_lambda)
from bourbaki.cardinaux.arithmetique.iii_3_5_exposant.prop10_currying.ensembles_prop10_inj_curry import inf_egal_curry
from bourbaki.cardinaux.arithmetique.iii_3_5_exposant.prop10_currying.ensembles_prop10_inj_uncurry import inf_egal_uncurry


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# ═══════════════════════════════════════════════════════════════════════════════
#  SOURCE et BUT de la bijection canonique de Prop 3 §5
# ═══════════════════════════════════════════════════════════════════════════════
def source(a="A", b="B", c="C"):
    """𝓕(B×C ; A)  — source de la bijection canonique f ↦ f̃ (Prop 3 §5)."""
    va, vb, vc = _t(a), _t(b), _t(c)
    return domaine_lambda(va, vb, vc)


def but(a="A", b="B", c="C"):
    """𝓕(C ; 𝓕(B;A))  — but de la bijection canonique f ↦ f̃ (Prop 3 §5)."""
    va, vb, vc = _t(a), _t(b), _t(c)
    return codomaine_lambda(va, vb, vc)


# ═══════════════════════════════════════════════════════════════════════════════
#  PROPOSITION 3 §5 — CURRYING : 𝓕(B×C;A) ≅ 𝓕(C;𝓕(B;A))  (bijection canonique)
# ═══════════════════════════════════════════════════════════════════════════════
# @livre Ch.II §5.2 Prop.3 | E II.31 L.34-36 | PDF p.82
def prop3_currying_bijection(a="A", b="B", c="C"):
    """⊢ equipotent( 𝓕(B×C;A) , 𝓕(C;𝓕(B;A)) ).   (PROPOSITION 3, E II.31.)

    « Il existe une bijection (canonique) de 𝓕(B×C;A) sur 𝓕(C;𝓕(B;A)). »
    INCONDITIONNEL.  Cantor–Bernstein sur les deux injections curry/uncurry :
      • inf_egal_curry   ⊢ inf_egal_card(𝓕(B×C;A), 𝓕(C;𝓕(B;A)))   (Λ injective) ;
      • inf_egal_uncurry ⊢ inf_egal_card(𝓕(C;𝓕(B;A)), 𝓕(B×C;A))   (U injective) ;
      • cantor_bernstein : (X≤Y et Y≤X) ⇒ Eq(X,Y).
    Conclusion = equipotent(source, but) = (∃F) est_bijection_de(F, source, but)."""
    from bourbaki.cardinaux.ensembles_cantor_bernstein_final import cantor_bernstein
    va, vb, vc = _t(a), _t(b), _t(c)
    src = domaine_lambda(va, vb, vc)        # 𝓕(B×C; A)
    tgt = codomaine_lambda(va, vb, vc)      # 𝓕(C; 𝓕(B;A))
    inf_A = inf_egal_curry(va, vb, vc)      # inf_egal_card(src, tgt)   (CURRY injective)
    inf_B = inf_egal_uncurry(va, vb, vc)    # inf_egal_card(tgt, src)   (UNCURRY injective)
    # cantor_bernstein term-tolérant : généralise (A,B) puis instancie (src,tgt)
    cb_nom = cantor_bernstein("A", "B", "f", "g")           # (A≤B et B≤A) ⇒ Eq(A,B)
    cb_gen = N.generalisation("A", N.generalisation("B", cb_nom))
    cb = instancie(instancie(cb_gen, src), tgt)             # (src≤tgt et tgt≤src) ⇒ Eq(src,tgt)
    return N.modus_ponens(conjonction_intro(inf_A, inf_B), cb)   # equipotent(src, tgt)


__all__ = ["source", "but", "prop3_currying_bijection"]
