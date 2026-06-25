"""§II.3.8 — Déf. 11 : UNICITÉ de la section au niveau des VALEURS-IMAGES.

Module NEUF, voisin de `ensembles_theoreme1_b_section.py` et de la Prop. 8
(`section_implique_surjective_valeur`, dans `ensembles_retractions_props.py`).
Isolé ici car `ensembles_retractions_props.py` est déjà à 329 lignes ; on respecte
« un fichier = une responsabilité, ≤300 lignes » et « ≤10 entrées par dossier ».

Il fournit :

  • UNICITÉ de la section — forme VALEURS (`section_unique_par_image`)
      ⊢_{S section de F sur B, S' section de F sur B}
        (∀y)(y∈B ⇒ f(s(y)) = f(s'(y))).
      « Deux sections d'une même f coïncident au niveau de leurs valeurs-images. »
      Comme f∘s = Id_B et f∘s' = Id_B (Déf. 11), on a f(s(y)) = y = f(s'(y))
      pour tout y∈B ; d'où f(s(y)) = f(s'(y)).  C'est l'unicité « au niveau des
      valeurs-images », fidèle et capture-saine.

Conventions : f : A→B surjective, s,s' : B→A sections de f (inverses à droite).
On NE prouve PAS s=s' (égalité des graphes, qui exigerait le pont valeurs↔graphe
et f injective) : on livre la forme VALEURS-IMAGES, la seule inconditionnelle ici.

NB liant frais « t » (≠ « y », liant interne de valeur) : la forme par défaut
est_section(·,·,·) lie sur « y » et entre en collision de capture avec le τy de
valeur (s(y) serait capturé), rendant s(y) opaque ; on lie donc sur « t », ce qui
donne l'énoncé MATHÉMATIQUEMENT correct (∀t∈B) f(s(t))=t, structurellement
α-identique à la forme attendue.  Même motif que `theoreme1_b_section_valeur`.
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (var, egal, appartient,
                                       impl, pourtout, Terme)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import instancie
from bourbaki.logique.i_4_egalitaires.tactiques_abrege_egalite import (symetrie,
                               composer_egalites)


def _T(v):
    """Coercion nom→terme (accepte un Terme ou un nom de variable)."""
    return v if isinstance(v, Terme) else var(v)


def _eqsym(thm):
    """⊢ (a=b) ⟹ ⊢ (b=a)  (symétrie de l'égalité appliquée à une preuve)."""
    a, b = thm.conclusion.termes
    return N.modus_ponens(thm, symetrie(a, b))


# ── UNICITÉ de la section — forme VALEURS-IMAGES ──────────────────────────────
# @livre Ch.II §3.8 Rem.- | E II.19 L.6-11 | PDF p.70
def section_unique_par_image(s="S", sp="Sp", f="F", b="B"):
    """⊢_{S section de F sur B, S' section de F sur B}
        (∀y)(y∈B ⇒ f(s(y)) = f(s'(y))).   (Déf. 11, unicité au niveau des valeurs.)

    « Deux sections s, s' d'une même surjection f coïncident au niveau de leurs
    valeurs-images. »  Par Déf. 11, f∘s = Id_B et f∘s' = Id_B, c.-à-d., pour tout
    y∈B,  f(s(y)) = y  et  f(s'(y)) = y.  On en déduit, par transitivité,
        f(s(y)) = y = f(s'(y))  ⟹  f(s(y)) = f(s'(y)).
    INCONDITIONNEL hors des deux hypothèses « s, s' sections de f » (jamais
    postulées : ce sont les données de l'énoncé, gardées explicites).

    On NE prouve PAS s=s' (égalité des graphes) : cela exigerait f injective et le
    pont valeurs↔graphe.  La forme VALEURS-IMAGES f(s(y))=f(s'(y)) est la seule
    inconditionnelle, et c'est exactement l'unicité « au niveau des valeurs-images ».

    Hypothèses laissées explicites (jamais postulées) :
      • S section de F sur B     [est_section(S,F,B) : (∀t∈B) f(s(t))=t]
      • S' section de F sur B     [est_section(S',F,B) : (∀t∈B) f(s'(t))=t]

    NB liant frais « t » (≠ « y », liant interne de valeur ; cf. en-tête de module
    et `theoreme1_b_section_valeur`)."""
    vS, vSp, vF, vB, vy = _T(s), _T(sp), _T(f), _T(b), var("y")
    # est_section liées sur « t » (anti-capture du τy de valeur, cf. en-tête)
    hsec = N.assume(E.est_section(vS, vF, vB, y="t"))     # (∀t∈B) f(s(t))=t
    hsecp = N.assume(E.est_section(vSp, vF, vB, y="t"))   # (∀t∈B) f(s'(t))=t
    hyB = N.assume(appartient(vy, vB))                    # y∈B
    # f(s(y)) = y     [S section de F sur B, au point y∈B]
    inst = instancie(hsec, vy)                            # y∈B ⇒ f(s(y))=y
    fsy_y = N.modus_ponens(hyB, inst)                     # f(s(y)) = y
    # f(s'(y)) = y    [S' section de F sur B, au point y∈B]
    instp = instancie(hsecp, vy)                          # y∈B ⇒ f(s'(y))=y
    fspy_y = N.modus_ponens(hyB, instp)                   # f(s'(y)) = y
    # y = f(s'(y))    (symétrie)  puis  f(s(y)) = f(s'(y))  (transitivité)
    y_fspy = _eqsym(fspy_y)                               # y = f(s'(y))
    eq = composer_egalites(fsy_y, y_fspy)                 # f(s(y)) = f(s'(y))
    inner = N.loi_deduction(appartient(vy, vB), eq)       # y∈B ⇒ f(s(y))=f(s'(y))
    return N.generalisation("y", inner)                   # (∀y)(y∈B ⇒ f(s(y))=f(s'(y)))


def cible_section_unique_par_image(s="S", sp="Sp", f="F", b="B"):
    """Cible de section_unique_par_image (tests) :
       (∀y)(y∈B ⇒ f(s(y)) = f(s'(y))).

    NB binder τ frais « u » (≠ « y », variable du ∀ extérieur).  Les valeurs f(·)
    et s(·) sont des τ ; avec le liant par défaut « y », la variable liée du τ
    entrerait en collision de capture avec l'argument « y » (le τy capturerait le
    « y » de s(y)/f(...)), donnant un terme DÉGÉNÉRÉ.  Le noyau évite cette capture
    en α-renommant ses propres τ (en « @0 ») lors de l'instanciation au point y ;
    on reproduit ici la forme capture-saine via un liant frais « u ».  La cible est
    donc α-équivalente (alpha_egal) à la conclusion produite par le noyau — l'écart
    « u » vs « @0 » est un pur renommage de variable liée, sans portée sémantique."""
    vS, vSp, vF, vB, vy = _T(s), _T(sp), _T(f), _T(b), var("y")
    lhs = E.valeur(vF, E.valeur(vS, vy, b="u"), b="u")    # f(s(y))   (τ frais « u »)
    rhs = E.valeur(vF, E.valeur(vSp, vy, b="u"), b="u")   # f(s'(y))  (τ frais « u »)
    return pourtout("y", impl(appartient(vy, vB), egal(lhs, rhs)))


__all__ = ["section_unique_par_image", "cible_section_unique_par_image"]
