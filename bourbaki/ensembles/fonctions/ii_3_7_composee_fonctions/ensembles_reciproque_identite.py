"""§II.3.7 (suite Prop. 7) — identité de COMPOSITION F⁻¹∘F = Id_A au niveau VALEURS.

Énoncé formalisé
----------------
    {est_retraction(F⁻¹,F,A), F⁻¹∘F fonctionnel, x∈dom F, f(x)∈dom F⁻¹}
        ⊢ (x ∈ A) ⇒ (F⁻¹∘F)(x) = x

c.-à-d. la composée F⁻¹∘F, restreinte à ses valeurs, coïncide avec l'identité Id_A
sur A — lorsque F⁻¹ est une RÉTRACTION de F (hypothèse honnête est_retraction).

Valeur ajoutée vs. l'hypothèse (garde anti-tautologie)
-----------------------------------------------------
La clause de rétraction est_retraction(F⁻¹,F,A) est, par définition (E.II.48, Déf. 11),
    (∀x)(x∈A ⇒ valeur(F⁻¹, valeur(F,x)) = x),
soit l'identité des VALEURS IMBRIQUÉES f⁻¹(f(x))=x. Le présent théorème conclut sur la
forme COMPOSÉE
    valeur(composee(F⁻¹,F), x) = x,
terme STRICTEMENT DIFFÉRENT : (F⁻¹∘F)(x) lit la composée comme un seul graphe appliqué
à x, là où la rétraction emboîte deux applications. Le pont entre les deux est fourni
par composition_valeur ((g∘f)(x)=g(f(x))). La conclusion n'est donc α-égale à AUCUNE
hypothèse (cf. test test_reciproque_identite, assertion anti-tautologie explicite) :
ce n'est pas un P⇒P, mais l'identification de la définition matricielle de ∘ à Id_A.

Mise en place (LCF, réutilisation pure)
---------------------------------------
On réinstancie retraction_compose_valeur (§II.3.8) avec r := reciproque(F). La signature
de retraction_compose_valeur n'accepte que des NOMS (elle applique var() à ses arguments,
ce qui double-emballerait un terme reciproque(F)) ; on recopie donc sa preuve à
l'identique mais en acceptant des TERMES via _t — aucune primitive n'est ajoutée, toutes
les étapes restent celles du noyau (composition_valeur_t, assume, modus_ponens,
loi_deduction, instancie, composer_egalites).

Volet dual f∘f⁻¹ = Id_B (section)
---------------------------------
REPORTÉ : aucune version « section_compose_valeur » n'existe encore dans
ii_3_8_retractions_sections (grep négatif). Le volet section sera traité quand cet outil
dual sera disponible ; il n'est pas forcé ici.
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import var, appartient, egal, impl, Terme
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import instancie
from bourbaki.logique.i_4_egalitaires.tactiques_abrege_egalite import composer_egalites
from bourbaki.ensembles.fonctions.ii_3_8_retractions_sections.ensembles_composee_valeurs import (
    composition_valeur_t,
)


def _t(v):
    """Accepte un TERME tel quel, ou en construit un depuis un nom (lettre)."""
    return v if isinstance(v, Terme) else var(v)


def cible_reciproque_compose_identite_valeur(f="F", a="A", x="x"):
    """Énoncé visé : (x ∈ A) ⇒ (F⁻¹∘F)(x) = x   — forme COMPOSÉE (≠ clause de rétraction)."""
    vF, vA, vx = _t(f), _t(a), _t(x)
    rof = E.valeur(E.composee(E.reciproque(vF), vF), vx)     # (F⁻¹∘F)(x)
    return impl(appartient(vx, vA), egal(rof, vx))


# @livre Ch.II §3.7 Prop.7 | E II.17 L.32-33 | PDF p.68
def reciproque_compose_identite_valeur(f="F", a="A", x="x"):
    """{F⁻¹ rétraction de F sur A, F⁻¹∘F fonctionnel, x∈domF, f(x)∈domF⁻¹}
        ⊢ (x ∈ A) ⇒ (F⁻¹∘F)(x) = x.

    Réinstanciation de retraction_compose_valeur (§II.3.8) avec r := reciproque(F).
    Chaîne : (F⁻¹∘F)(x) = F⁻¹(F(x))   (composition_valeur_t)
             F⁻¹(F(x))   = x          (est_retraction(F⁻¹,F,A) sous x∈A)
             ───────────────────────
             (F⁻¹∘F)(x)  = x          (sous garde x∈A)."""
    vF, vA, vx = _t(f), _t(a), _t(x)
    vR = E.reciproque(vF)                                    # r := F⁻¹
    cv = composition_valeur_t(vR, vF, vx)                    # (F⁻¹∘F)(x) = F⁻¹(F(x))
    hret = N.assume(E.est_retraction(vR, vF, vA))            # (∀x)(x∈A ⇒ F⁻¹(F(x))=x)
    inst = instancie(hret, vx)                               # x∈A ⇒ F⁻¹(F(x))=x
    hxa = N.assume(appartient(vx, vA))                       # x∈A
    eq_rfx_x = N.modus_ponens(hxa, inst)                     # {ret, x∈A} ⊢ F⁻¹(F(x))=x
    chained = composer_egalites(cv, eq_rfx_x)                # (F⁻¹∘F)(x) = x
    return N.loi_deduction(appartient(vx, vA), chained)      # (x∈A) ⇒ (F⁻¹∘F)(x)=x


__all__ = [
    "cible_reciproque_compose_identite_valeur",
    "reciproque_compose_identite_valeur",
]
