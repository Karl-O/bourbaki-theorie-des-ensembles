"""§II.3.8 — Théorème 1 b) : composition des SECTIONS (niveau VALEURS).

Module NEUF, jumeau dual de `theoreme1_a_retraction_valeur` (composition des
RÉTRACTIONS, dans `ensembles_retractions_props.py`).  Isolé ici car le fichier
`ensembles_retractions_props.py` atteignait la limite de 300 lignes ; on respecte
« un fichier = une responsabilité, ≤300 lignes » et « ≤10 entrées par dossier ».

Il fournit :

  • THÉORÈME 1 b) — composition des sections, au niveau des VALEURS
      (`theoreme1_b_section_valeur`)
      ⊢_{S section de F sur B, S' section de F' sur C, s'(z)∈B}
        (z∈C) ⇒ f'(f(s(s'(z)))) = z.
      « Si s, s' sont des sections associées à f et f', s∘s' est une section
      associée à f'' = f'∘f. »  C'est le DUAL EXACT de la composition des
      rétractions (a) : on inverse la composition gauche↔droite.

Conventions : f : A→B, f' : B→C, f'' = f'∘f ; s : B→A section de f, s' : C→B
section de f', s∘s' : C→A section de f''.  Forme DÉPLIÉE au niveau des valeurs
(g∘h)(t)=g(h(t)) ; la forme repliée via la τ-composée-de-composées reste REPORTÉE
(verrou τ-capture, cf. rapport).
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import var, egal, appartient, impl
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import instancie
from bourbaki.logique.i_4_egalitaires.tactiques_abrege_egalite import (composer_egalites,
                               congruence_terme)


def _T(v):
    """Coercion nom→terme (accepte un Terme ou un nom de variable)."""
    from bourbaki.logique.i_1_termes_relations.formule import Terme
    return v if isinstance(v, Terme) else var(v)


# ── THÉORÈME 1 b) — composition des sections (niveau VALEURS, forme matricielle) ─
# @livre Ch.II §3.8 Th.1 | E II.19 L.16-17 | PDF p.70
def theoreme1_b_section_valeur(s="S", sp="Sp", f="F", fp="Fp", b="B", c="C"):
    """⊢_{S section de F sur B, S' section de F' sur C, s'(z)∈B}
        (z∈C) ⇒ f'(f(s(s'(z)))) = z.   (Théorème 1 b, partie « s∘s' section de f'' ».)

    « Si s, s' sont des sections associées à f et f', s∘s' est une section associée
    à f'' = f'∘f. »  C'est le DUAL EXACT de `theoreme1_a_retraction_valeur`
    (composition des rétractions) : on inverse la composition gauche↔droite.

    Lue MATRICIELLEMENT au niveau des valeurs (encodage du projet, Déf. 11),
    « s∘s' est une section de f'∘f » signifie que, pour tout z∈C,
    (f'∘f)((s∘s')(z)) = z ; en dépliant les composées au niveau des valeurs
    (g∘h)(t)=g(h(t)), cela s'écrit  f'(f(s(s'(z)))) = z.  C'est exactement la
    démonstration de Bourbaki, duale du a) :
        f'(f(s(s'(z)))) = f'(s'(z)) = z.

    On livre ici cette FORME DÉPLIÉE (sans la τ-composée-de-composées, qui
    déclenche la capture de liant documentée dans composee_associee_droite_valeur).
    Le passage à la forme repliée (f'∘f)((s∘s')(z)) via composition_valeur_t en un
    point qui est lui-même une valeur τ est REPORTÉ (cf. rapport, verrou τ-capture).

    Hypothèses laissées explicites (jamais postulées) :
      • S section de F sur B      [est_section(S,F,B) : (∀t∈B) f(s(t))=t]
      • S' section de F' sur C     [est_section(S',F',C) : (∀t∈C) f'(s'(t))=t]
      • s'(z)∈B  (pour appliquer la section de f au point s'(z)).

    NB liant frais « t » (≠ « y », liant interne de valeur) : la forme par défaut
    est_section(·,·,·) lie sur « y » et entre en collision de capture avec le τy de
    valeur (s(y) y serait capturé), rendant s(t) opaque ; on lie donc sur « t », ce
    qui donne l'énoncé MATHÉMATIQUEMENT correct (∀t∈B) f(s(t))=t, structurellement
    α-identique à est_retraction (le dual a) lie déjà sur « x », sans collision)."""
    vS, vSp, vF, vFp, vB, vC = _T(s), _T(sp), _T(f), _T(fp), _T(b), _T(c)
    vz = var("z")
    spz = E.valeur(vSp, vz)                                # s'(z)
    s_spz = E.valeur(vS, spz)                              # s(s'(z))
    hzC = N.assume(appartient(vz, vC))                     # z∈C
    # (4) f(s(s'(z))) = s'(z)          [S section de F sur B, au point s'(z)∈B]
    hsecS = N.assume(E.est_section(vS, vF, vB, y="t"))    # (∀t∈B) f(s(t))=t
    inst_s = instancie(hsecS, spz)                        # s'(z)∈B ⇒ f(s(s'(z)))=s'(z)
    hspzB = N.assume(appartient(spz, vB))
    f_s_spz = N.modus_ponens(hspzB, inst_s)              # f(s(s'(z))) = s'(z)
    # (5) f'(s'(z)) = z                [S' section de F' sur C, au point z∈C]
    hsecSp = N.assume(E.est_section(vSp, vFp, vC, y="t")) # (∀t∈C) f'(s'(t))=t
    inst_sp = instancie(hsecSp, vz)                       # z∈C ⇒ f'(s'(z))=z
    fp_spz = N.modus_ponens(hzC, inst_sp)                # f'(s'(z)) = z
    #  f'(f(s(s'(z)))) = f'(s'(z))                        (congruence sous f'(·))
    f_s_spz_term = E.valeur(vF, s_spz)                   # f(s(s'(z)))
    fp_cong = N.modus_ponens(f_s_spz, congruence_terme(
        f_s_spz_term, spz, E.valeur(vFp, var("w")), "w")) # f'(f(s(s'(z)))) = f'(s'(z))
    #  f'(f(s(s'(z)))) = z                                + (5)
    fp_eq_z = composer_egalites(fp_cong, fp_spz)         # f'(f(s(s'(z)))) = z
    return N.loi_deduction(appartient(vz, vC), fp_eq_z)  # (z∈C) ⇒ f'(f(s(s'(z))))=z


def cible_theoreme1_b_section_valeur(s="S", sp="Sp", f="F", fp="Fp", c="C"):
    """Cible : (z∈C) ⇒ f'(f(s(s'(z)))) = z."""
    vS, vSp, vF, vFp, vC = _T(s), _T(sp), _T(f), _T(fp), _T(c)
    vz = var("z")
    spz = E.valeur(vSp, vz)
    lhs = E.valeur(vFp, E.valeur(vF, E.valeur(vS, spz)))
    return impl(appartient(vz, vC), egal(lhs, vz))


__all__ = ["theoreme1_b_section_valeur", "cible_theoreme1_b_section_valeur"]
