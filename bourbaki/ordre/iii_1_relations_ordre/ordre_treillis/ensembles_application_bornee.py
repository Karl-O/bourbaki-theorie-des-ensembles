"""§III.1 — Application majorée / minorée / bornée ; borne sup/inf d'une application.

Résumé §6 item 7 (E.R.28) : une application f : A → (E, G) (E ordonné par G) est
MAJORÉE si son image f⟨A⟩ est majorée dans E, etc. ; sa BORNE SUPÉRIEURE est la borne
supérieure de son image (« sup_{x∈A} f(x) »).  On spécialise les notions
d'ensemble (`majorant`, `minorant`, `borne_superieure`, `borne_inferieure`, E III.1.8-9)
à l'IMAGE img(F) = f⟨A⟩ de l'application (F son graphe) :

    est_application_majoree(G,F,E) := (∃m) majorant(G, img F, m, E)
    est_application_minoree(G,F,E) := (∃m) minorant(G, img F, m, E)
    est_application_bornee(G,F,E)  := majorée ET minorée
    borne_superieure_application(G,F,E,m) := borne_superieure(G, img F, m, E)

On certifie les liens élémentaires (tous CLOS) : une application qui admet une borne
supérieure est majorée ; bornée ⇒ majorée et minorée (et duals).  Rien postulé ;
theorie_ensembles INCHANGÉE (22 axiomes).
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import Terme, var, et, existe, impl
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    conjonction_elim_gauche, conjonction_elim_droite)
from bourbaki.ordre.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_relation import (
    majorant, minorant, borne_superieure, borne_inferieure)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# ═══════════════════════════════════════════════════════════════════════════════
#  DÉFINITIONS (Résumé §6 item 7 ; via l'image img F = f⟨A⟩)
# ═══════════════════════════════════════════════════════════════════════════════
# @livre Ch.R §6 Def.- | E.R.28 item 7 (application majorée) | PDF p.331
def est_application_majoree(g="G", f="F", e="E"):
    """« F (d'image dans (E,G)) est majorée » := (∃m) majorant(G, img F, m, E)."""
    return existe("m", majorant(_t(g), E.img(_t(f)), var("m"), _t(e)))


# @livre Ch.R §6 Def.- | E.R.28 item 7 (application minorée) | PDF p.331
def est_application_minoree(g="G", f="F", e="E"):
    """« F est minorée » := (∃m) minorant(G, img F, m, E)."""
    return existe("m", minorant(_t(g), E.img(_t(f)), var("m"), _t(e)))


# @livre Ch.R §6 Def.- | E.R.28 item 7 (application bornée) | PDF p.331
def est_application_bornee(g="G", f="F", e="E"):
    """« F est bornée » := F majorée ET F minorée."""
    return et(est_application_majoree(g, f, e), est_application_minoree(g, f, e))


# @livre Ch.R §6 Def.- | E.R.28 item 7 (borne sup d'une application) | PDF p.331
def borne_superieure_application(g="G", f="F", e="E", m="m"):
    """« m est la borne supérieure de F » := borne_superieure(G, img F, m, E)
       ( = sup_{x∈A} f(x) )."""
    return borne_superieure(_t(g), E.img(_t(f)), _t(m), _t(e))


# @livre Ch.R §6 Def.- | E.R.28 item 7 (borne inf d'une application) | PDF p.331
def borne_inferieure_application(g="G", f="F", e="E", m="m"):
    """« m est la borne inférieure de F » := borne_inferieure(G, img F, m, E)."""
    return borne_inferieure(_t(g), E.img(_t(f)), _t(m), _t(e))


# ═══════════════════════════════════════════════════════════════════════════════
#  THÉORÈMES ÉLÉMENTAIRES (tous CLOS)
# ═══════════════════════════════════════════════════════════════════════════════
# @livre Ch.R §6 Prop.- | E.R.28 item 7 (borne sup ⇒ majorée) | PDF p.331
def borne_sup_application_majoree(g="G", f="F", e="E", s="s"):
    """⊢ borne_superieure_application(G,F,E,s) ⇒ est_application_majoree(G,F,E).

    La borne supérieure est en particulier un majorant (1ᵉʳ conjoint de sa définition),
    donc l'image est majorée : ∃-introduction du témoin s."""
    vg, vf, ve, vs = _t(g), _t(f), _t(e), _t(s)
    imgF = E.img(vf)
    hbs = N.assume(borne_superieure(vg, imgF, vs, ve))
    maj = conjonction_elim_gauche(hbs)                         # majorant(G, img F, s, E)
    ex = N.modus_ponens(maj, N.s5(majorant(vg, imgF, var("m"), ve), vs, "m"))
    return N.loi_deduction(borne_superieure(vg, imgF, vs, ve), ex)


# @livre Ch.R §6 Prop.- | E.R.28 item 7 (borne inf ⇒ minorée) | PDF p.331
def borne_inf_application_minoree(g="G", f="F", e="E", s="s"):
    """⊢ borne_inferieure_application(G,F,E,s) ⇒ est_application_minoree(G,F,E)."""
    vg, vf, ve, vs = _t(g), _t(f), _t(e), _t(s)
    imgF = E.img(vf)
    hbi = N.assume(borne_inferieure(vg, imgF, vs, ve))
    minr = conjonction_elim_gauche(hbi)                        # minorant(G, img F, s, E)
    ex = N.modus_ponens(minr, N.s5(minorant(vg, imgF, var("m"), ve), vs, "m"))
    return N.loi_deduction(borne_inferieure(vg, imgF, vs, ve), ex)


# @livre Ch.R §6 Prop.- | E.R.28 item 7 (bornée ⇒ majorée) | PDF p.331
def application_bornee_majoree(g="G", f="F", e="E"):
    """⊢ est_application_bornee(G,F,E) ⇒ est_application_majoree(G,F,E)."""
    h = N.assume(est_application_bornee(g, f, e))
    return N.loi_deduction(est_application_bornee(g, f, e), conjonction_elim_gauche(h))


# @livre Ch.R §6 Prop.- | E.R.28 item 7 (bornée ⇒ minorée) | PDF p.331
def application_bornee_minoree(g="G", f="F", e="E"):
    """⊢ est_application_bornee(G,F,E) ⇒ est_application_minoree(G,F,E)."""
    h = N.assume(est_application_bornee(g, f, e))
    return N.loi_deduction(est_application_bornee(g, f, e), conjonction_elim_droite(h))


def cible_borne_sup_application_majoree(g="G", f="F", e="E", s="s"):
    return impl(borne_superieure_application(g, f, e, s), est_application_majoree(g, f, e))


def cible_borne_inf_application_minoree(g="G", f="F", e="E", s="s"):
    return impl(borne_inferieure_application(g, f, e, s), est_application_minoree(g, f, e))


def cible_application_bornee_majoree(g="G", f="F", e="E"):
    return impl(est_application_bornee(g, f, e), est_application_majoree(g, f, e))


def cible_application_bornee_minoree(g="G", f="F", e="E"):
    return impl(est_application_bornee(g, f, e), est_application_minoree(g, f, e))


__all__ = [
    "est_application_majoree", "est_application_minoree", "est_application_bornee",
    "borne_superieure_application", "borne_inferieure_application",
    "borne_sup_application_majoree", "borne_inf_application_minoree",
    "application_bornee_majoree", "application_bornee_minoree",
    "cible_borne_sup_application_majoree", "cible_borne_inf_application_minoree",
    "cible_application_bornee_majoree", "cible_application_bornee_minoree",
]
