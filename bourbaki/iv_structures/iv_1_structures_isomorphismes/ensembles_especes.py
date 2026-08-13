"""§IV.1.4–IV.1.5 — Espèces de structure, structures, isomorphismes, transport,
automorphismes.   REPRÉSENTATIONNEL.

⚠️ MÉTAMATHÉMATIQUE.  Une espèce de structure Σ (IV.1.4) est un TEXTE (lettres de
base + ensembles auxiliaires + une typification T + un axiome R transportable) ;
la « théorie de l'espèce » est une théorie au sens méta.  On en donne ici une
REPRÉSENTATION FIDÈLE au niveau objet, le tout SANS toucher theorie_ensembles()
(reste à 22 axiomes) :

  • `Espece` (dataclass) porte les données d'un Σ : nombre n de bases principales,
    auxiliaires A₁,…,A_m, le schéma S de la caractérisation typique, et l'axiome R
    (PRÉDICAT abstrait R(bases, s) -> Formule, transportable — IV.1.3) ;
  • `caracterisation_typique(Σ, bases, s)` = la Formule T{E,s} : s ∈ S(E₁,…,Eₙ,A₁,…,A_m) ;
  • `est_structure_espece(Σ, bases, U)` = la Formule « T{E,U} et R{E,U} » : U est
    une structure d'espèce Σ sur E₁,…,Eₙ (IV.1.4) ;
  • `est_isomorphisme(Σ, f, bases, basesp, U, Up)` = la Formule (4) de IV.1.5 :
    (f₁ bij …) et … et ⟨f₁,…,fₙ,Id,…⟩^S(U) = U' ;
  • `structure_transportee(Σ, f, bases, U)` = le Terme U' = ⟨f₁,…,fₙ,Id,…⟩^S(U)
    (transport de structure, IV.1.5) ;
  • `sont_isomorphes`, `structures_isomorphes`, `est_automorphisme` — relations
    dérivées (IV.1.5) ;
  • `est_univalente` — REPRÉSENTATIONNEL (quantification méta sur toutes structures).

Les énoncés sont VERBATIM de IV.1.4–IV.1.5.  Aucun gros théorème n'est prouvé ici
(CST1–CST7 : reportés) ; un LEMME DIRECT `transport_donne_isomorphisme` est fourni
(la structure transportée fait de (f₁,…,fₙ) un isomorphisme PAR DÉFINITION — c'est
la clause (4) appliquée à U' := ⟨…⟩^S(U), prouvable au niveau objet)."""
from __future__ import annotations

from dataclasses import dataclass
from typing import Callable, Sequence, Tuple, Optional

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, egal, et, existe, appartient
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import est_bijection_de
from bourbaki.iv_structures.iv_1_structures_isomorphismes.ensembles_especes_echelon import (
    Schema, echelon, extension_canonique)
from bourbaki.iv_structures.iv_1_structures_isomorphismes.ensembles_especes_typification import _conj


# ─────────────────────────────────────────────────────────────────────────────
# §IV.1.4 — ESPÈCE DE STRUCTURE Σ (objet méta)
# ─────────────────────────────────────────────────────────────────────────────
# @livre Ch.IV §1.4 Def.- | E IV.4 L.2-17 | PDF p.207
@dataclass(frozen=True)
class Espece:
    """Espèce de structure Σ dans 𝒯 (IV.1.4) — REPRÉSENTATION.

    « Une espèce de structure dans 𝒯 est un texte Σ formé : 1° d'un certain nombre
    de lettres x₁,…,xₙ,s (x₁,…,xₙ : ensembles de base principaux) ; 2° de termes
    A₁,…,A_m (ensembles de base auxiliaires ; éventuellement aucun) ; 3° d'une
    typification T{x₁,…,xₙ,s} : s∈S(x₁,…,xₙ,A₁,…,A_m) où S est un schéma de
    construction d'échelon sur n+m termes (caractérisation typique de Σ) ; 4° d'une
    relation R{x₁,…,xₙ,s} transportable dans 𝒯 pour la typification T (axiome de
    l'espèce Σ). »

    Champs : `nom`, `n` = nb d'ensembles de base principaux, `auxiliaires` =
    [A₁,…,A_m] (Termes ; éventuellement vide), `schema` = S (Schema sur n+m termes),
    `axiome` = R, prédicat abstrait R(bases, s) -> Formule (transportable, IV.1.3)."""
    nom: str
    n: int
    auxiliaires: Tuple
    schema: Schema
    axiome: Callable

    @property
    def m(self) -> int:
        """Nombre m d'ensembles de base auxiliaires."""
        return len(self.auxiliaires)


# @livre Ch.IV §1.4 Def.- | E IV.4 L.11-14 | PDF p.207
def caracterisation_typique(sigma: Espece, bases: Sequence, s):
    """Caractérisation typique T{E₁,…,Eₙ, s} de Σ (IV.1.4, 3°).

    T{E,s} : s ∈ S(E₁,…,Eₙ, A₁,…,A_m), l'échelon S interprété sur les bases
    principales E suivies des auxiliaires A de Σ.  Renvoie la Formule d'appartenance."""
    socle = list(bases) + list(sigma.auxiliaires)
    return appartient(s, echelon(sigma.schema, socle))


# @livre Ch.IV §1.4 Def.- | E IV.4 L.22-27 | PDF p.207
def est_structure_espece(sigma: Espece, bases: Sequence, U):
    """« U est une structure d'espèce Σ sur les bases E₁,…,Eₙ » (IV.1.4).

    « On dit que U est une structure d'espèce Σ sur les ensembles de base principaux
    E₁,…,Eₙ … si la relation "T{E₁,…,Eₙ,U} et R{E₁,…,Eₙ,U}" est un théorème. »
    Renvoie la Formule « T{E,U} et R{E,U} »."""
    return et(caracterisation_typique(sigma, bases, U), sigma.axiome(list(bases), U))


# ── E IV.5 : exemples d'espèces de structures + remarques (prose du livre) ───
# @livre Ch.IV §1.4 Ex.1 | E IV.4 L.28-33 ; E IV.5 L.1-4 | PDF p.208
#   (Ex.1 : espèce de structure D'ORDRE sur A — formalisée au chap. III,
#    iii_1_relations_ordre ; ici seule la lecture « espèce » est nouvelle)
# @livre Ch.IV §1.4 Ex.2 | E IV.5 L.5-12 | PDF p.208
#   (Ex.2 : structures ALGÉBRIQUES, F ∈ 𝔓((A×A)×A) graphe fonctionnel de
#    domaine A×A = loi de composition — prose illustrative, hors Traité E)
# @livre Ch.IV §1.4 Ex.3 | E IV.5 L.13-20 | PDF p.208
#   (Ex.3 : espèce de structure TOPOLOGIQUE, V ∈ 𝔓(𝔓(A)), axiomes réunion/
#    intersection/A∈V — prose illustrative, renvoie à TG I §1)
# @livre Ch.IV §1.4 Ex.4 | E IV.5 L.21-29 | PDF p.208
#   (Ex.4 : espace VECTORIEL à gauche sur K, base auxiliaire K — prose, cf. A II §1)
# @livre Ch.IV §1.4 Ex.5 | E IV.5 L.30-34 | PDF p.208
#   (Ex.5 : variété analytique complexe, C terme sans lettre en base auxiliaire — prose)
# @livre Ch.IV §1.4 Rem.- | E IV.5 L.35-52 | PDF p.208
#   (Remarques 1-3 : échelon produit/multiplet ; axiome = conjonction de
#    relations transportables « les axiomes de Σ » ; espèce de structure
#    d'ensemble Σ₀ sans caractérisation ni axiome — prose)

# ─────────────────────────────────────────────────────────────────────────────
# §IV.1.5 — ISOMORPHISME, TRANSPORT, AUTOMORPHISME
# ─────────────────────────────────────────────────────────────────────────────
# @livre Ch.IV §1.5 Def.- | E IV.6 L.11-11 | PDF p.209
def structure_transportee(sigma: Espece, f_bij: Sequence, U):
    """Structure transportée U' = ⟨f₁,…,fₙ,Id₁,…,Id_m⟩^S(U) (IV.1.5, transport).

    « On dit que la structure U' (définie par la relation (4)) est obtenue en
    transportant la structure U aux ensembles E₁',…,Eₙ' au moyen des applications
    bijectives f₁,…,fₙ. »  Id_h = application identique de A_h sur lui-même =
    diagonale(A_h).  Renvoie le Terme-objet U'."""
    ids = [E.diagonale(A) for A in sigma.auxiliaires]
    ext = extension_canonique(sigma.schema, list(f_bij) + ids)
    return E.valeur(ext, U)


def _clauses_bijections(f_bij, bases, basesp):
    """Liste [f₁ bij de E₁ sur E₁', …, fₙ bij de Eₙ sur Eₙ'] (Formules)."""
    return [est_bijection_de(f, e, ep)
            for f, e, ep in zip(f_bij, bases, basesp)]


# @livre Ch.IV §1.5 Def.- | E IV.6 L.8-12 | PDF p.209
def est_isomorphisme(sigma: Espece, f_bij: Sequence, bases: Sequence,
                     basesp: Sequence, U, Up):
    """« (f₁,…,fₙ) est un isomorphisme de (E,U) sur (E',U') » (IV.1.5, relation (4)).

    « Soit f_i une bijection de E_i sur E_i' (1≤i≤n).  On dit que (f₁,…,fₙ) est un
    isomorphisme des ensembles E₁,…,Eₙ munis de U sur les ensembles E₁',…,Eₙ' munis
    de U' si l'on a (4) ⟨f₁,…,fₙ,Id₁,…,Id_m⟩^S(U) = U'. »

    Renvoie la Formule : (f₁ bij de E₁ sur E₁') et … et (fₙ bij …) et
    ⟨f₁,…,fₙ,Id,…⟩^S(U) = U'.  (On EXPLICITE l'hypothèse "f_i bijection", implicite
    dans la phrase de Bourbaki — un isomorphisme EST un système de bijections.)"""
    bij = _clauses_bijections(f_bij, bases, basesp)
    eq4 = egal(structure_transportee(sigma, f_bij, U), Up)          # (4)
    return _conj(bij + [eq4])


# @livre Ch.IV §1.5 Def.- | E IV.6 L.19-21 | PDF p.209
def sont_isomorphes(sigma: Espece, bases: Sequence, basesp: Sequence, U, Up,
                    noms_f: Optional[Sequence[str]] = None):
    """« (E',U') sont isomorphes à (E,U) » (IV.1.5).

    « On dit que E₁',…,Eₙ' munis de U' sont isomorphes à E₁,…,Eₙ munis de U s'il
    existe un isomorphisme de l'un sur l'autre ; on dit alors que les structures U
    et U' sont isomorphes. »  Renvoie la Formule (∃f₁)…(∃fₙ) est_isomorphisme(…)."""
    if noms_f is None:
        noms_f = [f"f{i+1}" for i in range(sigma.n)]
    f_vars = [var(nm) for nm in noms_f]
    corps = est_isomorphisme(sigma, f_vars, bases, basesp, U, Up)
    for nm in reversed(list(noms_f)):
        corps = existe(nm, corps)
    return corps


# « structures isomorphes » : synonyme (IV.1.5) de sont_isomorphes pour les U,U'.
# @livre Ch.IV §1.5 Def.- | E IV.6 L.19-21 | PDF p.209
def structures_isomorphes(sigma: Espece, bases, basesp, U, Up, noms_f=None):
    """« Les structures U et U' sont isomorphes » (IV.1.5) — synonyme de
    sont_isomorphes (existence d'un isomorphisme de l'un sur l'autre)."""
    return sont_isomorphes(sigma, bases, basesp, U, Up, noms_f)


# @livre Ch.IV §1.5 Def.- | E IV.6 L.28-29 | PDF p.209
def est_automorphisme(sigma: Espece, f_bij: Sequence, bases: Sequence, U):
    """« (f₁,…,fₙ) est un automorphisme de E₁,…,Eₙ » (IV.1.5).

    « On dit qu'un isomorphisme de E₁,…,Eₙ sur E₁,…,Eₙ (pour la même structure) est
    un automorphisme de E₁,…,Eₙ. »  Cas E=E', U=U' de est_isomorphisme."""
    return est_isomorphisme(sigma, f_bij, bases, bases, U, U)


# @livre Ch.IV §1.5 Def.- | E IV.7 L.11-12 | PDF p.210
def est_univalente(sigma: Espece):
    """Espèce de structure univalente (IV.1.5) — REPRÉSENTATIONNEL.

    « Il peut se faire que deux structures quelconques d'espèce Σ soient
    nécessairement isomorphes ; on dit alors que l'espèce de structure Σ est
    univalente. »  La propriété « DEUX STRUCTURES QUELCONQUES … nécessairement
    isomorphes » quantifie MÉTA sur toutes les structures (ensembles E, E' et
    structures U, U' arbitraires) ; elle n'est pas exprimable d'un trait par une
    formule du fragment objet.  On renvoie ici un MARQUEUR documenté (l'énoncé +
    le drapeau représentationnel) plutôt qu'une Formule — la propriété est
    REPORTÉE.  (Théorème de transport / unicité : CST5, reporté.)"""
    return {
        "espece": sigma.nom,
        "enonce": ("deux structures quelconques d'espèce Σ sont nécessairement "
                   "isomorphes (IV.1.5)"),
        "representationnel": True,
        "reporte": True,
    }


# ─────────────────────────────────────────────────────────────────────────────
# LEMME DIRECT (niveau objet) — la structure transportée EST témoin d'isomorphisme
# ─────────────────────────────────────────────────────────────────────────────
def transport_egalite(sigma: Espece, f_bij: Sequence, U):
    """⊢ ⟨f₁,…,fₙ,Id,…⟩^S(U) = U'  où U' := structure_transportee(Σ,f,U).

    Trivialité de réflexivité (T=T) : la structure transportée U' est, PAR
    DÉFINITION (IV.1.5, relation (4)), le terme ⟨f₁,…,fₙ,Id,…⟩^S(U).  Cette égalité
    est donc la clause (4) de l'isomorphisme, certifiée close par le noyau
    (réflexivité, Théorème 1).  C'est le cœur OBJET du critère CST5 (« le transport
    fait de (f₁,…,fₙ) un isomorphisme »), la partie « bijection » restant en
    hypothèse — cf. transport_donne_isomorphisme."""
    Ut = structure_transportee(sigma, f_bij, U)
    return N.reflexivite(Ut)                       # ⊢ U' = U'  (U' = ⟨…⟩^S(U))


def transport_donne_isomorphisme(sigma: Espece, f_bij: Sequence,
                                 bases: Sequence, basesp: Sequence, U):
    """⊢ (f₁ bij …) et … et (fₙ bij …) ⇒ est_isomorphisme(Σ, f, E, E', U, U')
    où U' := structure_transportee(Σ, f, U).   (IV.1.5 / cœur objet de CST5.)

    Énoncé : SI chaque f_i est une bijection de E_i sur E_i', ALORS (f₁,…,fₙ) est
    un isomorphisme de (E,U) sur (E',U'), U' étant la structure transportée.
    Démonstration : sous l'hypothèse H = « toutes les f_i sont des bijections », la
    conclusion est_isomorphisme = (mêmes clauses de bijection) et (clause (4)).  Les
    clauses de bijection sont H lui-même ; la clause (4) ⟨…⟩^S(U)=U' est la
    réflexivité (transport_egalite).  On recolle par conjonction sous H."""
    bij = _clauses_bijections(f_bij, bases, basesp)
    Up = structure_transportee(sigma, f_bij, U)
    hyp = _conj(bij)                               # H : toutes les bijections
    h = N.assume(hyp)                              # H ⊢ H
    # décompose H en ses conjoints (les clauses de bijection), dans l'ordre
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
        conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite)
    parts = []
    reste = h
    for k in range(len(bij)):
        if k < len(bij) - 1:
            parts.append(conjonction_elim_gauche(reste))   # conjoint gauche courant
            reste = conjonction_elim_droite(reste)         # queue
        else:
            parts.append(reste)                            # dernier conjoint
    eq4 = transport_egalite(sigma, f_bij, U)               # ⊢ ⟨…⟩^S(U)=U'
    # reconstruit la conjonction est_isomorphisme = bij₁ et … et bijₙ et (4)
    acc = parts[0]
    for p in parts[1:]:
        acc = conjonction_intro(acc, p)
    iso = conjonction_intro(acc, eq4)                      # sous H
    return N.loi_deduction(hyp, iso)                       # H ⇒ est_isomorphisme(…)


__all__ = [
    "Espece", "caracterisation_typique", "est_structure_espece",
    "structure_transportee", "est_isomorphisme", "sont_isomorphes",
    "structures_isomorphes", "est_automorphisme", "est_univalente",
    "transport_egalite", "transport_donne_isomorphisme",
]
