#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Échecs de preuve CERTIFIÉS — un échec est un THÉORÈME sur l'espace de recherche.

DOCTRINE (à lire AVANT d'écrire quoi que ce soit dans `outils_ia/verite/`)
────────────────────────────────────────────────────────────────────────
Un échec n'est PAS une note dans un journal, ni une phrase de rapport (« bloqué »,
« mur C62 »). C'est un énoncé sur l'espace de recherche, muni :
  1. d'un CERTIFICAT vérifiable — quand la classe le permet, un `Theoreme` du noyau ;
  2. d'un PÉRIMÈTRE CALCULÉ — l'ensemble des situations effectivement couvertes,
     obtenu en APPLIQUANT un prédicat, jamais en le supposant ;
  3. d'un REBROUSSEMENT — ce qu'il faut changer pour ne pas y retomber.
Un `Echec` dont `verifier()` est faux est REJETÉ du corpus. Pas « enregistré avec un
avertissement » : rejeté. Le journal de « murs » de ce projet a déjà déclaré 6 fois
« bloqué » à tort (mémoire : *« bloqué » faux 6×*) — la seule parade est un certificat
que la machine refait.

FRONTIÈRE DE CONFIANCE (interdits, valables aussi pour tout agent qui éditera ce fichier)
  • ce module ne FABRIQUE aucun `Theoreme` : il en REÇOIT et les INSPECTE
    (`.hypotheses`, `.conclusion`, `.est_clos`). Aucun `_CLE`, aucun monkeypatch,
    aucune substitution de fonction du noyau. Il n'ajoute AUCUN axiome :
    `theorie_ensembles()` vaut 22 avant et après (mesuré, cf. test_echec.py).
  • le seul théorème que ce module construit lui-même est le TÉMOIN CLOS ⊢ ¬(∅∈∅),
    refait par les primitives publiques du noyau à chaque validation d'un E2.
  • outil SUR le corpus, pas notion du livre ⇒ aucun marqueur `@livre` ici.

LES CLASSES
  E1 dérive    la recherche a CONSTRUIT quelque chose, mais pas la cible (test syntaxique).
  E2 vacuité   le résidu invoqué est RÉFUTABLE ⇒ tout théorème qui le porte est vide.
  E3 impasse   un MUR calculé barre la route ; son prédicat dit qui est hors d'atteinte.
  E4 dette     la preuve consomme des axiomes hors de la théorie de référence T0.
  E5 fantôme   le « résidu » est en fait un THÉORÈME CLOS de T0 : le mur n'existait pas.
  E6 infidélité l'énoncé formalisé n'est pas celui du livre (soundness ≠ fidélité).
  E7 erreur de mesure  le chiffre annoncé ≠ le chiffre refait.

TÉMOIN D'ABSURDITÉ. Il n'y a pas de « faux » primitif chez Bourbaki : la contradiction
s'exhibe par un couple (formule dérivée, sa négation close). On fixe ici le témoin
canonique ∅∈∅, dont la négation ⊢ ¬(∅∈∅) est un théorème CLOS de la théorie des
ensembles (axiome du vide instancié en ∅). Un E2 est donc : « le résidu prouve ∅∈∅ ».
"""
from __future__ import annotations

from dataclasses import dataclass, field
from functools import lru_cache
from typing import Callable

CLASSES = {
    "E1": "dérive", "E2": "vacuité", "E3": "impasse", "E4": "dette",
    "E5": "fantôme", "E6": "infidélité", "E7": "erreur de mesure",
}


# ── Témoin d'absurdité (Bourbaki n'a pas de « faux » primitif) ────────────────
def temoin_absurdite():
    """La formule ∅∈∅ : le témoin d'absurdité canonique de ce corpus."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import appartient
    from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
    return appartient(E.VIDE, E.VIDE)


@lru_cache(maxsize=1)
def negation_temoin_close():
    """⊢ ¬(∅∈∅) — théorème CLOS, REFAIT par le noyau (axiome du vide instancié en ∅).

    C'est ce qui donne son sens à un E2 : si le résidu prouve ∅∈∅ alors qu'on prouve
    sans hypothèse ¬(∅∈∅), le résidu est réfutable. On le reconstruit au lieu de le
    postuler ; si un jour l'axiome du vide changeait, la vérification E2 tomberait.
    """
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import instancie
    from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_VIDE)      # (∀z)¬(z∈∅)
    return instancie(ax, E.VIDE)                             # ⊢ ¬(∅∈∅)


def _est_theoreme(o) -> bool:
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau.noyau_abrege import Theoreme
    return isinstance(o, Theoreme)


def _est_formule(o) -> bool:
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import Formule
    return isinstance(o, Formule)


def _residus(residu) -> frozenset | None:
    """Normalise l'argument `residu` en frozenset de Formule ; None si non fourni."""
    if residu is None:
        return None
    if _est_formule(residu):
        return frozenset({residu})
    try:
        s = frozenset(residu)
    except TypeError:
        return None
    return s if all(_est_formule(f) for f in s) else None


# ── Murs : un périmètre CALCULÉ, jamais supposé ───────────────────────────────
@dataclass(frozen=True)
class Mur:
    """Une frontière de l'espace de recherche.

    condition  : énoncé lisible de la frontière (ce qui est vrai EXACTEMENT quand
                 `predicat` est vrai) — de la prose, donc jamais une preuve.
    predicat   : callable(objet) -> bool qui CALCULE si `objet` est dans la portée
                 du mur. Il inspecte la syntaxe ; il ne consulte aucune table écrite
                 à la main. `portee()` l'applique pour obtenir le périmètre.
    certificat : ce qui fonde le mur (typiquement un `Theoreme` clos). Facultatif.
    """
    condition: str
    predicat: Callable
    certificat: object = None

    def forme_valide(self) -> bool:
        return bool(self.condition) and callable(self.predicat)

    def portee(self, candidats) -> frozenset:
        """Périmètre CALCULÉ = { c ∈ candidats | predicat(c) }. Aucune supposition."""
        if not self.forme_valide():
            raise ValueError("Mur mal formé : condition vide ou prédicat non appelable")
        return frozenset(c for c in candidats if self.predicat(c))

    def hors_atteinte(self, candidats) -> frozenset:
        """Le complémentaire, tout aussi utile : ce que ce mur NE décide PAS."""
        return frozenset(candidats) - self.portee(candidats)


# ── L'échec lui-même ──────────────────────────────────────────────────────────
@dataclass(frozen=True)
class Echec:
    """Un échec certifié. `verifier()` doit être vrai, sinon l'échec est REJETÉ."""
    but: object                      # Formule visée (ou repère lisible)
    classe: str                      # "E1".."E7"
    certificat: object               # forme imposée par la classe (cf. verifier)
    rebroussement: str               # ce qu'il faut changer pour ne pas y retomber
    perimetre: frozenset = field(default_factory=frozenset)

    def __post_init__(self):
        object.__setattr__(self, "perimetre", frozenset(self.perimetre))

    @classmethod
    def depuis_mur(cls, but, classe, mur: Mur, rebroussement: str, candidats):
        """Construit un échec dont le périmètre est CALCULÉ par le mur sur `candidats`."""
        return cls(but=but, classe=classe, certificat=mur,
                   rebroussement=rebroussement, perimetre=mur.portee(candidats))


# ── derive : test SYNTAXIQUE, à ne pas confondre avec α-égalité ───────────────
def derive(construit, cible) -> bool:
    """E1 — vrai si la recherche a ABOUTI à un théorème dont la conclusion n'est PAS la cible.

    Test d'ÉGALITÉ SYNTAXIQUE (`Formule.__eq__`, structure + noms de liants).

    ⚠️ `outil_formule.alpha_egal` est un test DISTINCT et STRICTEMENT PLUS FAIBLE
    (il identifie deux formules qui ne diffèrent que par le nom des lettres liées).
    Il n'est JAMAIS un substitut ici : une preuve qui rend `(∀x)R` là où l'on visait
    `(∀y)R` a bel et bien dérivé — le corpus, lui, distingue ces deux énoncés (les
    collisions de liants sont un mode d'échec réel et documenté de ce projet). Si l'on
    veut ce diagnostic plus fin, on le rapporte SÉPARÉMENT, jamais en remplaçant ce test.

    ⚠️ La `cible` doit être reconstruite HORS du module testé (dans le test, ou depuis
    l'énoncé du livre). Si on la lit dans le module qui a échoué, on compare un module
    à lui-même : `derive` renverra False par construction et l'échec restera invisible.
    """
    if not _est_theoreme(construit):
        return False                       # rien de complet n'a été construit
    return construit.conclusion != cible


# ── vérification : chaque classe impose une FORME de certificat ───────────────
def _v_E1(e, _res) -> bool:
    return derive(e.certificat, e.but)


def _v_E2(e, res) -> bool:
    """Vacuité : {résidu} ⊢ ∅∈∅, avec ⊢ ¬(∅∈∅) clos par ailleurs."""
    if res is None or not _est_theoreme(e.certificat):
        return False
    c = e.certificat
    if c.conclusion != temoin_absurdite():
        return False
    if not c.hypotheses:
        # un ⊢ ∅∈∅ CLOS ne serait pas la vacuité d'un résidu : ce serait
        # l'incohérence de la théorie elle-même. Autre diagnostic, autre classe.
        return False
    if not (c.hypotheses <= res):
        return False
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import non
    n = negation_temoin_close()
    return n.est_clos and n.conclusion == non(temoin_absurdite())


def _v_E3(e, _res) -> bool:
    return isinstance(e.certificat, Mur) and e.certificat.forme_valide()


def _v_E4(e, _res) -> bool:
    """Dette : un ensemble NON VIDE de couples (nom_theorie, axiome) hors T0."""
    c = e.certificat
    if not isinstance(c, (frozenset, set, tuple, list)) or not c:
        return False
    return all(isinstance(p, tuple) and len(p) == 2
               and isinstance(p[0], str) and _est_formule(p[1]) for p in c)


def _v_E5(e, res) -> bool:
    """Fantôme : le résidu déclaré est prouvé SANS hypothèse ⇒ le mur n'existait pas."""
    if res is None or not _est_theoreme(e.certificat):
        return False
    return e.certificat.est_clos and e.certificat.conclusion in res


def _v_E6(e, _res) -> bool:
    """Infidélité : couple (formule formalisée, repère du livre), et l'écart doit EXISTER."""
    c = e.certificat
    if not (isinstance(c, tuple) and len(c) == 2 and _est_formule(c[0]) and isinstance(c[1], str)):
        return False
    return bool(c[1]) and c[0] != e.but


def _v_E7(e, _res) -> bool:
    """Erreur de mesure : couple (annoncé, refait) qui DIFFÈRENT effectivement."""
    c = e.certificat
    return isinstance(c, tuple) and len(c) == 2 and c[0] != c[1]


_VERIF = {"E1": _v_E1, "E2": _v_E2, "E3": _v_E3, "E4": _v_E4,
          "E5": _v_E5, "E6": _v_E6, "E7": _v_E7}


def verifier(e: Echec, residu=None) -> bool:
    """Vrai ssi le certificat de `e` correspond à sa classe. Faux ⇒ échec REJETÉ.

    `residu` (Formule ou itérable de Formule) est requis par E2 et E5 : ce sont les
    deux classes qui parlent D'UN résidu précis, et l'on refuse de les valider à
    l'aveugle. Un `Echec` de classe inconnue est faux, jamais toléré.
    """
    if not isinstance(e, Echec) or e.classe not in _VERIF:
        return False
    if not isinstance(e.rebroussement, str) or not e.rebroussement.strip():
        return False                       # sans rebroussement, on y retombera
    if not isinstance(e.perimetre, frozenset):
        return False
    return bool(_VERIF[e.classe](e, _residus(residu)))


# ── Cas réel encodé : le mur « résidu d'indice » ──────────────────────────────
def est_vide_syntaxique(t) -> bool:
    """CALCULE si le terme `t` EST l'ensemble vide au sens SYNTAXIQUE : le signe ∅.

    Décidable et local : `t` est `app("vide")` sans argument. Rien d'autre n'est
    déclaré vide — surtout pas un terme dont on « sait » qu'il l'est : J∪{j} n'est
    pas ∅ syntaxiquement (et de fait il contient j), une variable I ne l'est pas non
    plus. C'est précisément ce que le mur ci-dessous doit dire.
    """
    return getattr(t, "tag", None) == "app" and getattr(t, "nom", None) == "vide" \
        and not getattr(t, "args", ())


def mur_residu_indice_vide(j: str = "j") -> Mur:
    """Mur RÉEL : Réfutable( j∈I ) ⇔ I est syntaxiquement ∅.

    ⇒ (sens direct) si I est ∅, l'axiome du vide instancié en j réfute le résidu :
       le certificat ci-dessous est le théorème CLOS ⊢ ¬(j∈∅).
    ⇐ (le périmètre, c'est-à-dire ce que le mur NE prend PAS) : pour I = J∪{j} le
       résidu est au contraire PROUVABLE (j y appartient), et pour I variable il est
       indépendant. Ces deux formes sont HORS D'ATTEINTE de ce mur — le prédicat le
       calcule sur la syntaxe du terme, il ne le suppose pas.
    """
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import instancie
    from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
    cert = instancie(N.axiome(E.theorie_ensembles(), E.AXIOME_VIDE), var(j))   # ⊢ ¬(j∈∅)
    return Mur(condition=f"Réfutable( {j}∈I ) ⇔ I est syntaxiquement ∅",
               predicat=est_vide_syntaxique, certificat=cert)


__all__ = ["CLASSES", "Echec", "Mur", "verifier", "derive", "temoin_absurdite",
           "negation_temoin_close", "est_vide_syntaxique", "mur_residu_indice_vide"]
