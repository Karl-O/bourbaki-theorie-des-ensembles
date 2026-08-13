"""Couche 1 — Lecture : assemblage ⇄ arbre de syntaxe.

Bourbaki, Chap. I, Appendice « Caractérisation des termes et des relations »
(E I.42--E I.46, PDF p.42--46 — la citation antérieure « p.33--35 » était fausse).

C'est LA pièce que la V8 n'avait jamais implémentée (`est_significatif`
y valait littéralement ``len(M) <= 50``). Ici on réalise la *lecture unique*
des mots significatifs : un assemblage en notation préfixe se décompose de
manière unique grâce aux poids (arités) des signes. C'est l'unicité de
lecture à la Łukasiewicz, qui est précisément ce que démontre l'Appendice.

Grammaire (notation préfixe) :

    Relation ::= OU  Relation Relation
               | NON Relation
               | s   Terme … Terme        (s signe spécifique *relationnel*, arité n)

    Terme    ::= lettre
               | CARRE                    (▢, lié à un τ englobant — De Bruijn)
               | TAU Relation             (τ ; le corps contient les ▢ qu'il lie)
               | f   Terme … Terme        (f signe spécifique *fonctionnel*, arité n)

Les ▢ sont représentés par leur **indice de De Bruijn** (nombre de τ qui les
séparent de leur lieur), ce qui rend l'arbre indépendant des positions et
garantit le round-trip exact avec les liens de l'assemblage.
"""
from __future__ import annotations
from dataclasses import dataclass

from bourbaki.i_description_mathematique_formelle.assemblage import Assemblage, est_lettre

# Signature : nom du signe spécifique -> (arité, sorte∈{'relation','terme'}).
Signature = dict[str, tuple[int, str]]

# Signature par défaut de la théorie des ensembles : = et ∈, relationnels, arité 2.
# @livre Ch.I §1.1 Def.- | E I.14 L.8-10 | PDF p.14  (3° signes spécifiques ; en Théorie des Ensembles : = et ∈ seulement)
DEFAUT: Signature = {"=": (2, "relation"), "in": (2, "relation")}


# @livre Ch.I §App.0 Rem.- | E I.42 L.14-20 | PDF p.42  (but de l'Appendice : exemple de raisonnement métamathématique — prose)
class NonSignificatif(ValueError):
    """L'assemblage n'est ni un terme ni une relation bien formé."""


@dataclass(frozen=True)
class Arbre:
    """Arbre de syntaxe. ``sorte`` ∈ {'terme','relation'}.

    tete ∈ {'OU','NON','TAU','CARRE','LETTRE','SIGNE'}.
    etiquette : nom de lettre ou de signe spécifique (sinon '').
    db : indice de De Bruijn (uniquement pour 'CARRE').
    """
    tete: str
    sorte: str
    enfants: tuple["Arbre", ...] = ()
    etiquette: str = ""
    db: int = -1


# ── depuis_assemblage : lecture (parse) ───────────────────────────────────────

# @livre Ch.I §1.1 Def.- | E I.15 L.24-27 | PDF p.15  (théorie mathématique : règles disant quels assemblages sont termes/relations — ici, les règles de lecture)
# @livre Ch.I §App.1 Def.- | E I.42 L.21-32 | PDF p.42  (signes, mots = suites finies, monoïde libre L₀(S), longueur l(A))
# @livre Ch.I §App.1 Def.- | E I.43 L.1-7 | PDF p.43  (poids n(A), segments, segments initiaux/finaux/disjoints)
# @livre Ch.I §App.2 Def.- | E I.43 L.8-15 | PDF p.43  (suite significative, mots significatifs — réalisés par la lecture récursive)
# @livre Ch.I §App.4 Def.- | E I.45 L.3-10 | PDF p.45  (application aux assemblages : poids n(▢)=0, n(τ)=n(¬)=1, n(∨)=2, n(lettre)=0 ; mot A*, segments d'assemblages)
# @livre Ch.I §App.4 Rem.- | E I.46 L.23-29 | PDF p.46  (procédé de décision de proche en proche — c'est exactement cet algorithme récursif ; petit texte)
def depuis_assemblage(a: Assemblage, sig: Signature = DEFAUT) -> Arbre:
    """Lit l'assemblage en arbre. Lève NonSignificatif si mal formé.

    Vérifie que TOUT l'assemblage est consommé (un mot significatif n'a pas
    de « reste »), ce qui est exactement le critère de l'Appendice.
    """
    arbre, i = _lire(a, 0, [], sig)
    if i != a.n:
        raise NonSignificatif(f"signes résiduels après lecture (i={i}, n={a.n})")
    return arbre


def _binder_de(a: Assemblage, pos_carre: int) -> int:
    """Position 1-based du τ liant le ▢ situé à ``pos_carre`` (1-based)."""
    binders = [u for (u, v) in a.liens if v == pos_carre]
    if len(binders) != 1:
        raise NonSignificatif(f"▢ en {pos_carre} doit avoir exactement un lieur")
    return binders[0]


# @livre Ch.I §App.3 Lem.1 | E I.44 L.9-23 | PDF p.44  (segment équilibré unique commençant à la (k+1)-ème place ; énoncé L.9-10, démo L.11-23)
# @livre Ch.I §App.3 Lem.2 | E I.44 L.24-33 | PDF p.44  (tout mot équilibré = fA₁…Aₚ, Aᵢ équilibrés, n(f)=p ; démo L.26-33)
# @livre Ch.I §App.3 Cor.1 | E I.44 L.36-37 | PDF p.44  (segment significatif unique à la (k+1)-ème place — l'unicité de la lecture)
# @livre Ch.I §App.3 Cor.2 | E I.45 L.1-2 | PDF p.45  (décomposition UNIQUE fA₁…Aₚ d'un mot significatif — lecture préfixe déterministe, réalisée par _lire)
# @livre Ch.I §App.4 Def.- | E I.45 L.20-24 | PDF p.45  (assemblages antécédents — introduction ; la condition « équilibré » seule ne suffit pas)
# @livre Ch.I §App.4 Def.- | E I.45 L.25-31 | PDF p.45  (1° antécédents pour ¬, ∨, signe spécifique ; « parfaitement équilibré »)
# @livre Ch.I §App.4 Def.- | E I.45 L.32-38 | PDF p.45  (2° antécédents pour τ : remplacer les ▢ liés par une lettre fraîche)
# @livre Ch.I §App.4 Def.- | E I.46 L.1-3 | PDF p.46  (fin du 2° : parfaitement équilibré pour τ)
def _lire(a: Assemblage, i: int, taus: list[int], sig: Signature) -> tuple[Arbre, int]:
    """Lit un mot significatif à partir de l'indice ``i`` (0-based).

    ``taus`` = pile des positions 1-based des τ ouverts (du plus externe au
    plus interne). Retourne (arbre, indice suivant).
    """
    if i >= a.n:
        raise NonSignificatif("lecture au-delà de la fin")
    s = a.signes[i]

    if s == "OU":
        g, i = _lire(a, i + 1, taus, sig)
        d, i = _lire(a, i, taus, sig)
        _exiger(g.sorte == "relation" and d.sorte == "relation", "OU attend deux relations")
        return Arbre("OU", "relation", (g, d)), i

    if s == "NON":
        r, i = _lire(a, i + 1, taus, sig)
        _exiger(r.sorte == "relation", "NON attend une relation")
        return Arbre("NON", "relation", (r,)), i

    if s == "TAU":
        pos_tau = i + 1  # 1-based
        corps, i = _lire(a, i + 1, taus + [pos_tau], sig)
        _exiger(corps.sorte == "relation", "TAU attend une relation")
        return Arbre("TAU", "terme", (corps,)), i

    if s == "CARRE":
        pos = i + 1
        binder = _binder_de(a, pos)
        _exiger(binder in taus, f"▢ en {pos} non lié à un τ englobant")
        db = (len(taus) - 1) - taus.index(binder)  # 0 = τ le plus interne
        return Arbre("CARRE", "terme", db=db), i + 1

    # La signature est consultée AVANT est_lettre : un signe déclaré (ex. un
    # atome propositionnel « A » de poids 0) prime sur son statut de lettre.
    if s in sig:
        arite, sorte = sig[s]
        enfants: list[Arbre] = []
        i += 1  # consommer le signe spécifique avant de lire ses arguments
        for _ in range(arite):
            c, i = _lire(a, i, taus, sig)
            _exiger(c.sorte == "terme", f"signe {s!r} attend des termes")
            enfants.append(c)
        return Arbre("SIGNE", sorte, tuple(enfants), etiquette=s), i

    if est_lettre(s):
        return Arbre("LETTRE", "terme", etiquette=s), i + 1

    raise NonSignificatif(f"signe inconnu ou hors-place : {s!r}")


def _exiger(cond: bool, msg: str) -> None:
    if not cond:
        raise NonSignificatif(msg)


# ── vers_assemblage : écriture (unparse) ──────────────────────────────────────

# @livre Ch.I §App.2 Prop.1 | E I.43 L.16-17 | PDF p.43  (fA₁…Aₚ est significatif si les Aᵢ le sont — sens « écriture » : recomposer un mot significatif)
def vers_assemblage(arbre: Arbre) -> Assemblage:
    """Reconstruit l'assemblage à partir de l'arbre (inverse de depuis_assemblage)."""
    signes: list[str] = []
    liens: list[tuple[int, int]] = []
    _ecrire(arbre, [], signes, liens)
    return Assemblage(tuple(signes), tuple(liens))


def _ecrire(arbre: Arbre, taus: list[int], signes: list[str],
            liens: list[tuple[int, int]]) -> None:
    if arbre.tete == "OU":
        signes.append("OU")
        _ecrire(arbre.enfants[0], taus, signes, liens)
        _ecrire(arbre.enfants[1], taus, signes, liens)
    elif arbre.tete == "NON":
        signes.append("NON")
        _ecrire(arbre.enfants[0], taus, signes, liens)
    elif arbre.tete == "TAU":
        pos_tau = len(signes) + 1
        signes.append("TAU")
        _ecrire(arbre.enfants[0], taus + [pos_tau], signes, liens)
    elif arbre.tete == "CARRE":
        pos = len(signes) + 1
        signes.append("CARRE")
        liens.append((taus[-1 - arbre.db], pos))  # De Bruijn -> position du τ lieur
    elif arbre.tete == "LETTRE":
        signes.append(arbre.etiquette)
    elif arbre.tete == "SIGNE":
        signes.append(arbre.etiquette)
        for c in arbre.enfants:
            _ecrire(c, taus, signes, liens)
    else:
        raise ValueError(f"tête d'arbre inconnue : {arbre.tete!r}")


# ── Prédicats de l'Appendice (enfin réels) ────────────────────────────────────

# @livre Ch.I §App.3 Def.- | E I.43 L.18-20 | PDF p.43  (mot équilibré : l(A)=n(A)+1 et l(B)≤n(B) pour tout segment initial propre — réalisé implicitement par la lecture)
# @livre Ch.I §App.3 Prop.2 | E I.43 L.21-32 | PDF p.43  (significatif ⇔ équilibré ; énoncé L.21, démo (⇒) L.22-32)
# @livre Ch.I §App.3 Demo.- | E I.44 L.1-8 | PDF p.44  (fin de la démo de la prop. 2, sens direct ; annonce des deux lemmes)
# @livre Ch.I §App.3 Demo.- | E I.44 L.34-35 | PDF p.44  (démo de la prop. 2, sens réciproque : récurrence sur la longueur via lemme 2 + prop. 1)
# @livre Ch.I §App.4 Crit.1 | E I.45 L.11-19 | PDF p.45  (si A est un terme ou une relation, A est équilibré ; énoncé L.11, démo L.12-19)
# @livre Ch.I §App.4 Rem.- | E I.46 L.30-33 | PDF p.46  (Remarque finale : pas de procédé général pour décider si R est un THÉORÈME — prose, rien à formaliser)
def est_significatif(a: Assemblage, sig: Signature = DEFAUT) -> bool:
    """True ssi A est un terme OU une relation bien formé. Appendice, E I.43-46 (PDF p.43-46)."""
    try:
        depuis_assemblage(a, sig)
        return True
    except NonSignificatif:
        return False


# @livre Ch.I §App.4 Crit.2 | E I.46 L.4-12 | PDF p.46  (Critère 2 : conditions nécessaires et suffisantes terme/relation ; volet relations L.9-12)
# @livre Ch.I §App.4 Demo.- | E I.46 L.13-22 | PDF p.46  (démo du critère 2 : suffisance par CF1-CF4, nécessité par cas ∨/¬/signe/τ)
def est_relation(a: Assemblage, sig: Signature = DEFAUT) -> bool:
    """True ssi A est une relation. Critère 2 de l'Appendice, E I.46 (PDF p.46)."""
    try:
        return depuis_assemblage(a, sig).sorte == "relation"
    except NonSignificatif:
        return False


# @livre Ch.I §App.4 Crit.2 | E I.46 L.4-8 | PDF p.46  (Critère 2, volet termes : lettre, ou τ parfaitement équilibré à antécédents relations)
def est_terme(a: Assemblage, sig: Signature = DEFAUT) -> bool:
    """True ssi A est un terme. Critère 2 de l'Appendice, E I.46 (PDF p.46)."""
    try:
        return depuis_assemblage(a, sig).sorte == "terme"
    except NonSignificatif:
        return False


__all__ = [
    "Signature", "DEFAUT", "NonSignificatif", "Arbre",
    "depuis_assemblage", "vers_assemblage",
    "est_significatif", "est_relation", "est_terme",
]
