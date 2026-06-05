"""Couche abrégée (chemin Bourbaki) — formules à connecteurs ABRÉVIATEURS.

Primitifs : termes (var, τ, application) ; formules ¬, ∨, =, ∈, ∃.
Abréviateurs (constructeurs intelligents bâtis sur les primitifs, comme Bourbaki) :
  A⇒B := ¬A∨B ;  A et B := ¬(¬A∨¬B) ;  A⇔B := (A⇒B) et (B⇒A) ;
  (∀x)F := ¬(∃x)¬F ;  T⊂U := (∀z)(z∈T⇒z∈U) ;  Coll_x F := (∃y)(∀x)((x∈y)⇔F).

Ainsi une abréviation EST sa définition (mêmes nœuds) → le dépliage est gratuit,
et ∃ reste un NŒUD (jamais τ-substitué) → AUCUN gonflement exponentiel.
`developper_f` donne le pont vers l'assemblage-τ (justification, petits cas).
"""
from __future__ import annotations
from dataclasses import dataclass

from bourbaki.assemblage import assemblage as A


@dataclass(frozen=True)
class Terme:
    tag: str                 # 'var' | 'tau' | 'app'
    nom: str = ""
    lieur: str = ""          # variable liée ('tau')
    args: tuple = ()         # ('tau' : (Formule,)) | ('app' : Terme…)


@dataclass(frozen=True)
class Formule:
    tag: str                 # primitifs : '=' 'in' 'non' 'ou' 'exists'
    lieur: str = ""          # variable liée ('exists')
    termes: tuple = ()       # arguments Terme ('=', 'in')
    sous: tuple = ()         # sous-formules ('non','ou','exists')


# ── Termes ────────────────────────────────────────────────────────────────────
def var(n): return Terme("var", nom=n)
def tau(x, f): return Terme("tau", lieur=x, args=(f,))
def app(s, *args): return Terme("app", nom=s, args=tuple(args))


# ── Formules primitives ───────────────────────────────────────────────────────
def egal(t, u): return Formule("=", termes=(t, u))
def appartient(t, u): return Formule("in", termes=(t, u))
def non(f): return Formule("non", sous=(f,))
def ou(f, g): return Formule("ou", sous=(f, g))
def existe(x, f): return Formule("exists", lieur=x, sous=(f,))


# ── Abréviateurs (= leur définition) ──────────────────────────────────────────
def impl(f, g): return ou(non(f), g)
def et(f, g): return non(ou(non(f), non(g)))
def equiv(f, g): return et(impl(f, g), impl(g, f))
def pourtout(x, f): return non(existe(x, non(f)))


def inclus(t, u, z="z"):
    if z in libres_t(t) | libres_t(u):
        z = _fraiche(libres_t(t) | libres_t(u))
    zt = var(z)
    return pourtout(z, impl(appartient(zt, t), appartient(zt, u)))


def coll(x, f, y="y"):
    if y in libres_f(f) | {x}:
        y = _fraiche(libres_f(f) | {x})
    return existe(y, pourtout(x, equiv(appartient(var(x), var(y)), f)))


# ── Variables libres ──────────────────────────────────────────────────────────
def libres_t(t: Terme) -> set:
    if t.tag == "var":
        return {t.nom}
    if t.tag == "tau":
        return libres_f(t.args[0]) - {t.lieur}
    return set().union(*(libres_t(a) for a in t.args)) if t.args else set()


def libres_f(f: Formule) -> set:
    s = set().union(*(libres_t(t) for t in f.termes)) if f.termes else set()
    if f.tag == "exists":
        return s | (libres_f(f.sous[0]) - {f.lieur})
    return s | (set().union(*(libres_f(g) for g in f.sous)) if f.sous else set())


def _fraiche(eviter: set) -> str:
    """Variable fraîche DÉTERMINISTE et EXOTIQUE (@0, @1, …).

    Les noms « @k » ne coïncident jamais avec un liant utilisateur (z, y, x, u, v,
    F, G…) : un renommage capture-évitant ne peut donc plus cascader sur un liant
    interne homonyme (ex. le « z » de est_fonctionnel). Déterministe → deux chemins
    de substitution produisent des structures IDENTIQUES (matching MP robuste)."""
    k = 0
    while True:
        c = "@" + str(k)
        if c not in eviter:
            return c
        k += 1


# ── Substitution capture-évitante (T|x) ───────────────────────────────────────
def subst_t(tval: Terme, x: str, t: Terme) -> Terme:
    if t.tag == "var":
        return tval if t.nom == x else t
    if t.tag == "tau":
        y, corps = t.lieur, t.args[0]
        if y == x:
            return t
        if y in libres_t(tval):
            z = _fraiche(libres_t(tval) | libres_f(corps) | {x})
            corps, y = subst_f(var(z), y, corps), z
        return Terme("tau", lieur=y, args=(subst_f(tval, x, corps),))
    return Terme("app", nom=t.nom, args=tuple(subst_t(tval, x, a) for a in t.args))


def subst_f(tval: Terme, x: str, f: Formule) -> Formule:
    if f.tag == "exists":
        y, corps = f.lieur, f.sous[0]
        if y == x:
            return f
        if y in libres_t(tval):
            z = _fraiche(libres_t(tval) | libres_f(corps) | {x})
            corps, y = subst_f(var(z), y, corps), z
        return Formule("exists", lieur=y, sous=(subst_f(tval, x, corps),))
    return Formule(f.tag,
                   termes=tuple(subst_t(tval, x, t) for t in f.termes),
                   sous=tuple(subst_f(tval, x, g) for g in f.sous))


# ── Affichage (reconnaît les abréviateurs) ────────────────────────────────────
def afficher_t(t: Terme) -> str:
    if t.tag == "var":
        return t.nom
    if t.tag == "tau":
        return f"τ{t.lieur}({afficher_f(t.args[0])})"
    return f"{t.nom}({', '.join(afficher_t(a) for a in t.args)})"


def _est(f, tag):
    return isinstance(f, Formule) and f.tag == tag


def afficher_f(f: Formule) -> str:
    if f.tag == "=":
        return f"({afficher_t(f.termes[0])} = {afficher_t(f.termes[1])})"
    if f.tag == "in":
        return f"({afficher_t(f.termes[0])} ∈ {afficher_t(f.termes[1])})"
    if f.tag == "exists":
        return f"(∃{f.lieur}) {afficher_f(f.sous[0])}"
    if f.tag == "ou":
        g, d = f.sous
        if _est(g, "non"):                                  # ¬a ∨ b  =  a ⇒ b
            return f"({afficher_f(g.sous[0])} ⇒ {afficher_f(d)})"
        return f"({afficher_f(g)} ∨ {afficher_f(d)})"
    if f.tag == "non":
        g = f.sous[0]
        if _est(g, "exists") and _est(g.sous[0], "non"):     # ¬(∃x)¬h  =  (∀x)h
            return f"(∀{g.lieur}) {afficher_f(g.sous[0].sous[0])}"
        if _est(g, "ou") and _est(g.sous[0], "non") and _est(g.sous[1], "non"):
            a, b = g.sous[0].sous[0], g.sous[1].sous[0]      # ¬(¬a∨¬b) = a et b
            if _est(a, "ou") and _est(a.sous[0], "non") and _est(b, "ou") and _est(b.sous[0], "non"):
                return f"({afficher_f(a)} ⇔ {afficher_f(b)})"  # heuristique ⇔
            return f"({afficher_f(a)} et {afficher_f(b)})"
        return f"¬{afficher_f(g)}"
    raise ValueError(f"tag inconnu : {f.tag}")


# ── Pont vers l'assemblage-τ (justification ; petits cas) ─────────────────────
def developper_t(t: Terme) -> A.Assemblage:
    if t.tag == "var":
        return A.Assemblage((t.nom,))
    if t.tag == "tau":
        return A.tau_x(developper_f(t.args[0]), t.lieur)
    d = A.Assemblage((t.nom,))
    for a in t.args:
        d = A.concat(d, developper_t(a))
    return d


def developper_f(f: Formule) -> A.Assemblage:
    if f.tag == "=":
        return A.egalite(developper_t(f.termes[0]), developper_t(f.termes[1]))
    if f.tag == "in":
        return A.concat(A.concat(A.Assemblage(("in",)), developper_t(f.termes[0])),
                        developper_t(f.termes[1]))
    if f.tag == "non":
        return A.negation(developper_f(f.sous[0]))
    if f.tag == "ou":
        return A.disjonction(developper_f(f.sous[0]), developper_f(f.sous[1]))
    if f.tag == "exists":
        return A.existe(f.lieur, developper_f(f.sous[0]))
    raise ValueError(f"tag inconnu : {f.tag}")


# ── α-équivalence (canonicalisation des variables liées) ──────────────────────
def _canon_t(t: Terme, env: dict, c: list) -> Terme:
    if t.tag == "var":
        return Terme("var", nom=env.get(t.nom, t.nom))
    if t.tag == "tau":
        nom = f"§{c[0]}"; c[0] += 1
        return Terme("tau", lieur=nom, args=(_canon_f(t.args[0], {**env, t.lieur: nom}, c),))
    return Terme("app", nom=t.nom, args=tuple(_canon_t(a, env, c) for a in t.args))


def _canon_f(f: Formule, env: dict, c: list) -> Formule:
    if f.tag == "exists":
        nom = f"§{c[0]}"; c[0] += 1
        return Formule("exists", lieur=nom, sous=(_canon_f(f.sous[0], {**env, f.lieur: nom}, c),))
    return Formule(f.tag,
                   termes=tuple(_canon_t(t, env, c) for t in f.termes),
                   sous=tuple(_canon_f(g, env, c) for g in f.sous))


def canon_f(f: Formule) -> Formule:
    """Forme canonique : variables liées renommées §0,§1,… (ordre de liaison)."""
    return _canon_f(f, {}, [0])


def alpha_egal(f: Formule, g: Formule) -> bool:
    """Égalité À RENOMMAGE PRÈS des variables liées (α-équivalence)."""
    return canon_f(f) == canon_f(g)


__all__ = ["Terme", "Formule", "var", "tau", "app", "egal", "appartient",
           "non", "ou", "existe", "impl", "et", "equiv", "pourtout", "inclus", "coll",
           "libres_t", "libres_f", "subst_t", "subst_f",
           "afficher_t", "afficher_f", "developper_t", "developper_f",
           "canon_f", "alpha_egal"]
