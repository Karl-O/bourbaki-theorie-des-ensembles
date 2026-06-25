"""§IV.1.1–IV.1.2 — Échelons : schémas de construction, échelon S(E₁,…,Eₙ),
extension canonique ⟨f₁,…,fₙ⟩^S, typification.   REPRÉSENTATIONNEL.

⚠️ MÉTAMATHÉMATIQUE.  Un schéma de construction d'échelon (IV.1.1) est une SUITE
FINIE de couples d'entiers naturels c_i=(a_i,b_i) ; l'échelon S(E₁,…,Eₙ) et
l'extension canonique ⟨f₁,…,fₙ⟩^S sont définis par une RÉCURRENCE MÉTA sur cette
suite (passage aux parties 𝔓 et au produit ×).  Ce ne sont donc PAS des notions
exprimables par une seule formule du fragment objet : ce sont des schémas/objets
du MÉTALANGAGE.  On en donne ici une REPRÉSENTATION FIDÈLE :

  • un schéma = un objet Python `Schema` (tuple de couples (a,b) d'entiers ≥ 0),
    avec la condition de validité de IV.1.1 vérifiée par `schema_valide` ;
  • l'INTERPRÉTATION d'un schéma sur des Termes-objets E₁,…,Eₙ est réalisée par la
    récurrence méta `echelon(S, [E₁,…,Eₙ])`, qui RETOURNE un Terme du fragment
    objet (bâti avec `produit` et `parties` de ensembles_abrege) : c'est très
    exactement la suite A₁,…,A_m de IV.1.1 et son dernier terme A_m = S(E₁,…,Eₙ) ;
  • de même `extension_canonique(S, [f₁,…,fₙ])` RETOURNE le Terme-objet
    ⟨f₁,…,fₙ⟩^S (récurrence de IV.1.2 : extension aux parties `ext_parties`,
    produit d'applications `produit_applications`).  Ces deux extensions
    (`ext_parties`, `produit_applications`) sont laissées OPAQUES au niveau objet
    (termes app(...) neufs) — leur théorie propre relève de E.II ; on les
    documente honnêtement comme primitives représentationnelles.

Aucun axiome ajouté à theorie_ensembles() (reste à 22).  Les `def` ci-dessous sont
soit des objets Python (schémas), soit des FONCTIONS méta renvoyant des Termes
du fragment objet — FIDÈLES aux énoncés VERBATIM de IV.1.1–IV.1.2.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Sequence, Tuple

from bourbaki.logique.i_1_termes_relations.formule import app
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E


# ─────────────────────────────────────────────────────────────────────────────
# §IV.1.1 — SCHÉMA DE CONSTRUCTION D'ÉCHELON (objet méta)
# ─────────────────────────────────────────────────────────────────────────────
# @livre Ch.IV §1.1 Def.- | E IV.1 L.6-12 | PDF p.204
@dataclass(frozen=True)
class Schema:
    """Schéma de construction d'échelon (IV.1.1) — REPRÉSENTATION.

    « Un schéma de construction d'échelon est une suite c_1,c_2,…,c_m de couples
    d'entiers naturels c_i=(a_i,b_i) satisfaisant : a) Si b_i=0, on a 1≤a_i≤i−1 ;
    b) Si a_i≠0 et b_i≠0, on a 1≤a_i≤i−1 et 1≤b_i≤i−1.  Ces conditions entraînent
    que c_1=(0,b_1) avec b_1>0.  Si n est le plus grand des entiers b_i figurant
    dans les couples (0,b_i), on dit que c_1,…,c_m est un schéma de construction
    d'échelon sur n termes. »

    Représentation : `couples` est le tuple ((a_1,b_1),…,(a_m,b_m)) (indexé à
    partir de 0 en Python, c_i = couples[i-1])."""
    couples: Tuple[Tuple[int, int], ...]

    def __post_init__(self):
        object.__setattr__(self, "couples", tuple((int(a), int(b)) for (a, b) in self.couples))

    @property
    def m(self) -> int:
        """Longueur m de la suite (nombre de termes de la construction)."""
        return len(self.couples)


# @livre Ch.IV §1.1 Def.- | E IV.1 L.6-9 | PDF p.204
def schema_valide(s: Schema) -> bool:
    """Vrai ssi `s` satisfait les conditions a)/b) de IV.1.1.

    Pour c_i=(a_i,b_i) (i de 1 à m) : a) si b_i=0 alors 1≤a_i≤i−1 ;
    b) si a_i≠0 et b_i≠0 alors 1≤a_i≤i−1 et 1≤b_i≤i−1.
    (Le cas restant a_i=0 — un terme de base E_{b_i} — exige b_i>0 ; c'est imposé
    par « ces conditions entraînent c_1=(0,b_1) avec b_1>0 », généralisé à tout
    terme de base : un couple (0,0) ne désigne aucun terme et est rejeté.)"""
    for i, (a, b) in enumerate(s.couples, start=1):
        if a < 0 or b < 0:
            return False
        if a == 0:
            # terme de base E_{b} : il faut b ≥ 1
            if b < 1:
                return False
        elif b == 0:
            # passage aux parties 𝔓(A_a) : 1 ≤ a ≤ i−1
            if not (1 <= a <= i - 1):
                return False
        else:
            # produit A_a × A_b : 1 ≤ a ≤ i−1 et 1 ≤ b ≤ i−1
            if not (1 <= a <= i - 1 and 1 <= b <= i - 1):
                return False
    return True


# @livre Ch.IV §1.1 Def.- | E IV.1 L.10-12 | PDF p.204
def schema_nb_termes(s: Schema) -> int:
    """n = le plus grand des entiers b_i figurant dans les couples (0,b_i) (IV.1.1).

    C'est le nombre d'ensembles de base principaux sur lesquels le schéma opère ;
    on dit que `s` est « un schéma de construction d'échelon sur n termes »."""
    bases = [b for (a, b) in s.couples if a == 0]
    return max(bases) if bases else 0


# Schémas usuels (exemples de IV.1.1) — pratiques pour les tests et le lecteur.
def schema_base(k: int = 1) -> Schema:
    """Schéma à un seul terme c_1=(0,k) : l'échelon S(E₁,…) = E_k (identité)."""
    return Schema(((0, k),))


def schema_parties() -> Schema:
    """Schéma c_1=(0,1), c_2=(1,0) : l'échelon S(E) = 𝔓(E)."""
    return Schema(((0, 1), (1, 0)))


def schema_produit() -> Schema:
    """Schéma c_1=(0,1), c_2=(0,2), c_3=(1,2) : l'échelon S(E₁,E₂) = E₁×E₂."""
    return Schema(((0, 1), (0, 2), (1, 2)))


def schema_relation() -> Schema:
    """Schéma de S(E) = 𝔓(E×E) : c_1=(0,1), c_2=(1,1), c_3=(2,0).

    A_1=E, A_2=E×E (produit a=b=1), A_3=𝔓(A_2).  Échelon relationnel : une
    structure d'ordre, de graphe, etc. (échelon non trivial le plus simple)."""
    return Schema(((0, 1), (1, 1), (2, 0)))


# ─────────────────────────────────────────────────────────────────────────────
# §IV.1.1 — CONSTRUCTION D'ÉCHELON et ÉCHELON S(E₁,…,Eₙ) (interprétation objet)
# ─────────────────────────────────────────────────────────────────────────────
# @livre Ch.IV §1.1 Def.- | E IV.1 L.13-20 | PDF p.204
def construction_echelon(s: Schema, bases: Sequence) -> list:
    """Construction d'échelon, de schéma S, sur E₁,…,Eₙ (IV.1.1).

    « une suite A_1,…,A_m de m termes définis de proche en proche par :
      a) Si c_i=(0,b_i), A_i est le terme E_{b_i} ;
      b) Si c_i=(a_i,0), A_i est le terme 𝔓(A_{a_i}) ;
      c) Si c_i=(a_i,b_i) avec a_i≠0,b_i≠0, A_i est le terme A_{a_i}×A_{b_i}. »

    `bases` = [E₁,…,Eₙ] (Termes du fragment objet).  Renvoie la LISTE [A_1,…,A_m]
    de Termes-objets (𝔓 = parties, × = produit de ensembles_abrege)."""
    A: list = []
    for (a, b) in s.couples:
        if a == 0:
            A.append(bases[b - 1])                  # E_{b_i}
        elif b == 0:
            A.append(E.parties(A[a - 1]))           # 𝔓(A_{a_i})
        else:
            A.append(E.produit(A[a - 1], A[b - 1])) # A_{a_i} × A_{b_i}
    return A


# @livre Ch.IV §1.1 Def.- | E IV.2 L.1-4 | PDF p.205
def echelon(s: Schema, bases: Sequence):
    """Échelon de schéma S sur les ensembles de base E₁,…,Eₙ (IV.1.1).

    « Le dernier terme A_m de la construction d'échelon de schéma S sur E₁,…,Eₙ est
    l'échelon de schéma S sur les ensembles de base E₁,…,Eₙ ; il est désigné par la
    notation S(E₁,…,Eₙ). »  Renvoie le Terme-objet A_m."""
    A = construction_echelon(s, bases)
    if not A:
        raise ValueError("schéma vide : aucun échelon")
    return A[-1]


# ─────────────────────────────────────────────────────────────────────────────
# §IV.1.2 — EXTENSION CANONIQUE ⟨f₁,…,fₙ⟩^S
# ─────────────────────────────────────────────────────────────────────────────
# Les deux briques de l'extension (extension aux parties d'une application,
# produit de deux applications) sont laissées OPAQUES au niveau objet : termes
# neufs app("ext_parties", g) et app("produit_app", g, h).  Représentationnel :
# leur caractérisation propre (E.II) n'est pas requise pour INTRODUIRE la notion.
# @livre Ch.IV §1.2 Def.- | E IV.2 L.22-23 | PDF p.205
def ext_parties(g):
    """Extension canonique ḡ de g aux ensembles de parties (IV.1.2 b)) — OPAQUE.

    Si g:A→A', ḡ:𝔓(A)→𝔓(A') est l'application image-directe X↦g⟨X⟩ (E.II.5)."""
    return app("ext_parties", g)


# @livre Ch.IV §1.2 Def.- | E IV.2 L.24-25 | PDF p.205
def produit_applications(g, h):
    """Extension canonique g×h à A_a×A_b (IV.1.2 c)) — OPAQUE.

    Si g:A→A', h:B→B', g×h:A×B→A'×B' est (x,y)↦(g(x),h(y)) (E.II.3.9)."""
    return app("produit_app", g, h)


# @livre Ch.IV §1.2 Def.- | E IV.2 L.13-28 | PDF p.205
def extension_canonique(s: Schema, applis: Sequence):
    """Extension canonique, de schéma S, des applications f₁,…,fₙ (IV.1.2).

    « On définit de proche en proche g_1,…,g_m, chacun application de A_i dans A_i',
    par : a) Si c_i=(0,b_i), g_i est l'application f_{b_i} ; b) Si c_i=(a_i,0), g_i
    est l'extension canonique ḡ_{a_i} de g_{a_i} aux ensembles de parties ; c) Si
    c_i=(a_i,b_i) avec a_i,b_i≠0, g_i est l'extension canonique g_{a_i}×g_{b_i} à
    A_{a_i}×A_{b_i}.  Le dernier terme g_m est l'extension canonique, de schéma S,
    des applications f_1,…,f_n, désignée par ⟨f_1,…,f_n⟩^S. »

    `applis` = [f₁,…,fₙ] (Termes-objets).  Renvoie le Terme-objet ⟨f₁,…,fₙ⟩^S = g_m."""
    g: list = []
    for (a, b) in s.couples:
        if a == 0:
            g.append(applis[b - 1])                      # f_{b_i}
        elif b == 0:
            g.append(ext_parties(g[a - 1]))              # ḡ_{a_i}
        else:
            g.append(produit_applications(g[a - 1], g[b - 1]))  # g_{a_i} × g_{b_i}
    if not g:
        raise ValueError("schéma vide : aucune extension")
    return g[-1]


__all__ = [
    "Schema", "schema_valide", "schema_nb_termes",
    "schema_base", "schema_parties", "schema_produit", "schema_relation",
    "construction_echelon", "echelon",
    "ext_parties", "produit_applications", "extension_canonique",
]
