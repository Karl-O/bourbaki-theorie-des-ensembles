"""Couche 3 — Tactiques (règles dérivées).

PDF p.~26--40, Bourbaki, Chap. I §3 (critères de la logique).

Chaque tactique **produit** un ``Theoreme`` du noyau — jamais une assertion.
Une tactique ne peut donc rien démontrer de faux : elle ne fait qu'enchaîner
des règles primitives, et le noyau vérifie chaque pas.

Deux statuts :
  * « constructive » : n'utilise que S1–S4 + MP (rien de plus que le noyau
    minimal) — n'ajoute RIEN à la base de confiance ;
  * « via C6 »        : utilise aussi la loi de déduction (primitive de
    confiance C6). Correcte, mais repose sur C6.
"""
from __future__ import annotations

from assemblage import Assemblage, negation, disjonction, implication, est_lettre
from lecture import Signature, DEFAUT, depuis_assemblage, vers_assemblage
import noyau
from noyau import Theoreme


# ── Décomposition utilitaire ──────────────────────────────────────────────────

def antecedent_consequent(impl: Assemblage, sig: Signature = DEFAUT
                          ) -> tuple[Assemblage, Assemblage]:
    """Décompose une implication A ⇒ B (= ∨ ¬A B) en (A, B)."""
    arbre = depuis_assemblage(impl, sig)
    if not (arbre.tete == "OU" and arbre.enfants[0].tete == "NON"):
        raise ValueError("ce n'est pas une implication ∨ ¬A B")
    a = vers_assemblage(arbre.enfants[0].enfants[0])
    b = vers_assemblage(arbre.enfants[1])
    return a, b


# ── Tactiques constructives (S1–S4 + MP uniquement) ───────────────────────────

def affaiblissement(thm: Theoreme, a: Assemblage, sig: Signature = DEFAUT) -> Theoreme:
    """Γ ⊢ X  ⟹  Γ ⊢ (A ⇒ X).  Constructive (S2, S3, MP).

    Preuve : X ⊢ X∨¬A (S2) ; X∨¬A ⊢ ¬A∨X (S3) ; or ¬A∨X = A⇒X.
    """
    x = thm.conclusion
    t_disj = noyau.modus_ponens(thm, noyau.s2(x, negation(a), sig), sig)  # Γ ⊢ X∨¬A
    t_comm = noyau.s3(x, negation(a), sig)                                # (X∨¬A)⇒(¬A∨X)
    return noyau.modus_ponens(t_disj, t_comm, sig)                        # Γ ⊢ A⇒X


# ── Tactiques via la loi de déduction (C6) ─────────────────────────────────────

def a_implique_a(a: Assemblage, sig: Signature = DEFAUT) -> Theoreme:
    """⊢ A ⇒ A.  Via C6 : de A⊢A par déduction.  (C8 chez Bourbaki.)"""
    return noyau.loi_deduction(a, noyau.assume(a, sig), sig)


def syllogisme(thm_ab: Theoreme, thm_bc: Theoreme, sig: Signature = DEFAUT) -> Theoreme:
    """⊢ A⇒B,  ⊢ B⇒C  ⟹  ⊢ A⇒C.  (Transitivité de ⇒, via C6.)

    Preuve : A ⊢ A ; MP avec A⇒B → A ⊢ B ; MP avec B⇒C → A ⊢ C ; déduction.
    """
    a, _ = antecedent_consequent(thm_ab.conclusion, sig)
    h = noyau.assume(a, sig)                       # A ⊢ A
    hb = noyau.modus_ponens(h, thm_ab, sig)        # A ⊢ B
    hc = noyau.modus_ponens(hb, thm_bc, sig)       # A ⊢ C
    return noyau.loi_deduction(a, hc, sig)         # ⊢ A⇒C


def distribution(thm_a_bc: Theoreme, thm_ab: Theoreme,
                 sig: Signature = DEFAUT) -> Theoreme:
    """⊢ A⇒(B⇒C),  ⊢ A⇒B  ⟹  ⊢ A⇒C.  (Combinateur S, via C6.)

    Preuve : A ⊢ A ; → A⊢B (MP thm_ab) ; → A⊢(B⇒C) (MP thm_a_bc) ;
             MP(A⊢B, A⊢B⇒C) → A⊢C ; déduction.
    """
    a, _ = antecedent_consequent(thm_ab.conclusion, sig)
    h = noyau.assume(a, sig)
    hb = noyau.modus_ponens(h, thm_ab, sig)        # A ⊢ B
    hbc = noyau.modus_ponens(h, thm_a_bc, sig)     # A ⊢ B⇒C
    hc = noyau.modus_ponens(hb, hbc, sig)          # A ⊢ C
    return noyau.loi_deduction(a, hc, sig)


def importation(a: Assemblage, b: Assemblage, c: Assemblage,
                sig: Signature = DEFAUT) -> Theoreme:
    """Règle d'enchaînement : de A⊢(B⇒C) on récupère ⊢ A⇒(B⇒C) etc.

    Ici, version pratique : ⊢ (A⇒B) ⇒ ((B⇒C) ⇒ (A⇒C)) — le syllogisme
    *internalisé* comme théorème clos, via trois déductions emboîtées.
    """
    hab = noyau.assume(implication(a, b), sig)     # (A⇒B) ⊢ (A⇒B)
    hbc = noyau.assume(implication(b, c), sig)     # (B⇒C) ⊢ (B⇒C)
    ha = noyau.assume(a, sig)                       # A ⊢ A
    hb = noyau.modus_ponens(ha, hab, sig)          # A, (A⇒B) ⊢ B
    hc = noyau.modus_ponens(hb, hbc, sig)          # A, (A⇒B), (B⇒C) ⊢ C
    t1 = noyau.loi_deduction(a, hc, sig)           # (A⇒B),(B⇒C) ⊢ A⇒C
    t2 = noyau.loi_deduction(implication(b, c), t1, sig)   # (A⇒B) ⊢ (B⇒C)⇒(A⇒C)
    return noyau.loi_deduction(implication(a, b), t2, sig) # ⊢ (A⇒B)⇒((B⇒C)⇒(A⇒C))


def mono_droite(thm_pq: Theoreme, c: Assemblage, sig: Signature = DEFAUT) -> Theoreme:
    """⊢ P⇒Q  ⟹  ⊢ (C∨P) ⇒ (C∨Q).  Constructive (S4 + MP)."""
    p, q = antecedent_consequent(thm_pq.conclusion, sig)
    return noyau.modus_ponens(thm_pq, noyau.s4(p, q, c, sig), sig)


def mono_gauche(thm_pq: Theoreme, c: Assemblage, sig: Signature = DEFAUT) -> Theoreme:
    """⊢ P⇒Q  ⟹  ⊢ (P∨C) ⇒ (Q∨C).  Constructive (S3 + S4 + syllogisme)."""
    p, q = antecedent_consequent(thm_pq.conclusion, sig)
    t1 = noyau.s3(p, c, sig)                    # (P∨C)⇒(C∨P)
    t2 = mono_droite(thm_pq, c, sig)            # (C∨P)⇒(C∨Q)
    t3 = noyau.s3(c, q, sig)                    # (C∨Q)⇒(Q∨C)
    return syllogisme(syllogisme(t1, t2, sig), t3, sig)


__all__ = [
    "antecedent_consequent", "affaiblissement",
    "a_implique_a", "syllogisme", "distribution", "importation",
    "mono_droite", "mono_gauche",
]
