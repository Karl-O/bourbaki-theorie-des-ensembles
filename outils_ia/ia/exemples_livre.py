"""Couche 5 — corpus d'exemples : les démonstrations DU LIVRE, encodées en scripts.

Chaque entrée est une démonstration de Bourbaki (réellement présente dans le
texte) écrite dans le langage de script de `verificateur_preuve`, et **certifiée
par le noyau**. Double usage :
  * banc d'essai : tous les exemples doivent se vérifier (régression) ;
  * exemples pour une IA (« few-shot ») : on montre à un LLM comment ces preuves
    s'écrivent, à partir des vraies démonstrations du livre.

Format : (titre, but en notation lisible ascii, script).
"""
from __future__ import annotations

EXEMPLES: list[tuple[str, str, str]] = [
    (
        "C8 — A ⇒ A (via S1, S2, S4, modus ponens)  [E.I.~26]",
        "((a = b) => (a = b))",
        """
        t1 := S1 (a = b)
        t2 := S4 ((a = b) ou (a = b)) (a = b) (non (a = b))
        t3 := MP t1 t2
        t4 := S2 (a = b) (a = b)
        t5 := MP t4 t3
        """,
    ),
    (
        "A ⇒ A (via le théorème de la déduction C6)",
        "((a = b) => (a = b))",
        """
        h := hyp (a = b)
        g := ded (a = b) h
        """,
    ),
    (
        "Théorème 1 — réflexivité : x = x  [E.I.39]",
        "(x = x)",
        "r := refl x",
    ),
    (
        "Théorème 2 — symétrie : (x = y) ⇒ (y = x)  [E.I.40]",
        "((x = y) => (y = x))",
        "s := sym x y",
    ),
    (
        "Théorème 3 — transitivité : ((x = y) et (y = z)) ⇒ (x = z)  [E.I.40]",
        "(((x = y) et (y = z)) => (x = z))",
        "t := trans x y z",
    ),
    (
        "Syllogisme : de A⇒B et B⇒C, déduire A⇒C  (hyp. supposées)",
        "((a = b) => (c = d))",
        """
        ab := hyp ((a = b) => (b = c))
        bc := hyp ((b = c) => (c = d))
        ac := syll ab bc
        """,
    ),
    (
        "Tiers exclu : A ∨ ¬A",
        "((a = b) ou (non (a = b)))",
        "t := tiers (a = b)",
    ),
    (
        "Contraposition (théorème) : (A⇒B) ⇒ (¬B⇒¬A)",
        "(((a = b) => (c = d)) => ((non (c = d)) => (non (a = b))))",
        "c := contrapos (a = b) (c = d)",
    ),
]


def verifier_tous(sig=None):
    """Vérifie chaque exemple par le noyau. Renvoie [(titre, Rapport), ...]."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.i_1_app_lecture import DEFAUT
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_notation import lire_formule
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.verification.verificateur_preuve import executer_preuve
    sig = sig or DEFAUT
    resultats = []
    for titre, but_txt, script in EXEMPLES:
        but = lire_formule(but_txt, sig)
        resultats.append((titre, executer_preuve(script, but, sig)))
    return resultats


__all__ = ["EXEMPLES", "verifier_tous"]


if __name__ == "__main__":
    for titre, rap in verifier_tous():
        etat = "✓" if rap.succes else "✗"
        print(f"{etat}  {titre}")
        if not rap.succes:
            print(f"     → {rap}")
