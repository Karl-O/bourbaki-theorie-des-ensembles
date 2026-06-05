"""Couche 5 — « brouillon + vérification » : exécuter une preuve PROPOSÉE.

Principe neuro-symbolique : une IA (ou n'importe quelle source) propose une
preuve sous forme de script ; ce module la rejoue **pas à pas dans le noyau**.
Soit elle la certifie (théorème vérifié), soit elle indique la **ligne exacte**
qui échoue. L'IA ne peut donc rien prouver de faux : elle ne fait que proposer.

Interface AGNOSTIQUE : `executer_preuve` prend une chaîne de script (d'où qu'elle
vienne). `prouver_par_llm` prend un *proposeur* `str -> str` ; le brancher sur
Claude plus tard est un simple remplacement de cette fonction.

Langage de script (une étape par ligne) :

    nom := REGLE arg1 arg2 ...

Les formules sont parenthésées (cf. notation.py). Règles disponibles :

  Noyau   : hyp (F) | S1 (F) | S2 (F)(F) | S3 (F)(F) | S4 (F)(F)(F)
            | S5 (R)(T) x | S6 (T)(U) x (R) | S7 (R)(S) x
            | MP nomA nomImpl | ded (F) nom | gen x nom
  Macros  : aia (F)            (⊢ A⇒A)            | syll nomAB nomBC
  (livre)   refl x | sym x y | trans x y z         (réflex./sym./transit. de =)

Un argument `(F)` est une formule, `x` une lettre, `nom` un pas précédent.
La dernière ligne (ou un pas de l'env) doit conclure le but.
"""
from __future__ import annotations
from dataclasses import dataclass

from lecture import Signature, DEFAUT
import noyau
from tactiques import a_implique_a, syllogisme
from tactiques_prop import tiers_exclu, contraposition_theoreme
from tactiques_egalite import reflexivite, symetrie, transitivite
from notation import _TOKEN, _parse, ErreurNotation, afficher

# Règle -> (fonction, sortes d'arguments). 'F' = formule, 'x' = lettre, 'T' = pas.
REGLES: dict = {
    "hyp": (noyau.assume, ["F"]),
    "S1": (noyau.s1, ["F"]),
    "S2": (noyau.s2, ["F", "F"]),
    "S3": (noyau.s3, ["F", "F"]),
    "S4": (noyau.s4, ["F", "F", "F"]),
    "S5": (noyau.s5, ["F", "F", "x"]),
    "S6": (noyau.s6, ["F", "F", "x", "F"]),
    "S7": (noyau.s7, ["F", "F", "x"]),
    "MP": (noyau.modus_ponens, ["T", "T"]),
    "ded": (noyau.loi_deduction, ["F", "T"]),
    "gen": (noyau.generalisation, ["x", "T"]),
    "aia": (a_implique_a, ["F"]),
    "syll": (syllogisme, ["T", "T"]),
    "tiers": (tiers_exclu, ["F"]),
    "contrapos": (contraposition_theoreme, ["F", "F"]),
    "refl": (reflexivite, ["x"]),
    "sym": (symetrie, ["x", "x"]),
    "trans": (transitivite, ["x", "x", "x"]),
}


@dataclass
class Rapport:
    """Verdict de vérification d'une preuve proposée."""
    succes: bool
    theoreme: object = None
    ligne_echec: int | None = None
    message: str = ""

    def __repr__(self) -> str:
        if self.succes:
            return f"✓ vérifié : {self.theoreme!r}"
        loc = f" (ligne {self.ligne_echec})" if self.ligne_echec else ""
        return f"✗ échec{loc} : {self.message}"


def executer_preuve(script: str, but, sig: Signature = DEFAUT) -> Rapport:
    """Rejoue le script dans le noyau. Renvoie un Rapport (certifié ou ligne fautive)."""
    env: dict = {}
    derniere = None
    for no, brute in enumerate(script.splitlines(), 1):
        ligne = brute.split("#", 1)[0].strip()
        if not ligne:
            continue
        if ":=" not in ligne:
            return Rapport(False, None, no, "ligne sans ':='")
        nom, reste = ligne.split(":=", 1)
        toks = _TOKEN.findall(reste)
        if not toks:
            return Rapport(False, None, no, "règle manquante")
        regle, toks = toks[0], toks[1:]
        if regle not in REGLES:
            return Rapport(False, None, no, f"règle inconnue : {regle!r}")
        fn, sortes = REGLES[regle]
        try:
            args, i = [], 0
            for sorte in sortes:
                if sorte == "F":
                    a, i = _parse(toks, i)
                    args.append(a)
                elif sorte == "T":
                    args.append(env[toks[i]]); i += 1
                else:  # 'x' : lettre brute
                    args.append(toks[i]); i += 1
            thm = fn(*args)
        except (ValueError, KeyError, IndexError, ErreurNotation) as e:
            return Rapport(False, None, no, f"{regle} : {e}")
        env[nom.strip()] = thm
        derniere = thm

    if derniere is None:
        return Rapport(False, None, None, "preuve vide")
    if derniere.conclusion == but:
        return Rapport(True, derniere, None, "preuve vérifiée")
    for thm in env.values():
        if thm.conclusion == but:
            return Rapport(True, thm, None, "preuve vérifiée (pas intermédiaire)")
    return Rapport(False, derniere, None, "aucun pas ne conclut le but")


def prouver_par_llm(but, proposeur, sig: Signature = DEFAUT, essais: int = 1) -> Rapport:
    """Demande un script à `proposeur` (str→str) puis le vérifie. Hook IA/LLM.

    `proposeur` reçoit le but en notation lisible et renvoie un script. En test,
    on lui passe une fonction qui retourne un script codé en dur (LLM simulé) ;
    en production, une fonction qui interroge Claude. Le noyau vérifie dans les
    deux cas — un mauvais proposeur ne peut produire qu'un échec, jamais un faux.
    """
    but_txt = afficher(but, sig)
    rapport = Rapport(False, None, None, "aucun essai")
    for _ in range(max(1, essais)):
        script = proposeur(but_txt)
        rapport = executer_preuve(script, but, sig)
        if rapport.succes:
            return rapport
    return rapport


__all__ = ["Rapport", "executer_preuve", "prouver_par_llm", "REGLES"]
