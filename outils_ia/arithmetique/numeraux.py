"""Numéraux mémoïsés — et la mesure qui justifie ce module.

────────────────────────────────────────────────────────────────────────────────
LE FAIT, MESURÉ LE 5 AOÛT 2026.  Construire ⊢ Fini(N(11)) par itération de
`fini_implique_fini_successeur` depuis `fini_zero` coûte :

    sans cache des numéraux : 559,7 s
    avec cache des numéraux :   1,2 s        ← facteur 466

**La preuve est la MÊME.**  Mêmes règles, même théorème, mêmes 0 hypothèses.  La
seule différence est que `N(k)` est mémoïsé au lieu d'être rebâti à chaque appel.

────────────────────────────────────────────────────────────────────────────────
POURQUOI L'ÉCART EST SI GRAND.  Un numéral `N(k) = successeur^k(Card ∅)` est un
τ-terme dont la taille explose avec k.  Le reconstruire à chaque tour donne deux
coûts qui se composent : la construction elle-même est quadratique en k, et
surtout les sous-termes ne sont plus PARTAGÉS — or l'égalité et le hachage du
noyau sont bon marché sur des objets partagés et ruineux sur des copies.  Chaque
`instancie` et chaque comparaison repayaient donc l'arbre entier.

⚠️ CONSÉQUENCE À RETENIR.  Un chantier arithmétique peut paraître hors de portée
alors qu'il est instantané : nous avons annoncé une « frontière du coût » qui
n'existait pas, et qui n'était que cette construction naïve.  Avant de déclarer
un calcul impraticable dans ce noyau, vérifier que les termes sont partagés.

────────────────────────────────────────────────────────────────────────────────
CE QUE CE MODULE N'EST PAS.  Il ne démontre rien de neuf : tout ce qu'il rend est
déjà dérivable par le corpus.  Il ne postule rien, ne touche pas au noyau, et
`theorie_ensembles()` reste à 22 axiomes.  C'est un accélérateur, et les
théorèmes qu'il rend sont vérifiés à la construction (conclusion attendue,
clôture) plutôt que crus sur parole.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import (
    noyau_abrege as N,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    instancie,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    est_cardinal,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (
    est_fini, successeur, ZERO,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_fini_zero import (
    fini_zero,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_fini_successeur import (
    fini_implique_fini_successeur,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers_theoremes import (
    fini_implique_cardinal,
)

#: LE cache qui vaut le facteur 466 — les numéraux partagent leurs sous-termes.
_NUM: dict[int, object] = {0: ZERO}
_FINI: dict[int, object] = {}
_CARD: dict[int, object] = {}

#: les deux implications génériques, généralisées UNE fois pour toutes.
_FIFS = None
_FIC = None


def num(k: int):
    """Le numéral N(k) = successeur^k(Card ∅), mémoïsé.

    ⚠️ Ne jamais reconstruire un numéral hors de cette fonction : c'est le partage
    des sous-termes qui rend tout le reste praticable (cf. l'en-tête)."""
    if k < 0:
        raise ValueError("num : k doit être positif ou nul")
    if k not in _NUM:
        _NUM[k] = successeur(num(k - 1))
    return _NUM[k]


def _fifs(t):
    """⊢ Fini(T) ⇒ Fini(T+1), pour un TERME T."""
    global _FIFS
    if _FIFS is None:
        _FIFS = N.generalisation("afifs", fini_implique_fini_successeur("afifs"))
    return instancie(_FIFS, t)


def _fic(t):
    """⊢ Fini(T) ⇒ est_cardinal(T), pour un TERME T."""
    global _FIC
    if _FIC is None:
        _FIC = N.generalisation("afic", fini_implique_cardinal("afic"))
    return instancie(_FIC, t)


def fini(k: int):
    """⊢ Fini( N(k) ).  CLOS, pour k arbitraire.

    Itère l'implication close `fini_implique_fini_successeur` depuis `fini_zero`.
    Chaque étage est mémoïsé, donc le k-ième appel ne repaie pas les précédents."""
    if k not in _FINI:
        r = fini_zero() if k == 0 else N.modus_ponens(fini(k - 1), _fifs(num(k - 1)))
        assert r.conclusion == est_fini(num(k)), f"fini({k}) : conclusion inattendue"
        assert r.est_clos, f"fini({k}) : devrait être clos"
        _FINI[k] = r
    return _FINI[k]


def cardinal_num(k: int):
    """⊢ est_cardinal( N(k) ).  CLOS."""
    if k not in _CARD:
        r = N.modus_ponens(fini(k), _fic(num(k)))
        assert r.conclusion == est_cardinal(num(k)), f"cardinal_num({k}) : inattendu"
        assert r.est_clos, f"cardinal_num({k}) : devrait être clos"
        _CARD[k] = r
    return _CARD[k]


# Gate paramétré du volant (7 août 2026) : instances canoniques PETITES, énoncés
# par combinateurs (jamais en re-prouvant) ; caches déclarés pour le voile du gate.
fini_gate_caches = ("_FINI",)


def fini_instances():
    """Instances canoniques : (args, énoncé attendu par ==)."""
    return [((2,), est_fini(num(2))), ((3,), est_fini(num(3)))]


cardinal_num_gate_caches = ("_CARD",)


def cardinal_num_instances():
    return [((2,), est_cardinal(num(2))), ((3,), est_cardinal(num(3)))]


def vider_caches():
    """Remet les caches à zéro.

    🔴 PIÈGE MESURÉ LE 5 AOÛT 2026 — NE PAS UTILISER POUR CHRONOMÉTRER.
    Vider les caches en cours de processus remet les numéraux à neuf, mais les
    théorèmes déjà construits tiennent les ANCIENS termes.  Toute comparaison
    ultérieure croise alors du partagé et du non-partagé, et repaie l'arbre τ
    entier — exactement la pathologie que ce module existe pour éviter.  Mesuré :
    un fichier de tests dont chaque test passait isolément (~40 s au total) ne
    terminait plus du tout, même après 50 minutes.

    Pour mesurer un coût de première construction, lancer un **process neuf**
    (cf. `tests/outils_ia/test_numeraux.py`).  Un « à froid » observé dans un
    process déjà chaud n'est pas un à froid.

    ⚠️ Vaut aussi pour l'instrument de dette : `Ax(D)` est aveugle à ce qui sort
    d'un cache, donc toute mesure de dette se fait en process frais."""
    _NUM.clear()
    _NUM[0] = ZERO
    _FINI.clear()
    _CARD.clear()


__all__ = ["num", "fini", "cardinal_num", "vider_caches"]
