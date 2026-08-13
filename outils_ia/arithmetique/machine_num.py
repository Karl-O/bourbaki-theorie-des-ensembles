"""Calcul certifié sur les numéraux — ordre, énumération, somme et produit.

────────────────────────────────────────────────────────────────────────────────
CE QUE CE MODULE APPORTE, ET POURQUOI IL EXISTE.

`numeraux.py` a montré que **ne pas reconstruire les TERMES** vaut un facteur 466.
Ce module est le second étage de la même leçon : **ne pas reconstruire les
THÉORÈMES GÉNÉRIQUES**.

Mesuré le 6 août 2026, coût NU des lemmes du dépôt, deux appels chacun (le second
révèle l'absence de mémoïsation) :

    somme_succ_distribue          11,9 s  puis 12,9 s
    produit_succ_distribue         7,6 s  puis  7,8 s
    somme_zero_neutre_droite       5,8 s  puis  6,3 s
    successeur_ordre               8,3 s  puis  5,2 s
    succ_pas_inf_egal              3,4 s  puis  3,3 s
    fini_implique_fini_successeur  9,3 s  puis  1,5 s

Aucun n'est mémoïsé : le travail était intégralement repayé à chaque pas.  Ici
chaque générique est construit UNE fois, généralisé UNE fois, et seule
l'INSTANCIATION est repayée.  Effet mesuré bout à bout :

    somme_num(3,3)          54,4 s → 27,5 s (à froid) → 0,000 s (rejoué)
    non_divise(2,3)        490,7 s → 0,3 s
    non_divise(2,7)   « pas de fin en 600 s » → 51,9 s

⚠️ RÈGLE QUI EN DÉCOULE.  Avant de déclarer un calcul impraticable dans ce noyau,
vérifier les DEUX étages : les sous-termes sont-ils partagés, les théorèmes
génériques sont-ils réutilisés ?  Trois « frontières de coût » annoncées pendant
la campagne arithmétique se sont dissoutes ainsi.

────────────────────────────────────────────────────────────────────────────────
CE QUE CE MODULE N'EST PAS.  Il ne démontre rien de neuf et ne change AUCUNE
preuve : mêmes règles, mêmes lemmes du dépôt, mêmes conclusions.  Aucun
`Theoreme` fabriqué, aucun monkeypatch ; `theorie_ensembles()` reste à 22
axiomes.  Chaque théorème rendu est vérifié à la construction (conclusion
attendue + clôture), jamais cru sur parole.

    NUM(k)             successeur^k(Card ∅)                      [terme, partagé]
    le_num(m,n)        ⊢ N(m) ≤ N(n)                             (m ≤ n)
    ne_num(m,n)        ⊢ ¬( N(m) = N(n) )                        (m < n)
    ex_falso / neg_intro / reecrit                               [gestes logiques]

L'énumération et le calcul (`enum`, `somme_num`, `produit_num`) vivent dans
`calcul_num.py`, qui consomme les génériques d'ici : une responsabilité par
fichier, et ce module-ci reste sous la barre des 300 lignes de code.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, egal, non,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    instancie, equivalence_avant,
)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
    symetrie,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    inf_egal_card,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux_theoremes import (
    inf_egal_reflexif,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_produit.ensembles_produit_petits import (
    produit_cardinal_zero,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers_theoremes import (
    fini_implique_cardinal,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_2_inegalites_ordre_soustraction.ensembles_successeur_ordre import (
    successeur_ordre, succ_pas_inf_egal, _inf_egal_monotone_successeur,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_recurrence_c61_existence_n.ensembles_recurrence_C61 import (
    b_le_0_implique_egal_0,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_1_somme_produit_entiers.ensembles_combinatoire_iii5 import (
    somme_succ_distribue, somme_zero_neutre_droite,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_1_somme_produit_entiers.ensembles_prop3_produit_entier_iii5 import (
    produit_succ_distribue,
)

#: LE cache des numéraux — un seul pour tout le projet (cf. `numeraux.py`).
from outils_ia.arithmetique.numeraux import num as NUM, fini as fini_num, cardinal_num as card_num

mp = N.modus_ponens

#: variable-trou pour les réécritures de Leibniz.  FRAÎCHE : aucun lieur du dépôt
#: ne porte ce nom, donc aucune capture possible.
_HOLE = "wmach"

# ══════════════════════════════════════════════════════════════════════════════
#  LES GÉNÉRIQUES, GÉNÉRALISÉS UNE SEULE FOIS  —  le cœur de l'accélération
# ══════════════════════════════════════════════════════════════════════════════
_GEN: dict[str, object] = {}


def _gen1(cle, build, x):
    """(∀x) thm(x), construit UNE fois pour toutes.

    ⚠️ La clôture est vérifiée AVANT de généraliser : généraliser sous hypothèse
    serait une faute de règle (la variable pourrait y être libre)."""
    if cle not in _GEN:
        th = build(x)
        assert th.est_clos, "%s : générique non clos, généralisation interdite" % cle
        _GEN[cle] = N.generalisation(x, th)
    return _GEN[cle]


def _gen2(cle, build, x1, x2):
    """(∀x1)(∀x2) thm(x1,x2), construit UNE fois pour toutes."""
    if cle not in _GEN:
        th = build(x1, x2)
        assert th.est_clos, "%s : générique non clos, généralisation interdite" % cle
        _GEN[cle] = N.generalisation(x1, N.generalisation(x2, th))
    return _GEN[cle]


def fic_t(t):
    """⊢ Fini(T) ⇒ est_cardinal(T), pour un TERME T quelconque."""
    return instancie(_gen1("fic", fini_implique_cardinal, "afic"), t)


def _refl_le_t(t):
    """⊢ T ≤ T."""
    return instancie(_gen1("refl", inf_egal_reflexif, "Xrefl"), t)


def _spie_t(t):
    """⊢ Fini(T) ⇒ ¬( T+1 ≤ T )."""
    return instancie(_gen1("spie", succ_pas_inf_egal, "bspie"), t)


def _ble0_t(t):
    """⊢ ( T ≤ 0 ) ⇒ ( T = 0 )."""
    return instancie(_gen1("ble0", b_le_0_implique_egal_0, "bl0"), t)


def _szn_t(ta):
    """⊢ est_cardinal(A) ⇒ A + 0 = A."""
    return instancie(_gen1("szn", somme_zero_neutre_droite, "Asz"), ta)


def _pcz_t(ta):
    """⊢ Card(A × ∅) = Card(∅)."""
    return instancie(_gen1("pcz", produit_cardinal_zero, "Apcz"), ta)


def _ssd_t(ta, tb):
    """⊢ (est_cardinal A et est_cardinal B) ⇒ A + (B+1) = (A+B) + 1."""
    return instancie(instancie(_gen2("ssd", somme_succ_distribue, "Asd", "Bsd"), ta), tb)


def _psd_t(ta, tn):
    """⊢ (est_cardinal A et est_cardinal N) ⇒ A·(N+1) = A·N + A."""
    return instancie(instancie(_gen2("psd", produit_succ_distribue, "Apsd", "Npsd"), ta), tn)


def _so_t(tx, tb):
    """⊢ est_cardinal(X) ⇒ ( (X ≤ B+1) ⟺ (X ≤ B ou X = B+1) ).

    ⚠️ `successeur_ordre` re-généralise à CHAQUE appel dans le dépôt (5,2 s
    mesurés au second appel) : on garde ici la généralisation, pas la preuve."""
    return instancie(instancie(_gen2("so", successeur_ordre, "xso", "bso"), tx), tb)


def _iems_t(tx, tb):
    """⊢ ( X ≤ B ) ⇒ ( X ≤ B+1 )."""
    return instancie(instancie(_gen2("iems", _inf_egal_monotone_successeur, "xiem", "biem"), tx), tb)


# ══════════════════════════════════════════════════════════════════════════════
#  OUTILS LOGIQUES  —  trois gestes qui reviennent partout
# ══════════════════════════════════════════════════════════════════════════════
def ex_falso(thm_p, thm_np, cible):
    """Γ ⊢ P  et  Δ ⊢ ¬P  ⟹  Γ∪Δ ⊢ cible   (n'importe quoi)."""
    return mp(thm_p, mp(thm_np, N.s2(non(thm_p.conclusion), cible)))


def neg_intro(f, thm_falso):
    """Γ ⊢ ¬F sous l'hypothèse F  ⟹  Γ\\{F} ⊢ ¬F.

    C'est S1 — (¬F ou ¬F) ⇒ ¬F — appliqué à l'implication F ⇒ ¬F, qui EST
    (¬F ou ¬F) puisque l'implication est abrégée."""
    return mp(N.loi_deduction(f, thm_falso), N.s1(non(f)))


def reecrit(thm_eq, thm_R, R, w=_HOLE):
    """⊢ t = u  et  ⊢ R[w:=t]  ⟹  ⊢ R[w:=u]   (Leibniz, S6)."""
    t, u = thm_eq.conclusion.termes
    return mp(thm_R, equivalence_avant(mp(thm_eq, N.s6(t, u, w, R))))


def existe_temoin_verifie(temoin_thm, corps, temoin, lieur):
    """Γ ⊢ (T|x)corps  ⟹  Γ ⊢ (∃x) corps   —   ∃-intro par témoin VÉRIFIÉ (S5).

    LA tactique désignée le 6 août 2026 par la convergence de DEUX instruments
    aveugles l'un à l'autre : l'indexation WL des formules et l'anti-unification
    des preuves ont pointé le même motif, réécrit ≥5 fois à la main pendant la
    campagne Goldbach (divisibilité positive, parité positive, branches de
    décomposition, multiples).  Le geste : prouver l'instance au témoin, VÉRIFIER
    que sa conclusion est exactement (T|x)corps — c'est le garde-fou qui attrape
    les matrices mal formées AVANT le noyau — puis introduire l'existentielle.

    ⚠️ `subst_f` suit l'ordre de Bourbaki (T|x)R : subst_f(TERME, nom, FORMULE)."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
        existe, subst_f,
    )
    assert temoin_thm.conclusion == subst_f(temoin, lieur, corps), (
        "existe_temoin_verifie : la conclusion du témoin n'est pas (T|%s)corps "
        "— matrice mal formée ou mauvais témoin" % lieur)
    r = mp(temoin_thm, N.s5(corps, temoin, lieur))
    assert r.conclusion == existe(lieur, corps)
    return r


# ══════════════════════════════════════════════════════════════════════════════
#  ORDRE ET DISTINCTION DES NUMÉRAUX
# ══════════════════════════════════════════════════════════════════════════════
_LE, _NE, _NES = {}, {}, {}


def le_num(m, n):
    """⊢ N(m) ≤ N(n)   (pour m ≤ n).  Réflexivité, puis monotonie du successeur."""
    assert m <= n, "le_num : m <= n attendu"
    if (m, n) not in _LE:
        r = _refl_le_t(NUM(m)) if m == n else mp(le_num(m, n - 1), _iems_t(NUM(m), NUM(n - 1)))
        assert r.conclusion == inf_egal_card(NUM(m), NUM(n)) and r.est_clos
        _LE[(m, n)] = r
    return _LE[(m, n)]


# Gate paramétré du volant (7 août 2026) — instances canoniques + caches déclarés.
le_num_gate_caches = ("_LE",)


def le_num_instances():
    """Instances canoniques : (args, énoncé attendu par ==)."""
    return [((1, 2), inf_egal_card(NUM(1), NUM(2))),
            ((2, 2), inf_egal_card(NUM(2), NUM(2)))]


def ne_num(m, n):
    """⊢ ¬( N(m) = N(n) )   (pour m < n).

    Si N(m) = N(n), alors de N(m+1) ≤ N(n) et de Leibniz on tire N(m+1) ≤ N(m) —
    ce que `succ_pas_inf_egal` interdit sous Fini(N(m))."""
    assert m < n, "ne_num : m < n attendu"
    if (m, n) not in _NE:
        h = N.assume(egal(NUM(m), NUM(n)))
        bad = reecrit(mp(h, symetrie(NUM(m), NUM(n))), le_num(m + 1, n),
                      inf_egal_card(NUM(m + 1), var(_HOLE)))
        falso = ex_falso(bad, mp(fini_num(m), _spie_t(NUM(m))),
                         non(egal(NUM(m), NUM(n))))
        r = neg_intro(egal(NUM(m), NUM(n)), falso)
        assert r.conclusion == non(egal(NUM(m), NUM(n))) and r.est_clos
        _NE[(m, n)] = r
    return _NE[(m, n)]


def ne_num_sym(m, n):
    """⊢ ¬( N(n) = N(m) )   (pour m < n)."""
    if (m, n) not in _NES:
        h = N.assume(egal(NUM(n), NUM(m)))
        falso = ex_falso(mp(h, symetrie(NUM(n), NUM(m))), ne_num(m, n),
                         non(egal(NUM(n), NUM(m))))
        r = neg_intro(egal(NUM(n), NUM(m)), falso)
        assert r.conclusion == non(egal(NUM(n), NUM(m))) and r.est_clos
        _NES[(m, n)] = r
    return _NES[(m, n)]


ne_num_sym_gate_caches = ("_NES",)


def ne_num_sym_instances():
    """Instances canoniques : (args, énoncé attendu par ==)."""
    return [((1, 2), non(egal(NUM(2), NUM(1)))),
            ((0, 3), non(egal(NUM(3), NUM(0))))]


def ne_num_quelconque(a, b):
    """⊢ ¬( N(a) = N(b) )  pour a ≠ b quelconques (choisit le sens)."""
    assert a != b, "ne_num_quelconque : a != b attendu"
    return ne_num(a, b) if a < b else ne_num_sym(b, a)


__all__ = ["NUM", "fini_num", "card_num", "fic_t", "ex_falso", "neg_intro", "reecrit",
           "existe_temoin_verifie", "le_num", "ne_num", "ne_num_sym",
           "ne_num_quelconque"]
