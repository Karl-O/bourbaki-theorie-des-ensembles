"""Pont-α DÉRIVÉ — transporter ⊢ F vers ⊢ G quand F et G sont α-équivalentes.

────────────────────────────────────────────────────────────────────────────────
PROBLÈME (le « verrou de liants »).  Le noyau abrégé compare les conclusions par
`==` STRICT (égalité structurelle, liants compris).  Or deux formules peuvent être
α-équivalentes (`formule.alpha_egal` True) sans être `==` : il suffit qu'un liant
porte un autre NOM.  C'est exactement ce qui se produit quand on prouve une
injectivité avec des liants SÛRS (m0, m0p — choisis pour ne PAS collisionner avec
les τ-liants internes de NN / successeur) alors que la cible `est_injection_de(…)`
exige la forme PAR DÉFAUT (liants u, up fixés par `injective_dans`).  Un simple
`alpha_pour_tout(m0, u, R)` échoue : `subst_f(var("u"), "m0", R)` déclenche le
capture-évitement qui RENOMME les liants internes « u » (dans NN) en « @0 », donc
le résultat est α-équivalent à la cible mais STRUCTURELLEMENT distinct.

────────────────────────────────────────────────────────────────────────────────
SOLUTION (DÉRIVÉE, SANS NOUVELLE PRIMITIVE — noyau INCHANGÉ, theorie=22).

On CONSTRUIT le théorème d'équivalence `⊢ F ⇔ G` par récursion structurelle sur la
forme commune (à α-près) de F et G, puis on conclut `⊢ G` par modus ponens.  Chaque
brique est une tactique déjà certifiée :

  • atomes / sous-formules IDENTIQUES (`==`)        → réflexivité `⊢ A ⇔ A` ;
  • ¬, ∨ (donc ⇒, et, ⇔ qui en dérivent)            → `equiv_neg`, `ou_congruence` ;
  • liant ∃ de MÊME nom                              → `congruence_existe` ;
  • liant ∃ de noms DIFFÉRENTS (a vs b)             → on renomme LES DEUX vers un nom
        FRAIS EXOTIQUE c (= `_fraiche`, jamais un liant interne) via `alpha_existe`
        — `subst_f(var(c), a, ·)` ne touche AUCUN liant interne (c est neuf), donc
        PAS de @0-injection — puis on recolle par transitivité de ⇔.

L'astuce-clé du COURT-CIRCUIT : dès que les deux branches sont `==`, on renvoie la
réflexivité sans descendre.  Les τ-termes profonds (NN, successeur, …) sont
IDENTIQUES dans F et G (seuls les liants de l'ÉPINE diffèrent), donc la récursion ne
travaille QUE le long de cette épine — coût O(profondeur de l'épine), pas O(taille).

SOUNDNESS.  Toutes les briques (`alpha_existe`, `congruence_existe`, `equiv_neg`,
`ou_congruence`, `equivalence_transitivite`, `a_implique_a`, réflexivité de ⇔) sont
DÉRIVÉES des schémas S1–S7 / C6 / C27 déjà vérifiés ; aucune n'ajoute de confiance.
Le pont ne fabrique JAMAIS une équivalence fausse : il REFUSE (`ValueError`) si F et
G ne sont pas α-équivalentes, et chaque pas de la récursion produit une équivalence
réellement démontrée par le noyau.

PORTÉE.  `alpha_bridge` est GÉNÉRAL pour les renommages de liants ∃/∀ et la
congruence propositionnelle (¬, ∨, ⇒, et, ⇔, ∀, ∃).  Limite documentée : il NE
traite PAS les différences α PORTÉES PAR UN τ-LIANT INTERNE À UN TERME d'un atome
(= / ∈) — c.-à-d. quand deux atomes α-équivalents diffèrent par le NOM d'un τ-liant
sous un terme.  Ce cas n'apparaît pas pour le verrou ℵ₀ (les atomes deviennent
`==` après alignement de l'épine) ; il lève une `ValueError` explicite si rencontré.
"""
from __future__ import annotations

from bourbaki.logique.formule import (
    Formule, Terme, var, tau, subst_f, alpha_egal,
)
from bourbaki.logique import noyau_abrege as N
from bourbaki.logique.tactiques.tactiques_abrege import a_implique_a, syllogisme
from bourbaki.logique.tactiques.tactiques_abrege2 import (
    conjonction_intro, equiv_neg, ou_congruence, equivalence_transitivite,
    equivalence_symetrie, equivalence_avant,
)
from bourbaki.logique.tactiques.tactiques_abrege_quantif import (
    congruence_existe, existe_elimination,
)


def _vars_t(t: Terme, acc: set) -> None:
    """Collecte TOUTES les variables d'un terme — LIBRES *ET* LIÉES (liants τ inclus)."""
    if t.tag == "var":
        acc.add(t.nom)
    elif t.tag == "tau":
        acc.add(t.lieur)                 # liant τ (capital : on l'évite aussi)
        _vars_f(t.args[0], acc)
    else:                                # 'app'
        for a in t.args:
            _vars_t(a, acc)


def _vars_f(f: Formule, acc: set) -> None:
    """Collecte TOUTES les variables d'une formule — LIBRES *ET* LIÉES (∃ inclus)."""
    for t in f.termes:
        _vars_t(t, acc)
    if f.tag == "exists":
        acc.add(f.lieur)                 # liant ∃
    for g in f.sous:
        _vars_f(g, acc)


def _fraiche_totale(fs) -> str:
    """Nom EXOTIQUE « @k » évitant TOUTES les variables (libres ET liées) des formules fs.

    `formule._fraiche` n'évite que les variables LIBRES ; or les τ-termes profonds (NN,
    successeur) contiennent des liants INTERNES « @0 » (issus d'un capture-évitement
    antérieur).  Renommer un liant ∃ vers un tel « @0 » déclencherait à nouveau le
    capture-évitement (→ structure divergente).  On évite donc AUSSI les liants."""
    eviter = set()
    for f in fs:
        _vars_f(f, eviter)
    k = 0
    while True:
        c = "@" + str(k)
        if c not in eviter:
            return c
        k += 1


def _refl_equiv(f: Formule):
    """⊢ F ⇔ F   (réflexivité de l'équivalence : (F⇒F) et (F⇒F))."""
    aa = a_implique_a(f)
    return conjonction_intro(aa, aa)


def _alpha_existe_exact(b: str, c: str, gb: Formule):
    """⊢ (∃b)gb ⇔ (∃c)(c|b)gb,   AVEC LES DEUX CÔTÉS STRUCTURELLEMENT EXACTS.

    `tactiques_abrege_quantif.alpha_existe` n'est PAS fiable ici : son sens DIRECT
    passe par le ROND-TRIP `(b|c)(c|b)gb`, et si le NOM b coïncide avec un τ-liant
    INTERNE à gb (cas du verrou : la cible lie « u » alors que NN/successeur lient « u »
    en interne), la deuxième substitution re-substitue « b » → le capture-évitement
    renomme le liant interne en « @k » → résultat α-équivalent mais ≠ structurellement.

    On reconstruit donc les deux implications SANS rond-trip, à partir des SEULES
    primitives S5 et témoin-∃ (existe_temoin), dont la sortie est exacte :
      • SENS DIRECT  (∃b)gb ⇒ (∃c)(c|b)gb :
            existe_temoin(gb,b) : (∃b)gb ⇒ (W|b)gb   où W = τb(gb) ;
            s5((c|b)gb, W, c)   : (W|c)(c|b)gb ⇒ (∃c)(c|b)gb ;
            or (W|c)(c|b)gb = (W|b)gb  (c neuf ⇒ pas de capture) → syllogisme.
      • SENS RÉCIPROQUE  (∃c)(c|b)gb ⇒ (∃b)gb :
            s5(gb, var(c), b) : (c|b)gb ⇒ (∃b)gb ;  existe_elimination(·, c).
    Les deux sens ne substituent JAMAIS le nom b (qui collisionne) — seul c (neuf) et
    le témoin canonique W interviennent, donc AUCUNE @k-injection.  SOUND (S5, témoin-∃,
    existe_elimination sont déjà certifiés)."""
    gb_c = subst_f(var(c), b, gb)                # (c|b)gb
    W = tau(b, gb)                               # témoin canonique τb(gb)
    fwd = syllogisme(N.existe_temoin(gb, b), N.s5(gb_c, W, c))   # (∃b)gb ⇒ (∃c)(c|b)gb
    bwd = existe_elimination(N.s5(gb, var(c), b), c)             # (∃c)(c|b)gb ⇒ (∃b)gb
    return conjonction_intro(fwd, bwd)


def bridge_equiv(f: Formule, g: Formule):
    """⊢ F ⇔ G,  pour F, G α-ÉQUIVALENTES  (DÉRIVÉ, noyau intact).

    Récursion structurelle sur la forme commune (à α-près).  Court-circuit `==`."""
    if f == g:                                   # branches identiques → réflexivité
        return _refl_equiv(f)
    if not alpha_egal(f, g):
        raise ValueError("bridge_equiv : F et G ne sont PAS α-équivalentes")
    if f.tag != g.tag:
        raise ValueError(f"bridge_equiv : structures incompatibles ({f.tag} vs {g.tag})")

    if f.tag == "non":
        return equiv_neg(bridge_equiv(f.sous[0], g.sous[0]))

    if f.tag == "ou":
        return ou_congruence(bridge_equiv(f.sous[0], g.sous[0]),
                             bridge_equiv(f.sous[1], g.sous[1]))

    if f.tag == "exists":
        a, fb = f.lieur, f.sous[0]
        b, gb = g.lieur, g.sous[0]
        if a == b:                               # même liant → congruence directe
            return congruence_existe(bridge_equiv(fb, gb), a)
        # liants distincts : on renomme LES DEUX vers un nom FRAIS EXOTIQUE c, évitant
        # TOUTES les variables (libres ET liées) des deux corps — sinon un liant ∃ pourrait
        # tomber sur un liant interne « @k » et re-déclencher le capture-évitement.
        c = _fraiche_totale((fb, gb))            # « @k » — jamais un liant (même interne)
        fb_c = subst_f(var(c), a, fb)            # (c|a)Fb  (c neuf ⇒ pas de @-injection)
        gb_c = subst_f(var(c), b, gb)            # (c|b)Gb
        eq_f = _alpha_existe_exact(a, c, fb)     # (∃a)Fb ⇔ (∃c)(c|a)Fb  (exact des 2 côtés)
        eq_g = _alpha_existe_exact(b, c, gb)     # (∃b)Gb ⇔ (∃c)(c|b)Gb  (exact des 2 côtés)
        eq_mid = congruence_existe(bridge_equiv(fb_c, gb_c), c)  # (∃c)(c|a)Fb ⇔ (∃c)(c|b)Gb
        # (∃a)Fb ⇔ (∃c)(c|a)Fb ⇔ (∃c)(c|b)Gb ⇔ (∃b)Gb
        chaine = equivalence_transitivite(eq_f, eq_mid)
        return equivalence_transitivite(chaine, equivalence_symetrie(eq_g))

    # atomes = / ∈ : ils sont α-équivalents mais ≠ → différence α SOUS un τ-terme.
    raise ValueError(
        f"bridge_equiv : atome α-équivalent non structurellement égal (tag={f.tag}) "
        "— différence portée par un τ-liant interne à un terme ; hors de portée du pont."
    )


def alpha_bridge(thm: N.Theoreme, cible: Formule) -> N.Theoreme:
    """De ⊢ F (= thm) et G (= cible) α-équivalente, déduire ⊢ G.   (DÉRIVÉ.)

    Construit ⊢ F ⇔ G (`bridge_equiv`) puis applique modus ponens (sens ⇒).
    Préserve les hypothèses de `thm`.  Lève `ValueError` si F et G ne sont pas
    α-équivalentes ou si la différence est hors de portée (cf. docstring module)."""
    f = thm.conclusion
    if f == cible:
        return thm                               # déjà la cible : rien à faire
    eq = bridge_equiv(f, cible)                   # ⊢ F ⇔ G  (clos)
    res = N.modus_ponens(thm, equivalence_avant(eq))  # ⊢ G  (hyps de thm préservées)
    assert res.conclusion == cible, "alpha_bridge : conclusion ≠ cible (bug interne)"
    return res


__all__ = ["bridge_equiv", "alpha_bridge"]
