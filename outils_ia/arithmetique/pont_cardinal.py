"""PONT DE CARDINALITÉ — Card(m ⊔ m) = Card(Card m ⊔ Card m) pour un TERME m QUELCONQUE.

    |-  somme_cardinale_binaire(m, m)  =  somme_cardinale_binaire(Card m, Card m)

en clair (afficher_f) :   ( cardinal(sd(m, m)) = cardinal(sd(cardinal(m), cardinal(m))) )
où sd = somme_disjointe.  THÉORÈME CLOS : 0 hypothèse, m n'a PAS besoin d'être un cardinal.

────────────────────────────────────────────────────────────────────────────────
POURQUOI.  « n est pair » s'écrit (∃m)(n = m + m) où m est un ENSEMBLE quelconque,
pas un cardinal ; les lemmes d'ordre cardinal ne s'y appliquent donc pas.  Ce pont
ramène m à Card m, qui EST un cardinal — c'est la pièce qui permettra d'écrire
Goldbach borné sur n plutôt que sur la moitié k.

────────────────────────────────────────────────────────────────────────────────
PREUVE — aucune brique neuve, assemblage de DEUX acquis du dépôt.

 (1) `somme_disjointe_cardinal(X, Y, a, b)`  (ensembles_arith_somme, CLOS) :
         |- (Card X = a et Card Y = b) => Card(X ⊔ Y) = somme_cardinale_binaire(a, b)
     — la « forme finale bien-définie » de la somme cardinale.  Elle accepte des
     TERMES quelconques en X, Y, a, b.
 (2) On l'instancie en  X := Y := m,  a := b := Card m.  L'antécédent devient
     (Card m = Card m et Card m = Card m), déchargé par la RÉFLEXIVITÉ
     (Théorème 1, E.I.39 — N.reflexivite) et conjonction_intro ; modus ponens.
 (3) La conclusion est littéralement Card(m ⊔ m) = Card(Card m ⊔ Card m), car
     somme_cardinale_binaire(a, b) EST cardinal(somme_disjointe(a, b)) par
     définition (vérifié au lancement, pas supposé).

────────────────────────────────────────────────────────────────────────────────
HYGIÈNE DES LIANTS — la vraie difficulté, MESURÉE.

Appliquer (1)-(2) DIRECTEMENT au terme m fourni par l'appelant échoue dès que m
contient une variable libre homonyme d'un liant interne du keystone
`eq_somme_invariant` / `somme_graphe_image`.  Sonde `probe_liants.py`, 37 noms :

    OK      n a b c d e f g h i j r K X Y A B M mm mzz          (20/37)
    ÉCHEC   m z u v w x F           modus ponens : mineure ≠ antécédent
            t k y p q yb            't' libre dans C : (∃x)C ⇒ C invalide
            m1 m2                   renommage-α invalide : 'm1' libre dans R
            G s                     généralisation : 'G' libre dans une hypothèse

Cause exacte, pour m = var("m") : `somme_graphe_image` (ensembles_somme_equipotence
ligne 704) construit la coordonnée du graphe avec le liant « m »
(`membre_graphe_terme(AB, T, "t", "m", "k", "yb")` puis `N.generalisation("m", mem)`) ;
un « m » libre dans AB = m ⊔ m y est CAPTURÉ, la mineure ne colle plus à
l'antécédent, et le noyau refuse — noyau_abrege.py:160.

REMÈDE (idiome du dépôt, cf. `_prop1_direct_t`) : démontrer le pont UNE fois sur un
nom VÉRIFIÉ frais (« mzz »), GÉNÉRALISER (C27), puis INSTANCIER (C30) au terme voulu.
La substitution finale se fait hors de toute machinerie à liants, donc AUCUN nom
n'est plus interdit — et le coût de la preuve n'est payé qu'une seule fois
(≈2,7 s à froid, ≈0 s ensuite ; mesuré, deux appels).

────────────────────────────────────────────────────────────────────────────────
SECONDE CAPTURE, PLUS SUBTILE — c'est la CIBLE naïve qui est fausse, pas le théorème.

`cardinal(X) := τ_Z(Eq(X, Z))` et le corps de Eq lie **F, Z, u, up, v, y, z**
(LIANTS_CARD, calculé par le script, pas recopié).  Écrire la cible par appel
DIRECT — `cardinal(somme_disjointe(m, m))` — CAPTURE donc ces lettres si m les a
libres.  Pour m = {u} ∪ {v}, la conclusion du noyau et cette cible directe
diffèrent (diag_capture.py) — et ce n'est pas un désaccord α : `libres` coïncident
mais les formules non, parce que la cible directe a réellement lié les u, v de m.
C'est `instancie` qui a raison : subst_t renomme (on lit `(∀@0)` dans la sortie).

Donc la cible de référence est la cible substituée :
    cible_pont(m) = subst_f(m, "mzz", cible_pont_directe(var("mzz")))
(ordre de Bourbaki (T|x)R : subst_f(TERME, nom_var, FORMULE)).
`cible_pont_directe` est conservée et sert de CONTRÔLE : quand
libres(m) ∩ LIANTS_CARD = ∅ les deux DOIVENT coïncider (garde-fou 3), et quand
l'intersection est non vide elles DOIVENT différer (contrôle négatif n°2).

GARDE-FOUS À CHAQUE APPEL (3) : conclusion == cible substituée ; conclusion ==
la même cible réécrite sans somme_cardinale_binaire (défense en profondeur) ;
conclusion == cible directe si et seulement si aucune capture n'est possible.
Rien n'est recopié à la main.

RÉSULTAT MESURÉ : CLOS (0 hypothèse) pour N(3), var('m'), {u}∪{v}, ∅,
Card(z)⊔N(2), Card(F)⊔N(1), et pour les 17 noms qui bloquaient la voie directe.
Coût : 2,2 s à froid (preuve unique), ≈0,002 s par terme ensuite.
theorie_ensembles() = 22 axiomes.
"""
from __future__ import annotations

import os
import sys
import time

RACINE = r"C:\Users\KARL\OneDrive\Bureau\Apprendre\Livre\Bourbakie\Theorie_des_ensembles\V9"
SCRATCH = os.path.dirname(os.path.abspath(__file__))
for p in (RACINE, SCRATCH):
    if p not in sys.path:
        sys.path.insert(0, p)
sys.setrecursionlimit(100000)      # afficher_t/afficher_f sont récursifs

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, Formule, var, egal, et, afficher_f, afficher_t, subst_f, libres_t,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, instancie,
)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    cardinal,
)
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_recollement_somme.ensembles_somme_disjointe import (
    somme_disjointe, somme_cardinale_binaire,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_somme.ensembles_arith_somme import (
    somme_disjointe_cardinal,
)
from outils_ia.arithmetique.machine_num import NUM


def _t(v):
    return v if isinstance(v, Terme) else var(v)


#: nom de variable VÉRIFIÉ frais par la sonde probe_liants.py — aucun liant du
#: keystone de la somme ne le porte.
_FRAIS = "mzz"


# ══════════════════════════════════════════════════════════════════════════════
#  LA CIBLE, construite avec les termes du dépôt (jamais recopiée à la main)
# ══════════════════════════════════════════════════════════════════════════════
def cible_pont_directe(m):
    """somme_cardinale_binaire(m, m) = somme_cardinale_binaire(Card m, Card m),
    construite par appel DIRECT aux termes du dépôt.

    ⚠️ Card(X) := τ_Z(Eq(X, Z)) et le corps de Eq LIE F, u, v, z, up, y (cf.
    LIANTS_CARD).  Pour un m dont une variable libre porte un de ces noms, cet
    appel direct CAPTURE — la formule obtenue n'est alors PAS l'énoncé voulu.
    Utiliser `cible_pont`, qui passe par la substitution capture-évitante."""
    vm = _t(m)
    return egal(somme_cardinale_binaire(vm, vm),
                somme_cardinale_binaire(cardinal(vm), cardinal(vm)))


def cible_pont(m):
    """LA cible, capture-évitante : (m | mzz) [ cible sur la variable fraîche mzz ].

    subst_f suit l'ordre de Bourbaki (T|x)R : subst_f(TERME, nom_var, FORMULE)."""
    return subst_f(_t(m), _FRAIS, cible_pont_directe(var(_FRAIS)))


def _liants(obj, acc=None):
    """noms de tous les lieurs (τ, ∃) apparaissant dans un terme / une formule."""
    acc = set() if acc is None else acc
    pile = [obj]
    while pile:
        u = pile.pop()
        if isinstance(u, Terme):
            if u.tag == "tau":
                acc.add(u.lieur)
            pile.extend(u.args)
        else:
            if u.tag == "exists":
                acc.add(u.lieur)
            pile.extend(u.termes)
            pile.extend(u.sous)
    return acc


#: lettres LIÉES par le terme Card(·) — toute variable libre de m portant un de
#: ces noms est capturée par la construction DIRECTE (mesuré, cf. diag_capture.py).
LIANTS_CARD = _liants(cardinal(var("QQQ")))


# ══════════════════════════════════════════════════════════════════════════════
#  LE PONT
# ══════════════════════════════════════════════════════════════════════════════
_BASE = None            # cache : (∀mzz) Card(mzz⊔mzz) = Card(Card mzz ⊔ Card mzz)


def pont_card_quantifie():
    """|- (∀m) [ Card(m ⊔ m) = Card(Card m ⊔ Card m) ].   CLOS.  Construit une fois."""
    global _BASE
    if _BASE is not None:
        return _BASE
    vm = var(_FRAIS)
    cm = cardinal(vm)

    # (1) forme bien-définie, instanciée X=Y=m, a=b=Card m
    impl_thm = somme_disjointe_cardinal(vm, vm, cm, cm)
    attendu_ant = et(egal(cardinal(vm), cm), egal(cardinal(vm), cm))

    # (2) l'antécédent : Card m = Card m, deux fois — réflexivité (Th.1, E.I.39)
    refl = N.reflexivite(cm)
    ant = conjonction_intro(refl, refl)
    assert ant.conclusion == attendu_ant, (
        "antécédent construit != antécédent attendu\n"
        f"  attendu : {afficher_f(attendu_ant)}\n  obtenu  : {afficher_f(ant.conclusion)}")

    # (3) modus ponens
    base = N.modus_ponens(ant, impl_thm)
    assert base.conclusion == cible_pont_directe(vm), "base : conclusion != cible"
    assert not base.hypotheses, f"base NON close : {len(base.hypotheses)} hyps"

    _BASE = N.generalisation(_FRAIS, base)          # C27
    assert not _BASE.hypotheses, "quantifié NON clos"
    return _BASE


def pont_card(m):
    """|- Card(m ⊔ m) = Card(Card m ⊔ Card m)  pour un TERME m ARBITRAIRE.

    m : un Terme (ou un nom de variable, converti en var(m)).  AUCUNE hypothèse —
    m n'a pas besoin d'être un cardinal.  Théorème CLOS.

    Robuste à tout nom de variable libre dans m : la preuve est faite sur le nom
    frais « mzz », généralisée, puis instanciée en m (C30)."""
    vm = _t(m)
    thm = instancie(pont_card_quantifie(), vm)

    # GARDE-FOU 1 — la conclusion EST la cible (m | mzz), reconstruite à part.
    assert thm.conclusion == cible_pont(vm), "conclusion != cible"

    # GARDE-FOU 2 — écrit sans somme_cardinale_binaire (défense en profondeur) :
    #   subst_f(m, mzz, [ Card(mzz⊔mzz) = Card(Card mzz ⊔ Card mzz) ]).
    fm = var(_FRAIS)
    cf = cardinal(fm)
    assert thm.conclusion == subst_f(
        vm, _FRAIS, egal(cardinal(somme_disjointe(fm, fm)),
                         cardinal(somme_disjointe(cf, cf)))), \
        "la conclusion n'est pas Card(m⊔m) = Card(Card m ⊔ Card m)"

    # GARDE-FOU 3 — quand m ne peut PAS être capturé (aucune de ses variables
    # libres n'est liée par Card), la construction DIRECTE doit coïncider.
    if not (libres_t(vm) & LIANTS_CARD):
        assert thm.conclusion == cible_pont_directe(vm), \
            "cible directe != cible substituée alors qu'aucune capture n'est possible"
    return thm


# ══════════════════════════════════════════════════════════════════════════════
#  AFFICHAGE (les termes-τ des cardinaux sont énormes : on borne)
# ══════════════════════════════════════════════════════════════════════════════
FORME = "( cardinal(sd(m,m)) = cardinal(sd(cardinal(m),cardinal(m))) )"


def _noeuds(obj, cap):
    """nombre de nœuds (termes + formules), arrêt anticipé à `cap`.  Itératif."""
    n, pile = 0, [obj]
    while pile and n < cap:
        u = pile.pop()
        n += 1
        if isinstance(u, Terme):
            pile.extend(u.args if u.tag != "tau" else u.args)
        else:                                   # Formule
            pile.extend(u.termes)
            pile.extend(u.sous)
    return n


def _apercu_t(t, cap=20000, n=200):
    if _noeuds(t, cap) >= cap:
        return f"<terme géant : ≥{cap} nœuds (τ-cardinal développé)>"
    s = afficher_t(t)
    return s if len(s) <= n else s[:n] + f" …[+{len(s) - n} car.]"


def _apercu_f(f, cap=20000, n=400):
    if _noeuds(f, cap) >= cap:
        return f"<formule géante : ≥{cap} nœuds> — forme : {FORME}"
    s = afficher_f(f)
    return s if len(s) <= n else s[:n] + f" …[+{len(s) - n} car.]"


def _rapport(nom, m):
    t0 = time.time()
    thm = pont_card(m)
    dt = time.time() - t0
    clos = (len(thm.hypotheses) == 0)
    print(f"\n--- {nom} ---")
    print(f"  m          : {_apercu_t(_t(m))}")
    print(f"  CLOS = {clos}   nb_hyps = {len(thm.hypotheses)}   ({dt:.3f} s)")
    for h in thm.hypotheses:
        print(f"     hyp: {_apercu_f(h)}")
    print(f"  conclusion : {_apercu_f(thm.conclusion)}")
    print(f"  conclusion == cible reconstruite indépendamment : OK")
    return clos, len(thm.hypotheses)


def main():
    print("=" * 78)
    print("PONT DE CARDINALITÉ :  |- Card(m ⊔ m) = Card(Card m ⊔ Card m)")
    print("=" * 78)

    # (a) la définition consommée, vérifiée et non supposée
    aa, bb = var("aaa"), var("bbb")
    assert somme_cardinale_binaire(aa, bb) == cardinal(somme_disjointe(aa, bb)), \
        "somme_cardinale_binaire n'est PAS cardinal(somme_disjointe(.,.))"
    print("\n[def] somme_cardinale_binaire(a,b) == cardinal(somme_disjointe(a,b))   OK")
    print(f"[def] Card(X) := τ_Z(Eq(X,Z)) LIE {sorted(LIANTS_CARD)}")
    print("      → une variable libre de m portant un de ces noms serait CAPTURÉE")
    print("        par la construction DIRECTE ; d'où la cible substituée (m|mzz).")

    # (b) l'énoncé quantifié (la forme lisible du pont)
    t0 = time.time()
    q = pont_card_quantifie()
    t_froid = time.time() - t0
    t1 = time.time()
    pont_card_quantifie()
    t_chaud = time.time() - t1
    print(f"\n[énoncé quantifié]  CLOS = {not q.hypotheses}  nb_hyps = {len(q.hypotheses)}")
    print(f"  taille : {_noeuds(q.conclusion, 10**7)} nœuds ; forme : (∀{_FRAIS}) {FORME}")
    print(f"  {_apercu_f(q.conclusion, cap=10**7, n=700)}")
    print(f"  coût : {t_froid:.3f} s à froid, {t_chaud:.6f} s rejoué (mémoïsé)")

    # (c) TROIS termes m distincts (+ 2 en bonus)
    cas = [
        ("m = N(3)   NUMÉRAL (successeur³(Card ∅))",   NUM(3)),
        ("m = var('m')   VARIABLE LIBRE",              var("m")),
        ("m = {u} ∪ {v}   TERME COMPOSÉ",              E.reunion(E.singleton(var("u")),
                                                                 E.singleton(var("v")))),
        ("m = ∅   terme clos (bonus)",                 E.VIDE),
        ("m = Card(z) ⊔ N(2)   composé mixte (bonus)", somme_disjointe(cardinal(var("z")),
                                                                       NUM(2))),
    ]
    res = []
    for nom, m in cas:
        res.append((nom,) + _rapport(nom, m))

    # (d) contrôle : les noms qui FAISAIENT échouer la voie directe passent tous
    print("\n" + "-" * 78)
    print("CONTRÔLE anti-collision — noms rejetés par la voie DIRECTE (sonde) :")
    bloques = ["m", "z", "t", "k", "u", "v", "w", "x", "y", "p", "q",
               "F", "G", "s", "m1", "m2", "yb"]
    ok_all = True
    for nom in bloques:
        thm = pont_card(var(nom))
        ok = (thm.conclusion == cible_pont(var(nom))) and not thm.hypotheses
        ok_all &= ok
        print(f"   m = var({nom!r}):  clos={not thm.hypotheses}  cible={ok}")
    print(f"   => {len(bloques)}/{len(bloques)} passent par la voie quantifiée : {ok_all}")
    assert ok_all

    # (e) CONTRÔLE NÉGATIF : la voie DIRECTE échoue bien, et à la ligne annoncée
    print("\n" + "-" * 78)
    print("CONTRÔLE NÉGATIF (voie directe, sans généralisation) :")
    import traceback
    for nom in ("m", "n"):
        vm = var(nom)
        try:
            im = somme_disjointe_cardinal(vm, vm, cardinal(vm), cardinal(vm))
            r = N.reflexivite(cardinal(vm))
            th = N.modus_ponens(conjonction_intro(r, r), im)
            print(f"   m = var({nom!r}) : la voie directe PASSE "
                  f"(clos={not th.hypotheses}) — nom sans collision")
        except Exception as exc:
            tb = traceback.extract_tb(sys.exc_info()[2])[-1]
            print(f"   m = var({nom!r}) : ÉCHEC {type(exc).__name__}: {exc}")
            print(f"        à {os.path.basename(tb.filename)}:{tb.lineno}"
                  f"   (collision de liant — d'où la voie quantifiée)")

    # (e-bis) CONTRÔLE NÉGATIF n°2 : la cible DIRECTE est fausse quand m contient
    #         une lettre liée par Card — c'est elle qui capture, pas le théorème.
    print("\n" + "-" * 78)
    print("CONTRÔLE NÉGATIF n°2 (capture par la construction DIRECTE de la cible) :")
    for etiq, mm in [("{u} ∪ {v}  (u, v liés par Card)",
                      E.reunion(E.singleton(var("u")), E.singleton(var("v")))),
                     ("{aa} ∪ {bb}  (aucune lettre liée)",
                      E.reunion(E.singleton(var("aa")), E.singleton(var("bb"))))]:
        thm = pont_card(mm)
        col = sorted(libres_t(mm) & LIANTS_CARD)
        idem = (thm.conclusion == cible_pont_directe(mm))
        print(f"   m = {etiq}")
        print(f"      libres(m) ∩ liants(Card) = {col}")
        print(f"      conclusion == cible DIRECTE   : {idem}"
              f"   {'← capture attendue' if col else '← doit être True'}")
        print(f"      conclusion == cible (m|mzz)   : "
              f"{thm.conclusion == cible_pont(mm)}   clos={not thm.hypotheses}")
        assert idem == (not col), "le comportement de capture ne correspond pas au diagnostic"

    # (f) bilan + invariant
    print("\n" + "=" * 78)
    print("BILAN")
    for nom, clos, nh in res:
        print(f"   {'CLOS' if clos else 'HYPS'}  nb_hyps={nh}   {nom}")

    th = E.theorie_ensembles()
    n_ax = len(th.axiomes)
    print(f"\nINVARIANT : theorie_ensembles() = {n_ax} axiomes   "
          f"{'OK' if n_ax == 22 else '### ÉCHEC ###'}")
    assert n_ax == 22, f"invariant cassé : {n_ax} axiomes au lieu de 22"
    print("=" * 78)
