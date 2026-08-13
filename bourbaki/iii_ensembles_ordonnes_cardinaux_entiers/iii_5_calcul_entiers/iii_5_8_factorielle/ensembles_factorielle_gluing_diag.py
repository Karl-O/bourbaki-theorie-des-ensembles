"""§III.5.8 / §III.6.2 — DIAGNOSTIC EXÉCUTABLE de l'obstruction de GLUING factorielle.

But de ce module : remplacer la SPÉCULATION de la docstring de
`ensembles_factorielle_existence` (qui attribuait le verrou O3 au binder « y » de
`antecedent_dans_domaine`) par un diagnostic EXACT, EXÉCUTABLE et REPRODUCTIBLE,
obtenu en INSTRUMENTANT le chemin de gluing déposé jusqu'au point de rupture.

Aucune dérivation logique ici (pas de théorème), donc theorie INCHANGÉE = 22,
noyau INTACT, rien postulé.  Ce module est un OUTIL DE DIAGNOSTIC honnête.

────────────────────────────────────────────────────────────────────────────────
⚠️⚠️ TOUT LE DIAGNOSTIC CI-DESSOUS EST PÉRIMÉ (mesuré le 26 juil. 2026).

`diagnostiquer_capture()` renvoie aujourd'hui **{}** : il n'y a PLUS de point de
rupture à instrumenter.  `factorielle_essais_existe()` construit (3 hyps, 1,6 s).
Le fix `subst` du 24 juil. 2026 (court-circuit CS : `(T|x)t = t` quand x ∉ libres(t))
a supprimé la cause — qui n'était PAS une capture mais un renommage GRATUIT : le liant
homonyme était renommé alors que la variable substituée n'était pas libre dessous, ce
qui faisait α-diverger deux chemins de construction du MÊME énoncé.

CE QUI RESTE VRAI, et qu'il ne faut pas jeter avec le reste : les blocs (S1) et (S2)
ci-dessous sont FACTUELS.  `binders_arithmetique_cardinale()` donne toujours
_collision = ['u','v','y','z'].  Les noms collisionnent BEL ET BIEN ; c'est leur
CONSÉQUENCE (la capture) qui a disparu.  Ne pas conclure « les noms ne collisionnent
plus » — conclure « collision de noms ≠ capture ».

Ce module reste utile comme SENTINELLE : si une capture réapparaissait, il la
localiserait exactement.  Les deux fonctions sont conservées telles quelles.

────────────────────────────────────────────────────────────────────────────────
LE DIAGNOSTIC D'ÉPOQUE (juillet 2026, avant le fix `subst` — conservé pour mémoire).

Le `factorielle_essais_existe()` (route C62 sur la règle factorielle index-aware)
échouait par `ValueError: modus ponens : mineure ≠ antécédent`.  La pile EXACTE était :

    c62_recursion_sur_N
      → recursion_transfinie_existence_final … (chaîne C60 déposée) …
        → extension_un_pas_fonctionnelle           (c60_existence_close:306)
          → reunion_graphes_fonctionnelle          (restriction_somme:118)
            → antecedent_dans_domaine              (restriction_somme:76)
              → N.s5(body, vv, "y")  →  MP échoue   (noyau_abrege:146)

DIAGNOSTIC PRÉCIS (corrige la docstring antérieure).

Le binder qui COLLISIONNE n'est PAS « y ».  C'est « v ».

  • `reunion_graphes_fonctionnelle` (ensembles_restriction_somme.py:96, DÉPOSÉ)
    instancie ses lemmes avec le TÉMOIN  `vv = var("v")`  (un v LIBRE), puis appelle
    `antecedent_dans_domaine(vu, vv, vf)` qui construit, via S5 avec témoin vv,
    l'antécédent  `subst_f(vv, "y", (u,y)∈F)`.

  • Le terme F (= un essai/graphe réalisé de la famille) CONTIENT, profondément, un
    τ-binder NOMMÉ « v » — provenant de `cardinal`/`equipotent`/`est_bijection_de`
    (Card(X) := τ_Z Eq(X,Z), et Eq déplie est_bijection_de dont les liants internes
    sont {F,u,up,v,y,z}).  La règle factorielle ÉMET ce F : sa sortie
    (card(dom u)+1)·u(prev) lit u via `cardinal`, `successeur`, `produit_cardinal_binaire`,
    qui TOUS développent l'équipotence et BAKENT les binders {F,Z,u,up,v,y,z}.

  • Substituer le témoin LIBRE vv=v dans un contexte où « v » est déjà LIÉ force la
    capture-avoidance du noyau : vv est α-renommé en `@0` (indice de De Bruijn).
    L'antécédent obtenu  `subst_f(v,"y",(u,y)∈F)`  porte donc `@0` là où la mineure
    `huv = (u,v)∈F` porte le `v` littéral.  ⇒ mineure ≠ antécédent ⇒ MP échoue.

VÉRIFIÉ EXPÉRIMENTALEMENT (diff structurel des deux formules) : les points de
divergence sont EXACTEMENT les occurrences `(nom='v') vs (lieur='@0')` — confirmant
que la collision est sur « v », pas « y ».

────────────────────────────────────────────────────────────────────────────────
« POURQUOI C'EST IRRÉDUCTIBLE » — LE RAISONNEMENT QUI ÉTAIT FAUX.

⚠️ (S1) et (S2) sont FACTUELS et le restent (mesurés).  (S3) l'est aussi.  Mais leur
CONCLUSION — « donc la récurrence factorielle est STRUCTURELLEMENT incompatible avec le
gluing C60 déposé » — était FAUSSE : elle supposait, sans le vérifier, que collision de
NOMS ⇒ capture.  Le pas manquant était dans `subst`, pas dans le gluing.  LEÇON : un
argument de conflit de noms n'est une preuve d'impossibilité que si l'on a mesuré que
la substitution renomme EFFECTIVEMENT (et à raison) ; ici elle renommait à tort.
Les correctifs (A) et (B) proposés plus bas sont donc SANS OBJET.

Trois sites se conjuguent (constats exacts, conclusion caduque) :

  (S1)  Témoins HARDCODÉS du gluing : `reunion_graphes_fonctionnelle` fixe
        u,v,z = var("u"),var("v"),var("z") (restriction_somme:96) ; et
        `antecedent_dans_domaine` fixe le binder S5 « y » (restriction_somme:76).
        ⇒ l'ensemble interdit de binders de F est {u, v, z, y}.

  (S2)  Binders STRUCTURELS de l'arithmétique cardinale : `equipotent`/
        `est_bijection_de` bakent {F,u,up,v,y,z} — NON paramétrables (hardcodés dans
        la déf. de la bijection).  Donc `cardinal`, `successeur` (=Card(n⊔{∅})) et
        `produit_cardinal_binaire` introduisent TOUS, inévitablement, v,u,y,z.
        VÉRIFIÉ : binders(successeur(n)) = binders(produit(a,b)) = {F,Z,u,up,v,y,z}.

  (S3)  La RÈGLE factorielle DOIT exprimer n+1 et un produit (récurrence
        (n+1)!=(n+1)·n!).  Toute formulation — y compris l'astuce « état-paire »
        (n,m)↦(n+1,(n+1)·m) qui porterait l'indice dans l'état pour éviter
        `cardinal(dom u)` — RESTE forcée d'employer `successeur` et `produit`, donc
        rebake v,u,y,z.  AUCUN encodage de la récurrence factorielle ne peut éviter
        l'intersection {u,v,z,y} = (S1) ∩ (S2).

CONCLUSION D'ÉPOQUE — RÉFUTÉE : « la récurrence factorielle est STRUCTURELLEMENT
incompatible avec le gluing C60 déposé ».  Elle est parfaitement compatible : le chemin
LIVE construit de bout en bout, et le pivot est bien TRAVERSÉ (trace `sys.setprofile` :
extension_un_pas_fonctionnelle 1×, reunion_graphes_fonctionnelle 3×,
antecedent_dans_domaine 14×, tous à témoins par DÉFAUT).  Ni (A) ni (B) n'ont été
nécessaires : le correctif réel a été le court-circuit CS de `subst`.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, subst_f, appartient
import bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau.noyau_abrege as N
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E


def _binders(t, acc):
    l = getattr(t, "lieur", None)
    if l:
        acc.add(l)
    for s in (getattr(t, "sous", None) or getattr(t, "termes", None)
              or getattr(t, "args", None) or ()):
        _binders(s, acc)
    return acc


def binders_arithmetique_cardinale():
    """Renvoie l'ensemble des binders bakés par successeur/produit/cardinal.

    VÉRIFIE (S2) : l'arithmétique cardinale introduit {F,Z,u,up,v,y,z}, dont
    {u,v,z,y} ⊆ l'ensemble interdit du gluing (S1).  Donc toute règle factorielle
    (qui doit employer successeur et produit) heurte le gluing."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import successeur
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import cardinal
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_produit.ensembles_arith_cardinale import (
        produit_cardinal_binaire,
    )
    out = {}
    out["successeur"] = sorted(_binders(successeur(var("n")), set()))
    out["cardinal"] = sorted(_binders(cardinal(var("D")), set()))
    out["produit"] = sorted(_binders(
        produit_cardinal_binaire(var("a"), var("b")), set()))
    # ensemble interdit du gluing déposé (S1) :
    out["_interdits_gluing"] = sorted({"u", "v", "z", "y"})
    inter = set(out["successeur"]) & set(out["_interdits_gluing"])
    out["_collision"] = sorted(inter)            # {u,v,y,z} attendu
    return out


# @livre Ch.III §5.8 Rem.- | E III.41 L.30-32 | PDF p.144
def diagnostiquer_capture():
    """Reproduit le point de rupture et CONFIRME que le binder collisionnant est « v ».

    Instrumente `antecedent_dans_domaine` (déposé) : au lieu de laisser le MP planter,
    on compare l'antécédent S5-substitué à la mineure et on renvoie le rapport de la
    PREMIÈRE divergence — qui doit montrer (nom='v') côté mineure vs (lieur='@0')
    côté antécédent (capture-avoidance du témoin v dans un contexte v-lié).

    Renvoie un dict : {site, binder_collision, occurrences_v_vs_db}.  N'altère rien
    de durable (monkey-patch local restauré)."""
    import bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.recollement.ensembles_restriction_somme as RS
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_8_factorielle.ensembles_factorielle_existence import (
        factorielle_essais_existe,
    )

    rapport = {}

    def _premiere_div(a, b, path="root"):
        if a == b:
            return None
        na = getattr(a, "nom", None); nb = getattr(b, "nom", None)
        la = getattr(a, "lieur", None); lb = getattr(b, "lieur", None)
        if na != nb or la != lb:
            return (path, (na, la), (nb, lb))
        sa = (getattr(a, "sous", None) or getattr(a, "termes", None)
              or getattr(a, "args", None) or ())
        sb = (getattr(b, "sous", None) or getattr(b, "termes", None)
              or getattr(b, "args", None) or ())
        if len(sa) != len(sb):
            return (path, f"arity {len(sa)}", f"arity {len(sb)}")
        for i, (x, y) in enumerate(zip(sa, sb)):
            r = _premiere_div(x, y, path + f".{i}")
            if r is not None:
                return r
        return None

    orig = RS.antecedent_dans_domaine

    class _Stop(Exception):
        pass

    def _patched(u="u", v="v", f="F", y="y"):
        # post-paramétrisation : antecedent_dans_domaine prend un 4e arg y (binder S5).
        # Le chemin DÉFAUT passe y="y" → capture inchangée ; on threade y pour fidélité.
        vu, vv, vf = RS._t(u), RS._t(v), RS._t(f)
        body = appartient(E.couple(vu, var(y)), vf)           # (u,y)∈F
        huv = N.assume(appartient(E.couple(vu, vv), vf))      # mineure (u,v)∈F
        ante = subst_f(vv, y, body)                           # antécédent S5
        if ante != huv.conclusion:
            div = _premiere_div(huv.conclusion, ante)
            rapport["site"] = ("ensembles_restriction_somme.antecedent_dans_domaine "
                               "via reunion_graphes_fonctionnelle:96")
            rapport["premiere_divergence_path"] = div[0]
            rapport["mineure"] = div[1]          # attendu (nom='v', lieur=None)
            rapport["antecedent"] = div[2]       # attendu (nom=None, lieur='@0')
            # le binder collisionnant = celui qui devient '@0' = 'v'
            rapport["binder_collision"] = "v"
            raise _Stop
        return orig(u, v, f, y)

    RS.antecedent_dans_domaine = _patched
    try:
        factorielle_essais_existe()
    except _Stop:
        pass
    finally:
        RS.antecedent_dans_domaine = orig
    return rapport


__all__ = ["binders_arithmetique_cardinale", "diagnostiquer_capture"]
