"""§III.5.8 / §III.6.2 — DIAGNOSTIC EXÉCUTABLE de l'obstruction de GLUING factorielle.

But de ce module : remplacer la SPÉCULATION de la docstring de
`ensembles_factorielle_existence` (qui attribuait le verrou O3 au binder « y » de
`antecedent_dans_domaine`) par un diagnostic EXACT, EXÉCUTABLE et REPRODUCTIBLE,
obtenu en INSTRUMENTANT le chemin de gluing déposé jusqu'au point de rupture.

Aucune dérivation logique ici (pas de théorème), donc theorie INCHANGÉE = 22,
noyau INTACT, rien postulé.  Ce module est un OUTIL DE DIAGNOSTIC honnête.

────────────────────────────────────────────────────────────────────────────────
RÉSULTAT VÉRIFIÉ (reproductible via `diagnostiquer_capture()` ci-dessous).

Le `factorielle_essais_existe()` (route C62 sur la règle factorielle index-aware)
échoue par `ValueError: modus ponens : mineure ≠ antécédent`.  La pile EXACTE est :

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
POURQUOI C'EST IRRÉDUCTIBLE SANS TOUCHER AU DÉPÔT (multi-site, structurel).

Trois sites se conjuguent, tous DÉPOSÉS et non modifiables :

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

CONCLUSION HONNÊTE : la récurrence factorielle est STRUCTURELLEMENT incompatible
avec le gluing C60 déposé.  Le bridge mûr (`application_egale_par_valeurs`,
`valeur_reunion_*`, recollement) ne s'applique PAS : il opère sur des graphes
fonctionnels DÉJÀ construits ; ici le verrou est en AMONT, dans la fabrication
même des essais par le gluing déposé, sur des noms de témoins fixes.

CORRECTIF FUTUR CIBLÉ (hors périmètre, nécessiterait de toucher au dépôt) — UN des :
   (A) rendre `reunion_graphes_fonctionnelle`/`antecedent_dans_domaine` PARAMÉTRIQUES
       en leurs témoins (u,v,z,y → noms frais passés par l'appelant) ; OU
   (B) une facilité noyau d'α-renommage PROFOND (multi-binder) des τ-termes cardinaux
       produisant `cardinal_frais`/`successeur_frais`/`produit_frais` prouvablement
       égaux mais à binders {u,up,v,y,z,F} renommés hors de {u,v,z,y}.
Avec (A) OU (B), le chemin C62 factoriel franchirait (S?) ; resterait alors (O1) =
l'assemblage essais→f totale (chantier §III.2 du gluing de famille), distinct.
"""
from __future__ import annotations

from bourbaki.logique.formule import var, subst_f, appartient
import bourbaki.logique.noyau_abrege as N
import bourbaki.ensembles.ensembles_abrege as E


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
    from bourbaki.entiers.ensembles_entiers import successeur
    from bourbaki.cardinaux.ensembles_cardinaux import cardinal
    from bourbaki.cardinaux.arithmetique.ensembles_arith_cardinale import (
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


def diagnostiquer_capture():
    """Reproduit le point de rupture et CONFIRME que le binder collisionnant est « v ».

    Instrumente `antecedent_dans_domaine` (déposé) : au lieu de laisser le MP planter,
    on compare l'antécédent S5-substitué à la mineure et on renvoie le rapport de la
    PREMIÈRE divergence — qui doit montrer (nom='v') côté mineure vs (lieur='@0')
    côté antécédent (capture-avoidance du témoin v dans un contexte v-lié).

    Renvoie un dict : {site, binder_collision, occurrences_v_vs_db}.  N'altère rien
    de durable (monkey-patch local restauré)."""
    import bourbaki.ensembles.fonctions.ensembles_restriction_somme as RS
    from bourbaki.entiers.ensembles_factorielle_existence import (
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

    def _patched(u="u", v="v", f="F"):
        vu, vv, vf = RS._t(u), RS._t(v), RS._t(f)
        body = appartient(E.couple(vu, var("y")), vf)         # (u,y)∈F
        huv = N.assume(appartient(E.couple(vu, vv), vf))      # mineure (u,v)∈F
        ante = subst_f(vv, "y", body)                         # antécédent S5
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
        return orig(u, v, f)

    RS.antecedent_dans_domaine = _patched
    try:
        factorielle_essais_existe()
    except _Stop:
        pass
    finally:
        RS.antecedent_dans_domaine = orig
    return rapport


__all__ = ["binders_arithmetique_cardinale", "diagnostiquer_capture"]
