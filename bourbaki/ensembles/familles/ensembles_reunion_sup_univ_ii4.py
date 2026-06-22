"""§II.4 — PROPRIÉTÉ UNIVERSELLE de la réunion d'une famille (caractérisation sup).

Module NEUF.  Ne modifie aucun fichier existant ; complète l'algèbre des familles
(`ensembles_familles`, `ensembles_familles_algebre`) SANS rien dupliquer.

On formalise, comme énoncé AUTONOME et INCONDITIONNEL (0 hypothèse), la propriété
universelle de la réunion ⋃_{ι∈I} X_ι : c'est le PLUS PETIT MAJORANT (au sens de
⊂) de la famille (X_ι).  Précisément (E.II.4.1) :

        ⊢  ( ⋃_{ι∈I} X_ι ⊂ A )  ⟺  ( (∀i)(i∈I ⇒ X_i ⊂ A) )       (`reunion_sup_universelle`)

C'est la caractérisation « borne supérieure » de la réunion : ⋃ X_ι est inclus
dans A si et seulement si CHAQUE terme X_ι l'est.  Le sens « ⇐ » contient la
borne X_α ⊂ ⋃ (toutes les bornes inférieures de A majorent ⋃) ; le sens « ⇒ »
redonne X_α ⊂ ⋃ ⊂ A.  Complète `inter_incluse_terme` / `terme_inclus_reunion`
(bornes ponctuelles) par leur forme UNIVERSELLE quantifiée.

STRATÉGIE : appartenance via AXIOME_REUNION_FAM (réutilisé, theorie_ensembles=22),
loi de déduction sur « w∈· ⇒ w∈· » généralisée, et élimination existentielle pour
le sens « ⇐ ».  Point courant nommé « w » (capture-safe vis-à-vis du liant « i »
de l'axiome de réunion et du liant « z » de l'abréviation ⊂).
"""
from __future__ import annotations

from bourbaki.logique.formule import (var, egal, et, impl, appartient,
                                       existe, pourtout, inclus, equiv)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.logique.tactiques.tactiques_abrege import syllogisme
from bourbaki.logique.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche as cg,
    conjonction_elim_droite as cd, equivalence_avant, equivalence_arriere,
    instancie)
from bourbaki.logique.tactiques.tactiques_abrege_quantif import existe_elimination


def _inst_reunion(f, i, z):
    """⊢ (z ∈ ⋃_{ι∈I} X_ι) ⇔ (∃i)(i∈I et z∈X_i)."""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_REUNION_FAM)
    return instancie(instancie(instancie(ax, f), i), z)


def _enonce(vf, vI, vA):
    """⋃X_ι ⊂ A  ⟺  (∀i)(i∈I ⇒ X_i ⊂ A)."""
    reun = E.reunion_famille(vf, vI)
    gauche = inclus(reun, vA)
    droite = pourtout("k", impl(appartient(var("k"), vI),
                                inclus(E.valeur_famille(vf, var("k")), vA)))
    return equiv(gauche, droite)


def cible_reunion_sup_universelle(f="X", i="I", a="A"):
    """L'énoncé Bourbaki visé (E.II.4.1, propriété universelle de la réunion)."""
    return _enonce(var(f), var(i), var(a))


def reunion_sup_universelle(f="X", i="I", a="A"):
    """⊢ ( ⋃_{ι∈I} X_ι ⊂ A ) ⟺ ( (∀i)(i∈I ⇒ X_i ⊂ A) ).   (E.II.4.1, sup de la famille.)

    INCONDITIONNEL (0 hypothèse).  ⋃ est le plus petit majorant (⊂) de (X_ι)."""
    vf, vI, vA = var(f), var(i), var(a)
    vz, vk = var("z"), var("k")
    reun = E.reunion_famille(vf, vI)
    Xk = E.valeur_famille(vf, vk)
    gauche = inclus(reun, vA)
    droite = pourtout("k", impl(appartient(vk, vI), inclus(Xk, vA)))

    vi = var("i")                                          # binder de l'existentiel d'AXIOME_REUNION_FAM
    Xi = E.valeur_famille(vf, vi)
    body = et(appartient(vi, vI), appartient(vz, Xi))      # i∈I et w∈X_i  (forme axiome)

    # ── sens « ⇒ » :  ⋃⊂A  ⊢  (∀k)(k∈I ⇒ X_k ⊂ A) ──────────────────────────
    hG = N.assume(gauche)                                  # ⋃⊂A = (∀w')(w'∈⋃ ⇒ w'∈A)
    w_reun_A = instancie(hG, vz)                           # w∈⋃ ⇒ w∈A
    hk = N.assume(appartient(vk, vI))                      # k∈I
    hw = N.assume(appartient(vz, Xk))                      # w∈X_k
    w_reun = N.modus_ponens(conjonction_intro(hk, hw),     # (∃i)(i∈I et w∈X_i)  [témoin k]
                            N.s5(body, vk, "i"))
    w_reun = N.modus_ponens(w_reun, equivalence_arriere(_inst_reunion(vf, vI, vz)))
    w_A = N.modus_ponens(w_reun, w_reun_A)                 # w∈A
    Xk_A = N.generalisation("z", N.loi_deduction(appartient(vz, Xk), w_A))  # X_k ⊂ A
    imp_k = N.loi_deduction(appartient(vk, vI), Xk_A)      # k∈I ⇒ X_k ⊂ A
    droite_de_gauche = N.generalisation("k", imp_k)        # {gauche} ⊢ droite
    sens_avant = N.loi_deduction(gauche, droite_de_gauche)

    # ── sens « ⇐ » :  (∀k)(k∈I ⇒ X_k ⊂ A)  ⊢  ⋃⊂A ─────────────────────────
    hD = N.assume(droite)                                  # (∀k)(k∈I ⇒ X_k ⊂ A)
    hwU = N.assume(appartient(vz, reun))                   # w∈⋃
    exi = N.modus_ponens(hwU, equivalence_avant(_inst_reunion(vf, vI, vz)))  # (∃i)(i∈I et w∈X_i)
    hb = N.assume(body)                                    # i∈I et w∈X_i
    Xi_A2 = N.modus_ponens(cg(hb), instancie(hD, vi))      # X_i ⊂ A   (hD instancié en i)
    w_in_A = N.modus_ponens(cd(hb), instancie(Xi_A2, vz))  # w∈A
    imp_b = existe_elimination(N.loi_deduction(body, w_in_A), "i")  # (∃i …) ⇒ w∈A
    w_A2 = N.modus_ponens(exi, imp_b)                      # w∈A
    gauche_de_droite = N.generalisation("z", N.loi_deduction(appartient(vz, reun), w_A2))
    sens_arriere = N.loi_deduction(droite, gauche_de_droite)

    return conjonction_intro(sens_avant, sens_arriere)
