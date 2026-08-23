# -*- coding: utf-8 -*-
"""§III.6.3, Corollaire 4 — VOLET SOMME : a + b = a pour b ≤ a, a infini.

🎯 CIBLE :

    cor4_somme(A, b) :
        { enonce_hessenberg(A), est_infini(Card A), b ≤ Card A }
            ⊢  Card A + b = Card A

L'ÉNONCÉ DE BOURBAKI (E III.49) est « ab = a + b = sup(a,b) » pour a, b non nuls
dont l'un est infini.  Il le déduit des Corollaires 2 et 3, qui passent tous
deux par la Proposition 14 sous sa forme FAMILLE — que le dépôt ne possède pas
(il n'a que le cas binaire, et le dit lui-même).  Mais l'énoncé du Cor. 4 est
BINAIRE : la déduction directe évite entièrement les familles.

⚠️ CHOIX DE FORME, assumé et documenté.  Écrire `sup(a,b)` exigerait la
comparabilité des cardinaux (Th. 1 §III.3) pour que le TERME soit défini.  On
formule donc sous la garde « b ≤ Card A », qui rend `sup = Card A` manifeste
sans rien postuler.  L'écart avec Bourbaki est de FORME ; le CONTENU est le
même — c'est la moitié « a + b = sup(a,b) » du corollaire.

⚠️ `b` n'a PAS besoin d'être supposé cardinal : `b ≤ Card A` suffit.  L'énoncé
est donc un peu plus général que nécessaire, ce qui ne coûte rien.

LA ROUTE :
    a + b ≤ a + a          [monotonie droite de la somme, sous b ≤ a]
    a + a = a              [absorption globale, depuis Hessenberg]
    a ≤ a + b              [borne gauche, via le pont ENSEMBLE → CARDINAL]
    ⇒ a + b = a            [antisymétrie de ≤ sur les cardinaux]

⚠️ Le pont ENSEMBLE → CARDINAL est nécessaire parce que
`_inf_egal_somme_gauche_t` conclut « a ≤ a ⊔ b » au niveau des ENSEMBLES, alors
que la somme cardinale est `Card(a ⊔ b)`.  On enchaîne X ≤ Card X puis la
transitivité, exactement comme le fait `absorption_depuis_carre`.

⚠️ RÈGLE PERF : `enonce_hessenberg(A)` reste porté, jamais dérivé ici.

theorie_ensembles() INCHANGÉE (22).  Noyau INTACT.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, equivalence_avant, instancie,
)

from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_recollement_somme.ensembles_somme_disjointe import (
    somme_cardinale_binaire, somme_disjointe,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    cardinal, inf_egal_card,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.ordre_cardinaux.ensembles_cardinal_ordre_props import (
    somme_cardinale_monotone_droite,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.ordre_cardinaux.ensembles_cardinaux_props_restantes_ordre import (
    inf_egal_antisymetrique_card,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.props_restantes.ensembles_cardinaux_props_restantes import (
    _inf_egal_somme_gauche_t,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_2_finis_props.ensembles_chap3_props_restantes import (
    est_cardinal_de_cardinal,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_3_infinis_denombrables.ensembles_infinis import (
    est_infini,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.hessenberg.coeur.ensembles_hessenberg import (
    enonce_hessenberg,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.hessenberg.coeur.ensembles_hessenberg_structural_discharge import (
    _set_le_eq_card, _le_trans_t,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.iii_6_2_proprietes_infinis.ensembles_absorption_generale import (
    absorption_sous_hessenberg,
)


def _t(t):
    """Coercion str/Terme → Terme."""
    return t if isinstance(t, Terme) else var(t)


def enonce_cor4_somme(a="A", b="bc4"):
    """FORMULE : Card A + b = Card A."""
    cA = cardinal(_t(a))
    return egal(somme_cardinale_binaire(cA, _t(b)), cA)


# @livre Ch.III §6.3 Cor.4 | E III.49 L.28-30 | PDF p.152
#   (« a + b = sup(a,b) » — moitié SOMME, cas binaire, sous la garde b ≤ a)
def cor4_somme(a="A", b="bc4"):
    """🎯 { enonce_hessenberg(A), est_infini(Card A), b ≤ Card A }
           ⊢ Card A + b = Card A.

    La moitié « somme » du Corollaire 4, par monotonie et absorption — sans
    jamais passer par les familles dont Bourbaki se sert."""
    vA, vb = _t(a), _t(b)
    cA = cardinal(vA)
    somme_ab = somme_cardinale_binaire(cA, vb)
    somme_aa = somme_cardinale_binaire(cA, cA)

    #  ── (1) a + b ≤ a + a   (monotonie du sommant DROIT, sous b ≤ a) ────────
    h_le = N.assume(inf_egal_card(vb, cA))
    mono = somme_cardinale_monotone_droite(vb, cA, cA)   # (b≤a) ⇒ Card(a⊔b) ≤ Card(a⊔a)
    haut = N.modus_ponens(h_le, mono)
    assert haut.conclusion == inf_egal_card(somme_ab, somme_aa), \
        "cor4_somme : la monotonie ne donne pas a+b ≤ a+a"

    #  ── (2) a + a = a, puis réécriture de Leibniz SUR LA FORMULE ───────────
    abso = absorption_sous_hessenberg(a)                 # a+a = a
    haut = N.modus_ponens(haut, equivalence_avant(N.modus_ponens(
        abso, N.s6(somme_aa, cA, "wc4", inf_egal_card(somme_ab, var("wc4"))))))
    assert haut.conclusion == inf_egal_card(somme_ab, cA), "cor4_somme : a+b ≤ a"

    #  ── (3) a ≤ a + b   (pont ENSEMBLE → CARDINAL, comme dans l'absorption) ─
    disj = somme_disjointe(cA, vb)
    bas = N.modus_ponens(conjonction_intro(_inf_egal_somme_gauche_t(cA, vb),
                                           _set_le_eq_card(disj)),
                         _le_trans_t(cA, disj, somme_ab))
    assert bas.conclusion == inf_egal_card(cA, somme_ab), "cor4_somme : a ≤ a+b"

    #  ── (4) antisymétrie ────────────────────────────────────────────────────
    anti = instancie(instancie(inf_egal_antisymetrique_card(), somme_ab), cA)
    res = N.modus_ponens(conjonction_intro(conjonction_intro(
        conjonction_intro(haut, bas), est_cardinal_de_cardinal(disj)),
        est_cardinal_de_cardinal(vA)), anti)

    assert res.conclusion == enonce_cor4_somme(a, b), "cor4_somme : forme"
    assert set(res.hypotheses) == {enonce_hessenberg(a), est_infini(cA),
                                   inf_egal_card(vb, cA)}, \
        "cor4_somme : hypothèses résiduelles inattendues (%d)" % len(res.hypotheses)
    return res


__all__ = ["enonce_cor4_somme", "cor4_somme"]
