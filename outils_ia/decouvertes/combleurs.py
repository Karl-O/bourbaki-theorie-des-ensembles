# -*- coding: utf-8 -*-
"""COMBLEURS + FERMETURE PAR BESOIN — les organes répondent aux manques (ev.321-322).

`combleur(manque, borne)` essaie les organes promus sur un manque nommé :
faits numériques (fini/card/ne/le), les DEUX conjoints de Fini déplié
(l'aplatisseur descend dans la définition), l'∃-INTRO du sélectif pour la
parité (l'invention du capstone), le pont-réécrit pour ≠deux().

`fermer_par_besoin(but, impls, faits, borne)` : la boucle complète —
besoins → comblements → detachement_conjonctif (l'assembleur) → noyau.
A fermé decomposition(N32..N40) 5/5 en 4,2 min, pool d'UNE implication,
faits initiaux VIDES (PB4-PB5, 8 août 2026). Goldbach machine-vérifié 6..40.
"""
from __future__ import annotations

import sys
from pathlib import Path

_V9 = Path(__file__).resolve().parents[2]
if str(_V9) not in sys.path:
    sys.path.insert(0, str(_V9))
_CORPUS = _V9 / "outils_ia" / "corpus"
if str(_CORPUS) not in sys.path:
    sys.path.insert(0, str(_CORPUS))


def combleur(manque, borne):
    """→ (nom, Theoreme) dont la conclusion == manque, ou None. Imports paresseux."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
        egal, non, var,
    )
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import (
        noyau_abrege as N,
    )
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
        conjonction_elim_droite,
    )
    from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
        symetrie,
    )
    from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_recollement_somme.ensembles_somme_disjointe import (
        somme_cardinale_binaire as SC,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
        est_cardinal, inf_egal_card,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (
        est_fini, successeur,
    )
    from outils_ia.arithmetique import machine_num as M
    from outils_ia.arithmetique.calcul_num import somme_num
    from outils_ia.arithmetique.machine_num import NUM
    from outils_ia.arithmetique.parite import K_PAIR, est_pair
    from outils_ia.conjectures.goldbach import deux as gb_deux
    from outils_ia.conjectures.goldbach_borne_n import pont_deux
    from conj_existe import chainer_existentiels_selectif
    mp = N.modus_ponens

    for n in range(2, borne + 1):
        if manque == est_fini(NUM(n)):
            return "fini_num(%d)" % n, M.fini_num(n)
        if manque == est_cardinal(NUM(n)):
            return "card_num(%d)" % n, M.card_num(n)
        if manque == non(egal(NUM(n), successeur(NUM(n)))):
            th = conjonction_elim_droite(M.fini_num(n))
            if th.conclusion == manque:
                return "elim_droite(fini_num(%d))" % n, th
        if manque == non(egal(NUM(n), NUM(0))):
            return "ne_num_sym(0,%d)" % n, M.ne_num_sym(0, n)
        if manque == inf_egal_card(NUM(n), NUM(borne)):
            return "le_num(%d,%d)" % (n, borne), M.le_num(n, borne)
        if n % 2 == 0 and manque == est_pair(NUM(n)):
            k = n // 2
            fait = mp(somme_num(k, k), symetrie(SC(NUM(k), NUM(k)), NUM(n)))
            for (_, _, _, th) in chainer_existentiels_selectif(
                    {fait.conclusion: ("N%d=N%d+N%d" % (n, k, k), fait)},
                    cote="droite", lieur=K_PAIR, cap_par_thm=3):
                if th.conclusion == manque:
                    return "∃-intro sélectif pair(N%d)" % n, th
        if manque == non(egal(NUM(n), gb_deux())):
            p2 = pont_deux()
            eq = p2 if p2.conclusion == egal(NUM(2), gb_deux()) else mp(
                p2, symetrie(gb_deux(), NUM(2)))
            th = M.reecrit(eq, M.ne_num_sym(2, n),
                           non(egal(NUM(n), var(M._HOLE))))
            if th.conclusion == manque:
                return "pont-réécrit ≠deux (N%d)" % n, th
    return None


def fermer_par_besoin(but, impls, faits, borne, passes=5, trace=None):
    """Boucle besoin→comblement→assemblage. → (Theoreme_ou_None, provenances)."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
        var, libres_f,
    )
    from conj_base import _match, _instancier
    from conj_existe import conjoints_de, detachement_conjonctif
    from conjecturer import _comme_impl
    from outils_ia.decouvertes.besoin import besoins

    for _passe in range(passes):
        th, _manques = besoins(but, impls, faits, profondeur=2, trace=trace)
        if th is not None:
            return th, ["chaînage arrière"]
        combles = 0
        for (nom, T, A, B) in impls:
            s = {}
            if not _match(B, but, s, libres_f(T.conclusion)):
                continue
            Tp = _instancier(T, {k: t for k, t in s.items() if t != var(k)})
            ab = _comme_impl(Tp.conclusion)
            if ab is None:
                continue
            for c in conjoints_de(ab[0], faits):
                if c in faits:
                    continue
                r = combleur(c, borne)
                if r is not None:
                    nomf, thf = r
                    assert thf.est_clos and thf.conclusion == c
                    faits[c] = (nomf, thf)
                    combles += 1
                    if trace:
                        trace({"type": "comblé", "par": nomf})
            res, prov = detachement_conjonctif(Tp, faits)
            if res is not None and res.est_clos and res.conclusion == but:
                if trace:
                    trace({"type": "FERMÉ", "via": prov})
                return res, prov
        if combles == 0:
            break
    return None, []


__all__ = ["combleur", "fermer_par_besoin"]
