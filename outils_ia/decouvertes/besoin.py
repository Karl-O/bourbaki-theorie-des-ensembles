# -*- coding: utf-8 -*-
"""ORGANE DE BESOIN — la machine juge ce qui lui est nécessaire (ev.317-320).

Chaînage À REBOURS depuis un BUT : pour chaque implication A⇒B du pool dont le
conséquent B s'unifie au but (σ), le sous-but devient σ(A) —
  · si σ(A) est un fait connu → fermeture VÉRIFIÉE AU NOYAU (modus ponens) ;
  · sinon récursion bornée ; et si rien ne ferme → BESOINS machine-lisibles
    {pour, manque, via, chaîne}, ÉCLATÉS EN CONJOINTS (conjoints_de,
    arrêt-aux-faits) — seuls les insatisfaits sont nommés.

Philosophie (Karl, 8 août 2026) : on ne formalise un théorème que quand l'ALGO
l'a jugé nécessaire — la direction sort de la machine. Premier verdict réel :
pour Goldbach(32), la machine a désigné ses propres organes (∃-intro, pont)
et LE MUR (la borne). Pièges consignés : un but « hors de portée » peut être
fermable (interning : succ³(N2) EST N5 — l'organe avait raison) ; le chaîneur
ne sait pas CONJOINDRE (l'assembleur est `detachement_conjonctif`, cf.
`combleurs.fermer_par_besoin`).
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

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (  # noqa: E402
    var, libres_f,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import (  # noqa: E402
    noyau_abrege as N,
)
from conj_base import _match, _instancier, _fmt                       # noqa: E402

mp = N.modus_ponens


def _affiche(f):
    """Manque LISIBLE : l'imprimeur d'abord, le _fmt déplié en repli honnête."""
    try:
        from outils_ia.decouvertes.imprimeur import code_de, _registre_arithmetique
        _registre_arithmetique()
        return code_de(f)
    except Exception:
        return _fmt(f)[:120]


def _recomposer(f, faits, fermes):
    """⊢ f par recomposition : faits/fermés aux feuilles, ∧-intro aux nœuds.

    Miroir structurel de conjoints_de (arrêt-aux-faits) : et(a,b) est ABRÉGÉ
    ¬(¬a ∨ ¬b) — l'extraction suit cet encodage. → Theoreme | None."""
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
        conjonction_intro,
    )
    if f in faits:
        return faits[f][1]
    if f in fermes:
        return fermes[f]
    if (getattr(f, "tag", None) == "non" and f.sous[0].tag == "ou"
            and f.sous[0].sous[0].tag == "non" and f.sous[0].sous[1].tag == "non"):
        a = f.sous[0].sous[0].sous[0]
        b = f.sous[0].sous[1].sous[0]
        tha = _recomposer(a, faits, fermes)
        thb = _recomposer(b, faits, fermes)
        if tha is not None and thb is not None:
            th = conjonction_intro(tha, thb)
            if th.conclusion == f:
                return th
    return None


def besoins(but, impls, faits, profondeur=2, trace=None, _chaine=None,
            proposeurs=None):
    """→ (theoreme_ou_None, liste_de_besoins). Le noyau juge toute fermeture."""
    from conjecturer import _comme_impl
    from conj_existe import conjoints_de
    _chaine = _chaine or []
    _manques_temoins = []          # v14 : manques des routes-témoins échouées
    if but in faits:
        return faits[but][1], []
    # ── ORGANE V19 (12 août) : L'ORACLE NUMÉRIQUE EN GARDE-FOU. Avant de
    #    chercher une preuve, on CALCULE. Si le but est numériquement FAUX,
    #    aucune preuve n'existe : on le dit tout de suite au lieu de dépenser
    #    le budget. Coût mesuré d'une consultation qui ne conclut pas : 1 µs
    #    (l'index des formules est bâti une fois — cf. la loi « les termes
    #    sont opaques » dans ANOMALIES, 12 août).
    #    ⚠️ ASYMÉTRIE ESSENTIELLE : on n'utilise QUE le verdict FAUX. « Aucun
    #    contre-exemple » ne ferme rien et ne doit rien fermer — c'est
    #    exactement l'erreur que Goldbach illustre.
    try:
        from outils_ia.arithmetique.oracle_num import verite as _oracle
        if _oracle(but) is False:
            if trace:
                trace({"type": "réfuté", "but": _affiche(but), "via": "oracle"})
            return None, [{"manque": _affiche(but), "formule": but,
                           "chaine": _chaine, "refute": True}]
    except Exception:                                  # noqa: BLE001
        pass                                           # l'oracle ne bloque JAMAIS
    # ── ORGANE V9 (10 août, ev.381) : ÉGALITÉS RÉFLEXIVES. Un but t=t est
    #    vrai par le Théorème 1 (E I.39) mais restait un « manque » (mesuré :
    #    route JUMELLE de PB28, obligation 2k = 2k). Le noyau juge.
    if getattr(but, "tag", None) == "=" and but.termes[0] == but.termes[1]:
        from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import (
            noyau_abrege as _N9,
        )
        try:
            _th9 = _N9.reflexivite(but.termes[0])
        except Exception:
            _th9 = None
        if _th9 is not None and _th9.conclusion == but:
            if trace:
                trace({"type": "fermé", "but": _affiche(but), "via": "refl"})
            return _th9, []
    # ── ORGANE V16 (11 août, ev.410) : CONGRUENCE AUTOMATIQUE. Un but
    #    « u = v » dont les deux membres ne divergent qu'en UNE position se
    #    ramène à l'égalité des sous-termes divergents (congruence_terme,
    #    jugée noyau). Diagnostic : sur une opération NOUVELLE (a⊕b:=(a+b)+1),
    #    la machine fermait « a⊕b = b⊕a » dès qu'on lui DONNAIT la congruence,
    #    jamais sans — elle savait la chaîner, pas la fabriquer. C'est ce pas
    #    qui lui ouvre l'étude des structures dérivées. Détail : autonomie/
    #    congruence.py (anti-unification à une divergence, τ-termes compris).
    if (getattr(but, "tag", None) == "=" and profondeur > 1
            and but.termes[0] != but.termes[1]):
        from outils_ia.decouvertes.autonomie.congruence import (
            fermer_par_congruence as _fpc,
        )

        def _viser16(sous_but):
            _t, _ = besoins(sous_but, impls, faits, profondeur - 1, trace,
                            _chaine + ["congruence"], proposeurs)
            return _t

        _th16 = _fpc(but, _viser16)
        if _th16 is not None:
            if trace:
                trace({"type": "fermé", "but": _affiche(but), "via": "congruence"})
            return _th16, []
        # ── ORGANE V17 (11 août, ev.411) : RÉÉCRITURE. Une seule congruence
        #    ne suffit pas dès que la preuve demande d'associer PUIS commuter
        #    (mesuré : l'associativité de a⊕b:=(a+b)+1 échouait, chaîne
        #    « aucune route »). On enchaîne les égalités du pool, dans les
        #    deux sens, et on compose par transitivité. + ORGANE V18 (12 août,
        #    ev.412) : les lois sont INSTANCIÉES au moment d'être appliquées
        #    (le pool dit `a+b`, le but contient `(a+b)+1`). Bornes explicites
        #    dans autonomie/reecriture.py — le seul moteur qui explore.
        from outils_ia.decouvertes.autonomie.reecriture import (
            fermer_par_reecriture as _fpr,
        )
        _th17 = _fpr(but, faits)
        if _th17 is not None:
            if trace:
                trace({"type": "fermé", "but": _affiche(but), "via": "réécriture"})
            return _th17, []
    # ── ORGANE V4 (10 août, ev.369-370) : INSTANCIER les faits-∀. Un fait
    #    (∀x)φ = ¬∃x¬φ du pool peut conclure le but en φ[x:=t] — l'hypothèse
    #    S{n} du pas de descente est de cette forme et restait inerte. On
    #    unifie la matrice au but (σ sur la SEULE variable liée), le noyau
    #    juge l'instanciation.
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
        instancie as _inst,
    )
    for _ccl, (_nomf, _thf) in list(faits.items()):
        if not (getattr(_ccl, "tag", None) == "non" and _ccl.sous[0].tag == "exists"
                and _ccl.sous[0].sous[0].tag == "non"):
            continue
        _x = _ccl.sous[0].lieur
        _mat = _ccl.sous[0].sous[0].sous[0]
        _s = {}
        if not _match(_mat, but, _s, {_x}):
            continue
        _t = _s.get(_x)
        if _t is None:
            continue
        try:
            _thi = _inst(_thf, _t)
        except Exception:
            continue
        if _thi.conclusion == but:
            if trace:
                trace({"type": "fermé", "but": _affiche(but),
                       "via": _nomf + "[∀-inst]"})
            return _thi, []
    # ── ORGANE V8 (10 août, ev.375) : un but-CONJONCTION direct se ferme par
    #    récursion sur ses conjoints + recomposition ∧-intro (le symétrique de
    #    la v2, qui ne jouait que SOUS les routes). Nécessaire au cœur additif
    #    (premier ∧ premier ∧ somme).
    if (getattr(but, "tag", None) == "non" and but.sous[0].tag == "ou"
            and but.sous[0].sous[0].tag == "non" and but.sous[0].sous[1].tag == "non"
            and profondeur > 1):
        try:
            _mx = [c for c in conjoints_de(but, faits) if c not in faits]
        except Exception:
            _mx = None
        if _mx is not None:
            _fx = {}
            for _mc in _mx:
                _thm8, _ = besoins(_mc, impls, faits, profondeur - 1,
                                   trace, _chaine + ["∧-but"], proposeurs)
                if _thm8 is not None:
                    _fx[_mc] = _thm8
            if len(_fx) == len(_mx):
                _th8 = _recomposer(but, faits, _fx)
                if _th8 is not None and _th8.conclusion == but:
                    if trace:
                        trace({"type": "fermé", "but": _affiche(but),
                               "via": "∧-recomposition"})
                    return _th8, []

    # ── ORGANE V7 (10 août, ev.375) : ∃-DESCENTE À TÉMOINS PROPOSÉS. Un but
    #    ∃x φ n'était JAMAIS décomposé. Ici : chaque proposeur peut suggérer
    #    ("∃", terme) pour le but courant ; on vise φ[x:=t] (récursion) puis
    #    ré-introduction JUGÉE NOYAU (existe_temoin_verifie). Le cœur additif
    #    du pas de Goldbach (∃p∃q…) devient attaquable par témoins.
    if (getattr(but, "tag", None) == "exists" and proposeurs and profondeur > 1):
        from outils_ia.arithmetique.machine_num import (
            existe_temoin_verifie as _etv,
        )
        from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
            subst_f as _subst_f,
        )
        _xE = but.lieur
        _phi = but.sous[0]
        for _prop in proposeurs:
            try:
                _suggE = [s for s in _prop(but, faits)
                          if isinstance(s, tuple) and s[0] == "∃"]
            except Exception:
                continue
            for (_marq, _tE) in _suggE[:16]:
                try:
                    _cibleE = _subst_f(_tE, _xE, _phi)
                except Exception:
                    continue
                _thE, _mE = besoins(_cibleE, impls, faits, profondeur - 1,
                                    trace, _chaine + ["∃-témoin"], proposeurs)
                if _thE is None:
                    # ── ORGANE V14 (10 août, ev.401) : NE PLUS JETER les
                    #    manques d'une route-témoin qui échoue. Mesuré avec le
                    #    proposeur canonique (v13) : le but ∃ restait reporté
                    #    TEL QUEL alors que la descente avait déjà nommé les
                    #    obligations sur le témoin. On les garde ; elles ne
                    #    sont remontées que si AUCUN témoin ne ferme.
                    _manques_temoins.extend(_mE)
                    continue
                try:
                    _thEx = _etv(_thE, _phi, _tE, _xE)
                except Exception:
                    continue
                if _thEx.conclusion == but:
                    if trace:
                        trace({"type": "fermé", "but": _affiche(but),
                               "via": "∃-témoin[" + str(_tE)[:40] + "]"})
                    return _thEx, []
    #   ⚠️ v14 ne RETOURNE PAS ici : un return anticipé court-circuitait les
    #   organes suivants (v5, v6, boucle standard) et faisait exploser le coût
    #   en amont — mesuré ×2,7 sur l'intégration Goldbach. Les manques du
    #   témoin sont simplement FUSIONNÉS au rapport final ci-dessous.
    manques = []
    # ── ORGANE V5 (10 août, ev.372) : les faits-∀ D'IMPLICATION deviennent
    #    des ROUTES. On les RÉ-OUVRE (instancie à leur propre variable → elle
    #    redevient libre) et la boucle standard fait le reste (σ, sous-buts,
    #    recomposition v2). S{n} du pas de descente devient enfin actif.
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
        instancie as _inst5,
    )
    impls_all = list(impls)
    for _ccl, (_nomf, _thf) in list(faits.items()):
        if (getattr(_ccl, "tag", None) == "non" and _ccl.sous[0].tag == "exists"
                and _ccl.sous[0].sous[0].tag == "non"):
            _x5 = _ccl.sous[0].lieur
            try:
                _tho = _inst5(_thf, var(_x5))
            except Exception:
                continue
            _ab5 = _comme_impl(_tho.conclusion)
            if _ab5 and _ab5[0] != _ab5[1]:
                impls_all.append((_nomf + "[∀]", _tho, _ab5[0], _ab5[1]))
    # ── ORGANE V6-ébauche (10 août, ev.374) : PROPOSEURS DE TÉMOINS. Un
    #    proposeur(but, faits) suggère des (conclusion-∀ du pool, terme) ; la
    #    route instanciée AU TÉMOIN rejoint la boucle standard — le noyau
    #    juge, un mauvais témoin ne coûte qu'une route morte. C'est l'organe
    #    CRÉATIF demandé par la machine (¬(n=n), ev.373).
    for _prop in (proposeurs or []):
        try:
            _sugg = list(_prop(but, faits))
        except Exception:
            continue
        for (_cclp, _tp) in _sugg[:16]:
            _fp = faits.get(_cclp)
            if _fp is None:
                continue
            try:
                _thi = _inst5(_fp[1], _tp)
            except Exception:
                continue
            _abp = _comme_impl(_thi.conclusion)
            if _abp and _abp[0] != _abp[1]:
                impls_all.append((_fp[0] + "[témoin]", _thi, _abp[0], _abp[1]))
    for (nom, T, A, B) in impls_all:
        s = {}
        if not _match(B, but, s, libres_f(T.conclusion)):
            continue
        sig = {k: t for k, t in s.items() if t != var(k)}
        try:
            Tp = _instancier(T, sig) if sig else T
            ab = _comme_impl(Tp.conclusion)
            if ab is None or ab[1] != but:
                continue
            sous_but = ab[0]
        except Exception:
            continue
        if sous_but in faits:
            th = mp(faits[sous_but][1], Tp)
            if th.conclusion == but:
                if trace:
                    trace({"type": "fermé", "but": _affiche(but), "via": nom})
                return th, []
        if profondeur > 1:
            th_sb, m_sb = besoins(sous_but, impls, faits, profondeur - 1,
                                  trace, _chaine + [nom], proposeurs)
            if th_sb is not None:
                th = mp(th_sb, Tp)
                if th.conclusion == but:
                    if trace:
                        trace({"type": "fermé", "but": _affiche(but),
                               "via": nom, "profond": True})
                    return th, []
            manques.extend(m_sb)
        try:
            morceaux = [c for c in conjoints_de(sous_but, faits)
                        if c not in faits] or [sous_but]
        except Exception:
            morceaux = [sous_but]
        # ── ORGANE V2 (9 août 2026, diagnostic PB14-15) : les conjoints
        #    étaient NOMMÉS mais jamais RE-SOUMIS aux impls — les faits du
        #    pool qui les fermaient n'étaient jamais consultés. Ici : tenter
        #    de fermer CHAQUE morceau ; si TOUS ferment, recomposer la
        #    conjonction (∧-intro structurel) et conclure par modus ponens.
        if profondeur > 1 and morceaux != [sous_but]:
            fermes = {}
            for morceau in morceaux:
                th_m, _ = besoins(morceau, impls, faits, profondeur - 1,
                                  trace, _chaine + [nom, "∧"], proposeurs)
                if th_m is not None:
                    fermes[morceau] = th_m
            if len(fermes) == len(morceaux):
                th_sb2 = _recomposer(sous_but, faits, fermes)
                if th_sb2 is not None and th_sb2.conclusion == sous_but:
                    th = mp(th_sb2, Tp)
                    if th.conclusion == but:
                        if trace:
                            trace({"type": "fermé", "but": _affiche(but),
                                   "via": nom, "conjoints": len(fermes)})
                        return th, []
            # reporting v2 : seuls les morceaux RÉCALCITRANTS sont nommés —
            # ce qui ferme individuellement ne redevient pas un « manque ».
            morceaux = [m for m in morceaux if m not in fermes] or morceaux
        for morceau in morceaux:
            besoin = {"type": "besoin", "pour": _affiche(but),
                      "manque": _affiche(morceau), "formule": morceau,
                      "via": nom, "chaine": " > ".join(_chaine + [nom])}
            manques.append(besoin)
            if trace:
                trace({k: v for k, v in besoin.items() if k != "formule"})
    # ── ORGANE V14 (10 août, ev.401) : les manques nommés par une route-témoin
    #    ÉCHOUÉE ne sont plus jetés. Ils remplacent le rapport « le but ∃
    #    lui-même » — bien plus informatif : ce sont les obligations portant
    #    sur le témoin proposé (avec v13, exactement la forme de GG9).
    if _manques_temoins:
        return None, manques + _manques_temoins
    if not manques:
        # AUCUNE route : le manque, c'est le but lui-même — le DIRE (piège
        # mesuré PB8 : le silence ressemblait à « rien à signaler »).
        manques = [{"type": "besoin", "pour": _affiche(but),
                    "manque": _affiche(but), "formule": but,
                    "via": "∅", "chaine": " > ".join(_chaine) or "(aucune route)"}]
        if trace:
            trace({k: v for k, v in manques[0].items() if k != "formule"})
    return None, manques


__all__ = ["besoins"]
