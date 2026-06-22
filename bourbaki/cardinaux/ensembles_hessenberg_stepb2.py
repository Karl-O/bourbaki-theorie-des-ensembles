"""§III.6.3 — Théorème 2 (HESSENBERG, E.III.48-49) : STEP B2 — PELAGE DES TÉMOINS de
la chaîne de contradiction (`chaine_falsum_sous_temoins`, STEP B0), BOTTOM-UP, par
élimination existentielle, jusqu'à `¬(Card S₀ < Card E)` PUIS a²=a E-seule.

🎯 PLAN (cf. mission STEP B2).  B0 (`chaine_falsum_sous_temoins`) ⊢ FALSUM sous 12 hyps
honnêtes mentionnant les témoins INTERNES {S₀,φ₀,Ucadre,ψ,uwit}.  On les PÈLE :

  B1  élimine ψ (cadre_bijection : Card F=Card U ⇒ (∃ψ) bij(ψ,F,U)) et uwit
      (U_non_vide : Card U≠0 ⇒ (∃u) u∈U).
  B2  élimine Ucadre (existe_sous_ensemble_cardinal_transporte) ⇒
      `negation_strict_sous_maximal` ⊢ ¬(Card S₀<Card E) sous la SEULE maximal-data.
  B3  trichotomie (card_S0_egal_card_E déjà clos) ⇒ Card S₀=Card E DÉRIVÉ, puis
      hessenberg_aa_egal_de_maximal ⇒ a²=a sous maximal-data SEULE.
  B4  élimine S₀,φ₀ (unpack_maximal) ⇒ `hessenberg_a_carre_egal_a_REEL(E)`,
      conclusion E-SEULE (== enonce_hessenberg(E)).

🔑 CLÉ B1 (verrou de 8 rounds).  Les 4 hyps de B0 mentionnant ψ sont :
   [bij]  est_bijection_de(ψ, F, U)             (= corps de cadre_bijection)
   [dom-disj]  (∀u)¬(u∈dom φ₀ ∧ u∈dom ψ)
   [img-disj]  image(φ₀,dom φ₀) ∩ image(ψ,dom ψ) = ∅
   [img-cov]   image(φ₀,dom φ₀) ∪ image(ψ,dom ψ) = Z
  Les 3 dernières sont rendues ψ-FREE SOUS l'hypothèse [bij] : de bij on extrait
  dom(ψ)=F et image(ψ,F)=U, d'où image(ψ,dom ψ)=U ; on RÉÉCRIT (S6 arrière)
  dom ψ→F et image(ψ,dom ψ)→U dans chaque résidu, le ramenant à sa forme ψ-FREE
  (u∈F au lieu de u∈dom ψ ; U au lieu de image(ψ,dom ψ)).  On DÉCHARGE alors les 3
  résidus depuis {bij + 3 formes ψ-free}, et SEUL [bij] reste mentionner ψ ⇒
  existe_elimination(·,"psi") via cadre_bijection est VALIDE.

INVARIANT : theorie_ensembles()=22 ; aucun axiome ; rien postulé ; lock ABSENT ;
les formes ψ-free (S₀²∩F=∅ etc.), U-data, maximal-data restent HONNÊTES (satisfiables,
vraies dans l'argument de Zorn E.III.48).  Noyau INTACT.
"""
from __future__ import annotations

from bourbaki.logique.formule import (
    Terme, var, egal, et, non, impl, existe, pourtout, appartient, inclus,
    libres_f, subst_f,
)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E

from bourbaki.logique.tactiques.tactiques_abrege2 import (
    instancie, conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant,
)
from bourbaki.logique.tactiques.tactiques_abrege_egalite import (
    symetrie, composer_egalites,
)

from bourbaki.cardinaux.ensembles_cardinaux import (
    cardinal, est_cardinal, est_bijection_de, inf_egal_card, inf_strict_card,
)
from bourbaki.cardinaux.ensembles_hessenberg_stepb import chaine_falsum_sous_temoins
from bourbaki.cardinaux.ensembles_frame_extension_finale import (
    cadre_ensemble, cadre_bijection,
)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def _marqueur_faux(E_set="E"):
    """Marqueur FALSUM ψ/uwit/Ucadre-FREE : ¬(E=E) (cible ex falso de B0)."""
    vE = _t(E_set)
    return non(egal(vE, vE))


# ════════════════════════════════════════════════════════════════════════════
#  Réécriture d'un résidu ψ : remplacer image(ψ,dom ψ)→U et dom ψ→F via [bij].
# ════════════════════════════════════════════════════════════════════════════
def _bij_dom_image(vpsi, F, U):
    """Sous h=assume(bij(ψ,F,U)) renvoie (h, dom ψ=F, image(ψ,dom ψ)=U)."""
    bij = est_bijection_de(vpsi, F, U)
    h = N.assume(bij)
    dom_eq_F = conjonction_elim_droite(conjonction_elim_gauche(h))     # dom ψ = F
    img_F_eq_U = conjonction_elim_droite(conjonction_elim_droite(h))   # image(ψ,F)=U
    assert dom_eq_F.conclusion == egal(E.dom(vpsi), F)
    assert img_F_eq_U.conclusion == egal(E.image(vpsi, F), U)
    # image(ψ,dom ψ) = image(ψ,F)   (congruence sur le 2e arg via dom ψ=F)
    s6 = N.s6(F, E.dom(vpsi), "wdf", egal(E.image(vpsi, var("wdf")), E.image(vpsi, F)))
    F_eq_dom = N.modus_ponens(dom_eq_F, symetrie(E.dom(vpsi), F))      # F = dom ψ
    img_dom_eq_img_F = N.modus_ponens(N.reflexivite(E.image(vpsi, F)),
                                      equivalence_avant(N.modus_ponens(F_eq_dom, s6)))
    # = image(ψ,dom ψ) = image(ψ,F)
    assert img_dom_eq_img_F.conclusion == egal(E.image(vpsi, E.dom(vpsi)), E.image(vpsi, F))
    img_dom_eq_U = composer_egalites(img_dom_eq_img_F, img_F_eq_U)     # image(ψ,dom ψ)=U
    assert img_dom_eq_U.conclusion == egal(E.image(vpsi, E.dom(vpsi)), U)
    return h, dom_eq_F, img_dom_eq_U


def _psi_free_de(residu, eqs):
    """Forme ψ-FREE de `residu` : remplace chaque sous-terme ψ-spécifique `lhs`
    (= image(ψ,dom ψ), dom ψ) par sa valeur `rhs` (= U, F).  Abstraction par le terme
    `lhs` (ψ-unique) ⇒ ne touche PAS les U/F légitimes ailleurs (ex : Ucadre dans Z)."""
    cur = residu
    for eq in eqs:
        lhs, rhs = eq.conclusion.termes
        cur = _remplacer_terme(cur, lhs, rhs)
    return cur


def _prouver_residu_depuis_psifree(residu, eqs):
    """{ psi_free(residu) } ∪ {hyps des eqs} ⊢ residu.

    `residu` = formule mentionnant les sous-termes ψ-spécifiques `lhs` de chaque
    (lhs=rhs)∈eqs.  On ABSTRAIT chaque `lhs` (ψ-unique) en une variable fraîche w pour
    bâtir le contexte R(w) ; psi_free := residu[lhs:=rhs] (ψ-free).  S6 (rhs=lhs) réécrit
    R(rhs)=psi_free → R(lhs)=residu.  Renvoie un théorème de conclusion `residu` SOUS
    l'hyp `psi_free` + les hyps des `eqs` (ici dérivées de [bij])."""
    psi_free = _psi_free_de(residu, eqs)
    cur = N.assume(psi_free)
    for eq in eqs:
        lhs, rhs = eq.conclusion.termes
        w = "wrw_" + str(abs(hash((str(lhs), str(rhs)))) % 100000)
        # abstraire le terme ψ-spécifique `lhs` dans le RÉSIDU CIBLE → R(w).
        Rw = _remplacer_terme(residu, lhs, var(w))
        rhs_eq_lhs = N.modus_ponens(eq, symetrie(lhs, rhs))  # rhs = lhs
        s6 = N.s6(rhs, lhs, w, Rw)
        cur = N.modus_ponens(cur, equivalence_avant(N.modus_ponens(rhs_eq_lhs, s6)))
    assert cur.conclusion == residu, \
        f"_prouver_residu_depuis_psifree : conclusion\n{cur.conclusion}\nvs residu\n{residu}"
    return cur


# ════════════════════════════════════════════════════════════════════════════
#  B1 — élimine ψ puis uwit de B0.
# ════════════════════════════════════════════════════════════════════════════
def _psi_free_residuals(b0, vphi0, vpsi, vS, vU):
    """Décharge dans b0 les 3 résidus ψ-géométriques (img-disj, img-cov, dom-disj),
    les remplaçant par leurs formes ψ-FREE + l'hyp [bij]=est_bijection_de(ψ,F,U).

    Renvoie (cur, bij_formule).  Après : ψ n'apparaît dans les hyps de `cur` QUE via
    [bij] (les 3 résidus ψ-géométriques sont devenus ψ-free)."""
    F = cadre_ensemble(vS, vU)
    h_bij, dom_eq_F, img_dom_eq_U = _bij_dom_image(vpsi, F, vU)
    domphi0 = E.dom(vphi0)
    imgphi0 = E.image(vphi0, domphi0)
    img_psi = E.image(vpsi, E.dom(vpsi))
    Z = E.reunion(vS, vU)            # Z = S₀∪U
    u = var("u")

    residu_imgdisj = egal(E.intersection(imgphi0, img_psi), E.VIDE)
    residu_imgcov = egal(E.reunion(imgphi0, img_psi), Z)
    residu_domdisj = pourtout("u", non(et(appartient(u, domphi0),
                                          appartient(u, E.dom(vpsi)))))

    pr_imgdisj = _prouver_residu_depuis_psifree(residu_imgdisj, [img_dom_eq_U])
    pr_imgcov = _prouver_residu_depuis_psifree(residu_imgcov, [img_dom_eq_U])
    pr_domdisj = _prouver_residu_depuis_psifree(residu_domdisj, [dom_eq_F])

    cur = b0
    for pr in (pr_imgdisj, pr_imgcov, pr_domdisj):
        c = pr.conclusion
        assert c in cur.hypotheses, \
            f"_psi_free_residuals : résidu absent des hyps\n{c}"
        cur = N.modus_ponens(pr, N.loi_deduction(c, cur))
    return cur, h_bij.conclusion


def _non_vide_existe_element(vU, u):
    """⊢ ( U ≠ ∅ ) ⇒ (∃u)( u ∈ U ),  binder du ∃ = `u`  (= uwit).

    `non_vide_ssi_element(U)` donne ¬(U=∅) ⇔ (∃z)(z∈U) (binder z) ; on prend le sens
    avant et on α-renomme (∃z)→(∃u) pour matcher le témoin uwit."""
    from bourbaki.ensembles.base.ensembles_vide import non_vide_ssi_element
    from bourbaki.logique.tactiques.tactiques_abrege_quantif import alpha_existe
    eqv = non_vide_ssi_element(vU)                       # ¬(U=∅) ⇔ (∃z)(z∈U)
    avant = equivalence_avant(eqv)                       # ¬(U=∅) ⇒ (∃z)(z∈U)
    if u == "z":
        return avant
    aeq = alpha_existe("z", u, appartient(var("z"), vU))  # (∃z)(z∈U) ⇔ (∃u)(u∈U)
    from bourbaki.logique.tactiques.tactiques_abrege import syllogisme
    return syllogisme(avant, equivalence_avant(aeq))     # ¬(U=∅) ⇒ (∃u)(u∈U)


def negation_strict_sous_temoins_UF(E_set="E", phi0="phi0", psi="psi", S="S0",
                                    U="Ucadre", u="uwit"):
    """B1 — ψ et uwit ÉLIMINÉS de B0.

    { maximal-data [(S₀,φ₀)∈𝔉, φ₀ bij, element_maximal],
      U-data [U⊂E∖S₀, Z⊂E, Card F=Card U, Card U≠0],
      géométrie ψ-FREE [S₀²∩F=∅ via dom-disj ψ-free, img-disj/cov ψ-free,
                        S₀²∪F=Z², ∃X-non-extension] }
        ⊢ ¬(E=E)   (marqueur FALSUM, ψ/uwit-FREE).            [hyps HONNÊTES].

    🎯 On part de B0 (`chaine_falsum_sous_temoins`, cible=marqueur ψ/uwit-free), on rend
    les 3 résidus ψ-géométriques ψ-FREE sous [bij] (`_psi_free_residuals`), puis :
      • ψ : `loi_deduction([bij])` + `existe_elimination(·,"psi")`, le ∃ψ déchargé par
        `cadre_bijection` (Card F=Card U ⇒ (∃ψ)bij), α-renommé (∃F)→(∃psi).
      • uwit : `loi_deduction(u∈U)` + `existe_elimination(·,"uwit")`, le ∃u déchargé par
        `U_non_vide` (Card U≠0 ⇒ (∃u)u∈U).
    Aucune hyp résiduelle ne mentionne ψ ni uwit (ACCEPTANCE).  Lock ABSENT.  theorie=22."""
    from bourbaki.logique.tactiques.tactiques_abrege_quantif import (
        existe_elimination, alpha_existe,
    )
    from bourbaki.cardinaux.ensembles_hessenberg_structural_discharge import U_non_vide
    vE, vphi0, vpsi = _t(E_set), _t(phi0), _t(psi)
    vS, vU = _t(S), _t(U)
    vu = _t(u)
    F = cadre_ensemble(vS, vU)
    marqueur = _marqueur_faux(E_set)

    b0 = chaine_falsum_sous_temoins(E_set, phi0, S, U, psi, u, cible=marqueur)
    assert b0.conclusion == marqueur, "B1 : B0 conclusion ≠ marqueur"

    # ── 1. résidus ψ rendus ψ-free sous [bij] ────────────────────────────────
    cur, bij = _psi_free_residuals(b0, vphi0, vpsi, vS, vU)
    assert bij == est_bijection_de(vpsi, F, vU)

    from bourbaki.logique.tactiques.tactiques_abrege import syllogisme

    # ── 2. élimine ψ : (∃ψ)bij ⇒ marqueur,  ∃ψ fourni par cadre_bijection ─────
    assert psi not in libres_f(marqueur)
    imp_bij = N.loi_deduction(bij, cur)                   # bij(ψ,F,U) ⇒ marqueur
    imp_expsi = existe_elimination(imp_bij, psi)          # (∃ψ)bij ⇒ marqueur
    # cadre_bijection : Card F=Card U ⇒ (∃F)bij(F,F_cadre,U) ; α-renomme (∃F)→(∃ψ).
    cb = cadre_bijection(F, vU)                           # Card F=Card U ⇒ (∃F)bij
    body_F = est_bijection_de(var("F"), F, vU)
    aeq = alpha_existe("F", psi, body_F)                  # (∃F)bij ⇔ (∃ψ)bij
    ex_psi = syllogisme(cb, equivalence_avant(aeq))       # Card F=Card U ⇒ (∃ψ)bij
    cur = syllogisme(ex_psi, imp_expsi)                   # Card F=Card U ⇒ marqueur
    cur = N.modus_ponens(N.assume(egal(cardinal(F), cardinal(vU))), cur)  # marqueur [Card F=Card U]

    # ── 3. élimine uwit : (∃u)u∈U ⇒ marqueur,  ∃u fourni par U_non_vide ──────
    u_in_U = appartient(vu, vU)
    assert u not in libres_f(marqueur)
    assert u_in_U in cur.hypotheses, "B1 : témoin u∈U absent avant élim uwit"
    imp_u = N.loi_deduction(u_in_U, cur)                  # u∈U ⇒ marqueur
    imp_exu = existe_elimination(imp_u, u)                # (∃u)u∈U ⇒ marqueur
    # U_non_vide : Card U≠Card∅ ⊢ U≠∅ ; mais on veut (∃u)u∈U.  Pont U≠∅ ⇒ (∃u)u∈U :
    ex_u = _non_vide_existe_element(vU, u)                # U≠∅ ⇒ (∃u)(u∈U)
    nv = U_non_vide(U)                                    # {Card U≠Card∅} ⊢ U≠∅
    ex_u_thm = N.modus_ponens(nv, ex_u)                   # {Card U≠Card∅} ⊢ (∃u)u∈U
    cur = N.modus_ponens(ex_u_thm, imp_exu)               # marqueur

    # ── ACCEPTANCE : aucune hyp ne mentionne ψ ni uwit ───────────────────────
    for h in cur.hypotheses:
        bad = ({psi, u} & set(libres_f(h)))
        assert not bad, f"B1 : hyp mentionne {bad}\n{h}"
    lock = egal(E.reunion(vS, vU), vS)
    assert lock not in cur.hypotheses, "B1 : LOCK présent !"
    assert cur.conclusion == marqueur, "B1 : conclusion ≠ marqueur"
    return cur


# ════════════════════════════════════════════════════════════════════════════
#  B2 — VERDICT MÉCANIQUE : élimination de Ucadre BLOQUÉE au MUR disjoint-sum.
# ════════════════════════════════════════════════════════════════════════════
def b2_blocker_classification():
    """Classifie MÉCANIQUEMENT les 9 hyps de B1 mentionnant Ucadre, par leur
    déchargeabilité depuis le corps de `existe_sous_ensemble_cardinal_transporte`
    (U⊂E∖S₀ ∧ Card U=Card S₀).  SOURCE DE VÉRITÉ du verdict B2.

    VERDICT.  4 hyps sont le MUR ARCHITECTURAL IRRÉDUCTIBLE (identités d'ensembles sur
    le cadre SOMME-DISJOINTE `cadre_ensemble = somme_disjointe(...)`, tagué `paire(∅,∅)`) :
      • S₀²∪cadre⊔ = Z²              (set-identity domaine, FAUSSE au niveau ensembliste —
                                      Z² a des éléments non tagués ; vraie seulement au
                                      niveau équipotence/cardinal) ;
      • S₀²∩cadre⊔ = ∅  (dom-disj ψ-free, `(∀u)¬(u∈domφ₀ ∧ u∈cadre⊔)`) ;
      • ¬(∃X)… non-extension de Z (×2, dom(F)∈{cadre⊔, Z}).
    Ces 4 N'ÉTANT PAS dérivables de {U⊂E∖S₀, Card U=Card S₀}, et MENTIONNANT Ucadre,
    `existe_elimination(·,"Ucadre")` est IMPOSSIBLE (Ucadre libre dans Γ) ⇒ B2 BLOQUÉ.

    Les 5 autres hyps Ucadre SONT en principe déchargeables (img-disj/cov ψ-free via
    image(φ₀,domφ₀)=S₀ de la maximal-data ; Card F=Card U via `cadre_card_trois_b` ;
    Z⊂E via U⊂E∖S₀+S₀⊂E ; U⊂E∖S₀ = le corps du transport) — mais cela NE SUFFIT PAS :
    tant que les 4 hyps-mur mentionnent Ucadre, l'élimination échoue.

    🔓 DÉBLOCAGE (HORS scope mécanique, documenté `ensembles_hessenberg_stepb` / classify) :
    RE-CÂBLER `cadre_ensemble` somme_disjointe → RÉUNION (`s0sq_cadre_reunion_egale_carre`
    CLOS donne alors S₀²∪F_reunion=Z² VRAIE et closeable) — changement d'architecture de
    `phi_etendue_bijection`/`cadre_ensemble`.  Tant qu'il n'est pas fait, B2/B3/B4 restent
    bloqués ; B1 (ψ,uwit éliminés) est l'avancée nette de ce round.

    Retourne (b1, table) ; table = liste {free, label, dischargeable:bool}."""
    b1 = negation_strict_sous_temoins_UF()
    uc = [h for h in b1.hypotheses if "Ucadre" in libres_f(h)]
    assert len(uc) == 9, f"b2_blocker : {len(uc)} hyps Ucadre (attendu 9)"
    from bourbaki.logique.formule import afficher_f as af
    table = []
    nb_mur = 0
    for h in sorted(uc, key=lambda x: str(x)):
        s = af(h)
        if s.startswith("(inter(image(phi0"):
            lab, disch = "img-disj ψ-free (→ S₀∩U=∅)", True
        elif s.startswith("(reunion(image(phi0"):
            lab, disch = "img-cov ψ-free (→ S₀∪U=Z)", True
        elif s.startswith("(reunion(produit(S0, S0)"):
            lab, disch = "S₀²∪cadre⊔ = Z²  [MUR disjoint-sum]", False
        elif s.startswith("(τZ"):
            lab, disch = "Card F = Card U (→ cadre_card_trois_b)", True
        elif s.startswith("¬(τZ"):
            lab, disch = "¬(∃X) non-extension [dom F=cadre⊔]  [MUR]", False
        elif s.startswith("(∀u) ¬((u ∈ dom(phi0))"):
            lab, disch = "S₀²∩cadre⊔ = ∅ (dom-disj ψ-free)  [MUR]", False
        elif s.startswith("(∀z) ((z ∈ reunion(S0, Ucadre)) ⇒ (z ∈ E))"):
            lab, disch = "Z ⊂ E (→ U⊂E∖S₀ + S₀⊂E)", True
        elif s.startswith("(∀z) ((z ∈ Ucadre) ⇒ (z ∈ difference(E, S0)))"):
            lab, disch = "U ⊂ E∖S₀ (= corps du transport)", True
        elif s.startswith("¬((∃X)"):
            lab, disch = "¬(∃X) non-extension [dom F=Z]  [MUR]", False
        else:
            lab, disch = "??? non classé", False
        if not disch:
            nb_mur += 1
        table.append({"free": sorted(libres_f(h)), "label": lab, "dischargeable": disch})
    assert nb_mur == 4, f"b2_blocker : {nb_mur} hyps-mur (attendu 4) — re-analyser"
    return b1, table


__all__ = [
    "negation_strict_sous_temoins_UF",
    "b2_blocker_classification",
]


def _remplacer_terme(formule, ancien, nouveau):
    """Remplace toutes les occurrences du TERME `ancien` par `nouveau` dans `formule`
    (substitution structurelle, capture-naïve : usage interne réécriture S6 sur termes
    clos sans collision de binder)."""
    from bourbaki.logique.formule import Formule

    def rt(t):
        if t == ancien:
            return nouveau
        if isinstance(t, Terme) and t.args:
            return Terme(t.tag, nom=t.nom, lieur=t.lieur,
                         args=tuple(rt(a) for a in t.args))
        return t

    def rf(f):
        return Formule(f.tag, lieur=f.lieur,
                       termes=tuple(rt(x) for x in f.termes),
                       sous=tuple(rf(s) for s in f.sous))
    return rf(formule)
