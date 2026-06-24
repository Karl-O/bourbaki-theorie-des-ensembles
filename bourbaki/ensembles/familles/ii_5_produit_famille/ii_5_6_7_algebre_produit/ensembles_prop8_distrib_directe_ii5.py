"""§II.5 — PROPOSITION 8 (E II.35–36, n°6 « Formules de distributivité »).

ÉNONCÉ VERBATIM (Bourbaki, E II.35, Proposition 8) :
    « Soit ((X_{λ,ι})_{ι∈J_λ})_{λ∈L} une famille (admettant L pour ensemble
      d'indices) de familles d'ensembles.  On suppose L ≠ ∅ et J_λ ≠ ∅ pour tout
      λ ∈ L.  Soit  I = ∏_{λ∈L} J_λ ≠ ∅.  On a
          ⋃_{λ∈L} ( ⋂_{ι∈J_λ} X_{λ,ι} )  =  ⋂_{f∈I} ( ⋃_{λ∈L} X_{λ,f(λ)} )      (1)
      et   ⋂_{λ∈L} ( ⋃_{ι∈J_λ} X_{λ,ι} )  =  ⋃_{f∈I} ( ⋂_{λ∈L} X_{λ,f(λ)} ). »   (2)

CIBLE DE CE MODULE — la PREMIÈRE INCLUSION de la formule (1), SEULE :

    ⊢  ⋃_{λ∈L} ( ⋂_{ι∈J_λ} X_{λ,ι} )  ⊂  ⋂_{f∈I} ( ⋃_{λ∈L} X_{λ,f(λ)} ).

INCLUSION DIRECTE SEULE, RÉCIPROQUE = CHOIX EXCLU.  Bourbaki démontre l'égalité (1)
en deux temps (E II.36) :
  • le sens ⊂ (celui formalisé ici) est PUREMENT PONCTUEL — « Soit x ∈ ⋃_λ⋂_ι X_{λ,ι} ;
    il existe λ tel que x∈⋂_ι X_{λ,ι} ; on a par suite x∈X_{λ,f(λ)}, d'où x∈⋃_λ X_{λ,f(λ)} ;
    ceci étant vrai pour tout f∈I, on a x∈⋂_f⋃_λ X_{λ,f(λ)} » — AUCUN axiome du choix ;
  • le sens ⊃ utilise « le cor. 2 de la prop. 5 (II, p. 34) » (existence d'une fonction
    de choix f∈I=∏J_λ), donc le signe τ / le CHOIX : il est HORS CIBLE de ce module.

PARAMÉTRAGE FIDÈLE (mécanisme C54 « famille définie par un terme »).
──────────────────────────────────────────────────────────────────────────────────
Les deux familles EXTERNES de (1) ne sont pas des termes calculables : une famille
est un graphe fonctionnel quelconque (E.II.4.1), et `valeur_famille(G, λ)` est un
TERME OPAQUE — rien dans la théorie de base ne le relie à `inter_famille(...)`.  Comme
pour la famille des complémentaires `complement_famille` (AXIOME_COMPL_FAM, De Morgan
des familles), on NOMME ces familles par des paramètres et on les CARACTÉRISE par leur
ι-ème terme, via des axiomes-schémas (C54) portés par une THÉORIE LOCALE dédiée
`theorie_distrib(...)` — strictement comme `theorie_graphe_terme` / `theorie_diagonale_cantor`
/ `theorie_exposant`.  Cette théorie locale n'entre PAS dans `theorie_ensembles()`, qui
reste à 22 axiomes ; les axiomes-schémas sont des DÉFINITIONS (légitimées par S8+A1),
pas des hypothèses : `N.axiome(theorie_distrib, …)` produit `∅ ⊢ …` (théorème CLOS).

Notations (XX, J, L paramètres libres) :
  • X_{λ,ι} = valeur_famille( valeur_famille(XX, λ), ι )   (famille de familles) ;
  • J_λ     = valeur_famille(J, λ) ;   I = ∏_{λ∈L} J_λ = produit_famille(J, L) ;
  • f(λ)    = valeur(f, λ) ;
  • GL  : famille λ ↦ ⋂_{ι∈J_λ} X_{λ,ι}        [AX_GL  : valeur_famille(GL,λ)=inter_famille(XX_λ,J_λ)] ;
  • GRin(f) : famille λ ↦ X_{λ,f(λ)}            [AX_RIN : valeur_famille(GRin_f,λ)=X_{λ,f(λ)}] ;
  • GR  : famille f ↦ ⋃_{λ∈L} X_{λ,f(λ)}        [AX_GR  : valeur_famille(GR,f)=reunion_famille(GRin_f,L)].

STRATÉGIE (preuve ponctuelle, calquée sur le plan validé) :
  Soit x ; h = assume(x ∈ ⋃_λ ⋂_ι X_{λ,ι}).
  (1) membre_reunion_famille (sens AVANT) : (∃λ)(λ∈L et x∈⋂_{ι∈J_λ}X_{λ,ι}).
  (2) existe_elimination : témoin λ₀, avec λ₀∈L et x∈⋂_{ι∈J_λ₀}X_{λ₀,ι}.
  (3) but x∈⋂_{f∈I}(…) : membre_inter_famille (sens ARRIÈRE) ⇐ (∀f)(f∈I ⇒ x∈⋃_λ X_{λ,f(λ)}) ;
      f frais, hf = assume(f∈I).
  (4) f∈I=∏J_λ ⇒ f(λ₀)∈J_λ₀  : projection_dans_facteur + λ₀∈L.
  (5) inter_famille_elim (sur J_λ₀) : x∈⋂_{ι∈J_λ₀} ⇒ (f(λ₀)∈J_λ₀ ⇒ x∈X_{λ₀,f(λ₀)}) → x∈X_{λ₀,f(λ₀)}.
  (6) reunion_famille_intro (sur L) : (λ₀∈L et x∈X_{λ₀,f(λ₀)}) ⇒ x∈⋃_λ X_{λ,f(λ)}.
  (7) loi_deduction(f∈I,…), generalisation(f), equivalence_arriere(membre_inter_famille) → x∈⋂_f.
  (8) décharge témoin (existe_elimination), loi_deduction(x∈⋃…, but), generalisation(x).

STATUT : CLOS (0 hypothèse pendante).  theorie_ensembles() = 22 axiomes (inchangée).
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (Terme, var, et, impl, appartient, egal,
                                       inclus, pourtout)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    instancie, equivalence_avant, equivalence_arriere, conjonction_intro)
from bourbaki.logique.i_3_quantifies.tactiques_abrege_quantif import (
    existe_elimination, alpha_pour_tout, alpha_existe)
from bourbaki.ensembles.familles.ii_4_reunion_intersection_familles.ii_4_1_definitions_algebre.ensembles_familles import (
    membre_reunion_famille)
from bourbaki.ensembles.familles.ii_5_produit_famille.ii_5_definitions.ensembles_produit_famille import (
    projection_dans_facteur)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# ── notations dérivées ────────────────────────────────────────────────────────
def _X(xx, lam, iota):
    """X_{λ,ι} = valeur_famille(valeur_famille(XX,λ), ι)  (famille de familles)."""
    return E.valeur_famille(E.valeur_famille(xx, lam), iota)


def _Jlam(j, lam):
    """J_λ = valeur_famille(J, λ)."""
    return E.valeur_famille(j, lam)


def _membre_gauche(xx="XX", j="J", L="L", gl="GL"):
    """⋃_{λ∈L} (⋂_{ι∈J_λ} X_{λ,ι}) = reunion_famille(GL, L)  (GL caractérisée par AX_GL)."""
    return E.reunion_famille(_t(gl), _t(L))


def _membre_droit(gr="GR", j="J", L="L"):
    """⋂_{f∈I} (⋃_{λ∈L} X_{λ,f(λ)}) = inter_famille(GR, I),  I = ∏_{λ∈L} J_λ."""
    return E.inter_famille(_t(gr), E.produit_famille(_t(j), _t(L)))


# ── axiomes-schémas (C54) de définition des familles externes ─────────────────
def _ax_gl(xx, j, L, gl, lam="lam"):
    """AX_GL : (∀λ) valeur_famille(GL, λ) = ⋂_{ι∈J_λ} X_{λ,ι}.

    « GL est la famille λ ↦ ⋂_{ι∈J_λ} X_{λ,ι}. »  (déf. par un terme, C54.)"""
    vlam = var(lam)
    return pourtout(lam, egal(E.valeur_famille(gl, vlam),
                              E.inter_famille(E.valeur_famille(xx, vlam), _Jlam(j, vlam))))


def _ax_rin(xx, grin, ff, L, lam="lam"):
    """AX_RIN : (∀λ) valeur_famille(GRin_f, λ) = X_{λ,f(λ)}.

    « GRin_f est la famille λ ↦ X_{λ,f(λ)}. »  (déf. par un terme, C54 ; f fixé.)"""
    vlam = var(lam)
    return pourtout(lam, egal(E.valeur_famille(grin, vlam),
                              _X(xx, vlam, E.valeur(ff, vlam))))


def _ax_gr(xx, grin, gr, ff, L, eff="g"):
    """AX_GR : (∀g) valeur_famille(GR, g) = ⋃_{λ∈L} X_{λ,g(λ)} = reunion_famille(GRin_g, L).

    « GR est la famille g ↦ ⋃_{λ∈L} X_{λ,g(λ)}. »  Ici on caractérise GR EN f
    (le f courant de l'intersection) : valeur_famille(GR,f) = reunion_famille(GRin_f, L)."""
    return egal(E.valeur_famille(gr, ff), E.reunion_famille(grin, _t(L)))


def theorie_distrib(xx="XX", j="J", L="L", gl="GL", grin="GRin", gr="GR", ff="f"):
    """Théorie LOCALE portant les trois axiomes-schémas C54 de définition des
    familles externes GL, GRin_f, GR (instances aux paramètres concrets).

    N'entre PAS dans theorie_ensembles() (qui reste à 22) : ce sont des DÉFINITIONS
    (S8+A1), pas des hypothèses ; chaque `N.axiome(theorie_distrib, …)` donne `∅ ⊢ …`."""
    vxx, vj, vL = _t(xx), _t(j), _t(L)
    vgl, vgrin, vgr, vff = _t(gl), _t(grin), _t(gr), _t(ff)
    return N.Theorie("Distributivite-ext", [
        _ax_gl(vxx, vj, vL, vgl),
        _ax_rin(vxx, vgrin, vff, vL),
        _ax_gr(vxx, vgrin, vgr, vff, vL),
    ])


# ── cible ─────────────────────────────────────────────────────────────────────
def _cible(xx="XX", j="J", L="L", gl="GL", gr="GR"):
    """⊢-cible : ⋃_{λ∈L}(⋂_{ι∈J_λ}X_{λ,ι}) ⊂ ⋂_{f∈I}(⋃_{λ∈L}X_{λ,f(λ)})."""
    return inclus(_membre_gauche(xx, j, L, gl), _membre_droit(gr, j, L))


# ── théorème principal ────────────────────────────────────────────────────────
def distributivite_reunion_inter_inclusion_directe(
        xx="XX", j="J", L="L", gl="GL", grin="GRin", gr="GR", ff="f"):
    """⊢ ⋃_{λ∈L}(⋂_{ι∈J_λ}X_{λ,ι}) ⊂ ⋂_{f∈I}(⋃_{λ∈L}X_{λ,f(λ)}),  I = ∏_{λ∈L}J_λ.

    PROPOSITION 8, formule (1), PREMIÈRE INCLUSION (sens ⊂), E II.35–36.  Inclusion
    DIRECTE PONCTUELLE — la réciproque (sens ⊃) consomme le choix-τ (cor. 2, prop. 5)
    et est HORS cible.  Clos (0 hyp).  GL, GRin_f, GR : familles externes définies par
    `theorie_distrib` (axiomes C54)."""
    vxx, vj, vL = _t(xx), _t(j), _t(L)
    vgl, vgrin, vgr, vff = _t(gl), _t(grin), _t(gr), _t(ff)
    vx = var("z")                       # élément courant (= liant de inclus)
    vI = E.produit_famille(vj, vL)      # I = ∏_{λ∈L} J_λ

    th = theorie_distrib(vxx, vj, vL, vgl, vgrin, vgr, vff)
    ax_gl = N.axiome(th, _ax_gl(vxx, vj, vL, vgl))      # (∀λ) GL(λ) = ⋂_{ι∈J_λ}X_{λ,ι}
    ax_rin = N.axiome(th, _ax_rin(vxx, vgrin, vff, vL))  # (∀λ) GRin(λ) = X_{λ,f(λ)}
    ax_gr = N.axiome(th, _ax_gr(vxx, vgrin, vgr, vff, vL))  # GR(f) = ⋃_λ X_{λ,f(λ)}

    gauche = _membre_gauche(vxx, vj, vL, vgl)
    droite = _membre_droit(vgr, vj, vL)

    # ── (1) décomposer x ∈ ⋃GL  →  (∃λ)(λ∈L et x ∈ GL(λ)) ────────────────────
    h = N.assume(appartient(vx, gauche))
    eq_reun = membre_reunion_famille(vgl.nom, vL.nom, "z")     # (x∈⋃GL) ⇔ (∃i)(i∈L et x∈GL(i))
    ex_i = N.modus_ponens(h, equivalence_avant(eq_reun))       # (∃i)(i∈L et x∈GL(i))
    # α-renommer le témoin i → lam pour travailler avec un nom propre
    corps_i = et(appartient(var("i"), vL), appartient(vx, E.valeur_famille(vgl, var("i"))))
    ex_lam = N.modus_ponens(ex_i, equivalence_avant(alpha_existe("i", "lam", corps_i)))
    vlam = var("lam")

    # ── corps sous le témoin λ₀ = lam :  (λ₀∈L et x∈GL(λ₀)) ⊢ x ∈ ⋂GR ─────────
    corps_lam = et(appartient(vlam, vL), appartient(vx, E.valeur_famille(vgl, vlam)))
    hLam = N.assume(corps_lam)
    lam_in_L = _proj_et_gauche(hLam, corps_lam)               # λ₀ ∈ L
    x_in_GLlam = _proj_et_droite(hLam, corps_lam)             # x ∈ GL(λ₀)
    # GL(λ₀) = ⋂_{ι∈J_λ₀} X_{λ₀,ι}  (axiome GL), réécrire x∈GL(λ₀) → x∈⋂_{ι∈J_λ₀}
    eq_gl_lam = instancie(ax_gl, vlam)                        # GL(λ₀) = ⋂_{ι∈J_λ₀}X_{λ₀,ι}
    inter_lam = E.inter_famille(E.valeur_famille(vxx, vlam), _Jlam(vj, vlam))
    x_in_inter = N.modus_ponens(x_in_GLlam,
                                _reecrit_appartient(vx, E.valeur_famille(vgl, vlam),
                                                    inter_lam, eq_gl_lam))   # x ∈ ⋂_{ι∈J_λ₀}

    # ── but x ∈ ⋂GR  ⇐  (∀f)(f∈I ⇒ x∈⋃_λ X_{λ,f(λ)}) ────────────────────────
    # construire, pour f frais, l'implication (f∈I ⇒ x ∈ GR(f))
    hf = N.assume(appartient(vff, vI))                        # f ∈ I = ∏_{λ∈L}J_λ
    # (4) f(λ₀) ∈ J_λ₀  par projection_dans_facteur + λ₀∈L
    #     famille de facteurs = J (les J_λ), indices = L, élément = f, indice = λ₀
    proj = projection_dans_facteur(vj.nom, vL.nom, vff.nom, vlam.nom)  # (f∈∏_{λ∈L}J_λ)⇒(λ₀∈L⇒ f(λ₀)∈J_λ₀)
    fλ_in_J = N.modus_ponens(lam_in_L, N.modus_ponens(hf, proj))       # f(λ₀) ∈ J_λ₀
    # (5) inter_famille_elim sur la famille ι↦X_{λ₀,ι} (= XX_λ₀) sur J_λ₀
    elim = _inter_elim_terme(E.valeur_famille(vxx, vlam), _Jlam(vj, vlam),
                             E.valeur(vff, vlam), vx)         # (x∈⋂_{ι∈J_λ₀})⇒(f(λ₀)∈J_λ₀⇒x∈X_{λ₀,f(λ₀)})
    x_in_X = N.modus_ponens(fλ_in_J, N.modus_ponens(x_in_inter, elim))  # x ∈ X_{λ₀,f(λ₀)}
    # (6) reunion_famille_intro sur GRin_f (famille λ↦X_{λ,f(λ)}), témoin λ₀
    #     d'abord réécrire x∈X_{λ₀,f(λ₀)} → x∈GRin_f(λ₀)  via AX_RIN
    eq_rin_lam = instancie(ax_rin, vlam)                      # GRin(λ₀) = X_{λ₀,f(λ₀)}
    x_in_GRin = N.modus_ponens(x_in_X,
                               _reecrit_appartient(vx, _X(vxx, vlam, E.valeur(vff, vlam)),
                                                   E.valeur_famille(vgrin, vlam),
                                                   _sym(eq_rin_lam)))        # x ∈ GRin(λ₀)
    intro = _reunion_intro_terme(vgrin, vL, vlam, vx)         # (λ₀∈L et x∈GRin(λ₀)) ⇒ x∈⋃GRin
    x_in_reunGRin = N.modus_ponens(conjonction_intro(lam_in_L, x_in_GRin), intro)  # x ∈ ⋃_λ GRin(λ)
    # ⋃GRin = GR(f)  (axiome GR), réécrire x∈⋃GRin → x∈GR(f)
    reunGRin = E.reunion_famille(vgrin, vL)
    x_in_GRf = N.modus_ponens(x_in_reunGRin,
                              _reecrit_appartient(vx, reunGRin, E.valeur_famille(vgr, vff),
                                                  _sym(ax_gr)))             # x ∈ GR(f)

    # (7) f∈I ⇒ x∈GR(f) ; généraliser sur f ; passer en ⋂GR
    imp_f = N.loi_deduction(appartient(vff, vI), x_in_GRf)    # {hLam,…} ⊢ (f∈I ⇒ x∈GR(f))
    # liant f → i pour matcher membre_inter_famille (liant interne "i")
    corps_f = impl(appartient(vff, vI), appartient(vx, E.valeur_famille(vgr, vff)))
    forall_f = N.generalisation(vff.nom, imp_f)               # (∀f)(f∈I ⇒ x∈GR(f))
    forall_i = N.modus_ponens(forall_f, equivalence_avant(alpha_pour_tout(vff.nom, "i", corps_f)))
    eq_inter = _membre_inter_terme(vgr, vI, vx)               # (x∈⋂GR) ⇔ (∀i)(i∈I ⇒ x∈GR(i))
    x_in_interGR = N.modus_ponens(forall_i, equivalence_arriere(eq_inter))  # x ∈ ⋂GR  {hLam}

    # ── (8) décharger le témoin, puis l'élément x ───────────────────────────
    imp_lam = N.loi_deduction(corps_lam, x_in_interGR)        # (corps_lam ⇒ x∈⋂GR)
    elim_temoin = existe_elimination(imp_lam, "lam")          # (∃lam)corps_lam ⇒ x∈⋂GR
    x_in_droite = N.modus_ponens(ex_lam, elim_temoin)         # x ∈ ⋂GR  {x∈⋃GL}
    imp_x = N.loi_deduction(appartient(vx, gauche), x_in_droite)   # (x∈⋃GL ⇒ x∈⋂GR)
    incl = N.generalisation("z", imp_x)                       # (∀z)(z∈⋃GL ⇒ z∈⋂GR) = inclus

    assert incl.conclusion == _cible(xx, j, L, gl, gr), \
        "distributivite_reunion_inter_inclusion_directe : conclusion ≠ cible"
    return incl


# ── micro-helpers (instances à termes, réécriture d'appartenance) ─────────────
def _proj_et_gauche(h_et, formule_et):
    """De Γ⊢(A et B) déduire Γ⊢A."""
    from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import conjonction_elim_gauche
    return conjonction_elim_gauche(h_et)


def _proj_et_droite(h_et, formule_et):
    """De Γ⊢(A et B) déduire Γ⊢B."""
    from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import conjonction_elim_droite
    return conjonction_elim_droite(h_et)


def _sym(thm_eq):
    """De ⊢ a = b déduire ⊢ b = a."""
    from bourbaki.logique.i_4_egalitaires.tactiques_abrege_egalite import symetrie
    a, b = thm_eq.conclusion.termes
    return N.modus_ponens(thm_eq, symetrie(a, b))


def _reecrit_appartient(t, a, b, thm_eq_ab):
    """De ⊢ a = b déduire ⊢ (t∈a) ⇒ (t∈b)  (réécriture de l'appartenance par S6)."""
    R = appartient(t, var("@rw"))
    equ = N.modus_ponens(thm_eq_ab, N.s6(a, b, "@rw", R))     # (t∈a) ⇔ (t∈b)
    return equivalence_avant(equ)


def _inter_elim_terme(fam, idx, a, z):
    """⊢ (z ∈ ⋂_{ι∈idx} fam_ι) ⇒ (a∈idx ⇒ z∈fam_a)  (inter_famille_elim à TERMES).

    Instance directe de l'axiome ⋂ + instanciation au témoin a, sans passer par les
    paramètres-lettres de `inter_famille_elim` (fam, idx, a, z sont des termes)."""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_INTER_FAM)
    inst = instancie(instancie(instancie(ax, fam), idx), z)  # (z∈⋂)⇔(∀i)(i∈idx⇒z∈fam_i)
    h = N.assume(appartient(z, E.inter_famille(fam, idx)))
    forall = N.modus_ponens(h, equivalence_avant(inst))      # (∀i)(i∈idx⇒z∈fam_i)
    at_a = instancie(forall, a)                              # (a∈idx ⇒ z∈fam_a)
    return N.loi_deduction(appartient(z, E.inter_famille(fam, idx)), at_a)


def _reunion_intro_terme(fam, idx, a, z):
    """⊢ ((a∈idx) et (z∈fam_a)) ⇒ (z ∈ ⋃_{ι∈idx} fam_ι)  (reunion_famille_intro à TERMES)."""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_REUNION_FAM)
    inst = instancie(instancie(instancie(ax, fam), idx), z)  # (z∈⋃)⇔(∃i)(i∈idx et z∈fam_i)
    body = et(appartient(a, idx), appartient(z, E.valeur_famille(fam, a)))
    h = N.assume(body)
    inner = et(appartient(var("i"), idx), appartient(z, E.valeur_famille(fam, var("i"))))
    ex = N.modus_ponens(h, N.s5(inner, a, "i"))              # (∃i)(i∈idx et z∈fam_i)
    zU = N.modus_ponens(ex, equivalence_arriere(inst))
    return N.loi_deduction(body, zU)


def _membre_inter_terme(fam, idx, z):
    """⊢ (z ∈ ⋂_{ι∈idx} fam_ι) ⇔ (∀i)(i∈idx ⇒ z∈fam_i)  (instance à TERMES)."""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_INTER_FAM)
    return instancie(instancie(instancie(ax, fam), idx), z)


__all__ = ["distributivite_reunion_inter_inclusion_directe", "_cible",
           "theorie_distrib"]
