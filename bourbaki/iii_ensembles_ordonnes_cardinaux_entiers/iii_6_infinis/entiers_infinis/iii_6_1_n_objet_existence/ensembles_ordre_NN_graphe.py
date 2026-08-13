"""§III.6.1 — LE GRAPHE DE L'ORDRE DE ℕ :  G_≤  et  ⊢ est_bien_ordonne(R_G≤, ℕ).

La chaîne C60/C62 parle en ordre-GRAPHE (R = _graphe_R(G) : (a,b)∈G) ; le bon ordre
de ℕ déposé (`n_bien_ordonne`, CLOS) parle en relation-CALLABLE (`ordre_induit_NN`).
Ce module fait la JONCTION :

  • `G_ordre_NN()` — le terme-graphe de ≤ sur ℕ, caractérisé par S8 (pleine forme) :
        (∀z)( z∈G_≤ ⇔ (∃a)(∃b)( z=(a,b) ∧ ordre_induit_NN(a,b) ) )
    (sélection dans l'EXISTANT ℕ×ℕ — ordre_induit_NN contient a∈ℕ ∧ b∈ℕ ;
     théorie DÉDIÉE, motif Dtot/AXIOME_RESTRICTION ; theorie_ensembles()==22).
  • `couple_dans_G_ordre(a,b)`  ⊢ ((a,b)∈G_≤) ⇔ ordre_induit_NN(a,b)   [CLOS]
  • 🎯 `bo_graphe_NN()`         ⊢ est_bien_ordonne(R_G≤, ℕ)             [CLOS]
      — TRANSPORT de n_bien_ordonne par CONGRUENCE-PAR-FEUILLES : les deux formes
        de est_bien_ordonne ne diffèrent qu'aux feuilles R{s,t} ; on remonte le
        ⇔ feuille (couple_dans_G_ordre) à travers ¬/∨/∃ (motif bridge_equiv).
  • 🎯🎯 `c62_recursion_sur_NN` / `fonction_recursion_NN` — C62 et l'assemblage
        complet sur (ℕ, G_≤) avec le bon ordre DÉCHARGÉ :
        **DEUX résidus seulement : { essais_bien_formes(T), rule_codomain(T,V) }**
        — les données de la règle.  Le « ℕ est bien ordonné » du livre est un
        THÉORÈME (E III.46 : « L'ensemble ℕ étant bien ordonné… »).
  • 🎯🎯🎯 `existence_unicite_fonction_NN` — LE CAPSTONE : le **(∃!f)** de C62 sur le
        VRAI ℕ, MÊMES deux résidus.  C'est la phrase finale de C62 (« L'ensemble U et
        l'application f sont alors déterminés de façon unique par cette condition »).
        Niveau VALEUR-RÈGLE `f(z)=T(z)` — l'unicité au niveau LIVRE `f(z)=T{f|seg z}`
        exigera une récurrence transfinie (résidu déclaré, cf. `c62_fonction_unicite`).

INVARIANT : theorie_ensembles() = 22.  Rien postulé.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, app, egal, et, impl, equiv, non, ou, appartient, existe, pourtout,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E

from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege import a_implique_a
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, equivalence_transitivite,
    equiv_neg, ou_congruence, instancie,
)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import (
    existe_elimination, congruence_existe,
)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.outil_alpha_bridge import bridge_equiv
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import symetrie
from bourbaki.ii_theorie_des_ensembles.ii_2_couples.ii_2_1_definition_couples.ensembles_couples import couple_egal_implique_composantes

from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_recurrence_transfinie import _graphe_R
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_1_n_objet_existence.ensembles_ensemble_NN import ensemble_NN
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_1_n_objet_existence.ensembles_n_bien_ordonne import (
    ordre_induit_NN, n_bien_ordonne,
)


def _t(t):
    """Coercion str/Terme → Terme."""
    return t if isinstance(t, Terme) else var(t)


# ════════════════════════════════════════════════════════════════════════════
#  LE GRAPHE G_≤ — sélection S8 dans ℕ×ℕ, théorie dédiée (motif Dtot).
# ════════════════════════════════════════════════════════════════════════════
def G_ordre_NN():
    """G_≤ := { (a,b) ∈ ℕ×ℕ | a ≤ b }   (terme opaque ; caractérisé par l'axiome)."""
    return app("G_ordre_NN")


def _corps_G_ordre(z, a="aog", b="bog"):
    """Corps :  (∃a)(∃b)( z=(a,b) ∧ ordre_induit_NN(a,b) )."""
    va, vb = var(a), var(b)
    return existe(a, existe(b, et(egal(_t(z), E.couple(va, vb)),
                                  ordre_induit_NN(va, vb))))


def axiome_G_ordre_NN(z="zog", a="aog", b="bog"):
    """⊢-schéma  (∀z)( z∈G_≤ ⇔ (∃a)(∃b)( z=(a,b) ∧ ordre_induit_NN(a,b) ) ).

    Sélection S8 dans l'EXISTANT ℕ×ℕ (le sélecteur contient a∈ℕ ∧ b∈ℕ via
    ordre_induit_NN), unicité A1 — motif AXIOME_RESTRICTION / Dtot."""
    vz = var(z)
    return pourtout(z, equiv(appartient(vz, G_ordre_NN()), _corps_G_ordre(vz, a, b)))


def theorie_G_ordre_NN(z="zog", a="aog", b="bog"):
    """Théorie DÉDIÉE ne contenant que l'axiome de G_≤."""
    return N.Theorie("G-ordre-NN", [axiome_G_ordre_NN(z, a, b)])


def _inst_G_ordre(z):
    """⊢ ( z∈G_≤ ⇔ (∃a)(∃b)( z=(a,b) ∧ ordre_induit_NN(a,b) ) )   (instancié)."""
    ax = N.axiome(theorie_G_ordre_NN(), axiome_G_ordre_NN())
    return instancie(ax, _t(z))


# ════════════════════════════════════════════════════════════════════════════
#  ⊢ ((s,t)∈G_≤) ⇔ ordre_induit_NN(s,t)   [CLOS] — la forme couple de l'axiome.
# ════════════════════════════════════════════════════════════════════════════
def couple_dans_G_ordre(s, t):
    """⊢ ((s,t) ∈ G_≤) ⇔ ordre_induit_NN(s, t)   (s, t : Termes).      [CLOS].

    Construit sur les NOMS EXOTIQUES s0g/t0g puis ∀-clos et INSTANCIÉ à (s,t) —
    blindage anti-collision : s,t sont souvent les liants d'épine (a, w, xo…) de
    est_bien_ordonne, qui heurtent les trous/liants internes des briques (motif
    _inst_gen).  Un α-renommage résiduel côté ordre_induit est absorbé en aval
    (bridge_equiv au niveau feuille du marcheur)."""
    core = _couple_dans_G_ordre_noms()
    g = N.generalisation("s0g", N.generalisation("t0g", core))
    return instancie(instancie(g, _t(s)), _t(t))


def _couple_dans_G_ordre_noms():
    """⊢ ((s0g,t0g) ∈ G_≤) ⇔ ordre_induit_NN(s0g, t0g)   [CLOS, noms exotiques]."""
    s, t = var("s0g"), var("t0g")
    cst = E.couple(s, t)
    inst = _inst_G_ordre(cst)                    # (s,t)∈G ⇔ (∃a)(∃b)corps
    va, vb = var("aog"), var("bog")
    corps_ab = et(egal(cst, E.couple(va, vb)), ordre_induit_NN(va, vb))

    # ── ⇐ : ordre_induit_NN(s,t) ⇒ (s,t)∈G ─────────────────────────────────────
    h_ord = N.assume(ordre_induit_NN(s, t))
    wit = conjonction_intro(N.reflexivite(cst), h_ord)           # (s,t)=(s,t) ∧ ord(s,t)
    corps_sb = et(egal(cst, E.couple(s, vb)), ordre_induit_NN(s, vb))
    ex_b = N.modus_ponens(wit, N.s5(corps_sb, t, "bog"))
    ex_ab = N.modus_ponens(ex_b, N.s5(existe("bog", corps_ab), s, "aog"))
    dans_G = N.modus_ponens(ex_ab, equivalence_arriere(inst))    # (s,t)∈G
    arriere = N.loi_deduction(ordre_induit_NN(s, t), dans_G)

    # ── ⇒ : (s,t)∈G ⇒ ordre_induit_NN(s,t) ────────────────────────────────────
    h_in = N.assume(appartient(cst, G_ordre_NN()))
    dec = N.modus_ponens(h_in, equivalence_avant(inst))          # (∃a)(∃b)corps
    h_c = N.assume(corps_ab)
    eq_cpl = conjonction_elim_gauche(h_c)                        # (s,t)=(a,b)
    ord_ab = conjonction_elim_droite(h_c)                        # ord(a,b)
    # ⚠️ collision de NOM d'argument : s,t peuvent être les liants d'épine (a, w…) qui
    # heurtent les trous internes de la brique — _wrap4 : noms exotiques puis instancie.
    cec = couple_egal_implique_composantes("s0g", "t0g", "aog", "bog")
    for nom in ("bog", "aog", "t0g", "s0g"):
        cec = N.generalisation(nom, cec)
    for tm in (s, t, va, vb):
        cec = instancie(cec, tm)
    comps = N.modus_ponens(eq_cpl, cec)
    s_a = conjonction_elim_gauche(comps)                         # s=a
    t_b = conjonction_elim_droite(comps)                         # t=b
    a_s = N.modus_ponens(s_a, symetrie(s, va))                   # a=s
    b_t = N.modus_ponens(t_b, symetrie(t, vb))                   # b=t
    eq1 = N.modus_ponens(a_s, N.s6(va, s, "wog1", ordre_induit_NN(var("wog1"), vb)))
    ord_sb = N.modus_ponens(ord_ab, equivalence_avant(eq1))      # ord(s,b)
    eq2 = N.modus_ponens(b_t, N.s6(vb, t, "wog2", ordre_induit_NN(s, var("wog2"))))
    ord_st = N.modus_ponens(ord_sb, equivalence_avant(eq2))      # ord(s,t)
    imp_b = existe_elimination(N.loi_deduction(corps_ab, ord_st), "bog")
    imp_ab = existe_elimination(imp_b, "aog")
    avant = N.loi_deduction(appartient(cst, G_ordre_NN()),
                            N.modus_ponens(dec, imp_ab))

    res = conjonction_intro(avant, arriere)
    assert res.est_clos, "couple_dans_G_ordre : non clos"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  🎯 TRANSPORT — congruence PAR FEUILLES (motif bridge_equiv, feuilles ⇔ S8).
# ════════════════════════════════════════════════════════════════════════════
def _equiv_feuilles(f1, f2):
    """⊢ f1 ⇔ f2 quand f1,f2 ne diffèrent qu'aux FEUILLES (s,t)∈G_≤ vs ordre_induit.

    Récursion structurelle : identiques ⇒ réflexivité ; ¬/∨ ⇒ equiv_neg/ou_congruence ;
    ∃ même liant ⇒ congruence_existe ; sinon FEUILLE : f1=((s,t)∈G_≤) — l'axiome S8
    couple donne le ⇔ ; si son membre droit α-diverge de f2 (τ internes du ≤
    canonicalisés dans n_bien_ordonne), bridge_equiv recolle."""
    if f1 == f2:
        aa = a_implique_a(f1)
        return conjonction_intro(aa, aa)
    if f1.tag == "non" and f2.tag == "non":
        return equiv_neg(_equiv_feuilles(f1.sous[0], f2.sous[0]))
    if f1.tag == "ou" and f2.tag == "ou":
        return ou_congruence(_equiv_feuilles(f1.sous[0], f2.sous[0]),
                             _equiv_feuilles(f1.sous[1], f2.sous[1]))
    if f1.tag == "exists" and f2.tag == "exists" and f1.lieur == f2.lieur:
        return congruence_existe(_equiv_feuilles(f1.sous[0], f2.sous[0]), f1.lieur)
    # FEUILLE : f1 = ((s,t) ∈ G_≤)  (appartenance d'un couple au graphe)
    assert f1.tag == "in" and f1.termes[1] == G_ordre_NN(), \
        f"_equiv_feuilles : feuille inattendue ({f1.tag} vs {f2.tag})"
    cpl = f1.termes[0]                            # paire(paire(s,s), paire(s,t))
    s = cpl.args[0].args[0]
    t = cpl.args[1].args[1]
    lemme = couple_dans_G_ordre(s, t)             # (s,t)∈G ⇔ ord'(s,t) [instancié]
    rhs = equivalence_avant(lemme).conclusion.sous[1]      # le VRAI membre droit
    if rhs != f2:                                 # α-divergence interne du ≤
        lemme = equivalence_transitivite(lemme, bridge_equiv(rhs, f2))
    return lemme


# @livre Ch.III §6.2 Crit.C62 | E III.46 L.15-16 | PDF p.149  (« L'ensemble ℕ étant bien ordonné, on peut lui appliquer le critère C60 » — LE bon ordre de ℕ, forme graphe)
#   ⚠️ CE MARQUEUR A DIT « L.14-15 » alors que `ensembles_n_bien_ordonne.py:418` citait LA MÊME
#   phrase en « L.15-16 » : deux marqueurs en conflit sur un même texte. Recompté sur le PNG
#   (p.149, en-tête « E III.46 ») le 27 juil. 2026 : L.14 est le titre « 2. Définition
#   d'applications par récurrence », la phrase est bien en L.15-16. Les deux concordent désormais.
def bo_graphe_NN():
    """🎯 ⊢ est_bien_ordonne( R_G≤, ℕ ),   R_G≤ = (a,b)↦((a,b)∈G_≤)      [CLOS].

    Transport de `n_bien_ordonne` (forme callable, CLOS) vers la forme GRAPHE que
    la chaîne C60/C62 consomme — congruence par feuilles + MP."""
    from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.outil_alpha_bridge import alpha_bridge
    thm = n_bien_ordonne()                        # ⊢ est_bien_ordonne(ordre_induit, ℕ)
    f2 = thm.conclusion
    R = _graphe_R(G_ordre_NN())
    NN = ensemble_NN()
    # ÉPINE IDENTIQUE : mêmes binders que n_bien_ordonne ('xo','yo','zo','X','a','w')
    # ⇒ le marcheur ne traverse que des nœuds à liants égaux, SEULES les feuilles
    # R{s,t} diffèrent.  Le retour aux binders PAR DÉFAUT (forme que la chaîne C60/C62
    # construit) est délégué à alpha_bridge sur une paire PUREMENT α-équivalente.
    f1_xo = E.est_bien_ordonne(R, NN, "xo", "yo", "zo", "X", "a", "w")
    eq = _equiv_feuilles(f1_xo, f2)               # f1_xo ⇔ f2
    thm_xo = N.modus_ponens(thm, equivalence_arriere(eq))        # ⊢ f1_xo
    cible = E.est_bien_ordonne(R, NN)             # binders par défaut (forme chaîne)
    res = thm_xo if thm_xo.conclusion == cible else alpha_bridge(thm_xo, cible)

    assert res.conclusion == cible, "bo_graphe_NN : ≠ est_bien_ordonne(R_G≤, ℕ)"
    assert res.est_clos, "bo_graphe_NN : non clos"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  🎯🎯 C62 SUR (ℕ, G_≤) — le bon ordre DÉCHARGÉ : 2 résidus (données de règle).
# ════════════════════════════════════════════════════════════════════════════
def _cut(thm, P, pr):
    """Décharge l'hypothèse P de thm par sa preuve pr."""
    return N.modus_ponens(pr, N.loi_deduction(P, thm))


def c62_recursion_sur_NN(vh, V="Uval"):
    """🎯🎯 { essais_bien_formes(T), rule_codomain(T,V) } ⊢
          (∀n)( n∈ℕ ⇒ (∃p) est_essai(p, T, ≤_G, ℕ, n) )   — C62 SUR LE VRAI ℕ.

    Le résidu « ℕ bien ordonné » est DÉCHARGÉ par `bo_graphe_NN` (CLOS)."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_2_recursion_c62.ensembles_c62_recursion import c62_recursion_sur_N
    NN = ensemble_NN()
    Gle = G_ordre_NN()
    base = c62_recursion_sur_N(vh, NN, Gle, V)
    bo = E.est_bien_ordonne(_graphe_R(Gle), NN)
    res = _cut(base, bo, bo_graphe_NN())
    assert len(res.hypotheses) == 2, "c62_recursion_sur_NN : hyps ≠ 2"
    assert res.conclusion not in res.hypotheses, "c62_recursion_sur_NN : VACUOUS"
    return res


def fonction_recursion_NN(vh, V="Uval", fb="fglb", zn="zfgl"):
    """🎯🎯 { essais_bien_formes(T), rule_codomain(T,V) } ⊢
          (∃f)( est_fonctionnel(f) ∧ dom(f)=ℕ ∧ (∀z)(z∈ℕ ⇒ valeur(f,z)=T(z)) ).

    L'EXISTENCE C62 assemblée SUR LE VRAI ℕ, bon ordre déchargé — il ne reste que
    les DONNÉES DE LA RÈGLE.  (« Il existe une application f de ℕ… », E III.46.)"""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_2_recursion_c62.ensembles_c62_fonction_existence import fonction_recursion_c62
    NN = ensemble_NN()
    Gle = G_ordre_NN()
    base = fonction_recursion_c62(vh, NN, Gle, V, fb, zn)
    bo = E.est_bien_ordonne(_graphe_R(Gle), NN)
    res = _cut(base, bo, bo_graphe_NN())
    assert len(res.hypotheses) == 2, "fonction_recursion_NN : hyps ≠ 2"
    assert res.conclusion not in res.hypotheses, "fonction_recursion_NN : VACUOUS"
    return res


# @livre Ch.III §6.2 Crit.C62 | E III.46 L.14-20 | PDF p.149
def existence_unicite_fonction_NN(vh, V="Uval", fb="fglb", gb="gcand", zn="zfgl"):
    """🎯🎯🎯 { essais_bien_formes(T), rule_codomain(T,V) } ⊢
          (∃f)( P(f) ∧ (∀g)( P(g) ⇒ g = f ) )     — LE (∃!f) DE C62 SUR LE VRAI ℕ,
      P(t) = est_fonctionnel(t) ∧ est_un_graphe(t) ∧ dom(t)=ℕ ∧ (∀z)(z∈ℕ ⇒ t(z)=T(z)).

    LE CAPSTONE de C62 : existence ET unicité, sur ℕ = `ensemble_NN()` (le TERME CLOS,
    pas la variable `Enat`), bon ordre DÉCHARGÉ par `bo_graphe_NN` (CLOS, 0 hyp).  Il
    ne reste que les DEUX données de la règle — exactement les résidus de
    `fonction_recursion_NN`, dont ceci est la version AVEC unicité.

    C'est la dernière phrase de C62 chez Bourbaki : « L'ensemble U et l'application f
    sont alors DÉTERMINÉS DE FAÇON UNIQUE par cette condition » (E III.46) — et la
    décharge du bon ordre est LITTÉRALEMENT la première : « L'ensemble ℕ étant bien
    ordonné, on peut lui appliquer le critère C60 ».  Chez nous ce n'est pas une
    prémisse mais un THÉORÈME.

    GESTE : rigoureusement celui de `fonction_recursion_NN` — instancier au terme clos
    puis `_cut` par le bon ordre.  Les DEUX moitiés étaient au dépôt (le (∃!f) sur la
    variable d'un côté, `bo_graphe_NN` de l'autre) ; SEULE LA JOINTURE manquait.  Le
    résidu « instancier C60-final au terme lourd ensemble_NN() heurte un binder interne
    du gluing » (`ensembles_c62_recursion` L.60-65) est PÉRIMÉ depuis le fix `subst` du
    24 juil. 2026 : MESURÉ, l'instanciation passe (58 s, 3 hyps, puis 2 après décharge).

    RÉSIDU HONNÊTE conservé : ce (∃!f) est au niveau VALEUR-RÈGLE `f(z)=T(z)`.  Au
    niveau LIVRE `f(z)=T{f|seg z}` l'unicité n'est PAS assemblable ainsi (l'argument de
    T diffère entre g et f) — il y faudra une récurrence transfinie sur la coïncidence
    `g|seg x = f|seg x`.  Cf. `ensembles_c62_fonction_unicite`."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_2_recursion_c62.ensembles_c62_fonction_unicite import (
        existence_unicite_fonction_c62,
    )
    NN = ensemble_NN()
    Gle = G_ordre_NN()
    base = existence_unicite_fonction_c62(vh, NN, Gle, V, fb, gb, zn)
    bo = E.est_bien_ordonne(_graphe_R(Gle), NN)
    res = _cut(base, bo, bo_graphe_NN())
    assert len(res.hypotheses) == 2, "existence_unicite_fonction_NN : hyps ≠ 2"
    assert res.conclusion.tag == "exists", "existence_unicite_fonction_NN : pas un ∃"
    assert res.conclusion not in res.hypotheses, "existence_unicite_fonction_NN : VACUOUS"
    return res


__all__ = [
    "G_ordre_NN", "axiome_G_ordre_NN", "theorie_G_ordre_NN", "couple_dans_G_ordre",
    "bo_graphe_NN", "c62_recursion_sur_NN", "fonction_recursion_NN",
    "existence_unicite_fonction_NN",
]
