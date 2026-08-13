"""§III.6.3 Cor.1 Th.2 (n°111) — a^n = a pour a infini, n ≥ 1.

Bourbaki (E III.49 L.5-6, Cor.1 du Th.2) : si a est un cardinal infini et n un
entier ≥ 1, alors aⁿ = a.

ASSEMBLAGE (multi-tick, bricks TOUS clos) — récurrence sur n depuis 1 :
  · base a¹ = a                    [exposant_un_egale] ;
  · pas aⁿ⁺¹ = a sous a²=a (Th.2/Hessenberg) et l'HR aⁿ=a, par double inégalité
    Cantor-Bernstein :
      – borne INF  aⁿ ≤ aⁿ⁺¹  [support_extension_domaine : 𝓕(n;A) ≤ 𝓕(n⊔{∅};A)] ;
      – borne SUP  aⁿ⁺¹ ≤ a  [B_preuve : aⁿ⁺¹=Card(𝓕(n⊔{∅};A)) ; inf_egal_phi :
        𝓕(n⊔{∅};A) ≤ 𝓕(n;A)×𝓕({∅};A) = aⁿ·a¹ = a·a = a² = a].

Comme A⊔B = (A×{0})∪(B×{1}) (copies MARQUÉES), le « n⊆successeur(n) » du plan se
déploie en ponts : n ≅ n×{0} (équipotence), n×{0} ⊆ n⊔{∅} (inclusion gauche),
invariance de 𝓕 par équipotence [eq_exposant_invariant].  On pose ces ponts UN PAR UN.

PONT 1 (ce commit) : copie_gauche_inclus_somme — ⊢ (n×{0}) ⊆ (n ⊔ {∅}).
theorie_ensembles() inchangée (22 axiomes).
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, inclus, appartient, Terme
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import instancie
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_theoremes import inclusion_reunion_gauche
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_recollement_somme.ensembles_somme_disjointe import somme_disjointe, ZERO, UN
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_2_monotonie.ensembles_exposant_monotone_exp_incond import support_extension_domaine
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_4_prop8_successeur.ensembles_copie_marquee import eq_copie_gauche
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.somme_produit_bornes.ensembles_eq_exposant_invariant import eq_exposant_invariant
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.ordre_cardinaux.ensembles_cardinaux_ordre import equipotence_implique_inf_egal
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.ordre_cardinaux.ensembles_cardinaux_props_restantes_ordre import inf_egal_transitive_general
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import conjonction_intro, conjonction_elim_droite
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_5_exposant.prop9_exp_somme.ensembles_prop9_close import inf_egal_phi
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_produit.ensembles_produit_equipotence import eq_produit_invariant
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_5_exposant.definition.exposant_un._bijection import eq_applications_A
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import equipotent
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.equipotence.ensembles_bijection import equipotence_symetrique
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.cantor_bernstein.cloture import cantor_bernstein
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux_theoremes import cardinal_egal_si_equipotent, equipotent_si_cardinal_egal
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.entiers_cardinaux.ensembles_puissance_entiers_inconditionnel import B_preuve
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import successeur
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import composer_egalites
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import et, impl, pourtout
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import UN as UN_CARD, est_fini
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import inf_egal_card
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_fini_un import eq_un_singleton, un_est_un_cardinal
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import est_cardinal
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_recurrence_c61_existence_n.ensembles_recurrence_variantes import hypothese_recurrence_depuis, conclusion_recurrence_depuis
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_recurrence_c61_existence_n.ensembles_recurrence_depuis_preuve import recurrence_depuis


def _R111(m, a="A"):
    """R{m} := Eq(𝓕(m;A), A)  (= aᵐ = a, relation de récurrence de n°111)."""
    return equipotent(E.applications(_t(m), _t(a)), _t(a))


def _cut(thm, preuve_hyp):
    """Décharge de `thm` l'hypothèse H = preuve_hyp.conclusion (coupure)."""
    H = preuve_hyp.conclusion
    return N.modus_ponens(preuve_hyp, N.loi_deduction(H, thm))


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# La somme disjointe utilise les MARQUEURS ensemblistes ZERO=∅, UN={∅} (pas les
# cardinaux) ; le « 1 » du successeur est le terme {∅} = singleton(∅).
_UNITE = E.singleton(E.VIDE)   # {∅}  = second argument de la somme disjointe (successeur)


def _copie_gauche(n):
    """n × {∅}  (copie marquée gauche de n dans n⊔{∅})."""
    return E.produit(_t(n), E.singleton(ZERO))


def _copie_droite():
    """{∅} × {{∅}}  (copie marquée droite dans n⊔{∅})."""
    return E.produit(_UNITE, E.singleton(UN))


def enonce_copie_gauche_inclus_somme(n="n"):
    vn = _t(n)
    return inclus(_copie_gauche(vn), somme_disjointe(vn, _UNITE))


# @livre Ch.III §6.3 Demo.- | E III.49 L.5-6 | PDF p.152  (pont : copie gauche ⊆ somme disjointe)
def copie_gauche_inclus_somme(n="n"):
    """⊢ (n × {0}) ⊆ (n ⊔ {∅}).   (inclusion gauche de la réunion A⊔B=(A×{0})∪(B×{1}).)"""
    vn = _t(n)
    base = inclusion_reunion_gauche("a", "b")                     # a ⊆ a∪b
    g = N.generalisation("a", N.generalisation("b", base))
    res = instancie(instancie(g, _copie_gauche(vn)), _copie_droite())
    assert res.conclusion == enonce_copie_gauche_inclus_somme(n), \
        "copie_gauche_inclus_somme : conclusion ≠ énoncé attendu"
    return res


# @livre Ch.III §6.3 Demo.- | E III.49 L.5-6 | PDF p.152  (pont : 𝓕(n×{∅};A) ≤ 𝓕(n⊔{∅};A))
def support_copie_gauche(n="n", a0="a0", a="A"):
    """⊢ {a₀∈A}  inf_egal_card(𝓕(n×{∅};A), 𝓕(n⊔{∅};A)).

    support_extension_domaine(S=n×{∅}, D=n⊔{∅}, a₀, A) sous {S⊆D, a₀∈A} ; l'inclusion
    S⊆D est déchargée par le pont 1 (copie_gauche_inclus_somme, clos)."""
    vn, va0, va = _t(n), _t(a0), _t(a)
    S = _copie_gauche(vn)
    D = somme_disjointe(vn, _UNITE)
    sup = support_extension_domaine(S, D, va0, va)          # {S⊆D, a₀∈A} ⊢ 𝓕(S;A)≤𝓕(D;A)
    return _cut(sup, copie_gauche_inclus_somme(n))          # {a₀∈A} ⊢ 𝓕(S;A)≤𝓕(D;A)


# @livre Ch.III §6.3 Demo.- | E III.49 L.5-6 | PDF p.152  (pont : Eq(𝓕(n;A), 𝓕(n×{∅};A)))
def eq_exposant_copie_gauche(n="n", a="A"):
    """⊢ Eq(𝓕(n;A), 𝓕(n×{∅};A)).   (invariance de 𝓕 par l'équipotence n ≅ n×{∅}.)

    eq_copie_gauche(n) : Eq(n, n×{∅}) ; eq_exposant_invariant(n, n×{∅}, A) :
    Eq(n,n×{∅}) ⇒ Eq(𝓕(n;A), 𝓕(n×{∅};A))."""
    vn = _t(n)
    eq_nm = eq_copie_gauche(n)                               # Eq(n, n×{∅})   [clos]
    # eq_exposant_invariant casse sur des termes complexes en X,Y → NOMS puis generalize+instancie
    base = eq_exposant_invariant("X", "Y", a)                # Eq(X,Y) ⇒ Eq(𝓕(X;A),𝓕(Y;A))  [schéma clos]
    g = N.generalisation("X", N.generalisation("Y", base))
    inv = instancie(instancie(g, vn), _copie_gauche(vn))     # Eq(n,n×{∅}) ⇒ Eq(𝓕(n;A),𝓕(n×{∅};A))
    return N.modus_ponens(eq_nm, inv)


def _F(s, a):
    """𝓕(S;A) = applications de S dans A."""
    return E.applications(s, a)


def _eq_implique_inf(t1, t2):
    """De ⊢ Eq(t1,t2), déduire ⊢ (t1 ≤ t2)  (equipotence_implique_inf_egal en termes)."""
    # equipotence_implique_inf_egal casse parfois sur termes → NOMS puis generalize+instancie
    base = equipotence_implique_inf_egal("F", "X", "Y")          # Eq(X,Y) ⇒ X≤Y
    g = N.generalisation("X", N.generalisation("Y", base))
    return instancie(instancie(g, t1), t2)                       # Eq(t1,t2) ⇒ t1≤t2


# @livre Ch.III §6.3 Demo.- | E III.49 L.5-6 | PDF p.152  (borne INF au niveau 𝓕 : 𝓕(n;A) ≤ 𝓕(n⊔{∅};A))
def inf_Fn_Fsucc(n="n", a0="a0", a="A"):
    """⊢ {a₀∈A}  inf_egal_card(𝓕(n;A), 𝓕(n⊔{∅};A)).

    Eq(𝓕(n;A),𝓕(n×{∅};A)) [pont 3] ⇒ 𝓕(n;A)≤𝓕(n×{∅};A) ; transitivité avec
    𝓕(n×{∅};A)≤𝓕(n⊔{∅};A) [pont 2, sous a₀∈A]."""
    vn, va = _t(n), _t(a)
    T1 = _F(vn, va)                         # 𝓕(n;A)
    T2 = _F(_copie_gauche(vn), va)          # 𝓕(n×{∅};A)
    T3 = _F(somme_disjointe(vn, _UNITE), va)  # 𝓕(n⊔{∅};A)
    le12 = N.modus_ponens(eq_exposant_copie_gauche(n, a), _eq_implique_inf(T1, T2))  # T1≤T2
    le23 = support_copie_gauche(n, a0, a)                                            # {a₀∈A} T2≤T3
    trans = inf_egal_transitive_general()                     # (∀X∀Y∀Z)((X≤Y et Y≤Z)⇒X≤Z)
    trans_inst = instancie(instancie(instancie(trans, T1), T2), T3)
    return N.modus_ponens(conjonction_intro(le12, le23), trans_inst)                 # {a₀∈A} T1≤T3


# @livre Ch.III §6.3 Demo.- | E III.49 L.5-6 | PDF p.152  (borne SUP au niveau 𝓕 : 𝓕(n⊔{∅};A) ≤ 𝓕(n;A)×𝓕({∅};A))
def sup_Fsucc_produit(n="n", a="A"):
    """⊢ inf_egal_card(𝓕(n⊔{∅};A), 𝓕(n;A)×𝓕({∅};A)).   (Direction A de Prop.9, inf_egal_phi.)"""
    vn, va = _t(n), _t(a)
    return inf_egal_phi(va, vn, _UNITE)             # 𝓕(n⊔{∅};A) ≤ 𝓕(n;A)×𝓕({∅};A)  [clos]


def hyp_recurrence(n="n", a="A"):
    """HR := Eq(𝓕(n;A), A)  (= a^n = a, hypothèse de récurrence, niveau équipotence)."""
    return equipotent(_F(_t(n), _t(a)), _t(a))


# @livre Ch.III §6.3 Demo.- | E III.49 L.5-6 | PDF p.152  (SUP : Eq(𝓕(n;A)×𝓕({∅};A), A×A))
def eq_produit_Fn_F1(n="n", a="A"):
    """⊢ {Eq(𝓕(n;A),A)}  Eq(𝓕(n;A)×𝓕({∅};A), A×A).

    eq_produit_invariant (invariance du produit) sous Eq(𝓕(n;A),A) [HR] et
    Eq(𝓕({∅};A),A) [eq_applications_A]."""
    vn, va = _t(n), _t(a)
    T_Fn = _F(vn, va)                                # 𝓕(n;A)
    T_F1 = _F(_UNITE, va)                            # 𝓕({∅};A)
    hHR = N.assume(equipotent(T_Fn, va))             # Eq(𝓕(n;A), A)   [HR]
    eq_F1 = eq_applications_A(a)                      # Eq(𝓕({∅};A), A) [clos]
    # eq_produit_invariant en NOMS puis generalize+instancie (X,Y,X1,Y1)
    base = eq_produit_invariant()                    # défauts F,G,X,Y,X1,Y1 (schéma clos)
    g4 = N.generalisation("X", N.generalisation("Y", N.generalisation("X1", N.generalisation("Y1", base))))
    inst = instancie(instancie(instancie(instancie(g4, T_Fn), T_F1), va), va)
    return N.modus_ponens(conjonction_intro(hHR, eq_F1), inst)   # {HR} Eq(𝓕(n;A)×𝓕({∅};A), A×A)


def hyp_carre(a="A"):
    """a²=a := Eq(A×A, A)  (hypothèse de Hessenberg, déchargée en fin via hessenberg_0hyp)."""
    va = _t(a)
    return equipotent(E.produit(va, va), va)


def _trans3(le_xy, le_yz, tx, ty, tz):
    """De ⊢{..}(tx≤ty) et ⊢{..}(ty≤tz), déduire ⊢{..}(tx≤tz)  (inf_egal_transitive_general)."""
    trans = inf_egal_transitive_general()                        # (∀X∀Y∀Z)((X≤Y et Y≤Z)⇒X≤Z)
    trans_inst = instancie(instancie(instancie(trans, tx), ty), tz)
    return N.modus_ponens(conjonction_intro(le_xy, le_yz), trans_inst)


# @livre Ch.III §6.3 Demo.- | E III.49 L.5-6 | PDF p.152  (BORNE SUP : 𝓕(n⊔{∅};A) ≤ A sous a²=a)
def sup_Fsucc_le_A(n="n", a="A"):
    """⊢ {Eq(𝓕(n;A),A), Eq(A×A,A)}  inf_egal_card(𝓕(n⊔{∅};A), A).

    Chaîne : 𝓕(n⊔{∅};A) ≤ 𝓕(n;A)×𝓕({∅};A) [pont 5] ≤ A×A [pont 7, Eq→≤] ≤ A [a²=a, Eq→≤]."""
    vn, va = _t(n), _t(a)
    T3 = _F(somme_disjointe(vn, _UNITE), va)          # 𝓕(n⊔{∅};A)
    P = E.produit(_F(vn, va), _F(_UNITE, va))         # 𝓕(n;A)×𝓕({∅};A)
    AA = E.produit(va, va)                            # A×A
    le_T3_P = sup_Fsucc_produit(n, a)                 # T3 ≤ P          [clos]
    le_P_AA = N.modus_ponens(eq_produit_Fn_F1(n, a), _eq_implique_inf(P, AA))   # {HR} P ≤ A×A
    le_AA_A = N.modus_ponens(N.assume(hyp_carre(a)), _eq_implique_inf(AA, va))  # {a²=a} A×A ≤ A
    le_T3_AA = _trans3(le_T3_P, le_P_AA, T3, P, AA)   # {HR} T3 ≤ A×A
    return _trans3(le_T3_AA, le_AA_A, T3, AA, va)     # {HR, a²=a} T3 ≤ A


def _eq_sym_impl(t1, t2):
    """⊢ Eq(t1,t2) ⇒ Eq(t2,t1)  (equipotence_symetrique en DÉFAUTS + generalize/instancie)."""
    base = equipotence_symetrique()                  # Eq(X,Y) ⇒ Eq(Y,X)
    g = N.generalisation("X", N.generalisation("Y", base))
    return instancie(instancie(g, t1), t2)


# @livre Ch.III §6.3 Demo.- | E III.49 L.5-6 | PDF p.152  (BORNE INF : A ≤ 𝓕(n⊔{∅};A))
def inf_A_Fsucc(n="n", a0="a0", a="A"):
    """⊢ {Eq(𝓕(n;A),A), a₀∈A}  inf_egal_card(A, 𝓕(n⊔{∅};A)).

    HR Eq(𝓕(n;A),A) → Eq(A,𝓕(n;A)) [sym] → A≤𝓕(n;A) [Eq→≤] ; transitivité avec
    𝓕(n;A)≤𝓕(n⊔{∅};A) [pont 4, sous a₀∈A]."""
    vn, va = _t(n), _t(a)
    T_Fn = _F(vn, va)                                # 𝓕(n;A)
    T3 = _F(somme_disjointe(vn, _UNITE), va)         # 𝓕(n⊔{∅};A)
    hHR = N.assume(equipotent(T_Fn, va))             # Eq(𝓕(n;A), A)  [HR]
    eq_A_Fn = N.modus_ponens(hHR, _eq_sym_impl(T_Fn, va))         # Eq(A, 𝓕(n;A))
    le_A_Fn = N.modus_ponens(eq_A_Fn, _eq_implique_inf(va, T_Fn)) # A ≤ 𝓕(n;A)
    le_Fn_T3 = inf_Fn_Fsucc(n, a0, a)                # {a₀∈A} 𝓕(n;A) ≤ 𝓕(n⊔{∅};A)
    return _trans3(le_A_Fn, le_Fn_T3, va, T_Fn, T3)  # {HR, a₀∈A} A ≤ 𝓕(n⊔{∅};A)


def enonce_eq_Fsucc_A(n="n", a="A"):
    vn, va = _t(n), _t(a)
    return equipotent(_F(somme_disjointe(vn, _UNITE), va), va)


# @livre Ch.III §6.3 Demo.- | E III.49 L.5-6 | PDF p.152  (Cantor-Bernstein : Eq(𝓕(n⊔{∅};A), A))
def eq_Fsucc_A(n="n", a0="a0", a="A"):
    """⊢ {Eq(𝓕(n;A),A), Eq(A×A,A), a₀∈A}  Eq(𝓕(n⊔{∅};A), A).

    Cantor-Bernstein sur les deux bornes : 𝓕(n⊔{∅};A)≤A [SUP] et A≤𝓕(n⊔{∅};A) [INF]
    ⇒ Eq(𝓕(n⊔{∅};A), A)."""
    vn, va = _t(n), _t(a)
    T3 = _F(somme_disjointe(vn, _UNITE), va)          # 𝓕(n⊔{∅};A)
    sup = sup_Fsucc_le_A(n, a)                        # {HR,a²=a} T3 ≤ A
    inf = inf_A_Fsucc(n, a0, a)                       # {HR,a₀∈A} A ≤ T3
    cb_nom = cantor_bernstein("A", "B", "f", "g")     # (A≤B et B≤A) ⇒ Eq(A,B)
    cb = instancie(instancie(N.generalisation("A", N.generalisation("B", cb_nom)), T3), va)  # (T3≤A et A≤T3)⇒Eq(T3,A)
    res = N.modus_ponens(conjonction_intro(sup, inf), cb)         # Eq(T3, A)
    assert res.conclusion == enonce_eq_Fsucc_A(n, a), "eq_Fsucc_A : conclusion ≠ énoncé attendu"
    return res


def _eq_impl_card(t1, t2):
    """⊢ Eq(t1,t2) ⇒ Card t1 = Card t2  (cardinal_egal_si_equipotent, DÉFAUTS+gen/inst)."""
    base = cardinal_egal_si_equipotent("X", "Y")
    return instancie(instancie(N.generalisation("X", N.generalisation("Y", base)), t1), t2)


def _card_impl_eq(t1, t2):
    """⊢ (Card t1 = Card t2) ⇒ Eq(t1,t2)  (equipotent_si_cardinal_egal, DÉFAUTS+gen/inst)."""
    base = equipotent_si_cardinal_egal("X", "Y")
    return instancie(instancie(N.generalisation("X", N.generalisation("Y", base)), t1), t2)


def enonce_eq_R_np1(n="n", a="A"):
    vn, va = _t(n), _t(a)
    return equipotent(_F(successeur(vn), va), va)


# @livre Ch.III §6.3 Demo.- | E III.49 L.5-6 | PDF p.152  (pas de récurrence : R{n+1}=Eq(𝓕(n+1;A),A))
def eq_R_np1(n="n", a0="a0", a="A"):
    """⊢ {Eq(𝓕(n;A),A), Eq(A×A,A), a₀∈A}  Eq(𝓕(succ n;A), A).   (= R{n+1}.)

    B_preuve : Card(𝓕(succ n;A))=Card(𝓕(n⊔{∅};A)) ; pont 11 Eq(𝓕(n⊔{∅};A),A)→Card= ;
    transitivité Card ⇒ Card(𝓕(succ n;A))=Card(A) ⇒ Eq [equipotent_si_cardinal_egal]."""
    vn, va = _t(n), _t(a)
    T3 = _F(somme_disjointe(vn, _UNITE), va)          # 𝓕(n⊔{∅};A)
    T_succ = _F(successeur(vn), va)                   # 𝓕(succ n;A)
    b = B_preuve(a, n)                                # Card(𝓕(succ n;A))=Card(𝓕(n⊔{∅};A))  [clos]
    card_T3_A = N.modus_ponens(eq_Fsucc_A(n, a0, a), _eq_impl_card(T3, va))   # {..} Card(T3)=Card(A)
    card_succ_A = composer_egalites(b, card_T3_A)     # Card(𝓕(succ n;A))=Card(A)
    res = N.modus_ponens(card_succ_A, _card_impl_eq(T_succ, va))   # Eq(𝓕(succ n;A), A)
    assert res.conclusion == enonce_eq_R_np1(n, a), "eq_R_np1 : conclusion ≠ énoncé attendu"
    return res


def enonce_base_111(a="A"):
    return _R111(UN_CARD, a)


# @livre Ch.III §6.3 Demo.- | E III.49 L.5-6 | PDF p.152  (base R{1} = a^1 = a, exposant ENTIER 1)
def base_111(a="A"):
    """⊢ Eq(𝓕(1;A), A).   (base R{1} avec l'exposant ENTIER 1=successeur(0), pas {∅}.)

    eq_un_singleton : Eq(1,{∅}) ; eq_exposant_invariant ⇒ Eq(𝓕(1;A),𝓕({∅};A)) ;
    eq_applications_A : Eq(𝓕({∅};A),A) ; chaînés par Card (transitivité)."""
    va = _t(a)
    FUN = _F(UN_CARD, va)                             # 𝓕(1;A) = applications(1,A)
    F1 = _F(_UNITE, va)                               # 𝓕({∅};A)
    base_inv = eq_exposant_invariant("X", "Y", a)     # Eq(X,Y)⇒Eq(𝓕(X;A),𝓕(Y;A))
    g = N.generalisation("X", N.generalisation("Y", base_inv))
    inv = instancie(instancie(g, UN_CARD), _UNITE)    # Eq(1,{∅})⇒Eq(𝓕(1;A),𝓕({∅};A))
    eq1 = N.modus_ponens(eq_un_singleton(), inv)      # Eq(𝓕(1;A),𝓕({∅};A))
    card1 = N.modus_ponens(eq1, _eq_impl_card(FUN, F1))               # Card(𝓕(1;A))=Card(𝓕({∅};A))
    card2 = N.modus_ponens(eq_applications_A(a), _eq_impl_card(F1, va))  # Card(𝓕({∅};A))=Card(A)
    cardUN = composer_egalites(card1, card2)          # Card(𝓕(1;A))=Card(A)
    res = N.modus_ponens(cardUN, _card_impl_eq(FUN, va))   # Eq(𝓕(1;A), A)
    assert res.conclusion == enonce_base_111(a), "base_111 : conclusion ≠ énoncé attendu"
    return res


def enonce_heredite_111(a="A"):
    va = _t(a)
    vnd = var("ndep")
    return pourtout("ndep", impl(et(et(est_fini(vnd), inf_egal_card(UN_CARD, vnd)), _R111(vnd, va)),
                                 _R111(successeur(vnd), va)))


# @livre Ch.III §6.3 Demo.- | E III.49 L.5-6 | PDF p.152  (hérédité de la récurrence, R{n}⇒R{n+1} gardé)
def heredite_111(a0="a0", a="A"):
    """⊢ {Eq(A×A,A), a₀∈A}  (∀n)((n entier et n≥1 et R{n}) ⇒ R{n+1})   [R{m}=Eq(𝓕(m;A),A)].

    Conjonct hérédité de hypothese_recurrence_depuis(R,1) ; sous l'antécédent on extrait
    R{n} et on applique eq_R_np1 (les gardes n entier / n≥1 ne sont pas requises)."""
    va = _t(a)
    vnd = var("ndep")
    ant = et(et(est_fini(vnd), inf_egal_card(UN_CARD, vnd)), _R111(vnd, va))
    h = N.assume(ant)
    Rn = conjonction_elim_droite(h)                  # R{ndep} = Eq(𝓕(ndep;A),A)
    step = eq_R_np1("ndep", a0, a)                    # {R{ndep}, a²=a, a₀∈A} ⊢ R{succ ndep}
    cut_step = _cut(step, Rn)                         # {a²=a, a₀∈A, ant} ⊢ R{succ ndep}
    res = N.generalisation("ndep", N.loi_deduction(ant, cut_step))
    assert res.conclusion == enonce_heredite_111(a), "heredite_111 : conclusion ≠ énoncé attendu"
    return res


def enonce_a_puissance_n_egale_a(a="A"):
    """(∀n)((n entier et n≥1) ⇒ Eq(𝓕(n;A), A))   [= (∀n≥1) aⁿ = a]."""
    return conclusion_recurrence_depuis(_R111, UN_CARD, "ndep")


# @livre Ch.III §6.3 Cor.1 | E III.49 L.5-6 | PDF p.152   (Th.2 Cor.1 : aⁿ = a, a infini, n ≥ 1)
# @livre Ch.III §6.3 Demo.- | E III.49 L.5-6 | PDF p.152   (récurrence sur n depuis 1, base + hérédité + variante 2)
def a_puissance_n_egale_a(a0="a0", a="A"):
    """🎯 CONDITIONNEL {Eq(A×A,A), a₀∈A, predecesseur_fini_universel} ⊢
        (∀n)((n entier et n≥1) ⇒ Eq(𝓕(n;A), A))   (= aⁿ = a pour n ≥ 1).

    Récurrence « à partir de 1 » (variante 2, recurrence_depuis) sur R{n}=Eq(𝓕(n;A),A) :
      · base R{1}          = base_111        (clos) ;
      · hérédité R{n}⇒R{n+1} = heredite_111  ({a²=a, a₀∈A}).
    recurrence_depuis(_R111) est prouvée pour un k variable (kdep) ; on l'instancie à 1 en
    déchargeant d'abord ses deux gardes k-dépendantes dans la conclusion (loi_deduction),
    en généralisant kdep, puis en réinstanciant à UN_CARD et en déchargeant :
      · hypothese_recurrence_depuis(_R111,1) = conjonction_intro(base_111, heredite_111) ;
      · est_cardinal(1) = un_est_un_cardinal (clos).
    Résidu honnête : predecesseur_fini_universel (schéma C61, déchargeable par
    predecesseur_fini_universel_preuve dans un test lent isolé) ; l'hyp a²=a se décharge par
    Hessenberg (test lent) et a₀∈A par « A infini ⇒ A non vide » — d'où la version 0-hyp finale."""
    va = _t(a)
    rec = recurrence_depuis(_R111, k="kdep")          # {A1(kdep), est_card(kdep), pfu} ⊢ C(kdep)
    vk = var("kdep")
    A1 = hypothese_recurrence_depuis(_R111, vk, "ndep")   # garde 1 (k-dépendante)
    A2 = est_cardinal(vk)                                 # garde 2 (k-dépendante)
    assert A1 in rec.hypotheses and A2 in rec.hypotheses, "a_puissance_n : gardes attendues absentes"
    # décharger les deux gardes k-dépendantes dans la conclusion, puis ∀kdep, puis kdep:=1
    r1 = N.loi_deduction(A2, rec)                     # {A1, pfu} ⊢ est_card(kdep) ⇒ C(kdep)
    r2 = N.loi_deduction(A1, r1)                      # {pfu} ⊢ A1(kdep) ⇒ (est_card(kdep) ⇒ C(kdep))
    gen = N.generalisation("kdep", r2)               # {pfu} ⊢ (∀kdep)(...)
    inst = instancie(gen, UN_CARD)                   # {pfu} ⊢ A1(1) ⇒ (est_card(1) ⇒ C(1))
    A1_pr = conjonction_intro(base_111(a), heredite_111(a0, a))   # {a²=a, a₀∈A} ⊢ A1(1)
    A2_pr = un_est_un_cardinal()                     # ⊢ est_card(1)   [clos]
    mp1 = N.modus_ponens(A1_pr, inst)                # {pfu, a²=a, a₀∈A} ⊢ est_card(1) ⇒ C(1)
    res = N.modus_ponens(A2_pr, mp1)                 # {pfu, a²=a, a₀∈A} ⊢ C(1)
    assert res.conclusion == enonce_a_puissance_n_egale_a(a), \
        "a_puissance_n_egale_a : conclusion ≠ (∀n≥1) aⁿ=a"
    return res


__all__ = ["enonce_copie_gauche_inclus_somme", "copie_gauche_inclus_somme",
           "support_copie_gauche", "eq_exposant_copie_gauche", "inf_Fn_Fsucc",
           "sup_Fsucc_produit", "hyp_recurrence", "eq_produit_Fn_F1",
           "hyp_carre", "sup_Fsucc_le_A", "inf_A_Fsucc",
           "enonce_eq_Fsucc_A", "eq_Fsucc_A", "enonce_eq_R_np1", "eq_R_np1",
           "enonce_heredite_111", "heredite_111",
           "enonce_base_111", "base_111",
           "enonce_a_puissance_n_egale_a", "a_puissance_n_egale_a"]
