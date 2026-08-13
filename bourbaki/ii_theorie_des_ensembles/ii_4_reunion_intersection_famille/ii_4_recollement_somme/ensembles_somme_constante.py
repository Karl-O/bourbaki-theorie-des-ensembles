"""§II.4.8 / §III.3.4 — T3b LA SOMME D'UNE FAMILLE CONSTANTE  ⊔_{ι∈I} a = a×I
(Prop. 6, Cor. 2, E III.27) — la pièce maîtresse du mur des familles.

VOIE COURTE (décision) : PAS de bijection à construire.  Par AXIOME_SOMME_FAM,
z∈⊔(fam,I) ⇔ (∃i∈I)(z ∈ X_i×{i}) ; si CHAQUE X_i vaut a (ponctuellement),
chaque copie marquée a×{i} tombe dans a×I, et réciproquement tout (u,i)∈a×I
remonte dans ⊔ par l'injection canonique element_marque_dans_somme.  DOUBLE
INCLUSION ponctuelle + extensionnalité (C48) ⇒ ÉGALITÉ D'ENSEMBLES ⊔ = a×I ;
la forme cardinale suit par CONGRUENCE de Card sur cette égalité (même terme —
aucune invariance par équipotence n'est requise).  Le cœur générique
_somme_ponctuelle_produit sert AUSSI les bergers (ensembles_bergers_plein).

PALIERS CERTIFIÉS (un test chacun, cf. test_somme_constante.py) :
  P1 famille_constante_valeur {i0∈I}     ⊢ fam_const(i0) = a          [1 hyp]
  P2 fam_const_egale   Γ⊢t∈I ⟹ Γ∪{HFc}  ⊢ valeur_famille(fam_const,t) = a
  P3 somme_constante_egale_produit {HFc} ⊢ ⊔(fam_const, I) = a×I        🎯 T3b
  P4 card_somme_constante {HFc}          ⊢ Σ_{ι∈I} a = Card(a×I)  [= ab, Cor.2]

HYPOTHÈSE HONNÊTE (la seule) :
  HFc := (∀ihc∈I) valeur_famille(fam_const,ihc) = valeur(fam_const,ihc)
         — pont fam↔valeur de la famille constante (mur « fam », précédent HF/HW).

LIANTS : fam_const est un C54 de liant EXOTIQUE « jcs » au terme-valeur CONSTANT
a (τ-léger : subst triviale).  Liants locaux exotiques : zcs (élément), ics (∃i
renommé), ucs (témoin produit-singleton), pcs/qcs (∃p∃q du produit renommés —
OBLIGATOIRE : element_marque_dans_somme refuse p/q libres), wcs (trous Leibniz),
i0cs (point-valeur), ihc (liant de HFc).
GARDE : la machinerie TRAVERSÉE lie {i, p, q, u→ucs, w, x, y, z, jcs} —
les termes fournis (a, I) ne doivent contenir AUCUN de ces noms libre.
Rien postulé ; noyau/subst intouchés ; theorie_ensembles()==22 (asserté en test).
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, egal, et, impl, appartient, existe, pourtout, subst_f)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege import (
    a_implique_a)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, equivalence_transitivite, instancie)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
    composer_egalites, congruence_terme)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import (
    existe_elimination, alpha_existe, congruence_existe)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_theoremes import (
    egalite_par_extension)
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_recollement_somme.ensembles_somme_disjointe import (
    _membre_produit_singleton)
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_recollement_somme.ensembles_somme_indexee import (
    membre_somme_famille, element_marque_dans_somme)
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_recollement_somme.ensembles_fibres_famille import (
    _t, _dech)

JCS = "jcs"    # liant C54 de la famille constante — EXOTIQUE


# ── La famille constante (a)_{ι∈I} et ses hypothèses ─────────────────────────
# @livre Ch.III §3.4 Cor.2 | E III.27 L.27-29 | PDF p.130
#   (« pour tout ι∈I, soit a_ι = a » — la famille constante du Corollaire 2,
#    codée graphe_terme C54 au terme-valeur CONSTANT a, liant exotique jcs.)
def famille_constante(a="Acs", i_set="Ics"):
    """fam_const := graphe_terme(I, a, "jcs")   (la famille (a)_{ι∈I} ; le
    terme-valeur est la VARIABLE a — jamais « jcs » libre dedans, subst triviale)."""
    return E.graphe_terme(_t(i_set), _t(a), JCS)


def hypothese_pont_const(a="Acs", i_set="Ics"):
    """HFc := (∀ihc)((ihc∈I) ⇒ (valeur_famille(fam_const,ihc) = valeur(fam_const,ihc))).

    Pont fam↔valeur pour la famille constante (improuvable : « fam » est un
    symbole libre de l'encodage — mur documenté de T1c, précédent HF de S3)."""
    X = famille_constante(a, i_set)
    vi = var("ihc")
    return pourtout("ihc", impl(appartient(vi, _t(i_set)),
                                egal(E.valeur_famille(X, vi), E.valeur(X, vi))))


# ── P1 : la valeur de fam_const en un NOM i0 ─────────────────────────────────
def famille_constante_valeur(i0="i0cs", a="Acs", i_set="Ics"):
    """P1 {i0∈I} ⊢ fam_const(i0) = a                          [1 hyp ; i0 NOM].

    graphe_terme_valeur (nom-basée) : T[i0] = (i0|jcs)a = a car jcs ∉ libres(a).
    Pour un TERME, passer par fam_const_egale (motif _inst_gen)."""
    assert isinstance(i0, str), "famille_constante_valeur : i0 doit être un NOM"
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.cantor.ensembles_cantor import (
        graphe_terme_valeur)
    va, vI = _t(a), _t(i_set)
    res = graphe_terme_valeur(vI, va, i0, JCS)
    cible = egal(E.valeur(famille_constante(a, i_set), var(i0)), va)
    assert res.conclusion == cible, "P1 : ≠ fam_const(i0)=a"
    assert res.hypotheses == frozenset({appartient(var(i0), vI)}), "P1 : hyps"
    return res


# ── P2 : la valeur_famille au TERME (pont HFc + _inst_gen) ───────────────────
def fam_const_egale(thm_in_I, tt, a="Acs", i_set="Ics"):
    """P2 : Γ ⊢ t∈I  ⟹  Γ∪{HFc} ⊢ valeur_famille(fam_const, t) = a.  (t TERME.)

    (α) HFc instanciée en t ; (β) P1 ∀-close sur le nom i0cs puis instanciée en
    t (motif _inst_gen) ; (γ) composition.  t sans « i0cs »/« ihc » libres."""
    vI, va = _t(i_set), _t(a)
    X = famille_constante(a, i_set)
    hf = N.assume(hypothese_pont_const(a, i_set))
    fam_eq = N.modus_ponens(thm_in_I, instancie(hf, tt))   # fam(X,t)=valeur(X,t)
    imp = N.loi_deduction(appartient(var("i0cs"), vI),
                          famille_constante_valeur("i0cs", a, i_set))
    val_eq = N.modus_ponens(thm_in_I,
                            instancie(N.generalisation("i0cs", imp), tt))
    res = composer_egalites(fam_eq, val_eq)                # fam(X,t)=a
    assert res.conclusion == egal(E.valeur_famille(X, tt), va), "P2 : forme"
    return res


# ── LE CŒUR : ⊔ d'une famille PONCTUELLEMENT constante = a×I ─────────────────
def _somme_ponctuelle_produit(fam, vI, va, ptw):
    """⊢ somme_famille(fam, I) = a×I  sous les hypothèses de ptw.

    ptw(t, Γ⊢t∈I) doit rendre Γ' ⊢ valeur_famille(fam, t) = a  (t TERME).
    ⊂ : z∈⊔ ⇒ (∃ics∈I) z∈X_ics×{ics} ; X_ics=a (ptw), z=(ucs,ics), ucs∈a,
        ics∈I ⇒ (ucs,ics)∈a×I ⇒ z∈a×I (trous Leibniz wcs).
    ⊃ : z∈a×I ⇒ z=(pcs,qcs), pcs∈a=X_qcs ⇒ (pcs,qcs)∈⊔ (element_marque) ⇒ z∈⊔.
        Les ∃p∃q d'AXIOME_PRODUIT sont α-renommés pcs/qcs (element_marque
        refuse p/q libres).  Élément zcs α-renommé en z pour l'extension (C48)."""
    S, P = E.somme_famille(fam, vI), E.produit(va, vI)
    vz, vics, vucs = var("zcs"), var("ics"), var("ucs")
    vpcs, vqcs = var("pcs"), var("qcs")

    # ── ⊂ : z∈⊔ ⇒ z∈a×I ─────────────────────────────────────────────────────
    corps_i = et(appartient(var("i"), vI),
                 appartient(vz, E.produit(E.valeur_famille(fam, var("i")),
                                          E.singleton(var("i")))))
    som_car = equivalence_transitivite(membre_somme_famille(fam, vI, vz),
                                       alpha_existe("i", "ics", corps_i))
    corps_ics = subst_f(vics, "i", corps_i)
    hb = N.assume(corps_ics)
    i_in = conjonction_elim_gauche(hb)                     # ics∈I
    prod_in = conjonction_elim_droite(hb)                  # z ∈ X_ics×{ics}
    pw = ptw(vics, i_in)                                   # fam(fam,ics) = a
    leib = N.modus_ponens(pw, N.s6(E.valeur_famille(fam, vics), va, "wcs",
        appartient(vz, E.produit(var("wcs"), E.singleton(vics)))))
    prod_a = N.modus_ponens(prod_in, equivalence_avant(leib))   # z ∈ a×{ics}
    ex_u = N.modus_ponens(prod_a,
        equivalence_avant(_membre_produit_singleton(va, vics, vz, "ucs")))
    inner = et(appartient(vucs, va), egal(vz, E.couple(vucs, vics)))
    hi = N.assume(inner)
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_produit.ensembles_produit_commute import (
        _couple_dans_produit_t)
    cpl = E.couple(vucs, vics)
    cpl_in = N.modus_ponens(
        conjonction_intro(conjonction_elim_gauche(hi), i_in),
        _couple_dans_produit_t(vucs, vics, va, vI))        # (ucs,ics)∈a×I
    leib2 = N.modus_ponens(conjonction_elim_droite(hi),
        N.s6(vz, cpl, "wcs", appartient(var("wcs"), P)))
    z_in_P = N.modus_ponens(cpl_in, equivalence_arriere(leib2))  # z∈a×I
    z_in_P = N.modus_ponens(ex_u,
        existe_elimination(N.loi_deduction(inner, z_in_P), "ucs"))
    imp_i = existe_elimination(N.loi_deduction(corps_ics, z_in_P), "ics")
    hs = N.assume(appartient(vz, S))
    fwd = N.loi_deduction(appartient(vz, S),
        N.modus_ponens(N.modus_ponens(hs, equivalence_avant(som_car)), imp_i))

    # ── ⊃ : z∈a×I ⇒ z∈⊔ ─────────────────────────────────────────────────────
    ax_prod = N.axiome(E.theorie_ensembles(), E.AXIOME_PRODUIT)
    inst = instancie(instancie(instancie(ax_prod, va), vI), vz)
    body = et(et(egal(vz, E.couple(var("p"), var("q"))),
                 appartient(var("p"), va)), appartient(var("q"), vI))
    ren_q = congruence_existe(alpha_existe("q", "qcs", body), "p")
    body_q = subst_f(vqcs, "q", body)
    ren_p = alpha_existe("p", "pcs", existe("qcs", body_q))
    car = equivalence_transitivite(inst, equivalence_transitivite(ren_q, ren_p))
    body_pq = subst_f(vpcs, "p", body_q)
    hb2 = N.assume(body_pq)
    z_eq = conjonction_elim_gauche(conjonction_elim_gauche(hb2))  # z=(pcs,qcs)
    p_in = conjonction_elim_droite(conjonction_elim_gauche(hb2))  # pcs∈a
    q_in = conjonction_elim_droite(hb2)                           # qcs∈I
    pw2 = ptw(vqcs, q_in)                                  # fam(fam,qcs) = a
    leib3 = N.modus_ponens(pw2, N.s6(E.valeur_famille(fam, vqcs), va, "wcs",
        appartient(vpcs, var("wcs"))))
    p_in_X = N.modus_ponens(p_in, equivalence_arriere(leib3))    # pcs ∈ X_qcs
    ems = _dech(element_marque_dans_somme(fam, vI, vpcs, vqcs), q_in, p_in_X)
    leib4 = N.modus_ponens(z_eq, N.s6(vz, E.couple(vpcs, vqcs), "wcs",
        appartient(var("wcs"), S)))
    z_in_S = N.modus_ponens(ems, equivalence_arriere(leib4))     # z∈⊔
    imp_pq = existe_elimination(existe_elimination(
        N.loi_deduction(body_pq, z_in_S), "qcs"), "pcs")
    hp = N.assume(appartient(vz, P))
    bwd = N.loi_deduction(appartient(vz, P),
        N.modus_ponens(N.modus_ponens(hp, equivalence_avant(car)), imp_pq))

    # ── double inclusion → égalité (zcs α-renommé en z, motif S3) ────────────
    equiv_z = instancie(N.generalisation("zcs", conjonction_intro(fwd, bwd)),
                        var("z"))
    char = N.generalisation("z", equiv_z)
    zP = appartient(var("z"), P)
    self_P = N.generalisation("z",
        conjonction_intro(a_implique_a(zP), a_implique_a(zP)))
    res = egalite_par_extension(char, self_P, S, P, "z")
    assert res.conclusion == egal(S, P), "cœur : forme"
    return res


# ── P3 = T3b : ⊔ d'une famille constante = a×I ───────────────────────────────
# @livre Ch.III §3.4 Cor.2 | E III.27 L.27-29 | PDF p.130
#   (« Soient a et b des cardinaux, et soit I un ensemble équipotent à b ; pour
#    tout ι∈I, soit a_ι = a … ab = Σ_{ι∈I} a_ι » — ICI le contenu ENSEMBLISTE :
#    la somme de la famille constante EST a×I, égalité d'ensembles ; la forme
#    cardinale Σ = Card(a×I) = ab est card_somme_constante ci-dessous.)
def somme_constante_egale_produit(a="Acs", i_set="Ics"):
    """🎯 T3b {HFc} ⊢ somme_famille(fam_const, I) = a × I.  (égalité d'ENSEMBLES.)"""
    va, vI = _t(a), _t(i_set)
    X = famille_constante(a, i_set)
    res = _somme_ponctuelle_produit(X, vI, va,
        lambda tt, thm: fam_const_egale(thm, tt, a, i_set))
    assert res.conclusion == egal(E.somme_famille(X, vI),
                                  E.produit(va, vI)), "T3b : forme"
    assert res.hypotheses == frozenset({hypothese_pont_const(a, i_set)}), "T3b : hyps"
    return res


# ── P4 : la forme cardinale du Corollaire 2 ──────────────────────────────────
# @livre Ch.III §3.4 Cor.2 | E III.27 L.27-29 | PDF p.130
def card_somme_constante(a="Acs", i_set="Ics"):
    """P4 {HFc} ⊢ somme_cardinale(fam_const, I) = Card(a×I)  [= ab, Cor. 2].

    CONGRUENCE de Card sur l'égalité d'ENSEMBLES T3b (même terme, aucune
    invariance requise) ; le LHS EST Σ_{ι∈I} a, le RHS EST a·I (assertés)."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
        cardinal, somme_cardinale)
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_produit.ensembles_arith_cardinale import (
        produit_cardinal_binaire)
    va, vI = _t(a), _t(i_set)
    X = famille_constante(a, i_set)
    S, P = E.somme_famille(X, vI), E.produit(va, vI)
    res = N.modus_ponens(somme_constante_egale_produit(a, i_set),
                         congruence_terme(S, P, cardinal(var("wcs")), "wcs"))
    assert res.conclusion == egal(cardinal(S), cardinal(P)), "P4 : forme"
    assert cardinal(S) == somme_cardinale(X, vI), "P4 : LHS ≠ Σ_{ι∈I} a"
    assert cardinal(P) == produit_cardinal_binaire(va, vI), "P4 : RHS ≠ a·I"
    assert res.hypotheses == frozenset({hypothese_pont_const(a, i_set)}), "P4 : hyps"
    return res


__all__ = ["JCS", "famille_constante", "hypothese_pont_const",
           "famille_constante_valeur", "fam_const_egale",
           "somme_constante_egale_produit", "card_somme_constante",
           "_somme_ponctuelle_produit"]
