"""Tests MIROIR — ensembles_subset_realise_close : vers `subset_realise_segment` par la
TRICHOTOMIE (Th3 §III.2) appliquée à (B, ordre induit) vs (a, Ro), func/dom RÉCUPÉRÉS
du témoin h' (h-derivé, PAS le ∃f nu).

On vérifie (hypothèses EXACTES contrôlées, theorie=22, anti-tautologie) :
  • les 5 briques h-niveau instanciées à (B,graphe_induit(Ro,B),a,Ro) :
        iso_h_prime / func_h_prime / maximalite_h_prime  (2 hyps honnêtes {bo,⊆}),
        seg_dom_h_prime / seg_pr2_h_prime                (CLOS, theorie=22) ;
  • eq_B_pr2_sous_dom_eq_B : { bo, B⊆a, dom h'=B } ⊢ Eq(B, pr₂h') ;
  • pr2_eq_seg_exists      : { bo, pr₂h'≠a } ⊢ ∃t(t∈a et pr₂h'=seg(Ro,a,t)) ;
  • realise_segment_pour_B : { bo, B⊆a, dom h'=B, pr₂h'≠a } ⊢ ∃t(t∈a et Eq(B,seg)) ;
  • realise_segment_pour_B_sans_dom : { bo, B⊆a, ¬(pr₂h'=a) } ⊢ ∃t(t∈a et Eq(B,seg)).

⚠️ subset_realise_segment LITTÉRAL (∀B incl. B=a) N'EST PAS clos : pour B=a (et pour
le cardinal TOP Card(a)), un segment PROPRE seg(Ro,a,t) n'est pas équipotent à a (a
fini) ⇒ la condition de branche ¬(pr₂h'=a) (= « B n'épuise pas a ») est précisément
le contenu honnête restant.  Cf. RAPPORT.
"""
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
import bourbaki.cardinaux.ensembles_subset_realise_close as M


def test_theorie_ensembles_22():
    assert len(E.theorie_ensembles().axiomes) == 22


# ── les 5 briques h-niveau instanciées ────────────────────────────────────────
def _bo_Ro_a():
    from bourbaki.cardinaux.ensembles_segments_construction import _R_de
    return E.est_bien_ordonne(_R_de("Ro"), E.var("asr"))


def _B_sub_a():
    from bourbaki.logique.i_1_termes_relations.formule import inclus
    return inclus(E.var("Bsr"), E.var("asr"))


def test_iso_h_prime_hyps_honnetes():
    t = M.iso_h_prime()
    assert set(t.hypotheses) == {_bo_Ro_a(), _B_sub_a()}
    assert t.conclusion not in set(t.hypotheses)
    assert len(E.theorie_ensembles().axiomes) == 22


def test_func_h_prime_hyps_honnetes():
    t = M.func_h_prime()
    assert set(t.hypotheses) == {_bo_Ro_a(), _B_sub_a()}
    assert t.conclusion not in set(t.hypotheses)


def test_maximalite_h_prime_disjonction():
    from bourbaki.logique.i_1_termes_relations.formule import ou, egal
    t = M.maximalite_h_prime()
    vh = M.h_prime()
    assert t.conclusion == ou(egal(E.dom(vh), E.var("Bsr")), egal(E.img(vh), E.var("asr")))
    assert set(t.hypotheses) == {_bo_Ro_a(), _B_sub_a()}


def test_seg_dom_h_prime_clos():
    t = M.seg_dom_h_prime()
    assert t.est_clos and len(t.hypotheses) == 0
    assert len(E.theorie_ensembles().axiomes) == 22


def test_seg_pr2_h_prime_clos():
    t = M.seg_pr2_h_prime()
    assert t.est_clos and len(t.hypotheses) == 0


# ── cœur : Eq(B, pr₂h') sous dom h'=B ─────────────────────────────────────────
def test_eq_B_pr2_conclusion_et_hyps():
    t = M.eq_B_pr2_sous_dom_eq_B()
    assert t.conclusion == M.eq_B_pr2_sous_dom_eq_B_cible()
    assert t.conclusion not in set(t.hypotheses)         # non vacueux
    assert len(t.hypotheses) == 3                        # {bo, B⊆a, dom h'=B}
    # toutes les hyps sont honnêtes : bo, B⊆a, ou dom h'=B (pas la conclusion)
    assert len(E.theorie_ensembles().axiomes) == 22


# ── pr₂h' = seg(Ro,a,t) sous pr₂h'≠a ──────────────────────────────────────────
def test_pr2_eq_seg_exists_conclusion():
    t = M.pr2_eq_seg_exists()
    assert t.conclusion == M.pr2_eq_seg_exists_cible()
    assert t.conclusion not in set(t.hypotheses)


# ── assemblage per-B ──────────────────────────────────────────────────────────
def test_realise_segment_pour_B_conclusion():
    t = M.realise_segment_pour_B()
    assert t.conclusion == M.realise_segment_pour_B_cible()
    assert t.conclusion not in set(t.hypotheses)
    assert len(t.hypotheses) == 4                        # {bo, B⊆a, dom h'=B, pr₂h'≠a}


def test_realise_segment_pour_B_sans_dom_3_hyps():
    from bourbaki.logique.i_1_termes_relations.formule import non, egal
    t = M.realise_segment_pour_B_sans_dom()
    assert t.conclusion == M.realise_segment_pour_B_cible()
    assert t.conclusion not in set(t.hypotheses)
    # exactement 3 hyps HONNÊTES : bo(Ro,a), B⊆a, ¬(pr₂h'=a)
    vh = M.h_prime()
    assert set(t.hypotheses) == {_bo_Ro_a(), _B_sub_a(), non(egal(E.img(vh), E.var("asr")))}
    assert len(E.theorie_ensembles().axiomes) == 22


# ── equipotent ⇒ ≤  (CLOS) ────────────────────────────────────────────────────
def test_equipotent_implique_inf_egal_clos():
    t = M.equipotent_implique_inf_egal()
    assert t.est_clos and len(t.hypotheses) == 0
    assert len(E.theorie_ensembles().axiomes) == 22


# ── pr₂h'=a ⇒ Eq(B,a) (Cantor-Bernstein) ─────────────────────────────────────
def test_pr2_eq_a_donne_eq_B_a():
    from bourbaki.logique.i_1_termes_relations.formule import egal
    from bourbaki.cardinaux.ensembles_cardinaux import equipotent
    t = M.pr2_eq_a_donne_eq_B_a()
    assert t.conclusion == equipotent(E.var("Bsr"), E.var("asr"))   # Eq(B,a)
    assert t.conclusion not in set(t.hypotheses)
    # 3 hyps honnêtes : bo, B⊆a, pr₂h'=a
    vh = M.h_prime()
    assert set(t.hypotheses) == {_bo_Ro_a(), _B_sub_a(), egal(E.img(vh), E.var("asr"))}


# ── FORME PROPRE : ¬Eq(B,a) ⇒ ∃t(t∈a et Eq(B,seg)) ───────────────────────────
def test_realise_segment_pour_B_clean_3_hyps():
    from bourbaki.logique.i_1_termes_relations.formule import non
    from bourbaki.cardinaux.ensembles_cardinaux import equipotent
    t = M.realise_segment_pour_B_clean()
    assert t.conclusion == M.realise_segment_pour_B_clean_cible()
    assert t.conclusion not in set(t.hypotheses)
    # exactement 3 hyps HONNÊTES : bo(Ro,a), B⊆a, ¬Eq(B,a)
    assert set(t.hypotheses) == {_bo_Ro_a(), _B_sub_a(),
                                 non(equipotent(E.var("Bsr"), E.var("asr")))}
    assert len(E.theorie_ensembles().axiomes) == 22
