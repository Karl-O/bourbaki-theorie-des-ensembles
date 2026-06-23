"""Tests §III.3.5 — PROPOSITION 10 (currying) a^(b·c)=(a^b)^c : BIEN-DÉFINITION de Λ.

Verrouille la BIEN-DÉFINITION de la bijection de currying Λ : 𝓕(B×C;A)→𝓕(C;𝓕(B;A)),
f ↦ (c ↦ (b ↦ f(b,c))), en représentation FIDÈLE AU PONT membership×valeur
(f(b,c)=valeur(graphe_de(f),(b,c))=G(b,c)), DÉBLOQUÉE par `valeur_dans_codomaine`.

NIVEAU 0 (la TRANCHE est une application B→A), sous {graphe_de(f)⊂(B×C)×A,
dom graphe_de(f)=B×C, c∈C} :
  • tranche0_inclus_produit   tranche0(f,c) ⊂ B×A          [le PONT le long de q∈B] ;
  • tranche0_fonctionnel      est_fonctionnel(tranche0(f,c))           [C54, CLOS] ;
  • tranche0_domaine          dom(tranche0(f,c)) = B                   [C54, CLOS] ;
  • tranche0_dans_exposant    tranche0(f,c) ∈ A^B ;
  • slice0_dans_BA            slice0(f,c) = ((tranche0(f,c),B),A) ∈ 𝓕(B;A) ;
  • slice0_dans_BA_via_membership  f∈𝓕(B×C;A) ⇒ (c∈C ⇒ slice0(f,c)∈𝓕(B;A))   [CLOS].

NIVEAU 1 (la CURRYFIÉE est une application C→𝓕(B;A) ; Λ est BIEN DÉFINIE) :
  • curry0_fonctionnel        est_fonctionnel(curry0(f))               [C54, CLOS] ;
  • curry0_domaine            dom(curry0(f)) = C                       [C54, CLOS] ;
  • curry0_inclus_produit     f∈𝓕(B×C;A) ⇒ curry0(f) ⊂ C×𝓕(B;A)        [CLOS] ;
  • curry0_dans_exposant      f∈𝓕(B×C;A) ⇒ curry0(f) ∈ 𝓕(B;A)^C        [CLOS] ;
  • lambda_val0_dans_codomaine  f∈𝓕(B×C;A) ⇒ Λval0(f) ∈ 𝓕(C;𝓕(B;A))   [CLOS].

Aucun axiome ajouté (theorie_ensembles inchangée = 22) : axiome_exposant /
axiome_applications (instances GÉNÉRALES déjà admises), PONT valeur_dans_codomaine,
graphe_de_triple, C54.  Rien postulé.  Reste REPORTÉ : injectivité complète et
surjectivité à deux niveaux (back-and-forth d'extensionnalité fonctionnelle).
"""
from bourbaki.logique.formule import var, egal, impl, appartient, inclus
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.cardinaux.arithmetique import ensembles_prop10_close as P


def _ctx(f="f", c="c", a="A", b="B", cc="C"):
    return var(f), var(c), var(a), var(b), var(cc)


# hypothèses-graphe (conjoints du témoin de f∈𝓕(B×C;A)) :
def _h_incl(vf, va, vb, vcc):
    return inclus(P.gr(vf), E.produit(E.produit(vb, vcc), va))   # gr ⊂ (B×C)×A


def _h_dom(vf, vb, vcc):
    return egal(E.dom(P.gr(vf)), E.produit(vb, vcc))            # dom gr = B×C


# ═══════════════════════════════════════════════════════════════════════════════
# NIVEAU 0 — la TRANCHE tranche0(f,c) = { (b, G(b,c)) | b∈B }
# ═══════════════════════════════════════════════════════════════════════════════
def test_tranche0_fonctionnel():
    """⊢ est_fonctionnel(tranche0(f,c)), CLOS  (C54)."""
    vf, vc, va, vb, _ = _ctx()
    t = P.tranche0_fonctionnel()
    assert t.est_clos
    assert t.conclusion == E.est_fonctionnel(P.tranche0(vf, vc, va, vb))


def test_tranche0_domaine():
    """⊢ dom(tranche0(f,c)) = B, CLOS  (C54)."""
    vf, vc, va, vb, _ = _ctx()
    t = P.tranche0_domaine()
    assert t.est_clos
    assert t.conclusion == egal(E.dom(P.tranche0(vf, vc, va, vb)), vb)


def test_tranche0_inclus_produit():
    """{gr⊂(B×C)×A, dom gr=B×C, c∈C} ⊢ tranche0(f,c) ⊂ B×A  (le PONT le long de q∈B)."""
    vf, vc, va, vb, vcc = _ctx()
    t = P.tranche0_inclus_produit()
    assert t.conclusion == inclus(P.tranche0(vf, vc, va, vb), E.produit(vb, va))
    hyps = {str(h) for h in t.hypotheses}
    assert hyps == {str(_h_incl(vf, va, vb, vcc)), str(_h_dom(vf, vb, vcc)),
                    str(appartient(vc, vcc))}


def test_tranche0_dans_exposant():
    """{gr⊂(B×C)×A, dom gr=B×C, c∈C} ⊢ tranche0(f,c) ∈ A^B."""
    vf, vc, va, vb, vcc = _ctx()
    t = P.tranche0_dans_exposant()
    assert t.conclusion == appartient(P.tranche0(vf, vc, va, vb), E.exposant(vb, va))
    hyps = {str(h) for h in t.hypotheses}
    assert hyps == {str(_h_incl(vf, va, vb, vcc)), str(_h_dom(vf, vb, vcc)),
                    str(appartient(vc, vcc))}


def test_slice0_dans_BA():
    """{gr⊂(B×C)×A, dom gr=B×C, c∈C} ⊢ slice0(f,c) ∈ 𝓕(B;A)."""
    vf, vc, va, vb, vcc = _ctx()
    t = P.slice0_dans_BA()
    assert t.conclusion == appartient(P.slice0(vf, vc, va, vb), E.applications(vb, va))
    hyps = {str(h) for h in t.hypotheses}
    assert hyps == {str(_h_incl(vf, va, vb, vcc)), str(_h_dom(vf, vb, vcc)),
                    str(appartient(vc, vcc))}


def test_slice0_dans_BA_via_membership():
    """⊢ f∈𝓕(B×C;A) ⇒ (c∈C ⇒ slice0(f,c) ∈ 𝓕(B;A)), CLOS.

    BIEN-DÉFINITION de NIVEAU 0 AUTONOME : la valeur de la curryfiée en c est une
    vraie application B→A.  Hypothèses-graphe déchargées depuis f∈𝓕(B×C;A) (témoin
    G, graphe_de_triple + exposant_BA)."""
    vf, vc, va, vb, vcc = _ctx()
    t = P.slice0_dans_BA_via_membership()
    assert t.est_clos
    attendu = impl(appartient(vf, E.applications(E.produit(vb, vcc), va)),
                   impl(appartient(vc, vcc),
                        appartient(P.slice0(vf, vc, va, vb), E.applications(vb, va))))
    assert t.conclusion == attendu


# ═══════════════════════════════════════════════════════════════════════════════
# NIVEAU 1 — la CURRYFIÉE curry0(f) = { (c, f_c) | c∈C } est une application C→𝓕(B;A)
# ═══════════════════════════════════════════════════════════════════════════════
def test_curry0_fonctionnel():
    """⊢ est_fonctionnel(curry0(f)), CLOS  (C54)."""
    vf, _, va, vb, vcc = _ctx()
    t = P.curry0_fonctionnel()
    assert t.est_clos
    assert t.conclusion == E.est_fonctionnel(P.curry0(vf, va, vb, vcc))


def test_curry0_domaine():
    """⊢ dom(curry0(f)) = C, CLOS  (C54)."""
    vf, _, va, vb, vcc = _ctx()
    t = P.curry0_domaine()
    assert t.est_clos
    assert t.conclusion == egal(E.dom(P.curry0(vf, va, vb, vcc)), vcc)


def test_curry0_inclus_produit():
    """⊢ f∈𝓕(B×C;A) ⇒ curry0(f) ⊂ C×𝓕(B;A), CLOS  (le « pont » de niveau 1 = niveau 0)."""
    vf, _, va, vb, vcc = _ctx()
    t = P.curry0_inclus_produit()
    assert t.est_clos
    h_f = appartient(vf, E.applications(E.produit(vb, vcc), va))
    FBA = E.applications(vb, va)
    assert t.conclusion == impl(h_f, inclus(P.curry0(vf, va, vb, vcc),
                                            E.produit(vcc, FBA)))


def test_curry0_dans_exposant():
    """⊢ f∈𝓕(B×C;A) ⇒ curry0(f) ∈ 𝓕(B;A)^C, CLOS."""
    vf, _, va, vb, vcc = _ctx()
    t = P.curry0_dans_exposant()
    assert t.est_clos
    h_f = appartient(vf, E.applications(E.produit(vb, vcc), va))
    FBA = E.applications(vb, va)
    assert t.conclusion == impl(h_f, appartient(P.curry0(vf, va, vb, vcc),
                                                E.exposant(vcc, FBA)))


def test_lambda_val0_dans_codomaine():
    """⊢ f∈𝓕(B×C;A) ⇒ Λval0(f) ∈ 𝓕(C;𝓕(B;A)), CLOS.

    BIEN-DÉFINITION COMPLÈTE de Λ (les deux niveaux) : l'image de f par la
    currification tombe dans le codomaine 𝓕(C;𝓕(B;A)).  Conjoint (i) reporté de
    `ensembles_prop10_currying`, ICI CLOS (représentation fidèle au pont)."""
    vf, _, va, vb, vcc = _ctx()
    t = P.lambda_val0_dans_codomaine()
    assert t.est_clos
    h_f = appartient(vf, E.applications(E.produit(vb, vcc), va))
    FBA = E.applications(vb, va)
    assert t.conclusion == impl(h_f, appartient(P.lambda_val0(vf, va, vb, vcc),
                                                E.applications(vcc, FBA)))


# ═══════════════════════════════════════════════════════════════════════════════
# Termes de la construction (cohérence structurelle de Λ niveau 0 / niveau 1)
# ═══════════════════════════════════════════════════════════════════════════════
def test_slice0_terme():
    """slice0(f,c) est bien le triple ((tranche0(f,c), B), A)."""
    vf, vc, va, vb, _ = _ctx()
    assert P.slice0(vf, vc, va, vb) == E.couple(
        E.couple(P.tranche0(vf, vc, va, vb), vb), va)


def test_lambda_val0_terme():
    """Λval0(f) est bien le triple ((curry0(f), C), 𝓕(B;A))."""
    vf, _, va, vb, vcc = _ctx()
    assert P.lambda_val0(vf, va, vb, vcc) == E.couple(
        E.couple(P.curry0(vf, va, vb, vcc), vcc), E.applications(vb, va))
