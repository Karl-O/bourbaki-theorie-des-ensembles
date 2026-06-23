"""Tests §III.3.5 — PROPOSITION 9 (forme exponentielle), CLÔTURE par CANTOR–BERNSTEIN :
a^(b+c) = a^b · a^c, i.e. Card(𝓕(B⊔C;A)) = Card(𝓕(B;A) × 𝓕(C;A)).

Couvre les PALIERS CLOS du module ensembles_prop9_close :
  • bien-définition des restrictions (LE déblocage : pont graphe_de) ;
  • Φ(f) ∈ 𝓕(B;A)×𝓕(C;A)  sous f∈𝓕(B⊔C;A) ;
  • les 4 conjoints de est_injection_de(W_Φ, …) → inf_egal_card (DIRECTION A) ;
  • DIRECTION B (ψ), Cantor-Bernstein, égalité-cible — selon l'état du module.

Les représentations τ imbriquées rendent certains théorèmes lents (cf. MEMORY) ;
les tests les plus lourds sont marqués pour exécution ciblée si besoin.
"""
from bourbaki.logique.formule import var, egal, et, impl, appartient, inclus
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.cardinaux.ensembles_cardinaux import (
    inf_egal_card, est_injection_de, equipotent, cardinal)
from bourbaki.ensembles.familles.ii_4_reunion_intersection_familles.ii_4_recollement_somme.ensembles_somme_disjointe import somme_disjointe
from bourbaki.cardinaux.arithmetique.ensembles_prop9_exp_somme import cible_prop9_exp_somme
import bourbaki.cardinaux.arithmetique.ensembles_prop9_close as P


# ── PALIER restrictions : fonctionnelle / domaine (C54) ───────────────────────
def test_restriction_fonctionnelle_domaine():
    """f|B, f|C sont de VRAIES fonctions (fonctionnelles, domaines B, C)."""
    assert P.restriction_gauche_fonctionnelle().est_clos
    assert P.restriction_gauche_domaine().est_clos
    assert P.restriction_droite_fonctionnelle().est_clos
    assert P.restriction_droite_domaine().est_clos


# ── PALIER bien-définition (LE PONT graphe_de) :  f|B ⊂ B×A,  f|C ⊂ C×A ────────
def test_restriction_inclus_gauche():
    """{graphe_de(f)⊂(B⊔C)×A, dom graphe_de(f)=B⊔C} ⊢ f|B ⊂ B×A  (bien-déf gauche)."""
    t = P.restriction_gauche_inclus()
    assert not t.est_clos and len(t.hypotheses) == 2


def test_restriction_inclus_droite():
    """{…} ⊢ f|C ⊂ C×A  (bien-déf droite)."""
    t = P.restriction_droite_inclus()
    assert not t.est_clos and len(t.hypotheses) == 2


# ── PALIER triple ∈ 𝓕(·;A)  et  Φ(f) ∈ codomaine ──────────────────────────────
def test_triple_dans_applications():
    """((f|B,B),A)∈𝓕(B;A) et ((f|C,C),A)∈𝓕(C;A)  (sous hyps structurelles)."""
    assert P.triple_gauche_dans_applications().est_clos is False
    assert P.triple_droite_dans_applications().est_clos is False


def test_phi_dans_codomaine_sous_appartenance():
    """{f∈𝓕(B⊔C;A)} ⊢ Φ(f) ∈ 𝓕(B;A)×𝓕(C;A)  (BIEN-DÉFINITION COMPLÈTE de Φ)."""
    va, vb, vc = var("A"), var("B"), var("C")
    t = P.phi_dans_codomaine_sous_appartenance()
    BC = somme_disjointe(vb, vc)
    hyp = appartient(var("f"), E.applications(BC, va))
    assert t.hypotheses == frozenset({hyp})
    cod = P.codomaine_phi(va, vb, vc)
    assert t.conclusion == appartient(P.phi_valeur(var("f"), va, vb, vc), cod)


# ── PALIER conjoints de W_Φ ───────────────────────────────────────────────────
def test_W_phi_conjoints_structurels():
    """W_Φ fonctionnel, dom W_Φ=𝓕(B⊔C;A), image⊂codomaine  (CLOS)."""
    assert P.W_phi_fonctionnel().est_clos
    assert P.W_phi_domaine().est_clos
    assert P.W_phi_image_incluse().est_clos


def test_W_phi_injective():
    """⊢ injective_dans(W_Φ, 𝓕(B⊔C;A))  (CLOS) — cœur back-and-forth via extensionnalité."""
    va, vb, vc = var("A"), var("B"), var("C")
    t = P.W_phi_injective()
    assert t.est_clos
    assert t.conclusion == E.injective_dans(P.W_phi(va, vb, vc),
                                            P.domaine_phi(va, vb, vc))


# ── DIRECTION A :  𝓕(B⊔C;A) ≤ 𝓕(B;A)×𝓕(C;A) ──────────────────────────────────
def test_W_phi_est_injection():
    """⊢ est_injection_de(W_Φ, 𝓕(B⊔C;A), 𝓕(B;A)×𝓕(C;A))  (les 4 conjoints, CLOS)."""
    va, vb, vc = var("A"), var("B"), var("C")
    t = P.W_phi_est_injection()
    assert t.est_clos
    assert t.conclusion == est_injection_de(P.W_phi(va, vb, vc),
                                            P.domaine_phi(va, vb, vc),
                                            P.codomaine_phi(va, vb, vc))


def test_inf_egal_phi_direction_A():
    """⊢ inf_egal_card(𝓕(B⊔C;A), 𝓕(B;A)×𝓕(C;A))  =  a^(b+c) ≤ a^b·a^c  (CLOS, DIRECTION A)."""
    va, vb, vc = var("A"), var("B"), var("C")
    t = P.inf_egal_phi()
    assert t.est_clos
    assert t.conclusion == inf_egal_card(P.domaine_phi(va, vb, vc),
                                        P.codomaine_phi(va, vb, vc))


# ── DIRECTION B (ψ) : tout SAUF l'injectivité ─────────────────────────────────
def test_K_recollement_structurel():
    """K = K_g∪K_h : K fonctionnel (copies disjointes) et dom K = B⊔C  (CLOS)."""
    va, vb, vc = var("A"), var("B"), var("C")
    assert P.K_fonctionnelle().est_clos
    td = P.K_domaine()
    assert td.est_clos
    K = P.K_psi(var("g"), var("h"), vb, vc)
    assert td.conclusion == egal(E.dom(K), somme_disjointe(vb, vc))


def test_K_dans_exposant():
    """{hyps gr g,h} ⊢ K ∈ A^(B⊔C)  (K⊂(B⊔C)×A via le pont + fonctionnel + domaine)."""
    t = P.K_dans_exposant()
    assert not t.est_clos and len(t.hypotheses) == 4


def test_psi_bien_definie():
    """{g∈𝓕(B;A), h∈𝓕(C;A)} ⊢ ψ(g,h) ∈ 𝓕(B⊔C;A)  (BIEN-DÉFINITION de ψ, CLOS-conditionnel)."""
    va, vb, vc = var("A"), var("B"), var("C")
    t = P.psi_dans_applications_sous_appartenance()
    hyps = {appartient(var("g"), E.applications(vb, va)),
            appartient(var("h"), E.applications(vc, va))}
    assert t.hypotheses == frozenset(hyps)


def test_W_psi_structurel():
    """W_ψ fonctionnel, dom W_ψ=𝓕(B;A)×𝓕(C;A), image⊂𝓕(B⊔C;A)  (3 conjoints CLOS)."""
    assert P.W_psi_fonctionnel().est_clos
    assert P.W_psi_domaine().est_clos
    assert P.W_psi_image_incluse().est_clos


# ── ASSEMBLEUR FINAL (Cantor–Bernstein) : la cible À UNE INJECTION près ────────
def test_assembleur_cantor_bernstein():
    """prop9_depuis_deux_injections(A, B) ⊢ cible_prop9_exp_somme dès que les DEUX
    inf_egal_card sont fournies.  Ici les deux directions sont SUPPOSÉES : on vérifie
    que l'assembleur atteint EXACTEMENT la cible (conclusion == cible_prop9_exp_somme)
    et que ses deux seules hypothèses sont les deux directions."""
    from bourbaki.logique import noyau_abrege as N
    va, vb, vc = var("A"), var("B"), var("C")
    dom = P.domaine_phi(va, vb, vc)
    cod = P.codomaine_phi(va, vb, vc)
    infA = N.assume(inf_egal_card(dom, cod))
    infB = N.assume(inf_egal_card(cod, dom))
    t = P.prop9_depuis_deux_injections(infA, infB, va, vb, vc)
    assert t.conclusion == cible_prop9_exp_somme(va, vb, vc)
    assert t.hypotheses == frozenset({inf_egal_card(dom, cod), inf_egal_card(cod, dom)})


def test_direction_A_est_une_hypothese_du_final():
    """La DIRECTION A (inf_egal_phi, CLOSE) DÉCHARGE l'une des deux hypothèses de
    l'assembleur : il ne resterait QUE la Direction B (ψ) à clore."""
    from bourbaki.logique import noyau_abrege as N
    va, vb, vc = var("A"), var("B"), var("C")
    dom = P.domaine_phi(va, vb, vc)
    cod = P.codomaine_phi(va, vb, vc)
    infA = P.inf_egal_phi()                         # CLOS : dom ≤ cod
    infB = N.assume(inf_egal_card(cod, dom))        # SUPPOSÉ : cod ≤ dom (Direction B)
    t = P.prop9_depuis_deux_injections(infA, infB, va, vb, vc)
    assert t.conclusion == cible_prop9_exp_somme(va, vb, vc)
    # une SEULE hypothèse restante : la Direction B
    assert t.hypotheses == frozenset({inf_egal_card(cod, dom)})
