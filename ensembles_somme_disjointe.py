"""§II.4.8 / §III.3.3 — Somme disjointe BINAIRE A ⊔ B (fondation de la somme
cardinale, miroir du produit A×B).

Bourbaki (E.II.4.8, Déf. 8 ; E.III.3.3, Déf. 3) code la somme d'une famille
(X_ι)_{ι∈I} par la réunion des « copies marquées » X_ι × {ι}.  Spécialisé à
deux ensembles, avec les indices ι = 0, 1 (et, fidèle à E.III.3.1, 0 = ∅,
1 = {∅}), la SOMME DISJOINTE binaire est

        A ⊔ B := (A × {0}) ∪ (B × {1})       avec 0 = ∅,  1 = {∅}.

C'est un TERME DÉRIVÉ des termes déjà présents (produit, réunion, singleton,
VIDE) — il n'introduit donc AUCUN axiome nouveau : sa caractérisation de
membership découle des axiomes EXISTANTS (AXIOME_REUNION + AXIOME_PRODUIT +
AXIOME_PAIRE), ce qui est plus sûr (rien à postuler) et tout aussi fidèle que la
construction de Bourbaki.  La somme cardinale est alors  a + b := Card(A ⊔ B)
(miroir famille : ensembles_cardinaux.somme_cardinale).

THÉORÈMES CERTIFIÉS (chacun testé, cf. test_somme_disjointe.py) :
  • somme_disjointe_reunion     (clos) — A⊔B = (A×{0}) ∪ (B×{1})  (déf., forme) ;
  • membre_somme_reunion        (clos) — z∈A⊔B ⇔ (z∈A×{0}) ∨ (z∈B×{1}) ;
  • injection_gauche_dans_somme (clos) — (u∈A) ⇒ (u,0) ∈ A⊔B ;
  • injection_droite_dans_somme (clos) — (v∈B) ⇒ (v,1) ∈ A⊔B ;
  • membre_somme_caracterise    (clos) — z∈A⊔B ⇔ ((∃u)(u∈A et z=(u,0))
                                          ou (∃v)(v∈B et z=(v,1))).

L'INVARIANCE de la somme par équipotence (miroir de eq_produit_invariant) est
REPORTÉE pour un round suivant : elle demande la bijection F⊔G assemblée à partir
des paliers fonctionnel/domaine/injectif/image, sur la même machinerie liants a,b
que le produit (voir ensembles_produit_equipotence).
"""
from __future__ import annotations

from formule import (Terme, var, egal, et, ou, non, impl, appartient, existe, subst_f)
import noyau_abrege as N
import ensembles_abrege as E
from tactiques_abrege import syllogisme, antecedent_consequent
from tactiques_abrege2 import (conjonction_intro, conjonction_elim_gauche,
                               conjonction_elim_droite, equivalence_avant,
                               equivalence_arriere, equivalence_transitivite,
                               instancie, cas)
from tactiques_abrege_quantif import existe_elimination
from tactiques_abrege_egalite import composer_egalites, congruence_terme
from ensembles_produit import couple_dans_produit_ssi


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# ── Les marqueurs 0 = ∅, 1 = {∅} (E.III.3.1) ─────────────────────────────────
ZERO = E.VIDE                       # 0 = Card(∅) = ∅
UN = E.singleton(E.VIDE)            # 1 = Card({∅}) = {∅}


# ── Outils propositionnels sur le « ou » (congruence / idempotence) ──────────
def _ou_mono(thm_imp1, thm_imp2):
    """⊢ (P⇒P') et ⊢ (Q⇒Q') ⟹ ⊢ ((P ou Q) ⇒ (P' ou Q')).  (monotonie du « ou ».)"""
    P, Pp = antecedent_consequent(thm_imp1.conclusion)
    Q, Qp = antecedent_consequent(thm_imp2.conclusion)
    h = N.assume(ou(P, Q))
    # P ⇒ P' ⇒ (P' ou Q')   (S2 : P'⇒P'∨Q')
    brP = N.loi_deduction(P, N.modus_ponens(N.modus_ponens(N.assume(P), thm_imp1),
                                            N.s2(Pp, Qp)))
    # Q ⇒ Q' ⇒ (P' ou Q')   (S3 : Q'∨P' ⇒ P'∨Q', via S2 puis S3)
    brQ = N.loi_deduction(Q, N.modus_ponens(N.modus_ponens(
        N.modus_ponens(N.assume(Q), thm_imp2), N.s2(Qp, Pp)), N.s3(Qp, Pp)))
    return N.loi_deduction(ou(P, Q), cas(h, brP, brQ))


def _ou_congruence(thm_pq, thm_rs):
    """⊢ (P⇔P') et ⊢ (Q⇔Q') ⟹ ⊢ ((P ou Q) ⇔ (P' ou Q')).  (congruence du « ou ».)"""
    av = _ou_mono(equivalence_avant(thm_pq), equivalence_avant(thm_rs))      # (P∨Q)⇒(P'∨Q')
    ar = _ou_mono(equivalence_arriere(thm_pq), equivalence_arriere(thm_rs))  # (P'∨Q')⇒(P∨Q)
    return conjonction_intro(av, ar)


def _ou_idem(thm_or, p):
    """⊢ (P ou P), P  ⟹  ⊢ P.   (idempotence du « ou ».)"""
    pp = N.assume(p)
    return N.modus_ponens(thm_or, N.loi_deduction(ou(p, p),
        cas(N.assume(ou(p, p)), N.loi_deduction(p, pp), N.loi_deduction(p, pp))))


# ── Le terme somme disjointe binaire (dérivé) ─────────────────────────────────
def somme_disjointe(a, b):
    """A ⊔ B := (A × {0}) ∪ (B × {1})   (somme disjointe binaire, E.II.4.8 / III.3.3).

    Terme DÉRIVÉ : réunion des deux copies marquées A×{∅} et B×{{∅}}."""
    va, vb = _t(a), _t(b)
    return E.reunion(E.produit(va, E.singleton(ZERO)),
                     E.produit(vb, E.singleton(UN)))


def somme_disjointe_reunion(a="A", b="B"):
    """⊢ (A⊔B) = ((A×{0}) ∪ (B×{1})).   (la déf. est littéralement cette réunion ;
    réflexivité — sert d'ancrage de forme, conclusion EXACTE, clos.)"""
    va, vb = _t(a), _t(b)
    return N.reflexivite(somme_disjointe(va, vb))


# ── Membership : décomposition par la réunion (AXIOME_REUNION) ────────────────
def membre_somme_reunion(a="A", b="B", z="z"):
    """⊢ (z ∈ A⊔B) ⇔ ((z ∈ A×{0}) ou (z ∈ B×{1})).   (z : nom ou terme sans x,y.)

    Application directe d'AXIOME_REUNION au terme A⊔B = (A×{0}) ∪ (B×{1})."""
    va, vb = _t(a), _t(b)
    vz = _t(z)
    GA = E.produit(va, E.singleton(ZERO))      # A×{0}
    GB = E.produit(vb, E.singleton(UN))        # B×{1}
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_REUNION)
    return instancie(instancie(instancie(ax, GA), GB), vz)


# ── 0∈{0}, 1∈{1} (singleton trivial) ──────────────────────────────────────────
def _dans_singleton(c):
    """⊢ c ∈ {c}.   (c termes ; c∈{c,c} ⇔ (c=c ou c=c), témoin c=c.)"""
    vc = _t(c)
    ax_p = N.axiome(E.theorie_ensembles(), E.AXIOME_PAIRE)
    car = instancie(instancie(instancie(ax_p, vc), vc), vc)    # c∈{c,c} ⇔ (c=c ou c=c)
    return N.modus_ponens(
        N.modus_ponens(N.reflexivite(vc), N.s2(egal(vc, vc), egal(vc, vc))),
        equivalence_arriere(car))


# ── Injections canoniques : u↦(u,0), v↦(v,1) ──────────────────────────────────
def injection_gauche_dans_somme(u="u", a="A", b="B"):
    """⊢ (u ∈ A) ⇒ ((u, 0) ∈ A⊔B).   (injection canonique de gauche ; clos.)"""
    vu, va, vb = _t(u), _t(a), _t(b)
    GA = E.produit(va, E.singleton(ZERO))
    GB = E.produit(vb, E.singleton(UN))
    cpl = E.couple(vu, ZERO)
    hu = N.assume(appartient(vu, va))                          # u∈A
    in_GA = N.modus_ponens(conjonction_intro(hu, _dans_singleton(ZERO)),
        equivalence_arriere(couple_dans_produit_ssi(vu, ZERO, va, E.singleton(ZERO))))  # (u,0)∈A×{0}
    in_somme = N.modus_ponens(
        N.modus_ponens(in_GA, N.s2(appartient(cpl, GA), appartient(cpl, GB))),
        equivalence_arriere(membre_somme_reunion(a, b, cpl)))  # (u,0)∈A⊔B
    return N.loi_deduction(appartient(vu, va), in_somme)


def injection_droite_dans_somme(v="v", a="A", b="B"):
    """⊢ (v ∈ B) ⇒ ((v, 1) ∈ A⊔B).   (injection canonique de droite ; clos.)"""
    vv, va, vb = _t(v), _t(a), _t(b)
    GA = E.produit(va, E.singleton(ZERO))
    GB = E.produit(vb, E.singleton(UN))
    cpl = E.couple(vv, UN)
    hv = N.assume(appartient(vv, vb))                          # v∈B
    in_GB = N.modus_ponens(conjonction_intro(hv, _dans_singleton(UN)),
        equivalence_arriere(couple_dans_produit_ssi(vv, UN, vb, E.singleton(UN))))  # (v,1)∈B×{1}
    # (v,1)∈B×{1} ⇒ ((v,1)∈A×{0} ou (v,1)∈B×{1}) : S2 donne (GB ou GA), S3 swap
    in_GAB = N.modus_ponens(N.modus_ponens(in_GB,
                 N.s2(appartient(cpl, GB), appartient(cpl, GA))),
             N.s3(appartient(cpl, GB), appartient(cpl, GA)))
    in_somme = N.modus_ponens(in_GAB,
        equivalence_arriere(membre_somme_reunion(a, b, cpl)))  # (v,1)∈A⊔B
    return N.loi_deduction(appartient(vv, vb), in_somme)


# ── z∈A×{c} ⇔ (∃u)(u∈A et z=(u,c)) ────────────────────────────────────────────
def _membre_produit_singleton(a, c, z, u="u"):
    """⊢ (z ∈ A×{c}) ⇔ (∃u)(u∈A et z=(u,c)).   (la 2ᵉ coordonnée est forcée = c.)
    a,c,z termes ; liant u (≠ p,q,w)."""
    va, vc, vz = _t(a), _t(c), _t(z)
    vu, vp, vq = var(u), var("p"), var("q")
    Sc = E.singleton(vc)
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_PRODUIT)
    inst = instancie(instancie(instancie(ax, va), Sc), vz)     # z∈A×{c} ⇔ (∃p)(∃q)body
    body = et(et(egal(vz, E.couple(vp, vq)), appartient(vp, va)), appartient(vq, Sc))
    ax_p = N.axiome(E.theorie_ensembles(), E.AXIOME_PAIRE)
    cible = et(appartient(vu, va), egal(vz, E.couple(vu, vc)))  # u∈A et z=(u,c)

    # ── ⇒ : (∃p)(∃q)body ⇒ (∃u)cible ─────────────────────────────────────────
    hb = N.assume(body)
    z_pq = conjonction_elim_gauche(conjonction_elim_gauche(hb))  # z=(p,q)
    p_in = conjonction_elim_droite(conjonction_elim_gauche(hb))  # p∈A
    q_in = conjonction_elim_droite(hb)                           # q∈{c}
    car_q = instancie(instancie(instancie(ax_p, vc), vc), vq)    # q∈{c,c} ⇔ (q=c ou q=c)
    q_eq_c = _ou_idem(N.modus_ponens(q_in, equivalence_avant(car_q)), egal(vq, vc))  # q=c
    # z=(p,q)=(p,c)
    pq_eq_pc = N.modus_ponens(q_eq_c, congruence_terme(vq, vc, E.couple(vp, var("w"))))
    z_pc = composer_egalites(z_pq, pq_eq_pc)                     # z=(p,c)
    temoin = conjonction_intro(p_in, z_pc)                       # p∈A et z=(p,c)
    ex = N.modus_ponens(temoin, N.s5(cible, vp, u))             # (∃u)cible (témoin p)
    avant = existe_elimination(existe_elimination(
        N.loi_deduction(body, ex), "q"), "p")                   # (∃p)(∃q)body ⇒ (∃u)cible

    # ── ⇐ : (∃u)cible ⇒ (∃p)(∃q)body ─────────────────────────────────────────
    hc = N.assume(cible)
    u_in = conjonction_elim_gauche(hc)                          # u∈A
    z_uc = conjonction_elim_droite(hc)                          # z=(u,c)
    c_in = _dans_singleton(vc)                                  # c∈{c}
    temoin2 = conjonction_intro(conjonction_intro(z_uc, u_in), c_in)  # z=(u,c) et u∈A et c∈{c}
    body_uc = subst_f(vu, "p", body)                           # (p:=u) body  (libre q)
    qq = N.modus_ponens(temoin2, N.s5(body_uc, vc, "q"))       # (∃q)(p:=u)body
    pp = N.modus_ponens(qq, N.s5(existe("q", body), vu, "p"))  # (∃p)(∃q)body
    arriere = existe_elimination(N.loi_deduction(cible, pp), u)  # (∃u)cible ⇒ (∃p)(∃q)body

    return equivalence_transitivite(inst, conjonction_intro(avant, arriere))


# ── Caractérisation complète de l'appartenance à A⊔B ──────────────────────────
def membre_somme_caracterise(a="A", b="B", z="z"):
    """⊢ (z ∈ A⊔B) ⇔ ((∃u)(u∈A et z=(u,0)) ou (∃v)(v∈B et z=(v,1))).

    Réunion (membre_somme_reunion) ∘ caractérisation de chaque appartenance au
    produit-par-singleton (_membre_produit_singleton) ∘ congruence du « ou »."""
    va, vb = _t(a), _t(b)
    vz = _t(z)
    reun = membre_somme_reunion(a, b, vz)                       # z∈A⊔B ⇔ (z∈A×{0} ou z∈B×{1})
    eqA = _membre_produit_singleton(va, ZERO, vz, "u")          # z∈A×{0} ⇔ (∃u)(u∈A et z=(u,0))
    eqB = _membre_produit_singleton(vb, UN, vz, "v")            # z∈B×{1} ⇔ (∃v)(v∈B et z=(v,1))
    ou_cong = _ou_congruence(eqA, eqB)
    return equivalence_transitivite(reun, ou_cong)


# ── Somme cardinale binaire : a + b := Card(A ⊔ B) (E.III.3.3, Déf. 3) ─────────
def somme_cardinale_binaire(a, b):
    """a + b := Card(A ⊔ B)   (somme cardinale de deux cardinaux, E.III.3.3, Déf. 3).

    « Pour deux cardinaux a et b on note a + b leur somme. »  Codée par le
    cardinal de la somme disjointe binaire — miroir exact du produit cardinal
    binaire ab := Card(A×B).  Sa BIEN-DÉFINITION (Card(A⊔B)=Card(A₁⊔B₁) dès que
    Eq(A,A₁) et Eq(B,B₁)) suit de l'invariance de la somme par équipotence
    (REPORTÉE), via proposition_1_cardinaux."""
    from ensembles_cardinaux import cardinal
    return cardinal(somme_disjointe(_t(a), _t(b)))


__all__ = ["somme_disjointe", "ZERO", "UN", "somme_disjointe_reunion",
           "membre_somme_reunion", "injection_gauche_dans_somme",
           "injection_droite_dans_somme", "membre_somme_caracterise",
           "somme_cardinale_binaire"]
