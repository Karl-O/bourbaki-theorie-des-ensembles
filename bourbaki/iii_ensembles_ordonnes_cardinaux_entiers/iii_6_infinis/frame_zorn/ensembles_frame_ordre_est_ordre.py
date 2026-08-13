"""§III.6.3 — Théorème 2 (HESSENBERG, Zorn E.III.48) : Γ𝔉(E) est un ORDRE sur 𝔉(E).

DÉCHARGE l'une des deux hypothèses honnêtes de `frame_inductif_inconditionnel`
(`iii_6_infinis/frame_zorn/ensembles_frame_inductif_assemblage.py`, même dossier) : `est_ordre(Γ𝔉,𝔉)`.

L'ordre d'extension de Bourbaki sur le poset 𝔉 des couples-bijections est porté
au niveau des couples p=(S_p,φ_p) par :

    (p,q) ∈ Γ𝔉(E)  ⟺  ( p∈𝔉 et q∈𝔉 et pr₁(p)⊂pr₁(q) et pr₂(p)⊂pr₂(q) )

(= `frame_ordre_membre`, axiome définitionnel clos).  On en déduit que Γ𝔉 est un
ORDRE (E.III.1.1) : réflexif sur 𝔉, antisymétrique, transitif — car ⊂ l'est :

  • RÉFLEXIVITÉ : p∈𝔉 ⇒ (p,p)∈Γ𝔉  (pr₁(p)⊂pr₁(p), pr₂(p)⊂pr₂(p) par ⊂-réflexivité).
  • TRANSITIVITÉ : (p,q),(q,r)∈Γ𝔉 ⇒ (p,r)∈Γ𝔉  (⊂ transitive sur pr₁ et pr₂).
  • ANTISYMÉTRIE : (p,q),(q,p)∈Γ𝔉 ⇒ p=q.  pr₁(p)=pr₁(q) et pr₂(p)=pr₂(q) par
        ⊂-antisymétrie (A1) ; comme p,q∈𝔉 sont des COUPLES (p=(S_p,φ_p) via
        `frame_membre`), p=(pr₁p,pr₂p)=(pr₁q,pr₂q)=q (reconstruction + congruence).

RÉSULTAT : `frame_ordre_est_ordre(E)` ⊢ est_ordre(Γ𝔉(E), 𝔉(E)), CLOS (0 hyp).

INVARIANT : theorie_ensembles() reste = 22.  L'axiome de Γ𝔉 (et de 𝔉) vit dans
sa théorie DÉDIÉE ; rien postulé en plus.  Noyau INTACT.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import Terme, var, egal, et, appartient, inclus
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E

from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege import inclusion_reflexive
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    instancie, conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, inclusion_transitive,
)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
    symetrie, composer_egalites, congruence_terme,
)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import existe_elimination
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_theoremes import extensionnalite_appliquee
from bourbaki.ii_theorie_des_ensembles.ii_2_couples.ii_2_1_definition_couples.ensembles_projections import (
    projection_premiere, projection_seconde,
)

from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.hessenberg.coeur.ensembles_hessenberg_hard import frame_pair, frame_ordre, frame_membre
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.frame_zorn.ensembles_frame_ordre_axiome import frame_ordre_membre_t
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_relation import (
    reflexivite_sur, antisymetrie, transitivite_rel, est_ordre,
)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def _couple_dans_gamma(vE, t, u):
    """Formule « (t,u) ∈ Γ𝔉(E) »."""
    return appartient(E.couple(_t(t), _t(u)), frame_ordre(_t(vE)))


# ════════════════════════════════════════════════════════════════════════════
#  RÉFLEXIVITÉ — p∈𝔉 ⇒ (p,p)∈Γ𝔉.
# ════════════════════════════════════════════════════════════════════════════
def frame_ordre_reflexive(E_set="E", x="p"):
    """⊢ reflexivite_sur(Γ𝔉(E), 𝔉(E)).   = (∀p)(p∈𝔉 ⇒ (p,p)∈Γ𝔉).

    Si p∈𝔉 alors le corps de Γ𝔉 en (p,p) tient : p∈𝔉, p∈𝔉, pr₁(p)⊂pr₁(p),
    pr₂(p)⊂pr₂(p) (⊂ réflexive) ; donc (p,p)∈Γ𝔉 (sens ⇐ de frame_ordre_membre).
    Binder « p » ≠ x,y (liants internes de pr₁/pr₂) : aucune capture."""
    vE, vp = _t(E_set), var(x)
    Fr = frame_pair(vE)
    h = N.assume(appartient(vp, Fr))                       # p∈𝔉
    membre = frame_ordre_membre_t(vE, vp, vp)              # ((p,p)∈Γ𝔉) ⇔ corps
    pr1p, pr2p = E.pr1(vp), E.pr2(vp)
    corps = conjonction_intro(
        conjonction_intro(
            conjonction_intro(h, h),
            inclusion_reflexive_terme(pr1p)),
        inclusion_reflexive_terme(pr2p))
    pp_in = N.modus_ponens(corps, equivalence_arriere(membre))
    body = N.loi_deduction(appartient(vp, Fr), pp_in)      # p∈𝔉 ⇒ (p,p)∈Γ𝔉
    return N.generalisation(x, body)


def inclusion_reflexive_terme(t):
    """⊢ t ⊂ t pour un TERME t quelconque (instance close de la réflexivité de ⊂)."""
    # inclusion_reflexive(name) ⊢ x⊂x ; on le généralise et instancie au terme t.
    base = inclusion_reflexive("x")                        # ⊢ x⊂x
    return instancie(N.generalisation("x", base), _t(t))   # ⊢ t⊂t


# ════════════════════════════════════════════════════════════════════════════
#  TRANSITIVITÉ — (p,q),(q,r)∈Γ𝔉 ⇒ (p,r)∈Γ𝔉.
# ════════════════════════════════════════════════════════════════════════════
def frame_ordre_transitive(E_set="E", x="p", y="q", z="r"):
    """⊢ transitivite_rel(Γ𝔉(E)).   = (∀x∀y∀z)(((x,y)∈Γ𝔉 et (y,z)∈Γ𝔉) ⇒ (x,z)∈Γ𝔉).

    Des deux corps : p∈𝔉, r∈𝔉, pr₁p⊂pr₁q⊂pr₁r (⊂ trans), pr₂p⊂pr₂q⊂pr₂r ; d'où
    le corps en (p,r) et (p,r)∈Γ𝔉 par frame_ordre_membre (sens ⇐)."""
    vE = _t(E_set)
    vp, vq, vr = var(x), var(y), var(z)
    hyp = et(_couple_dans_gamma(vE, vp, vq), _couple_dans_gamma(vE, vq, vr))
    h = N.assume(hyp)
    mem_pq = frame_ordre_membre_t(vE, vp, vq)
    mem_qr = frame_ordre_membre_t(vE, vq, vr)
    mem_pr = frame_ordre_membre_t(vE, vp, vr)
    corps_pq = N.modus_ponens(conjonction_elim_gauche(h), equivalence_avant(mem_pq))
    corps_qr = N.modus_ponens(conjonction_elim_droite(h), equivalence_avant(mem_qr))
    # extraire les conjoints : corps = ((p∈𝔉 et q∈𝔉) et pr₁p⊂pr₁q) et pr₂p⊂pr₂q
    p_in = conjonction_elim_gauche(conjonction_elim_gauche(conjonction_elim_gauche(corps_pq)))  # p∈𝔉
    r_in = conjonction_elim_droite(conjonction_elim_gauche(conjonction_elim_gauche(corps_qr)))  # r∈𝔉
    inc1_pq = conjonction_elim_droite(conjonction_elim_gauche(corps_pq))   # pr₁p⊂pr₁q
    inc1_qr = conjonction_elim_droite(conjonction_elim_gauche(corps_qr))   # pr₁q⊂pr₁r
    inc2_pq = conjonction_elim_droite(corps_pq)                            # pr₂p⊂pr₂q
    inc2_qr = conjonction_elim_droite(corps_qr)                            # pr₂q⊂pr₂r
    # binders p,q,r ≠ x,y (binders internes de pr₁/pr₂) ⇒ aucune capture : pr_i = E.pr_i(v)
    pr1p, pr1q, pr1r = E.pr1(vp), E.pr1(vq), E.pr1(vr)
    pr2p, pr2q, pr2r = E.pr2(vp), E.pr2(vq), E.pr2(vr)
    # transitivité de ⊂
    inc1_pr = _inclusion_transitive_termes(pr1p, pr1q, pr1r, inc1_pq, inc1_qr)  # pr₁p⊂pr₁r
    inc2_pr = _inclusion_transitive_termes(pr2p, pr2q, pr2r, inc2_pq, inc2_qr)  # pr₂p⊂pr₂r
    corps_pr = conjonction_intro(
        conjonction_intro(conjonction_intro(p_in, r_in), inc1_pr),
        inc2_pr)
    pr_in = N.modus_ponens(corps_pr, equivalence_arriere(mem_pr))
    body = N.loi_deduction(hyp, pr_in)
    return N.generalisation(x, N.generalisation(y, N.generalisation(z, body)))


def _inclusion_transitive_termes(a, b, c, inc_ab, inc_bc):
    """{a⊂b, b⊂c} ⊢ a⊂c  pour des TERMES a,b,c (transitivité de ⊂ instanciée)."""
    va, vb, vc = _t(a), _t(b), _t(c)
    base = inclusion_transitive("a", "b", "c")            # ((a⊂b et b⊂c)) ⇒ a⊂c
    gen = N.generalisation("a", N.generalisation("b", N.generalisation("c", base)))
    impl_t = instancie(instancie(instancie(gen, va), vb), vc)  # ((a⊂b et b⊂c)) ⇒ a⊂c
    return N.modus_ponens(conjonction_intro(inc_ab, inc_bc), impl_t)


# ════════════════════════════════════════════════════════════════════════════
#  RECONSTRUCTION — { p∈𝔉(E) } ⊢ p = (pr₁p, pr₂p).
#  (p∈𝔉 ⇒ ∃S∃φ(p=(S,φ) et …) ; dans le témoin, pr₁p=S, pr₂p=φ ⇒ p=(pr₁p,pr₂p).)
# ════════════════════════════════════════════════════════════════════════════
def _frame_reconstruction(E_set, p):
    """{ p∈𝔉(E) } ⊢ p = (pr₁(p), pr₂(p)).   (p∈𝔉 est un couple : reconstruction.)"""
    vE, vp = _t(E_set), _t(p)
    Fr = frame_pair(vE)
    pr1p, pr2p = E.pr1(vp), E.pr2(vp)
    cible = egal(vp, E.couple(pr1p, pr2p))
    # p∈𝔉 ⇒ (∃S)(∃φ)( p=(S,φ) et S⊂E et S infini et φ:S×S→S bij )
    decl = N.modus_ponens(N.assume(appartient(vp, Fr)),
                          equivalence_avant(_frame_membre_t(vE, vp)))  # (∃S)(∃φ)(…)
    exS = decl.conclusion                                  # (∃S)(∃φ)(…)
    nS = exS.lieur                                         # "S"
    bodyS = exS.sous[0]                                    # (∃φ)(…)
    nphi = bodyS.lieur                                     # "phi"
    bodyphi = bodyS.sous[0]                                # ( ((p=(S,φ) et S⊂E) et S∞) et φ bij )

    def inner(b):
        # b = (((p=(S,φ) et S⊂E) et S∞) et φ:S×S→S bij)
        hh = N.assume(b)
        p_eq = conjonction_elim_gauche(conjonction_elim_gauche(conjonction_elim_gauche(hh)))  # p=(S,φ)
        vS, vphi = var(nS), var(nphi)
        Scpl = E.couple(vS, vphi)
        # pr₁p = pr₁((S,φ)) = S
        cong1 = N.modus_ponens(p_eq, congruence_terme(vp, Scpl, E.pr1(var("w"))))   # pr₁p=pr₁((S,φ))
        pr1_eq_S = composer_egalites(cong1, projection_premiere(nS, nphi))          # pr₁p=S
        cong2 = N.modus_ponens(p_eq, congruence_terme(vp, Scpl, E.pr2(var("w"))))   # pr₂p=pr₂((S,φ))
        pr2_eq_phi = composer_egalites(cong2, projection_seconde(nS, nphi))         # pr₂p=φ
        # (pr₁p,pr₂p) = (S,pr₂p) = (S,φ) = p
        c1 = N.modus_ponens(pr1_eq_S, congruence_terme(pr1p, vS, E.couple(var("w"), pr2p)))  # (pr₁p,pr₂p)=(S,pr₂p)
        c2 = N.modus_ponens(pr2_eq_phi, congruence_terme(pr2p, vphi, E.couple(vS, var("w"))))  # (S,pr₂p)=(S,φ)
        pr_eq_Scpl = composer_egalites(c1, c2)             # (pr₁p,pr₂p)=(S,φ)
        Scpl_eq_pr = N.modus_ponens(pr_eq_Scpl, symetrie(E.couple(pr1p, pr2p), Scpl))  # (S,φ)=(pr₁p,pr₂p)
        p_eq_pr = composer_egalites(p_eq, Scpl_eq_pr)      # p=(S,φ)=(pr₁p,pr₂p)
        return N.loi_deduction(b, p_eq_pr)                 # b ⇒ p=(pr₁p,pr₂p)

    imp_phi = existe_elimination(inner(bodyphi), nphi)     # (∃φ)(…) ⇒ cible
    body_phi_to_cible = N.modus_ponens(N.assume(bodyS), imp_phi)  # under (∃φ)… ⊢ cible
    imp_S = existe_elimination(N.loi_deduction(bodyS, body_phi_to_cible), nS)  # (∃S)(∃φ)(…) ⇒ cible
    return N.modus_ponens(decl, imp_S)                     # { p∈𝔉 } ⊢ p=(pr₁p,pr₂p)


def _frame_membre_t(vE, vp):
    """Version TERME de frame_membre : ⊢ (p∈𝔉(E)) ⇔ corps_frame, instancié aux termes."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.hessenberg.coeur.ensembles_hessenberg_hard import theorie_frame, axiome_frame
    ax = N.axiome(theorie_frame(), axiome_frame())         # (∀E)(∀p)( p∈𝔉(E) ⇔ corps )
    return instancie(instancie(ax, _t(vE)), _t(vp))


# ════════════════════════════════════════════════════════════════════════════
#  ANTISYMÉTRIE — (p,q),(q,p)∈Γ𝔉 ⇒ p=q.
# ════════════════════════════════════════════════════════════════════════════
def frame_ordre_antisymetrique(E_set="E", x="p", y="q"):
    """⊢ antisymetrie(Γ𝔉(E)).   = (∀x∀y)(((x,y)∈Γ𝔉 et (y,x)∈Γ𝔉) ⇒ x=y).

    Des deux corps : pr₁p⊂pr₁q et pr₁q⊂pr₁p ⇒ pr₁p=pr₁q (A1) ; idem pr₂p=pr₂q.
    Comme p,q∈𝔉 sont des couples, p=(pr₁p,pr₂p)=(pr₁q,pr₂q)=q (reconstruction)."""
    vE = _t(E_set)
    vp, vq = var(x), var(y)
    hyp = et(_couple_dans_gamma(vE, vp, vq), _couple_dans_gamma(vE, vq, vp))
    h = N.assume(hyp)
    corps_pq = N.modus_ponens(conjonction_elim_gauche(h),
                              equivalence_avant(frame_ordre_membre_t(vE, vp, vq)))
    corps_qp = N.modus_ponens(conjonction_elim_droite(h),
                              equivalence_avant(frame_ordre_membre_t(vE, vq, vp)))
    p_in = conjonction_elim_gauche(conjonction_elim_gauche(conjonction_elim_gauche(corps_pq)))  # p∈𝔉
    q_in = conjonction_elim_droite(conjonction_elim_gauche(conjonction_elim_gauche(corps_pq)))  # q∈𝔉
    inc1_pq = conjonction_elim_droite(conjonction_elim_gauche(corps_pq))   # pr₁p⊂pr₁q
    inc1_qp = conjonction_elim_droite(conjonction_elim_gauche(corps_qp))   # pr₁q⊂pr₁p
    inc2_pq = conjonction_elim_droite(corps_pq)                            # pr₂p⊂pr₂q
    inc2_qp = conjonction_elim_droite(corps_qp)                            # pr₂q⊂pr₂p
    pr1p, pr1q = E.pr1(vp), E.pr1(vq)
    pr2p, pr2q = E.pr2(vp), E.pr2(vq)
    # antisymétrie de ⊂ (A1)
    pr1_eq = N.modus_ponens(conjonction_intro(inc1_pq, inc1_qp),
                            extensionnalite_appliquee(pr1p, pr1q))         # pr₁p=pr₁q
    pr2_eq = N.modus_ponens(conjonction_intro(inc2_pq, inc2_qp),
                            extensionnalite_appliquee(pr2p, pr2q))         # pr₂p=pr₂q
    # reconstructions (déchargent p∈𝔉, q∈𝔉)
    p_recon = N.modus_ponens(p_in, N.loi_deduction(appartient(vp, frame_pair(vE)),
                                                   _frame_reconstruction(vE, vp)))  # p=(pr₁p,pr₂p)
    q_recon = N.modus_ponens(q_in, N.loi_deduction(appartient(vq, frame_pair(vE)),
                                                   _frame_reconstruction(vE, vq)))  # q=(pr₁q,pr₂q)
    # (pr₁p,pr₂p) = (pr₁q,pr₂p) = (pr₁q,pr₂q)
    c1 = N.modus_ponens(pr1_eq, congruence_terme(pr1p, pr1q, E.couple(var("w"), pr2p)))  # (pr₁p,pr₂p)=(pr₁q,pr₂p)
    c2 = N.modus_ponens(pr2_eq, congruence_terme(pr2p, pr2q, E.couple(pr1q, var("w"))))  # (pr₁q,pr₂p)=(pr₁q,pr₂q)
    prp_eq_prq = composer_egalites(c1, c2)                 # (pr₁p,pr₂p)=(pr₁q,pr₂q)
    # p = (pr₁p,pr₂p) = (pr₁q,pr₂q) = q
    p_eq_prq = composer_egalites(p_recon, prp_eq_prq)      # p=(pr₁q,pr₂q)
    q_recon_sym = N.modus_ponens(q_recon, symetrie(vq, E.couple(pr1q, pr2q)))  # (pr₁q,pr₂q)=q
    p_eq_q = composer_egalites(p_eq_prq, q_recon_sym)      # p=q
    body = N.loi_deduction(hyp, p_eq_q)
    return N.generalisation(x, N.generalisation(y, body))


# ════════════════════════════════════════════════════════════════════════════
#  ASSEMBLAGE — Γ𝔉 est un ORDRE sur 𝔉.
# ════════════════════════════════════════════════════════════════════════════
# @livre Ch.III §6.3 Demo.2 | E III.48 L.21-23 | PDF p.151  (« Ordonnons l'ensemble 𝔐 par la relation… » : Γ𝔐 est bien un ordre sur 𝔐)
def frame_ordre_est_ordre(E_set="E", x="p", y="q", z="r"):
    """⊢ est_ordre(Γ𝔉(E), 𝔉(E)).   L'ordre d'extension est un ordre sur 𝔉 (E.III.48).

    Décharge l'hypothèse `est_ordre(Γ𝔉,𝔉)` de `frame_inductif_inconditionnel`.
    CLOS, 0 hyp : conjonction de réflexivité, antisymétrie, transitivité."""
    return conjonction_intro(
        conjonction_intro(frame_ordre_reflexive(E_set, x),
                          frame_ordre_antisymetrique(E_set, x, y)),
        frame_ordre_transitive(E_set, x, y, z))


__all__ = [
    "frame_ordre_reflexive",
    "frame_ordre_antisymetrique",
    "frame_ordre_transitive",
    "frame_ordre_est_ordre",
]
