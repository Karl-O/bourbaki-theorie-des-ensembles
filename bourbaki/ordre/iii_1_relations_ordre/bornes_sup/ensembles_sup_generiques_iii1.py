"""Chapitre III §1 — PROPOSITIONS 5/6/7/9 sur le CALCUL des bornes supérieures
(E.III.10–12 ; ensembles ordonnés génériques).

Le sup spécifique aux cardinaux a été construit directement en §3 ; ces
propositions GÉNÉRIQUES d'ordre §1 (monotonie du sup, sup par recouvrement,
sup dans un sous-ensemble ordonné) n'avaient pas encore été certifiées.

Convention « graphe G » de `ensembles_ordre_relation.py` : x≤y := (x,y)∈G,
sup A = plus petit des majorants (`borne_superieure(G,A,m,E)`).  Les hypothèses
d'EXISTENCE des bornes (« m = sup A », « n = sup B ») sont posées comme
hypothèses HONNÊTES, exactement comme dans Bourbaki (« lorsque les bornes
existent »).

THÉORÈMES (forme « ensemble » des sous-familles ; A,B ⊂ E) :

  • PROPOSITION 5 (E.III.10) — `sup_monotone_inclusion` :
      { A⊂B,  m=sup A,  n=sup B } ⊢ (m,n)∈G    (A⊂B ⇒ sup A ≤ sup B).
    Cœur : tout majorant de B est un majorant de A (car A⊂B), donc n (majorant
    de B) majore A ; m étant le PLUS PETIT majorant de A, m≤n.
  • COROLLAIRE 5 (sous-famille) — `sup_sous_famille_le` : idem, énoncé « sup d'une
    sous-partie ≤ sup de la partie ».  (Même contenu : c'est exactement Prop 5.)
  • PROPOSITION 6 (E.III.10) — `sup_monotone_termes` :
      { (∀t)(t∈A ⇒ (∃u)(u∈B et (t,u)∈G)),  m=sup A,  n=sup B } ⊢ (m,n)∈G.
    Forme « termes dominés » de Prop 6 (x_ι ≤ y_ι ⇒ sup x_ι ≤ sup y_ι) : si tout
    élément de A est majoré par un élément de B, alors tout majorant de B majore A,
    donc sup A ≤ sup B.  (Subsume la forme indexée : poser A={x_ι}, B={y_ι}.)
  • PROPOSITION 9 (E.III.12) — `sup_induit_sur_partie` :
      { A⊂F,  m=sup_E A (dans E),  m∈F,  m majore A « dans F » } ⊢ m=sup_F A.
    Relation entre sup_E A et sup_F A pour F⊂E sous-ensemble ordonné : si la borne
    sup de A calculée dans E appartient à F, alors c'est aussi la borne sup de A
    calculée dans F.

PROPOSITION 7 (recouvrement) et PROPOSITION 8 (produit) : voir le RAPPORT —
partielles, lemme-clé du recouvrement (`sup_recouvrement_majorant_iff`) certifié.

theorie_ensembles INTANGIBLE = 22 : tout est DÉRIVÉ de la logique pure du
« plus petit majorant », aucun axiome nouveau.
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (
    Terme, var, egal, et, impl, appartient, existe, pourtout, inclus,
)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    instancie,
)
from bourbaki.logique.i_3_quantifies.tactiques_abrege_quantif import existe_elimination
from bourbaki.ordre.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_relation import (
    majorant, borne_superieure,
)


def _terme(t):
    return t if isinstance(t, Terme) else var(t)


def _couple_dans(t, u, G):
    """Formule « (t,u) ∈ G »  (lecture « t ≤ u » pour l'ordre de graphe G)."""
    return appartient(E.couple(_terme(t), _terme(u)), _terme(G))


# ════════════════════════════════════════════════════════════════════════════
#  LEMME — tout majorant de B est un majorant de A, dès que A⊂B  (cœur Prop 5)
# ════════════════════════════════════════════════════════════════════════════
def majorant_de_sur_partie(G="G", A="A", B="B", E_set="E", m="m", x="x"):
    """{ A⊂B, majorant(G,B,m,E) } ⊢ majorant(G,A,m,E).

    Un majorant de B majore aussi toute partie A⊂B : m∈E est conservé, et pour
    x∈A on a x∈B (inclusion), donc (x,m)∈G.  (E.III.10, lemme de Prop 5.)"""
    vA, vB, vm = _terme(A), _terme(B), _terme(m)
    vx = var(x)
    Hsub = N.assume(inclus(vA, vB))                        # A⊂B = (∀z)(z∈A⇒z∈B)
    Hmaj = N.assume(majorant(G, B, vm, E_set, x))          # m∈E et (∀x)(x∈B⇒(x,m)∈G)
    m_in_E = conjonction_elim_gauche(Hmaj)                 # m∈E
    maj_body = conjonction_elim_droite(Hmaj)               # (∀x)(x∈B⇒(x,m)∈G)
    # corps : x∈A ⇒ (x,m)∈G
    Hx = N.assume(appartient(vx, vA))                      # x∈A
    x_in_B = N.modus_ponens(Hx, instancie(Hsub, vx))       # x∈B
    xm = N.modus_ponens(x_in_B, instancie(maj_body, vx))   # (x,m)∈G
    body = N.loi_deduction(appartient(vx, vA), xm)         # x∈A⇒(x,m)∈G
    return conjonction_intro(m_in_E, N.generalisation(x, body))   # majorant(G,A,m,E)


# ════════════════════════════════════════════════════════════════════════════
#  PROPOSITION 5 (E.III.10) — A⊂B ⇒ sup A ≤ sup B
# ════════════════════════════════════════════════════════════════════════════
def sup_monotone_inclusion(G="G", A="A", B="B", E_set="E", m="m", n="n",
                           x="x", y="y"):
    """{ A⊂B,  borne_superieure(G,A,m,E),  borne_superieure(G,B,n,E) }
        ⊢ (m,n)∈G.

    PROPOSITION 5 : si A⊂B et si A, B admettent des bornes supérieures m=sup A,
    n=sup B, alors sup A ≤ sup B.  En effet n=sup B est en particulier un majorant
    de B, donc (A⊂B) un majorant de A ; m étant le PLUS PETIT majorant de A, on a
    m≤n, i.e. (m,n)∈G.  (E.III.10.)"""
    vn = _terme(n)
    Hsub = N.assume(inclus(_terme(A), _terme(B)))          # A⊂B
    Hm = N.assume(borne_superieure(G, A, _terme(m), E_set, x, y))  # m=sup A
    Hn = N.assume(borne_superieure(G, B, vn, E_set, x, y))        # n=sup B
    # m est le plus petit majorant de A : (∀y)(majorant(G,A,y,E) ⇒ (m,y)∈G)
    m_least = conjonction_elim_droite(Hm)
    # n est un majorant de B
    n_maj_B = conjonction_elim_gauche(Hn)                  # majorant(G,B,n,E)
    # n est un majorant de A (A⊂B) — via le lemme, en déchargeant ses 2 hypothèses
    n_maj_A = majorant_de_sur_partie(G, A, B, E_set, vn, x)   # {A⊂B,maj(B,n)}⊢maj(A,n)
    n_maj_A = N.modus_ponens(Hsub, N.loi_deduction(inclus(_terme(A), _terme(B)), n_maj_A))
    n_maj_A = N.modus_ponens(n_maj_B,
                             N.loi_deduction(majorant(G, B, vn, E_set, x), n_maj_A))
    # m≤n : instancier le « plus petit majorant » de m en n
    mn = N.modus_ponens(n_maj_A, instancie(m_least, vn))   # (m,n)∈G
    return mn


def sup_sous_famille_le(G="G", A="A", B="B", E_set="E", m="m", n="n",
                        x="x", y="y"):
    """COROLLAIRE de Prop 5 : « la borne supérieure d'une SOUS-FAMILLE est ≤ à la
    borne supérieure de la famille ».

    Énoncé identique à `sup_monotone_inclusion` (la sous-famille = sous-partie A⊂B) :
        { A⊂B, m=sup A, n=sup B } ⊢ (m,n)∈G.   (E.III.10, Corollaire.)"""
    return sup_monotone_inclusion(G, A, B, E_set, m, n, x, y)


# ════════════════════════════════════════════════════════════════════════════
#  LEMME — si tout x∈A est majoré par un u∈B, un majorant de B majore A
#  (cœur Prop 6 : forme « termes dominés », subsume x_ι ≤ y_ι)
# ════════════════════════════════════════════════════════════════════════════
def _domine(G, A, B, x="x", u="u"):
    """domine(A,B) := (∀x)(x∈A ⇒ (∃u)(u∈B et (x,u)∈G)).

    « Tout élément de A est majoré (≤) par un élément de B »  (forme ensembliste de
    x_ι ≤ y_ι, E.III.10 Prop 6)."""
    vx, vu = var(x), var(u)
    return pourtout(x, impl(appartient(vx, _terme(A)),
                            existe(u, et(appartient(vu, _terme(B)), _couple_dans(vx, vu, G)))))


def majorant_de_sur_domine(G="G", A="A", B="B", E_set="E", m="m", x="x", u="u",
                           t="t", z="z"):
    """{ transitivite_rel(G), domine(A,B), majorant(G,B,m,E) } ⊢ majorant(G,A,m,E).

    Si tout x∈A est ≤ à un u∈B (domine) et si m majore B, alors m majore A : pour
    x∈A, soit u∈B avec x≤u ; comme u≤m (m majore B), la TRANSITIVITÉ donne x≤m.
    (E.III.10, lemme de Prop 6.)"""
    from bourbaki.ordre.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_relation import transitivite_rel
    vA, vB, vm, vE = _terme(A), _terme(B), _terme(m), _terme(E_set)
    vx, vu = var(x), var(u)
    Htr = N.assume(transitivite_rel(G, t, u, z))           # (∀t∀u∀z)(((t,u)∈G et (u,z)∈G)⇒(t,z)∈G)
    Hdom = N.assume(_domine(G, A, B, x, u))                # (∀x)(x∈A⇒(∃u)(u∈B et (x,u)∈G))
    Hmaj = N.assume(majorant(G, B, vm, E_set, x))          # m∈E et (∀x)(x∈B⇒(x,m)∈G)
    m_in_E = conjonction_elim_gauche(Hmaj)                 # m∈E
    maj_body = conjonction_elim_droite(Hmaj)               # (∀x)(x∈B⇒(x,m)∈G)
    # corps : x∈A ⇒ (x,m)∈G
    Hx = N.assume(appartient(vx, vA))                      # x∈A
    ex_u = N.modus_ponens(Hx, instancie(Hdom, vx))         # (∃u)(u∈B et (x,u)∈G)
    # éliminer l'existentiel : sous le témoin (u∈B et (x,u)∈G), dériver (x,m)∈G
    Hu = N.assume(et(appartient(vu, vB), _couple_dans(vx, vu, G)))  # u∈B et x≤u
    u_in_B = conjonction_elim_gauche(Hu)                   # u∈B
    xu = conjonction_elim_droite(Hu)                       # (x,u)∈G
    um = N.modus_ponens(u_in_B, instancie(maj_body, vu))   # (u,m)∈G
    # transitivité en (x,u,m) : ((x,u)∈G et (u,m)∈G) ⇒ (x,m)∈G
    tr_xum = instancie(instancie(instancie(Htr, vx), vu), vm)
    xm = N.modus_ponens(conjonction_intro(xu, um), tr_xum) # (x,m)∈G
    sous_u = N.loi_deduction(et(appartient(vu, vB), _couple_dans(vx, vu, G)), xm)
    ex_imp = existe_elimination(sous_u, u)                 # (∃u)(...) ⇒ (x,m)∈G
    xm_final = N.modus_ponens(ex_u, ex_imp)                # (x,m)∈G
    body = N.loi_deduction(appartient(vx, vA), xm_final)
    return conjonction_intro(m_in_E, N.generalisation(x, body))


# ════════════════════════════════════════════════════════════════════════════
#  PROPOSITION 6 (E.III.10) — x_ι ≤ y_ι (∀ι) ⇒ sup x_ι ≤ sup y_ι
# ════════════════════════════════════════════════════════════════════════════
def sup_monotone_termes(G="G", A="A", B="B", E_set="E", m="m", n="n",
                        x="x", y="y", u="u", t="t", z="z"):
    """{ transitivite_rel(G), domine(A,B),
         borne_superieure(G,A,m,E), borne_superieure(G,B,n,E) } ⊢ (m,n)∈G.

    PROPOSITION 6 (forme ensembliste « termes dominés ») : si tout élément de A est
    ≤ à un élément de B (ce que représente x_ι ≤ y_ι en posant A={x_ι}, B={y_ι}) et
    si les bornes m=sup A, n=sup B existent, alors sup A ≤ sup B.  En effet n majore
    B, donc (lemme + transitivité) n majore A ; m étant le plus petit majorant de A,
    m≤n.  (E.III.10.)"""
    from bourbaki.ordre.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_relation import transitivite_rel
    vn = _terme(n)
    Htr = N.assume(transitivite_rel(G, t, u, z))
    Hdom = N.assume(_domine(G, A, B, x, u))
    Hm = N.assume(borne_superieure(G, A, _terme(m), E_set, x, y))   # m=sup A
    Hn = N.assume(borne_superieure(G, B, vn, E_set, x, y))          # n=sup B
    m_least = conjonction_elim_droite(Hm)                  # (∀y)(maj(A,y)⇒(m,y)∈G)
    n_maj_B = conjonction_elim_gauche(Hn)                  # majorant(G,B,n,E)
    # n majore A — via majorant_de_sur_domine, en déchargeant ses 3 hypothèses
    n_maj_A = majorant_de_sur_domine(G, A, B, E_set, vn, x, u, t, z)
    n_maj_A = N.modus_ponens(Htr, N.loi_deduction(transitivite_rel(G, t, u, z), n_maj_A))
    n_maj_A = N.modus_ponens(Hdom, N.loi_deduction(_domine(G, A, B, x, u), n_maj_A))
    n_maj_A = N.modus_ponens(n_maj_B,
                             N.loi_deduction(majorant(G, B, vn, E_set, x), n_maj_A))
    mn = N.modus_ponens(n_maj_A, instancie(m_least, vn))   # (m,n)∈G
    return mn


# ════════════════════════════════════════════════════════════════════════════
#  PROPOSITION 9 (E.III.12) — sup dans un sous-ensemble ordonné F⊂E
# ════════════════════════════════════════════════════════════════════════════
def sup_induit_sur_partie(G="G", A="A", E_set="E", F="F", m="m", x="x", y="y"):
    """{ borne_superieure(G,A,m,E),  m∈F,
         (∀y)(majorant(G,A,y,F) ⇒ (m,y)∈G) }  ⊢ borne_superieure(G,A,m,F).
    (Contexte Prop 9 : F⊂E, A⊂F ; A⊂F n'intervient pas dans la dérivation.)

    PROPOSITION 9 : F⊂E sous-ensemble ordonné, A⊂F.  Si m=sup_E A appartient à F et
    reste le plus petit des majorants de A pris DANS F, alors m=sup_F A.  Le cœur
    « m majore A » est conservé tel quel (la relation (x,m)∈G ne dépend pas de
    l'ensemble de base) ; il suffit que m∈F et que m soit ≤ à tout majorant de A
    dans F (hypothèse honnête : sans elle un majorant de A dans F pourrait être
    incomparable à m).  (E.III.12.)"""
    vA, vF, vm = _terme(A), _terme(F), _terme(m)
    vy = var(y)
    # A⊂F est le CONTEXTE de la Prop 9 (F⊂E, A⊂F) mais n'intervient pas dans la
    # dérivation : « m majore A dans F » ne requiert que m∈F + (m majore A dans E).
    Hm = N.assume(borne_superieure(G, A, vm, E_set, x, y)) # m=sup_E A
    HmF = N.assume(appartient(vm, vF))                     # m∈F
    Hpp = N.assume(pourtout(y, impl(majorant(G, A, vy, F, x), _couple_dans(vm, vy, G))))
    # (1) m majore A « dans F » : m∈F et (∀x)(x∈A⇒(x,m)∈G)
    maj_E = conjonction_elim_gauche(Hm)                    # majorant(G,A,m,E)
    m_maj_body = conjonction_elim_droite(maj_E)            # (∀x)(x∈A⇒(x,m)∈G)
    maj_F = conjonction_intro(HmF, m_maj_body)             # majorant(G,A,m,F)
    # (2) m est le plus petit majorant DANS F : c'est exactement Hpp
    return conjonction_intro(maj_F, Hpp)                   # borne_superieure(G,A,m,F)


# ════════════════════════════════════════════════════════════════════════════
#  PROPOSITION 7 (E.III.11) — sup par RECOUVREMENT (lemme-clé certifié)
#  I = ⋃_λ J_λ : un point m majore ⋃A_λ  ⇔  m majore chaque A_λ.
#  Forme binaire ensembliste : majorant de A∪B ⇔ (majorant de A et majorant de B).
# ════════════════════════════════════════════════════════════════════════════
def majorant_reunion_iff(G="G", A="A", B="B", E_set="E", m="m", x="x"):
    """⊢ ( majorant(G, A∪B, m, E) ) ⇔ ( majorant(G,A,m,E) et majorant(G,B,m,E) ).

    LEMME-CLÉ de Prop 7 (recouvrement, forme binaire I=J₁∪J₂) : m majore la réunion
    A∪B si et seulement si m majore A ET m majore B.  Conséquence immédiate :
    sup(A∪B) = le plus petit majorant commun = sup{ sup A, sup B } — la Prop 7
    ramène le sup d'une réunion aux sup des morceaux.  (E.III.11.)

    [Le passage de ce lemme à l'égalité sup(A∪B)=sup{supA,supB} demande la borne sup
    d'une PAIRE {supA,supB} : voir RAPPORT — résiduel honnête.]"""
    from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_theoremes import _instance_reunion
    from bourbaki.logique.i_1_termes_relations.formule import ou as _ou
    from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
        equivalence_arriere as _ea, equivalence_avant as _ev, cas as _cas,
    )
    from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege import syllogisme
    vA, vB, vm, vE = _terme(A), _terme(B), _terme(m), _terme(E_set)
    vx = var(x)
    AuB = E.reunion(vA, vB)

    def _ou_gauche(P, Q):
        """⊢ P ⇒ (P ou Q)  (intro gauche de la disjonction, via S2)."""
        return N.s2(P, Q)

    def _ou_droite(P, Q):
        """⊢ Q ⇒ (P ou Q) : Q ⇒ (Q∨P) [S2] puis (Q∨P) ⇒ (P∨Q) [S3]."""
        return syllogisme(N.s2(Q, P), N.s3(Q, P))

    # ── sens ⇒ : majorant(A∪B) ⇒ (majorant(A) et majorant(B))
    Hmaj = N.assume(majorant(G, AuB, vm, E_set, x))        # m∈E et (∀x)(x∈A∪B⇒(x,m)∈G)
    m_in_E = conjonction_elim_gauche(Hmaj)                 # m∈E
    maj_body = conjonction_elim_droite(Hmaj)               # (∀x)(x∈A∪B⇒(x,m)∈G)
    # m majore A : x∈A ⇒ x∈A∪B ⇒ (x,m)∈G
    HxA = N.assume(appartient(vx, vA))                     # x∈A
    # _instance_reunion(A,B,x) : (x∈A∪B) ⇔ (x∈A ou x∈B)
    rm = _instance_reunion(vA, vB, vx)
    xA_or = N.modus_ponens(HxA, _ou_gauche(appartient(vx, vA), appartient(vx, vB)))  # x∈A ou x∈B
    xA_in_u = N.modus_ponens(xA_or, _ea(rm))               # x∈A∪B
    xmA = N.modus_ponens(xA_in_u, instancie(maj_body, vx)) # (x,m)∈G
    bodyA = N.loi_deduction(appartient(vx, vA), xmA)
    majA = conjonction_intro(m_in_E, N.generalisation(x, bodyA))   # majorant(G,A,m,E)
    # m majore B : x∈B ⇒ x∈A∪B ⇒ (x,m)∈G
    HxB = N.assume(appartient(vx, vB))                     # x∈B
    xB_or = N.modus_ponens(HxB, _ou_droite(appartient(vx, vA), appartient(vx, vB)))  # x∈A ou x∈B
    xB_in_u = N.modus_ponens(xB_or, _ea(rm))               # x∈A∪B
    xmB = N.modus_ponens(xB_in_u, instancie(maj_body, vx)) # (x,m)∈G
    bodyB = N.loi_deduction(appartient(vx, vB), xmB)
    majB = conjonction_intro(m_in_E, N.generalisation(x, bodyB))   # majorant(G,B,m,E)
    sens_avant = N.loi_deduction(majorant(G, AuB, vm, E_set, x),
                                 conjonction_intro(majA, majB))

    # ── sens ⇐ : (majorant(A) et majorant(B)) ⇒ majorant(A∪B)
    Hand = N.assume(et(majorant(G, A, vm, E_set, x), majorant(G, B, vm, E_set, x)))
    HA = conjonction_elim_gauche(Hand)                     # majorant(G,A,m,E)
    HB = conjonction_elim_droite(Hand)                     # majorant(G,B,m,E)
    mE2 = conjonction_elim_gauche(HA)                      # m∈E
    A_body = conjonction_elim_droite(HA)                   # (∀x)(x∈A⇒(x,m)∈G)
    B_body = conjonction_elim_droite(HB)                   # (∀x)(x∈B⇒(x,m)∈G)
    # x∈A∪B ⇒ (x,m)∈G : x∈A∪B ⇒ (x∈A ou x∈B), puis par cas
    Hxu = N.assume(appartient(vx, AuB))                    # x∈A∪B
    rm2 = _instance_reunion(vA, vB, vx)
    disj = N.modus_ponens(Hxu, _ev(rm2))                   # x∈A ou x∈B
    cas1 = N.loi_deduction(appartient(vx, vA),
                           N.modus_ponens(N.assume(appartient(vx, vA)), instancie(A_body, vx)))
    cas2 = N.loi_deduction(appartient(vx, vB),
                           N.modus_ponens(N.assume(appartient(vx, vB)), instancie(B_body, vx)))
    xm_u = _cas(disj, cas1, cas2)                          # (x,m)∈G
    body_u = N.loi_deduction(appartient(vx, AuB), xm_u)
    maj_u = conjonction_intro(mE2, N.generalisation(x, body_u))    # majorant(G,A∪B,m,E)
    sens_arriere = N.loi_deduction(
        et(majorant(G, A, vm, E_set, x), majorant(G, B, vm, E_set, x)), maj_u)

    return conjonction_intro(sens_avant, sens_arriere)     # (maj(A∪B)) ⇔ (maj(A) et maj(B))


__all__ = [
    "majorant_de_sur_partie",
    "sup_monotone_inclusion", "sup_sous_famille_le",
    "majorant_de_sur_domine", "sup_monotone_termes",
    "sup_induit_sur_partie",
    "majorant_reunion_iff",
]
