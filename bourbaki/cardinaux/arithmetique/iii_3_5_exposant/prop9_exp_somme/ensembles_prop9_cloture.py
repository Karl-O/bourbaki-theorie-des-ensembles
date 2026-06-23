"""§III.3.5 — PROPOSITION 9 (forme exponentielle), CLÔTURE : a^(b+c) = a^b · a^c.

ÉNONCÉ visé (forme cardinale binaire du projet) :

        ⊢ Card(𝓕(B⊔C; A)) = Card(𝓕(B;A) × 𝓕(C;A))           (= cible_prop9_exp_somme)

via la BIJECTION  Φ : 𝓕(B⊔C;A) → 𝓕(B;A) × 𝓕(C;A),  f ↦ (f|B , f|C), de graphe
W = graphe_terme(𝓕(B⊔C;A), Φ(f), « f »)  (cf. ensembles_prop9_final).

═══════════════════════════════════════════════════════════════════════════════
CE QUE CE MODULE FERME (paliers sûrs, additif, AUCUN fichier existant modifié) :

PALIER ASSEMBLAGE (CLOS) — la bijection à partir de ses CONJOINTS :
  • bijection_de_conjoints(fonct, dom_eq, inj, img)
        de  ⊢ est_fonctionnel(W), ⊢ dom W = dom_phi, ⊢ injective_dans(W, dom_phi),
            ⊢ image(W, dom_phi) = cod_phi
        produit  ⊢ est_bijection_de(W, dom_phi, cod_phi).
    Assembleur PUR (structure de est_bijection_de = (fonct et dom=) et (inj et img=)),
    miroir EXACT de chi_bijection (Prop 12) et eta_bijection (a^1=a).

PALIER DERNIER MILE TIGHT (CLOS, CONDITIONNEL aux DEUX conjoints DURS SEULEMENT) :
  • prop9_si_conjoints_durs(a,b,c)
        {injective_dans(W, dom_phi),  image(W, dom_phi) = cod_phi}
        ⊢ Card(𝓕(B⊔C;A)) = Card(𝓕(B;A) × 𝓕(C;A)).
    On CONSOMME les conjoints STRUCTURELS déjà CLOS au round 32 (W_fonctionnel,
    W_domaine) + l'assembleur ci-dessus + card_eq_si_bijection (R32).  La
    conditionnalité passe ainsi de « est_bijection_de(W,…) tout entier » (état R32)
    aux DEUX SEULS conjoints DURS encore ouverts — un resserrement strict du « reste
    à faire » de la Proposition 9.

CŒUR REPORTÉ (les deux conjoints DURS) : voir `conjoints_durs_REPORTE`.  Les trois
verrous (bien-définition image, injectivité complète, surjectivité) reposent TOUS
sur le MÊME pont absent : la VALEUR f((u,0)) d'une APPLICATION-TRIPLE f=((G,B⊔C),A)
le long de l'injection ι_B : u↦(u,0).  Diagnostic précis dans le REPORTE et la note
StructuredOutput (verrou hérité R24→R32, partagé par la Prop 12 dont le sens
fonction-espace χ∘ρ=id est lui aussi reporté).
═══════════════════════════════════════════════════════════════════════════════
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import Terme, var, egal, et, appartient
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import conjonction_intro
from bourbaki.cardinaux.ensembles_cardinaux import est_bijection_de
from bourbaki.cardinaux.arithmetique.iii_3_5_exposant.prop9_exp_somme.ensembles_prop9_final import (
    W, domaine_phi, codomaine_phi, W_fonctionnel, W_domaine,
    card_eq_si_bijection)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# ═══════════════════════════════════════════════════════════════════════════════
# PALIER ASSEMBLAGE — est_bijection_de(W,…) à partir de ses quatre CONJOINTS
# ═══════════════════════════════════════════════════════════════════════════════
def bijection_de_conjoints(fonct, dom_eq, inj, img):
    """De  ⊢ est_fonctionnel(W),  ⊢ dom W = dom_phi,  ⊢ injective_dans(W, dom_phi),
       ⊢ image(W, dom_phi) = cod_phi  →  ⊢ est_bijection_de(W, dom_phi, cod_phi).

    Assembleur PUR.  La définition (ensembles_cardinaux.est_bijection_de) est
        est_bijection_de(F,X,Y) = (est_fonctionnel(F) et dom F = X)
                                  et est_bijective(F,X,Y),
    où est_bijective(F,X,Y) = (injective_dans(F,X) et est_surjective(F,X,Y))
    et est_surjective(F,X,Y) = (image(F,X) = Y).  On RECOLLE les quatre conjoints
    par double conjonction — exactement comme chi_bijection (Prop 12) /
    eta_bijection (a^1=a).  Les arguments sont des THÉORÈMES (mêmes hypothèses Γ
    pour pouvoir composer)."""
    bij = conjonction_intro(inj, img)                    # est_bijective(W, dom, cod)
    return conjonction_intro(conjonction_intro(fonct, dom_eq), bij)


# ═══════════════════════════════════════════════════════════════════════════════
# PALIER DERNIER MILE TIGHT — la cible, CONDITIONNELLE aux DEUX conjoints DURS
# ═══════════════════════════════════════════════════════════════════════════════
def W_injective_hyp(a="A", b="B", c="C"):
    """La formule injective_dans(W, 𝓕(B⊔C;A))  (1ᵉʳ conjoint DUR, hypothèse)."""
    va, vb, vc = _t(a), _t(b), _t(c)
    return E.injective_dans(W(va, vb, vc), domaine_phi(va, vb, vc))


def W_image_hyp(a="A", b="B", c="C"):
    """La formule image(W, 𝓕(B⊔C;A)) = 𝓕(B;A)×𝓕(C;A)  (2ᵉ conjoint DUR, hypothèse).

    = est_surjective(W, dom_phi, cod_phi) déplié (E.II.49, Déf. 10)."""
    va, vb, vc = _t(a), _t(b), _t(c)
    return egal(E.image(W(va, vb, vc), domaine_phi(va, vb, vc)),
                codomaine_phi(va, vb, vc))


def prop9_si_conjoints_durs(a="A", b="B", c="C"):
    """{injective_dans(W, 𝓕(B⊔C;A)),  image(W, 𝓕(B⊔C;A)) = 𝓕(B;A)×𝓕(C;A)}
        ⊢ Card(𝓕(B⊔C;A)) = Card(𝓕(B;A) × 𝓕(C;A)).      (= cible_prop9_exp_somme.)

    DERNIER MILE RESSERRÉ de la Proposition 9.  Les conjoints STRUCTURELS de la
    bijection W sont DÉJÀ CLOS (round 32) : W fonctionnel (W_fonctionnel) et
    dom W = 𝓕(B⊔C;A) (W_domaine).  On les recolle, via `bijection_de_conjoints`,
    avec les DEUX conjoints DURS encore ouverts (injectivité + surjectivité, ici
    pris comme HYPOTHÈSES) pour former est_bijection_de(W, dom_phi, cod_phi) ; puis
    card_eq_si_bijection (R32) conclut l'égalité des cardinaux.

    La conclusion est LITTÉRALEMENT `cible_prop9_exp_somme(A,B,C)` (= a^(b+c)=a^b·a^c).
    Il ne reste, pour CLORE INCONDITIONNELLEMENT la Proposition 9, qu'à DÉCHARGER ces
    deux hypothèses — c.-à-d. fermer les deux conjoints DURS (`conjoints_durs_REPORTE`).
    C'est un resserrement strict : l'état R32 conditionnait la cible sur la CONJONCTION
    ENTIÈRE est_bijection_de(W,…) (quatre conjoints) ; ici, sur DEUX SEULEMENT."""
    va, vb, vc = _t(a), _t(b), _t(c)
    # conjoints STRUCTURELS, déjà CLOS (R32)
    fonct = W_fonctionnel(va, vb, vc)                    # ⊢ est_fonctionnel(W)
    dom_eq = W_domaine(va, vb, vc)                       # ⊢ dom W = 𝓕(B⊔C;A)
    # conjoints DURS, pris comme HYPOTHÈSES (à décharger une fois fermés)
    inj = N.assume(W_injective_hyp(va, vb, vc))          # injective_dans(W, dom_phi)
    img = N.assume(W_image_hyp(va, vb, vc))              # image(W, dom_phi) = cod_phi
    # est_bijection_de(W, dom_phi, cod_phi) par assemblage des quatre conjoints
    bij = bijection_de_conjoints(fonct, dom_eq, inj, img)
    # Card(dom_phi) = Card(cod_phi)  (card_eq_si_bijection, R32, sous {bij W})
    cond = card_eq_si_bijection(va, vb, vc)              # {est_bijection_de(W,…)} ⊢ cible
    return N.modus_ponens(bij, N.loi_deduction(
        est_bijection_de(W(va, vb, vc), domaine_phi(va, vb, vc),
                         codomaine_phi(va, vb, vc)), cond))


def prop9_cible_conditionnelle(a="A", b="B", c="C"):
    """{conjoints DURS} ⊢ a^(b+c) = a^b · a^c   (alias EXPLICITE de la cible Prop 9).

    Identique à prop9_si_conjoints_durs ; nom mettant en avant l'énoncé arithmétique
    (Cor. 1 de la Proposition 10, E.III.3.5).  Sa conclusion est EXACTEMENT
    cible_prop9_exp_somme(A,B,C)."""
    return prop9_si_conjoints_durs(a, b, c)


# ═══════════════════════════════════════════════════════════════════════════════
# CŒUR REPORTÉ — les deux conjoints DURS de est_bijection_de(W, …)
# ═══════════════════════════════════════════════════════════════════════════════
def conjoints_durs_REPORTE():
    """REPORTÉ (non clos) — les deux conjoints DURS  injective_dans(W, 𝓕(B⊔C;A))  et
    image(W, 𝓕(B⊔C;A)) = 𝓕(B;A)×𝓕(C;A).

    Ce module ferme l'ASSEMBLAGE de la bijection (bijection_de_conjoints) et le
    DERNIER MILE RESSERRÉ (prop9_si_conjoints_durs : la cible Prop 9 conditionnée aux
    DEUX conjoints DURS seulement, les structurels W_fonctionnel/W_domaine étant
    consommés depuis R32).  Restent REPORTÉS, tous bloqués sur le MÊME pont absent :

      VERROU UNIQUE — la VALEUR d'une APPLICATION-TRIPLE le long de l'injection ι_B.
        Une application f ∈ 𝓕(B⊔C;A) est le TRIPLE ((G, B⊔C), A) de son graphe G
        (axiome_applications).  Mais valeur(f, (u,0)) = τy( ((u,0),y) ∈ ((G,B⊔C),A) )
        porte sur l'appartenance d'un couple au TRIPLE (une paire imbriquée de paires),
        SANS aucun lien avec l'appartenance au graphe G.  Le projet ne dispose
        d'AUCUN axiome ni lemme reliant valeur(f,·) (sur le triple) à valeur(G,·) (sur
        le graphe sous-jacent).  Or les trois conjoints en ont besoin :

      (i)   BIEN-DÉFINITION (sous-cas de l'image) : f|B ∈ 𝓕(B;A) exige f|B ⊂ B×A,
            donc la valeur f((u,0)) ∈ A pour u∈B — transport de « f∈𝓕(B⊔C;A) ⇒
            G((u,0))∈A car (u,0)∈B⊔C=dom G » À TRAVERS le triple jusqu'à valeur(f,·) ;
      (ii)  INJECTIVITÉ COMPLÈTE : de f₁|B=f₂|B et f₁|C=f₂|C
            (W_injective_restrictions_coincident, CLOS R32) à f₁=f₂, par
            EXTENSIONNALITÉ fonctionnelle (graphe_egal_par_valeurs) sur B⊔C — qui
            apparie les valeurs, donc retombe sur valeur(fᵢ,·) à travers le triple ;
            l'analogue Prop 12 le contourne par une RÉTRACTION (Pre(χ_Y)=Y,
            rho_chi_identite) ; ici la rétraction serait le RECOLLEMENT
            recollement(f|B,f|C)=f, qui réclame le même pont ;
      (iii) SURJECTIVITÉ : depuis (g,h) arbitraire, le recollement réindexé ψ(g,h)
            (recollement_fonctionnel, CLOS R25) vérifie Φ(ψ(g,h))=(g,h), soit
            ψ(g,h)|B=g — encore l'identification de la valeur d'un triple à celle de
            son graphe.

    C'est le verrou hérité des rounds 24→32 ; il est PARTAGÉ par la Proposition 12,
    dont le sens fonction-espace χ∘ρ=id (bijection_prop12_REPORTE) reste reporté pour
    la même raison.  Le lever demande soit un AXIOME de valeur-d'application
    (valeur(((G,E),F), x) = valeur(G, x) sous x∈dom G), soit une RÉINGÉNIERIE des
    restrictions pour lire directement le graphe sous-jacent pr₁(pr₁ f) — hors budget
    et hors périmètre (interdiction de modifier les fichiers existants en parallèle)."""
    raise NotImplementedError(
        "Conjoints DURS de est_bijection_de(W,…) reportés : injective_dans(W,dom_phi) "
        "(ii) et image(W,dom_phi)=cod_phi (i bien-déf + iii surjectivité), tous bloqués "
        "sur le pont absent valeur-d'application-triple le long de ι_B,ι_C "
        "(valeur(((G,B⊔C),A),(u,0)) ↔ valeur(G,(u,0)) — aucun axiome/lemme dans le "
        "projet).  Ce module livre l'ASSEMBLEUR bijection_de_conjoints et le DERNIER "
        "MILE RESSERRÉ prop9_si_conjoints_durs (cible Prop 9 conditionnée aux DEUX "
        "conjoints DURS seulement).")


__all__ = [
    "bijection_de_conjoints",
    "W_injective_hyp", "W_image_hyp",
    "prop9_si_conjoints_durs", "prop9_cible_conditionnelle",
    "conjoints_durs_REPORTE",
]
