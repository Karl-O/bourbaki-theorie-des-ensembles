"""§III.1 n°2 — PROPOSITION 1 (E.III.2) : RÉCIPROQUE (la SUFFISANCE).

ÉNONCÉ DE BOURBAKI (verbatim, E.III.2, Proposition 1) :
    « Pour qu'une correspondance Γ = (G, E, E) entre E et E soit un ordre sur E,
      il faut et il suffit que son graphe G satisfasse aux conditions suivantes :
        a) On a  G ∘ G = G.
        b) L'ensemble  G ∩ G⁻¹  est la diagonale Δ de E × E. »

CE MODULE FORMALISE LA RÉCIPROQUE (la SUFFISANCE) : SI  (a) G∘G = G  et
(b) G ∩ G⁻¹ = Δ_E,  ALORS  est_ordre(G, E)  (réflexivité sur E, antisymétrie,
transitivité, E.III.1.1).  Le résultat est certifié par le noyau LCF (primitives
N.* uniquement), CLOS SOUS LES DEUX HYPOTHÈSES HONNÊTES (les conditions a) et b)
de Bourbaki) :

    H_a = composee(G, G) = G                         (condition a)
    H_b = inter(G, reciproque(G)) = graphe_identite(E)   (condition b ; Δ_E)

ASYMÉTRIE AVEC LE SENS DIRECT — le CHAMP G⊆E×E n'est PAS nécessaire ici.
Le module direct doit ajouter H2 = G⊆E×E (pour décomposer un couple quelconque
de G en (a,b) avec a,b∈E).  Dans la RÉCIPROQUE, au contraire, on ne décompose
JAMAIS un élément arbitraire de G : on part toujours d'éléments DÉJÀ couples sur
E.  Plus précisément, le champ E entre uniquement par Δ_E = graphe_identite(E),
dont le lemme membre_graphe_terme PORTE DÉJÀ l'appartenance « ∈E » :
    ((a,b) ∈ Δ_E) ⇔ (a∈E et b=a).
  • réflexivité : l'antécédent est « x∈E », et (x,x)∈Δ_E s'obtient de (x∈E et x=x)
        par membre_graphe_terme (⇐) ; Δ_E⊆G (de H_b) conclut (x,x)∈G.
  • antisymétrie / transitivité : pures propriétés de G, aucun « ∈E » requis.
Donc les SEULES hypothèses load-bearing sont H_a et H_b.  (theorie==22.)

STRATÉGIE (la preuve Bourbaki marche dans les deux sens) :
  transitivité :  H_a ⇒ G∘G⊆G ;  (x,y)∈G et (y,z)∈G ⇒(couple_composee, témoin y)
      (x,z)∈G∘G ⇒(H_a, Leibniz) (x,z)∈G.
  antisymétrie :  H_b ⇒ G∩G⁻¹⊆Δ_E ;  (x,y)∈G et (y,x)∈G ⇒ (x,y)∈G et (x,y)∈G⁻¹
      [couple_reciproque] ⇒ (x,y)∈G∩G⁻¹ ⇒(H_b) (x,y)∈Δ_E ⇒(membre_graphe_terme) x=y.
  réflexivité :   H_b ⇒ Δ_E⊆G∩G⁻¹⊆G ;  x∈E ⇒ (x,x)∈Δ_E [membre_graphe_terme]
      ⇒(H_b) (x,x)∈G∩G⁻¹ ⇒ (x,x)∈G.   conjonction_intro des trois → est_ordre(G,E).
Une ÉGALITÉ de graphes A=B s'exploite comme inclusion (w∈A ⇒ w∈B) en
transportant par N.s6 le long de l'égalité.

STATUT : RÉCIPROQUE bouclée, CLOSE sous { composee(G,G)=G, inter(G,G⁻¹)=Δ_E }.
BONUS : l'ÉQUIVALENCE complète de la Prop 1, CLOSE sous { champ(G,E) } (le champ
n'est requis que par le sens direct), assemblée à partir du sens direct et de la
réciproque.  theorie_ensembles() reste à 22 axiomes (aucun axiome ajouté).
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (
    var, egal, et, appartient, Terme)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, instancie)
from bourbaki.logique.i_4_egalitaires.tactiques_abrege_egalite import symetrie

from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_theoremes import _instance_intersection
from bourbaki.ensembles.fonctions.ii_3_2_reciproque.ensembles_reciproque import couple_reciproque
from bourbaki.ensembles.fonctions.ii_3_3_composee_graphes.ensembles_composee import couple_composee
from bourbaki.ensembles.fonctions.ii_3_6_fonction_terme.ensembles_fonction_terme import membre_graphe_terme
from bourbaki.ensembles.ii_3_correspondances.ensembles_fondations_notions import graphe_identite
from bourbaki.ordre.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_relation import est_ordre
from bourbaki.ordre.iii_1_relations_ordre.iii_1_2_caracterisation_ordre.ensembles_prop1_caracterisation import (
    champ, caracterisation_ordre_sens_direct)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def _couple(a, b):
    return E.couple(a, b)


def _dans(a, b, S):
    return appartient(_couple(a, b), S)


def _transporte_appartenance(eq_thm, A, B, w):
    """De ⊢ A=B (eq_thm) déduit ⊢ (w∈A) ⇒ (w∈B).   (réécriture par Leibniz S6.)

    A=B ⇒ (w∈A ⇔ w∈B) (N.s6, trou « t » sur l'ensemble) ; on garde le sens ⇒."""
    leib = N.modus_ponens(eq_thm, N.s6(A, B, "t", appartient(w, var("t"))))
    return equivalence_avant(leib)                        # (w∈A) ⇒ (w∈B)


def _membre_diagonale(vE, s, t):
    """⊢ ((s,t) ∈ graphe_identite(E)) ⇔ (s∈E et t=s),   pour des TERMES s, t.

    Δ_E = graphe_identite(E) = graphe_terme(E, x, "x").  membre_graphe_terme donne
    le schéma sur les coordonnées (a,b) — coords DISTINCTES des liants x,y du
    graphe_terme, sinon collision de liant ; on universalise puis instancie en s,t."""
    schema = membre_graphe_terme(vE, var("x"), "a", "b", "x", "y")   # ((a,b)∈Δ_E) ⇔ (a∈E et b=a)
    universel = N.generalisation("a", N.generalisation("b", schema))
    return instancie(instancie(universel, s), t)          # ((s,t)∈Δ_E) ⇔ (s∈E et t=s)


# ════════════════════════════════════════════════════════════════════════════
#  TRANSITIVITÉ — de  composee(G,G) = G
# ════════════════════════════════════════════════════════════════════════════
def reciproque_transitivite(g="G", e="E", x="u", y="v", z="s"):
    """{ composee(G,G)=G } ⊢ transitivite_rel(G,x,y,z).

    G∘G⊆G (de H_a, Leibniz) ; (x,y)∈G et (y,z)∈G ⇒(couple_composee, témoin y)
    (x,z)∈G∘G ⇒ (x,z)∈G.  (Le champ n'intervient pas.)

    Liants « u, v, s » par DÉFAUT — cohérents avec reflexivité/antisymétrie ; ici
    H_a = composee(G,G)=G ne laisse AUCUN liant libre, donc x serait permis, mais
    on uniformise sur u, v, s pour reconstruire est_ordre(G,E,u,v,s).  Les liants u,
    v, s évitent {x, y, p, r, w} (liants/trous internes de couple_composee et de
    couple_egal_implique_composantes).  Le témoin de composition reste le liant
    interne « y » de couple_composee (corps déchargé avant toute généralisation)."""
    vG = _t(g)
    vx, vy, vz = var(x), var(y), var(z)
    vyt = var("y")                                         # liant interne de couple_composee
    Comp = E.composee(vG, vG)

    Hcomp = N.assume(egal(Comp, vG))                       # composee(G,G) = G
    # corps : ((x,y)∈G et (y,z)∈G) ⇒ (x,z)∈G
    hyp = et(_dans(vx, vy, vG), _dans(vy, vz, vG))
    Hbody = N.assume(hyp)
    xy_G = conjonction_elim_gauche(Hbody)                  # (x,y)∈G
    yz_G = conjonction_elim_droite(Hbody)                  # (y,z)∈G
    # (x,z)∈G∘G  via couple_composee — couple_composee(Gp,G,a,c) est
    # ((a,c)∈Gp∘G) ⇔ (∃y)((a,y)∈G et (y,c)∈Gp) ; ici Gp=G donc le corps colle.
    cc = couple_composee(vG, vG, vx, vz)                   # ((x,z)∈G∘G) ⇔ (∃y)((x,y)∈G et (y,z)∈G)
    # témoin (∃y), instancié en v : (x,v)∈G et (v,z)∈G = (v|y)((x,y)∈G et (y,z)∈G)
    wit = conjonction_intro(xy_G, yz_G)
    ex_y = N.modus_ponens(wit, N.s5(et(_dans(vx, vyt, vG), _dans(vyt, vz, vG)), vy, "y"))
    xz_comp = N.modus_ponens(ex_y, equivalence_arriere(cc))   # (x,z)∈G∘G
    xz_G = N.modus_ponens(xz_comp, _transporte_appartenance(
        Hcomp, Comp, vG, _couple(vx, vz)))                # (x,z)∈G
    body = N.loi_deduction(hyp, xz_G)
    return N.generalisation(x, N.generalisation(y, N.generalisation(z, body)))


# ════════════════════════════════════════════════════════════════════════════
#  ANTISYMÉTRIE — de  inter(G, reciproque(G)) = graphe_identite(E)
# ════════════════════════════════════════════════════════════════════════════
def reciproque_antisymetrie(g="G", e="E", x="u", y="v"):
    """{ inter(G,reciproque(G))=Δ_E } ⊢ antisymetrie(G,x,y).

    G∩G⁻¹⊆Δ_E (de H_b, Leibniz) ; (x,y)∈G et (y,x)∈G ⇒ (x,y)∈G et (x,y)∈G⁻¹
    [couple_reciproque] ⇒ (x,y)∈G∩G⁻¹ ⇒ (x,y)∈Δ_E ⇒(membre_graphe_terme) x=y.
    (Le champ n'intervient pas : membre_graphe_terme donne directement y=x.)

    Les liants x, y de la conclusion sont « u, v » par DÉFAUT, distincts du « x »
    que graphe_identite(E)=graphe_terme(E,x) laisse LIBRE dans l'hypothèse H_b :
    on ne peut C27-généraliser sur un nom libre d'une hypothèse encore en scope.
    u, v évitent aussi {p, q, w} (liants/trous de couple_reciproque)."""
    vG, vE = _t(g), _t(e)
    vx, vy = var(x), var(y)
    Grec = E.reciproque(vG)
    Inter = E.intersection(vG, Grec)
    Id = graphe_identite(vE)                               # = graphe_terme(E,x) = Δ_E

    Hb = N.assume(egal(Inter, Id))                         # inter(G,G⁻¹) = Δ_E
    inter_xy = _instance_intersection(vG, Grec, _couple(vx, vy))   # ((x,y)∈inter) ⇔ ((x,y)∈G et (x,y)∈G⁻¹)
    # corps : ((x,y)∈G et (y,x)∈G) ⇒ x=y
    hyp = et(_dans(vx, vy, vG), _dans(vy, vx, vG))
    Hbody = N.assume(hyp)
    xy_G = conjonction_elim_gauche(Hbody)                  # (x,y)∈G
    yx_G = conjonction_elim_droite(Hbody)                  # (y,x)∈G
    cr = couple_reciproque(vG, vx, vy)                     # ((x,y)∈G⁻¹) ⇔ ((y,x)∈G)
    xy_Grec = N.modus_ponens(yx_G, equivalence_arriere(cr))   # (x,y)∈G⁻¹
    xy_inter = N.modus_ponens(conjonction_intro(xy_G, xy_Grec),
                              equivalence_arriere(inter_xy))   # (x,y)∈G∩G⁻¹
    xy_Id = N.modus_ponens(xy_inter, _transporte_appartenance(
        Hb, Inter, Id, _couple(vx, vy)))                  # (x,y)∈Δ_E
    mid = _membre_diagonale(vE, vx, vy)                   # ((x,y)∈Δ_E) ⇔ (x∈E et y=x)
    xE_yx = N.modus_ponens(xy_Id, equivalence_avant(mid))  # x∈E et y=x
    y_eq_x = conjonction_elim_droite(xE_yx)               # y=x
    x_eq_y = N.modus_ponens(y_eq_x, symetrie(vy, vx))     # x=y
    body = N.loi_deduction(hyp, x_eq_y)
    return N.generalisation(x, N.generalisation(y, body))


# ════════════════════════════════════════════════════════════════════════════
#  RÉFLEXIVITÉ SUR E — de  inter(G, reciproque(G)) = graphe_identite(E)
# ════════════════════════════════════════════════════════════════════════════
def reciproque_reflexivite(g="G", e="E", x="u"):
    """{ inter(G,reciproque(G))=Δ_E } ⊢ reflexivite_sur(G,E,x).

    Δ_E⊆G∩G⁻¹ (de H_b, Leibniz, sens B=A) puis G∩G⁻¹⊆G (projection) ; pour x∈E,
    (x,x)∈Δ_E [membre_graphe_terme, x∈E et x=x] ⇒ (x,x)∈G∩G⁻¹ ⇒ (x,x)∈G.
    Ici « x∈E » EST l'antécédent : aucun champ requis.

    Liant « u » par DÉFAUT (≠ « x » laissé libre par graphe_identite dans H_b)."""
    vG, vE = _t(g), _t(e)
    vx = var(x)
    Grec = E.reciproque(vG)
    Inter = E.intersection(vG, Grec)
    Id = graphe_identite(vE)

    Hb = N.assume(egal(Inter, Id))                         # inter(G,G⁻¹) = Δ_E
    inter_xx = _instance_intersection(vG, Grec, _couple(vx, vx))   # ((x,x)∈inter) ⇔ ((x,x)∈G et (x,x)∈G⁻¹)
    # corps : x∈E ⇒ (x,x)∈G
    Hx = N.assume(appartient(vx, vE))                      # x∈E
    mid = _membre_diagonale(vE, vx, vx)                   # ((x,x)∈Δ_E) ⇔ (x∈E et x=x)
    xx_Id = N.modus_ponens(conjonction_intro(Hx, N.reflexivite(vx)),
                           equivalence_arriere(mid))      # (x,x)∈Δ_E
    # Δ_E = inter (symétrie de H_b) ⇒ (x,x)∈Δ_E ⇒ (x,x)∈G∩G⁻¹
    Hb_sym = N.modus_ponens(Hb, symetrie(Inter, Id))      # Δ_E = inter(G,G⁻¹)
    xx_inter = N.modus_ponens(xx_Id, _transporte_appartenance(
        Hb_sym, Id, Inter, _couple(vx, vx)))              # (x,x)∈G∩G⁻¹
    xx_pair = N.modus_ponens(xx_inter, equivalence_avant(inter_xx))   # (x,x)∈G et (x,x)∈G⁻¹
    xx_G = conjonction_elim_gauche(xx_pair)               # (x,x)∈G
    body = N.loi_deduction(appartient(vx, vE), xx_G)
    return N.generalisation(x, body)


# ════════════════════════════════════════════════════════════════════════════
#  RÉCIPROQUE COMPLÈTE — est_ordre(G,E)
# ════════════════════════════════════════════════════════════════════════════
def caracterisation_ordre_reciproque(g="G", e="E", x="u", y="v", z="s"):
    """{ composee(G,G)=G,  inter(G,reciproque(G))=Δ_E } ⊢ est_ordre(G,E,x,y,z).

    LA SUFFISANCE de la Proposition 1 (E.III.2) : les conditions a) et b)
    entraînent que G est le graphe d'un ordre sur E.  Conjonction des trois
    propriétés certifiées ci-dessus.  CLOS sous les seules conditions a), b)
    (le champ G⊆E×E n'est pas load-bearing — voir docstring du module).

    Liants « u, v, s » par DÉFAUT (≠ « x » laissé libre par graphe_identite dans
    la condition b) ; la conclusion est est_ordre(G,E,u,v,s), structurellement
    identique à est_ordre(G,E) au renommage près des variables muettes."""
    refl = reciproque_reflexivite(g, e, x)
    antis = reciproque_antisymetrie(g, e, x, y)
    trans = reciproque_transitivite(g, e, x, y, z)
    # est_ordre(G,E,x,y,z) = (reflexivite_sur(G,E,x) et antisymetrie(G,x,y)) et transitivite_rel(G,x,y,z)
    return conjonction_intro(conjonction_intro(refl, antis), trans)


# ════════════════════════════════════════════════════════════════════════════
#  ÉQUIVALENCE COMPLÈTE — Proposition 1 (E.III.2), « il faut et il suffit »
# ════════════════════════════════════════════════════════════════════════════
def _renomme_est_ordre(g, e, x="u", y="v", z="s"):
    """{ est_ordre(G,E,x,y,z) } ⊢ est_ordre(G,E)   (renommage des liants → x,y,z par défaut).

    Le sens direct (caracterisation_ordre_sens_direct) raisonne sur est_ordre(G,E)
    avec liants par défaut x,y,z ; la réciproque conclut est_ordre(G,E,u,v,s).  Ces
    deux formules ne diffèrent QUE par le nom des variables muettes ; ici on
    re-généralise composante par composante (l'hypothèse est_ordre(G,E,u,v,s) n'a
    pour libres que G, E, donc C27 sur x,y,z est licite)."""
    vG, vE = _t(g), _t(e)
    H = N.assume(est_ordre(vG, vE, x, y, z))                   # est_ordre(G,E,u,v,s)
    refl_s = conjonction_elim_gauche(conjonction_elim_gauche(H))   # (∀u)(u∈E⇒(u,u)∈G)
    antis_s = conjonction_elim_droite(conjonction_elim_gauche(H))  # (∀u)(∀v)(...)
    trans_s = conjonction_elim_droite(H)                       # (∀u)(∀v)(∀s)(...)
    # réflexivité : instancie en x, re-généralise sur x
    refl = N.generalisation("x", instancie(refl_s, var("x")))
    # antisymétrie : instancie en x,y, re-généralise sur x,y
    antis = N.generalisation("x", N.generalisation("y",
        instancie(instancie(antis_s, var("x")), var("y"))))
    # transitivité : instancie en x,y,z, re-généralise sur x,y,z
    trans = N.generalisation("x", N.generalisation("y", N.generalisation("z",
        instancie(instancie(instancie(trans_s, var("x")), var("y")), var("z")))))
    return conjonction_intro(conjonction_intro(refl, antis), trans)   # est_ordre(G,E) défaut


def proposition1_equivalence(g="G", e="E"):
    """{ champ(G,E) } ⊢ ( est_ordre(G,E)  ⇔  (composee(G,G)=G et inter(G,G⁻¹)=Δ_E) ).

    L'ÉNONCÉ COMPLET « il faut et il suffit » de la Proposition 1, sous la seule
    hypothèse de champ G⊆E×E (qui n'est requise QUE par le sens direct ; la
    réciproque n'en a pas besoin).  est_ordre(G,E) y est avec ses liants par défaut.
      ⇒ (nécessité) : caracterisation_ordre_sens_direct ; on décharge est_ordre(G,E),
         reste champ(G,E).
      ⇐ (suffisance) : caracterisation_ordre_reciproque (liants u,v,s) renommée en
         est_ordre(G,E) par défaut (_renomme_est_ordre), conjonction déchargée.
    conjonction_intro des deux implications = equiv(...)  (equiv = et(⇒,⇐))."""
    vG, vE = _t(g), _t(e)
    direct = caracterisation_ordre_sens_direct(g, e)             # { est_ordre(G,E), champ } ⊢ conds
    conds = direct.conclusion                                   # composee(G,G)=G et inter(G,G⁻¹)=Δ_E
    ordre = est_ordre(vG, vE)                                   # est_ordre(G,E) liants par défaut

    # ── ⇒  (nécessité) : { champ } ⊢ est_ordre(G,E) ⇒ conds ───────────────────
    fwd = N.loi_deduction(ordre, direct)                         # { champ } ⊢ est_ordre ⇒ conds

    # ── ⇐  (suffisance) : ⊢ conds ⇒ est_ordre(G,E) ────────────────────────────
    recip = caracterisation_ordre_reciproque(g, e)              # { condA, condB } ⊢ est_ordre(G,E,u,v,s)
    # renomme la conclusion u,v,s → liants par défaut x,y,z (cut du lemme)
    ren = _renomme_est_ordre(g, e)                             # { est_ordre(G,E,u,v,s) } ⊢ est_ordre(G,E)
    recip = N.modus_ponens(recip, N.loi_deduction(recip.conclusion, ren))   # { condA, condB } ⊢ est_ordre(G,E)
    # décharge les deux conditions
    Hconds = N.assume(conds)                                     # condA et condB
    condA = conjonction_elim_gauche(Hconds)                     # composee(G,G)=G
    condB = conjonction_elim_droite(Hconds)                     # inter(G,G⁻¹)=Δ_E
    recip = N.modus_ponens(condA, N.loi_deduction(condA.conclusion, recip))
    recip = N.modus_ponens(condB, N.loi_deduction(condB.conclusion, recip))
    bwd = N.loi_deduction(conds, recip)                         # ⊢ conds ⇒ est_ordre(G,E)

    return conjonction_intro(fwd, bwd)                          # est_ordre(G,E) ⇔ conds


__all__ = [
    "reciproque_transitivite",
    "reciproque_antisymetrie",
    "reciproque_reflexivite",
    "caracterisation_ordre_reciproque",
    "proposition1_equivalence",
]
