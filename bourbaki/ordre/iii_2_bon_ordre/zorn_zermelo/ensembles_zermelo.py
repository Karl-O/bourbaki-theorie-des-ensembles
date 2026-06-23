"""Chapitre III §2 — THÉORÈME DE ZERMELO (Théorème 1) : « tout ensemble peut être
bien ordonné », E.III.2, via le THÉORÈME DE ZORN.

Module NEUF.  Il vise

    zermelo(X) :  (∃R) est_bien_ordonne(R, X)

(tout ensemble X admet un bon ordre).  On CALQUE la structure d'assemblage de
`ensembles_comparabilite.py` (Zorn sur un poset construit par un axiome de
sélection DÉDIÉ + une réunion DÉDIÉE), mais avec une difficulté SUPÉRIEURE : ici
la réunion d'une chaîne doit non pas « injecter » mais BIEN ORDONNER.

RECETTE (Zermelo ⇐ Zorn par le POSET DES BONS ORDRES PARTIELS) :
  1. Un BON ORDRE PARTIEL de X est un graphe G⊂X×X qui est une relation de bon
     ordre sur son CHAMP A=champ(G).  Plus précisément on encode le couple
     (A,R) bourbakien par le seul graphe G (A se relit comme champ(G), R comme
     « (a,b)∈G »).  W := { G | bon_ordre_partiel(G,X) }.
     [terme opaque + axiome DÉFINITIONNEL ; motif axiome_Inj / axiome_P.]
  2. L'ordre sur W est l'END-EXTENSION Θ : G ⊴ H ssi  G⊂H  ET  champ(G) est un
     SEGMENT INITIAL de (champ(H), H) :  (∀a∈champ G)(∀y∈champ H)((y,a)∈H ⇒
     y∈champ G).   [terme opaque + axiome DÉFINITIONNEL.]
  3. (Θ,W) est INDUCTIF : une Θ-chaîne 𝔇 de bons ordres partiels a pour majorant
     l'UNION ⋃𝔇, qui est ENCORE un bon ordre partiel.  [LE CŒUR — bien plus dur
     que comparabilité : il faut prouver que ⋃𝔇 BIEN ORDONNE son champ.]
  4. ZORN : (∃M) element_maximal(Θ,W,M).
  5. champ(M)=X PAR L'ABSURDE : sinon x∈X∖champ M ; on étend M en mettant x AU
     SOMMET → bon ordre partiel STRICTEMENT plus grand → contredit la maximalité.
  6. CONCLUSION : M bien ordonne champ(M)=X ⇒ (∃R) est_bien_ordonne(R,X).

INVARIANT : theorie_ensembles() reste = 22 (axiomes de W/Θ/Union en théories
DÉDIÉES, motif Inj/Γ/Union).  Rien n'est postulé : le bon ordre est CONSTRUIT,
jamais supposé.  🚫 JAMAIS postuler le bon ordre.

NOTATIONS :  (a,b)∈G := appartient(couple(a,b),G) ;  G⊂H := inclus(G,H).
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (
    Terme, var, egal, et, ou, non, impl, equiv, appartient, existe, pourtout, inclus, tau,
)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege import a_implique_a, syllogisme
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    contraposition, cas, tiers_exclu, equivalence_avant, equivalence_arriere,
    equivalence_symetrie, equivalence_transitivite, instancie,
)
from bourbaki.logique.i_3_quantifies.tactiques_abrege_quantif import (
    existe_elimination, congruence_existe, alpha_existe, monotonie_existe,
)
from bourbaki.logique.i_4_egalitaires.tactiques_abrege_egalite import symetrie as _sym


# Trou de substitution Leibniz GARANTI FRAIS pour ce module.
_H = "hole_leibniz_zermelo"


def _terme(t):
    return t if isinstance(t, Terme) else var(t)


def _dans(a, b, G):
    """Formule « (a,b)∈G »."""
    return appartient(E.couple(_terme(a), _terme(b)), _terme(G))


def _cut(thm, hyp, preuve_hyp):
    """De Γ∪{H}⊢C et Δ⊢H, déduit Γ∪Δ⊢C (décharge de H puis MP)."""
    return N.modus_ponens(preuve_hyp, N.loi_deduction(hyp, thm))


def _incl_refl(t):
    """⊢ t⊂t  pour un TERME t."""
    from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege import inclusion_reflexive
    th = inclusion_reflexive("_r")
    return instancie(N.generalisation("_r", th), _terme(t))


def _incl_trans(a, b, c, ab, bc):
    """De ⊢ a⊂b [ab] et ⊢ b⊂c [bc] (TERMES) déduit ⊢ a⊂c (avec le binder canonique)."""
    from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import _peler_pourtout
    va, vb, vc = _terme(a), _terme(b), _terme(c)
    cible = inclus(va, vc)
    bndr, _ = _peler_pourtout(cible)
    zt = var(bndr)
    hz = N.assume(appartient(zt, va))
    z_in_b = N.modus_ponens(hz, instancie(ab, zt))
    z_in_c = N.modus_ponens(z_in_b, instancie(bc, zt))
    body = N.loi_deduction(appartient(zt, va), z_in_c)
    return N.generalisation(bndr, body)


def _ou_gauche(thm_p, q):
    """De ⊢ P, déduit ⊢ (P OU Q)."""
    return N.modus_ponens(thm_p, N.s2(thm_p.conclusion, q))


def _ou_droite(thm_q, p):
    """De ⊢ Q, déduit ⊢ (P OU Q)."""
    q = thm_q.conclusion
    return N.modus_ponens(N.modus_ponens(thm_q, N.s2(q, p)), N.s3(q, p))


# ════════════════════════════════════════════════════════════════════════════
#  Le CHAMP d'un graphe G :  champ(G) := dom(G) ∪ img(G)  (sommets reliés par G).
#  Et le PRÉDICAT « G est un bon ordre partiel de X ».
# ════════════════════════════════════════════════════════════════════════════
def champ(G):
    """champ(G) := dom(G) ∪ img(G)  (l'ensemble des sommets touchés par G)."""
    return E.reunion(E.dom(_terme(G)), E.img(_terme(G)))


def R_de(G):
    """La relation (a,b)↦(a,b)∈G  associée au graphe G  (R-as-function bourbakien)."""
    vG = _terme(G)
    return lambda a, b: appartient(E.couple(_terme(a), _terme(b)), vG)


def bon_ordre_partiel(G, X, x="x", y="y", z="z", S="S", a="a", w="w"):
    """bon_ordre_partiel(G,X) := G⊂X×X  ET  est_bien_ordonne(R_G, champ(G)).

    « G est (le graphe d')un bon ordre partiel de X » : un graphe inclus dans X×X
    qui est une relation de bon ordre sur son propre champ A=champ(G).  Le couple
    (A,R) de Bourbaki est ainsi encodé par le seul graphe G (A=champ(G))."""
    vG, vX = _terme(G), _terme(X)
    A = champ(vG)
    bo = E.est_bien_ordonne(R_de(vG), A, x, y, z, S, a, w)
    return et(inclus(vG, E.produit(vX, vX)), bo)


# ════════════════════════════════════════════════════════════════════════════
#  ÉTAPE 1 — le POSET DES BONS ORDRES PARTIELS :
#  W := { G ∈ 𝔓(X×X) | bon_ordre_partiel(G,X) }
#  Terme opaque + axiome DÉFINITIONNEL (S8+A1, motif axiome_Inj).
#  theorie_ensembles() reste INCHANGÉE = 22.
# ════════════════════════════════════════════════════════════════════════════
def W(X):
    """W(X) := { G | bon_ordre_partiel(G,X) }  (les bons ordres partiels de X)."""
    return E.app("zermelo_W", _terme(X))


def axiome_W(X="X", G="G"):
    """⊢-schéma (∀X G)( G∈W ⇔ bon_ordre_partiel(G,X) ).

    Axiome DÉFINITIONNEL du poset des bons ordres partiels (sélection S8 dans
    𝔓(X×X), unicité A1 ; motif axiome_Inj).  N'altère PAS theorie_ensembles()."""
    vX, vG = var(X), var(G)
    return pourtout(X, pourtout(G,
        equiv(appartient(vG, W(vX)), bon_ordre_partiel(vG, vX))))


def theorie_W(X="X", G="G"):
    """Théorie DÉDIÉE ne contenant que l'axiome de W (E.III.2, Zermelo, ÉTAPE 1)."""
    return N.Theorie("W-Zermelo", [axiome_W(X, G)])


def _inst_W(X, G):
    """⊢ ( G∈W ⇔ bon_ordre_partiel(G,X) )   (axiome instancié aux TERMES)."""
    ax = N.axiome(theorie_W(), axiome_W())
    for tm in (X, G):
        ax = instancie(ax, _terme(tm))
    return ax


def W_membre(X="X", G="G"):
    """⊢ ( G∈W ) ⇔ bon_ordre_partiel(G,X)."""
    return _inst_W(var(X), var(G))


# ════════════════════════════════════════════════════════════════════════════
#  Le GRAPHE D'ORDRE Θ (END-EXTENSION) sur W :
#  (G,H)∈Θ ⇔ ( G∈W et H∈W et G⊂H et seg_initial(G,H) )
#  où seg_initial(G,H) := (∀a)(∀y)((a∈champ G et (y,a)∈H) ⇒ a∈champ G ... )
#  Terme opaque + axiome DÉFINITIONNEL.
# ════════════════════════════════════════════════════════════════════════════
def seg_initial(G, H, a="p", y="q"):
    """seg_initial(G,H) := (∀p)(∀q)((p∈champ G et (q,p)∈H) ⇒ q∈champ G).

    « champ(G) est un segment initial de (champ H, H) » : tout H-prédécesseur q
    d'un point p de champ(G) est déjà dans champ(G).  (END-EXTENSION.)  Binders
    « p,q » (≠ x,y des axiomes dom/img) pour éviter toute capture."""
    vG = _terme(G)
    va, vy = var(a), var(y)
    A = champ(vG)
    return pourtout(a, pourtout(y,
        impl(et(appartient(va, A), _dans(vy, va, H)), appartient(vy, A))))


def Theta(X):
    """Θ(X) := { (G,H) | G∈W et H∈W et G⊂H et seg_initial(G,H) }  (end-extension)."""
    return E.app("zermelo_Theta", _terme(X))


def _corps_Theta(X, G, H):
    """Corps de Θ :  G∈W et H∈W et G⊂H et seg_initial(G,H)."""
    vW = W(_terme(X))
    return et(et(et(appartient(_terme(G), vW), appartient(_terme(H), vW)),
                 inclus(_terme(G), _terme(H))),
              seg_initial(G, H))


def axiome_Theta(X="X", G="G", H="H"):
    """⊢-schéma (∀X G H)( (G,H)∈Θ ⇔ (G∈W et H∈W et G⊂H et seg_initial(G,H)) ).

    Axiome DÉFINITIONNEL de l'end-extension sur W (S8+A1).  N'altère PAS
    theorie_ensembles()."""
    vX, vG, vH = var(X), var(G), var(H)
    return pourtout(X, pourtout(G, pourtout(H,
        equiv(appartient(E.couple(vG, vH), Theta(vX)),
              _corps_Theta(vX, vG, vH)))))


def theorie_Theta(X="X", G="G", H="H"):
    """Théorie DÉDIÉE ne contenant que l'axiome de Θ (E.III.2, Zermelo, ÉTAPE 1)."""
    return N.Theorie("Theta-Zermelo", [axiome_Theta(X, G, H)])


def _inst_Theta(X, G, H):
    """⊢ ( (G,H)∈Θ ⇔ (G∈W et H∈W et G⊂H et seg_initial(G,H)) )   (instancié)."""
    ax = N.axiome(theorie_Theta(), axiome_Theta())
    for tm in (X, G, H):
        ax = instancie(ax, _terme(tm))
    return ax


def Theta_membre(X="X", G="G", H="H"):
    """⊢ ( (G,H)∈Θ ) ⇔ ( G∈W et H∈W et G⊂H et seg_initial(G,H) )."""
    return _inst_Theta(var(X), var(G), var(H))


def _tle(G, H, X):
    """Formule « (G,H)∈Θ »  (l'ordre du poset W, end-extension)."""
    return appartient(E.couple(_terme(G), _terme(H)), Theta(_terme(X)))


def _Theta_intro(X, G, H, hGW, hHW, hGH, hseg):
    """De ⊢ G∈W, ⊢ H∈W, ⊢ G⊂H, ⊢ seg_initial(G,H), déduit ⊢ (G,H)∈Θ."""
    corps = conjonction_intro(conjonction_intro(conjonction_intro(hGW, hHW), hGH), hseg)
    return N.modus_ponens(corps, equivalence_arriere(_inst_Theta(X, G, H)))


def _theta_corps(X, G, H, hTheta):
    """De ⊢ (G,H)∈Θ [hTheta] déduit ⊢ (G∈W et H∈W et G⊂H et seg_initial(G,H))."""
    return N.modus_ponens(hTheta, equivalence_avant(_inst_Theta(X, G, H)))


def _theta_incl(X, G, H, hTheta):
    """De ⊢ (G,H)∈Θ [hTheta] déduit ⊢ G⊂H."""
    corps = _theta_corps(X, G, H, hTheta)
    return conjonction_elim_droite(conjonction_elim_gauche(corps))


def _theta_seg(X, G, H, hTheta):
    """De ⊢ (G,H)∈Θ [hTheta] déduit ⊢ seg_initial(G,H)."""
    return conjonction_elim_droite(_theta_corps(X, G, H, hTheta))


# ════════════════════════════════════════════════════════════════════════════
#  Outillage CHAMP : appartenance à dom/img/champ depuis un couple de G.
# ════════════════════════════════════════════════════════════════════════════
def _inst_dom(G, x):
    """⊢ (x∈dom G) ⇔ (∃y)((x,y)∈G)."""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_DOM)
    return instancie(instancie(ax, _terme(G)), _terme(x))


def _inst_img(G, y):
    """⊢ (y∈img G) ⇔ (∃x)((x,y)∈G)."""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_IMG)
    return instancie(instancie(ax, _terme(G)), _terme(y))


def _inst_reunion(A, B, z):
    """⊢ (z∈A∪B) ⇔ (z∈A ou z∈B)."""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_REUNION)
    return instancie(instancie(instancie(ax, _terme(A)), _terme(B)), _terme(z))


def _frais(*termes, base="w"):
    """Nom de variable FRAIS, n'apparaissant libre dans aucun des termes donnés."""
    from bourbaki.logique.i_1_termes_relations.formule import libres_t, _fraiche
    evite = set()
    for t in termes:
        evite |= libres_t(t)
    if base not in evite:
        return base
    return _fraiche(evite)


def _libres_hyps(*thms):
    """Réunion des variables libres des HYPOTHÈSES de chaque théorème donné."""
    from bourbaki.logique.i_1_termes_relations.formule import libres_f
    s = set()
    for th in thms:
        for h in th.hypotheses:
            s |= libres_f(h)
    return s


def _frais_eviter(eviter, *termes, base="z"):
    """Nom de variable FRAIS hors `eviter` ET hors des variables libres des termes."""
    from bourbaki.logique.i_1_termes_relations.formule import libres_t, _fraiche
    ev = set(eviter)
    for t in termes:
        ev |= libres_t(t)
    if base not in ev:
        return base
    return _fraiche(ev)


def _exists_binder(equiv_thm):
    """Renvoie le nom de lieur du PREMIER nœud existentiel dans la conclusion."""
    def find_ex(f):
        if f.lieur and len(f.sous) == 1 and not f.termes:
            return f
        for s in f.sous:
            r = find_ex(s)
            if r is not None:
                return r
        return None
    return find_ex(equiv_thm.conclusion).lieur


def _dom_de_couple(G, a, b, hab):
    """De ⊢ (a,b)∈G [hab] déduit ⊢ a∈dom G  (a a une image).

    Le binder ∃ du domaine peut avoir été α-renommé par l'instanciation (capture
    du graphe) ; on RELIT le binder réel et on l'utilise tel quel via S5."""
    vG, va, vb = _terme(G), _terme(a), _terme(b)
    dom_ax = _inst_dom(vG, va)                                 # (a∈dom G) ⇔ (∃Y)((a,Y)∈G)
    nm = _exists_binder(dom_ax)                                # le binder RÉEL (peut être @k)
    r = appartient(E.couple(va, var(nm)), vG)                 # (a,Y)∈G
    ex = N.modus_ponens(hab, N.s5(r, vb, nm))                 # (∃Y)((a,Y)∈G)
    return N.modus_ponens(ex, equivalence_arriere(dom_ax))     # a∈dom G


def _img_de_couple(G, a, b, hab):
    """De ⊢ (a,b)∈G [hab] déduit ⊢ b∈img G  (b est une valeur)."""
    vG, va, vb = _terme(G), _terme(a), _terme(b)
    img_ax = _inst_img(vG, vb)                                 # (b∈img G) ⇔ (∃X)((X,b)∈G)
    nm = _exists_binder(img_ax)                                # binder RÉEL
    r = appartient(E.couple(var(nm), vb), vG)                 # (X,b)∈G
    ex = N.modus_ponens(hab, N.s5(r, va, nm))                 # (∃X)((X,b)∈G)
    return N.modus_ponens(ex, equivalence_arriere(img_ax))     # b∈img G


def _dom_dans_champ(G, x, hxdom):
    """De ⊢ x∈dom G [hxdom] déduit ⊢ x∈champ G  (= dom G ∪ img G, branche gauche)."""
    vG, vx = _terme(G), _terme(x)
    disj = N.modus_ponens(hxdom, N.s2(appartient(vx, E.dom(vG)), appartient(vx, E.img(vG))))  # x∈dom ∨ x∈img
    return N.modus_ponens(disj, equivalence_arriere(_inst_reunion(E.dom(vG), E.img(vG), vx)))  # x∈champ G


def _img_dans_champ(G, y, hyimg):
    """De ⊢ y∈img G [hyimg] déduit ⊢ y∈champ G  (branche droite de la réunion)."""
    vG, vy = _terme(G), _terme(y)
    disj0 = N.modus_ponens(hyimg, N.s2(appartient(vy, E.img(vG)), appartient(vy, E.dom(vG))))  # y∈img ∨ y∈dom
    disj = N.modus_ponens(N.modus_ponens(disj0, N.s3(appartient(vy, E.img(vG)), appartient(vy, E.dom(vG)))),
                          a_implique_a(ou(appartient(vy, E.dom(vG)), appartient(vy, E.img(vG)))))  # (dom ∨ img)
    return N.modus_ponens(disj, equivalence_arriere(_inst_reunion(E.dom(vG), E.img(vG), vy)))  # y∈champ G


def _couple_dans_champ_gauche(G, a, b, hab):
    """De ⊢ (a,b)∈G [hab] déduit ⊢ a∈champ G."""
    return _dom_dans_champ(G, a, _dom_de_couple(G, a, b, hab))


def _couple_dans_champ_droite(G, a, b, hab):
    """De ⊢ (a,b)∈G [hab] déduit ⊢ b∈champ G."""
    return _img_dans_champ(G, b, _img_de_couple(G, a, b, hab))


def _champ_cas(G, z, hz, but_de_dom, but_de_img):
    """De ⊢ z∈champ G [hz] et deux preuves conditionnelles
       (z∈dom G ⊢ but) [but_de_dom], (z∈img G ⊢ but) [but_de_img], déduit ⊢ but.

    champ G = dom G ∪ img G ; on casse la disjonction z∈dom ∨ z∈img."""
    vG, vz = _terme(G), _terme(z)
    disj = N.modus_ponens(hz, equivalence_avant(_inst_reunion(E.dom(vG), E.img(vG), vz)))  # z∈dom ∨ z∈img
    bd = N.loi_deduction(appartient(vz, E.dom(vG)), but_de_dom)
    bi = N.loi_deduction(appartient(vz, E.img(vG)), but_de_img)
    return cas(disj, bd, bi)


# ════════════════════════════════════════════════════════════════════════════
#  ÉTAPE 1 (suite) — Θ est un ORDRE sur W  (réflexive/antisym/transitive).
# ════════════════════════════════════════════════════════════════════════════
def _seg_initial_refl(G, a="p", y="q"):
    """⊢ seg_initial(G,G).   (réflexivité de l'end-extension : trivial.)

    Si p∈champ G et (q,p)∈G alors q∈dom G ⊂ champ G."""
    vG = _terme(G)
    va, vy = var(a), var(y)
    A = champ(vG)
    Hp = N.assume(et(appartient(va, A), _dans(vy, va, vG)))    # p∈champ G et (q,p)∈G
    ya_G = conjonction_elim_droite(Hp)                         # (q,p)∈G
    y_champ = _couple_dans_champ_gauche(vG, vy, va, ya_G)      # q∈champ G
    body = N.loi_deduction(et(appartient(va, A), _dans(vy, va, vG)), y_champ)
    return N.generalisation(a, N.generalisation(y, body))      # seg_initial(G,G)


def Theta_reflexive_sur(X="X", G="x"):
    """⊢ reflexivite_sur(Θ, W).   = (∀x)( x∈W ⇒ (x,x)∈Θ )."""
    from bourbaki.ordre.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_relation import reflexivite_sur
    vX, vG = var(X), var(G)
    hGW = N.assume(appartient(vG, W(vX)))                      # G∈W
    GG = _incl_refl(vG)                                        # G⊂G
    seg = _seg_initial_refl(vG)                                # seg_initial(G,G)
    GG_Theta = _Theta_intro(vX, vG, vG, hGW, hGW, GG, seg)     # (G,G)∈Θ
    body = N.loi_deduction(appartient(vG, W(vX)), GG_Theta)
    return N.generalisation(G, body)


def Theta_antisymetrique(X="X", G="x", H="y"):
    """⊢ antisymetrie(Θ).   = (∀x∀y)( ((x,y)∈Θ et (y,x)∈Θ) ⇒ x=y ).

    (G,H)∈Θ ⇒ G⊂H ; (H,G)∈Θ ⇒ H⊂G ; A1 donne G=H.  (seg_initial non requis.)"""
    from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_theoremes import extensionnalite_appliquee
    vX, vG, vH = var(X), var(G), var(H)
    hyp = et(_tle(vG, vH, vX), _tle(vH, vG, vX))
    h = N.assume(hyp)
    GH = _theta_incl(vX, vG, vH, conjonction_elim_gauche(h))   # G⊂H
    HG = _theta_incl(vX, vH, vG, conjonction_elim_droite(h))   # H⊂G
    a1 = extensionnalite_appliquee(vG, vH)                     # (G⊂H et H⊂G)⇒G=H
    G_eq_H = N.modus_ponens(conjonction_intro(GH, HG), a1)
    body = N.loi_deduction(hyp, G_eq_H)
    return N.generalisation(G, N.generalisation(H, body))


# ── champ-monotonie : G⊂H ⇒ champ G ⊂ champ H  (INCONDITIONNEL) ───────────────
def champ_monotone(G, H, hGH, z="zc"):
    """De ⊢ G⊂H [hGH] déduit ⊢ champ G ⊂ champ H.

    z∈champ G = z∈dom G ∪ img G ; si z∈dom G, témoin (z,b)∈G⊂H ⇒ z∈dom H ⊂ champ H ;
    si z∈img G, témoin (a,z)∈G⊂H ⇒ z∈img H ⊂ champ H."""
    vG, vH = _terme(G), _terme(H)
    vz = var(z)
    AG = champ(vG)
    hz = N.assume(appartient(vz, AG))                          # z∈champ G
    # noms de témoins FRAIS, n'apparaissant pas libres dans vG/vH/vz  (vG ou vH
    # peuvent ÊTRE la variable « x » ou « y » des axiomes dom/img → collision si
    # on hardcode ces binders ; on relit le binder RÉEL et on choisit wd/wi frais).
    wdn = _frais(vG, vH, vz, base="wd")
    win = _frais(vG, vH, vz, base="wi")
    wd, wi = var(wdn), var(win)
    # z∈dom G ⇒ z∈champ H  (témoin frais « wd » ≠ binders réels des axiomes)
    z_domG = N.assume(appartient(vz, E.dom(vG)))               # z∈dom G
    dom_ax = _inst_dom(vG, vz)
    bd = _exists_binder(dom_ax)                                # binder RÉEL du ∃ dom
    ex_d0 = N.modus_ponens(z_domG, equivalence_avant(dom_ax))  # (∃bd)((z,bd)∈G)
    ex_d = N.modus_ponens(ex_d0, equivalence_avant(
        alpha_existe(bd, wdn, appartient(E.couple(vz, var(bd)), vG))))  # (∃wd)((z,wd)∈G)
    Hwd = N.assume(appartient(E.couple(vz, wd), vG))           # (z,wd)∈G
    zy_H = N.modus_ponens(Hwd, instancie(hGH, E.couple(vz, wd)))   # (z,wd)∈H
    z_domH = _dom_de_couple(vH, vz, wd, zy_H)                  # z∈dom H
    z_champH_d = _dom_dans_champ(vH, vz, z_domH)               # z∈champ H
    ex_imp_d = existe_elimination(N.loi_deduction(appartient(E.couple(vz, wd), vG), z_champH_d), wdn)
    but_d = N.modus_ponens(ex_d, ex_imp_d)                     # z∈champ H  [z∈dom G, G⊂H]
    # z∈img G ⇒ z∈champ H  (témoin frais « wi »)
    z_imgG = N.assume(appartient(vz, E.img(vG)))               # z∈img G
    img_ax = _inst_img(vG, vz)
    bi = _exists_binder(img_ax)                                # binder RÉEL du ∃ img
    ex_i0 = N.modus_ponens(z_imgG, equivalence_avant(img_ax))  # (∃bi)((bi,z)∈G)
    ex_i = N.modus_ponens(ex_i0, equivalence_avant(
        alpha_existe(bi, win, appartient(E.couple(var(bi), vz), vG))))  # (∃wi)((wi,z)∈G)
    Hwi = N.assume(appartient(E.couple(wi, vz), vG))           # (wi,z)∈G
    xz_H = N.modus_ponens(Hwi, instancie(hGH, E.couple(wi, vz)))   # (wi,z)∈H
    z_imgH = _img_de_couple(vH, wi, vz, xz_H)                  # z∈img H
    z_champH_i = _img_dans_champ(vH, vz, z_imgH)               # z∈champ H
    ex_imp_i = existe_elimination(N.loi_deduction(appartient(E.couple(wi, vz), vG), z_champH_i), win)
    but_i = N.modus_ponens(ex_i, ex_imp_i)                     # z∈champ H  [z∈img G, G⊂H]
    z_champH = _champ_cas(vG, vz, hz, but_d, but_i)            # z∈champ H  [z∈champ G, G⊂H]
    body = N.loi_deduction(appartient(vz, AG), z_champH)
    return N.generalisation(z, body)                          # champ G ⊂ champ H


# ── extraction des composantes de bon_ordre_partiel(G,X) ─────────────────────
def _bo_de_W(X, G, hGW):
    """De ⊢ G∈W [hGW] déduit ⊢ bon_ordre_partiel(G,X)."""
    vX, vG = _terme(X), _terme(G)
    return N.modus_ponens(hGW, equivalence_avant(_inst_W(vX, vG)))


def _bien_ordonne_de_W(X, G, hGW):
    """De ⊢ G∈W [hGW] déduit ⊢ est_bien_ordonne(R_G, champ G)."""
    return conjonction_elim_droite(_bo_de_W(X, G, hGW))


def _ordre_dans_de_W(X, G, hGW):
    """De ⊢ G∈W [hGW] déduit ⊢ est_relation_ordre_dans(R_G, champ G)."""
    return conjonction_elim_gauche(_bien_ordonne_de_W(X, G, hGW))


def _antisym_de_W(X, G, hGW):
    """De ⊢ G∈W [hGW] déduit ⊢ ordre_antisymetrique(R_G).

    est_relation_ordre_dans = ((transitif et antisym) et reflexif_implicite) et
    reflexive_dans ; antisym = projection."""
    ord_dans = _ordre_dans_de_W(X, G, hGW)                    # est_relation_ordre_dans(R_G,champ G)
    rel_ordre = conjonction_elim_gauche(ord_dans)             # est_relation_ordre(R_G)
    return conjonction_elim_droite(conjonction_elim_gauche(rel_ordre))  # ordre_antisymetrique(R_G)


def _rel_ordre_de_W(X, G, hGW):
    """De ⊢ G∈W [hGW] déduit ⊢ est_relation_ordre(R_G).

    est_relation_ordre(R) = ((ordre_transitif et ordre_antisym) et reflexif_impl)."""
    return conjonction_elim_gauche(_ordre_dans_de_W(X, G, hGW))


def _transitif_de_W(X, G, hGW):
    """De ⊢ G∈W [hGW] déduit ⊢ ordre_transitif(R_G)."""
    rel_ordre = _rel_ordre_de_W(X, G, hGW)
    return conjonction_elim_gauche(conjonction_elim_gauche(rel_ordre))


def _refl_impl_de_W(X, G, hGW):
    """De ⊢ G∈W [hGW] déduit ⊢ ordre_reflexif_implicite(R_G)
       = (∀x∀y)((x,y)∈G ⇒ ((x,x)∈G et (y,y)∈G))."""
    return conjonction_elim_droite(_rel_ordre_de_W(X, G, hGW))


def _refl_dans_de_W(X, G, hGW):
    """De ⊢ G∈W [hGW] déduit ⊢ est_reflexive_dans_ordre(R_G, champ G)
       = (∀x)((x,x)∈G ⇔ x∈champ G)."""
    return conjonction_elim_droite(_ordre_dans_de_W(X, G, hGW))


def _moindre_de_W(X, G, hGW, S="S", a="a", w="w"):
    """De ⊢ G∈W [hGW] déduit ⊢ (∀S)((S⊂champ G et ¬(S=∅)) ⇒ (∃a)(a∈S et (∀w)(w∈S⇒(a,w)∈G))).

    La 2e composante de est_bien_ordonne : toute partie non vide du champ a un plus
    petit élément."""
    return conjonction_elim_droite(_bien_ordonne_de_W(X, G, hGW))


def _leib_eq(a, b, h_ab, phi_fun):
    """De ⊢ a=b [h_ab] déduit ⊢ ( Φ[a] ⇔ Φ[b] )  via S6 (trou _H)."""
    va, vb = _terme(a), _terme(b)
    return N.modus_ponens(h_ab, N.s6(va, vb, _H, phi_fun(var(_H))))


def _leib_transport(a, b, h_ab, phi_fun, h_phi_a):
    """De ⊢ a=b [h_ab] et ⊢ Φ[a] [h_phi_a] déduit ⊢ Φ[b]."""
    return N.modus_ponens(h_phi_a, equivalence_avant(_leib_eq(a, b, h_ab, phi_fun)))


def _paire_membre(u, v, z):
    """⊢ (z∈{u,v}) ⇔ (z=u ou z=v)."""
    from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_theoremes import _instance_paire
    return _instance_paire(_terme(u), _terme(v), _terme(z))


def _doubleton_inclus_champ(X, H, u, v, hu, hv, z="zd"):
    """{ u∈champ H [hu], v∈champ H [hv] } ⊢ {u,v} ⊂ champ H.

    z∈{u,v} ⇒ z=u ou z=v ; dans chaque cas z∈champ H par Leibniz."""
    from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import _peler_pourtout
    vH, vu, vv = _terme(H), _terme(u), _terme(v)
    AH = champ(vH)
    cible = inclus(E.paire(vu, vv), AH)
    bndr, _ = _peler_pourtout(cible)                         # binder canonique de ⊂
    z = bndr
    vz = var(z)
    hz = N.assume(appartient(vz, E.paire(vu, vv)))            # z∈{u,v}
    disj = N.modus_ponens(hz, equivalence_avant(_paire_membre(vu, vv, vz)))  # z=u ou z=v
    # z=u ⇒ z∈champ H
    Hzu = N.assume(egal(vz, vu))
    zu_champ = _leib_transport(vu, vz, N.modus_ponens(Hzu, _sym(vz, vu)),
                               lambda wq: appartient(wq, AH), hu)  # z∈champ H
    bu = N.loi_deduction(egal(vz, vu), zu_champ)
    # z=v ⇒ z∈champ H
    Hzv = N.assume(egal(vz, vv))
    zv_champ = _leib_transport(vv, vz, N.modus_ponens(Hzv, _sym(vz, vv)),
                               lambda wq: appartient(wq, AH), hv)
    bv = N.loi_deduction(egal(vz, vv), zv_champ)
    z_champ = cas(disj, bu, bv)                               # z∈champ H
    body = N.loi_deduction(appartient(vz, E.paire(vu, vv)), z_champ)
    return N.generalisation(z, body)                          # {u,v}⊂champ H


def _doubleton_non_vide(u, v):
    """⊢ ¬({u,v}=∅).   (u∈{u,v} mais u∉∅ si {u,v}=∅ ⇒ contradiction.)"""
    from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_theoremes import appartient_paire_gauche, vide_sans_element
    from bourbaki.ordre.iii_2_bon_ordre.zorn_zermelo.ensembles_bourbaki_witt_chaine import _ex_falso, _refute_self
    vu, vv = _terme(u), _terme(v)
    u_in = appartient_paire_gauche_t(vu, vv)                  # u∈{u,v}
    Heq = N.assume(egal(E.paire(vu, vv), E.VIDE))             # {u,v}=∅
    u_vide = _leib_transport(E.paire(vu, vv), E.VIDE, Heq,
                             lambda wq: appartient(vu, wq), u_in)  # u∈∅
    not_u_vide = vide_sans_element_t(vu)                      # ¬(u∈∅)
    falso = _ex_falso(u_vide, not_u_vide, non(egal(E.paire(vu, vv), E.VIDE)))
    return _refute_self(N.loi_deduction(egal(E.paire(vu, vv), E.VIDE), falso))


def appartient_paire_gauche_t(u, v):
    """⊢ u∈{u,v}  pour des TERMES u,v."""
    from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_theoremes import _instance_paire
    vu, vv = _terme(u), _terme(v)
    c = _instance_paire(vu, vv, vu)                          # u∈{u,v} ⇔ (u=u ∨ u=v)
    oraa = N.modus_ponens(N.reflexivite(vu), N.s2(egal(vu, vu), egal(vu, vv)))
    return N.modus_ponens(oraa, equivalence_arriere(c))


def appartient_paire_droite_t(u, v):
    """⊢ v∈{u,v}  pour des TERMES u,v."""
    from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_theoremes import _instance_paire
    vu, vv = _terme(u), _terme(v)
    c = _instance_paire(vu, vv, vv)                          # v∈{u,v} ⇔ (v=u ∨ v=v)
    bb = N.modus_ponens(N.reflexivite(vv), N.s2(egal(vv, vv), egal(vv, vu)))
    orba = N.modus_ponens(bb, N.s3(egal(vv, vv), egal(vv, vu)))
    return N.modus_ponens(orba, equivalence_arriere(c))


def vide_sans_element_t(u):
    """⊢ ¬(u∈∅)  pour un TERME u."""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_VIDE)
    return instancie(ax, _terme(u))


def totalite_de_W(X, H, u, v, hHW, hu, hv, a="aw", w="ww"):
    """{ H∈W [hHW], u∈champ H [hu], v∈champ H [hv] } ⊢ ( (u,v)∈H ou (v,u)∈H ).

    🔑 TOTALITÉ d'un bon ordre : {u,v}⊂champ H non vide a un plus petit élément
    'a' (R_H-minimal) ; a∈{u,v} ⇒ a=u ou a=v ; a minore u et v ; si a=u alors
    (u,v)∈H, si a=v alors (v,u)∈H."""
    vH, vu, vv = _terme(H), _terme(u), _terme(v)
    AH = champ(vH)
    P = E.paire(vu, vv)
    but = ou(_dans(vu, vv, vH), _dans(vv, vu, vH))
    # {u,v}⊂champ H et ¬({u,v}=∅)
    P_sub = _doubleton_inclus_champ(X, H, u, v, hu, hv)        # {u,v}⊂champ H  [hu,hv]
    P_nv = _doubleton_non_vide(u, v)                          # ¬({u,v}=∅)
    # least element : (∀S)((S⊂champ H et ¬(S=∅)) ⇒ (∃a)(a∈S et (∀w)(w∈S⇒(a,w)∈H)))
    moindre = _moindre_de_W(X, H, hHW)                        # [hHW]
    moindre_P = instancie(moindre, P)                        # (S:=P)
    ex_min = N.modus_ponens(conjonction_intro(P_sub, P_nv), moindre_P)  # (∃a)(a∈P et (∀w)(w∈P⇒(a,w)∈H))
    # α-renomme le binder du ∃ (lieur « a » de est_bien_ordonne) vers `a`(=aw)
    R_a = et(appartient(var("a"), P),
             pourtout("w", impl(appartient(var("w"), P), _dans(var("a"), var("w"), vH))))
    ex_min = N.modus_ponens(ex_min, equivalence_avant(alpha_existe("a", a, R_a)))
    va = var(a)
    R_aw = et(appartient(va, P),
              pourtout("w", impl(appartient(var("w"), P), _dans(va, var("w"), vH))))
    Hmin = N.assume(R_aw)                                    # a∈P et (∀w)(w∈P⇒(a,w)∈H)
    a_in_P = conjonction_elim_gauche(Hmin)                   # a∈P
    a_min = conjonction_elim_droite(Hmin)                    # (∀w)(w∈P⇒(a,w)∈H)
    u_in_P = appartient_paire_gauche_t(vu, vv)               # u∈{u,v}
    v_in_P = appartient_paire_droite_t(vu, vv)               # v∈{u,v}
    a_u = N.modus_ponens(u_in_P, instancie(a_min, vu))       # (a,u)∈H
    a_v = N.modus_ponens(v_in_P, instancie(a_min, vv))       # (a,v)∈H
    # a∈{u,v} ⇒ a=u ou a=v
    disj = N.modus_ponens(a_in_P, equivalence_avant(_paire_membre(vu, vv, va)))  # a=u ou a=v
    # a=u : (a,v)∈H et a=u ⇒ (u,v)∈H ⇒ gauche
    Hau = N.assume(egal(va, vu))
    uv_H = _leib_transport(va, vu, Hau, lambda wq: _dans(wq, vv, vH), a_v)  # (u,v)∈H
    b_u = N.loi_deduction(egal(va, vu), _ou_gauche(uv_H, _dans(vv, vu, vH)))
    # a=v : (a,u)∈H et a=v ⇒ (v,u)∈H ⇒ droite
    Hav = N.assume(egal(va, vv))
    vu_H = _leib_transport(va, vv, Hav, lambda wq: _dans(wq, vu, vH), a_u)  # (v,u)∈H
    b_v = N.loi_deduction(egal(va, vv), _ou_droite(vu_H, _dans(vu, vv, vH)))
    res = cas(disj, b_u, b_v)                                # but  [Hmin,…]
    wit_imp = N.loi_deduction(R_aw, res)
    ex_imp = existe_elimination(wit_imp, a)                  # (∃a)R ⇒ but
    return N.modus_ponens(ex_min, ex_imp)                    # but  [hHW,hu,hv]


# ── seg_initial transitive (le pas dur de l'end-extension), via totalité ─────
def _seg_initial_trans(X, G, H, K, hGW, hHW, hKW, hGH, hHK, hsegGH, hsegHK, p="p", q="q"):
    """{ G∈W, H∈W, K∈W, G⊂H, H⊂K, seg_initial(G,H), seg_initial(H,K) }
       ⊢ seg_initial(G,K).

    Soit p∈champ G et (q,p)∈K.  (1) champ G ⊂ champ H (champ_monotone, G⊂H) ⇒
    p∈champ H.  (2) seg_initial(H,K) : p∈champ H et (q,p)∈K ⇒ q∈champ H.  (3) H
    total sur champ H (totalite_de_W) : (q,p)∈H ou (p,q)∈H.
      • (q,p)∈H : seg_initial(G,H) avec p∈champ G ⇒ q∈champ G.  ✓
      • (p,q)∈H ⊂ K : alors (p,q)∈K et (q,p)∈K ; K antisym (antisym_de_W) ⇒ p=q ;
        donc q=p∈champ G.  ✓"""
    vX, vG, vH, vK = _terme(X), _terme(H), _terme(H), _terme(K)
    vG, vH, vK = _terme(G), _terme(H), _terme(K)
    AG = champ(vG)
    AH = champ(vH)
    vp, vq = var(p), var(q)
    # corps : (p∈champ G et (q,p)∈K) ⇒ q∈champ G
    Hp = N.assume(et(appartient(vp, AG), _dans(vq, vp, vK)))   # p∈champ G et (q,p)∈K
    p_champG = conjonction_elim_gauche(Hp)                     # p∈champ G
    qp_K = conjonction_elim_droite(Hp)                         # (q,p)∈K
    # (1) p∈champ H
    cm = champ_monotone(vG, vH, hGH)                          # champ G ⊂ champ H   [G⊂H]
    p_champH = N.modus_ponens(p_champG, instancie(cm, vp))    # p∈champ H
    # (2) q∈champ H  via seg_initial(H,K)
    segHK_inst = instancie(instancie(hsegHK, vp), vq)         # (p∈champ H et (q,p)∈K)⇒q∈champ H
    q_champH = N.modus_ponens(conjonction_intro(p_champH, qp_K), segHK_inst)  # q∈champ H
    # (3) totalité de H : (q,p)∈H ou (p,q)∈H
    tot = totalite_de_W(vX, vH, vq, vp, hHW, q_champH, p_champH)  # (q,p)∈H ou (p,q)∈H
    but = appartient(vq, AG)                                  # q∈champ G
    # branche (q,p)∈H : seg_initial(G,H) ⇒ q∈champ G
    Hqp_H = N.assume(_dans(vq, vp, vH))                       # (q,p)∈H
    segGH_inst = instancie(instancie(hsegGH, vp), vq)         # (p∈champ G et (q,p)∈H)⇒q∈champ G
    q_champG_1 = N.modus_ponens(conjonction_intro(p_champG, Hqp_H), segGH_inst)
    b1 = N.loi_deduction(_dans(vq, vp, vH), q_champG_1)
    # branche (p,q)∈H : (p,q)∈K (H⊂K) et (q,p)∈K ⇒ K antisym ⇒ p=q ⇒ q∈champ G
    Hpq_H = N.assume(_dans(vp, vq, vH))                       # (p,q)∈H
    pq_K = N.modus_ponens(Hpq_H, instancie(hHK, E.couple(vp, vq)))  # (p,q)∈K
    antiK = _antisym_de_W(vX, vK, hKW)                        # ordre_antisymetrique(R_K)
    anti_inst = instancie(instancie(antiK, vp), vq)          # ((p,q)∈K et (q,p)∈K)⇒p=q
    p_eq_q = N.modus_ponens(conjonction_intro(pq_K, qp_K), anti_inst)  # p=q
    q_eq_p = N.modus_ponens(p_eq_q, _sym(vp, vq))            # q=p
    q_champG_2 = _leib_transport(vp, vq, p_eq_q, lambda wq: appartient(wq, AG), p_champG)  # q∈champ G
    b2 = N.loi_deduction(_dans(vp, vq, vH), q_champG_2)
    q_champG = cas(tot, b1, b2)                              # q∈champ G  [Hp, hyps]
    body = N.loi_deduction(et(appartient(vp, AG), _dans(vq, vp, vK)), q_champG)
    return N.generalisation(p, N.generalisation(q, body))    # seg_initial(G,K)


def _theta_gauche_corps(X, G, H, hTheta):
    """De ⊢ (G,H)∈Θ déduit ⊢ G∈W."""
    corps = _theta_corps(X, G, H, hTheta)
    return conjonction_elim_gauche(conjonction_elim_gauche(conjonction_elim_gauche(corps)))


def _theta_droite_corps(X, G, H, hTheta):
    """De ⊢ (G,H)∈Θ déduit ⊢ H∈W."""
    corps = _theta_corps(X, G, H, hTheta)
    return conjonction_elim_droite(conjonction_elim_gauche(conjonction_elim_gauche(corps)))


def Theta_transitive(X="X", G="x", H="y", K="z"):
    """⊢ transitivite_rel(Θ).   = (∀x∀y∀z)( ((x,y)∈Θ et (y,z)∈Θ) ⇒ (x,z)∈Θ ).

    🔑 LE PAS DUR de l'end-extension : on extrait G∈W,H∈W,K∈W,G⊂H,H⊂K,
    seg_initial(G,H),seg_initial(H,K) des deux corps Θ, on obtient G⊂K (⊂
    transitive) et seg_initial(G,K) (_seg_initial_trans, via totalité de H et
    antisymétrie de K), puis (G,K)∈Θ.  INCONDITIONNEL."""
    # ⚠ On prouve le CORPS avec des binders INTERNES « Gt,Ht,Kt » qui NE COLLISENT
    # PAS avec la machinerie interne (x,y,z,S,a,w,X,p,q,zd,wd,wi + le binder « z »
    # des inclusions de est_bien_ordonne).  Sinon, p.ex. K=« z » serait libre dans
    # les hypothèses au moment de généraliser le binder « z » du doubleton ⊂.
    # On α-renomme ensuite les trois ∀ vers les noms demandés (x,y,z).
    from bourbaki.logique.i_3_quantifies.tactiques_abrege_quantif import (
        alpha_pour_tout, congruence_pour_tout,
    )
    Gt, Ht, Kt = "Gt", "Ht", "Kt"
    vX, vG, vH, vK = var(X), var(Gt), var(Ht), var(Kt)
    hyp = et(_tle(vG, vH, vX), _tle(vH, vK, vX))
    h = N.assume(hyp)
    hGH_t = conjonction_elim_gauche(h)                       # (G,H)∈Θ
    hHK_t = conjonction_elim_droite(h)                       # (H,K)∈Θ
    GW = _theta_gauche_corps(vX, vG, vH, hGH_t)              # G∈W
    HW = _theta_droite_corps(vX, vG, vH, hGH_t)              # H∈W
    KW = _theta_droite_corps(vX, vH, vK, hHK_t)              # K∈W
    GH = _theta_incl(vX, vG, vH, hGH_t)                      # G⊂H
    HK = _theta_incl(vX, vH, vK, hHK_t)                      # H⊂K
    segGH = _theta_seg(vX, vG, vH, hGH_t)                    # seg_initial(G,H)
    segHK = _theta_seg(vX, vH, vK, hHK_t)                    # seg_initial(H,K)
    GK = _incl_trans(vG, vH, vK, GH, HK)                     # G⊂K
    segGK = _seg_initial_trans(vX, vG, vH, vK, GW, HW, KW, GH, HK, segGH, segHK)  # seg_initial(G,K)
    GK_Theta = _Theta_intro(vX, vG, vK, GW, KW, GK, segGK)   # (G,K)∈Θ
    body = N.loi_deduction(hyp, GK_Theta)
    body3 = N.generalisation(Kt, body)                       # (∀Kt)(…)
    # α-renomme Kt→K (innermost), puis sous ∀Ht et ∀Gt par congruence
    if Kt != K:
        eqK = alpha_pour_tout(Kt, K, body.conclusion)        # (∀Kt)body ⇔ (∀K)body'
        body3 = N.modus_ponens(body3, equivalence_avant(eqK))
    body2 = N.generalisation(Ht, body3)                      # (∀Ht)(∀K)(…)
    if Ht != H:
        _, inner = __import__("bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2",
                              fromlist=["_peler_pourtout"])._peler_pourtout(body2.conclusion)
        eqH = alpha_pour_tout(Ht, H, inner)                  # (∀Ht)inner ⇔ (∀H)inner'
        body2 = N.modus_ponens(body2, equivalence_avant(eqH))
    body1 = N.generalisation(Gt, body2)                      # (∀Gt)(∀H)(∀K)(…)
    if Gt != G:
        _, inner = __import__("bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2",
                              fromlist=["_peler_pourtout"])._peler_pourtout(body1.conclusion)
        eqG = alpha_pour_tout(Gt, G, inner)
        body1 = N.modus_ponens(body1, equivalence_avant(eqG))
    return body1


def Theta_est_ordre(X="X"):
    """⊢ est_ordre(Θ, W).   (L'end-extension Θ est un ordre sur les bons ordres
    partiels de X.)  INCONDITIONNEL — theorie_ensembles()=22.

    réflexivité (Theta_reflexive_sur), antisymétrie (A1, Theta_antisymetrique),
    transitivité (Theta_transitive, via totalité + antisymétrie des membres de W)."""
    refl = Theta_reflexive_sur(X, "x")
    antisym = Theta_antisymetrique(X, "x", "y")
    trans = Theta_transitive(X, "x", "y", "z")
    return conjonction_intro(conjonction_intro(refl, antisym), trans)


# ════════════════════════════════════════════════════════════════════════════
#  ÉTAPE 1 — (Θ,W) est INDUCTIF  (LE CŒUR).  Le majorant d'une Θ-chaîne 𝔇 de
#  bons ordres partiels est l'UNION ⋃𝔇 (réunion des graphes).  ⋃𝔇 = terme opaque
#  + axiome de membership (S8+A1, motif zorn_Union).  theorie_ensembles() = 22.
# ════════════════════════════════════════════════════════════════════════════
def Union(X, D):
    """⋃𝔇 := { w | (∃G)(G∈𝔇 et w∈G) }  (réunion d'une famille 𝔇 de graphes)."""
    return E.app("zermelo_Union", _terme(X), _terme(D))


def _corps_Union(X, D, w, G="G"):
    """Corps de ⋃𝔇 :  (∃G)( G∈𝔇 et w∈G )."""
    vG = var(G)
    return existe(G, et(appartient(vG, _terme(D)), appartient(_terme(w), vG)))


def axiome_Union(X="X", D="D", w="w", G="G"):
    """⊢-schéma (∀X D w)( w∈⋃𝔇 ⇔ (∃G)(G∈𝔇 et w∈G) ).

    Axiome DÉFINITIONNEL de la réunion d'une famille (légitime S8+A1, motif
    reunion_famille / zorn_Union).  N'altère PAS theorie_ensembles()."""
    vX, vD, vw = var(X), var(D), var(w)
    return pourtout(X, pourtout(D, pourtout(w,
        equiv(appartient(vw, Union(vX, vD)), _corps_Union(vX, vD, vw, G)))))


def theorie_Union(X="X", D="D", w="w", G="G"):
    """Théorie DÉDIÉE ne contenant que l'axiome de ⋃𝔇 (E.III.2, Zermelo, ÉTAPE 1)."""
    return N.Theorie("Union-Zermelo", [axiome_Union(X, D, w, G)])


def _inst_Union(X, D, w):
    """⊢ ( w∈⋃𝔇 ⇔ (∃G)(G∈𝔇 et w∈G) )   (axiome instancié aux TERMES)."""
    ax = N.axiome(theorie_Union(), axiome_Union())
    for tm in (X, D, w):
        ax = instancie(ax, _terme(tm))
    return ax


def Union_membre(X="X", D="D", w="w"):
    """⊢ ( w∈⋃𝔇 ) ⇔ ( (∃G)(G∈𝔇 et w∈G) )."""
    return _inst_Union(var(X), var(D), var(w))


def _alpha_ex(thm_ex, src, dst, corps_src):
    """De ⊢ (∃src)corps déduit ⊢ (∃dst)(dst|src)corps  (α-renommage du ∃)."""
    if src == dst:
        return thm_ex
    ren = alpha_existe(src, dst, corps_src)
    return N.modus_ponens(thm_ex, equivalence_avant(ren))


# ── un élément de 𝔇 est un bon ordre partiel (𝔇⊂W) ──────────────────────────
def _bop_de_D(X, D, G, hGD, hDW):
    """{ 𝔇⊂W [hDW], G∈𝔇 [hGD] } ⊢ bon_ordre_partiel(G,X)  (élément de 𝔇 ∈ W)."""
    vX = _terme(X)
    GW = N.modus_ponens(hGD, instancie(hDW, _terme(G)))           # G∈W
    return N.modus_ponens(GW, equivalence_avant(_inst_W(vX, _terme(G))))


def _GW_de_D(X, D, G, hGD, hDW):
    """{ 𝔇⊂W [hDW], G∈𝔇 [hGD] } ⊢ G∈W."""
    return N.modus_ponens(hGD, instancie(hDW, _terme(G)))


# ── (A) ⋃𝔇 ⊂ X×X ────────────────────────────────────────────────────────────
def Union_inclus_produit(X="X", D="D", w="w", G="G"):
    """⊢ { 𝔇⊂W } ⊢ ⋃𝔇 ⊂ X×X.

    Si w∈⋃𝔇, témoin G∈𝔇⊂W donc G⊂X×X (bon ordre partiel), et w∈G ⇒ w∈X×X."""
    from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import _peler_pourtout
    vX, vD = var(X), var(D)
    Ut = Union(vX, vD)
    XX = E.produit(vX, vX)
    cible = inclus(Ut, XX)
    bndr, _ = _peler_pourtout(cible)
    vw = var(bndr)
    HDW = N.assume(inclus(vD, W(vX)))                            # 𝔇⊂W
    hwU = N.assume(appartient(vw, Ut))                           # w∈⋃𝔇
    ex = N.modus_ponens(hwU, equivalence_avant(_inst_Union(vX, vD, vw)))  # (∃G)(G∈𝔇 et w∈G)
    vG = var(G)
    Hw = N.assume(et(appartient(vG, vD), appartient(vw, vG)))
    GD = conjonction_elim_gauche(Hw)                            # G∈𝔇
    wG = conjonction_elim_droite(Hw)                            # w∈G
    bop = _bop_de_D(vX, vD, vG, GD, HDW)                        # bon_ordre_partiel(G,X)
    G_XX = conjonction_elim_gauche(bop)                        # G⊂X×X
    wXX = N.modus_ponens(wG, instancie(G_XX, vw))             # w∈X×X
    wit_imp = N.loi_deduction(et(appartient(vG, vD), appartient(vw, vG)), wXX)
    ex_imp = existe_elimination(wit_imp, G)                     # (∃G)(…) ⇒ w∈X×X
    wXX_final = N.modus_ponens(ex, ex_imp)                     # w∈X×X  [w∈⋃𝔇, 𝔇⊂W]
    body = N.loi_deduction(appartient(vw, Ut), wXX_final)
    return N.generalisation(bndr, body)                        # ⋃𝔇⊂X×X


# ── COMMUN : deux points/couples de ⋃𝔇 sont dans un même membre G* de 𝔇 ───────
def _dans_union(X, D, c, h_in_union):
    """De ⊢ c∈⋃𝔇 [h_in_union], renvoie ⊢ (∃G)(G∈𝔇 et c∈G)."""
    vX, vD = _terme(X), _terme(D)
    return N.modus_ponens(h_in_union, equivalence_avant(_inst_Union(vX, vD, _terme(c))))


def _commun_membre(X, D, hDW, Htot, c1, c2, hc1, hc2, but, G1="Ga", G2="Gb"):
    """{ 𝔇⊂W [hDW], totalement_ordonne(Θ,𝔇) [Htot], c1∈⋃𝔇 [hc1], c2∈⋃𝔇 [hc2] }
       ⊢ but, où `but` se déduit de « ∃G*∈W∩𝔇 contenant c1 ET c2 » via le callback
       but_de(G*, c1_in_Gstar, c2_in_Gstar, G*∈W, G*∈𝔇).

    PREUVE : témoins G1,G2∈𝔇 avec c1∈G1, c2∈G2 ; 𝔇 Θ-total ⇒ (G1,G2)∈Θ ou
    (G2,G1)∈Θ ; (G1,G2)∈Θ ⇒ G1⊂G2 donc c1∈G2, G*=G2 ; sinon G*=G1."""
    vX, vD = _terme(X), _terme(D)
    vc1, vc2 = _terme(c1), _terme(c2)
    comp_D = conjonction_elim_droite(Htot)        # (∀Ga∀Gb)((Ga∈𝔇 et Gb∈𝔇)⇒((Ga,Gb)∈Θ ou (Gb,Ga)∈Θ))
    ex1 = _dans_union(vX, vD, vc1, hc1)           # (∃G)(G∈𝔇 et c1∈G)
    ex2 = _dans_union(vX, vD, vc2, hc2)           # (∃G)(G∈𝔇 et c2∈G)
    ex1 = _alpha_ex(ex1, "G", G1, et(appartient(var("G"), vD), appartient(vc1, var("G"))))
    ex2 = _alpha_ex(ex2, "G", G2, et(appartient(var("G"), vD), appartient(vc2, var("G"))))
    vG1, vG2 = var(G1), var(G2)
    Hw1 = N.assume(et(appartient(vG1, vD), appartient(vc1, vG1)))   # G1∈𝔇 et c1∈G1
    Hw2 = N.assume(et(appartient(vG2, vD), appartient(vc2, vG2)))   # G2∈𝔇 et c2∈G2
    G1D = conjonction_elim_gauche(Hw1)                            # G1∈𝔇
    c1G1 = conjonction_elim_droite(Hw1)                           # c1∈G1
    G2D = conjonction_elim_gauche(Hw2)                            # G2∈𝔇
    c2G2 = conjonction_elim_droite(Hw2)                           # c2∈G2
    comp = N.modus_ponens(conjonction_intro(G1D, G2D),
                          instancie(instancie(comp_D, vG1), vG2))  # (G1,G2)∈Θ ou (G2,G1)∈Θ
    G1W = _GW_de_D(vX, vD, vG1, G1D, hDW)                         # G1∈W
    G2W = _GW_de_D(vX, vD, vG2, G2D, hDW)                         # G2∈W
    # BRANCHE (G1,G2)∈Θ : G1⊂G2 ⇒ c1∈G2 ; G*=G2 contient c1,c2 ; G2∈W ; G2∈𝔇
    H12 = N.assume(_tle(vG1, vG2, vX))
    G1_G2 = _theta_incl(vX, vG1, vG2, H12)                        # G1⊂G2
    c1G2 = N.modus_ponens(c1G1, instancie(G1_G2, vc1))           # c1∈G2
    b1 = N.loi_deduction(_tle(vG1, vG2, vX), but(vG2, c1G2, c2G2, G2W, G2D))
    # BRANCHE (G2,G1)∈Θ : G2⊂G1 ⇒ c2∈G1 ; G*=G1 contient c1,c2 ; G1∈W ; G1∈𝔇
    H21 = N.assume(_tle(vG2, vG1, vX))
    G2_G1 = _theta_incl(vX, vG2, vG1, H21)                        # G2⊂G1
    c2G1 = N.modus_ponens(c2G2, instancie(G2_G1, vc2))           # c2∈G1
    b2 = N.loi_deduction(_tle(vG2, vG1, vX), but(vG1, c1G1, c2G1, G1W, G1D))
    par_cas = cas(comp, b1, b2)                                  # but  [Hw1, Hw2, …]
    wit2 = N.loi_deduction(et(appartient(vG2, vD), appartient(vc2, vG2)), par_cas)
    ex_imp2 = existe_elimination(wit2, G2)                       # (∃G2)(…) ⇒ but   [Hw1,…]
    after2 = N.modus_ponens(ex2, ex_imp2)                       # but   [Hw1,…]
    wit1 = N.loi_deduction(et(appartient(vG1, vD), appartient(vc1, vG1)), after2)
    ex_imp1 = existe_elimination(wit1, G1)                       # (∃G1)(…) ⇒ but
    return N.modus_ponens(ex1, ex_imp1)                         # but   [hDW, Htot, hc1, hc2]


def _couple_dans_union_intro(X, D, G, c, hGD, hcG):
    """De ⊢ G∈𝔇 [hGD] et ⊢ c∈G [hcG] déduit ⊢ c∈⋃𝔇  (introduction réunion)."""
    vX, vD, vG, vc = _terme(X), _terme(D), _terme(G), _terme(c)
    corps_temoin = conjonction_intro(hGD, hcG)                  # G∈𝔇 et c∈G
    R = et(appartient(var("G"), vD), appartient(vc, var("G")))
    ex = N.modus_ponens(corps_temoin, N.s5(R, vG, "G"))        # (∃G)(G∈𝔇 et c∈G)
    return N.modus_ponens(ex, equivalence_arriere(_inst_Union(vX, vD, vc)))  # c∈⋃𝔇


# ── (B) R_⋃𝔇 est TRANSITIVE ──────────────────────────────────────────────────
def Union_transitif(X="X", D="D", a="a", b="b", c="c"):
    """⊢ { 𝔇⊂W, totalement_ordonne(Θ,𝔇) } ⊢ ordre_transitif(R_⋃𝔇).

    = (∀a∀b∀c)(((a,b)∈⋃𝔇 et (b,c)∈⋃𝔇) ⇒ (a,c)∈⋃𝔇).  Les couples (a,b),(b,c)
    sont dans un même membre G*∈W∩𝔇 (_commun_membre) ; G* transitif ⇒ (a,c)∈G*,
    et G*∈𝔇 ⇒ (a,c)∈⋃𝔇."""
    from bourbaki.ordre.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_relation import totalement_ordonne
    vX, vD = var(X), var(D)
    va, vb, vc = var(a), var(b), var(c)
    Ut = Union(vX, vD)
    HDW = N.assume(inclus(vD, W(vX)))
    Htot = N.assume(totalement_ordonne(Theta(vX), vD))
    cab, cbc, cac = E.couple(va, vb), E.couple(vb, vc), E.couple(va, vc)
    hyp = et(appartient(cab, Ut), appartient(cbc, Ut))
    Hpair = N.assume(hyp)
    hc1 = conjonction_elim_gauche(Hpair)                        # (a,b)∈⋃𝔇
    hc2 = conjonction_elim_droite(Hpair)                        # (b,c)∈⋃𝔇

    def but(Gstar, c1_in, c2_in, GW, GD):
        trans = _transitif_de_W(vX, Gstar, GW)                 # ordre_transitif(R_G*)
        inst = instancie(instancie(instancie(trans, va), vb), vc)  # ((a,b)∈G* et (b,c)∈G*)⇒(a,c)∈G*
        ac_G = N.modus_ponens(conjonction_intro(c1_in, c2_in), inst)  # (a,c)∈G*
        return _couple_dans_union_intro(vX, vD, Gstar, cac, GD, ac_G)  # (a,c)∈⋃𝔇

    res = _commun_membre(vX, vD, HDW, Htot, cab, cbc, hc1, hc2, but)   # (a,c)∈⋃𝔇
    body = N.loi_deduction(hyp, res)
    return N.generalisation(a, N.generalisation(b, N.generalisation(c, body)))


# ── (C) R_⋃𝔇 est ANTISYMÉTRIQUE ──────────────────────────────────────────────
def Union_antisymetrique(X="X", D="D", a="a", b="b"):
    """⊢ { 𝔇⊂W, totalement_ordonne(Θ,𝔇) } ⊢ ordre_antisymetrique(R_⋃𝔇).

    = (∀a∀b)(((a,b)∈⋃𝔇 et (b,a)∈⋃𝔇) ⇒ a=b).  Les couples (a,b),(b,a) sont dans
    un même membre G*∈W (_commun_membre) ; G* antisymétrique ⇒ a=b."""
    from bourbaki.ordre.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_relation import totalement_ordonne
    vX, vD = var(X), var(D)
    va, vb = var(a), var(b)
    Ut = Union(vX, vD)
    HDW = N.assume(inclus(vD, W(vX)))
    Htot = N.assume(totalement_ordonne(Theta(vX), vD))
    cab, cba = E.couple(va, vb), E.couple(vb, va)
    hyp = et(appartient(cab, Ut), appartient(cba, Ut))
    Hpair = N.assume(hyp)
    hc1 = conjonction_elim_gauche(Hpair)                        # (a,b)∈⋃𝔇
    hc2 = conjonction_elim_droite(Hpair)                        # (b,a)∈⋃𝔇

    def but(Gstar, c1_in, c2_in, GW, GD):
        anti = _antisym_de_W(vX, Gstar, GW)                    # ordre_antisymetrique(R_G*)
        inst = instancie(instancie(anti, va), vb)             # ((a,b)∈G* et (b,a)∈G*)⇒a=b
        return N.modus_ponens(conjonction_intro(c1_in, c2_in), inst)  # a=b

    res = _commun_membre(vX, vD, HDW, Htot, cab, cba, hc1, hc2, but)   # a=b
    body = N.loi_deduction(hyp, res)
    return N.generalisation(a, N.generalisation(b, body))


# ── (D) R_⋃𝔇 est RÉFLEXIVE-IMPLICITE ─────────────────────────────────────────
def Union_refl_impl(X="X", D="D", a="a", b="b"):
    """⊢ { 𝔇⊂W, totalement_ordonne(Θ,𝔇) } ⊢ ordre_reflexif_implicite(R_⋃𝔇).

    = (∀a∀b)((a,b)∈⋃𝔇 ⇒ ((a,a)∈⋃𝔇 et (b,b)∈⋃𝔇)).  Un seul couple (a,b) : témoin
    G*∈𝔇∩W avec (a,b)∈G* ; G* réflexif-implicite ⇒ (a,a)∈G* et (b,b)∈G* ⊂ ⋃𝔇."""
    vX, vD = var(X), var(D)
    va, vb = var(a), var(b)
    Ut = Union(vX, vD)
    cab = E.couple(va, vb)
    caa, cbb = E.couple(va, va), E.couple(vb, vb)
    HDW = N.assume(inclus(vD, W(vX)))
    hab = N.assume(appartient(cab, Ut))                        # (a,b)∈⋃𝔇
    ex = _dans_union(vX, vD, cab, hab)                        # (∃G)(G∈𝔇 et (a,b)∈G)
    vG = var("G")
    Hw = N.assume(et(appartient(vG, vD), appartient(cab, vG)))
    GD = conjonction_elim_gauche(Hw)                          # G∈𝔇
    abG = conjonction_elim_droite(Hw)                         # (a,b)∈G
    GW = _GW_de_D(vX, vD, vG, GD, HDW)                        # G∈W
    refl = _refl_impl_de_W(vX, vG, GW)                       # (∀x∀y)((x,y)∈G⇒((x,x)∈G et (y,y)∈G))
    inst = instancie(instancie(refl, va), vb)               # (a,b)∈G⇒((a,a)∈G et (b,b)∈G)
    conj = N.modus_ponens(abG, inst)                         # (a,a)∈G et (b,b)∈G
    aaG = conjonction_elim_gauche(conj)                      # (a,a)∈G
    bbG = conjonction_elim_droite(conj)                     # (b,b)∈G
    aaU = _couple_dans_union_intro(vX, vD, vG, caa, GD, aaG)  # (a,a)∈⋃𝔇
    bbU = _couple_dans_union_intro(vX, vD, vG, cbb, GD, bbG)  # (b,b)∈⋃𝔇
    both = conjonction_intro(aaU, bbU)                       # (a,a)∈⋃𝔇 et (b,b)∈⋃𝔇
    wit_imp = N.loi_deduction(et(appartient(vG, vD), appartient(cab, vG)), both)
    ex_imp = existe_elimination(wit_imp, "G")               # (∃G)(…) ⇒ both
    res = N.modus_ponens(ex, ex_imp)                        # both  [(a,b)∈⋃𝔇, 𝔇⊂W]
    body = N.loi_deduction(appartient(cab, Ut), res)
    return N.generalisation(a, N.generalisation(b, body))


# ── reflexive_dans : (x,x)∈⋃𝔇 venant d'un témoin couple sur x dans un G∈𝔇 ─────
def _xx_union_de_champG(X, D, x, G, GD, GW, hxchampG):
    """{ G∈𝔇 [GD], G∈W [GW], x∈champ G [hxchampG] } ⊢ (x,x)∈⋃𝔇.

    G réflexive_dans : (x,x)∈G ⇔ x∈champ G ; sens ⇐ donne (x,x)∈G ; G∈𝔇 ⇒ ⋃."""
    vX, vD, vx, vG = _terme(X), _terme(D), _terme(x), _terme(G)
    refl_dans = _refl_dans_de_W(vX, vG, GW)                  # (∀x)((x,x)∈G ⇔ x∈champ G)
    eqv = instancie(refl_dans, vx)                          # (x,x)∈G ⇔ x∈champ G
    xxG = N.modus_ponens(hxchampG, equivalence_arriere(eqv))  # (x,x)∈G
    return _couple_dans_union_intro(vX, vD, vG, E.couple(vx, vx), GD, xxG)  # (x,x)∈⋃𝔇


# ── (E) R_⋃𝔇 est RÉFLEXIVE DANS champ(⋃𝔇) ────────────────────────────────────
def Union_refl_dans(X="X", D="D", x="x"):
    """⊢ { 𝔇⊂W } ⊢ est_reflexive_dans_ordre(R_⋃𝔇, champ ⋃𝔇).

    = (∀x)((x,x)∈⋃𝔇 ⇔ x∈champ ⋃𝔇).
      ⇒ : (x,x)∈⋃𝔇 ⇒ x∈dom⋃𝔇 ⊂ champ⋃𝔇.
      ⇐ : x∈champ⋃𝔇 = x∈dom⋃𝔇 ∪ img⋃𝔇 ; un témoin couple sur x est dans un G∈𝔇⊂W,
          x∈champ G, G réflexive_dans ⇒ (x,x)∈G ⊂ ⋃𝔇."""
    vX, vD = var(X), var(D)
    vx = var(x)
    Ut = Union(vX, vD)
    AU = champ(Ut)
    cxx = E.couple(vx, vx)
    HDW = N.assume(inclus(vD, W(vX)))                        # 𝔇⊂W
    # ── sens ⇒ : (x,x)∈⋃𝔇 ⇒ x∈champ⋃𝔇 ────────────────────────────────────────
    Hxx = N.assume(appartient(cxx, Ut))                     # (x,x)∈⋃𝔇
    x_champU_fwd = _couple_dans_champ_gauche(Ut, vx, vx, Hxx)  # x∈champ⋃𝔇
    imp_fwd = N.loi_deduction(appartient(cxx, Ut), x_champU_fwd)
    # ── sens ⇐ : x∈champ⋃𝔇 ⇒ (x,x)∈⋃𝔇 ────────────────────────────────────────
    Hxc = N.assume(appartient(vx, AU))                      # x∈champ⋃𝔇
    # cas x∈dom⋃𝔇 : témoin (x,b)∈⋃𝔇 ⇒ (∃G)(G∈𝔇 et (x,b)∈G)
    bd = _frais(vX, vD, vx, base="bd")                      # nom frais pour le 2e point
    vbd = var(bd)
    Hxdom = N.assume(appartient(vx, E.dom(Ut)))             # x∈dom⋃𝔇
    ex_d0 = N.modus_ponens(Hxdom, equivalence_avant(_inst_dom(Ut, vx)))  # (∃·)((x,·)∈⋃𝔇)
    dax = _inst_dom(Ut, vx)
    bdr = _exists_binder(dax)
    ex_d = _alpha_ex(ex_d0, bdr, bd, appartient(E.couple(vx, var(bdr)), Ut))  # (∃bd)((x,bd)∈⋃𝔇)
    Hxb = N.assume(appartient(E.couple(vx, vbd), Ut))      # (x,bd)∈⋃𝔇
    exG_d = _dans_union(vX, vD, E.couple(vx, vbd), Hxb)    # (∃G)(G∈𝔇 et (x,bd)∈G)
    vGd = var("Gd")
    exG_d = _alpha_ex(exG_d, "G", "Gd", et(appartient(var("G"), vD), appartient(E.couple(vx, vbd), var("G"))))
    HwG_d = N.assume(et(appartient(vGd, vD), appartient(E.couple(vx, vbd), vGd)))
    Gd_D = conjonction_elim_gauche(HwG_d)                  # Gd∈𝔇
    xb_Gd = conjonction_elim_droite(HwG_d)                 # (x,bd)∈Gd
    Gd_W = _GW_de_D(vX, vD, vGd, Gd_D, HDW)               # Gd∈W
    x_champGd = _couple_dans_champ_gauche(vGd, vx, vbd, xb_Gd)  # x∈champ Gd
    xxU_d = _xx_union_de_champG(vX, vD, vx, vGd, Gd_D, Gd_W, x_champGd)  # (x,x)∈⋃𝔇
    wit_d = N.loi_deduction(et(appartient(vGd, vD), appartient(E.couple(vx, vbd), vGd)), xxU_d)
    exG_imp_d = existe_elimination(wit_d, "Gd")
    after_Gd = N.modus_ponens(exG_d, exG_imp_d)           # (x,x)∈⋃𝔇  [(x,bd)∈⋃𝔇]
    wit_bd = N.loi_deduction(appartient(E.couple(vx, vbd), Ut), after_Gd)
    ex_imp_bd = existe_elimination(wit_bd, bd)
    but_dom = N.modus_ponens(ex_d, ex_imp_bd)            # (x,x)∈⋃𝔇  [x∈dom⋃𝔇]
    # cas x∈img⋃𝔇 : témoin (a,x)∈⋃𝔇
    ai = _frais(vX, vD, vx, base="ai")
    vai = var(ai)
    Hximg = N.assume(appartient(vx, E.img(Ut)))           # x∈img⋃𝔇
    ex_i0 = N.modus_ponens(Hximg, equivalence_avant(_inst_img(Ut, vx)))  # (∃·)((·,x)∈⋃𝔇)
    iax = _inst_img(Ut, vx)
    ibr = _exists_binder(iax)
    ex_i = _alpha_ex(ex_i0, ibr, ai, appartient(E.couple(var(ibr), vx), Ut))  # (∃ai)((ai,x)∈⋃𝔇)
    Hax = N.assume(appartient(E.couple(vai, vx), Ut))     # (ai,x)∈⋃𝔇
    exG_i = _dans_union(vX, vD, E.couple(vai, vx), Hax)   # (∃G)(G∈𝔇 et (ai,x)∈G)
    vGi = var("Gi")
    exG_i = _alpha_ex(exG_i, "G", "Gi", et(appartient(var("G"), vD), appartient(E.couple(vai, vx), var("G"))))
    HwG_i = N.assume(et(appartient(vGi, vD), appartient(E.couple(vai, vx), vGi)))
    Gi_D = conjonction_elim_gauche(HwG_i)                 # Gi∈𝔇
    ax_Gi = conjonction_elim_droite(HwG_i)                # (ai,x)∈Gi
    Gi_W = _GW_de_D(vX, vD, vGi, Gi_D, HDW)              # Gi∈W
    x_champGi = _couple_dans_champ_droite(vGi, vai, vx, ax_Gi)  # x∈champ Gi
    xxU_i = _xx_union_de_champG(vX, vD, vx, vGi, Gi_D, Gi_W, x_champGi)  # (x,x)∈⋃𝔇
    wit_i = N.loi_deduction(et(appartient(vGi, vD), appartient(E.couple(vai, vx), vGi)), xxU_i)
    exG_imp_i = existe_elimination(wit_i, "Gi")
    after_Gi = N.modus_ponens(exG_i, exG_imp_i)          # (x,x)∈⋃𝔇  [(ai,x)∈⋃𝔇]
    wit_ai = N.loi_deduction(appartient(E.couple(vai, vx), Ut), after_Gi)
    ex_imp_ai = existe_elimination(wit_ai, ai)
    but_img = N.modus_ponens(ex_i, ex_imp_ai)           # (x,x)∈⋃𝔇  [x∈img⋃𝔇]
    # casse x∈champ⋃𝔇 = x∈dom⋃𝔇 ∪ img⋃𝔇
    xxU = _champ_cas(Ut, vx, Hxc, but_dom, but_img)     # (x,x)∈⋃𝔇  [x∈champ⋃𝔇, 𝔇⊂W]
    imp_bwd = N.loi_deduction(appartient(vx, AU), xxU)
    eqv = conjonction_intro(imp_fwd, imp_bwd)           # (x,x)∈⋃𝔇 ⇔ x∈champ⋃𝔇
    return N.generalisation(x, eqv)                     # (∀x)((x,x)∈⋃𝔇 ⇔ x∈champ⋃𝔇)


# ── (F) R_⋃𝔇 est une RELATION D'ORDRE DANS champ(⋃𝔇)  (assemblage B+C+D+E) ────
def Union_relation_ordre_dans(X="X", D="D", x="x", y="y", z="z"):
    """⊢ { 𝔇⊂W, totalement_ordonne(Θ,𝔇) } ⊢ est_relation_ordre_dans(R_⋃𝔇, champ ⋃𝔇).

    est_relation_ordre_dans = est_relation_ordre et est_reflexive_dans_ordre, où
    est_relation_ordre = ((ordre_transitif et ordre_antisym) et reflexif_implicite).
    Binders x,y,z pour s'aligner sur est_relation_ordre_dans(R,e,x,y,z)."""
    trans = Union_transitif(X, D, x, y, z)              # ordre_transitif(R_⋃𝔇)
    anti = Union_antisymetrique(X, D, x, y)             # ordre_antisymetrique(R_⋃𝔇)
    refl_impl = Union_refl_impl(X, D, x, y)            # ordre_reflexif_implicite(R_⋃𝔇)
    refl_dans = Union_refl_dans(X, D, x)              # est_reflexive_dans_ordre(R_⋃𝔇,champ⋃𝔇)
    rel_ordre = conjonction_intro(conjonction_intro(trans, anti), refl_impl)  # est_relation_ordre
    return conjonction_intro(rel_ordre, refl_dans)     # est_relation_ordre_dans


# ════════════════════════════════════════════════════════════════════════════
#  ÉTAPE 1 (LE CŒUR DUR) — R_⋃𝔇 BIEN ORDONNE champ(⋃𝔇).
#  Toute partie S⊂champ⋃𝔇 non vide a un plus petit élément.
#  IDÉE : S rencontre un membre G∈𝔇 (S≠∅, témoin s₀∈champ G) ; S∩champ G ⊂ champ G
#  bien ordonné ⇒ plus petit m ; m minore TOUT s∈S par END-EXTENSION (Θ-total).
# ════════════════════════════════════════════════════════════════════════════
def _point_champU_membre(X, D, x, HDW, hxchampU, but, Gp="Gp"):
    """{ 𝔇⊂W [HDW], x∈champ⋃𝔇 [hxchampU] } ⊢ but, où `but` se déduit de
       « ∃G∈𝔇∩W avec x∈champ G » via le callback but(G, GD, GW, x∈champG).

    x∈champ⋃𝔇 = x∈dom⋃𝔇 ∪ img⋃𝔇 ; un témoin couple (x,·)/(·,x)∈⋃𝔇 est dans un
    G∈𝔇⊂W, d'où x∈champ G."""
    vX, vD, vx = _terme(X), _terme(D), _terme(x)
    Ut = Union(vX, vD)
    # noms de témoins FRAIS vis-à-vis du CONTEXTE (hypothèses portées par HDW et
    # hxchampU) — sinon, en cas d'APPELS IMBRIQUÉS, le témoin (Gpd) serait libre
    # dans une hypothèse externe au moment de la généralisation.
    evite = _libres_hyps(HDW, hxchampU)
    bd = _frais_eviter(evite, vX, vD, vx, base=Gp + "bp")
    Gpd = _frais_eviter(evite | {bd}, vX, vD, vx, base=Gp + "d")
    vbd = var(bd)
    Hxdom = N.assume(appartient(vx, E.dom(Ut)))
    dax = _inst_dom(Ut, vx)
    bdr = _exists_binder(dax)
    ex_d0 = N.modus_ponens(Hxdom, equivalence_avant(dax))
    ex_d = _alpha_ex(ex_d0, bdr, bd, appartient(E.couple(vx, var(bdr)), Ut))  # (∃bp)((x,bp)∈⋃𝔇)
    Hxb = N.assume(appartient(E.couple(vx, vbd), Ut))
    exG_d = _dans_union(vX, vD, E.couple(vx, vbd), Hxb)
    vGpd = var(Gpd)
    exG_d = _alpha_ex(exG_d, "G", Gpd, et(appartient(var("G"), vD), appartient(E.couple(vx, vbd), var("G"))))
    HwG_d = N.assume(et(appartient(vGpd, vD), appartient(E.couple(vx, vbd), vGpd)))
    Gd_D = conjonction_elim_gauche(HwG_d)
    xb_Gd = conjonction_elim_droite(HwG_d)
    Gd_W = _GW_de_D(vX, vD, vGpd, Gd_D, HDW)
    x_champGd = _couple_dans_champ_gauche(vGpd, vx, vbd, xb_Gd)   # x∈champ Gd
    res_d = but(vGpd, Gd_D, Gd_W, x_champGd)
    wit_d = N.loi_deduction(et(appartient(vGpd, vD), appartient(E.couple(vx, vbd), vGpd)), res_d)
    after_Gd = N.modus_ponens(exG_d, existe_elimination(wit_d, Gpd))
    but_dom = N.modus_ponens(ex_d, existe_elimination(
        N.loi_deduction(appartient(E.couple(vx, vbd), Ut), after_Gd), bd))
    # cas x∈img⋃𝔇
    ai = _frais_eviter(evite, vX, vD, vx, base=Gp + "ap")
    Gpi = _frais_eviter(evite | {ai}, vX, vD, vx, base=Gp + "i")
    vai = var(ai)
    Hximg = N.assume(appartient(vx, E.img(Ut)))
    iax = _inst_img(Ut, vx)
    ibr = _exists_binder(iax)
    ex_i0 = N.modus_ponens(Hximg, equivalence_avant(iax))
    ex_i = _alpha_ex(ex_i0, ibr, ai, appartient(E.couple(var(ibr), vx), Ut))  # (∃ap)((ap,x)∈⋃𝔇)
    Hax = N.assume(appartient(E.couple(vai, vx), Ut))
    exG_i = _dans_union(vX, vD, E.couple(vai, vx), Hax)
    vGpi = var(Gpi)
    exG_i = _alpha_ex(exG_i, "G", Gpi, et(appartient(var("G"), vD), appartient(E.couple(vai, vx), var("G"))))
    HwG_i = N.assume(et(appartient(vGpi, vD), appartient(E.couple(vai, vx), vGpi)))
    Gi_D = conjonction_elim_gauche(HwG_i)
    ax_Gi = conjonction_elim_droite(HwG_i)
    Gi_W = _GW_de_D(vX, vD, vGpi, Gi_D, HDW)
    x_champGi = _couple_dans_champ_droite(vGpi, vai, vx, ax_Gi)   # x∈champ Gi
    res_i = but(vGpi, Gi_D, Gi_W, x_champGi)
    wit_i = N.loi_deduction(et(appartient(vGpi, vD), appartient(E.couple(vai, vx), vGpi)), res_i)
    after_Gi = N.modus_ponens(exG_i, existe_elimination(wit_i, Gpi))
    but_img = N.modus_ponens(ex_i, existe_elimination(
        N.loi_deduction(appartient(E.couple(vai, vx), Ut), after_Gi), ai))
    return _champ_cas(Ut, vx, hxchampU, but_dom, but_img)        # but  [x∈champ⋃𝔇, 𝔇⊂W]


# ── (z∈A∩B) ⇔ (z∈A et z∈B)  via AXIOME_INTER du noyau (∈ theorie_ensembles) ────
def _inst_inter(A, B, z):
    """⊢ (z∈A∩B) ⇔ (z∈A et z∈B)."""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_INTER)
    return instancie(instancie(instancie(ax, _terme(A)), _terme(B)), _terme(z))


def _inter_intro(A, B, z, hzA, hzB):
    """De ⊢ z∈A [hzA], ⊢ z∈B [hzB] déduit ⊢ z∈A∩B."""
    return N.modus_ponens(conjonction_intro(hzA, hzB),
                          equivalence_arriere(_inst_inter(A, B, _terme(z))))


def _inter_gauche(A, B, z, hzAB):
    """De ⊢ z∈A∩B [hzAB] déduit ⊢ z∈A."""
    return conjonction_elim_gauche(N.modus_ponens(hzAB, equivalence_avant(_inst_inter(A, B, _terme(z)))))


def _inter_droite(A, B, z, hzAB):
    """De ⊢ z∈A∩B [hzAB] déduit ⊢ z∈B."""
    return conjonction_elim_droite(N.modus_ponens(hzAB, equivalence_avant(_inst_inter(A, B, _terme(z)))))


def _inter_inclus_droite(A, B, z="zi"):
    """⊢ A∩B ⊂ B.   (l'intersection est incluse dans chaque facteur — ici le 2e.)"""
    from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import _peler_pourtout
    vA, vB = _terme(A), _terme(B)
    cible = inclus(E.intersection(vA, vB), vB)
    bndr, _ = _peler_pourtout(cible)
    vz = var(bndr)
    hz = N.assume(appartient(vz, E.intersection(vA, vB)))
    zB = _inter_droite(vA, vB, vz, hz)
    return N.generalisation(bndr, N.loi_deduction(appartient(vz, E.intersection(vA, vB)), zB))


def _least_inter_champ(X, D, S, G, GW, s0, hs0_inter, a="am", w="wm"):
    """{ G∈W [GW], s₀∈S∩champ G [hs0_inter] } ⊢
       (∃a)(a∈S∩champ G et (∀w)(w∈S∩champ G ⇒ (a,w)∈G)).

    S∩champ G ⊂ champ G (≠∅, témoin s₀) → R_G bien ordonne champ G donne le plus
    petit élément de S∩champ G."""
    from bourbaki.ordre.iii_2_bon_ordre.zorn_zermelo.ensembles_bourbaki_witt_chaine import _ex_falso, _refute_self
    vX, vG = _terme(X), _terme(G)
    vS = _terme(S)
    AG = champ(vG)
    Inter = E.intersection(vS, AG)
    # S∩champ G ⊂ champ G
    sub = _inter_inclus_droite(vS, AG)                          # S∩champ G ⊂ champ G
    # ¬(S∩champ G = ∅) : s₀∈S∩champ G ⇒ non vide
    from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_vide import non_vide_ssi_element
    ex_z = N.modus_ponens(hs0_inter, N.s5(appartient(var("z"), Inter), _terme(s0), "z"))  # (∃z)(z∈Inter)
    nv = N.modus_ponens(ex_z, equivalence_arriere(non_vide_ssi_element(Inter)))  # ¬(Inter=∅)
    moindre = _moindre_de_W(vX, vG, GW)                         # (∀S')((S'⊂champ G et ≠∅)⇒(∃a)…)
    moindre_I = instancie(moindre, Inter)
    ex_min = N.modus_ponens(conjonction_intro(sub, nv), moindre_I)  # (∃a)(a∈Inter et (∀w)(w∈Inter⇒(a,w)∈G))
    # α-renomme les binders « a »,« w » de est_bien_ordonne vers am,wm
    R_a = et(appartient(var("a"), Inter),
             pourtout("w", impl(appartient(var("w"), Inter), _dans(var("a"), var("w"), vG))))
    ex_min = _alpha_ex(ex_min, "a", a, R_a)
    return ex_min


def _ms_dans_union(X, D, S, G, m, s, HDW, Htot, GD, GW, m_champG, m_least, hsS):
    """{ 𝔇⊂W [HDW], totalement_ordonne(Θ,𝔇) [Htot], G∈𝔇 [GD], G∈W [GW],
        m∈champ G [m_champG],
        m_least = (∀w)(w∈S∩champ G ⇒ (m,w)∈G),  s∈S [hsS] } ⊢ (m,s)∈⋃𝔇.

    🔑 END-EXTENSION : s∈S⊂champ⋃𝔇 → témoin Gs∈𝔇∩W avec s∈champ Gs ; Θ-total ⇒
      • (Gs,G)∈Θ : Gs⊂G ⇒ champ Gs⊂champ G ⇒ s∈champ G ⇒ s∈S∩champ G ⇒ (m,s)∈G⊂⋃.
      • (G,Gs)∈Θ : seg_initial(G,Gs), G⊂Gs ⇒ m∈champ Gs ; Gs total ⇒ (m,s)∈Gs ou
        (s,m)∈Gs.  (m,s)∈Gs⊂⋃ ; sinon (s,m)∈Gs avec m∈champ G ⇒ (seg) s∈champ G ⇒
        s∈S∩champ G ⇒ (m,s)∈G⊂⋃."""
    vX, vD, vS, vG = _terme(X), _terme(D), _terme(S), _terme(G)
    vm, vs = _terme(m), _terme(s)
    Ut = Union(vX, vD)
    AG = champ(vG)
    Inter = E.intersection(vS, AG)
    HSsub = N.assume(inclus(vS, champ(Ut)))                     # S⊂champ⋃𝔇  (hyp portée)
    comp_D = conjonction_elim_droite(Htot)                     # comparabilité de 𝔇
    s_champU = N.modus_ponens(hsS, instancie(HSsub, vs))       # s∈champ⋃𝔇
    but = _dans(vm, vs, Ut)                                    # (m,s)∈⋃𝔇

    # ── helper : si s∈champ G alors (m,s)∈⋃𝔇  (via m_least sur S∩champ G) ──────
    def via_champG(s_champG):
        s_inter = _inter_intro(vS, AG, vs, hsS, s_champG)      # s∈S∩champ G
        ms_G = N.modus_ponens(s_inter, instancie(m_least, vs))  # (m,s)∈G
        return _couple_dans_union_intro(vX, vD, vG, E.couple(vm, vs), GD, ms_G)  # (m,s)∈⋃𝔇

    # callback _point_champU_membre : on a Gs∈𝔇∩W avec s∈champ Gs
    def but_pt(Gs, GsD, GsW, s_champGs):
        comp = N.modus_ponens(conjonction_intro(GD, GsD),
                              instancie(instancie(comp_D, vG), Gs))  # (G,Gs)∈Θ ou (Gs,G)∈Θ
        # branche (G,Gs)∈Θ
        HGGs = N.assume(_tle(vG, Gs, vX))
        G_Gs = _theta_incl(vX, vG, Gs, HGGs)                   # G⊂Gs
        segGGs = _theta_seg(vX, vG, Gs, HGGs)                  # seg_initial(G,Gs)
        cmGGs = champ_monotone(vG, Gs, G_Gs)                  # champ G ⊂ champ Gs
        m_champGs = N.modus_ponens(m_champG, instancie(cmGGs, vm))  # m∈champ Gs
        # Gs total : (m,s)∈Gs ou (s,m)∈Gs
        totGs = totalite_de_W(vX, Gs, vm, vs, GsW, m_champGs, s_champGs)  # (m,s)∈Gs ou (s,m)∈Gs
        #   (m,s)∈Gs ⊂ ⋃𝔇
        Hms_Gs = N.assume(_dans(vm, vs, Gs))
        b_ms = N.loi_deduction(_dans(vm, vs, Gs),
                               _couple_dans_union_intro(vX, vD, Gs, E.couple(vm, vs), GsD, Hms_Gs))
        #   (s,m)∈Gs : seg_initial(G,Gs) avec m∈champ G ⇒ s∈champ G
        Hsm_Gs = N.assume(_dans(vs, vm, Gs))
        seg_inst = instancie(instancie(segGGs, vm), vs)       # (m∈champ G et (s,m)∈Gs)⇒s∈champ G
        s_champG = N.modus_ponens(conjonction_intro(m_champG, Hsm_Gs), seg_inst)  # s∈champ G
        b_sm = N.loi_deduction(_dans(vs, vm, Gs), via_champG(s_champG))
        res_GGs = cas(totGs, b_ms, b_sm)                      # (m,s)∈⋃𝔇
        b1 = N.loi_deduction(_tle(vG, Gs, vX), res_GGs)
        # branche (Gs,G)∈Θ : Gs⊂G ⇒ champ Gs⊂champ G ⇒ s∈champ G
        HGsG = N.assume(_tle(Gs, vG, vX))
        Gs_G = _theta_incl(vX, Gs, vG, HGsG)                  # Gs⊂G
        cmGsG = champ_monotone(Gs, vG, Gs_G)                 # champ Gs⊂champ G
        s_champG2 = N.modus_ponens(s_champGs, instancie(cmGsG, vs))  # s∈champ G
        b2 = N.loi_deduction(_tle(Gs, vG, vX), via_champG(s_champG2))
        return cas(comp, b1, b2)                              # (m,s)∈⋃𝔇

    # tag DISTINCT « Gq » pour ce _point_champU_membre IMBRIQUÉ (le tag externe est
    # « Gp ») → noms de témoins disjoints, pas de capture en généralisation.
    res = _point_champU_membre(vX, vD, vs, HDW, s_champU, but_pt, Gp="Gq")  # (m,s)∈⋃𝔇
    return res


# ── (G) R_⋃𝔇 BIEN ORDONNE champ(⋃𝔇) : toute partie non vide a un plus petit élt
def Union_bien_ordonne_corps(X="X", D="D", S="S", aa="ae", ww="we", s0="s0", G="Gw", m="mw"):
    """⊢ { 𝔇⊂W, totalement_ordonne(Θ,𝔇) } ⊢
       (∀S)((S⊂champ⋃𝔇 et ¬(S=∅)) ⇒ (∃a)(a∈S et (∀w)(w∈S⇒(a,w)∈⋃𝔇))).

    🎯 LE CŒUR DUR.  S≠∅ → témoin s₀∈S∩champ G pour un membre G∈𝔇 ; S∩champ G a un
    plus petit élt m (R_G bien ordonne champ G) ; m est le plus petit de TOUT S par
    END-EXTENSION (_ms_dans_union)."""
    from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_vide import non_vide_ssi_element
    vX, vD, vS = var(X), var(D), var(S)
    Ut = Union(vX, vD)
    AU = champ(Ut)
    HDW = N.assume(inclus(vD, W(vX)))
    from bourbaki.ordre.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_relation import totalement_ordonne
    Htot = N.assume(totalement_ordonne(Theta(vX), vD))
    # corps : (S⊂champ⋃𝔇 et ¬(S=∅)) ⇒ (∃a)(a∈S et (∀w)(w∈S⇒(a,w)∈⋃𝔇))
    hypS = et(inclus(vS, AU), non(egal(vS, E.VIDE)))
    HypS = N.assume(hypS)
    Ssub = conjonction_elim_gauche(HypS)                       # S⊂champ⋃𝔇
    Snv = conjonction_elim_droite(HypS)                       # ¬(S=∅)
    but_ex = existe(aa, et(appartient(var(aa), vS),
                           pourtout(ww, impl(appartient(var(ww), vS), _dans(var(aa), var(ww), Ut)))))
    # témoin s₀∈S
    ex_s0 = N.modus_ponens(Snv, equivalence_avant(non_vide_ssi_element(vS)))  # (∃z)(z∈S)
    ex_s0 = _alpha_ex(ex_s0, "z", s0, appartient(var("z"), vS))
    vs0 = var(s0)
    Hs0 = N.assume(appartient(vs0, vS))                       # s₀∈S
    s0_champU = N.modus_ponens(Hs0, instancie(Ssub, vs0))    # s₀∈champ⋃𝔇

    # callback _point_champU_membre : G∈𝔇∩W avec s₀∈champ G
    def but_G(Gv, GD, GW, s0_champG):
        AG = champ(Gv)
        Inter = E.intersection(vS, AG)
        s0_inter = _inter_intro(vS, AG, vs0, Hs0, s0_champG)  # s₀∈S∩champ G
        ex_m = _least_inter_champ(vX, vD, vS, Gv, GW, vs0, s0_inter, a=m)  # (∃m)(m∈Inter et …)
        # per-témoin m
        R_m = et(appartient(var(m), Inter),
                 pourtout("w", impl(appartient(var("w"), Inter), _dans(var(m), var("w"), Gv))))
        vm = var(m)
        Hm = N.assume(R_m)
        m_inter = conjonction_elim_gauche(Hm)                # m∈S∩champ G
        m_least = conjonction_elim_droite(Hm)                # (∀w)(w∈Inter⇒(m,w)∈G)
        m_S = _inter_gauche(vS, AG, vm, m_inter)             # m∈S
        m_champG = _inter_droite(vS, AG, vm, m_inter)        # m∈champ G
        # (∀s)(s∈S ⇒ (m,s)∈⋃𝔇)
        vs = var("se")
        Hs = N.assume(appartient(vs, vS))
        ms_U = _ms_dans_union(vX, vD, vS, Gv, vm, vs, HDW, Htot, GD, GW, m_champG, m_least, Hs)
        ms_U = _cut(ms_U, inclus(vS, AU), Ssub)             # décharge le S⊂champ⋃ interne
        all_s = N.generalisation("se", N.loi_deduction(appartient(vs, vS), ms_U))  # (∀s)(s∈S⇒(m,s)∈⋃)
        # α-renomme « se » → ww  pour matcher but_ex
        from bourbaki.logique.i_3_quantifies.tactiques_abrege_quantif import alpha_pour_tout
        if "se" != ww:
            _, inner = __import__("bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2",
                                  fromlist=["_peler_pourtout"])._peler_pourtout(all_s.conclusion)
            all_s = N.modus_ponens(all_s, equivalence_avant(alpha_pour_tout("se", ww, inner)))
        least_m = conjonction_intro(m_S, all_s)             # m∈S et (∀w)(w∈S⇒(m,w)∈⋃)
        # (∃a)(…)  témoin m
        R_a = et(appartient(var(aa), vS),
                 pourtout(ww, impl(appartient(var(ww), vS), _dans(var(aa), var(ww), Ut))))
        ex_a = N.modus_ponens(least_m, N.s5(R_a, vm, aa))   # (∃a)(…)
        # éliminer ∃m
        wit_m = N.loi_deduction(R_m, ex_a)
        return N.modus_ponens(ex_m, existe_elimination(wit_m, m))  # (∃a)(…)  [hyps]

    res_G = _point_champU_membre(vX, vD, vs0, HDW, s0_champU, but_G)  # (∃a)(…)  [s₀∈S, hyps]
    # éliminer ∃s₀
    after_s0 = N.modus_ponens(ex_s0, existe_elimination(
        N.loi_deduction(appartient(vs0, vS), res_G), s0))    # (∃a)(…)  [hypS, hyps]
    body = N.loi_deduction(hypS, after_s0)
    return N.generalisation(S, body)


# ── (H) R_⋃𝔇 BIEN ORDONNE champ(⋃𝔇)  (relation_ordre_dans + plus petit élt) ───
def Union_bien_ordonne(X="X", D="D"):
    """⊢ { 𝔇⊂W, totalement_ordonne(Θ,𝔇) } ⊢ est_bien_ordonne(R_⋃𝔇, champ ⋃𝔇).

    est_bien_ordonne = est_relation_ordre_dans (Union_relation_ordre_dans) ET
    « toute partie non vide a un plus petit élément » (Union_bien_ordonne_corps,
    avec les binders X,a,w de est_bien_ordonne)."""
    rod = Union_relation_ordre_dans(X, D, "x", "y", "z")     # est_relation_ordre_dans(R_⋃,champ⋃)
    # bon_ordre_partiel(G,X) emploie le binder « S » (pas « X ») pour la partie ;
    # on s'aligne dessus.  binders a,w internes.
    corps = Union_bien_ordonne_corps(X, D, S="S", aa="a", ww="w")  # plus petit élt (binders S,a,w)
    return conjonction_intro(rod, corps)                    # est_bien_ordonne(R_⋃,champ⋃)


# ── (I) ⋃𝔇 est un BON ORDRE PARTIEL de X  (⋃𝔇⊂X×X + bien ordonné) ────────────
def Union_bop(X="X", D="D"):
    """⊢ { 𝔇⊂W, totalement_ordonne(Θ,𝔇) } ⊢ bon_ordre_partiel(⋃𝔇, X).

    bon_ordre_partiel(⋃𝔇,X) = ⋃𝔇⊂X×X (Union_inclus_produit) ET
    est_bien_ordonne(R_⋃𝔇, champ ⋃𝔇) (Union_bien_ordonne)."""
    incl_prod = Union_inclus_produit(X, D)                  # ⋃𝔇⊂X×X  [𝔇⊂W]
    bo = Union_bien_ordonne(X, D)                          # est_bien_ordonne(R_⋃,champ⋃)  [2 hyps]
    return conjonction_intro(incl_prod, bo)                # bon_ordre_partiel(⋃𝔇,X)


# ── (J) ⋃𝔇 ∈ W  (axiome de W) ─────────────────────────────────────────────────
def Union_dans_W(X="X", D="D"):
    """⊢ { 𝔇⊂W, totalement_ordonne(Θ,𝔇) } ⊢ ⋃𝔇 ∈ W.

    ⋃𝔇 est un bon ordre partiel de X (Union_bop) ; l'axiome de W conclut ⋃𝔇∈W."""
    vX, vD = var(X), var(D)
    Ut = Union(vX, vD)
    bop = Union_bop(X, D)                                  # bon_ordre_partiel(⋃𝔇,X)
    return N.modus_ponens(bop, equivalence_arriere(_inst_W(vX, Ut)))  # ⋃𝔇∈W


# ── G⊂⋃𝔇  (tout membre est inclus dans la réunion) ───────────────────────────
def _G_inclus_Union(X, D, G, hGD, w="wu"):
    """De ⊢ G∈𝔇 [hGD] déduit ⊢ G⊂⋃𝔇."""
    from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import _peler_pourtout
    vX, vD, vG = _terme(X), _terme(D), _terme(G)
    Ut = Union(vX, vD)
    cible = inclus(vG, Ut)
    bndr, _ = _peler_pourtout(cible)
    vw = var(bndr)
    hwG = N.assume(appartient(vw, vG))                          # w∈G
    wU = _couple_dans_union_intro(vX, vD, vG, vw, hGD, hwG)    # w∈⋃𝔇
    return N.generalisation(bndr, N.loi_deduction(appartient(vw, vG), wU))  # G⊂⋃𝔇


# ── seg_initial(G,⋃𝔇)  (END-EXTENSION : champ G est segment initial de ⋃𝔇) ────
def Union_seg_initial(X="X", D="D", G="G", p="pp", q="qq"):
    """⊢ { 𝔇⊂W, totalement_ordonne(Θ,𝔇), G∈𝔇 } ⊢ seg_initial(G, ⋃𝔇).

    = (∀p∀q)((p∈champ G et (q,p)∈⋃𝔇) ⇒ q∈champ G).  (q,p)∈⋃𝔇 dans un membre G'∈𝔇 ;
    Θ-total ⇒ (G',G)∈Θ (G'⊂G ⇒ (q,p)∈G ⇒ q∈champ G) ou (G,G')∈Θ (seg_initial(G,G')
    avec p∈champ G ⇒ q∈champ G)."""
    from bourbaki.ordre.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_relation import totalement_ordonne
    vX, vD, vG = var(X), var(D), var(G)
    vp, vq = var(p), var(q)
    Ut = Union(vX, vD)
    AG = champ(vG)
    HDW = N.assume(inclus(vD, W(vX)))
    Htot = N.assume(totalement_ordonne(Theta(vX), vD))
    HGD = N.assume(appartient(vG, vD))                          # G∈𝔇
    GW = _GW_de_D(vX, vD, vG, HGD, HDW)                        # G∈W
    comp_D = conjonction_elim_droite(Htot)
    # corps : (p∈champ G et (q,p)∈⋃𝔇) ⇒ q∈champ G
    Hpq = N.assume(et(appartient(vp, AG), _dans(vq, vp, Ut)))   # p∈champ G et (q,p)∈⋃𝔇
    p_champG = conjonction_elim_gauche(Hpq)                     # p∈champ G
    qp_U = conjonction_elim_droite(Hpq)                         # (q,p)∈⋃𝔇
    but = appartient(vq, AG)                                    # q∈champ G
    # (q,p)∈⋃𝔇 : témoin G'∈𝔇 avec (q,p)∈G'
    exGp = _dans_union(vX, vD, E.couple(vq, vp), qp_U)         # (∃G')(G'∈𝔇 et (q,p)∈G')
    exGp = _alpha_ex(exGp, "G", "Gpp", et(appartient(var("G"), vD), appartient(E.couple(vq, vp), var("G"))))
    vGp = var("Gpp")
    HwGp = N.assume(et(appartient(vGp, vD), appartient(E.couple(vq, vp), vGp)))
    Gp_D = conjonction_elim_gauche(HwGp)                       # G'∈𝔇
    qp_Gp = conjonction_elim_droite(HwGp)                      # (q,p)∈G'
    comp = N.modus_ponens(conjonction_intro(HGD, Gp_D),
                          instancie(instancie(comp_D, vG), vGp))  # (G,G')∈Θ ou (G',G)∈Θ
    # branche (G,G')∈Θ : seg_initial(G,G'), p∈champ G, (q,p)∈G' ⇒ q∈champ G
    HGGp = N.assume(_tle(vG, vGp, vX))
    segGGp = _theta_seg(vX, vG, vGp, HGGp)                     # seg_initial(G,G')
    seg_inst = instancie(instancie(segGGp, vp), vq)           # (p∈champ G et (q,p)∈G')⇒q∈champ G
    qG_1 = N.modus_ponens(conjonction_intro(p_champG, qp_Gp), seg_inst)  # q∈champ G
    b1 = N.loi_deduction(_tle(vG, vGp, vX), qG_1)
    # branche (G',G)∈Θ : G'⊂G ⇒ (q,p)∈G ⇒ q∈dom G ⊂ champ G
    HGpG = N.assume(_tle(vGp, vG, vX))
    Gp_G = _theta_incl(vX, vGp, vG, HGpG)                     # G'⊂G
    qp_G = N.modus_ponens(qp_Gp, instancie(Gp_G, E.couple(vq, vp)))  # (q,p)∈G
    qG_2 = _couple_dans_champ_gauche(vG, vq, vp, qp_G)        # q∈champ G
    b2 = N.loi_deduction(_tle(vGp, vG, vX), qG_2)
    qG = cas(comp, b1, b2)                                    # q∈champ G  [HwGp, …]
    wit = N.loi_deduction(et(appartient(vGp, vD), appartient(E.couple(vq, vp), vGp)), qG)
    qG_final = N.modus_ponens(exGp, existe_elimination(wit, "Gpp"))  # q∈champ G  [Hpq, …]
    body = N.loi_deduction(et(appartient(vp, AG), _dans(vq, vp, Ut)), qG_final)
    return N.generalisation(p, N.generalisation(q, body))    # seg_initial(G,⋃𝔇)


# ── (K) ⋃𝔇 MAJORE 𝔇 dans (Θ,W) ──────────────────────────────────────────────
def Union_majorant(X="X", D="D", G="x"):
    """⊢ { 𝔇⊂W, totalement_ordonne(Θ,𝔇) } ⊢ majorant(Θ, 𝔇, ⋃𝔇, W).

    majorant(Θ,𝔇,⋃𝔇,W) = ⋃𝔇∈W et (∀G)(G∈𝔇 ⇒ (G,⋃𝔇)∈Θ).  ⋃𝔇∈W (Union_dans_W) ;
    pour G∈𝔇 : G∈W (𝔇⊂W), ⋃𝔇∈W, G⊂⋃𝔇 (_G_inclus_Union), seg_initial(G,⋃𝔇)
    (Union_seg_initial) ⇒ (G,⋃𝔇)∈Θ."""
    from bourbaki.ordre.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_relation import totalement_ordonne, majorant
    vX, vD = var(X), var(D)
    Ut = Union(vX, vD)
    HDW = N.assume(inclus(vD, W(vX)))                          # 𝔇⊂W
    Htot = N.assume(totalement_ordonne(Theta(vX), vD))        # totalement_ordonne(Θ,𝔇)
    U_W = Union_dans_W(X, D)                                  # ⋃𝔇∈W  [2 hyps]
    vG = var(G)
    HGD = N.assume(appartient(vG, vD))                       # G∈𝔇
    GW = _GW_de_D(vX, vD, vG, HGD, HDW)                      # G∈W
    G_U = _G_inclus_Union(vX, vD, vG, HGD)                   # G⊂⋃𝔇
    # seg_initial emploie les binders « p,q » (cf. _corps_Theta) — on s'aligne.
    seg = Union_seg_initial(X, D, G, p="p", q="q")          # seg_initial(G,⋃𝔇)  [3 hyps]
    seg = _cut(seg, inclus(vD, W(vX)), HDW)
    seg = _cut(seg, totalement_ordonne(Theta(vX), vD), Htot)
    seg = _cut(seg, appartient(vG, vD), HGD)                # seg_initial(G,⋃𝔇)  [aucune nouv. hyp]
    G_U_Theta = _Theta_intro(vX, vG, Ut, GW, U_W, G_U, seg)  # (G,⋃𝔇)∈Θ
    body = N.loi_deduction(appartient(vG, vD), G_U_Theta)
    allG = N.generalisation(G, body)                         # (∀G)(G∈𝔇⇒(G,⋃𝔇)∈Θ)
    return conjonction_intro(U_W, allG)                      # majorant(Θ,𝔇,⋃𝔇,W)


# ════════════════════════════════════════════════════════════════════════════
#  ÉTAPE 1 (assemblage) — (Θ,W) est INDUCTIF
#  est_inductif(Θ,W) = est_ordre(Θ,W) et (∀C)(chaine(Θ,W,C) ⇒ (∃m)majorant(Θ,C,m,W)).
#  L'ordre vient de Theta_est_ordre ; le majorant d'une Θ-chaîne est ⋃C (Union_majorant).
# ════════════════════════════════════════════════════════════════════════════
def W_inductif(X="X", D="C", m="m", x="x", y="y", z="z"):
    """⊢ est_inductif(Θ, W).   (INCONDITIONNEL — theorie_ensembles()=22.)

    🎯🎯 LE CŒUR de Zermelo : toute Θ-chaîne de bons ordres partiels est majorée
    par sa réunion (qui est ENCORE un bon ordre partiel — la réunion BIEN ORDONNE,
    par end-extension).  est_ordre(Θ,W) inconditionnel (Theta_est_ordre) ; pour une
    Θ-chaîne C (chaine(Θ,W,C) = C⊂W et totalement_ordonne(Θ,C)), ⋃C majore C
    (Union_majorant), témoin du (∃m)."""
    from bourbaki.ordre.iii_2_bon_ordre.zorn_zermelo.ensembles_zorn import chaine, est_inductif
    from bourbaki.ordre.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_relation import totalement_ordonne, majorant
    vX, vD = var(X), var(D)
    Theta_set, W_set = Theta(vX), W(vX)
    Ut = Union(vX, vD)
    ord_Th = Theta_est_ordre(X)                              # est_ordre(Θ,W)  [binders x,y,z]
    Hch = N.assume(chaine(Theta_set, W_set, vD, x, y, z))    # chaine(Θ,W,C)
    D_W = conjonction_elim_gauche(Hch)                       # C⊂W
    tot_D = conjonction_elim_droite(Hch)                     # totalement_ordonne(Θ,C)
    maj_U = Union_majorant(X, D)                            # majorant(Θ,C,⋃C,W)  [2 hyps]
    maj_U = _cut(maj_U, inclus(vD, W_set), D_W)
    maj_U = _cut(maj_U, totalement_ordonne(Theta_set, vD), tot_D)  # majorant(Θ,C,⋃C,W)  [aucune hyp]
    corps_m = majorant(Theta_set, vD, var(m), W_set, x)
    s5 = N.s5(corps_m, Ut, m)                                # (⋃C|m)corps ⇒ (∃m)corps
    ex_maj = N.modus_ponens(maj_U, s5)                       # (∃m)majorant(Θ,C,m,W)
    body = N.loi_deduction(chaine(Theta_set, W_set, vD, x, y, z), ex_maj)
    allD = N.generalisation(D, body)                         # (∀D)(chaine⇒(∃m)majorant)
    # α-renomme le liant D → C pour matcher est_inductif(Θ,W) (binder canonique « C »)
    from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import _peler_pourtout
    if D != "C":
        from bourbaki.logique.i_3_quantifies.tactiques_abrege_quantif import alpha_pour_tout
        _, corps_D = _peler_pourtout(allD.conclusion)
        ren = alpha_pour_tout(D, "C", corps_D)
        allD = N.modus_ponens(allD, equivalence_avant(ren))
    return conjonction_intro(ord_Th, allD)                   # est_inductif(Θ,W)


# ════════════════════════════════════════════════════════════════════════════
#  ÉTAPE 2 — W ≠ ∅ : le GRAPHE VIDE ∅ est un bon ordre partiel de X.
# ════════════════════════════════════════════════════════════════════════════
def _vide_inclus(t, z="_zv"):
    """⊢ ∅ ⊂ t  pour un TERME t  (le vide est inclus dans tout ensemble)."""
    from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import _peler_pourtout
    vt = _terme(t)
    cible = inclus(E.VIDE, vt)
    bndr, _ = _peler_pourtout(cible)
    zt = var(bndr)
    nz = vide_sans_element_t(zt)                            # ¬(z∈∅)
    imp = N.modus_ponens(nz, N.s2(non(appartient(zt, E.VIDE)), appartient(zt, vt)))  # z∈∅⇒z∈t
    return N.generalisation(bndr, imp)


def _exfalso_vide_conj(c1, c2, phi):
    """De c1,c2 TERMES et Φ, déduit ⊢ ( (c1∈∅ et c2∈∅) ⇒ Φ )  (vacuité via c1∈∅)."""
    from bourbaki.ordre.iii_2_bon_ordre.zorn_zermelo.ensembles_bourbaki_witt_chaine import _ex_falso
    vc1 = _terme(c1)
    H = N.assume(et(appartient(vc1, E.VIDE), appartient(_terme(c2), E.VIDE)))
    c1_vide = conjonction_elim_gauche(H)                   # c1∈∅
    nc1 = vide_sans_element_t(vc1)                         # ¬(c1∈∅)
    falso = _ex_falso(c1_vide, nc1, phi)                  # Φ (ex falso)
    return N.loi_deduction(et(appartient(vc1, E.VIDE), appartient(_terme(c2), E.VIDE)), falso)


def _champ_vide_sans_element(x):
    """⊢ ¬( x ∈ champ ∅ )  pour un TERME x.

    champ ∅ = dom ∅ ∪ img ∅ ; x∈dom ∅ ⇒ (∃y)((x,y)∈∅) (faux), idem img ; donc
    x∈champ∅ ⇒ ⊥, d'où ¬(x∈champ∅)."""
    from bourbaki.ordre.iii_2_bon_ordre.zorn_zermelo.ensembles_bourbaki_witt_chaine import _ex_falso, _refute_self
    vx = _terme(x)
    A0 = champ(E.VIDE)
    Hx = N.assume(appartient(vx, A0))                      # x∈champ∅
    # x∈dom∅ ⇒ ⊥
    Hd = N.assume(appartient(vx, E.dom(E.VIDE)))
    dax = _inst_dom(E.VIDE, vx)
    bdr = _exists_binder(dax)
    exd = N.modus_ponens(Hd, equivalence_avant(dax))      # (∃·)((x,·)∈∅)
    # (∃bdr)((x,bdr)∈∅) ⇒ ⊥ : tout témoin (x,bdr)∈∅ est faux (vide_sans_element)
    Hwd = N.assume(appartient(E.couple(vx, var(bdr)), E.VIDE))
    nzc = vide_sans_element_t(E.couple(vx, var(bdr)))      # ¬((x,bdr)∈∅)
    abs_d = _ex_falso(Hwd, nzc, appartient(vx, E.VIDE))   # x∈∅  (ex falso)  [Hwd]
    impd = N.loi_deduction(appartient(E.couple(vx, var(bdr)), E.VIDE), abs_d)
    x_vide_d = N.modus_ponens(exd, existe_elimination(impd, bdr))  # x∈∅  [x∈dom∅]
    bd_d = N.loi_deduction(appartient(vx, E.dom(E.VIDE)), x_vide_d)
    # x∈img∅ ⇒ x∈∅
    Hi = N.assume(appartient(vx, E.img(E.VIDE)))
    iax = _inst_img(E.VIDE, vx)
    ibr = _exists_binder(iax)
    exi = N.modus_ponens(Hi, equivalence_avant(iax))
    Hwi = N.assume(appartient(E.couple(var(ibr), vx), E.VIDE))
    nzi = vide_sans_element_t(E.couple(var(ibr), vx))
    abs_i = _ex_falso(Hwi, nzi, appartient(vx, E.VIDE))
    impi = N.loi_deduction(appartient(E.couple(var(ibr), vx), E.VIDE), abs_i)
    x_vide_i = N.modus_ponens(exi, existe_elimination(impi, ibr))  # x∈∅  [x∈img∅]
    bd_i = N.loi_deduction(appartient(vx, E.img(E.VIDE)), x_vide_i)
    x_vide = _champ_cas(E.VIDE, vx, Hx, x_vide_d, x_vide_i)  # x∈∅  [x∈champ∅]
    not_x_vide = vide_sans_element_t(vx)                   # ¬(x∈∅)
    falso = _ex_falso(x_vide, not_x_vide, non(appartient(vx, A0)))  # ¬(x∈champ∅)  [x∈champ∅]
    return _refute_self(N.loi_deduction(appartient(vx, A0), falso))  # ¬(x∈champ∅)


def _vide_rel_ordre_dans():
    """⊢ est_relation_ordre_dans(R_∅, champ ∅).   (vacuité + champ ∅ vide.)

    transitif/antisym/refl_impl : prémisses « (·,·)∈∅ » fausses → vacuous ;
    reflexive_dans : (x,x)∈∅ ⇔ x∈champ∅ — les DEUX côtés faux (vide_sans_element /
    _champ_vide_sans_element)."""
    from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_abrege import (
        ordre_transitif, ordre_antisymetrique, ordre_reflexif_implicite,
        est_reflexive_dans_ordre,
    )
    from bourbaki.ordre.iii_2_bon_ordre.zorn_zermelo.ensembles_bourbaki_witt_chaine import _ex_falso
    R0 = R_de(E.VIDE)
    A0 = champ(E.VIDE)
    vx, vy, vz = var("x"), var("y"), var("z")
    # transitif : (∀x∀y∀z)(((x,y)∈∅ et (y,z)∈∅)⇒(x,z)∈∅)
    tb = _exfalso_vide_conj(E.couple(vx, vy), E.couple(vy, vz), _dans(vx, vz, E.VIDE))
    trans = N.generalisation("x", N.generalisation("y", N.generalisation("z", tb)))
    # antisym : (∀x∀y)(((x,y)∈∅ et (y,x)∈∅)⇒x=y)
    ab = _exfalso_vide_conj(E.couple(vx, vy), E.couple(vy, vx), egal(vx, vy))
    anti = N.generalisation("x", N.generalisation("y", ab))
    # refl_impl : (∀x∀y)((x,y)∈∅⇒((x,x)∈∅ et (y,y)∈∅))
    Hxy = N.assume(_dans(vx, vy, E.VIDE))
    nxy = vide_sans_element_t(E.couple(vx, vy))
    rib = _ex_falso(Hxy, nxy, et(_dans(vx, vx, E.VIDE), _dans(vy, vy, E.VIDE)))
    refl_impl = N.generalisation("x", N.generalisation("y",
        N.loi_deduction(_dans(vx, vy, E.VIDE), rib)))
    # reflexive_dans : (∀x)((x,x)∈∅ ⇔ x∈champ∅) — (x,x)∈∅⇒x∈champ∅ (ex falso) et inverse (ex falso)
    Hxx = N.assume(_dans(vx, vx, E.VIDE))
    nxx = vide_sans_element_t(E.couple(vx, vx))
    fwd = N.loi_deduction(_dans(vx, vx, E.VIDE), _ex_falso(Hxx, nxx, appartient(vx, A0)))
    Hxc = N.assume(appartient(vx, A0))
    nxc = _champ_vide_sans_element(vx)
    bwd = N.loi_deduction(appartient(vx, A0), _ex_falso(Hxc, nxc, _dans(vx, vx, E.VIDE)))
    refl_dans = N.generalisation("x", conjonction_intro(fwd, bwd))
    rel_ordre = conjonction_intro(conjonction_intro(trans, anti), refl_impl)
    return conjonction_intro(rel_ordre, refl_dans)        # est_relation_ordre_dans(R_∅,champ∅)


def _vide_bien_ordonne():
    """⊢ est_bien_ordonne(R_∅, champ ∅).   (relation ordre dans + plus petit élt vacuité.)

    Le « plus petit élément » est VACUE : S⊂champ∅ et S≠∅ ⇒ ∃s∈S, s∈champ∅ — or
    champ∅ est vide (_champ_vide_sans_element), contradiction."""
    from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_vide import non_vide_ssi_element
    from bourbaki.ordre.iii_2_bon_ordre.zorn_zermelo.ensembles_bourbaki_witt_chaine import _ex_falso
    A0 = champ(E.VIDE)
    rod = _vide_rel_ordre_dans()                          # est_relation_ordre_dans(R_∅,champ∅)
    # corps : (∀S)((S⊂champ∅ et ¬(S=∅)) ⇒ (∃a)(a∈S et (∀w)(w∈S⇒(a,w)∈∅)))
    vS = var("S")
    petit = existe("a", et(appartient(var("a"), vS),
                           pourtout("w", impl(appartient(var("w"), vS), _dans(var("a"), var("w"), E.VIDE)))))
    hypS = et(inclus(vS, A0), non(egal(vS, E.VIDE)))
    HypS = N.assume(hypS)
    Ssub = conjonction_elim_gauche(HypS)                  # S⊂champ∅
    Snv = conjonction_elim_droite(HypS)                   # ¬(S=∅)
    ex_s = N.modus_ponens(Snv, equivalence_avant(non_vide_ssi_element(vS)))  # (∃z)(z∈S)
    vz = var("z")
    Hz = N.assume(appartient(vz, vS))                    # z∈S
    z_champ0 = N.modus_ponens(Hz, instancie(Ssub, vz))   # z∈champ∅
    nz_champ0 = _champ_vide_sans_element(vz)             # ¬(z∈champ∅)
    falso = _ex_falso(z_champ0, nz_champ0, petit)        # petit (ex falso)  [z∈S]
    after_z = N.modus_ponens(ex_s, existe_elimination(
        N.loi_deduction(appartient(vz, vS), falso), "z"))  # petit  [hypS]
    corps = N.generalisation("S", N.loi_deduction(hypS, after_z))
    return conjonction_intro(rod, corps)                 # est_bien_ordonne(R_∅,champ∅)


def vide_bon_ordre_partiel(X="X"):
    """⊢ bon_ordre_partiel(∅, X).   (Le graphe VIDE est un bon ordre partiel.)

    ∅⊂X×X (vacuité) ET est_bien_ordonne(R_∅, champ ∅) (vacuité, champ ∅ vide)."""
    vX = var(X)
    vide_XX = _vide_inclus(E.produit(vX, vX))            # ∅⊂X×X
    bo = _vide_bien_ordonne()                           # est_bien_ordonne(R_∅,champ∅)
    return conjonction_intro(vide_XX, bo)               # bon_ordre_partiel(∅,X)


def vide_dans_W(X="X"):
    """⊢ ∅ ∈ W.   (∅ est un bon ordre partiel (vide_bon_ordre_partiel), axiome de W.)"""
    vX = var(X)
    bop = vide_bon_ordre_partiel(X)                     # bon_ordre_partiel(∅,X)
    return N.modus_ponens(bop, equivalence_arriere(_inst_W(vX, E.VIDE)))  # ∅∈W


def W_non_vide(X="X", w="w"):
    """⊢ W ≠ ∅.   (= enonce_non_vide(W) = (∃w)(w∈W) ; témoin ∅∈W.)"""
    vX = var(X)
    vide_W = vide_dans_W(X)                             # ∅∈W
    R = appartient(var(w), W(vX))
    return N.modus_ponens(vide_W, N.s5(R, E.VIDE, w))   # (∃w)(w∈W)


# ════════════════════════════════════════════════════════════════════════════
#  ÉTAPE 3 — ZORN sur (Θ, W) ⇒ (∃M) element_maximal(Θ, W, M).
# ════════════════════════════════════════════════════════════════════════════
def _zorn_instancie(X):
    """⊢ ( est_ordre(Θ,W) et est_inductif(Θ,W) et W≠∅ ) ⇒ (∃m)maximal(Θ,W,m).

    zorn_theoreme() (CLOS) instancié à G:=Θ(X), E:=W(X) via un PIVOT frais g0."""
    from bourbaki.ordre.iii_2_bon_ordre.zorn_zermelo.ensembles_zorn_theoreme import zorn_theoreme
    g0 = "_zg0"
    vg0 = var(g0)
    Theta0, W0 = Theta(vg0), W(vg0)
    th = zorn_theoreme()                                # CLOS (binders G,E,m,C,x,y,z)
    th = N.generalisation("G", N.generalisation("E", th))   # (∀E∀G)( … )
    th = instancie(th, Theta0)                          # G:=Θ(g0)
    th = instancie(th, W0)                              # E:=W(g0)
    th = instancie(N.generalisation(g0, th), _terme(X))  # g0:=X
    return th


def maximal_existe(X="X", m="m"):
    """⊢ (∃m) element_maximal(Θ, W, m).   (INCONDITIONNEL — via ZORN.)

    Les trois prémisses de Zorn sont PROUVÉES : est_ordre(Θ,W) (Theta_est_ordre),
    est_inductif(Θ,W) (W_inductif), W≠∅ (W_non_vide).  Donc Zorn donne l'existence
    d'un bon ordre partiel MAXIMAL M.  Rien postulé."""
    vX = var(X)
    ord_Th = Theta_est_ordre(X)                         # est_ordre(Θ,W)  [binders x,y,z]
    ind_Th = W_inductif(X)                              # est_inductif(Θ,W)  [binders C,m,x,y,z]
    nv = W_non_vide(X, "x")                             # W≠∅  [binder x, matche enonce_non_vide]
    premisses = conjonction_intro(conjonction_intro(ord_Th, ind_Th), nv)
    zorn = _zorn_instancie(vX)                          # premisses ⇒ (∃m)maximal
    return N.modus_ponens(premisses, zorn)             # (∃m)element_maximal(Θ,W,m)


# ════════════════════════════════════════════════════════════════════════════
#  ÉTAPE 4 — un M MAXIMAL vérifie champ(M)=X.  PAR L'ABSURDE : si x₀∈X∖champ M,
#  on étend M en mettant x₀ AU SOMMET :  M' := M ∪ { (y,x₀) | y∈champ M ou y=x₀ }.
#  M' est un bon ordre partiel STRICTEMENT plus grand (Θ) que M ⇒ contredit max.
#  Ext(X,M,x₀) = terme opaque + axiome de membership DÉDIÉ (S8+A1).  theorie = 22.
# ════════════════════════════════════════════════════════════════════════════
def Ext(X, M, x0):
    """M' := M ∪ { (y,x₀) | y∈champ M ou y=x₀ }  (M augmenté de x₀ au SOMMET)."""
    return E.app("zermelo_Ext", _terme(X), _terme(M), _terme(x0))


def _corps_Ext(X, M, x0, c, y="ye"):
    """Corps de M' :  c∈M ou (∃y)(c=(y,x₀) et (y∈champ M ou y=x₀))."""
    vM, vx0, vc = _terme(M), _terme(x0), _terme(c)
    vy = var(y)
    AM = champ(vM)
    return ou(appartient(vc, vM),
              existe(y, et(egal(vc, E.couple(vy, vx0)),
                           ou(appartient(vy, AM), egal(vy, vx0)))))


def axiome_Ext(X="X", M="M", x0="x0", c="c", y="ye"):
    """⊢-schéma (∀X M x₀ c)( c∈M' ⇔ (c∈M ou (∃y)(c=(y,x₀) et (y∈champ M ou y=x₀))) ).

    Axiome DÉFINITIONNEL de l'extension au sommet (légitime S8+A1).  N'altère PAS
    theorie_ensembles()."""
    vX, vM, vx0, vc = var(X), var(M), var(x0), var(c)
    return pourtout(X, pourtout(M, pourtout(x0, pourtout(c,
        equiv(appartient(vc, Ext(vX, vM, vx0)), _corps_Ext(vX, vM, vx0, vc, y))))))


def theorie_Ext(X="X", M="M", x0="x0", c="c", y="ye"):
    """Théorie DÉDIÉE ne contenant que l'axiome de M' (E.III.2, Zermelo, ÉTAPE 4)."""
    return N.Theorie("Ext-Zermelo", [axiome_Ext(X, M, x0, c, y)])


def _inst_Ext(X, M, x0, c):
    """⊢ ( c∈M' ⇔ (c∈M ou (∃y)(c=(y,x₀) et (y∈champ M ou y=x₀))) )  (instancié)."""
    ax = N.axiome(theorie_Ext(), axiome_Ext())
    for tm in (X, M, x0, c):
        ax = instancie(ax, _terme(tm))
    return ax


def _ext_intro_M(X, M, x0, c, hcM):
    """De ⊢ c∈M [hcM] déduit ⊢ c∈M'  (un couple de M est dans M')."""
    vc = _terme(c)
    disj = _ou_gauche(hcM, _corps_Ext(X, M, x0, vc).sous[1])
    return N.modus_ponens(disj, equivalence_arriere(_inst_Ext(X, M, x0, vc)))


def _ext_intro_top(X, M, x0, y, hy):
    """De ⊢ (y∈champ M ou y=x₀) [hy] déduit ⊢ (y,x₀)∈M'  (couple au sommet)."""
    vM, vx0, vy = _terme(M), _terme(x0), _terme(y)
    AM = champ(vM)
    c = E.couple(vy, vx0)
    corps_y = et(egal(c, E.couple(vy, vx0)), ou(appartient(vy, AM), egal(vy, vx0)))
    pair = conjonction_intro(N.reflexivite(c), hy)            # c=(y,x₀) et (y∈champ M ou y=x₀)
    ex = N.modus_ponens(pair, N.s5(et(egal(c, E.couple(var("ye"), vx0)),
                                      ou(appartient(var("ye"), AM), egal(var("ye"), vx0))), vy, "ye"))
    disj = _ou_droite(ex, appartient(c, vM))
    return N.modus_ponens(disj, equivalence_arriere(_inst_Ext(X, M, x0, c)))


def _ext_cas(X, M, x0, c, hcExt, but_M, but_top, y="ye"):
    """De ⊢ c∈M' [hcExt] et deux preuves conditionnelles
       (c∈M ⊢ but) [but_M],
       ((∃y)(c=(y,x₀) et (y∈champ M ou y=x₀)) ⊢ but) [but_top]  ⇒  ⊢ but."""
    vc = _terme(c)
    disj = N.modus_ponens(hcExt, equivalence_avant(_inst_Ext(X, M, x0, vc)))  # c∈M ou (∃y)…
    rhs = _corps_Ext(X, M, x0, vc, y).sous[1]
    bM = N.loi_deduction(appartient(vc, _terme(M)), but_M)
    bT = N.loi_deduction(rhs, but_top)
    return cas(disj, bM, bT)


# ── x₀∈champ M'  (x₀ est au sommet, via le couple (x₀,x₀)∈M') ─────────────────
def _x0_dans_champ_ext(X, M, x0):
    """⊢ x₀ ∈ champ M'.   ((x₀,x₀)∈M' (y=x₀ branche) ⇒ x₀∈dom M' ⊂ champ M'.)"""
    vM, vx0 = _terme(M), _terme(x0)
    hy = _ou_droite(N.reflexivite(vx0), appartient(vx0, champ(vM)))  # x₀∈champ M ou x₀=x₀
    x0x0 = _ext_intro_top(X, M, x0, vx0, hy)                  # (x₀,x₀)∈M'
    Ut = Ext(_terme(X), vM, vx0)
    return _couple_dans_champ_gauche(Ut, vx0, vx0, x0x0)     # x₀∈champ M'


# ── M ⊂ M'  et  M ≠ M' ───────────────────────────────────────────────────────
def _M_inclus_Ext(X, M, x0, c="ce"):
    """⊢ M ⊂ M'.   (tout couple de M est dans M' — branche gauche de M'.)"""
    from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import _peler_pourtout
    vX, vM, vx0 = _terme(X), _terme(M), _terme(x0)
    Mp = Ext(vX, vM, vx0)
    cible = inclus(vM, Mp)
    bndr, _ = _peler_pourtout(cible)
    vc = var(bndr)
    hcM = N.assume(appartient(vc, vM))
    cMp = _ext_intro_M(vX, vM, vx0, vc, hcM)                 # c∈M'
    return N.generalisation(bndr, N.loi_deduction(appartient(vc, vM), cMp))


def _M_ne_Ext(X, M, x0, Hx0nd):
    """{ x₀∉champ M [Hx0nd] } ⊢ M ≠ M'.

    x₀∈champ M' (au sommet) mais x₀∉champ M ; si M=M' alors champ M=champ M' ∋ x₀
    (Leibniz), contredisant x₀∉champ M."""
    from bourbaki.ordre.iii_2_bon_ordre.zorn_zermelo.ensembles_bourbaki_witt_chaine import _ex_falso, _refute_self
    vX, vM, vx0 = _terme(X), _terme(M), _terme(x0)
    Mp = Ext(vX, vM, vx0)
    x0_champMp = _x0_dans_champ_ext(vX, vM, vx0)            # x₀∈champ M'
    Heq = N.assume(egal(vM, Mp))                           # M=M'
    # champ M = champ M'  (Leibniz : M=M' ⇒ champ M = champ M')... on transporte
    # x₀∈champ M' en x₀∈champ M via M'=M.
    Mp_eq_M = N.modus_ponens(Heq, _sym(vM, Mp))           # M'=M
    x0_champM = N.modus_ponens(x0_champMp, equivalence_avant(
        _leib_eq(Mp, vM, Mp_eq_M, lambda w: appartient(vx0, champ(w)))))  # x₀∈champ M
    falso = _ex_falso(x0_champM, Hx0nd, non(egal(vM, Mp)))
    return _refute_self(N.loi_deduction(egal(vM, Mp), falso))  # M≠M'


# ── champ M ⊂ X  (depuis M⊂X×X : dom M⊂X et img M⊂X) ──────────────────────────
def _prod_couple(u, v, A, B):
    """⊢ ((u,v)∈A×B) ⇔ (u∈A et v∈B)."""
    from bourbaki.ensembles.familles.ii_2_produit_deux_ensembles.ensembles_produit import couple_dans_produit_ssi
    return couple_dans_produit_ssi(_terme(u), _terme(v), _terme(A), _terme(B))


def _champ_inclus_X(X, M, hMsub, z="zc"):
    """{ M⊂X×X [hMsub] } ⊢ champ M ⊂ X.

    z∈champ M = z∈dom M ∪ img M ; z∈dom M ⇒ (z,b)∈M⊂X×X ⇒ z∈X ; idem img."""
    from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import _peler_pourtout
    vX, vM = _terme(X), _terme(M)
    XX = E.produit(vX, vX)
    cible = inclus(champ(vM), vX)
    bndr, _ = _peler_pourtout(cible)
    vz = var(bndr)
    hz = N.assume(appartient(vz, champ(vM)))
    # z∈dom M ⇒ z∈X  (preuve SOUS l'hypothèse z∈dom M, pour _champ_cas)
    bd = _frais(vX, vM, vz, base="bz")
    vbd = var(bd)
    Hd = N.assume(appartient(vz, E.dom(vM)))
    dax = _inst_dom(vM, vz)
    bdr = _exists_binder(dax)
    exd = N.modus_ponens(Hd, equivalence_avant(dax))
    exd = _alpha_ex(exd, bdr, bd, appartient(E.couple(vz, var(bdr)), vM))   # (∃bd)((z,bd)∈M)
    Hwd = N.assume(appartient(E.couple(vz, vbd), vM))
    zb_XX = N.modus_ponens(Hwd, instancie(hMsub, E.couple(vz, vbd)))        # (z,bd)∈X×X
    zX_d0 = conjonction_elim_gauche(N.modus_ponens(zb_XX, equivalence_avant(_prod_couple(vz, vbd, vX, vX))))  # z∈X
    but_dom = N.modus_ponens(exd, existe_elimination(N.loi_deduction(appartient(E.couple(vz, vbd), vM), zX_d0), bd))  # z∈X  [z∈dom M]
    # z∈img M ⇒ z∈X
    ai = _frais(vX, vM, vz, base="az")
    vai = var(ai)
    Hi = N.assume(appartient(vz, E.img(vM)))
    iax = _inst_img(vM, vz)
    ibr = _exists_binder(iax)
    exi = N.modus_ponens(Hi, equivalence_avant(iax))
    exi = _alpha_ex(exi, ibr, ai, appartient(E.couple(var(ibr), vz), vM))   # (∃ai)((ai,z)∈M)
    Hwi = N.assume(appartient(E.couple(vai, vz), vM))
    az_XX = N.modus_ponens(Hwi, instancie(hMsub, E.couple(vai, vz)))        # (ai,z)∈X×X
    zX_i0 = conjonction_elim_droite(N.modus_ponens(az_XX, equivalence_avant(_prod_couple(vai, vz, vX, vX))))  # z∈X
    but_img = N.modus_ponens(exi, existe_elimination(N.loi_deduction(appartient(E.couple(vai, vz), vM), zX_i0), ai))  # z∈X  [z∈img M]
    zX = _champ_cas(vM, vz, hz, but_dom, but_img)          # z∈X  [z∈champ M]
    return N.generalisation(bndr, N.loi_deduction(appartient(vz, champ(vM)), zX))


# ── M' ⊂ X×X  (couples de M ⊂ X×X ; couples (y,x₀) avec y∈champ M∪{x₀}⊂X) ──────
def Ext_inclus_produit(X, M, x0, HMsub, Hx0X, c="ce", y="ye"):
    """{ M⊂X×X [HMsub], x₀∈X [Hx0X] } ⊢ M' ⊂ X×X.

    c∈M' : soit c∈M⊂X×X, soit c=(y,x₀) avec y∈champ M∪{x₀} ; y∈champ M⊂X (ou y=x₀∈X)
    et x₀∈X ⇒ (y,x₀)∈X×X."""
    from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import _peler_pourtout
    vX, vM, vx0 = _terme(X), _terme(M), _terme(x0)
    Mp = Ext(vX, vM, vx0)
    XX = E.produit(vX, vX)
    AM = champ(vM)
    cible = inclus(Mp, XX)
    bndr, _ = _peler_pourtout(cible)
    vc = var(bndr)
    hcMp = N.assume(appartient(vc, Mp))
    # branche c∈M ⇒ c∈X×X
    HcM = N.assume(appartient(vc, vM))
    bM = N.modus_ponens(HcM, instancie(HMsub, vc))         # c∈X×X
    # branche (∃y)(c=(y,x₀) et (y∈champ M ou y=x₀)) ⇒ c∈X×X
    champX = _cut(_champ_inclus_X(vX, vM, N.assume(inclus(vM, XX))),
                  inclus(vM, XX), HMsub)                    # champ M⊂X
    vy = var(y)
    body_y = et(egal(vc, E.couple(vy, vx0)), ou(appartient(vy, AM), egal(vy, vx0)))
    Hy = N.assume(body_y)
    c_eq = conjonction_elim_gauche(Hy)                     # c=(y,x₀)
    y_disj = conjonction_elim_droite(Hy)                   # y∈champ M ou y=x₀
    # y∈X : si y∈champ M alors y∈X (champX) ; si y=x₀ alors y∈X (Hx0X Leibniz)
    Hyc = N.assume(appartient(vy, AM))
    yX_1 = N.loi_deduction(appartient(vy, AM), N.modus_ponens(Hyc, instancie(champX, vy)))
    Hyx0 = N.assume(egal(vy, vx0))
    yX_2 = N.loi_deduction(egal(vy, vx0), _leib_transport(vx0, vy,
        N.modus_ponens(Hyx0, _sym(vy, vx0)), lambda w: appartient(w, vX), Hx0X))  # y∈X
    yX = cas(y_disj, yX_1, yX_2)                           # y∈X
    yx0_XX = N.modus_ponens(conjonction_intro(yX, Hx0X),
                            equivalence_arriere(_prod_couple(vy, vx0, vX, vX)))  # (y,x₀)∈X×X
    c_XX = N.modus_ponens(yx0_XX, equivalence_arriere(
        _leib_eq(vc, E.couple(vy, vx0), c_eq, lambda w: appartient(w, XX))))  # c∈X×X
    bT_y = N.loi_deduction(body_y, c_XX)
    bT = N.modus_ponens(N.assume(existe(y, body_y)), existe_elimination(bT_y, y))  # c∈X×X  [(∃y)…]
    cXX = _ext_cas(vX, vM, vx0, vc, hcMp, bM, bT, y=y)     # c∈X×X  [c∈M']
    return N.generalisation(bndr, N.loi_deduction(appartient(vc, Mp), cXX))  # M'⊂X×X


# ── seg_initial(M, M')  (champ M est segment initial de M' : x₀ est AU SOMMET) ─
def Ext_seg_initial(X, M, x0, Hx0nd, p="p", q="q"):
    """{ x₀∉champ M [Hx0nd] } ⊢ seg_initial(M, M').

    = (∀p∀q)((p∈champ M et (q,p)∈M') ⇒ q∈champ M).  (q,p)∈M' : soit (q,p)∈M
    (⇒ q∈champ M), soit (q,p)=(y,x₀) ⇒ p=x₀ ; mais p∈champ M et p=x₀ ⇒ x₀∈champ M,
    contredit x₀∉champ M (le cas sommet est IMPOSSIBLE)."""
    from bourbaki.ensembles.ii_2_couples_produit.ensembles_couples import couple_egal_implique_composantes
    from bourbaki.ordre.iii_2_bon_ordre.zorn_zermelo.ensembles_bourbaki_witt_chaine import _ex_falso
    vX, vM, vx0 = _terme(X), _terme(M), _terme(x0)
    Mp = Ext(vX, vM, vx0)
    AM = champ(vM)
    vp, vq = var(p), var(q)
    Hpq = N.assume(et(appartient(vp, AM), _dans(vq, vp, Mp)))   # p∈champ M et (q,p)∈M'
    p_champM = conjonction_elim_gauche(Hpq)                     # p∈champ M
    qp_Mp = conjonction_elim_droite(Hpq)                        # (q,p)∈M'
    but = appartient(vq, AM)                                    # q∈champ M
    # branche (q,p)∈M ⇒ q∈champ M
    Hqp_M = N.assume(_dans(vq, vp, vM))
    bM = _couple_dans_champ_gauche(vM, vq, vp, Hqp_M)          # q∈champ M
    # branche (∃y)((q,p)=(y,x₀) et …) ⇒ p=x₀ ⇒ x₀∈champ M ⇒ ⊥ ⇒ but
    vy = var("ye")
    body_y = et(egal(E.couple(vq, vp), E.couple(vy, vx0)), ou(appartient(vy, AM), egal(vy, vx0)))
    Hy = N.assume(body_y)
    ceq = conjonction_elim_gauche(Hy)                         # (q,p)=(y,x₀)
    comps = N.modus_ponens(ceq, couple_egal_implique_composantes(vq, vp, vy, vx0))  # q=y et p=x₀
    p_eq_x0 = conjonction_elim_droite(comps)                  # p=x₀
    x0_champM = _leib_transport(vp, vx0, p_eq_x0, lambda w: appartient(w, AM), p_champM)  # x₀∈champ M
    bT_y = _ex_falso(x0_champM, Hx0nd, but)                   # q∈champ M (ex falso)
    bT = N.modus_ponens(N.assume(existe("ye", body_y)), existe_elimination(
        N.loi_deduction(body_y, bT_y), "ye"))               # q∈champ M  [(∃y)…]
    qM = _ext_cas(vX, vM, vx0, E.couple(vq, vp), qp_Mp, bM, bT, y="ye")  # q∈champ M
    body = N.loi_deduction(et(appartient(vp, AM), _dans(vq, vp, Mp)), qM)
    return N.generalisation(p, N.generalisation(q, body))    # seg_initial(M,M')


# ── sous-ensemble propre ⇒ témoin d'un point manquant (champ M ⊂ X, champ M ≠ X) ─
def _sous_propre_temoin(A, B, hAB, hAneB, z="zp"):
    """{ A⊂B [hAB], A≠B [hAneB] } ⊢ (∃z)(z∈B et z∉A)."""
    from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import dne
    from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_theoremes import extensionnalite_appliquee
    from bourbaki.ordre.iii_2_bon_ordre.zorn_zermelo.ensembles_bourbaki_witt_chaine import _ex_falso, _refute_self, _neg_impl_equiv
    from bourbaki.logique.i_3_quantifies.tactiques_abrege_quantif import congruence_existe
    vA, vB = _terme(A), _terme(B)
    a1 = extensionnalite_appliquee(vA, vB)                # (A⊂B et B⊂A)⇒A=B
    # On LIT le terme B⊂A tel qu'utilisé par a1 (binder canonique de ⊂), et son
    # nom de lieur, pour rester syntaxiquement cohérent.
    BsubA = a1.conclusion.sous[0].sous[0].sous[0].sous[1] if False else inclus(vB, vA)
    # binder réel de B⊂A : pelage du ∀ (encodé non-∃-non)
    from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import _peler_pourtout
    zb, _ = _peler_pourtout(BsubA)
    vz = var(zb)
    HBA = N.assume(BsubA)
    A_eq_B = N.modus_ponens(conjonction_intro(hAB, HBA), a1)
    nBA = _ex_falso(A_eq_B, hAneB, non(BsubA))
    not_BsubA = _refute_self(N.loi_deduction(BsubA, nBA))
    Rz = impl(appartient(vz, vB), appartient(vz, vA))
    ex_negRz = N.modus_ponens(not_BsubA, dne(existe(zb, non(Rz))))
    eqv = _neg_impl_equiv(appartient(vz, vB), appartient(vz, vA))
    return N.modus_ponens(ex_negRz, equivalence_avant(congruence_existe(eqv, zb)))


# ════════════════════════════════════════════════════════════════════════════
#  ÉTAPE 4 (assemblage) — un M MAXIMAL a champ(M)=X.
#  ⚠ CONDITIONNÉ à `Ext_dans_W` (le bon-ordre du graphe étendu M', cf. REPORT).
# ════════════════════════════════════════════════════════════════════════════
def maximal_champ_eq_X(X="X", M="M", x0="x0", lemme_ext_dans_W=None):
    """{ element_maximal(Θ,W,M) } ⊢ champ(M) = X.   [CONDITIONNÉ à Ext_dans_W.]

    Par l'absurde : si champ M ≠ X (champ M⊂X car M∈W), ∃x₀∈X∖champ M ; M' (x₀ au
    sommet) est un bon ordre partiel (Ext_dans_W) Θ-strictement plus grand que M
    ((M,M')∈Θ via seg_initial, M≠M'), ce qui contredit la maximalité de M.

    `lemme_ext_dans_W(X,M,x0)` doit fournir ⊢ M'∈W sous { x₀∈X, x₀∉champ M, M∈W }
    (et éventuellement totalement_ordonne — ici M∈W suffit)."""
    from bourbaki.ordre.iii_2_bon_ordre.zorn_zermelo.ensembles_bourbaki_witt_chaine import _ex_falso
    from bourbaki.ordre.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_relation import element_maximal
    if lemme_ext_dans_W is None:
        lemme_ext_dans_W = Ext_dans_W
    vX, vM, vx0 = var(X), var(M), var(x0)
    Theta_set, W_set = Theta(vX), W(vX)
    Mp = Ext(vX, vM, vx0)
    AM = champ(vM)
    Hmax = N.assume(element_maximal(Theta_set, W_set, vM, "x"))   # element_maximal(Θ,W,M)
    M_in_W = conjonction_elim_gauche(Hmax)                   # M∈W
    max_body = conjonction_elim_droite(Hmax)                 # (∀g)((g∈W et (M,g)∈Θ)⇒g=M)
    # M⊂X×X, champ M⊂X
    bop_M = _bo_de_W(vX, vM, M_in_W)                        # bon_ordre_partiel(M,X)
    M_XX = conjonction_elim_gauche(bop_M)                  # M⊂X×X
    champM_X = _cut(_champ_inclus_X(vX, vM, N.assume(inclus(vM, E.produit(vX, vX)))),
                    inclus(vM, E.produit(vX, vX)), M_XX)   # champ M⊂X
    but = egal(AM, vX)                                      # champ M = X
    # tiers exclu sur champ M = X
    HchNE = N.assume(non(but))                             # champ M ≠ X
    ex_x0 = _sous_propre_temoin(AM, vX, champM_X, HchNE)   # (∃·)(·∈X et ·∉champ M)
    src_b = ex_x0.conclusion.lieur                         # binder réel du ∃
    ex_x0 = _alpha_ex(ex_x0, src_b, x0, et(appartient(var(src_b), vX), non(appartient(var(src_b), AM))))
    Hw = N.assume(et(appartient(vx0, vX), non(appartient(vx0, AM))))
    Hx0X = conjonction_elim_gauche(Hw)                     # x₀∈X
    Hx0nd = conjonction_elim_droite(Hw)                    # x₀∉champ M
    # M'∈W (lemme conditionnel)
    Mp_W = lemme_ext_dans_W(X, M, x0)
    Mp_W = _cut(Mp_W, appartient(vx0, vX), Hx0X)
    Mp_W = _cut(Mp_W, non(appartient(vx0, AM)), Hx0nd)
    Mp_W = _cut(Mp_W, appartient(vM, W_set), M_in_W)       # M'∈W  [Hw, Hmax]
    # (M,M')∈Θ : M∈W, M'∈W, M⊂M', seg_initial(M,M')
    M_Mp = _M_inclus_Ext(vX, vM, vx0)                     # M⊂M'
    seg = _cut(Ext_seg_initial(vX, vM, vx0, N.assume(non(appartient(vx0, AM)))),
               non(appartient(vx0, AM)), Hx0nd)            # seg_initial(M,M')
    M_Mp_Theta = _Theta_intro(vX, vM, Mp, M_in_W, Mp_W, M_Mp, seg)  # (M,M')∈Θ
    # maximalité en M' : (M'∈W et (M,M')∈Θ) ⇒ M'=M
    max_inst = instancie(max_body, Mp)
    Mp_eq_M = N.modus_ponens(conjonction_intro(Mp_W, M_Mp_Theta), max_inst)  # M'=M
    M_eq_Mp = N.modus_ponens(Mp_eq_M, _sym(Mp, vM))       # M=M'
    M_ne_Mp = _cut(_M_ne_Ext(vX, vM, vx0, N.assume(non(appartient(vx0, AM)))),
                   non(appartient(vx0, AM)), Hx0nd)        # M≠M'
    falso = _ex_falso(M_eq_Mp, M_ne_Mp, but)              # champ M=X (ex falso)  [Hw, …]
    # éliminer ∃x₀
    after_x0 = N.modus_ponens(ex_x0, existe_elimination(
        N.loi_deduction(et(appartient(vx0, vX), non(appartient(vx0, AM))), falso), x0))  # champ M=X  [champ M≠X]
    cas_NE = N.loi_deduction(non(but), after_x0)
    # cas champ M = X : trivial
    cas_EQ = N.loi_deduction(but, N.assume(but))
    return cas(tiers_exclu(but), cas_EQ, cas_NE)          # champ M = X  [Hmax]


# ════════════════════════════════════════════════════════════════════════════
#  Ext_dans_W : M' (x₀ au sommet) est un BON ORDRE PARTIEL de X.  LE bon-ordre du
#  graphe étendu : champ M'=champ M∪{x₀} bien ordonné (M bien ordonne champ M ; x₀
#  est strictement au-dessus de tout).
# ════════════════════════════════════════════════════════════════════════════
def _ext_top_comps(X, M, x0, u, v, htop):
    """De ⊢ (∃y)((u,v)=(y,x₀) et (y∈champ M ou y=x₀)) [htop] déduit
       ⊢ ( v=x₀ et (u∈champ M ou u=x₀) ).

    Le couple (u,v) étant (y,x₀) : u=y, v=x₀ ; donc v=x₀ et (u∈champ M ou u=x₀)."""
    from bourbaki.ensembles.ii_2_couples_produit.ensembles_couples import couple_egal_implique_composantes
    vM, vx0, vu, vv = _terme(M), _terme(x0), _terme(u), _terme(v)
    AM = champ(vM)
    vy = var("ye")
    body_y = et(egal(E.couple(vu, vv), E.couple(vy, vx0)), ou(appartient(vy, AM), egal(vy, vx0)))
    Hy = N.assume(body_y)
    ceq = conjonction_elim_gauche(Hy)                        # (u,v)=(y,x₀)
    ydisj = conjonction_elim_droite(Hy)                      # y∈champ M ou y=x₀
    comps = N.modus_ponens(ceq, couple_egal_implique_composantes(vu, vv, vy, vx0))  # u=y et v=x₀
    u_eq_y = conjonction_elim_gauche(comps)                  # u=y
    v_eq_x0 = conjonction_elim_droite(comps)                 # v=x₀
    # (u∈champ M ou u=x₀) : transporter ydisj par u=y
    y_eq_u = N.modus_ponens(u_eq_y, _sym(vu, vy))           # y=u
    udisj = _leib_transport(vy, vu, y_eq_u,
        lambda w: ou(appartient(w, AM), egal(w, vx0)), ydisj)  # u∈champ M ou u=x₀
    res = conjonction_intro(v_eq_x0, udisj)                  # v=x₀ et (u∈champ M ou u=x₀)
    return N.modus_ponens(htop, existe_elimination(N.loi_deduction(body_y, res), "ye"))


def _x0_pas_dans_dom_M(M, x0, Hx0nd, b="yb"):
    """{ x₀∉champ M [Hx0nd] } ⊢ ¬( (x₀,b)∈M )  pour tout TERME b.

    (x₀,b)∈M ⇒ x₀∈dom M ⊂ champ M, contredit x₀∉champ M."""
    from bourbaki.ordre.iii_2_bon_ordre.zorn_zermelo.ensembles_bourbaki_witt_chaine import _ex_falso, _refute_self
    vM, vx0, vb = _terme(M), _terme(x0), _terme(b)
    Hin = N.assume(appartient(E.couple(vx0, vb), vM))
    x0_champ = _couple_dans_champ_gauche(vM, vx0, vb, Hin)   # x₀∈champ M
    falso = _ex_falso(x0_champ, Hx0nd, non(appartient(E.couple(vx0, vb), vM)))
    return _refute_self(N.loi_deduction(appartient(E.couple(vx0, vb), vM), falso))


def _x0_pas_dans_img_M(M, x0, Hx0nd, a="xa"):
    """{ x₀∉champ M [Hx0nd] } ⊢ ¬( (a,x₀)∈M )  pour tout TERME a."""
    from bourbaki.ordre.iii_2_bon_ordre.zorn_zermelo.ensembles_bourbaki_witt_chaine import _ex_falso, _refute_self
    vM, vx0, va = _terme(M), _terme(x0), _terme(a)
    Hin = N.assume(appartient(E.couple(va, vx0), vM))
    x0_champ = _couple_dans_champ_droite(vM, va, vx0, Hin)   # x₀∈champ M
    falso = _ex_falso(x0_champ, Hx0nd, non(appartient(E.couple(va, vx0), vM)))
    return _refute_self(N.loi_deduction(appartient(E.couple(va, vx0), vM), falso))


def _Ext_transitif(X, M, x0, GW, Hx0nd, a="a", b="b", c="c"):
    """{ M∈W [GW], x₀∉champ M [Hx0nd] } ⊢ ordre_transitif(R_M').

    Cas sur (a,b),(b,c)∈M' : (M,M) M transitif ; (M,top) c=x₀, a∈champ M ⇒ (a,x₀)
    top ; (top,M) b=x₀ et (x₀,c)∈M IMPOSSIBLE (x₀∉champ M) ; (top,top) c=x₀,
    a∈champ M∪{x₀} ⇒ (a,x₀) top."""
    from bourbaki.ordre.iii_2_bon_ordre.zorn_zermelo.ensembles_bourbaki_witt_chaine import _ex_falso
    vX, vM, vx0 = _terme(X), _terme(M), _terme(x0)
    Mp = Ext(vX, vM, vx0)
    AM = champ(vM)
    va, vb, vc = var(a), var(b), var(c)
    cab, cbc, cac = E.couple(va, vb), E.couple(vb, vc), E.couple(va, vc)
    hyp = et(appartient(cab, Mp), appartient(cbc, Mp))
    H = N.assume(hyp)
    hab = conjonction_elim_gauche(H)                        # (a,b)∈M'
    hbc = conjonction_elim_droite(H)                        # (b,c)∈M'
    but = _dans(va, vc, Mp)                                 # (a,c)∈M'
    trans_M = _transitif_de_W(vX, vM, GW)                  # ordre_transitif(R_M)
    # helper : (a,x₀)∈M' top depuis a∈champ M
    def ac_top_de_champM(a_champM):
        hy = _ou_gauche(a_champM, egal(va, vx0))           # a∈champ M ou a=x₀
        return _ext_intro_top(vX, vM, vx0, va, hy)        # (a,x₀)∈M'
    # ── branche (a,b)∈M ──────────────────────────────────────────────────────
    def sous_ab_M(hab_M):
        a_champM = _couple_dans_champ_gauche(vM, va, vb, hab_M)  # a∈champ M
        # (b,c)∈M ⇒ M transitif ⇒ (a,c)∈M⊂M'
        def sous_bc_M(hbc_M):
            ac_M = N.modus_ponens(conjonction_intro(hab_M, hbc_M),
                                  instancie(instancie(instancie(trans_M, va), vb), vc))  # (a,c)∈M
            return _ext_intro_M(vX, vM, vx0, cac, ac_M)
        # (b,c) top ⇒ c=x₀ ⇒ (a,c)=(a,x₀) top (a∈champ M)
        def sous_bc_top(hbc_top):
            comps = _ext_top_comps(vX, vM, vx0, vb, vc, hbc_top)  # c=x₀ et (b∈champ M ou b=x₀)
            c_eq_x0 = conjonction_elim_gauche(comps)        # c=x₀
            ax0 = ac_top_de_champM(a_champM)                # (a,x₀)∈M'
            x0_eq_c = N.modus_ponens(c_eq_x0, _sym(vc, vx0))  # x₀=c
            return _leib_transport(vx0, vc, x0_eq_c, lambda w: _dans(va, w, Mp), ax0)  # (a,c)∈M'
        return _ext_cas(vX, vM, vx0, cbc, hbc, sous_bc_M(N.assume(appartient(cbc, vM))),
                        sous_bc_top(N.assume(_corps_Ext(vX, vM, vx0, cbc).sous[1])))
    # ── branche (a,b) top ────────────────────────────────────────────────────
    def sous_ab_top(hab_top):
        comps = _ext_top_comps(vX, vM, vx0, va, vb, hab_top)  # b=x₀ et (a∈champ M ou a=x₀)
        b_eq_x0 = conjonction_elim_gauche(comps)            # b=x₀
        a_disj = conjonction_elim_droite(comps)             # a∈champ M ou a=x₀
        # (b,c)∈M ⇒ (x₀,c)∈M IMPOSSIBLE
        def sous_bc_M(hbc_M):
            x0c_M = _leib_transport(vb, vx0, b_eq_x0, lambda w: _dans(w, vc, vM), hbc_M)  # (x₀,c)∈M
            not_x0c = instancie(N.generalisation("yb",
                _cut(_x0_pas_dans_dom_M(vM, vx0, N.assume(non(appartient(vx0, AM))), "yb"),
                     non(appartient(vx0, AM)), Hx0nd)), vc)  # ¬((x₀,c)∈M)
            return _ex_falso(x0c_M, not_x0c, but)           # (a,c)∈M' (ex falso)
        # (b,c) top ⇒ c=x₀ ; (a,c)=(a,x₀) top avec a∈champ M∪{x₀}
        def sous_bc_top(hbc_top):
            comps2 = _ext_top_comps(vX, vM, vx0, vb, vc, hbc_top)  # c=x₀ et …
            c_eq_x0 = conjonction_elim_gauche(comps2)        # c=x₀
            ax0 = _ext_intro_top(vX, vM, vx0, va, a_disj)   # (a,x₀)∈M'
            x0_eq_c = N.modus_ponens(c_eq_x0, _sym(vc, vx0))
            return _leib_transport(vx0, vc, x0_eq_c, lambda w: _dans(va, w, Mp), ax0)  # (a,c)∈M'
        return _ext_cas(vX, vM, vx0, cbc, hbc, sous_bc_M(N.assume(appartient(cbc, vM))),
                        sous_bc_top(N.assume(_corps_Ext(vX, vM, vx0, cbc).sous[1])))
    res = _ext_cas(vX, vM, vx0, cab, hab, sous_ab_M(N.assume(appartient(cab, vM))),
                   sous_ab_top(N.assume(_corps_Ext(vX, vM, vx0, cab).sous[1])))
    body = N.loi_deduction(hyp, res)
    return N.generalisation(a, N.generalisation(b, N.generalisation(c, body)))


def _Ext_antisym(X, M, x0, GW, Hx0nd, a="a", b="b"):
    """{ M∈W [GW], x₀∉champ M [Hx0nd] } ⊢ ordre_antisymetrique(R_M').

    Cas (M,M) M antisym ; (M,top) a=x₀ et (x₀,b)∈M IMPOSSIBLE ; (top,M) b=x₀ et
    (x₀,a)∈M IMPOSSIBLE ; (top,top) b=x₀ et a=x₀ ⇒ a=b."""
    from bourbaki.ordre.iii_2_bon_ordre.zorn_zermelo.ensembles_bourbaki_witt_chaine import _ex_falso
    from bourbaki.logique.i_4_egalitaires.tactiques_abrege_egalite import composer_egalites
    vX, vM, vx0 = _terme(X), _terme(M), _terme(x0)
    Mp = Ext(vX, vM, vx0)
    AM = champ(vM)
    va, vb = var(a), var(b)
    cab, cba = E.couple(va, vb), E.couple(vb, va)
    hyp = et(appartient(cab, Mp), appartient(cba, Mp))
    H = N.assume(hyp)
    hab = conjonction_elim_gauche(H)
    hba = conjonction_elim_droite(H)
    but = egal(va, vb)
    anti_M = _antisym_de_W(vX, vM, GW)                     # ordre_antisymetrique(R_M)
    not_x0dom = lambda t: instancie(N.generalisation("yb",
        _cut(_x0_pas_dans_dom_M(vM, vx0, N.assume(non(appartient(vx0, AM))), "yb"),
             non(appartient(vx0, AM)), Hx0nd)), t)          # ¬((x₀,t)∈M)
    # branche (a,b)∈M
    def sous_ab_M(hab_M):
        def sous_ba_M(hba_M):
            return N.modus_ponens(conjonction_intro(hab_M, hba_M),
                                  instancie(instancie(anti_M, va), vb))  # a=b
        def sous_ba_top(hba_top):  # (b,a) top ⇒ a=x₀ ; (a,b)=(x₀,b)∈M impossible
            comps = _ext_top_comps(vX, vM, vx0, vb, va, hba_top)  # a=x₀ et …
            a_eq_x0 = conjonction_elim_gauche(comps)        # a=x₀
            x0b_M = _leib_transport(va, vx0, a_eq_x0, lambda w: _dans(w, vb, vM), hab_M)  # (x₀,b)∈M
            return _ex_falso(x0b_M, not_x0dom(vb), but)
        return _ext_cas(vX, vM, vx0, cba, hba, sous_ba_M(N.assume(appartient(cba, vM))),
                        sous_ba_top(N.assume(_corps_Ext(vX, vM, vx0, cba).sous[1])))
    # branche (a,b) top
    def sous_ab_top(hab_top):
        comps = _ext_top_comps(vX, vM, vx0, va, vb, hab_top)  # b=x₀ et (a∈champ M ou a=x₀)
        b_eq_x0 = conjonction_elim_gauche(comps)            # b=x₀
        def sous_ba_M(hba_M):  # (b,a)=(x₀,a)∈M impossible
            x0a_M = _leib_transport(vb, vx0, b_eq_x0, lambda w: _dans(w, va, vM), hba_M)  # (x₀,a)∈M
            return _ex_falso(x0a_M, not_x0dom(va), but)
        def sous_ba_top(hba_top):  # (b,a) top ⇒ a=x₀ ; a=x₀=b ⇒ a=b
            comps2 = _ext_top_comps(vX, vM, vx0, vb, va, hba_top)  # a=x₀ et …
            a_eq_x0 = conjonction_elim_gauche(comps2)        # a=x₀
            x0_eq_b = N.modus_ponens(b_eq_x0, _sym(vb, vx0))  # x₀=b
            return composer_egalites(a_eq_x0, x0_eq_b)       # a=b
        return _ext_cas(vX, vM, vx0, cba, hba, sous_ba_M(N.assume(appartient(cba, vM))),
                        sous_ba_top(N.assume(_corps_Ext(vX, vM, vx0, cba).sous[1])))
    res = _ext_cas(vX, vM, vx0, cab, hab, sous_ab_M(N.assume(appartient(cab, vM))),
                   sous_ab_top(N.assume(_corps_Ext(vX, vM, vx0, cab).sous[1])))
    body = N.loi_deduction(hyp, res)
    return N.generalisation(a, N.generalisation(b, body))


def _Ext_refl_impl(X, M, x0, GW, Hx0nd, a="a", b="b"):
    """{ M∈W [GW], x₀∉champ M [Hx0nd] } ⊢ ordre_reflexif_implicite(R_M').

    (a,b)∈M' ⇒ ((a,a)∈M' et (b,b)∈M').  Cas (a,b)∈M : M refl_impl ⇒ (a,a),(b,b)∈M⊂M'.
    Cas (a,b) top : b=x₀, a∈champ M∪{x₀} ; (a,a)∈M' : si a∈champ M, M refl ⇒ (a,a)∈M⊂M' ;
    si a=x₀, (x₀,x₀) top.  (b,b)=(x₀,x₀) top."""
    vX, vM, vx0 = _terme(X), _terme(M), _terme(x0)
    Mp = Ext(vX, vM, vx0)
    AM = champ(vM)
    va, vb = var(a), var(b)
    cab = E.couple(va, vb)
    caa, cbb = E.couple(va, va), E.couple(vb, vb)
    Hab = N.assume(appartient(cab, Mp))                    # (a,b)∈M'
    refl_M = _refl_impl_de_W(vX, vM, GW)                  # ordre_reflexif_implicite(R_M)
    refl_dans_M = _refl_dans_de_W(vX, vM, GW)            # (∀x)((x,x)∈M ⇔ x∈champ M)
    # (x₀,x₀) top
    x0_top = _ext_intro_top(vX, vM, vx0,
        vx0, _ou_droite(N.reflexivite(vx0), appartient(vx0, AM)))  # (x₀,x₀)∈M'
    # branche (a,b)∈M
    def sous_M(hab_M):
        conj = N.modus_ponens(hab_M, instancie(instancie(refl_M, va), vb))  # (a,a)∈M et (b,b)∈M
        aaM = conjonction_elim_gauche(conj)
        bbM = conjonction_elim_droite(conj)
        return conjonction_intro(_ext_intro_M(vX, vM, vx0, caa, aaM),
                                 _ext_intro_M(vX, vM, vx0, cbb, bbM))  # ((a,a)∈M' et (b,b)∈M')
    # branche (a,b) top : b=x₀ et (a∈champ M ou a=x₀)
    def sous_top(hab_top):
        comps = _ext_top_comps(vX, vM, vx0, va, vb, hab_top)  # b=x₀ et (a∈champ M ou a=x₀)
        b_eq_x0 = conjonction_elim_gauche(comps)
        a_disj = conjonction_elim_droite(comps)
        # (a,a)∈M' : a∈champ M ⇒ (a,a)∈M (refl_dans) ⇒ M' ; a=x₀ ⇒ (x₀,x₀) top
        Ha_champ = N.assume(appartient(va, AM))
        aaM = N.modus_ponens(Ha_champ, equivalence_arriere(instancie(refl_dans_M, va)))  # (a,a)∈M
        aaMp_1 = N.loi_deduction(appartient(va, AM), _ext_intro_M(vX, vM, vx0, caa, aaM))
        Ha_x0 = N.assume(egal(va, vx0))
        x0_eq_a = N.modus_ponens(Ha_x0, _sym(va, vx0))      # x₀=a
        aaMp_2 = N.loi_deduction(egal(va, vx0), _leib_transport(vx0, va, x0_eq_a,
            lambda w: _dans(w, w, Mp), x0_top))             # (a,a)∈M'
        aaMp = cas(a_disj, aaMp_1, aaMp_2)                  # (a,a)∈M'
        # (b,b)=(x₀,x₀) top
        x0_eq_b = N.modus_ponens(b_eq_x0, _sym(vb, vx0))
        bbMp = _leib_transport(vx0, vb, x0_eq_b, lambda w: _dans(w, w, Mp), x0_top)  # (b,b)∈M'
        return conjonction_intro(aaMp, bbMp)
    res = _ext_cas(vX, vM, vx0, cab, Hab, sous_M(N.assume(appartient(cab, vM))),
                   sous_top(N.assume(_corps_Ext(vX, vM, vx0, cab).sous[1])))
    body = N.loi_deduction(appartient(cab, Mp), res)
    return N.generalisation(a, N.generalisation(b, body))


def _champ_ext_disj(X, M, x0, x, hx_champMp):
    """⊢ x∈champ M' [hx_champMp] ⇒ ⊢ ( x∈champ M ou x=x₀ ).

    x∈champ M' = x∈dom M'∪img M' ; témoin couple (x,·)/(·,x)∈M' soit dans M
    (⇒ x∈champ M), soit au sommet (1er point ⇒ x∈champ M∪{x₀} ; 2e point ⇒ x=x₀)."""
    vX, vM, vx0 = _terme(X), _terme(M), _terme(x0)
    vx = _terme(x)
    Mp = Ext(vX, vM, vx0)
    AM = champ(vM)
    but = ou(appartient(vx, AM), egal(vx, vx0))
    # cas x∈dom M'
    bd = _frais(vX, vM, vx0, vx, base="bz")
    vbd = var(bd)
    Hd = N.assume(appartient(vx, E.dom(Mp)))
    dax = _inst_dom(Mp, vx)
    bdr = _exists_binder(dax)
    exd = N.modus_ponens(Hd, equivalence_avant(dax))
    exd = _alpha_ex(exd, bdr, bd, appartient(E.couple(vx, var(bdr)), Mp))   # (∃bd)((x,bd)∈M')
    Hxb = N.assume(appartient(E.couple(vx, vbd), Mp))
    #   (x,bd)∈M ⇒ x∈champ M ; (x,bd) top ⇒ x∈champ M ou x=x₀
    def d_M(h):
        return _ou_gauche(_couple_dans_champ_gauche(vM, vx, vbd, h), egal(vx, vx0))
    def d_top(h):
        comps = _ext_top_comps(vX, vM, vx0, vx, vbd, h)  # bd=x₀ et (x∈champ M ou x=x₀)
        return conjonction_elim_droite(comps)            # x∈champ M ou x=x₀
    res_xb = _ext_cas(vX, vM, vx0, E.couple(vx, vbd), Hxb,
                      d_M(N.assume(appartient(E.couple(vx, vbd), vM))),
                      d_top(N.assume(_corps_Ext(vX, vM, vx0, E.couple(vx, vbd)).sous[1])))
    but_dom = N.modus_ponens(exd, existe_elimination(
        N.loi_deduction(appartient(E.couple(vx, vbd), Mp), res_xb), bd))  # but  [x∈dom M']
    # cas x∈img M'
    ai = _frais(vX, vM, vx0, vx, base="az")
    vai = var(ai)
    Hi = N.assume(appartient(vx, E.img(Mp)))
    iax = _inst_img(Mp, vx)
    ibr = _exists_binder(iax)
    exi = N.modus_ponens(Hi, equivalence_avant(iax))
    exi = _alpha_ex(exi, ibr, ai, appartient(E.couple(var(ibr), vx), Mp))   # (∃ai)((ai,x)∈M')
    Hax = N.assume(appartient(E.couple(vai, vx), Mp))
    def i_M(h):
        return _ou_gauche(_couple_dans_champ_droite(vM, vai, vx, h), egal(vx, vx0))
    def i_top(h):
        comps = _ext_top_comps(vX, vM, vx0, vai, vx, h)  # x=x₀ et (ai∈champ M ou ai=x₀)
        return _ou_droite(conjonction_elim_gauche(comps), appartient(vx, AM))  # x∈champ M ou x=x₀
    res_ax = _ext_cas(vX, vM, vx0, E.couple(vai, vx), Hax,
                      i_M(N.assume(appartient(E.couple(vai, vx), vM))),
                      i_top(N.assume(_corps_Ext(vX, vM, vx0, E.couple(vai, vx)).sous[1])))
    but_img = N.modus_ponens(exi, existe_elimination(
        N.loi_deduction(appartient(E.couple(vai, vx), Mp), res_ax), ai))  # but  [x∈img M']
    return _champ_cas(Mp, vx, hx_champMp, but_dom, but_img)  # but  [x∈champ M']


def _Ext_refl_dans(X, M, x0, GW, x="x"):
    """{ M∈W [GW] } ⊢ est_reflexive_dans_ordre(R_M', champ M').

    = (∀x)((x,x)∈M' ⇔ x∈champ M').  ⇒ : (x,x)∈M'⇒x∈dom M'⊂champ M'.  ⇐ : x∈champ M'
    ⇒ x∈champ M (⇒(x,x)∈M⊂M') ou x=x₀ (⇒(x₀,x₀) top)."""
    vX, vM, vx0 = _terme(X), _terme(M), _terme(x0)
    vx = var(x)
    Mp = Ext(vX, vM, vx0)
    AMp = champ(Mp)
    cxx = E.couple(vx, vx)
    refl_dans_M = _refl_dans_de_W(vX, vM, GW)             # (∀x)((x,x)∈M ⇔ x∈champ M)
    x0_top = _ext_intro_top(vX, vM, vx0, vx0,
        _ou_droite(N.reflexivite(vx0), appartient(vx0, champ(vM))))  # (x₀,x₀)∈M'
    # ⇒
    Hxx = N.assume(appartient(cxx, Mp))
    fwd = N.loi_deduction(appartient(cxx, Mp), _couple_dans_champ_gauche(Mp, vx, vx, Hxx))  # x∈champ M'
    # ⇐
    Hxc = N.assume(appartient(vx, AMp))
    disj = _champ_ext_disj(vX, vM, vx0, vx, Hxc)         # x∈champ M ou x=x₀
    Hxm = N.assume(appartient(vx, champ(vM)))
    xxM = N.modus_ponens(Hxm, equivalence_arriere(instancie(refl_dans_M, vx)))  # (x,x)∈M
    b1 = N.loi_deduction(appartient(vx, champ(vM)), _ext_intro_M(vX, vM, vx0, cxx, xxM))  # (x,x)∈M'
    Hx_x0 = N.assume(egal(vx, vx0))
    x0_eq_x = N.modus_ponens(Hx_x0, _sym(vx, vx0))
    b2 = N.loi_deduction(egal(vx, vx0), _leib_transport(vx0, vx, x0_eq_x,
        lambda w: _dans(w, w, Mp), x0_top))              # (x,x)∈M'
    xxMp = cas(disj, b1, b2)                             # (x,x)∈M'
    bwd = N.loi_deduction(appartient(vx, AMp), xxMp)
    return N.generalisation(x, conjonction_intro(fwd, bwd))


def _Ext_rel_ordre_dans(X, M, x0, GW, Hx0nd):
    """{ M∈W [GW], x₀∉champ M [Hx0nd] } ⊢ est_relation_ordre_dans(R_M', champ M')."""
    trans = _Ext_transitif(X, M, x0, GW, Hx0nd, "x", "y", "z")
    anti = _Ext_antisym(X, M, x0, GW, Hx0nd, "x", "y")
    refl_impl = _Ext_refl_impl(X, M, x0, GW, Hx0nd, "x", "y")
    refl_dans = _Ext_refl_dans(X, M, x0, GW, "x")
    rel_ordre = conjonction_intro(conjonction_intro(trans, anti), refl_impl)
    return conjonction_intro(rel_ordre, refl_dans)


def _ms_dans_ext(X, M, x0, m, s, GW, m_champM, m_least, hsS, vS_term):
    """{ M∈W [GW], m∈champ M [m_champM], m_least=(∀w)(w∈S∩champ M⇒(m,w)∈M),
        s∈S [hsS], S⊂champ M' (porté) } ⊢ (m,s)∈M'.

    s∈champ M' ⇒ s∈champ M (⇒ s∈S∩champ M ⇒ (m,s)∈M⊂M') ou s=x₀ (⇒ (m,x₀)∈M' top,
    m∈champ M)."""
    vX, vM, vx0 = _terme(X), _terme(M), _terme(x0)
    vm, vs, vSt = _terme(m), _terme(s), _terme(vS_term)
    Mp = Ext(vX, vM, vx0)
    AM = champ(vM)
    Inter = E.intersection(vSt, AM)
    HSsub = N.assume(inclus(vSt, champ(Mp)))               # S⊂champ M'
    s_champMp = N.modus_ponens(hsS, instancie(HSsub, vs))  # s∈champ M'
    disj = _champ_ext_disj(vX, vM, vx0, vs, s_champMp)     # s∈champ M ou s=x₀
    but = _dans(vm, vs, Mp)
    # s∈champ M ⇒ (m,s)∈M⊂M'
    Hs_champM = N.assume(appartient(vs, AM))
    s_inter = _inter_intro(vSt, AM, vs, hsS, Hs_champM)    # s∈S∩champ M
    ms_M = N.modus_ponens(s_inter, instancie(m_least, vs))  # (m,s)∈M
    b1 = N.loi_deduction(appartient(vs, AM), _ext_intro_M(vX, vM, vx0, E.couple(vm, vs), ms_M))
    # s=x₀ ⇒ (m,x₀)∈M' top (m∈champ M) ⇒ (m,s)∈M'
    Hs_x0 = N.assume(egal(vs, vx0))
    mx0 = _ext_intro_top(vX, vM, vx0, vm, _ou_gauche(m_champM, egal(vm, vx0)))  # (m,x₀)∈M'
    x0_eq_s = N.modus_ponens(Hs_x0, _sym(vs, vx0))
    b2 = N.loi_deduction(egal(vs, vx0), _leib_transport(vx0, vs, x0_eq_s,
        lambda w: _dans(vm, w, Mp), mx0))                 # (m,s)∈M'
    return cas(disj, b1, b2)                              # (m,s)∈M'


def _Ext_bien_ordonne_corps(X, M, x0, GW, Hx0nd, S="S", aa="a", ww="w", s0="s0", m="mw"):
    """{ M∈W [GW], x₀∉champ M [Hx0nd] } ⊢
       (∀S)((S⊂champ M' et ¬(S=∅)) ⇒ (∃a)(a∈S et (∀w)(w∈S⇒(a,w)∈M'))).

    Tiers exclu sur S∩champ M=∅ : si ≠∅, plus petit élt m de S∩champ M (M bien
    ordonne champ M) = plus petit de S (x₀ au-dessus) ; si =∅, S⊂{x₀}, x₀∈S est le
    plus petit."""
    from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_vide import non_vide_ssi_element
    from bourbaki.ordre.iii_2_bon_ordre.zorn_zermelo.ensembles_bourbaki_witt_chaine import _ex_falso
    vX, vM, vx0 = _terme(X), _terme(M), _terme(x0)
    vS = var(S)
    Mp = Ext(vX, vM, vx0)
    AMp = champ(Mp)
    AM = champ(vM)
    Inter = E.intersection(vS, AM)
    hypS = et(inclus(vS, AMp), non(egal(vS, E.VIDE)))
    HypS = N.assume(hypS)
    Ssub = conjonction_elim_gauche(HypS)                  # S⊂champ M'
    Snv = conjonction_elim_droite(HypS)                   # ¬(S=∅)
    petit = lambda t: et(appartient(t, vS),
        pourtout(ww, impl(appartient(var(ww), vS), _dans(t, var(ww), Mp))))
    but_ex = existe(aa, et(appartient(var(aa), vS),
        pourtout(ww, impl(appartient(var(ww), vS), _dans(var(aa), var(ww), Mp)))))
    # ── cas S∩champ M ≠ ∅ : plus petit m de S∩champ M ───────────────────────────
    HinterNE = N.assume(non(egal(Inter, E.VIDE)))         # S∩champ M ≠ ∅
    ex_s0 = N.modus_ponens(HinterNE, equivalence_avant(non_vide_ssi_element(Inter)))  # (∃z)(z∈Inter)
    ex_s0 = _alpha_ex(ex_s0, "z", s0, appartient(var("z"), Inter))
    vs0 = var(s0)
    Hs0 = N.assume(appartient(vs0, Inter))               # s₀∈S∩champ M
    ex_m = _least_inter_champ(vX, "Dummy", vS, vM, GW, vs0, Hs0, a=m)  # (∃m)(m∈Inter et …)
    R_m = et(appartient(var(m), Inter),
             pourtout("w", impl(appartient(var("w"), Inter), _dans(var(m), var("w"), vM))))
    vm = var(m)
    Hm = N.assume(R_m)
    m_inter = conjonction_elim_gauche(Hm)                # m∈S∩champ M
    m_least = conjonction_elim_droite(Hm)                # (∀w)(w∈Inter⇒(m,w)∈M)
    m_S = _inter_gauche(vS, AM, vm, m_inter)            # m∈S
    m_champM = _inter_droite(vS, AM, vm, m_inter)       # m∈champ M
    # (∀s)(s∈S⇒(m,s)∈M')
    vs = var("se")
    Hs = N.assume(appartient(vs, vS))
    ms = _ms_dans_ext(vX, vM, vx0, vm, vs, GW, m_champM, m_least, Hs, vS)
    ms = _cut(ms, inclus(vS, AMp), Ssub)
    all_s = N.generalisation("se", N.loi_deduction(appartient(vs, vS), ms))
    from bourbaki.logique.i_3_quantifies.tactiques_abrege_quantif import alpha_pour_tout
    if "se" != ww:
        _, inner = __import__("bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2",
                              fromlist=["_peler_pourtout"])._peler_pourtout(all_s.conclusion)
        all_s = N.modus_ponens(all_s, equivalence_avant(alpha_pour_tout("se", ww, inner)))
    least_m = conjonction_intro(m_S, all_s)             # m∈S et (∀w)(w∈S⇒(m,w)∈M')
    R_a = et(appartient(var(aa), vS),
             pourtout(ww, impl(appartient(var(ww), vS), _dans(var(aa), var(ww), Mp))))
    ex_a = N.modus_ponens(least_m, N.s5(R_a, vm, aa))   # (∃a)(…)
    after_m = N.modus_ponens(ex_m, existe_elimination(N.loi_deduction(R_m, ex_a), m))  # (∃a)(…)  [s₀∈Inter]
    cas_inter = N.modus_ponens(ex_s0, existe_elimination(
        N.loi_deduction(appartient(vs0, Inter), after_m), s0))  # (∃a)(…)  [Inter≠∅]
    cas_NE = N.loi_deduction(non(egal(Inter, E.VIDE)), cas_inter)
    # ── cas S∩champ M = ∅ : x₀∈S est le plus petit ─────────────────────────────
    HinterE = N.assume(egal(Inter, E.VIDE))              # S∩champ M = ∅
    ex_z = N.modus_ponens(Snv, equivalence_avant(non_vide_ssi_element(vS)))  # (∃z)(z∈S)
    vz = var("ze")
    ex_z = _alpha_ex(ex_z, "z", "ze", appartient(var("z"), vS))
    Hz = N.assume(appartient(vz, vS))                   # z∈S
    z_champMp = N.modus_ponens(Hz, instancie(Ssub, vz)) # z∈champ M'
    z_disj = _champ_ext_disj(vX, vM, vx0, vz, z_champMp)  # z∈champ M ou z=x₀
    # z∈champ M ⇒ z∈S∩champ M ⇒ Inter≠∅, contredit Inter=∅
    Hz_champM = N.assume(appartient(vz, AM))
    z_inter = _inter_intro(vS, AM, vz, Hz, Hz_champM)   # z∈S∩champ M
    inter_ne = N.modus_ponens(N.modus_ponens(z_inter, N.s5(appartient(var("z"), Inter), vz, "z")),
                              equivalence_arriere(non_vide_ssi_element(Inter)))  # ¬(Inter=∅)
    falso_zc = _ex_falso(HinterE, inter_ne, but_ex)     # (∃a)(…) ex falso
    bz1 = N.loi_deduction(appartient(vz, AM), falso_zc)
    # z=x₀ ⇒ x₀∈S ⇒ x₀ plus petit
    Hz_x0 = N.assume(egal(vz, vx0))
    x0_S = _leib_transport(vz, vx0, Hz_x0, lambda w: appartient(w, vS), Hz)  # x₀∈S
    # (∀s)(s∈S⇒(x₀,s)∈M') : s∈champ M' ⇒ s∈champ M (impossible, Inter=∅) ou s=x₀ ⇒ (x₀,x₀) top
    vs2 = var("se")
    Hs2 = N.assume(appartient(vs2, vS))
    s2_champMp = N.modus_ponens(Hs2, instancie(Ssub, vs2))
    s2_disj = _champ_ext_disj(vX, vM, vx0, vs2, s2_champMp)  # s∈champ M ou s=x₀
    #   s∈champ M ⇒ s∈S∩champ M ⇒ Inter≠∅ contredit Inter=∅
    Hs2_cM = N.assume(appartient(vs2, AM))
    s2_inter = _inter_intro(vS, AM, vs2, Hs2, Hs2_cM)
    inter_ne2 = N.modus_ponens(N.modus_ponens(s2_inter, N.s5(appartient(var("z"), Inter), vs2, "z")),
                               equivalence_arriere(non_vide_ssi_element(Inter)))
    x0s_1 = N.loi_deduction(appartient(vs2, AM), _ex_falso(HinterE, inter_ne2, _dans(vx0, vs2, Mp)))
    #   s=x₀ ⇒ (x₀,x₀) top ⇒ (x₀,s)∈M'
    Hs2_x0 = N.assume(egal(vs2, vx0))
    x0x0 = _ext_intro_top(vX, vM, vx0, vx0, _ou_droite(N.reflexivite(vx0), appartient(vx0, AM)))  # (x₀,x₀)∈M'
    x0_eq_s2 = N.modus_ponens(Hs2_x0, _sym(vs2, vx0))
    x0s_2 = N.loi_deduction(egal(vs2, vx0), _leib_transport(vx0, vs2, x0_eq_s2,
        lambda w: _dans(vx0, w, Mp), x0x0))             # (x₀,s)∈M'
    x0s = cas(s2_disj, x0s_1, x0s_2)                    # (x₀,s)∈M'
    all_s2 = N.generalisation("se", N.loi_deduction(appartient(vs2, vS), x0s))
    if "se" != ww:
        _, inner2 = __import__("bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2",
                               fromlist=["_peler_pourtout"])._peler_pourtout(all_s2.conclusion)
        all_s2 = N.modus_ponens(all_s2, equivalence_avant(alpha_pour_tout("se", ww, inner2)))
    least_x0 = conjonction_intro(x0_S, all_s2)          # x₀∈S et (∀w)(w∈S⇒(x₀,w)∈M')
    ex_a_x0 = N.modus_ponens(least_x0, N.s5(R_a, vx0, aa))  # (∃a)(…)
    bz2 = N.loi_deduction(egal(vz, vx0), ex_a_x0)
    res_z = cas(z_disj, bz1, bz2)                       # (∃a)(…)  [z∈S, Inter=∅]
    cas_E0 = N.modus_ponens(ex_z, existe_elimination(
        N.loi_deduction(appartient(vz, vS), res_z), "ze"))  # (∃a)(…)  [Inter=∅]
    cas_E = N.loi_deduction(egal(Inter, E.VIDE), cas_E0)
    res = cas(tiers_exclu(egal(Inter, E.VIDE)), cas_E, cas_NE)  # (∃a)(…)
    body = N.loi_deduction(hypS, res)
    return N.generalisation(S, body)


def _Ext_bien_ordonne(X, M, x0, GW, Hx0nd):
    """{ M∈W [GW], x₀∉champ M [Hx0nd] } ⊢ est_bien_ordonne(R_M', champ M')."""
    rod = _Ext_rel_ordre_dans(X, M, x0, GW, Hx0nd)        # est_relation_ordre_dans(R_M',champ M')
    corps = _Ext_bien_ordonne_corps(X, M, x0, GW, Hx0nd, S="S", aa="a", ww="w")
    return conjonction_intro(rod, corps)


def Ext_dans_W(X="X", M="M", x0="x0"):
    """⊢ { x₀∈X, x₀∉champ M, M∈W } ⊢ M' ∈ W.

    🎯 LE BON-ORDRE DU GRAPHE ÉTENDU : M' (x₀ au sommet) est un bon ordre partiel de
    X.  M'⊂X×X (Ext_inclus_produit) ; R_M' bien ordonne champ M' (_Ext_bien_ordonne :
    M bien ordonne champ M, x₀ strictement au-dessus de tout).  Axiome de W conclut."""
    vX, vM, vx0 = var(X), var(M), var(x0)
    Mp = Ext(vX, vM, vx0)
    Hx0X = N.assume(appartient(vx0, vX))                  # x₀∈X
    Hx0nd = N.assume(non(appartient(vx0, champ(vM))))     # x₀∉champ M
    GW = N.assume(appartient(vM, W(vX)))                  # M∈W
    # M'⊂X×X  (besoin M⊂X×X = depuis M∈W)
    bop_M = _bo_de_W(vX, vM, GW)
    M_XX = conjonction_elim_gauche(bop_M)                # M⊂X×X
    M_XX_sub = _cut(Ext_inclus_produit(vX, vM, vx0,
                        N.assume(inclus(vM, E.produit(vX, vX))), N.assume(appartient(vx0, vX))),
                    inclus(vM, E.produit(vX, vX)), M_XX)
    M_XX_sub = _cut(M_XX_sub, appartient(vx0, vX), Hx0X)  # M'⊂X×X  [M∈W, x₀∈X]
    # est_bien_ordonne(R_M', champ M')
    bo = _Ext_bien_ordonne(vX, vM, vx0, GW, Hx0nd)       # [M∈W, x₀∉champ M]
    bop_Mp = conjonction_intro(M_XX_sub, bo)             # bon_ordre_partiel(M',X)
    return N.modus_ponens(bop_Mp, equivalence_arriere(_inst_W(vX, Mp)))  # M'∈W


# ════════════════════════════════════════════════════════════════════════════
#  ÉTAPE 5 — 🎯 LE THÉORÈME DE ZERMELO  (E.III.2 — « tout ensemble peut être bien
#  ordonné »).  Le bon ordre est le M MAXIMAL (Zorn), dont le champ est X tout entier.
# ════════════════════════════════════════════════════════════════════════════
def est_bien_ordonne_graphe(G, e, x="x", y="y", z="z", X="X", a="a", w="w"):
    """est_bien_ordonne(R_G, e)  pour un GRAPHE G  (R_G{a,b} := (a,b)∈G).

    Forme « graphe » de est_bien_ordonne : la relation est l'appartenance au graphe
    G.  C'est le prédicat dont zermelo affirme l'existence d'un témoin sur X."""
    return E.est_bien_ordonne(R_de(_terme(G)), _terme(e), x, y, z, X, a, w)


def zermelo(X="X", M="M", R="R"):
    """⊢ (∃R) est_bien_ordonne(R_R, X).

    🎯🎯🎯 THÉORÈME DE ZERMELO (Théorème 1 §III.2, E.III.2) — « TOUT ENSEMBLE PEUT
    ÊTRE BIEN ORDONNÉ » — PROUVÉ via ZORN, INCONDITIONNEL (theorie_ensembles()=22).

    Schéma : par ZORN sur le poset (W, Θ) des BONS ORDRES PARTIELS de X ordonnés par
    END-EXTENSION (est_inductif via la RÉUNION d'une chaîne = bon ordre partiel —
    elle BIEN ORDONNE par end-extension —, W≠∅), il existe un bon ordre partiel
    MAXIMAL M (maximal_existe).  Le champ de M est X TOUT ENTIER (maximal_champ_eq_X,
    par l'absurde : sinon on étendrait M en mettant un point manquant au sommet).
    Donc R_M bien ordonne champ M = X : (∃R) est_bien_ordonne(R, X).  Le bon ordre
    est CONSTRUIT (le maximal vient de Zorn), JAMAIS postulé.  🚫"""
    vX, vM = var(X), var(M)
    Theta_set, W_set = Theta(vX), W(vX)
    from bourbaki.ordre.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_relation import element_maximal
    # (∃M) element_maximal(Θ,W,M)  via Zorn
    ex_max = maximal_existe(X, M)                        # (∃m)element_maximal(Θ,W,m)
    if M != "m":
        ex_max = _alpha_ex(ex_max, "m", M, element_maximal(Theta_set, W_set, var("m"), "x"))
    # per-témoin M : element_maximal ⇒ (∃R)est_bien_ordonne(R,X)
    Hmax = N.assume(element_maximal(Theta_set, W_set, vM, "x"))   # element_maximal(Θ,W,M)
    M_in_W = conjonction_elim_gauche(Hmax)              # M∈W
    bo_M = _bien_ordonne_de_W(vX, vM, M_in_W)           # est_bien_ordonne(R_M, champ M)
    # champ M = X
    champ_eq = _cut(maximal_champ_eq_X(X, M, "x0"),
                    element_maximal(Theta_set, W_set, vM, "x"), Hmax)  # champ M = X
    # est_bien_ordonne(R_M, X)  par Leibniz (champ M = X) — binders S,a,w (comme
    # bon_ordre_partiel, qui emploie « S » pour la partie).
    bo_M_X = _leib_transport(champ(vM), vX, champ_eq,
        lambda e: est_bien_ordonne_graphe(vM, e, X="S"), bo_M)  # est_bien_ordonne(R_M, X)
    # (∃R) est_bien_ordonne(R_R, X)  via S5 (témoin M)
    Rcorps = est_bien_ordonne_graphe(var(R), vX, X="S")
    ex_R = N.modus_ponens(bo_M_X, N.s5(Rcorps, vM, R))  # (∃R)est_bien_ordonne(R_R,X)
    # éliminer ∃M
    wit = N.loi_deduction(element_maximal(Theta_set, W_set, vM, "x"), ex_R)
    ex_imp = existe_elimination(wit, M)                 # (∃M)maximal ⇒ (∃R)…
    return N.modus_ponens(ex_max, ex_imp)               # (∃R)est_bien_ordonne(R_R,X)


__all__ = [
    # prédicats / définitions
    "champ", "R_de", "bon_ordre_partiel", "seg_initial", "est_bien_ordonne_graphe",
    # poset des bons ordres partiels W et end-extension Θ
    "W", "axiome_W", "theorie_W", "W_membre",
    "Theta", "axiome_Theta", "theorie_Theta", "Theta_membre",
    "Theta_reflexive_sur", "Theta_antisymetrique", "Theta_transitive", "Theta_est_ordre",
    "champ_monotone", "totalite_de_W",
    # ÉTAPE 1 — réunion d'une chaîne = bon ordre partiel ; (Θ,W) inductif
    "Union", "axiome_Union", "theorie_Union", "Union_membre",
    "Union_inclus_produit", "Union_transitif", "Union_antisymetrique",
    "Union_refl_impl", "Union_refl_dans", "Union_relation_ordre_dans",
    "Union_bien_ordonne_corps", "Union_bien_ordonne", "Union_bop", "Union_dans_W",
    "Union_seg_initial", "Union_majorant", "W_inductif",
    # ÉTAPE 2 — W ≠ ∅
    "vide_bon_ordre_partiel", "vide_dans_W", "W_non_vide",
    # ÉTAPE 3 — Zorn ⇒ maximal
    "maximal_existe",
    # ÉTAPE 4 — extension au sommet ; champ(M maximal) = X
    "Ext", "axiome_Ext", "theorie_Ext",
    "Ext_inclus_produit", "Ext_seg_initial", "Ext_dans_W", "maximal_champ_eq_X",
    # ÉTAPE 5 — 🎯 ZERMELO
    "zermelo",
]
