"""§III.3.5 — PROPOSITION 10 / Corollaire 3 (forme CURRYING) : a^(b·c) = (a^b)^c.

ÉNONCÉ visé (forme cardinale binaire du projet, E.III.3.5 Cor. 3, dont la BIJECTION
CANONIQUE est la Proposition 3 de §II.5.2) :

        ⊢ Card(𝓕(B×C; A)) = Card(𝓕(C; 𝓕(B;A)))                 (= `cible_prop10`)

c.-à-d. a^(b·c) = (a^b)^c (avec a=Card A, b=Card B, c=Card C : 𝓕(B×C;A) a pour
cardinal a^(b·c) car Card(B×C)=b·c ; 𝓕(C;𝓕(B;A)) a pour cardinal (a^b)^c car
Card(𝓕(B;A))=a^b).  Bourbaki §II.5.2 Prop. 3, verbatim ROADMAP ligne 75 :

   « la fonction f ↦ f̃ est une bijection (dite canonique) de 𝓕(B×C;A) sur
     𝓕(C;𝓕(B;A)) »,  f̃ = (y ↦ f_y),  f_y = (x ↦ f(x,y)).

CRUX : la bijection de CURRYING  Λ : 𝓕(B×C;A) → 𝓕(C;𝓕(B;A)),  f ↦ (c ↦ (b ↦ f(b,c))).
C'est un espace de fonctions À DEUX NIVEAUX — la plus dure des Prop. 9/10/12.

Ce module SUIT exactement le modèle de la Proposition 9 (`ensembles_prop9_final`,
modèle W graphe de bijection) et de la Proposition 12 (`ensembles_prop12_*`,
emballage triple) : on ASSEMBLE Λ comme un GRAPHE-TERME W (schéma C54), on ferme
tout ce qui est atteignable sans le pont membership×valeur reporté, et on pose le
DERNIER MILE conditionnel `card_eq_si_bijection_currying`.

═══════════════════════════════════════════════════════════════════════════════
CONSTRUCTION DE Λ (deux niveaux de graphe-terme) :

  Niveau 0 (TRANCHE).   Pour f ∈ 𝓕(B×C;A) et un point c, la tranche
        tranche(f, c) := graphe_terme( B , f((q,c)) , « q » )  = { (b, f(b,c)) | b∈B }
  est le GRAPHE de b ↦ f(b,c).  Emballé en application B→A :
        f_c := ( ( tranche(f,c) , B ) , A )  ∈ 𝓕(B;A).

  Niveau 1 (CURRY).   Le graphe de c ↦ f_c sur C :
        curry(f) := graphe_terme( C , f_c[c:=p] , « p » )  = { (c, f_c) | c∈C }.
  Emballé en application C→𝓕(B;A) :
        Λval(f) := ( ( curry(f) , C ) , 𝓕(B;A) )  ∈ 𝓕(C;𝓕(B;A)).

  Niveau 2 (GRAPHE DE Λ).   Comme pour W de la Prop. 9 (schéma graphe-terme),
        W := graphe_terme( 𝓕(B×C;A) , Λval(f) , « f » )  = { (f, Λval(f)) | f∈𝓕(B×C;A) }.

═══════════════════════════════════════════════════════════════════════════════
ÉTAT (SALVAGE, paliers sûrs livrés au fur et à mesure) :

PALIER M (CLOS) — CARACTÉRISATIONS MEMBERSHIP des 3 espaces (instances d'axiomes) :
  • membership_BCA(t,…)     ⊢ t∈𝓕(B×C;A) ⇔ (∃G)(t=((G,B×C),A) et G∈A^(B×C)) ;
  • membership_BA(t,…)      ⊢ t∈𝓕(B;A)   ⇔ (∃G)(t=((G,B),A)   et G∈A^B) ;
  • membership_C_BA(t,…)    ⊢ t∈𝓕(C;𝓕(B;A)) ⇔ (∃G)(t=((G,C),𝓕(B;A)) et G∈𝓕(B;A)^C) ;
  • exposant_BA(G,…)        ⊢ G∈A^B ⇔ (G⊂B×A et G fonctionnel et dom G=B)  (idem ×).
  Instances directes d'`axiome_applications`/`axiome_exposant` (Déf. 4, S8+A1).

PALIER W (CLOS) — LE GRAPHE W DE Λ ET SES CONJOINTS STRUCTURELS (C54, automatiques) :
  • tranche/slice_appli/curry/lambda_val      : les termes des deux niveaux ;
  • W(A,B,C)                                   : W = graphe_terme(𝓕(B×C;A),Λval,« f ») ;
  • W_fonctionnel  ⊢ est_fonctionnel(W)        [C54] ;
  • W_domaine      ⊢ dom W = 𝓕(B×C;A)          [C54] ;
  • W_valeur       {f∈𝓕(B×C;A)} ⊢ W(f) = Λval(f) [C54].

PALIER INJ½ (CLOS) — INJECTIVITÉ, demi-extraction (le contenu vraiment dérivable) :
  • W_injective_curry_coincident
        {f₁,f₂∈𝓕(B×C;A), W(f₁)=W(f₂)} ⊢ curry(f₁) = curry(f₂).
    Deux fonctions de même image par Λ ont le MÊME graphe curry (graphe de la
    curryfiée), par décomposition de couples (Bourbaki E.II.30, triple emballage).

PALIER FIN (CLOS, CONDITIONNEL) — DERNIER MILE Λ bijection ⟹ égalité-cible :
  • equipotent_si_bijection_currying
        {est_bijection_de(W, 𝓕(B×C;A), 𝓕(C;𝓕(B;A)))} ⊢ Eq(𝓕(B×C;A), 𝓕(C;𝓕(B;A))) ;
  • card_eq_si_bijection_currying
        {bij W} ⊢ Card(𝓕(B×C;A)) = Card(𝓕(C;𝓕(B;A)))   (= cible_prop10).
    Dès que W est une bijection, témoin de Eq (S5) + Proposition 1 (sens direct,
    `_prop1_direct_t`) donnent l'égalité.

CŒUR REPORTÉ (les conjoints DURS de la bijection, verrou membership×valeur À DEUX
NIVEAUX) : voir `bijection_currying_conjoints_durs_REPORTE`.
═══════════════════════════════════════════════════════════════════════════════
"""
from __future__ import annotations

from bourbaki.logique.formule import Terme, var, egal, et, appartient
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.logique.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    instancie)
from bourbaki.logique.tactiques.tactiques_abrege_egalite import (
    symetrie, composer_egalites)
from bourbaki.ensembles.base.ensembles_couples import (
    couple_egal_implique_composantes)
from bourbaki.ensembles.fonctions.ensembles_fonction_terme import (
    graphe_terme_fonctionnel)
from bourbaki.cardinaux.ensembles_cantor import (
    graphe_terme_domaine, graphe_terme_valeur)
from bourbaki.cardinaux.ensembles_cardinaux import (
    cardinal, equipotent, est_bijection_de)
from bourbaki.cardinaux.arithmetique.ensembles_arith_cardinale import _prop1_direct_t


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# ═══════════════════════════════════════════════════════════════════════════════
# LIANTS (exotiques, choisis pour éviter TOUTE capture le long des deux niveaux) :
#   • « f »  : point courant du graphe W (niveau 2)  — libre de collision ;
#   • « p »  : point courant du graphe curry (niveau 1, la variable « c » de la
#              curryfiée)  — ≠ {x,y} internes graphe-terme, ≠ {u,v,z,w} ;
#   • « q »  : point courant du graphe tranche (niveau 0, la variable « b »)  — idem ;
#   • « m »  : liant du τ de la valeur f((q,p))  — exotique, ≠ {x,y,u,v,z,w}.
# (mêmes choix d'évitement que ensembles_prop9_exp_somme `_VAL_BINDER`/`_GRAPHE_VAR`
#  et ensembles_prop9_final `_POINT`.)
# ═══════════════════════════════════════════════════════════════════════════════
_POINT = "f"          # point courant du graphe W (niveau 2)
_PT_C = "p"           # point courant du graphe curry (la variable « c »)
_PT_B = "q"           # point courant du graphe tranche (la variable « b »)
_VAL = "m"            # liant du τ de la valeur f((q,p))


# ═══════════════════════════════════════════════════════════════════════════════
# Les ESPACES (domaine, codomaine, espace intermédiaire 𝓕(B;A))
# ═══════════════════════════════════════════════════════════════════════════════
def espace_BA(a="A", b="B"):
    """𝓕(B; A)   (l'espace intermédiaire — but de chaque tranche f_c)."""
    va, vb = _t(a), _t(b)
    return E.applications(vb, va)


def domaine_lambda(a="A", b="B", c="C"):
    """𝓕(B×C; A)   (domaine de Λ, source de la bijection)."""
    va, vb, vc = _t(a), _t(b), _t(c)
    return E.applications(E.produit(vb, vc), va)


def codomaine_lambda(a="A", b="B", c="C"):
    """𝓕(C; 𝓕(B;A))   (codomaine de Λ, but de la bijection)."""
    va, vb, vc = _t(a), _t(b), _t(c)
    return E.applications(vc, espace_BA(va, vb))


def cible_prop10(a="A", b="B", c="C"):
    """L'ÉNONCÉ visé (Proposition 10 / Cor. 3, forme currying, E.III.3.5) :
        Card(𝓕(B×C; A)) = Card(𝓕(C; 𝓕(B;A)))  =  a^(b·c) = (a^b)^c.

    Renvoie la FORMULE (non un théorème) — fixe la signature de la cible."""
    va, vb, vc = _t(a), _t(b), _t(c)
    gauche = cardinal(domaine_lambda(va, vb, vc))         # Card(𝓕(B×C;A))  = a^(b·c)
    droite = cardinal(codomaine_lambda(va, vb, vc))       # Card(𝓕(C;𝓕(B;A))) = (a^b)^c
    return egal(gauche, droite)


# ═══════════════════════════════════════════════════════════════════════════════
# PALIER M — CARACTÉRISATIONS MEMBERSHIP des trois espaces (instances d'axiomes)
# ═══════════════════════════════════════════════════════════════════════════════
def membership_BCA(t="t", a="A", b="B", c="C"):
    """⊢ (t ∈ 𝓕(B×C; A)) ⇔ (∃G)(t = ((G, B×C), A) et G ∈ A^(B×C)).

    Caractérisation d'appartenance au DOMAINE de Λ (les applications f:B×C→A) :
    instance directe d'`axiome_applications` en (E:=B×C, F:=A), évaluée en t."""
    va, vb, vc = _t(a), _t(b), _t(c)
    vt = _t(t)
    BC = E.produit(vb, vc)
    ax = N.axiome(E.theorie_applications(BC, va), E.axiome_applications(BC, va))
    return instancie(ax, vt)


def membership_BA(t="t", a="A", b="B"):
    """⊢ (t ∈ 𝓕(B; A)) ⇔ (∃G)(t = ((G, B), A) et G ∈ A^B).

    Caractérisation d'appartenance à l'ESPACE INTERMÉDIAIRE 𝓕(B;A) (les tranches
    f_c : B→A) : instance d'`axiome_applications` en (E:=B, F:=A)."""
    va, vb = _t(a), _t(b)
    vt = _t(t)
    ax = N.axiome(E.theorie_applications(vb, va), E.axiome_applications(vb, va))
    return instancie(ax, vt)


def membership_C_BA(t="t", a="A", b="B", c="C"):
    """⊢ (t ∈ 𝓕(C; 𝓕(B;A))) ⇔ (∃G)(t = ((G, C), 𝓕(B;A)) et G ∈ 𝓕(B;A)^C).

    Caractérisation d'appartenance au CODOMAINE de Λ (les curryfiées f̃ : C→𝓕(B;A)) :
    instance d'`axiome_applications` en (E:=C, F:=𝓕(B;A))."""
    va, vb, vc = _t(a), _t(b), _t(c)
    vt = _t(t)
    FBA = espace_BA(va, vb)
    ax = N.axiome(E.theorie_applications(vc, FBA), E.axiome_applications(vc, FBA))
    return instancie(ax, vt)


def exposant_BA(g="G", a="A", b="B"):
    """⊢ (G ∈ A^B) ⇔ (G ⊂ B×A et G fonctionnel et dom G = B).

    Caractérisation du SUPPORT de graphes A^B (les graphes fonctionnels B→A) :
    instance directe d'`axiome_exposant` en (E:=B, F:=A), évaluée en G."""
    va, vb = _t(a), _t(b)
    vg = _t(g)
    ax = N.axiome(E.theorie_exposant(vb, va), E.axiome_exposant(vb, va))
    return instancie(ax, vg)


# ═══════════════════════════════════════════════════════════════════════════════
# PALIER W — Λ(f) (les DEUX niveaux), le graphe W de Λ, conjoints STRUCTURELS (C54)
# ═══════════════════════════════════════════════════════════════════════════════
def _val_fbc(f, b_pt, c_pt):
    """f((b_pt, c_pt))  =  valeur(f, (b_pt, c_pt))  — la valeur de f sur le couple.

    Liant du τ « m » (exotique).  b_pt, c_pt : termes (typiquement var(« q »), var(« p »))."""
    return E.valeur(_t(f), E.couple(_t(b_pt), _t(c_pt)), _VAL)


def tranche(f, c_pt, a="A", b="B"):
    """tranche(f, c) := graphe_terme( B , f((q, c)) , « q » )  = { (b, f(b,c)) | b∈B }.

    Le GRAPHE de la fonction b ↦ f(b,c) sur B (la « tranche » de f à c fixé).
    Point courant « q » (la variable b) ; valeur f((q,c)) avec τ-liant « m »."""
    va, vb = _t(a), _t(b)
    return E.graphe_terme(vb, _val_fbc(f, var(_PT_B), c_pt), _PT_B)


def slice_appli(f, c_pt, a="A", b="B"):
    """f_c := ( ( tranche(f,c) , B ) , A )   (la tranche EMBALLÉE en application B→A).

    Le triple (graphe, source, but) = ((tranche(f,c), B), A) ∈ 𝓕(B;A) — c'est
    la valeur de la curryfiée f̃ en c."""
    va, vb = _t(a), _t(b)
    return E.couple(E.couple(tranche(f, c_pt, va, vb), vb), va)


def curry(f, a="A", b="B", c="C"):
    """curry(f) := graphe_terme( C , f_p , « p » )  = { (c, f_c) | c∈C }.   (terme)

    Le GRAPHE de la curryfiée c ↦ f_c sur C.  Point courant « p » (la variable c) ;
    valeur = slice_appli(f, p) = ((tranche(f,p), B), A)."""
    va, vb, vc = _t(a), _t(b), _t(c)
    return E.graphe_terme(vc, slice_appli(f, var(_PT_C), va, vb), _PT_C)


def lambda_val(f, a="A", b="B", c="C"):
    """Λval(f) := ( ( curry(f) , C ) , 𝓕(B;A) )   (l'image de f par Λ, EMBALLÉE).

    La curryfiée f̃ = (c ↦ f_c) emballée en application C→𝓕(B;A) : le triple
    ((curry(f), C), 𝓕(B;A)) ∈ 𝓕(C;𝓕(B;A)).  C'est exactement Λ(f) = f̃."""
    va, vb, vc = _t(a), _t(b), _t(c)
    return E.couple(E.couple(curry(f, va, vb, vc), vc), espace_BA(va, vb))


def W(a="A", b="B", c="C"):
    """W := graphe_terme( 𝓕(B×C;A) , Λval(f) , « f » )   (le GRAPHE de Λ, terme).

    Schéma graphe-terme identique à W de la Proposition 9 (`ensembles_prop9_final.W`)
    et au graphe bijectif de la Proposition 12 : le graphe de f ↦ Λval(f) sur tout
    𝓕(B×C;A).  Point courant « f »."""
    va, vb, vc = _t(a), _t(b), _t(c)
    return E.graphe_terme(domaine_lambda(va, vb, vc),
                          lambda_val(var(_POINT), va, vb, vc), _POINT)


# ── CONJOINT 1 — W fonctionnel  (automatique, C54) ────────────────────────────
def W_fonctionnel(a="A", b="B", c="C"):
    """⊢ est_fonctionnel(W).   (Λ associe à chaque f UNE image Λval(f) ; cas C54.)"""
    va, vb, vc = _t(a), _t(b), _t(c)
    return graphe_terme_fonctionnel(domaine_lambda(va, vb, vc),
                                    lambda_val(var(_POINT), va, vb, vc), _POINT, "y")


# ── CONJOINT 2 — dom W = 𝓕(B×C;A)  (automatique, C54) ─────────────────────────
def W_domaine(a="A", b="B", c="C"):
    """⊢ dom(W) = 𝓕(B×C; A).   (Λ est définie sur TOUT l'espace 𝓕(B×C;A).)"""
    va, vb, vc = _t(a), _t(b), _t(c)
    return graphe_terme_domaine(domaine_lambda(va, vb, vc),
                                lambda_val(var(_POINT), va, vb, vc), _POINT, "y", "z")


def W_valeur(f="g", a="A", b="B", c="C"):
    """{f ∈ 𝓕(B×C; A)} ⊢ W(f) = Λval(f).   (la valeur de Λ en f.)

    ⚠ le point d'évaluation f doit être un NOM (string) ≠ liant « f » de W et ≠
    liants internes {x,y} de la machinerie graphe-terme (sinon capture).  Le DÉFAUT
    est « g » (≠ f, x, y, et ≠ p,q,m des deux niveaux de curry)."""
    if not isinstance(f, str):
        raise ValueError("W_valeur : le point d'évaluation doit être un NOM (string)")
    va, vb, vc = _t(a), _t(b), _t(c)
    return graphe_terme_valeur(domaine_lambda(va, vb, vc),
                               lambda_val(var(_POINT), va, vb, vc), f, _POINT, "y")


# ═══════════════════════════════════════════════════════════════════════════════
# PALIER INJ½ — injectivité de Λ, demi-extraction : MÊME graphe curry.
# ═══════════════════════════════════════════════════════════════════════════════
def W_injective_curry_coincident(a="A", b="B", c="C", f1="f1", f2="f2"):
    """{f₁∈𝓕(B×C;A), f₂∈𝓕(B×C;A), W(f₁)=W(f₂)}  ⊢  curry(f₁) = curry(f₂).

    CŒUR DE L'INJECTIVITÉ de Λ.  W(fᵢ)=Λval(fᵢ)=((curry(fᵢ),C),𝓕(B;A)) (W_valeur) ;
    de W(f₁)=W(f₂) on tire Λval(f₁)=Λval(f₂), puis par décomposition de couples
    (couple_egal_implique_composantes, E.II.30, appliquée deux fois : couple
    externe ((·,C),𝓕(B;A)) puis paire interne (·,C)) on extrait curry(f₁)=curry(f₂)
    — les deux graphes de curryfiées COÏNCIDENT.

    (Le dernier pas f₁=f₂ exige l'extensionnalité fonctionnelle À DEUX NIVEAUX :
    de curry(f₁)=curry(f₂) reconstruire f₁=f₂ sur tout B×C ; bloqué sur le pont
    reporté — cf. `bijection_currying_conjoints_durs_REPORTE`.)"""
    if not (isinstance(f1, str) and isinstance(f2, str)):
        raise ValueError("W_injective… : f1, f2 doivent être des NOMS (strings)")
    va, vb, vc = _t(a), _t(b), _t(c)
    vf1, vf2 = var(f1), var(f2)
    Wt = W(va, vb, vc)
    dom = domaine_lambda(va, vb, vc)
    FBA = espace_BA(va, vb)
    L1, L2 = lambda_val(vf1, va, vb, vc), lambda_val(vf2, va, vb, vc)

    # W(f₁)=Λval(f₁) et W(f₂)=Λval(f₂)   (W_valeur déchargée par fᵢ∈dom)
    Wf1 = N.modus_ponens(N.assume(appartient(vf1, dom)),
                         N.loi_deduction(appartient(vf1, dom), W_valeur(f1, va, vb, vc)))
    Wf2 = N.modus_ponens(N.assume(appartient(vf2, dom)),
                         N.loi_deduction(appartient(vf2, dom), W_valeur(f2, va, vb, vc)))
    # Λval(f₁) = W(f₁) = W(f₂) = Λval(f₂)
    heq = N.assume(egal(E.valeur(Wt, vf1), E.valeur(Wt, vf2)))             # W(f₁)=W(f₂)
    L1_eq_L2 = composer_egalites(composer_egalites(
        N.modus_ponens(Wf1, symetrie(E.valeur(Wt, vf1), L1)), heq), Wf2)   # Λval(f₁)=Λval(f₂)

    # décomposition du couple EXTERNE : ((curry₁,C),𝓕(B;A)) = ((curry₂,C),𝓕(B;A))
    #   ⇒ (curry₁,C) = (curry₂,C)  et  𝓕(B;A)=𝓕(B;A)
    inner1 = E.couple(curry(vf1, va, vb, vc), vc)         # (curry(f₁), C)
    inner2 = E.couple(curry(vf2, va, vb, vc), vc)         # (curry(f₂), C)
    comp_ext = N.modus_ponens(L1_eq_L2,
                              couple_egal_implique_composantes(inner1, FBA, inner2, FBA))
    inner_eq = conjonction_elim_gauche(comp_ext)          # (curry(f₁),C)=(curry(f₂),C)
    # décomposition de la PAIRE interne : (curry₁,C)=(curry₂,C) ⇒ curry₁=curry₂
    comp_in = N.modus_ponens(inner_eq,
                             couple_egal_implique_composantes(
                                 curry(vf1, va, vb, vc), vc,
                                 curry(vf2, va, vb, vc), vc))
    return conjonction_elim_gauche(comp_in)               # curry(f₁) = curry(f₂)


# ═══════════════════════════════════════════════════════════════════════════════
# PALIER FIN — Λ bijection ⟹ égalité-cible (le DERNIER MILE, CONDITIONNEL)
# ═══════════════════════════════════════════════════════════════════════════════
def equipotent_si_bijection_currying(a="A", b="B", c="C"):
    """{est_bijection_de(W, 𝓕(B×C;A), 𝓕(C;𝓕(B;A)))} ⊢ Eq(𝓕(B×C;A), 𝓕(C;𝓕(B;A))).

    Dès que W (le graphe de Λ) est une bijection 𝓕(B×C;A) → 𝓕(C;𝓕(B;A)),
    l'équipotence Eq(·,·) = (∃F)(bijection_de(F,·,·)) est attestée par le témoin
    F := W (S5)."""
    va, vb, vc = _t(a), _t(b), _t(c)
    Wt = W(va, vb, vc)
    dom = domaine_lambda(va, vb, vc)
    cod = codomaine_lambda(va, vb, vc)
    bij = N.assume(est_bijection_de(Wt, dom, cod))
    corps = est_bijection_de(var("F"), dom, cod)          # corps de Eq avec liant F
    return N.modus_ponens(bij, N.s5(corps, Wt, "F"))      # (∃F)bijection_de(F,dom,cod) = Eq


def card_eq_si_bijection_currying(a="A", b="B", c="C"):
    """{est_bijection_de(W, 𝓕(B×C;A), 𝓕(C;𝓕(B;A)))}
        ⊢ Card(𝓕(B×C; A)) = Card(𝓕(C; 𝓕(B;A))).        (= cible_prop10.)

    LE DERNIER MILE de la Proposition 10 (currying), CONDITIONNEL à la bijectivité
    de W.  Eq(𝓕(B×C;A), 𝓕(C;𝓕(B;A))) (equipotent_si_bijection_currying) ⇒ égalité
    des cardinaux (Proposition 1, sens direct, `_prop1_direct_t`).  La conclusion
    est LITTÉRALEMENT `cible_prop10(A,B,C)` (a^(b·c) = (a^b)^c).

    Il ne reste, pour CLORE inconditionnellement la Proposition 10, qu'à fournir
    est_bijection_de(W,…) — c.-à-d. les conjoints DURS reportés
    (`bijection_currying_conjoints_durs_REPORTE`)."""
    va, vb, vc = _t(a), _t(b), _t(c)
    dom = domaine_lambda(va, vb, vc)
    cod = codomaine_lambda(va, vb, vc)
    eq = equipotent_si_bijection_currying(va, vb, vc)     # {bij W} ⊢ Eq(dom, cod)
    prop1 = _prop1_direct_t(dom, cod)                     # Eq(dom,cod) ⇒ Card dom = Card cod
    return N.modus_ponens(eq, prop1)                      # {bij W} ⊢ Card(dom)=Card(cod)


# ═══════════════════════════════════════════════════════════════════════════════
# CŒUR REPORTÉ — les conjoints DURS de est_bijection_de(W, …)  (verrou à 2 niveaux)
# ═══════════════════════════════════════════════════════════════════════════════
def bijection_currying_conjoints_durs_REPORTE():
    """REPORTÉ (non clos) — les conjoints DURS de est_bijection_de(W, …).

    Ce module ferme : les 4 CARACTÉRISATIONS membership (membership_BCA / membership_BA
    / membership_C_BA / exposant_BA), le GRAPHE W de Λ (deux niveaux de curry) + ses
    conjoints structurels (W fonctionnel, dom W = 𝓕(B×C;A), W(f)=Λval(f)), la
    demi-injectivité (même graphe curry), et le DERNIER MILE conditionnel (W bijection
    ⟹ égalité-cible, card_eq_si_bijection_currying).

    Restent REPORTÉS (verrou membership×valeur À DEUX NIVEAUX — le pont le long du
    produit B×C, structurellement identique à R24/R25/R26 mais redoublé par
    l'imbrication 𝓕(C;𝓕(B;A))) :
      (i)   BIEN-DÉFINITION  Λval(f) ∈ 𝓕(C;𝓕(B;A))  pour f∈𝓕(B×C;A) : il faut, pour
            chaque c∈C, que f_c = ((tranche(f,c),B),A) ∈ 𝓕(B;A), c.-à-d. tranche(f,c)
            ∈ A^B — donc la valeur f((b,c))∈A pour (b,c)∈B×C (transport de
            « f∈𝓕(B×C;A) ⇒ f((b,c))∈A car (b,c)∈B×C » à la tranche) — PUIS que
            curry(f) ∈ 𝓕(B;A)^C (le NIVEAU SUPÉRIEUR : c↦f_c à valeurs dans 𝓕(B;A)) ;
            DOUBLE membership le long de B×C puis de C ;
      (ii)  INJECTIVITÉ COMPLÈTE : de curry(f₁)=curry(f₂) (W_injective_curry_coincident,
            CLOS) à f₁=f₂, par EXTENSIONNALITÉ fonctionnelle À DEUX NIVEAUX :
            curry égaux ⇒ tranche(f₁,c)=tranche(f₂,c) ∀c (extensionnalité de curry sur C)
            ⇒ f₁((b,c))=f₂((b,c)) ∀(b,c) (extensionnalité des tranches sur B)
            ⇒ f₁=f₂ (extensionnalité sur B×C, graphe_egal_par_valeurs) ;
      (iii) SURJECTIVITÉ  image(W,𝓕(B×C;A)) ⊃ 𝓕(C;𝓕(B;A)) : depuis g∈𝓕(C;𝓕(B;A))
            arbitraire, l'UNCURRY  f(b,c) := g(c)(b)  vérifie Λval(f)=g — même verrou
            d'extensionnalité fonctionnelle à deux niveaux, en sens inverse.

    Les trois conjoints durs sont bloqués sur le MÊME pont membership×valeur, ici
    REDOUBLÉ par l'imbrication (un espace de fonctions de fonctions).  Une fois
    fermés, est_bijection_de(W,…) alimente `card_eq_si_bijection_currying` et CLÔT
    inconditionnellement la Proposition 10."""
    raise NotImplementedError(
        "Conjoints DURS de est_bijection_de(W,…) reportés (currying à deux niveaux) : "
        "bien-définition Λval(f)∈𝓕(C;𝓕(B;A)) (i, double membership B×C puis C), "
        "injectivité complète f₁=f₂ depuis curry égaux (ii, extensionnalité fonctionnelle "
        "à deux niveaux), surjectivité via uncurry g(c)(b) (iii) — tous bloqués sur le "
        "pont membership×valeur le long du produit B×C, redoublé par l'imbrication "
        "𝓕(C;𝓕(B;A)).  Ce module livre les caractérisations membership des 3 espaces, "
        "le graphe W de Λ (W fonctionnel + dom W = 𝓕(B×C;A) + W(f)=Λval(f)), la "
        "demi-injectivité (même graphe curry) et le dernier mile conditionnel "
        "card_eq_si_bijection_currying.")


__all__ = [
    "espace_BA", "domaine_lambda", "codomaine_lambda", "cible_prop10",
    "membership_BCA", "membership_BA", "membership_C_BA", "exposant_BA",
    "tranche", "slice_appli", "curry", "lambda_val", "W",
    "W_fonctionnel", "W_domaine", "W_valeur",
    "W_injective_curry_coincident",
    "equipotent_si_bijection_currying", "card_eq_si_bijection_currying",
    "bijection_currying_conjoints_durs_REPORTE",
]
