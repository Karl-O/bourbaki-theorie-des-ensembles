"""§III.5.2 — LA SOUSTRACTION DES ENTIERS (Cor. 4 de la Prop. 3, E.III.37).

🎯 CARACTÉRISE la différence des entiers, jusqu'ici un terme OPAQUE inexploitable
(`difference_entiers(b,a) = app("diff_ent", b, a)` dans ensembles_entiers, SANS
axiome).  Bourbaki E.III.37, Cor. 4 (LU au PDF source) :

    « Si a et b sont des entiers tels que a ≤ b, il existe un entier c et un seul tel
      que b = a + c.  L'existence de c résulte de la prop. 13 de III, p. 29, et son
      unicité du cor. 3 ci-dessus.  L'entier c tel que b = a + c (pour a ≤ b)
      s'appelle la *différence* des entiers b et a, et se note b − a. »

On caractérise ici la VRAIE différence  b − a := μc.(b = a + c)  (le τ canonique
`tau("c", b = somme_cardinale_binaire(a, c))`), et non le terme opaque historique
`app("diff_ent",…)` (qui, n'étant pas un τ, n'a aucune propriété dérivable — on le
laisse INTACT dans ensembles_entiers, deposited, et on travaille avec le τ canonique).

────────────────────────────────────────────────────────────────────────────────
RÉSULTATS :

  • EXISTENCE (Prop. 13 §III.3, restreinte aux cardinaux) — CLOSE :
        existe_complement_somme(a, b) :
            ⊢ ( est_cardinal(a) et est_cardinal(b) et a ≤ b ) ⇒ (∃c) b = a + c.
    Pur ré-emploi de prop13_forward_ferme(b:=a, a:=b) (qui démontre
    « b≤a ⇒ (∃c)a=b+c » avec ses propres noms ; on l'instancie avec a/b échangés).

  • CARACTÉRISATION  a + (b−a) = b  (le cœur : (b−a) est un VRAI complément) — CLOSE :
        soustraction_caracterisation(a, b) :
            ⊢ ( est_cardinal(a) et est_cardinal(b) et a ≤ b ) ⇒ ( a + (b−a) = b ).
    Via le τ-axiome `existe_temoin` :  (∃c)(b = a+c) ⇒ (b = a + τc(b=a+c)) ;
    τc(b=a+c) EST `diff_somme(b,a)` ; symétrie ⇒ a + (b−a) = b.

  • UNICITÉ — close SOUS hypothèse honnête de simplifiabilité additive :
        soustraction_unicite(a, c, cp, b) :
            ⊢ ( a+c = b et a+cp = b et (a+c=a+cp ⇒ c=cp) ) ⇒ ( c = cp ).
    La simplifiabilité additive a+c=a+c'⇒c=c' est VRAIE pour a fini (Cor. 3 §III.5)
    mais FAUSSE en général (cardinaux infinis) ; sa preuve (récurrence sur a fini) est
    un chantier séparé → on la laisse en hypothèse EXPLICITE, jamais postulée.

⚠️ INVARIANT : theorie_ensembles() = 22.  Rien postulé : existence = Prop 13 close ;
   caractérisation = τ-axiome `existe_temoin` (déf-τ, déjà au noyau) + symétrie.
   Le terme opaque `app("diff_ent",…)` n'est PAS modifié (deposited).
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (
    Terme, var, egal, et, impl, existe, tau,
)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite, instancie,
)
from bourbaki.logique.i_4_egalitaires.tactiques_abrege_egalite import symetrie

from bourbaki.cardinaux.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    est_cardinal, cardinal, inf_egal_card,
)
from bourbaki.ensembles.familles.ii_4_reunion_intersection_familles.ii_4_recollement_somme.ensembles_somme_disjointe import (
    somme_cardinale_binaire,
)
from bourbaki.cardinaux.iii_3_equipotence_cardinaux.props_restantes.ensembles_prop13_complement import (
    prop13_forward_ferme, prop13_forward_ferme_cible,
)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def _est_cardinal_Xa(a):
    """est_cardinal(a) sous la forme binder « Xa » exigée par prop13_forward_ferme."""
    va = _t(a)
    return existe("Xa", egal(va, cardinal(var("Xa"))))


# ══════════════════════════════════════════════════════════════════════════════
#  LE τ CANONIQUE  :  b − a := μ c.( b = a + c )
# ══════════════════════════════════════════════════════════════════════════════
def diff_somme(b, a, c="c"):
    """b − a := τ c.( b = a + c )   (la VRAIE différence, terme caractérisable).

    Contrairement à `difference_entiers` (app opaque), c'est le τ canonique : sous
    existence d'un témoin, le τ-axiome `existe_temoin` donne (b = a + (b−a))."""
    vb, va = _t(b), _t(a)
    return tau(c, egal(vb, somme_cardinale_binaire(va, var(c))))


# ══════════════════════════════════════════════════════════════════════════════
#  EXISTENCE  :  ( card a et card b et a ≤ b ) ⇒ (∃c) b = a + c     (Prop. 13)
# ══════════════════════════════════════════════════════════════════════════════
def existe_complement_somme_enonce(a="a", b="b", c="c"):
    """Formule de l'EXISTENCE :
        ( est_cardinal(a) et est_cardinal(b) et a ≤ b ) ⇒ (∃c) b = a + c."""
    va, vb = _t(a), _t(b)
    return impl(et(et(est_cardinal(va), est_cardinal(vb)), inf_egal_card(va, vb)),
                existe(c, egal(vb, somme_cardinale_binaire(va, var(c)))))


def existe_complement_somme(a="a", b="b", c="c"):
    """⊢ ( est_cardinal(a) et est_cardinal(b) et a ≤ b ) ⇒ (∃c) b = a + c.  (CLOS.)

    Ré-emploi de prop13_forward_ferme(b:=a, a:=b) : ce théorème CLOS démontre
    « (card B et card A et A≤B) ⇒ (∃c)B = A+c » avec SES noms B, A ; en y substituant
    B:=a (notre petit) et A:=b (notre grand), on obtient « (card a et card b et a≤b)
    ⇒ (∃c)b = a+c ».  On réordonne le triplet d'antécédents pour coller à l'énoncé."""
    va, vb = _t(a), _t(b)

    # prop13_forward_ferme(B, A, c) : ((∃Xa)A=Card Xa et card B et B≤A) ⇒ (∃c)A = B+c
    # ⇒ ici B:=a (le PETIT, joue le rôle du « b » bourbakiste), A:=b (le GRAND).
    base = prop13_forward_ferme(va, vb, c)     # ((∃Xa)b=Card Xa et card a et a≤b) ⇒ (∃c)b=a+c
    assert base.est_clos and not base.hypotheses
    assert base.conclusion == prop13_forward_ferme_cible(va, vb, c)

    # antécédent de base : ( (∃Xa)b=Card Xa  et  est_cardinal(a) )  et  a≤b
    ante = et(et(est_cardinal(va), est_cardinal(vb)), inf_egal_card(va, vb))
    h = N.assume(ante)
    h_card_a = conjonction_elim_gauche(conjonction_elim_gauche(h))   # est_cardinal(a)
    h_card_b = conjonction_elim_droite(conjonction_elim_gauche(h))   # est_cardinal(b)
    h_le = conjonction_elim_droite(h)                               # a ≤ b

    # est_cardinal(b) ⇒ sa forme binder « Xa » : est_cardinal(b) EST (∃Xb)b=Card Xb ;
    # prop13_forward_ferme exige le binder littéral « Xa ».  On reconstruit (∃Xa)b=Card Xa
    # depuis est_cardinal(b) par α-équivalence des ∃ liés (renommage du témoin).
    card_b_Xa = _renomme_est_cardinal(h_card_b, vb)                 # (∃Xa) b = Card Xa

    res = N.modus_ponens(conjonction_intro(conjonction_intro(card_b_Xa, h_card_a), h_le),
                         base)                                      # (∃c) b = a+c
    out = N.loi_deduction(ante, res)
    assert out.conclusion == existe_complement_somme_enonce(a, b, c), \
        "existe_complement_somme : conclusion ≠ énoncé attendu"
    return out


def _renomme_est_cardinal(thm_card, va):
    """De ⊢ est_cardinal(V)  [binder « X » par défaut]  produire ⊢ (∃Xa) V = Card Xa.

    est_cardinal(V) = (∃X) V = Card X.  On élimine le témoin X (existe_temoin donne
    V = Card τX(...)), puis S5 le réintroduit sous le binder « Xa »."""
    # est_cardinal(va) = (∃X) va = Card X  ; body avec X
    from bourbaki.cardinaux.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import est_cardinal as _ec
    forme = thm_card.conclusion                    # (∃X) va = Card X
    x_bind = forme.lieur                           # « X »
    body = forme.sous[0]                           # va = Card X   (X libre dedans)
    # témoin : va = Card τX(body)
    tw = N.modus_ponens(thm_card, N.existe_temoin(body, x_bind))   # va = Card τX(body)
    tauX = tau(x_bind, body)
    # S5 : (va = Card τX | Xa) ⇒ (∃Xa) va = Card Xa
    body_Xa = egal(va, cardinal(var("Xa")))
    reintro = N.modus_ponens(tw, N.s5(body_Xa, tauX, "Xa"))        # (∃Xa) va = Card Xa
    return reintro


# ══════════════════════════════════════════════════════════════════════════════
#  🎯 CARACTÉRISATION  :  a + (b − a) = b
# ══════════════════════════════════════════════════════════════════════════════
def soustraction_caracterisation_enonce(a="a", b="b", c="c"):
    """Formule :  ( est_cardinal(a) et est_cardinal(b) et a ≤ b ) ⇒ ( a + (b−a) = b )."""
    va, vb = _t(a), _t(b)
    diff = diff_somme(vb, va, c)
    return impl(et(et(est_cardinal(va), est_cardinal(vb)), inf_egal_card(va, vb)),
                egal(somme_cardinale_binaire(va, diff), vb))


def soustraction_caracterisation(a="a", b="b", c="c"):
    """🎯 ⊢ ( est_cardinal(a) et est_cardinal(b) et a ≤ b ) ⇒ ( a + (b−a) = b ).  (CLOS.)

    Cor. 4 §III.5 (existence du complément).  EXISTENCE (existe_complement_somme) donne
    (∃c) b = a+c ; le τ-axiome `existe_temoin` réalise le témoin canonique τc(b=a+c) =
    diff_somme(b,a) : (∃c)(b=a+c) ⇒ (b = a + (b−a)) ; symétrie ⇒ a + (b−a) = b."""
    va, vb = _t(a), _t(b)
    diff = diff_somme(vb, va, c)                         # τc(b = a+c)
    body = egal(vb, somme_cardinale_binaire(va, var(c)))  # b = a + c

    ante = et(et(est_cardinal(va), est_cardinal(vb)), inf_egal_card(va, vb))
    h = N.assume(ante)

    exists = N.modus_ponens(h, existe_complement_somme(a, b, c))   # (∃c) b = a+c
    # existe_temoin : (∃c) body ⇒ (τc(body)|c)body  =  (b = a + (b−a))
    realise = N.modus_ponens(exists, N.existe_temoin(body, c))     # b = a + (b−a)
    # symétrie : a + (b−a) = b
    sym = N.modus_ponens(realise, symetrie(vb, somme_cardinale_binaire(va, diff)))
    out = N.loi_deduction(ante, sym)
    assert out.conclusion == soustraction_caracterisation_enonce(a, b, c), \
        "soustraction_caracterisation : conclusion ≠ énoncé attendu"
    return out


# ══════════════════════════════════════════════════════════════════════════════
#  UNICITÉ  (sous simplifiabilité additive HONNÊTE)
# ══════════════════════════════════════════════════════════════════════════════
def soustraction_unicite_enonce(a="a", c="c", cp="cp", b="b"):
    """Formule :  ( a+c = b  et  a+cp = b  et  (a+c = a+cp ⇒ c=cp) ) ⇒ ( c = cp )."""
    va, vc, vcp, vb = _t(a), _t(c), _t(cp), _t(b)
    ac = somme_cardinale_binaire(va, vc)
    acp = somme_cardinale_binaire(va, vcp)
    return impl(et(et(egal(ac, vb), egal(acp, vb)), impl(egal(ac, acp), egal(vc, vcp))),
                egal(vc, vcp))


def soustraction_unicite(a="a", c="c", cp="cp", b="b"):
    """⊢ ( a+c=b et a+cp=b et (a+c=a+cp ⇒ c=cp) ) ⇒ ( c = cp ).  (CLOS, hyp honnête.)

    Unicité de la différence (Cor. 3 §III.5).  a+c=b et a+cp=b ⇒ a+c=a+cp (transitivité
    via b) ; la SIMPLIFIABILITÉ additive (a+c=a+cp ⇒ c=cp), VRAIE pour a fini mais
    FAUSSE en général, est laissée en HYPOTHÈSE explicite (sa preuve = récurrence sur a
    fini, chantier séparé)."""
    va, vc, vcp, vb = _t(a), _t(c), _t(cp), _t(b)
    ac = somme_cardinale_binaire(va, vc)
    acp = somme_cardinale_binaire(va, vcp)

    ante = et(et(egal(ac, vb), egal(acp, vb)), impl(egal(ac, acp), egal(vc, vcp)))
    h = N.assume(ante)
    h_ac_b = conjonction_elim_gauche(conjonction_elim_gauche(h))    # a+c = b
    h_acp_b = conjonction_elim_droite(conjonction_elim_gauche(h))   # a+cp = b
    h_simpl = conjonction_elim_droite(h)                           # (a+c=a+cp) ⇒ c=cp

    # a+c = a+cp : a+c=b et a+cp=b ⇒ a+c = b = a+cp (symétrie + transitivité)
    b_eq_acp = N.modus_ponens(h_acp_b, symetrie(acp, vb))          # b = a+cp
    ac_eq_acp = _trans_egal(h_ac_b, b_eq_acp, ac, vb, acp)         # a+c = a+cp
    res = N.modus_ponens(ac_eq_acp, h_simpl)                       # c = cp
    out = N.loi_deduction(ante, res)
    assert out.conclusion == soustraction_unicite_enonce(a, c, cp, b), \
        "soustraction_unicite : conclusion ≠ énoncé attendu"
    return out


def _trans_egal(h_xy, h_yz, x, y, z):
    """De ⊢ X=Y et ⊢ Y=Z produire ⊢ X=Z (Leibniz : réécrire Y↦Z dans X=Y)."""
    from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import equivalence_avant
    equiv = N.modus_ponens(h_yz, N.s6(y, z, "w", egal(x, var("w"))))   # (X=Y) ⇔ (X=Z)
    return N.modus_ponens(h_xy, equivalence_avant(equiv))


__all__ = [
    "diff_somme",
    "existe_complement_somme", "existe_complement_somme_enonce",
    "soustraction_caracterisation", "soustraction_caracterisation_enonce",
    "soustraction_unicite", "soustraction_unicite_enonce",
]
