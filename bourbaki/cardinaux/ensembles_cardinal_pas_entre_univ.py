"""§III.4 — UNIVERSALISATION du LEMME N « pas de cardinal STRICTEMENT entre c et c+1 ».

OBJECTIF (gate #2 de ℕ — report #2 de ensembles_recurrence_C61.N_collectivise_final) :
fournir, sous forme UNIVERSELLE et CLOSE, le sous-lemme

        cardinal_pas_entre(b, c) :   ( b ≤ c+1 )  ⇒  ( b ≤ c  OU  b = c+1 ).

──────────────────────────────────────────────────────────────────────────────
RESSOURCE DE DÉPART — DÉJÀ PROUVÉE, sous une SEULE garde structurelle :

    cardinal_pas_entre_inconditionnel(b, c)
        (bourbaki.cardinaux.ensembles_equipotence_retrait, THÉORÈME CLOS, 0 hyp)
        ⊢  est_cardinal(b)  ⇒  cardinal_pas_entre(b, c).

    La garde est `est_cardinal(b)` SEUL (PAS est_cardinal(c) : le successeur c+1 est
    TOUJOURS un cardinal, card_succ_egale_succ donne Card(c+1)=c+1 sans garde sur c).
    Elle est INDISPENSABLE — et IRRÉDUCTIBLE — à la BRANCHE SURJECTIVE (branche A) :
    si le témoin f : b → c+1 est injectif ET d'image pleine, on obtient Eq(b, c+1),
    donc Card(b) = Card(c+1) = c+1 ; pour conclure « b = c+1 » il faut identifier
    b à Card(b), ce qui EXIGE est_cardinal(b) (cardinal_de_cardinal : Card b = b).

──────────────────────────────────────────────────────────────────────────────
POURQUOI LA GARDE est_cardinal(b) NE PEUT PAS ÊTRE LEVÉE DEPUIS L'ANTÉCÉDENT b≤c+1 :

  inf_egal_card(b, c+1) = (∃F) est_injection_de(F, b, c+1) (E.III.3.2, Implémentation) :
  F est un GRAPHE FONCTIONNEL de DOMAINE b à valeurs dans c+1.  Cela force seulement
  « b = dom F » (un ensemble QUELCONQUE), JAMAIS « b est de la forme Card(X) ».
  Il N'EXISTE donc PAS (et il ne peut exister) de lemme `inf_egal_card(b,_) ⇒
  est_cardinal(b)` : un ensemble NON cardinal peut parfaitement s'injecter dans un
  cardinal.  RECHERCHE EXHAUSTIVE faite (bourbaki/) : les seuls extracteurs
  d'est_cardinal sont `intervalle_implique_cardinal` (x∈[0,a] ⇒ est_cardinal x) et
  `fini_implique_cardinal` (Fini x ⇒ est_cardinal x) — AUCUN depuis ≤.

  CONTRE-EXEMPLE CONCRET au bare universel (∀b)cardinal_pas_entre(b,c) :
  prendre c=0, c+1 = 1 = {∅}, et b = {{∅}} (singleton, NON cardinal car ≠ Card({∅})=1=
  {∅}).  Alors b ≃ 1 donc b ≤ 1 (=c+1) : l'antécédent est VRAI.  Mais b ≤ 0 est FAUX
  (aucune injection d'un singleton dans ∅) ET b = 1 est FAUX (b={{∅}}≠{∅}=1) : la
  disjonction conséquente est FAUSSE.  Donc (∀b)cardinal_pas_entre(b,c) N'EST PAS un
  théorème — l'énoncé n'a de sens (et n'est vrai) que pour b CARDINAL.

  → La garde est_cardinal(b) est un RÉSIDU HONNÊTE, intrinsèque à l'énoncé, NON un
    défaut de preuve.  On la LÈVE dans le CORPS (la transformant en garde explicite
    universellement quantifiée), JAMAIS on ne la POSTULE.

──────────────────────────────────────────────────────────────────────────────
LIVRAISON (CLOSE, 0 hyp, theorie=22) :

    cardinal_pas_entre_univ()
        ⊢ (∀c)(∀b)( est_cardinal(b) ⇒ cardinal_pas_entre(b, c) ).

  Pur réagencement par GÉNÉRALISATION du théorème clos cardinal_pas_entre_inconditionnel
  (sur b, puis sur c).  AUCUN axiome, AUCUNE hypothèse, rien postulé.

  Le bare universel (∀c)(∀b)cardinal_pas_entre(b,c) — consommé tel quel par
  _preuve_step / fini_downward_thm / N_collectivise_final — N'EST PAS dérivable (cf.
  contre-exemple).  Le report #2 de la chaîne ℕ se RÉDUIT donc EXACTEMENT au résidu
  honnête est_cardinal(b) : `cardinal_pas_entre_univ` ferme tout SAUF cette garde.
  (Pour brancher en aval, le pas de récurrence devrait fournir est_cardinal(b) sur le
  b qu'il quantifie — ce que sa rédaction actuelle ne fait pas ; report documenté,
  ensembles_recurrence_C61.py NON modifié comme demandé.)
"""
from __future__ import annotations

from bourbaki.logique.formule import var, impl, pourtout
from bourbaki.logique import noyau_abrege as N
from bourbaki.cardinaux.ensembles_cardinaux import est_cardinal
from bourbaki.cardinaux.ensembles_equipotence_retrait import (
    cardinal_pas_entre_inconditionnel,
)
from bourbaki.entiers.ensembles_recurrence_C61 import cardinal_pas_entre


def cardinal_pas_entre_garde(b="b", c="c"):
    """⊢ est_cardinal(b) ⇒ cardinal_pas_entre(b, c).   (THÉORÈME CLOS, 0 hyp.)

    ALIAS de cardinal_pas_entre_inconditionnel (ensembles_equipotence_retrait), exposé
    ici comme brique de l'universalisation.  Sa conclusion EST, littéralement,
    impl(est_cardinal(b), cardinal_pas_entre(b, c))."""
    t = cardinal_pas_entre_inconditionnel(b, c)
    # Vérification stricte : la conclusion est bien la forme gardée attendue.
    assert t.conclusion == impl(est_cardinal(var(b) if isinstance(b, str) else b),
                                cardinal_pas_entre(var(b) if isinstance(b, str) else b,
                                                   var(c) if isinstance(c, str) else c)), \
        "cardinal_pas_entre_inconditionnel ne conclut pas est_cardinal(b)⇒cardinal_pas_entre(b,c)"
    return t


def cardinal_pas_entre_univ(b="b", c="c"):
    """⊢ (∀c)(∀b)( est_cardinal(b) ⇒ cardinal_pas_entre(b, c) ).   (THÉORÈME CLOS, 0 hyp.)

    UNIVERSALISATION du LEMME N (gate #2 de ℕ).  Pur réagencement par généralisation
    (sur b, puis sur c) du théorème CLOS cardinal_pas_entre_inconditionnel.

    🔒 RÉSIDU HONNÊTE : la garde est_cardinal(b) est INTRINSÈQUE à l'énoncé et NON
    levable depuis l'antécédent b≤c+1 (cf. docstring du module — contre-exemple b={{∅}}).
    Le bare universel (∀c)(∀b)cardinal_pas_entre(b,c) attendu par N_collectivise_final
    N'EST PAS un théorème ; le report #2 se réduit EXACTEMENT à cette garde.

    AUCUN axiome, AUCUNE hypothèse, rien postulé.  theorie=22."""
    nb = b if isinstance(b, str) else b.nom
    nc = c if isinstance(c, str) else c.nom
    base = cardinal_pas_entre_garde(b, c)                # ⊢ est_cardinal(b) ⇒ cardinal_pas_entre(b,c)
    gen_b = N.generalisation(nb, base)                   # ⊢ (∀b)( est_cardinal(b) ⇒ cardinal_pas_entre(b,c) )
    gen_bc = N.generalisation(nc, gen_b)                 # ⊢ (∀c)(∀b)( est_cardinal(b) ⇒ cardinal_pas_entre(b,c) )
    return gen_bc


def cible_cardinal_pas_entre_univ(b="b", c="c"):
    """La FORMULE-cible (∀c)(∀b)( est_cardinal(b) ⇒ cardinal_pas_entre(b, c) )."""
    vb = var(b) if isinstance(b, str) else b
    vc = var(c) if isinstance(c, str) else c
    return pourtout(c if isinstance(c, str) else c.nom,
                    pourtout(b if isinstance(b, str) else b.nom,
                             impl(est_cardinal(vb), cardinal_pas_entre(vb, vc))))


def cible_bare_universel(b="b", c="c"):
    """La FORMULE bare (∀c)(∀b)cardinal_pas_entre(b,c) attendue (telle quelle) par
    ensembles_recurrence_C61._preuve_step / fini_downward_thm / N_collectivise_final.

    ⚠️ NON un théorème (cf. module : contre-exemple b non cardinal équipotent à c+1).
    Fournie pour DOCUMENTER précisément ce que le report #2 demanderait et MONTRER que
    notre théorème gardé en diffère exactement par la garde est_cardinal(b)."""
    vb = var(b) if isinstance(b, str) else b
    vc = var(c) if isinstance(c, str) else c
    return pourtout(c if isinstance(c, str) else c.nom,
                    pourtout(b if isinstance(b, str) else b.nom,
                             cardinal_pas_entre(vb, vc)))


__all__ = [
    "cardinal_pas_entre_garde",
    "cardinal_pas_entre_univ",
    "cible_cardinal_pas_entre_univ",
    "cible_bare_universel",
]
