"""§III.5.8 — LA FONCTION FACTORIELLE EXISTE (assemblage C62 instancié à T_fac).

Depuis le fix subst (24 juil 2026), le chemin C62 CONSTRUIT sur la règle factorielle
INDEX-AWARE `regle_factorielle()` (O3 levée).  L'assemblage générique des essais en
LA fonction (`ensembles_c62_fonction_*` : 𝔇_tot, f=⋃𝔇_tot fonctionnelle CLOS,
dom(f)=ℕ, équation au point, paquet ∃) s'instancie ici à T_fac :

  `factorielle_fonction_existe` ⊢
      { est_bien_ordonne(≤,ℕ), essais_bien_formes(T_fac), rule_codomain(T_fac,V) }
        ⊢ (∃f)( est_fonctionnel(f) ∧ dom(f)=ℕ ∧ (∀n)( n∈ℕ ⇒ f(n) = T_fac(n) ) ).

C'est « il existe une application f de ℕ » de C62 pour la factorielle — le livre
(E III.41) remarque que 0!=1 et (n+1)!=n!(n+1) CARACTÉRISENT n! « comme on le voit
par récurrence sur n » : cette fonction-par-récurrence est désormais un OBJET.

ÉCARTS DE FIDÉLITÉ (état MESURÉ le 26 juil. 2026 — deux des trois sont CLOS) :
  • ✅ équation au niveau VALEUR-RÈGLE : le pont « T lit la RESTRICTION f|[0,n[ » est
    DÉRIVÉ — `factorielle_equation_restriction` ci-dessous (4 hyps, mesuré 12,2 s) ;
  • ✅ équations séparées f(0)=1 / f(n+1)=… : DÉRIVÉES depuis le 25 juil.
    (`ensembles_factorielle_zero.factorielle_zero`, 6 hyps ;
     `ensembles_factorielle_succ.factorielle_succ_fallback`, 9 hyps), et JOINTES
    en la phrase du livre par `ensembles_factorielle_existence_vrai
    .factorielle_caracterisation` (10 hyps) — la jointure a EXIGÉ d'unifier le liant
    `zcard` des deux moitiés (cf. le kwarg ajouté ci-dessous) ;
  • 🚧 Def.2 du livre (n! := ∏_{i<n}(i+1), produit d'une FAMILLE) exige l'arithmétique
    des familles indexées (§3.3) — la présente fonction en est la CARACTÉRISATION.
    SEUL écart encore ouvert de ce fichier.

INVARIANT : theorie_ensembles() = 22.  TROIS hypothèses honnêtes = résidus C62.
"""
from __future__ import annotations

from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_8_factorielle.ensembles_factorielle_existence import regle_factorielle
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_2_recursion_c62.ensembles_c62_fonction_existence import (
    c62_fonction_cible, fonction_recursion_c62,
)


def factorielle_fonction_cible(e="Enat", V="Vfac62", fb="fglb", zn="zfgl"):
    """L'énoncé : (∃f)( est_fonctionnel(f) ∧ dom(f)=ℕ ∧ (∀n∈ℕ)( f(n)=T_fac(n) ) )."""
    return c62_fonction_cible(regle_factorielle(), e, V, fb, zn)


# @livre Ch.III §5.8 Def.2 | E III.41 L.28-29 | PDF p.144  (n! — ici via sa CARACTÉRISATION par récurrence, la fonction C62 assemblée ; la Def.2-produit-de-famille reste un chantier familles)
# @livre Ch.III §5.8 Rem.- | E III.41 L.30-32 | PDF p.144  (« 0!=1 … (n+1)!=n!(n+1) caractérise le terme n!, comme on le voit par récurrence sur n »)
def factorielle_fonction_existe(e="Enat", G="Gle", V="Vfac62"):
    """🎯🎯 { bo(≤,ℕ), essais_bien_formes(T_fac), rule_codomain(T_fac,V) } ⊢
          (∃f)( est_fonctionnel(f) ∧ dom(f)=ℕ ∧ (∀n)( n∈ℕ ⇒ f(n)=T_fac(n) ) ).

    LA FONCTION FACTORIELLE (par récurrence C62) EXISTE.  Tout dérivé, rien postulé,
    theorie == 22 ; les 3 hypothèses sont les résidus honnêtes de C62."""
    T = regle_factorielle()
    res = fonction_recursion_c62(T, e, G, V)
    assert res.conclusion == factorielle_fonction_cible(e, V), \
        "factorielle_fonction_existe : ≠ cible"
    assert len(res.hypotheses) == 3, "factorielle_fonction_existe : hyps ≠ 3"
    return res


# @livre Ch.III §6.2 Crit.C62 | E III.46 L.14-20 | PDF p.149  (f(n)=T{f⁽ⁿ⁾} instancié à la règle factorielle — la forme du LIVRE)
def factorielle_equation_restriction(e="Enat", G="Gle", V="Vfac62", zn="zfgl",
                                     zcard="Zfac62"):
    """🎯🎯 { bo(≤,ℕ), essais_bien_formes(T_fac), rule_codomain(T_fac,V),
             essais_restriction(T_fac,T_fac) } ⊢
          (∀n)( n∈ℕ ⇒ f(n) = T_fac( f|seg(n) ) )      — LA FORME DU LIVRE (E III.46).

    La règle factorielle LIT LA RESTRICTION f⁽ⁿ⁾ = f|[0,n[ : c'est l'équation de
    C62 telle que Bourbaki l'écrit.  La 4ᵉ hypothèse `essais_restriction` est la
    donnée de LECTURE de la règle (l'encodage-point déposé coïncide avec la lecture
    restriction) — honnête, style regle_locale.  theorie == 22.

    `zcard` : liant du `cardinal` interne de T_fac (défaut "Zfac62", byte-identique à
    l'historique).  Il CHANGE LES TROIS hypothèses règle-dépendantes, donc deux appels
    à `zcard` distincts produisent des théorèmes NON recollables ; passer "Z" (liant
    canonique de `cardinal`) pour s'aligner sur le cas successeur."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_2_recursion_c62.ensembles_c62_equation_restriction import (
        equation_restriction_fonction)
    T = regle_factorielle(zcard=zcard)
    res = equation_restriction_fonction(T, T, e, G, V, zn)
    assert len(res.hypotheses) == 4, "factorielle_equation_restriction : hyps ≠ 4"
    return res


__all__ = ["factorielle_fonction_cible", "factorielle_fonction_existe",
           "factorielle_equation_restriction"]
