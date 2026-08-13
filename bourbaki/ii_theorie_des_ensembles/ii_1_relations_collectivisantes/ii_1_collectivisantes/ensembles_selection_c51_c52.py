"""Chap. II §1.6 — Sélection : C51, C52, l'ensemble {x ∈ A | P} (E II.5).

Cette page du livre est presque entièrement MÉTAMATHÉMATIQUE (fin de la
vérification que S8 est un schéma, critères C51-C53) : suivant la convention
du projet, les énoncés et démonstrations sont consignés ici en commentaire,
et le seul contenu exécutable est la FORME des énoncés au niveau assemblages
(via Coll_x, comme dans ensembles_appartenance_coll.py voisin).

STATUT HONNÊTE : C51 et C52 ne sont PAS encore dérivés comme `Theoreme` du
noyau (leurs preuves invoquent C27, S5, S8, C30, C43, C33 — la chaîne est
longue). Le PATRON exécutable qui les remplace partout dans le dépôt est la
« théorie dédiée S8+A1 » (cf. chap. III, ordre_treillis : [a,b] = {x∈E | …}).
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.assemblage import (
    Assemblage, conjonction, existe, pour_tout, equivalence)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.theorie_ensembles import (
    appartient)


# @livre Ch.II §1.6 Demo.- | E II.5 L.1-6 | PDF p.56
#
# FIN de la vérification que la sélection-réunion est bien un SCHÉMA (début
# E II.4) : dans S, substituons un terme T à une lettre z ; d'après CS8
# (E I.32 — implémenté dans i_4_1_quantificateurs.cs8), on peut supposer
# x, y, X, Y distincts de z et ne figurant pas dans T ; alors (T|z)S est
# identique à la relation de même forme construite sur R' = (T|z)R.  ∎

# @livre Ch.II §1.6 Rem.- | E II.5 L.7-13 | PDF p.56
#   (sens intuitif du schéma de sélection et réunion — prose)

# @livre Ch.II §1.6 Crit.51 | E II.5 L.14-28 | PDF p.56
#
# C51 (énoncé L.14-15). « Soient P une relation, A un ensemble et x une lettre
# ne figurant pas dans A. La relation " P et x ∈ A " est collectivisante en x. »
#
# DÉMONSTRATION (livre, L.16-28, condensée). Poser R := « P et x = y » (y
# fraîche). (∀x)(R ⇒ (x ∈ {y})) est vraie d'après C27 ; en la lisant comme
# ({y}|X)((∀x)(R ⇒ (x∈X))), la relation (∀y)(∃X)(∀x)(R ⇒ (x∈X)) est vraie
# (S5 + C27). S8 et C30 donnent alors que (A|Y)Coll_x((∃y)(y∈Y et R)) est
# vraie, identique à Coll_x((∃y)(y∈A et R)). Enfin « y∈A et R » équivaut à
# « x=y et x∈A et P » (C43), donc (∃y)(x=y et x∈A et P) équivaut à
# « P et x∈A » (C33, puis (∃y)(x=y) vraie).  ∎
def enonce_c51(p: Assemblage, a: Assemblage, x: str = "x",
               grand_y: str = "Y") -> Assemblage:
    """La FORME de la conclusion de C51 : Coll_x(P et x∈A), dépliée en
    (∃Y)(∀x)((x∈Y) ⇔ (P et x∈A)).  Niveau assemblages, rien n'est prouvé ici."""
    xt, yt = Assemblage((x,)), Assemblage((grand_y,))
    corps = conjonction(p, appartient(xt, a))
    return existe(grand_y, pour_tout(x, equivalence(appartient(xt, yt), corps)))


# @livre Ch.II §1.6 Def.- | E II.5 L.29-31 | PDF p.56
#
# « L'ensemble {x | P et x∈A} est appelé L'ENSEMBLE DES x ∈ A TELS QUE P et se
# note parfois {x∈A | P}. »  Dans le dépôt, ce terme n'est PAS construit par un
# abréviateur générique : chaque usage passe par une THÉORIE DÉDIÉE légitimée
# par S8 (sélection dans A) + A1 (unicité) — voir chap. III ordre_treillis
# (ensembles_ordre_vocab.py, intervalles [a,b] = {x∈E | a≤x et x≤b}).

# @livre Ch.II §1.6 Crit.52 | E II.5 L.32-34 | PDF p.56
#
# C52 (énoncé L.32-33). « Soient R une relation, A un ensemble, x une lettre ne
# figurant pas dans A. Si la relation R ⇒ (x ∈ A) est un théorème, R est
# collectivisante en x. »
# DÉMONSTRATION (livre, L.34). R est alors équivalente à « R et x ∈ A »,
# et on applique C51.  ∎

# @livre Ch.II §1.6 Rem.- | E II.5 L.35-39 | PDF p.56
#   (si Coll_x(R) et (∀x)(S ⇒ R) théorème, alors S collectivisante — via C52 ;
#    et {x|S} ⊂ {x|R} d'après C50 — prose, démontrée dans le livre)

# @livre Ch.II §1.6 Crit.53 | E II.5 L.40-40 | PDF p.56
#   (début de l'énoncé de C53 — la suite et la démonstration sont en E II.6,
#    page déjà annotée par ailleurs)

__all__ = ["enonce_c51"]
