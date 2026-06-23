"""§III.3.5 — Card(𝔓(X)) = 2^Card X  (E.III.3.5, Proposition 12) : LE SENS FACILE.

Bourbaki (Prop. 12) : « Soient X un ensemble et a son cardinal ; le cardinal de
l'ensemble 𝔓(X) des parties de X est 2^a. »  Le « 2 » est le 2-élément
2 = {0, 1} = {∅, {∅}} = paire(∅, {∅})  (socle DÉJÀ posé dans
`ensembles_powerset_exp` : deux, deux_membre, zero_dans_deux, un_dans_deux,
deux_elements_distincts).  Et  2^Card X := Card(applications(X, 2))
(exposant_cardinal_binaire(2, X), Définition 4 : a^b = cardinal des applications
de b dans a — ici BASE = 2, EXPOSANT = X).

La PREUVE COMPLÈTE passe par la bijection caractéristique
        χ : 𝔓(X) → 𝓕(X; {0,1}),   Y ↦ χ_Y   (x ↦ 1 si x∈Y, 0 sinon).
Le SENS DIFFICILE (χ_Y bien définie + injectif + image = 𝓕) exige un SÉLECTEUR
CONDITIONNEL (« si x∈Y alors 1 sinon 0 »), absent du noyau, et l'extensionnalité
fonctionnelle (cf. `ensembles_powerset_exp.bijection_caracteristique_REPORTE`).
RESTE DONC REPORTÉ ici aussi (raison précise dans `bijection_complete_REPORTE`).

CE MODULE LIVRE LE **SENS FACILE** 𝓕(X; {0,1}) → 𝔓(X), entièrement CERTIFIÉ par
le noyau (rien postulé : seul un axiome de DÉFINITION général fidèle, S8+A1,
exactement comme `diagonale_cantor` E.III.3) :

    f ∈ 𝓕(X; {0,1})  ↦  Pre(f) := { z ∈ X | (z, 1) ∈ f }  =  f⁻¹(1)  ⊂  X .

PALIERS (tous CLOS) :
  • membre_parties_t(Y, X)        ⊢ (Y ∈ P(X)) ⇔ (Y ⊂ X)            [A3, TERMES] ;
  • partie_dans_parties(Y, X)     {Y ⊂ X} ⊢ Y ∈ P(X)               [⇐ de A3] ;
  • preimage_un(f, X)             le terme Pre(f) = {z∈X | (z,1)∈f} = f⁻¹(1) ;
  • preimage_membre(f, X, z)      ⊢ (z ∈ Pre(f)) ⇔ (z∈X et (z,1)∈f) [axiome déf.] ;
  • preimage_inclus(f, X)         ⊢ Pre(f) ⊂ X                       [sens facile,
        toute préimage de 1 est une partie de X] ;
  • preimage_dans_parties(f, X)   ⊢ Pre(f) ∈ P(X)                    [Pre(f)⊂X + A3 :
        le sens facile 𝓕(X;2) → 𝔓(X) est BIEN DÉFINI à valeurs dans P(X)] ;
  • _rho(X) = graphe de f ↦ Pre(f) sur 𝓕(X;2), et
    rho_fonctionnel / rho_domaine   ⊢ ρ fonctionnel, dom ρ = 𝓕(X;2)  [C54 :
        l'application-réciproque-candidate f ↦ f⁻¹(1) est une FONCTION 𝓕(X;2)→𝔓(X)] ;
  • cible_powerset_deux(X)        l'ÉNONCÉ-CIBLE Card(𝔓(X)) = 2^Card X (formule).

Le « 2 » et 2^Card X sont importés du socle existant `ensembles_powerset_exp`
(deux, exposant_deux_base) — RIEN n'y est redéfini.
"""
from __future__ import annotations

from bourbaki.logique.formule import (Terme, var, egal, et, non, ou, impl, equiv,
                     appartient, existe, pourtout, inclus, app, subst_t)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.logique.tactiques.tactiques_abrege import a_implique_a, syllogisme
from bourbaki.logique.tactiques.tactiques_abrege2 import (conjonction_intro,
                               conjonction_elim_gauche, conjonction_elim_droite,
                               equivalence_avant, equivalence_arriere,
                               equivalence_transitivite, instancie)
from bourbaki.logique.tactiques.tactiques_abrege_egalite import (symetrie,
                               composer_egalites, congruence_terme)
from bourbaki.cardinaux.ensembles_cardinaux import cardinal
# Socle 2-élément + pivot 2^a = Card(𝓕(X;2))  (RÉUTILISÉS, jamais redéfinis) :
from bourbaki.cardinaux.arithmetique.ensembles_powerset_exp import (
    deux, deux_membre, exposant_deux_base, cible_powerset_exp)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# ═══════════════════════════════════════════════════════════════════════════════
# Palier A — A3 (axiome des parties) tolérant aux TERMES
# ═══════════════════════════════════════════════════════════════════════════════
def membre_parties_t(y, x):
    """⊢ (Y ∈ P(X)) ⇔ (Y ⊂ X).   (axiome A3 instancié à des TERMES Y, X ; E.II.5.1.)

    Version TERME de `membre_parties` (qui ne prend que des noms) : on instancie
    l'axiome A3 (∀X)(∀Y)(Y∈P(X) ⇔ Y⊂X) aux termes fournis."""
    vY, vX = _t(y), _t(x)
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_PARTIES)        # (∀X)(∀Y)(Y∈P(X)⇔Y⊂X)
    return instancie(instancie(ax, vX), vY)                       # (Y∈P(X)) ⇔ (Y⊂X)


def partie_dans_parties(y, x):
    """{Y ⊂ X} ⊢ Y ∈ P(X).   (toute partie Y⊂X est un élément de P(X) ; sens ⇐ de A3.)"""
    vY, vX = _t(y), _t(x)
    h = N.assume(inclus(vY, vX))                                  # Y ⊂ X
    return N.modus_ponens(h, equivalence_arriere(membre_parties_t(vY, vX)))   # Y∈P(X)


# ═══════════════════════════════════════════════════════════════════════════════
# Le SENS FACILE  𝓕(X; {0,1}) → 𝔓(X)  :  f ↦ Pre(f) = { z∈X | (z, 1) ∈ f }
# ═══════════════════════════════════════════════════════════════════════════════
# Pre(f) = f⁻¹(1) = { z∈X | (z,1)∈f }  est la PRÉIMAGE de 1 = {∅} par (le graphe) f.
# C'est un ensemble de SÉLECTION : « z∈X et R(z) » avec R(z) = « (z,1)∈f », exactement
# la FORME de diagonale_cantor (E.III.3) D = { z∈X | ¬(z∈F(z)) } où R(z) = ¬(z∈F(z)).
# Légitimité : existence par S8 (sélection dans X), unicité par A1 — IDENTIQUE à
# diagonale_cantor / différence E∖X.  X et f sont des PARAMÈTRES ; le liant est « z ».
# Aucun fichier existant n'est modifié : le terme et son axiome de DÉFINITION sont
# locaux à ce module (constructeur E.app, théorie dédiée pour N.axiome).
def _UN():
    """1 := {∅}  (le « 1 » du 2-élément 2 = {∅, {∅}} ; ⊂ Pre(f) repère la valeur 1)."""
    return E.singleton(E.VIDE)


def preimage_un(f, x):
    """Pre(f) := { z ∈ X | (z, 1) ∈ f }  =  f⁻¹(1)   (préimage de 1 = {∅} par f).

    Terme de sélection (S8 dans X, unicité A1), paramétré par f et X, liant « z ».
    C'est l'image de f par le SENS FACILE 𝓕(X; {0,1}) → 𝔓(X) de la Proposition 12."""
    return app("preimage_un", _t(f), _t(x))


def _axiome_preimage(f, x, z="z"):
    """⊢-schéma : (∀z)(z ∈ Pre(f) ⇔ (z∈X et (z,1)∈f))   (DÉFINITION de Pre(f), S8+A1).

    Légitime au même titre que `axiome_diagonale_cantor` : caractérisation
    d'appartenance d'un ensemble de sélection, PAS un théorème (Proposition)."""
    vz = var(z)
    return pourtout(z, equiv(appartient(vz, preimage_un(f, x)),
                             et(appartient(vz, _t(x)),
                                appartient(E.couple(vz, _UN()), _t(f)))))


def _theorie_preimage(f, x, z="z"):
    """Théorie ne contenant que l'instance de l'axiome de Pre(f)  (pour N.axiome)."""
    return N.Theorie("Preimage-un", [_axiome_preimage(f, x, z)])


def preimage_membre(f="f", x="X", z="z"):
    """⊢ (z ∈ Pre(f)) ⇔ (z∈X et (z,1)∈f).   (caractérisation des éléments de f⁻¹(1).)"""
    vf, vX, vz = _t(f), _t(x), _t(z)
    ax = N.axiome(_theorie_preimage(vf, vX), _axiome_preimage(vf, vX))   # (∀z)(...)
    return instancie(ax, vz)                                             # à z


# ── Pre(f) ⊂ X  (le sens facile est à valeurs dans les parties de X) ───────────
def preimage_inclus(f="f", x="X"):
    """⊢ Pre(f) ⊂ X.   (f⁻¹(1) est une PARTIE de X : tout z∈Pre(f) vérifie z∈X.)

    Pre(f)⊂X = (∀z)(z∈Pre(f) ⇒ z∈X).  z∈Pre(f) ⇔ (z∈X et (z,1)∈f) (preimage_membre),
    et la projection gauche donne z∈X."""
    vf, vX, vz = _t(f), _t(x), var("z")
    car = preimage_membre(vf, vX, vz)                            # z∈Pre(f) ⇔ (z∈X et (z,1)∈f)
    hz = N.assume(appartient(vz, preimage_un(vf, vX)))           # z∈Pre(f)
    z_inX = conjonction_elim_gauche(N.modus_ponens(hz, equivalence_avant(car)))   # z∈X
    imp = N.loi_deduction(appartient(vz, preimage_un(vf, vX)), z_inX)   # z∈Pre(f) ⇒ z∈X
    return N.generalisation("z", imp)                           # Pre(f) ⊂ X


# ── Pre(f) ∈ P(X)  (la valeur du sens facile est BIEN un élément de 𝔓(X)) ──────
def preimage_dans_parties(f="f", x="X"):
    """⊢ Pre(f) ∈ P(X).   (le SENS FACILE 𝓕(X;{0,1}) → 𝔓(X) est bien défini :
    f ↦ f⁻¹(1) a pour valeur une PARTIE de X, donc un élément de P(X).)

    Pre(f)⊂X (preimage_inclus) + axiome A3 tolérant aux termes (partie_dans_parties)."""
    vf, vX = _t(f), _t(x)
    incl = preimage_inclus(vf, vX)                              # Pre(f) ⊂ X
    return N.modus_ponens(incl, N.loi_deduction(
        inclus(preimage_un(vf, vX), vX), partie_dans_parties(preimage_un(vf, vX), vX)))


# ═══════════════════════════════════════════════════════════════════════════════
# Le graphe ρ du sens facile  :  ρ = graphe de  f ↦ Pre(f)  sur 𝓕(X; {0,1})
#   (l'application-réciproque-candidate de la bijection χ ; FONCTION 𝓕(X;2) → 𝔓(X))
# ═══════════════════════════════════════════════════════════════════════════════
def _SOURCE(x):
    """𝓕(X; {0,1}) = applications(X, 2)  (la SOURCE du sens facile ; support de 2^a)."""
    return E.applications(_t(x), deux())


def _rho(x):
    """ρ := graphe_terme(𝓕(X;2), Pre(f), "f")  = graphe de  f ↦ f⁻¹(1)  sur 𝓕(X;2).

    Variable de fonction « f » ; le terme-valeur Pre(f) = preimage_un(f, X) ne
    contient pas les liants internes {u,v,z,x,y,w} de la machinerie graphe-terme
    (son seul liant interne propre est « z », celui de la sélection, lié DANS Pre(f))."""
    vX = _t(x)
    return E.graphe_terme(_SOURCE(vX), preimage_un(var("f"), vX), "f")


def rho_fonctionnel(x="X"):
    """⊢ est_fonctionnel(ρ),  ρ = f↦Pre(f) sur 𝓕(X;2).   (cas T=Pre(f) de C54.)

    Le sens facile est une vraie FONCTION : à chaque f∈𝓕(X;2) il associe UNE partie
    Pre(f)=f⁻¹(1).  Fonctionnalité automatique du graphe-terme (graphe_terme_fonctionnel)."""
    from bourbaki.ensembles.fonctions.ii_3_6_fonction_terme.ensembles_fonction_terme import graphe_terme_fonctionnel
    vX = _t(x)
    return graphe_terme_fonctionnel(_SOURCE(vX), preimage_un(var("f"), vX), "f", "y")


def rho_domaine(x="X"):
    """⊢ dom(ρ) = 𝓕(X; {0,1}).   (le sens facile f↦f⁻¹(1) est défini sur TOUT 𝓕(X;2).)"""
    from bourbaki.cardinaux.ensembles_cantor import graphe_terme_domaine
    vX = _t(x)
    return graphe_terme_domaine(_SOURCE(vX), preimage_un(var("f"), vX), "f", "y", "z")


def rho_valeur(x="X", g="g"):
    """{g ∈ 𝓕(X;2)} ⊢ ρ(g) = Pre(g) = g⁻¹(1).   (la valeur du sens facile en g.)

    ⚠️ le point d'évaluation « g » doit DIFFÉRER du liant de fonction « f » de ρ
    (sinon la valeur Pre(g) capturerait le liant « f ») : la valeur de ρ en g est
    Pre(g)=T[f:=g], obtenue en substituant g au liant f dans le terme-valeur Pre(f)."""
    from bourbaki.cardinaux.ensembles_cantor import graphe_terme_valeur
    vX = _t(x)
    if (isinstance(g, str) and g == "f") or g == var("f"):
        raise ValueError("le point d'évaluation de ρ doit différer du liant « f »")
    # graphe_terme_valeur(A, T, u, x, y) ⊢ {u∈A} ⊢ F(u)=T[u] ; T=Pre(f) (liant « f »),
    # u = g (≠ f), donc T[g] = Pre(g) = preimage_un(g, X).
    return graphe_terme_valeur(_SOURCE(vX), preimage_un(var("f"), vX), g, "f", "y")


# ═══════════════════════════════════════════════════════════════════════════════
# L'ÉNONCÉ-CIBLE de la Proposition 12  (formule, fixe la signature de la cible)
# ═══════════════════════════════════════════════════════════════════════════════
def cible_powerset_deux(x="X"):
    """L'ÉNONCÉ visé (Proposition 12) : Card(𝔓(X)) = 2^Card X.

    Renvoie la FORMULE (non un théorème).  IDENTIQUE à
    `ensembles_powerset_exp.cible_powerset_exp` (réexposée ici pour la complétude
    de ce module) : Card(parties(X)) = exposant_cardinal_binaire(2, X) =
    Card(applications(X, 2))."""
    return cible_powerset_exp(_t(x))


# ═══════════════════════════════════════════════════════════════════════════════
# CRUX REPORTÉ : la bijection caractéristique complète  χ : 𝔓(X) → 𝓕(X; {0,1})
# ═══════════════════════════════════════════════════════════════════════════════
def bijection_complete_REPORTE():
    """REPORTÉ (non clos) — la bijection caractéristique χ : 𝔓(X) → 𝓕(X;{0,1}).

    Ce module ferme le SENS FACILE 𝓕(X;{0,1}) → 𝔓(X) (f ↦ f⁻¹(1) = Pre(f),
    BIEN DÉFINI à valeurs dans P(X) : preimage_dans_parties ; et c'est une FONCTION
    ρ : 𝓕(X;2) → 𝔓(X), rho_fonctionnel/rho_domaine).  Restent REPORTÉS, pour les
    raisons précises ci-dessous (toutes hors du budget de ce round) :

      (i)  χ_Y bien définie : χ_Y : X → {0,1} se définit par un SÉLECTEUR
           CONDITIONNEL « si x∈Y alors 1 sinon 0 », dont le graphe N'EST PAS un
           simple graphe_terme(X, T) mais un graphe défini par CAS (S8 sur (∀x∈X)
           puis A1) — primitive « fonction définie par cas » ABSENTE du noyau ;
      (ii) INJECTIVITÉ de χ (resp. SURJECTIVITÉ de ρ, ce qui revient au même) :
           χ_Y = χ_{Y'} ⇒ Y = Y' exige l'extensionnalité FONCTIONNELLE (égalité de
           graphes valeur-par-valeur sur tout X) reliée à l'extensionnalité
           d'ensembles A1 — machinerie de fonctions lourde non disponible ;
      (iii)IMAGE de χ = 𝓕(X;2) (resp. INJECTIVITÉ de ρ) : depuis f∈𝓕(X;2)
           arbitraire, prouver χ_{Pre(f)} = f par extensionnalité fonctionnelle,
           même verrou que (ii).

    La voie complète passe par une primitive « fonction définie par cas / sélecteur
    conditionnel » (analogue à graphe_terme mais à deux branches selon x∈Y) et par
    l'extensionnalité fonctionnelle, à introduire dans un round dédié.  Une fois χ
    bijection, Eq(𝔓(X), 𝓕(X;2)) puis la Proposition 1 (sens direct, _prop1_direct_t)
    donneront Card(𝔓(X)) = Card(𝓕(X;2)) = 2^Card X (cible_powerset_deux)."""
    raise NotImplementedError(
        "Bijection caractéristique complète 𝔓(X) ⇄ 𝓕(X;2) reportée : sélecteur "
        "conditionnel χ_Y (i) + extensionnalité fonctionnelle (ii, iii) absents. "
        "Ce module livre le sens facile f ↦ f⁻¹(1), entièrement certifié.")


__all__ = [
    "membre_parties_t", "partie_dans_parties",
    "preimage_un", "preimage_membre", "preimage_inclus", "preimage_dans_parties",
    "rho_fonctionnel", "rho_domaine", "rho_valeur",
    "cible_powerset_deux", "bijection_complete_REPORTE",
    # réexposés du socle (RIEN redéfini) :
    "deux", "exposant_deux_base",
]
