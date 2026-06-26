"""§IV.1.5 / IV.2.2 / IV.3.1 — PROPOSITIONS & CRITÈRES « logiquement directs » du
chapitre IV (structures, morphismes, applications universelles).   REPRÉSENTATIONNEL.

Module NEUF (campagne « complétude chap. IV », vague IV-structures-props).  Il
COMPLÈTE les modules déjà faits — `ensembles_universel_morphismes` (plus/moins fine,
(IN)), `ensembles_universel_finale` ((FI)), `ensembles_universel_applications` ((AU)),
`ensembles_CST_criteres` (CST9/CST18/CST5/transport préserve morphisme), `especes`
et `ensembles_isomorphismes` (Δ_E iso au niveau relationnel) — en PROUVANT (au niveau
du noyau, `.est_clos` ou conditionnel à hypothèses EXPLICITES) les énoncés du chap. IV
qui sont LOGIQUEMENT DIRECTS et qui n'étaient pas encore traités sous ce nom :

  1. COMPOSITION DE MORPHISMES EST UN MORPHISME (axiome (MO_II), IV.2.1) — théorème
     proprement nommé `composee_morphismes_est_morphisme` (le cœur (MO_II) figurait
     déjà sous le nom `transport_preserve_morphisme` dans CST_criteres ; on en donne
     ici la forme « catégorielle » nommée + le palier réutilisé par la transitivité).

  2. « PLUS FINE / MOINS FINE » EST UN PRÉORDRE (IV.2.2 : « réflexive d'après (MO_III),
     transitive d'après (MO_II) ») :
       • `plus_fine_reflexive`   — réflexivité (via (MO_III) / identité morphisme) ;
       • `plus_fine_transitive`  — TRANSITIVITÉ (via (MO_II) / composition) — NOUVEAU ;
       • `moins_fine_preordre`   — marqueur documenté assemblant réflexif + transitif.

  3. IDENTITÉ EST UN ISOMORPHISME (IV.1.5, niveau ESPÈCE Σ abstraite) :
       • `identite_est_isomorphisme_espece` — (f_i = Δ) est un isomorphisme de (E,U)
         sur (E,U), sous l'hyp explicite que la structure transportée par l'identité
         vaut U (instance de CST1 à l'identité : ⟨Δ,…⟩^S(U) = U), partie « bijection »
         INCONDITIONNELLE (Δ_E bijection de E sur E).

  4. TRANSPORT COMPOSÉ / COMPOSITION D'ISOMORPHISMES (CST4, IV.1.5) :
       • `composee_isomorphismes_est_isomorphisme` — (g∘f) est un isomorphisme de
         (E,U) sur (E'',U''), partie « bijection » INCONDITIONNELLE (composée de deux
         bijections est une bijection, `composee_bijection`), clause (4) transportée
         sous l'hyp explicite CST1 (⟨g∘f⟩^S = ⟨g⟩^S ∘ ⟨f⟩^S).

  5. UNICITÉ (À ISOMORPHISME UNIQUE PRÈS) DE LA SOLUTION UNIVERSELLE QUAND ELLE EXISTE
     (IV.3.1 / critère CST8) :
       • `solution_universelle_iso_unique` — assemble proprement la conclusion
         d'inversibilité croisée (f₂∘f₁=Id, f₁∘f₂=Id) sous (AU_I′) croisé + (AU_II′)
         (forme nommée « solution unique à iso unique près »).

CONVENTION DE PARAMÉTRAGE (identique au reste du chap. IV) : la donnée abstraite
(Σ, σ, α) — méta — est portée par des PRÉDICATS callables → Formule du fragment objet
(`morph(e1,s1,e2,s2,f)`, structures = termes opaques).  Les théorèmes prouvés ne
dépendent QUE de la structure logique (∀/∃/⇔/=) — donc valables QUELLE QUE SOIT la
donnée σ : c'est le « représentationnel / metamath », on certifie le squelette
déductif des énoncés de Bourbaki, le contenu σ restant un paramètre.

theorie_ensembles() reste à 22 axiomes : AUCUN axiome créé ici.  Tout est soit
LOGIQUE PUR (réflexivité, conjonction, modus ponens, S6/Leibniz), soit CONDITIONNEL à
des hypothèses EXPLICITES = les axiomes-schémas (MO_II)/(MO_III)/CST1/(AU_II′) de
Bourbaki INSTANCIÉS, fournis comme PRÉMISSES des théorèmes — JAMAIS postulés vrais.

REPORTÉ honnêtement (méta / lourd, hors fragment) : la TRANSPORTABILITÉ de R et donc
l'existence/validité R{…} des structures transportées (CST5 existence), la PREUVE de
CST1/CST3 (fonctorialité de l'extension d'échelon ⟨·⟩^S, IV.1.2 — récurrence sur le
schéma), l'EXISTENCE des structures initiale/finale (CST22), CST10–CST20.  Voir le
champ `reportes` du rapport.
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (var, egal, et, ou, impl, equiv, non,
                                       pourtout, existe, appartient, app)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege import a_implique_a, syllogisme
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, instancie)
from bourbaki.structures.iv_2_morphismes_structures_derivees.ensembles_universel_morphismes import (
    est_morphisme, plus_fine, moins_fine, _morph_defaut, _t)


# ════════════════════════════════════════════════════════════════════════════
#  Outils internes
# ════════════════════════════════════════════════════════════════════════════
def _morph(morph):
    return morph if morph is not None else _morph_defaut()


# @livre Ch.IV §2.1 Ax.- | E IV.11 L.28-31 | PDF p.214
def axiome_MO_II(e, s, ep, sp, epp, spp, f, g, morph=None):
    """(MO_II) instancié (IV.2.1, axiome de stabilité par composition) — Formule
       « (morph(E,𝒮,E',𝒮',f) et morph(E',𝒮',E'',𝒮'',g)) ⇒ morph(E,𝒮,E'',𝒮'', g∘f) ».

    VERBATIM (MO_II) : « les relations f ∈ σ[E,E',𝒮,𝒮'] et g ∈ σ[E',E'',𝒮',𝒮'']
    entraînent la relation g∘f ∈ σ[E,E'',𝒮,𝒮''] ».  PRÉMISSE EXPLICITE des théorèmes
    de composition ci-dessous — jamais postulée vraie dans la théorie.

    NB : on N'altère PAS les arguments de structure (𝒮,𝒮',𝒮'') — on les transmet TELS
    QUELS à `est_morphisme`, exactement comme le fait `plus_fine`, pour que les
    morphismes soient LITTÉRALEMENT identiques (cf. `plus_fine`)."""
    morph = _morph(morph)
    e, ep, epp, f, g = _t(e), _t(ep), _t(epp), _t(f), _t(g)
    m1 = est_morphisme(e, s, ep, sp, f, morph)
    m2 = est_morphisme(ep, sp, epp, spp, g, morph)
    concl = est_morphisme(e, s, epp, spp, E.composee(g, f), morph)
    return impl(et(m1, m2), concl)


# ════════════════════════════════════════════════════════════════════════════
#  1.  COMPOSITION DE MORPHISMES EST UN MORPHISME  (axiome (MO_II), IV.2.1)
# ════════════════════════════════════════════════════════════════════════════
# @livre Ch.IV §2.1 Ax.- | E IV.11 L.28-31 | PDF p.214
def composee_morphismes_est_morphisme(e="E", s="S", ep="Ep", sp="Sp",
                                      epp="Epp", spp="Spp", f="f", g="g",
                                      morph=None):
    """{(MO_II) instancié, morph(E,𝒮,E',𝒮',f), morph(E',𝒮',E'',𝒮'',g)}
        ⊢  morph(E,𝒮,E'',𝒮'', g∘f).

    « LA COMPOSÉE DE DEUX σ-MORPHISMES EST UN σ-MORPHISME » (axiome (MO_II), IV.2.1 —
    l'énoncé fondateur de la catégorie des Σ-structures).  Forme proprement nommée du
    cœur (MO_II) (le même palier sert sous le nom `transport_preserve_morphisme` dans
    `ensembles_CST_criteres`).  Preuve : sous les deux morphismes en hypothèse et
    (MO_II), modus ponens sur leur conjonction.  Purement logique."""
    morph = _morph(morph)
    e, s, ep, sp, epp, spp, f, g = map(_t, (e, s, ep, sp, epp, spp, f, g))
    mo2 = axiome_MO_II(e, s, ep, sp, epp, spp, f, g, morph)
    h_mo2 = N.assume(mo2)
    h_f = N.assume(morph(e, s, ep, sp, f))
    h_g = N.assume(morph(ep, sp, epp, spp, g))
    conj = conjonction_intro(h_f, h_g)
    return N.modus_ponens(conj, h_mo2)         # morph(E,𝒮,E'',𝒮'', g∘f)


# ════════════════════════════════════════════════════════════════════════════
#  2.  « PLUS FINE / MOINS FINE » EST UN PRÉORDRE  (IV.2.2)
# ════════════════════════════════════════════════════════════════════════════
#  « La relation "𝒮₁ moins fine que 𝒮₂" est une relation d'ordre … réflexive d'après
#    (MO_III), transitive d'après (MO_II), antisymétrique d'après (MO_III). »  (IV.2.2)
#  Réflexivité + transitivité = PRÉORDRE (l'antisymétrie, qui donne l'ordre, dépend de
#  (MO_III) et est fournie en hypothèse explicite ailleurs, cf. CST9/CST18).
#
# @livre Ch.IV §2.1 Ax.- | E IV.11 L.32-36 | PDF p.214
def id_est_morphisme(e, s, morph=None):
    """Formule « id_E = Δ_E est un σ-morphisme de (E,𝒮) dans (E,𝒮) ».  Instance d'
    (MO_III) (toute identité est un morphisme — c'est même un isomorphisme) ; PRÉMISSE
    structurelle EXPLICITE, jamais axiome de la théorie."""
    morph = _morph(morph)
    ve, vs = _t(e), _t(s)
    return est_morphisme(ve, vs, ve, vs, E.diagonale(ve), morph)


def plus_fine_reflexive(e="E", s="S", morph=None):
    """{« id_E morphisme (E,𝒮)->(E,𝒮) » (MO_III)}  ⊢  plus_fine(E, 𝒮, 𝒮).

    RÉFLEXIVITÉ de « plus fine » (IV.2.2, « réflexive d'après (MO_III) »).  Par
    définition, plus_fine(E,𝒮,𝒮) EST « id_E est un morphisme de (E,𝒮) dans (E,𝒮) » ;
    sous l'hypothèse (MO_III) instanciée (id_E morphisme), on conclut donc
    plus_fine(E,𝒮,𝒮) (a_implique_a : {idm} ⊢ idm)."""
    idm = id_est_morphisme(e, s, morph)               # == plus_fine(E,𝒮,𝒮)
    return N.assume(idm)                              # {idm} ⊢ idm


def plus_fine_transitive(e="E", s1="S1", s2="S2", s3="S3", morph=None):
    """{(MO_II) instancié à (E,𝒮₁)→(E,𝒮₂)→(E,𝒮₃) avec f=g=Δ_E,
        plus_fine(E,𝒮₁,𝒮₂), plus_fine(E,𝒮₂,𝒮₃)}
        ⊢  morph(E,𝒮₁,E,𝒮₃, Δ_E∘Δ_E)  ( = « plus_fine(E,𝒮₁,𝒮₃) modulo Δ∘Δ=Δ »).

    TRANSITIVITÉ de « plus fine » (IV.2.2, « transitive d'après (MO_II) »).  NOUVEAU.
    plus_fine(E,𝒮₁,𝒮₂) = « Δ_E morphisme (E,𝒮₁)->(E,𝒮₂) », plus_fine(E,𝒮₂,𝒮₃) =
    « Δ_E morphisme (E,𝒮₂)->(E,𝒮₃) » ; par (MO_II), leur composée Δ_E∘Δ_E est un
    morphisme (E,𝒮₁)->(E,𝒮₃).  Comme Δ_E∘Δ_E = Δ_E (l'identité est idempotente —
    lemme `composee_diagonale_diagonale` ci-dessous, fourni en hypothèse explicite
    pour rester self-contained), ce morphisme EST plus_fine(E,𝒮₁,𝒮₃).

    On délivre ici la forme avec Δ_E∘Δ_E (FIDÈLE à (MO_II), purement logique) ; la
    réécriture finale Δ∘Δ=Δ ⇒ plus_fine(E,𝒮₁,𝒮₃) est faite par
    `plus_fine_transitive_normalisee` (qui décharge en plus l'égalité Δ∘Δ=Δ)."""
    morph = _morph(morph)
    ve, vs1, vs2, vs3 = _t(e), _t(s1), _t(s2), _t(s3)   # structures PROMUES (termes)
    DE = E.diagonale(ve)
    # plus_fine(E,𝒮ᵢ,𝒮ⱼ) = morph(E,𝒮ᵢ,E,𝒮ⱼ,Δ_E) — structures = TERMES (substituables)
    pf12 = plus_fine(ve, vs1, vs2, morph)             # morph(E,𝒮₁,E,𝒮₂,Δ_E)
    pf23 = plus_fine(ve, vs2, vs3, morph)             # morph(E,𝒮₂,E,𝒮₃,Δ_E)
    h12, h23 = N.assume(pf12), N.assume(pf23)
    # MO_II : structures (𝒮₁,𝒮₂,𝒮₃) (termes), ensembles E=E'=E''=E, applications f=g=Δ_E.
    mo2 = axiome_MO_II(ve, vs1, ve, vs2, ve, vs3, DE, DE, morph)
    h_mo2 = N.assume(mo2)
    conj = conjonction_intro(h12, h23)
    return N.modus_ponens(conj, h_mo2)               # morph(E,𝒮₁,E,𝒮₃, Δ_E∘Δ_E)


def plus_fine_transitive_normalisee(e="E", s1="S1", s2="S2", s3="S3", morph=None):
    """{(MO_II), plus_fine(E,𝒮₁,𝒮₂), plus_fine(E,𝒮₂,𝒮₃), (Δ_E∘Δ_E = Δ_E)}
        ⊢  plus_fine(E, 𝒮₁, 𝒮₃).

    TRANSITIVITÉ pleine de « plus fine » (IV.2.2).  Reprend `plus_fine_transitive`
    (qui conclut morph(E,𝒮₁,E,𝒮₃, Δ_E∘Δ_E)) puis réécrit Δ_E∘Δ_E en Δ_E par
    l'égalité d'idempotence de l'identité (Δ_E∘Δ_E = Δ_E), fournie en HYPOTHÈSE
    EXPLICITE (lemme de composition de fonctions, certifié ailleurs ; ici prémisse
    pour rester self-contained et ne créer aucun axiome).  Le résultat EST
    littéralement plus_fine(E,𝒮₁,𝒮₃) = morph(E,𝒮₁,E,𝒮₃,Δ_E).  S6/Leibniz."""
    morph = _morph(morph)
    ve, vs1, vs3 = _t(e), _t(s1), _t(s3)              # structures PROMUES (termes)
    DE = E.diagonale(ve)
    DDE = E.composee(DE, DE)                          # Δ_E∘Δ_E
    th = plus_fine_transitive(e, s1, s2, s3, morph)   # morph(E,𝒮₁,E,𝒮₃, Δ_E∘Δ_E)
    # réécrit le dernier argument Δ_E∘Δ_E ↦ Δ_E via (Δ_E∘Δ_E = Δ_E) et S6
    idem = egal(DDE, DE)                              # Δ_E∘Δ_E = Δ_E  (hyp explicite)
    h_idem = N.assume(idem)
    # S6 : (DDE = DE) ⇒ ( motif[w:=DDE] ⇔ motif[w:=DE] ) ; motif = morph(E,𝒮₁,E,𝒮₃, w)
    # structures = TERMES (substituables) — sinon subst_f planterait.
    w = "w_pftrans"
    motif = est_morphisme(ve, vs1, ve, vs3, var(w), morph)   # morph(E,𝒮₁,E,𝒮₃, w)
    s6 = N.s6(DDE, DE, w, motif)                      # (DDE=DE) ⇒ (motif[DDE] ⇔ motif[DE])
    eqv = N.modus_ponens(h_idem, s6)                  # morph(...,Δ∘Δ) ⇔ morph(...,Δ)
    return N.modus_ponens(th, equivalence_avant(eqv)) # plus_fine(E,𝒮₁,𝒮₃)


def composee_diagonale_diagonale(e="E"):
    """Énoncé de l'idempotence de l'identité : Δ_E ∘ Δ_E = Δ_E  (id ∘ id = id).
    NOTE : c'est la PRÉMISSE Δ∘Δ=Δ de `plus_fine_transitive_normalisee` ; sa preuve
    (composition de fonctions, E.II.3.4) relève du module `composee`/`restrictions`
    — fournie ici comme Formule (l'égalité à charger), pas certifiée dans ce module
    NEUF (qui ne modifie aucun fichier existant)."""
    ve = _t(e)
    DE = E.diagonale(ve)
    return egal(E.composee(DE, DE), DE)


def moins_fine_preordre(e="E", s1="S1", s2="S2", s3="S3", morph=None):
    """« moins fine » est un PRÉORDRE sur les structures d'espèce Σ sur E (IV.2.2,
    partie « réflexive d'après (MO_III), transitive d'après (MO_II) »).

    MARQUEUR documenté assemblant les DEUX théorèmes certifiés de ce module :
      • réflexivité  : `plus_fine_reflexive`            (théorème, sous (MO_III)) ;
      • transitivité : `plus_fine_transitive_normalisee`(théorème, sous (MO_II)+Δ∘Δ=Δ).
    L'ANTISYMÉTRIE (qui ferait de « moins fine » un ORDRE, non un simple préordre)
    dépend de (MO_III) et est traitée en hypothèse explicite dans CST9/CST18
    (`ensembles_CST_criteres`).  Renvoie un dict {refl, trans, est_preordre, …}."""
    refl = plus_fine_reflexive(e, s1, morph)
    trans = plus_fine_transitive_normalisee(e, s1, s2, s3, morph)
    return {
        "relation": "moins fine (IV.2.2)",
        "reflexivite": refl,            # Théorème (sous (MO_III))
        "transitivite": trans,          # Théorème (sous (MO_II) + Δ∘Δ=Δ)
        "est_preordre": True,
        "antisymetrie": "hypothèse (MO_III), cf. CST9/CST18 — donne l'ORDRE",
        "representationnel": True,
    }


# ════════════════════════════════════════════════════════════════════════════
#  3.  IDENTITÉ EST UN ISOMORPHISME  (niveau ESPÈCE Σ, IV.1.5)
# ════════════════════════════════════════════════════════════════════════════
from bourbaki.cardinaux.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import est_bijection_de
from bourbaki.cardinaux.iii_3_equipotence_cardinaux.equipotence.ensembles_equipotence import (
    diagonale_fonctionnelle, diagonale_domaine, diagonale_injective,
    diagonale_image)
from bourbaki.cardinaux.iii_3_equipotence_cardinaux.equipotence.ensembles_composee_bijection import composee_bijection
from bourbaki.structures.iv_1_structures_isomorphismes.ensembles_especes import (
    est_isomorphisme, structure_transportee)


def _diagonale_bijection(e):
    """⊢ est_bijection_de(Δ_E, E, E)  — CLOS, INCONDITIONNEL (Δ_E est une bijection de
    E sur E).  Assemble les quatre paliers certifiés diagonale_fonctionnelle / _domaine
    / _injective / _image dans la structure ((func,dom),(inj,img)) de est_bijection_de
    (cf. `ensembles_isomorphismes.identite_est_isomorphisme`)."""
    ne = e if isinstance(e, str) else None
    if ne is None:
        # diagonale_* prennent un nom de variable ; si e est un Terme var, on récupère
        # son nom ; sinon on échoue proprement (cas hors fragment).
        ne = e.nom
    return conjonction_intro(
        conjonction_intro(diagonale_fonctionnelle(ne), diagonale_domaine(ne)),
        conjonction_intro(diagonale_injective(ne), diagonale_image(ne)))


def identite_est_isomorphisme_espece(sigma, e="E", u="U"):
    """{ ⟨Δ_E, Id⟩^S(U) = U  (CST1 à l'identité) }
        ⊢  est_isomorphisme(Σ, (Δ_E), [E], [E], U, U).

    « L'APPLICATION IDENTIQUE EST UN ISOMORPHISME » (IV.1.5, niveau ESPÈCE Σ abstraite ;
    cas particulier de l'automorphisme).  est_isomorphisme(Σ,(Δ_E),[E],[E],U,U) est la
    conjonction : (1) « Δ_E est une bijection de E sur E » — INCONDITIONNEL (les quatre
    paliers diagonale_*) ; (2) la clause (4) « ⟨Δ_E,Id⟩^S(U) = U ».

    La clause (4) EST l'instance de CST1 (fonctorialité de l'extension d'échelon) à
    l'identité : ⟨Δ_E,…⟩^S = Id sur l'échelon, donc ⟨Δ_E,…⟩^S(U) = U.  La PREUVE de
    CST1 (récurrence sur le schéma S, IV.1.2) sort du fragment ; on la fournit donc en
    HYPOTHÈSE EXPLICITE (l'égalité ⟨Δ_E,Id⟩^S(U) = U), JAMAIS postulée comme axiome de
    la théorie.  Recollement : conjonction (bijection ∧ clause (4)).

    Renvoie le théorème conditionnel ; UNIQUE hypothèse = la clause (4) à l'identité.
    NB : la partie « bijection » est INCONDITIONNELLE (théorème clos absorbé)."""
    ve = _t(e)
    DE = E.diagonale(ve)
    iso = est_isomorphisme(sigma, [DE], [ve], [ve], _t(u), _t(u))
    # est_isomorphisme = et(bij_clause, eq4) (n=1, 0 auxiliaire bijection extra)
    bij_target = est_bijection_de(DE, ve, ve)
    # clause (4) effective telle que la construit est_isomorphisme :
    eq4 = egal(structure_transportee(sigma, [DE], _t(u)), _t(u))     # ⟨Δ_E,Id⟩^S(U) = U
    # bijection — théorème clos
    bij_thm = _diagonale_bijection(e)
    assert bij_thm.conclusion == bij_target, "structure bijection inattendue"
    # clause (4) — hypothèse explicite (CST1 à l'identité)
    h_eq4 = N.assume(eq4)
    return conjonction_intro(bij_thm, h_eq4)        # ⊢ est_isomorphisme(Σ,(Δ),[E],[E],U,U)


# ════════════════════════════════════════════════════════════════════════════
#  4.  TRANSPORT COMPOSÉ / COMPOSITION D'ISOMORPHISMES  (CST4, IV.1.5)
# ════════════════════════════════════════════════════════════════════════════
def composee_isomorphismes_est_isomorphisme(sigma, e="E", ep="Ep", epp="Epp",
                                            u="U", up="Up", upp="Upp",
                                            f="f", g="g"):
    """{ est_bijection_de(f,E,E'), est_bijection_de(g,E',E''),
         ⟨f,Id⟩^S(U) = U', ⟨g,Id⟩^S(U') = U'',
         ⟨g∘f,Id⟩^S(U) = ⟨g,Id⟩^S(⟨f,Id⟩^S(U))   (CST1 : fonctorialité) }
        ⊢  est_isomorphisme(Σ, (g∘f), [E], [E''], U, U'').

    CRITÈRE CST4 (IV.1.5) — COMPOSITION D'ISOMORPHISMES / TRANSPORT COMPOSÉ : « si
    (f) est un isomorphisme de U sur U' et (g) un isomorphisme de U' sur U'', alors
    (g∘f) est un isomorphisme de U sur U'' ».  est_isomorphisme(Σ,(g∘f),[E],[E''],U,U'')
    = (1) « g∘f bijection de E sur E'' » ∧ (2) clause (4) « ⟨g∘f,Id⟩^S(U) = U'' ».

    PREUVE :
      (1) bijection : `composee_bijection` ⊢ (bij(f,E,E') ∧ bij(g,E',E'')) ⇒
          bij(g∘f,E,E'') — modus ponens sous les deux bijections (hypothèses, qui sont
          précisément les clauses « bijection » des deux isomorphismes donnés) ;
      (2) clause (4) : par CST1 (fonctorialité de ⟨·⟩^S — IV.1.2, hypothèse explicite),
          ⟨g∘f,Id⟩^S(U) = ⟨g,Id⟩^S(⟨f,Id⟩^S(U)) ; puis ⟨f,Id⟩^S(U)=U' (clause (4) de
          f) et ⟨g,Id⟩^S(U')=U'' (clause (4) de g) donnent, par S6/Leibniz,
          ⟨g∘f,Id⟩^S(U) = U''.
    Recollement par conjonction.  Hypothèses EXPLICITES (les 2 bijections + 2 clauses (4)
    des isos donnés + l'instance CST1) ; AUCUN axiome créé.  La preuve de CST1 (récurrence
    sur le schéma) est REPORTÉE (fournie en hypothèse)."""
    ve, vep, vepp = _t(e), _t(ep), _t(epp)
    vu, vup, vupp = _t(u), _t(up), _t(upp)
    vf, vg = _t(f), _t(g)
    gof = E.composee(vg, vf)                         # g∘f

    # — (1) bijection g∘f : E → E'' —
    bf = est_bijection_de(vf, ve, vep)
    bg = est_bijection_de(vg, vep, vepp)
    cb = composee_bijection(f, g, e, ep, epp)        # (bf ∧ bg) ⇒ bij(g∘f,E,E'')
    h_bf, h_bg = N.assume(bf), N.assume(bg)
    bij_gof = N.modus_ponens(conjonction_intro(h_bf, h_bg), cb)   # bij(g∘f,E,E'')

    # — (2) clause (4) : ⟨g∘f,Id⟩^S(U) = U'' —
    tr_f = structure_transportee(sigma, [vf], vu)    # ⟨f,Id⟩^S(U)
    tr_g_of_f = structure_transportee(sigma, [vg], tr_f)   # ⟨g,Id⟩^S(⟨f,Id⟩^S(U))
    tr_gof = structure_transportee(sigma, [gof], vu)       # ⟨g∘f,Id⟩^S(U)
    # clause (4) des isos donnés :
    eq_f = egal(tr_f, vup)                           # ⟨f,Id⟩^S(U) = U'        (iso f)
    eq_g = egal(structure_transportee(sigma, [vg], vup), vupp)  # ⟨g,Id⟩^S(U') = U'' (iso g)
    # CST1 : ⟨g∘f,Id⟩^S(U) = ⟨g,Id⟩^S(⟨f,Id⟩^S(U))   (fonctorialité, hyp explicite)
    cst1 = egal(tr_gof, tr_g_of_f)
    h_eq_f, h_eq_g, h_cst1 = N.assume(eq_f), N.assume(eq_g), N.assume(cst1)
    # étape A : réécrire ⟨g,Id⟩^S(⟨f,Id⟩^S(U)) ↦ ⟨g,Id⟩^S(U') via eq_f (S6, trou w)
    w = "w_cst4"
    motifG = egal(tr_gof, structure_transportee(sigma, [vg], var(w)))  # tr_gof = ⟨g⟩^S(w)
    # (⟨f⟩^S(U) = U') ⇒ ( [tr_gof = ⟨g⟩^S(w)][w:=tr_f] ⇔ [.][w:=U'] )
    s6A = N.s6(tr_f, vup, w, motifG)
    eqvA = N.modus_ponens(h_eq_f, s6A)              # (tr_gof = ⟨g⟩^S(tr_f)) ⇔ (tr_gof = ⟨g⟩^S(U'))
    # de CST1 (tr_gof = ⟨g⟩^S(tr_f)) on passe à (tr_gof = ⟨g⟩^S(U')) :
    tr_gof_eq_gUp = N.modus_ponens(h_cst1, equivalence_avant(eqvA))   # tr_gof = ⟨g⟩^S(U')
    # étape B : (⟨g⟩^S(U') = U'')  et  (tr_gof = ⟨g⟩^S(U'))  ⊢  tr_gof = U''  (transitivité)
    #   via S6 : (⟨g⟩^S(U') = U'') ⇒ ( [tr_gof = z][z:=⟨g⟩^S(U')] ⇔ [tr_gof = z][z:=U''] )
    z = "z_cst4"
    gUp = structure_transportee(sigma, [vg], vup)   # ⟨g⟩^S(U')
    motifZ = egal(tr_gof, var(z))                   # tr_gof = z
    s6B = N.s6(gUp, vupp, z, motifZ)
    eqvB = N.modus_ponens(h_eq_g, s6B)              # (tr_gof = ⟨g⟩^S(U')) ⇔ (tr_gof = U'')
    eq4_final = N.modus_ponens(tr_gof_eq_gUp, equivalence_avant(eqvB))  # tr_gof = U''  (clause (4))

    # — recollement : conjonction (bijection ∧ clause (4)) = est_isomorphisme —
    iso = conjonction_intro(bij_gof, eq4_final)
    # contrôle que c'est bien la cible est_isomorphisme(Σ,(g∘f),[E],[E''],U,U'')
    cible = est_isomorphisme(sigma, [gof], [ve], [vepp], vu, vupp)
    assert iso.conclusion == cible, "conclusion ≠ est_isomorphisme attendu"
    return iso


# ════════════════════════════════════════════════════════════════════════════
#  5.  UNICITÉ (À ISOMORPHISME UNIQUE PRÈS) DE LA SOLUTION UNIVERSELLE  (§IV.3.1, E IV.23)
#      Conséquence de (AU) + critère CST8 d'INVERSIBILITÉ (IV.12) — ⚠ PAS le critère CST8
#      lui-même (fragment : conclut seulement l'inversibilité croisée f₂∘f₁=Id, f₁∘f₂=Id).
# ════════════════════════════════════════════════════════════════════════════
def solution_universelle_iso_unique(fe="FE", se="SE", phi_e="phiE",
                                    fep="FEp", sep="SEp", phi_ep="phiEp",
                                    f1="f1", f2="f2", morph=None):
    """{ H1 := morph(F_E,S_E,F_E',S_E',f₁) et φ_E' = f₁∘φ_E      (AU_I′ croisé, sol. F_E),
         H2 := morph(F_E',S_E',F_E,S_E,f₂) et φ_E = f₂∘φ_E'      (AU_I′ croisé, sol. F_E'),
         INV := (H1 et H2) ⇒ (f₂∘f₁ = Id_{F_E} et f₁∘f₂ = Id_{F_E'})   (AU_II′) }
        ⊢  f₂∘f₁ = Id_{F_E}  et  f₁∘f₂ = Id_{F_E'}.

    « LA SOLUTION D'UN PROBLÈME D'APPLICATION UNIVERSELLE EST UNIQUE À UN ISOMORPHISME
    UNIQUE PRÈS QUAND ELLE EXISTE » (§IV.3.1, E IV.23 ; démontré via le critère CST8
    d'inversibilité, IV p. 12 — ce résultat n'est pas lui-même CST8).  Si (F_E,φ_E) et
    (F_E',φ_E') sont deux solutions, il existe des morphismes croisés f₁,f₂ avec
    φ_E'=f₁∘φ_E et φ_E=f₂∘φ_E' ; alors f₂∘f₁=Id_{F_E} et f₁∘f₂=Id_{F_E'}, donc f₁ est un
    isomorphisme de F_E sur F_E' et f₂ son réciproque.

    Le cœur logique est l'application de l'UNICITÉ (AU_II′) (deux morphismes de F_E qui
    coïncident dans φ_E(E) sont égaux : f₂∘f₁ et Id coïncident sur φ_E(E) donc sont égaux ;
    de même f₁∘f₂ et Id sur F_E') fournie ici sous forme d'HYPOTHÈSE EXPLICITE `INV`
    (instance de (AU_II′)) ; on conclut l'inversibilité croisée par modus ponens.  Rien
    postulé : `INV` est (AU_II′) instancié, prémisse du théorème ; l'EXISTENCE des f_i
    (AU_I′) est aussi en hypothèse (H1, H2).  Purement logique (conjonction + modus
    ponens) ; forme nommée du contenu de CST8 (équivalent de
    `ensembles_CST_criteres.factorisation_unique_des_solutions`, ici exposé sous le nom
    « unicité de la solution universelle »)."""
    morph = _morph(morph)
    fe, se, phi_e = map(_t, (fe, se, phi_e))
    fep, sep, phi_ep = map(_t, (fep, sep, phi_ep))
    vf1, vf2 = _t(f1), _t(f2)
    H1 = et(morph(fe, se, fep, sep, vf1), egal(phi_ep, E.composee(vf1, phi_e)))
    H2 = et(morph(fep, sep, fe, se, vf2), egal(phi_e, E.composee(vf2, phi_ep)))
    inv1 = egal(E.composee(vf2, vf1), E.diagonale(fe))      # f₂∘f₁ = Id_{F_E}
    inv2 = egal(E.composee(vf1, vf2), E.diagonale(fep))     # f₁∘f₂ = Id_{F_E'}
    INV = impl(et(H1, H2), et(inv1, inv2))                  # (AU_II′) instancié
    h1, h2, hinv = N.assume(H1), N.assume(H2), N.assume(INV)
    conj = conjonction_intro(h1, h2)
    return N.modus_ponens(conj, hinv)          # ⊢ (f₂∘f₁=Id et f₁∘f₂=Id)  — iso unique


__all__ = [
    # 1. composition de morphismes
    "axiome_MO_II", "composee_morphismes_est_morphisme",
    # 2. préordre « plus/moins fine »
    "id_est_morphisme",
    "plus_fine_reflexive", "plus_fine_transitive",
    "plus_fine_transitive_normalisee", "composee_diagonale_diagonale",
    "moins_fine_preordre",
    # 3. identité est iso (espèce)
    "identite_est_isomorphisme_espece",
    # 4. transport composé / CST4
    "composee_isomorphismes_est_isomorphisme",
    # 5. unicité solution universelle / CST8
    "solution_universelle_iso_unique",
]
