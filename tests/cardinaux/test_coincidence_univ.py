"""Tests §III.2 — Lemme 1 (cœur Cantor–Bernstein des bons ordres) : COÏNCIDENCE des
deux isos sur SEGMENTS EMBOÎTÉS S1 ⊂ S2 (dernière pièce de la TRICHOTOMIE, Th3).

Certifie que `ensembles_coincidence_univ` livre :

  ✅ coincidence_univ : ⊢ {  est_bien_ordonne(R,E) + inclus(S1,E)  [BON ORDRE AMBIANT,
                             jamais bo(R,S1)],  S1 ⊂ S2,  compatible_ordre(φ2,S2),
                             iso(φ1,S1,T1),  est_bijective(φ2,S1,T1),  + géométrie }
                          ⊢ (∀u)( u ∈ S1 ⇒ φ1(u) = φ2(u) ).

Points VÉRIFIÉS (honnêteté LCF stricte) :
  • conclusion == cible (= conclusion de coincidence_depuis_isos_compat S:=S1,φ:=φ1,φ':=φ2) ;
  • NON vacueux : conclusion ∉ hypothèses ;
  • l'EMBOÎTEMENT S1 ⊂ S2 est RÉELLEMENT dans le séquent (load-bearing, consommé par
    la restriction) ;
  • l'hypothèse iso(φ2,S1,T1) de la base est DÉCHARGÉE (absente du séquent final),
    REMPLACÉE par compatible_ordre(φ2,S2) + S1⊂S2 + est_bijective(φ2,S1,T1) ;
  • theorie_ensembles() reste = 22 ; aucun fichier modifié.
"""
from bourbaki.logique.formule import var, appartient, inclus, libres_f
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.ordre import ensembles_ordre_vocab as V
from bourbaki.cardinaux.ensembles_coincidence_pont import (
    coincidence_depuis_isos_compat,
)
from bourbaki.cardinaux import ensembles_coincidence_univ as U


def _Rgraphe(nom):
    return lambda a, b: appartient(E.couple(a, b), var(nom))


# ════════════════════════════════════════════════════════════════════════════
#  CONCLUSION — la coïncidence universelle conclut bien φ1=φ2 sur S1.
# ════════════════════════════════════════════════════════════════════════════
def test_coincidence_univ_conclusion():
    """⊢ (∀u)(u∈S1 ⇒ φ1(u)=φ2(u))  (conclusion == cible)."""
    t = U.coincidence_univ()
    assert not t.est_clos                              # conditionnel honnête
    assert t.conclusion == U.coincidence_univ_cible()
    assert t.conclusion not in t.hypotheses            # NON tautologique


def test_coincidence_univ_cible_libres():
    """La cible ne dépend QUE de S1, φ1, φ2 (φ1=φ2 sur S1)."""
    c = U.coincidence_univ_cible()
    assert sorted(libres_f(c)) == ["S1", "phi1", "phi2"]


# ════════════════════════════════════════════════════════════════════════════
#  EMBOÎTEMENT S1 ⊂ S2 — réellement consommé (load-bearing).
# ════════════════════════════════════════════════════════════════════════════
def test_coincidence_univ_inclusion_dans_sequent():
    """L'INCLUSION S1 ⊂ S2 (segments emboîtés) est dans le séquent : la coïncidence
    universelle dépend RÉELLEMENT de l'emboîtement (pièce nestée de Lemme 1)."""
    t = U.coincidence_univ()
    S1_sub_S2 = inclus(var("S1"), var("S2"))
    assert S1_sub_S2 in set(t.hypotheses)


def test_coincidence_univ_compat_phi2_sur_S2():
    """φ2 est ordre-compatible sur le GRAND segment S2 (sa demeure native, Lemme 1) :
    c'est compatible_ordre(φ2,S2) qui figure au séquent, pas la version sur S1."""
    t = U.coincidence_univ()
    Rf, Rpf = _Rgraphe("G"), _Rgraphe("Gp")
    compat_S2 = V.compatible_ordre(var("phi2"), var("S2"), Rf, Rpf, x="x", y="x2")
    assert compat_S2 in set(t.hypotheses)


# ════════════════════════════════════════════════════════════════════════════
#  DÉCHARGE — iso(φ2,S1,T1) de la base est REMPLACÉ par les données nestées.
# ════════════════════════════════════════════════════════════════════════════
def test_coincidence_univ_decharge_iso_phi2_sur_S1():
    """L'hypothèse iso(φ2,S1,T1) de la base (φ2 présupposé iso de S1) est ABSENTE du
    séquent final : elle est DÉRIVÉE de la restriction (φ2 sur S2 + S1⊂S2)."""
    base = coincidence_depuis_isos_compat(
        phi="phi1", phip="phi2", S="S1", T="T1", G="G", Gp="Gp")
    t = U.coincidence_univ()
    Rf, Rpf = _Rgraphe("G"), _Rgraphe("Gp")
    iso_phi2_S1 = V.est_isomorphisme_ordre(
        var("phi2"), var("S1"), var("T1"), Rf, Rpf, x="x", y="x2")
    # présente dans la base, ABSENTE après décharge
    assert iso_phi2_S1 in set(base.hypotheses)
    assert iso_phi2_S1 not in set(t.hypotheses)


def test_coincidence_univ_bijectivite_phi2_S1_explicite():
    """La BIJECTIVITÉ de φ2|S1 (codomaine, REPORTÉ) reste hypothèse EXPLICITE."""
    t = U.coincidence_univ()
    bij = E.est_bijective(var("phi2"), var("S1"), var("T1"))
    assert bij in set(t.hypotheses)


def test_coincidence_univ_garde_le_reste():
    """Toutes les AUTRES hypothèses de la base (sauf iso(φ2,S1,T1) déchargé) sont
    CONSERVÉES : on n'a touché QUE l'iso de φ2 sur S1."""
    base = coincidence_depuis_isos_compat(
        phi="phi1", phip="phi2", S="S1", T="T1", G="G", Gp="Gp")
    t = U.coincidence_univ()
    Rf, Rpf = _Rgraphe("G"), _Rgraphe("Gp")
    iso_phi2_S1 = V.est_isomorphisme_ordre(
        var("phi2"), var("S1"), var("T1"), Rf, Rpf, x="x", y="x2")
    reste = set(base.hypotheses) - {iso_phi2_S1}
    assert reste.issubset(set(t.hypotheses))           # rien d'autre n'a disparu


def test_coincidence_univ_parametrable():
    """Paramétrable : conclusion suit les noms (isos, segments, image) fournis, reste
    non vacueuse, et l'emboîtement A ⊂ B reste load-bearing.

    NB : on renomme les paramètres MATHÉMATIQUES PRINCIPAUX (les deux isos φ1,φ2, les
    segments emboîtés S1,S2, l'image T1, les automorphismes témoins c,k).  Les binders
    internes ψ,χ,u et les noms de graphe G,Gp sont laissés par défaut : la chaîne
    committée (coincidence_depuis_isos_compat / composee_fonctionnelle) emploie sur eux
    des binders internes fragiles vis-à-vis d'un renommage — fragilité PRÉEXISTANTE,
    hors périmètre de ce module (dont le rôle est l'emboîtement S1 ⊂ S2)."""
    t = U.coincidence_univ(
        phi1="f", phi2="g", S1="A", S2="B", T1="C", c="cc", k="kk")
    assert t.conclusion == U.coincidence_univ_cible(phi1="f", phi2="g", S1="A")
    assert t.conclusion not in t.hypotheses
    assert inclus(var("A"), var("B")) in set(t.hypotheses)


# ════════════════════════════════════════════════════════════════════════════
#  INVARIANT — theorie_ensembles() reste = 22.
# ════════════════════════════════════════════════════════════════════════════
def test_theorie_inchangee_22():
    """theorie_ensembles reste à 22 axiomes (rien postulé ; réutilise du CLOS)."""
    U.coincidence_univ()
    assert len(E.theorie_ensembles().axiomes) == 22
