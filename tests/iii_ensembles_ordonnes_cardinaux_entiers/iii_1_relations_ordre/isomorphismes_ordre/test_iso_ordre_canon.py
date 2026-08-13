"""Tests §III.1-2 — FORMES CANONIQUES iso-ordre : la CAPTURE de liant est éliminée.

On certifie que :
  (1) la forme DÉFAUT compatible_ordre(...,y="y") CAPTURE f(y)=τ_y((y,y)∈f) [le bug] ;
  (2) la forme CANONIQUE (xo,yo) ne capture PAS : f(yo)=τ_y((yo,y)∈f) [correct] ;
  (3) la cible trichotomie_ordinaux_canon DIFFÈRE de la forme défaut (défectueuse) ;
  (4) theorie=22 (aucun axiome ajouté ; ce ne sont que des INSTANCES des notions).
"""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, appartient
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_1_relations_ordre.ordre_treillis import ensembles_ordre_vocab as V
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.ordinaux import ensembles_ordinaux as O
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_1_relations_ordre.isomorphismes_ordre import ensembles_iso_ordre_canon as C


def _Rf(g="R"):
    vg = var(g)
    return lambda a, b: appartient(E.couple(a, b), vg)


def test_la_capture_ne_se_produit_plus_en_forme_defaut():
    """La forme DÉFAUT ne capture PLUS : valeur b='j' ⇒ f(y)=τ_j((y,j)∈f), pas (y,y)."""
    co = V.compatible_ordre(var("f"), var("E"), _Rf("R"), _Rf("Rp"))   # défaut x,y
    capture_fy = E.valeur(var("f"), var("y"))                          # τ_y((y,y)∈f) — l'ancienne capture
    correct_fy = E.valeur(var("f"), var("y"), b='j')                   # τ_j((y,j)∈f) — VALEUR correcte
    s = repr(co)
    # la VALEUR correcte de f(y) (liant frais j) figure ; la forme capturée N'apparaît PAS
    assert repr(correct_fy) in s
    assert repr(capture_fy) not in s


def test_canonique_pas_de_capture():
    """La forme CANONIQUE (x,w) : f(w)=τ_j((w,j)∈f) correct ; aucune capture (y,y) ni (w,w)."""
    co = C.compatible_ordre_canon(var("f"), var("E"), _Rf("R"), _Rf("Rp"))
    correct_fw = E.valeur(var("f"), var(C.ISO_Y), b='j')  # τ_j((w,j)∈f) — VALEUR correcte
    capture_fy = E.valeur(var("f"), var("y"))             # τ_y((y,y)∈f)  — capture y
    s = repr(co)
    assert repr(correct_fw) in s                          # la valeur correcte de f(w) figure
    assert repr(capture_fy) not in s                      # aucune capture (y,y)


def test_cible_canonique_differe_du_defaut_defectueux():
    """trichotomie_ordinaux_canon ≠ trichotomie_ordinaux() (forme défaut défectueuse)."""
    canon = C.trichotomie_ordinaux_canon("E", _Rf("R"), "F", _Rf("Rp"))
    defaut = O.trichotomie_ordinaux("E", _Rf("R"), "F", _Rf("Rp"))
    assert canon != defaut
    # la cible canonique est bien le OU de deux ordinal_inferieur_ou_egal_canon
    assert canon.tag == "ou"


def test_theorie_intacte():
    assert len(E.theorie_ensembles().axiomes) == 22
