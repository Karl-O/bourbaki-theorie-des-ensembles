"""Tests §III.1-2 — FORMES CANONIQUES iso-ordre : la CAPTURE de liant est éliminée.

On certifie que :
  (1) la forme DÉFAUT compatible_ordre(...,y="y") CAPTURE f(y)=τ_y((y,y)∈f) [le bug] ;
  (2) la forme CANONIQUE (xo,yo) ne capture PAS : f(yo)=τ_y((yo,y)∈f) [correct] ;
  (3) la cible trichotomie_ordinaux_canon DIFFÈRE de la forme défaut (défectueuse) ;
  (4) theorie=22 (aucun axiome ajouté ; ce ne sont que des INSTANCES des notions).
"""
from bourbaki.logique.formule import var, appartient
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.ordre import ensembles_ordre_vocab as V
from bourbaki.ordre import ensembles_ordinaux as O
from bourbaki.ordre import ensembles_iso_ordre_canon as C


def _Rf(g="R"):
    vg = var(g)
    return lambda a, b: appartient(E.couple(a, b), vg)


def test_la_capture_existe_en_forme_defaut():
    """La forme DÉFAUT est bien défectueuse : f(y) = τ_y((y,y)∈f) y apparaît capturé."""
    co = V.compatible_ordre(var("f"), var("E"), _Rf("R"), _Rf("Rp"))   # défaut x,y
    capture_fy = E.valeur(var("f"), var("y"))                          # τ_y((y,y)∈f)
    # la valeur capturée (point fixe) apparaît dans la forme défaut
    assert repr(capture_fy) in repr(co)


def test_canonique_pas_de_capture():
    """La forme CANONIQUE (x,w) : f(w)=τ_y((w,y)∈f) correct ; la capture ABSENTE."""
    co = C.compatible_ordre_canon(var("f"), var("E"), _Rf("R"), _Rf("Rp"))
    correct_fw = E.valeur(var("f"), var(C.ISO_Y))  # τ_y((w,y)∈f) — VALEUR correcte
    capture_fy = E.valeur(var("f"), var("y"))      # τ_y((y,y)∈f)  — la capture
    s = repr(co)
    assert repr(correct_fw) in s                   # la valeur correcte de f(w) figure
    assert repr(capture_fy) not in s               # la forme capturée N'apparaît PAS


def test_cible_canonique_differe_du_defaut_defectueux():
    """trichotomie_ordinaux_canon ≠ trichotomie_ordinaux() (forme défaut défectueuse)."""
    canon = C.trichotomie_ordinaux_canon("E", _Rf("R"), "F", _Rf("Rp"))
    defaut = O.trichotomie_ordinaux("E", _Rf("R"), "F", _Rf("Rp"))
    assert canon != defaut
    # la cible canonique est bien le OU de deux ordinal_inferieur_ou_egal_canon
    assert canon.tag == "ou"


def test_theorie_intacte():
    assert len(E.theorie_ensembles().axiomes) == 22
