"""Tests §III.1 & §III.7 — notions résiduelles : cofinal/coinitial, parties
filtrantes, ensemble ordonné filtrant, systèmes relatifs à un I filtrant, images
réciproque / directe d'un système.

Vérifie : (a) chaque NOTION s'introduit (prédicat/terme clos bien formé, VERBATIM) ;
(b) les lemmes DIRECTS certifient EXACTEMENT la cible (décompositions, instances) ;
(c) theorie_ensembles() reste INCHANGÉE à 22 axiomes (rien n'y est ajouté).
"""
from bourbaki.logique.formule import (
    Formule, var, app, egal, appartient, et, ou, impl, non, pourtout, existe, inclus,
)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.ensembles.familles.iii_7_limites import ensembles_limites as L
from bourbaki.ordre.iii_7_limites import ensembles_cofinal as C


def _R():
    return lambda u, v: appartient(E.couple(u, v), var("G"))


def _leq():
    return lambda u, v: appartient(E.couple(u, v), var("Gleq"))


# ════════════════════════════════════════════════════════════════════════════
#  III.1 — cofinal / coinitial dans un ensemble ordonné
# ════════════════════════════════════════════════════════════════════════════
def test_cofinale_dans_forme():
    """est_cofinale_dans = (A⊂E) et est_cofinale(R,A,E) — conjonction VERBATIM."""
    R = _R()
    f = C.est_cofinale_dans(R, "A", "E")
    attendu = et(inclus(var("A"), var("E")), E.est_cofinale(R, var("A"), var("E")))
    assert f == attendu
    assert isinstance(f, Formule)


def test_coinitiale_dans_forme():
    R = _R()
    f = C.est_coinitiale_dans(R, "A", "E")
    attendu = et(inclus(var("A"), var("E")), E.est_coinitiale(R, var("A"), var("E")))
    assert f == attendu


def test_cofinale_dans_inclusion_lemme():
    """{A cofinale DANS E} ⊢ A⊂E (projection gauche)."""
    th = C.cofinale_dans_inclusion(_R(), "A", "E")
    assert th.conclusion == inclus(var("A"), var("E"))
    assert C.est_cofinale_dans(_R(), "A", "E") in th.hypotheses


def test_cofinale_dans_condition_lemme():
    """{A cofinale DANS E} ⊢ condition de cofinalité (projection droite)."""
    R = _R()
    th = C.cofinale_dans_condition(R, "A", "E")
    assert th.conclusion == E.est_cofinale(R, var("A"), var("E"))
    assert C.est_cofinale_dans(R, "A", "E") in th.hypotheses


# ════════════════════════════════════════════════════════════════════════════
#  III.1 — parties filtrantes
# ════════════════════════════════════════════════════════════════════════════
def test_partie_filtrante_droite_forme():
    """A⊂E et (∀x,y∈A)(∃z∈A)(x≤z et y≤z) — majorant DANS A (ordre induit)."""
    R = _R()
    f = C.est_partie_filtrante_droite(R, "A", "E")
    vA, vx, vy, vz = var("A"), var("x"), var("y"), var("z")
    cœur = pourtout("x", pourtout("y",
        impl(et(appartient(vx, vA), appartient(vy, vA)),
             existe("z", et(et(appartient(vz, vA), R(vx, vz)), R(vy, vz))))))
    assert f == et(inclus(vA, var("E")), cœur)


def test_partie_filtrante_gauche_forme():
    R = _R()
    f = C.est_partie_filtrante_gauche(R, "A", "E")
    vA, vx, vy, vz = var("A"), var("x"), var("y"), var("z")
    cœur = pourtout("x", pourtout("y",
        impl(et(appartient(vx, vA), appartient(vy, vA)),
             existe("z", et(et(appartient(vz, vA), R(vz, vx)), R(vz, vy))))))
    assert f == et(inclus(vA, var("E")), cœur)


def test_partie_filtrante_droite_inclusion_lemme():
    """{A partie filtrante à droite de E} ⊢ A⊂E."""
    th = C.partie_filtrante_droite_inclusion(_R(), "A", "E")
    assert th.conclusion == inclus(var("A"), var("E"))


# ════════════════════════════════════════════════════════════════════════════
#  III.1 — ensemble préordonné / ordonné filtrant
# ════════════════════════════════════════════════════════════════════════════
def test_est_filtrant_forme():
    """est_filtrant = (filtrant à droite OU filtrant à gauche)."""
    R = _R()
    f = C.est_filtrant(R, "E")
    attendu = ou(E.est_filtrant_droite(R, var("E")),
                 E.est_filtrant_gauche(R, var("E")))
    assert f == attendu


def test_ensemble_ordonne_filtrant_droite_forme():
    """est_ensemble_ordonne_filtrant_droite = (ordre dans E) et (filtrant à droite)."""
    R = _R()
    f = C.est_ensemble_ordonne_filtrant_droite(R, "E")
    attendu = et(E.est_relation_ordre_dans(R, var("E")),
                 E.est_filtrant_droite(R, var("E")))
    assert f == attendu


def test_ensemble_ordonne_filtrant_gauche_forme():
    R = _R()
    f = C.est_ensemble_ordonne_filtrant_gauche(R, "E")
    attendu = et(E.est_relation_ordre_dans(R, var("E")),
                 E.est_filtrant_gauche(R, var("E")))
    assert f == attendu


def test_ordonne_filtrant_droite_decompositions():
    """{E ordonné filtrant à droite} ⊢ ordre dans E (gauche) ET filtrant (droite)."""
    R = _R()
    th_ordre = C.ensemble_ordonne_filtrant_droite_est_ordre(R, "E")
    assert th_ordre.conclusion == E.est_relation_ordre_dans(R, var("E"))
    th_filt = C.ensemble_ordonne_filtrant_droite_est_filtrant(R, "E")
    assert th_filt.conclusion == E.est_filtrant_droite(R, var("E"))


def test_filtrant_inclusion_forme():
    """(X_α) filtrante pour ⊂ : (∀α,β∈A)(∃γ∈A)(X_α⊂X_γ et X_β⊂X_γ)  (Lemme 1)."""
    f = C.est_filtrant_inclusion("X", "A")
    va, vb, vg = var("a"), var("b"), var("g")
    Xa = E.valeur_famille(var("X"), va)
    Xb = E.valeur_famille(var("X"), vb)
    Xg = E.valeur_famille(var("X"), vg)
    attendu = pourtout("a", pourtout("b",
        impl(et(appartient(va, var("A")), appartient(vb, var("A"))),
             existe("g", et(et(appartient(vg, var("A")), inclus(Xa, Xg)),
                            inclus(Xb, Xg))))))
    assert f == attendu


# ════════════════════════════════════════════════════════════════════════════
#  III.7 — systèmes relatifs à un I filtrant
# ════════════════════════════════════════════════════════════════════════════
def test_systeme_projectif_filtrant_forme():
    """sys. projectif filtrant = (I filtrant à droite) et (système projectif)."""
    leq = _leq()
    f = C.est_systeme_projectif_filtrant("f", leq, "I")
    attendu = et(E.est_filtrant_droite(leq, var("I"), "x", "y", "z"),
                 L.est_systeme_projectif(var("f"), leq, var("I"), "a", "b", "g", "x"))
    assert f == attendu


def test_systeme_projectif_filtrant_decompositions():
    """{sys. proj. filtrant} ⊢ I filtrant (gauche) ET système projectif (droite)."""
    leq = _leq()
    th_filt = C.systeme_projectif_filtrant_indices_filtrants("f", leq, "I")
    assert th_filt.conclusion == E.est_filtrant_droite(leq, var("I"), "x", "y", "z")
    th_sys = C.systeme_projectif_filtrant_est_systeme("f", leq, "I")
    assert th_sys.conclusion == L.est_systeme_projectif(
        var("f"), leq, var("I"), "a", "b", "g", "x")


def test_systeme_inductif_filtrant_alias():
    """sys. inductif filtrant = est_systeme_inductif (qui exige déjà I filtrant)."""
    leq = _leq()
    f = C.est_systeme_inductif_filtrant("f", leq, "I")
    assert f == L.est_systeme_inductif(var("f"), leq, var("I"), "a", "b", "g", "x")


# ════════════════════════════════════════════════════════════════════════════
#  III.7.2 — image réciproque d'un système (Prop. 2)
# ════════════════════════════════════════════════════════════════════════════
def test_image_reciproque_indice_forme():
    """(u_α)^{-1}(x'_α) = u_α^{-1}⟨{x'_α}⟩ = image(reciproque(u_α), {pr_α x'})."""
    t = C.image_reciproque_indice("u", "a", "xp")
    ua = app("u_indice", var("u"), var("a"))
    xpa = E.projection_indice(var("xp"), var("a"))
    attendu = E.image(E.reciproque(ua), E.singleton(xpa))
    assert t == attendu


def test_systeme_image_reciproque_caracterisation():
    """est_systeme_image_reciproque = (∀α)(M_α = (u_α)^{-1}(x'_α))."""
    f = C.est_systeme_image_reciproque("M", "u", "xp")
    va = var("a")
    Ma = app("M_indice", var("M"), va)
    attendu = pourtout("a", egal(Ma, C.image_reciproque_indice("u", va, "xp")))
    assert f == attendu


def test_image_reciproque_indice_composante_lemme():
    """{(M_α)=sys.img.récip de x' par (u_α)} ⊢ M_α = (u_α)^{-1}(x'_α)."""
    th = C.image_reciproque_indice_composante("u", "a", "xp")
    va = var("a")
    M = C.systeme_image_reciproque(var("u"), var("xp"))
    Ma = app("M_indice", M, va)
    attendu = egal(Ma, C.image_reciproque_indice(var("u"), va, var("xp")))
    assert th.conclusion == attendu


# ════════════════════════════════════════════════════════════════════════════
#  III.7.6 — image directe d'un système (dual)
# ════════════════════════════════════════════════════════════════════════════
def test_image_directe_indice_forme():
    """u_α⟨M_α⟩ = image(u_α, M_α)."""
    t = C.image_directe_indice("u", "a", "M")
    ua = app("u_indice", var("u"), var("a"))
    Ma = app("M_indice", var("M"), var("a"))
    assert t == E.image(ua, Ma)


def test_systeme_image_directe_caracterisation():
    """est_systeme_image_directe = (∀α)(M'_α = u_α⟨M_α⟩)."""
    f = C.est_systeme_image_directe("Mp", "u", "M")
    va = var("a")
    Mpa = app("M_indice", var("Mp"), va)
    attendu = pourtout("a", egal(Mpa, C.image_directe_indice("u", va, "M")))
    assert f == attendu


def test_image_directe_indice_composante_lemme():
    th = C.image_directe_indice_composante("u", "a", "M")
    va = var("a")
    Mp = C.systeme_image_directe(var("u"), var("M"))
    Mpa = app("M_indice", Mp, va)
    attendu = egal(Mpa, C.image_directe_indice(var("u"), va, var("M")))
    assert th.conclusion == attendu


# ════════════════════════════════════════════════════════════════════════════
#  INTANGIBILITÉ : theorie_ensembles reste à 22 axiomes
# ════════════════════════════════════════════════════════════════════════════
def test_theorie_ensembles_inchangee_22():
    """Aucune notion de ce module n'ajoute d'axiome à theorie_ensembles (= 22)."""
    assert len(E.theorie_ensembles().axiomes) == 22


def test_reportes_non_vide():
    """Les théorèmes durs sont nommés et explicitement REPORTÉS (honnêteté)."""
    assert isinstance(C.REPORTES, list) and len(C.REPORTES) >= 5
    assert all(isinstance(s, str) for s in C.REPORTES)
