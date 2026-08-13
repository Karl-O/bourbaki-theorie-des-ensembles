"""§II.4.8 — LA FAMILLE DES FIBRES (X_y)_{y∈F} de f : E → F  (P1-P2 de S3).

Pour f : E → F, la fibre en y est  X_y := f⁻¹⟨{y}⟩ = image(reciproque(f), {y}) ;
la FAMILLE des fibres est le graphe-terme (C54, liant EXOTIQUE « yfb »)

    Xfib := graphe_terme( F , image(reciproque(f), {yfb}) , "yfb" ).

PALIERS CERTIFIÉS (un test chacun) :
  P1a famille_fibres_fonctionnelle          ⊢ est_fonctionnel(Xfib)      [CLOS]
  P1b famille_fibres_valeur   {i0∈F}        ⊢ Xfib(i0) = f⁻¹⟨{i0}⟩       [1 hyp]
  P1c fam_fibre_egale  (au TERME, motif _inst_gen + pont HF)
      Γ⊢t∈F  ⟹  Γ∪{HF} ⊢ valeur_famille(Xfib, t) = f⁻¹⟨{t}⟩
  P2  membre_fibre_de_sa_valeur {dom f=E, x∈E} ⊢ x ∈ f⁻¹⟨{f(x)}⟩
      (chaque point est dans SA fibre — la clef du sens direct de S3 ;
       PAS besoin de « f fonctionnel » : couple_valeur_dans_graphe suffit.)

HYPOTHÈSES HONNÊTES DU CHANTIER (formules partagées par les modules S3) :
  Hf1 := est_fonctionnel(f)                  (« f est une fonction »)
  Hf2 := dom f = E                           (« définie sur E »)
  Hf3 := (∀xfh)(xfh∈E ⇒ f(xfh)∈F)            (« à valeurs dans F »)
  HF  := (∀yfh)(yfh∈F ⇒ valeur_famille(Xfib,yfh) = valeur(Xfib,yfh))
         — le PONT fam↔valeur pour la famille concrète des fibres : instance
         minimale du mur « fam » (précédent HW/HN, ensembles_factorielle_def2_rec).

LIANTS EXOTIQUES du chantier (aucun ne heurte la machinerie traversée
{x,y,z,u,v,up,w,p,q,i,d0}) : yfb (C54 famille), i0fb (point-valeur), xfb0 (P2),
xfh/yfh (liants des hypothèses), wfb (trou Leibniz).  Défauts des paramètres :
f="ffb", e="Efb", b="Ffb" — « Ffb » (PAS « F ») pour ne jamais heurter le liant
∃F de equipotent/cardinal.  theorie_ensembles()==22 ; rien postulé.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, et, impl, appartient, pourtout, subst_f)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, equivalence_arriere, instancie)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
    composer_egalites)
from bourbaki.ii_theorie_des_ensembles.ii_2_couples.ii_2_1_definition_couples.ensembles_couples import (
    singleton_membre)
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_2_reciproque.ensembles_reciproque import (
    couple_reciproque)
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_4_fonctions.ensembles_valeur_codomaine import (
    couple_valeur_dans_graphe)

YB = "yfb"     # liant C54 de la famille des fibres — EXOTIQUE


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def _dech(res, *premisses):
    """Décharge en chaîne : pour chaque prémisse-théorème p (dont la conclusion
    est une hypothèse ASSUMÉE de res), loi de déduction puis modus ponens."""
    for p in premisses:
        res = N.modus_ponens(p, N.loi_deduction(p.conclusion, res))
    return res


# ── Termes ────────────────────────────────────────────────────────────────────
def fibre(f, y):
    """X_y := f⁻¹⟨{y}⟩ = image(reciproque(f), {y})   (la fibre de f en y)."""
    return E.image(E.reciproque(_t(f)), E.singleton(_t(y)))


def terme_fibre(f="ffb"):
    """Le terme-valeur y ↦ f⁻¹⟨{y}⟩ de la famille (liant exotique yfb, libre)."""
    return fibre(f, var(YB))


# @livre Ch.II §4.8 Def.8 | E II.30 L.1-3 | PDF p.81
#   (la famille (X_ι)_{ι∈I} dont on prend la somme — ICI la famille des fibres
#    de f, indexée par le but F ; graphe-terme C54, liant exotique yfb.)
def famille_fibres(f="ffb", b="Ffb"):
    """Xfib := graphe_terme(F, f⁻¹⟨{yfb}⟩, "yfb")   (la famille des fibres de f)."""
    return E.graphe_terme(_t(b), terme_fibre(f), YB)


def somme_fibres(f="ffb", b="Ffb"):
    """⊔_{y∈F} f⁻¹⟨{y}⟩ := somme_famille(Xfib, F)   (la CIBLE de S3)."""
    return E.somme_famille(famille_fibres(f, b), _t(b))


# ── Les hypothèses honnêtes du chantier ───────────────────────────────────────
def hypothese_fonctionnelle(f="ffb"):
    """Hf1 := est_fonctionnel(f)."""
    return E.est_fonctionnel(_t(f))


def hypothese_domaine(f="ffb", e="Efb"):
    """Hf2 := (dom f = E)."""
    return egal(E.dom(_t(f)), _t(e))


def hypothese_valeurs(f="ffb", e="Efb", b="Ffb"):
    """Hf3 := (∀xfh)((xfh∈E) ⇒ (f(xfh)∈F))   (liant exotique xfh)."""
    vx = var("xfh")
    return pourtout("xfh", impl(appartient(vx, _t(e)),
                                appartient(E.valeur(_t(f), vx), _t(b))))


def hypothese_pont_fam(f="ffb", b="Ffb"):
    """HF := (∀yfh)((yfh∈F) ⇒ (valeur_famille(Xfib,yfh) = valeur(Xfib,yfh))).

    Pont fam↔valeur pour la famille CONCRÈTE des fibres (improuvable : « fam »
    est un symbole libre de l'encodage — cf. le mur documenté de T1c)."""
    X = famille_fibres(f, b)
    vy = var("yfh")
    return pourtout("yfh", impl(appartient(vy, _t(b)),
                                egal(E.valeur_famille(X, vy), E.valeur(X, vy))))


# ── P1a : la famille est fonctionnelle (C54) ──────────────────────────────────
def famille_fibres_fonctionnelle(f="ffb", b="Ffb"):
    """P1a ⊢ est_fonctionnel(Xfib)                                    [CLOS]."""
    from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_6_fonction_terme.ensembles_fonction_terme import (
        graphe_terme_fonctionnel)
    res = graphe_terme_fonctionnel(_t(b), terme_fibre(f), YB, "y")
    assert res.conclusion == E.est_fonctionnel(famille_fibres(f, b)), "P1a : forme"
    assert res.est_clos, "P1a : non clos"
    return res


# ── P1b : la valeur de la famille en un NOM i0 ────────────────────────────────
def famille_fibres_valeur(i0="i0fb", f="ffb", b="Ffb"):
    """P1b {i0∈F} ⊢ Xfib(i0) = f⁻¹⟨{i0}⟩                       [1 hyp ; i0 NOM].

    graphe_terme_valeur (nom-basée) sur le terme-valeur τ-LÉGER f⁻¹⟨{y}⟩ (terme
    app pur, sans τ) ; pour un TERME, passer par fam_fibre_egale (_inst_gen)."""
    assert isinstance(i0, str), "famille_fibres_valeur : i0 doit être un NOM"
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.cantor.ensembles_cantor import (
        graphe_terme_valeur)
    res = graphe_terme_valeur(_t(b), terme_fibre(f), i0, YB)
    cible = egal(E.valeur(famille_fibres(f, b), var(i0)), fibre(f, var(i0)))
    assert res.conclusion == cible, "P1b : ≠ Xfib(i0)=fibre(i0)"
    assert res.hypotheses == frozenset({appartient(var(i0), _t(b))}), "P1b : hyps"
    return res


# ── P1c : la valeur_famille au TERME (pont HF + _inst_gen) ────────────────────
def fam_fibre_egale(thm_in_F, tt, f="ffb", b="Ffb"):
    """Γ ⊢ t∈F  ⟹  Γ∪{HF} ⊢ valeur_famille(Xfib, t) = f⁻¹⟨{t}⟩.   (t TERME.)

    (α) HF instanciée en t : fam(Xfib,t) = valeur(Xfib,t) ;
    (β) P1b ∀-close sur le nom i0fb puis instanciée en t (motif _inst_gen —
        l'hypothèse i0fb∈F est déchargée AVANT la ∀-clôture) : valeur = fibre ;
    (γ) composition.  t ne doit pas contenir i0fb/yfh libres (exotiques)."""
    vb = _t(b)
    X = famille_fibres(f, b)
    hf = N.assume(hypothese_pont_fam(f, b))
    fam_eq = N.modus_ponens(thm_in_F, instancie(hf, tt))       # fam(X,t)=valeur(X,t)
    imp = N.loi_deduction(appartient(var("i0fb"), vb),
                          famille_fibres_valeur("i0fb", f, b))  # clos : (i0∈F)⇒(val=fibre)
    val_imp = instancie(N.generalisation("i0fb", imp), tt)
    val_eq = N.modus_ponens(thm_in_F, val_imp)                 # valeur(X,t)=fibre(t)
    res = composer_egalites(fam_eq, val_eq)
    assert res.conclusion == egal(E.valeur_famille(X, tt), fibre(f, tt)), "P1c : forme"
    return res


# ── P2 : chaque point est dans SA fibre ───────────────────────────────────────
# @livre Ch.II §3.4 Lem.- | E II.13 L.24-33 | PDF p.64
#   (lemme de plomberie : (x, f(x))∈f pour x∈dom f — transporté dans la fibre
#    via le graphe réciproque et l'axiome de l'image ; sert la Rem. E II.30.)
def membre_fibre_de_sa_valeur(x0="xfb0", f="ffb", e="Efb"):
    """P2 {dom f = E, x∈E} ⊢ x ∈ f⁻¹⟨{f(x)}⟩.   (x : nom exotique ou terme
    sans « x », « p », « q », « y » libres.)

    (x, f(x)) ∈ f  [couple_valeur_dans_graphe, sans fonctionnalité] ;
    (f(x), x) ∈ f⁻¹ [couple_reciproque] ;  f(x) ∈ {f(x)}  [singleton_membre] ;
    témoin x:=f(x) dans AXIOME_IMAGE (G:=f⁻¹, X:={f(x)}, y:=x)."""
    vf, ve, vx = _t(f), _t(e), _t(x0)
    fx = E.valeur(vf, vx)
    Sfx = E.singleton(fx)
    cpl_in = couple_valeur_dans_graphe(vf, ve, vx)         # {dom f=E, x∈E} ⊢ (x,f(x))∈f
    cr = couple_reciproque(vf, fx, vx)                     # ((f(x),x)∈f⁻¹) ⇔ ((x,f(x))∈f)
    in_recip = N.modus_ponens(cpl_in, equivalence_arriere(cr))     # (f(x),x)∈f⁻¹
    fx_in_s = N.modus_ponens(N.reflexivite(fx),
        equivalence_arriere(singleton_membre(fx, fx)))     # f(x) ∈ {f(x)}
    ax_img = N.axiome(E.theorie_ensembles(), E.AXIOME_IMAGE)
    img_car = instancie(instancie(instancie(ax_img, E.reciproque(vf)), Sfx), vx)
    corps = et(appartient(var("x"), Sfx),
               appartient(E.couple(var("x"), vx), E.reciproque(vf)))
    wit = conjonction_intro(fx_in_s, in_recip)
    assert wit.conclusion == subst_f(fx, "x", corps), "P2 : témoin ≠ (f(x)|x)corps"
    ex = N.modus_ponens(wit, N.s5(corps, fx, "x"))         # (∃x)corps
    res = N.modus_ponens(ex, equivalence_arriere(img_car)) # x ∈ f⁻¹⟨{f(x)}⟩
    assert res.conclusion == appartient(vx, fibre(f, fx)), "P2 : forme"
    assert res.hypotheses == frozenset({hypothese_domaine(f, e),
                                        appartient(vx, ve)}), "P2 : hyps"
    return res


__all__ = ["YB", "fibre", "terme_fibre", "famille_fibres", "somme_fibres",
           "hypothese_fonctionnelle", "hypothese_domaine", "hypothese_valeurs",
           "hypothese_pont_fam", "famille_fibres_fonctionnelle",
           "famille_fibres_valeur", "fam_fibre_egale", "membre_fibre_de_sa_valeur",
           "_t", "_dech"]
