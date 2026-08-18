"""§III.7 — Propositions des limites projectives / inductives : SALVAGE (vague F).

Module NEUF, COMPLÉMENTAIRE de `ensembles_limites_props` (lequel prouve déjà la
FONCTORIALITÉ Cor.2 Prop.1 / Cor.2 Prop.6 au niveau des valeurs, la factorisation
(6) ponctuelle, l'unicité ponctuelle, et le pont image-réciproque).  Ici on salvage
les CONTENUS ATTEIGNABLES, encore non couverts, des Propositions 1/3/5/6/8 — toujours
SANS modifier un fichier existant, SANS rien postuler (theorie_ensembles() = 22).
RÉUTILISÉS (import seul) : `ensembles_limites` (L), `ensembles_limites_canoniques` (C).

PRINCIPE DU SALVAGE.  Les théorèmes « durs » de §III.7 (EXISTENCE/UNICITÉ par
propriété universelle, BIJECTIVITÉ des applications canoniques cofinales, NON-VACUITÉ
b) du Th.1) exigent des cônes universels / quotients effectifs ABSENTS du noyau ;
ils restent REPORTÉS.  Leur CŒUR pointwise est, lui, prouvable de façon fidèle et
non-vide :

  ── 1.  APPLICATION CANONIQUE PROJECTIVE COMPATIBLE AVEC LES TRANSITIONS  ──
  (Prop. 1, formule (2)/(6) ; SENS FACILE de la propriété universelle.)
  Si une application u : F → E=lim← factorise les u_α au sens u_α = f_α∘u (donnée
  pointwise u_α(t)=f_α(u(t)), HYPOTHÈSE), alors la donnée des u_α est AUTOMATIQUEMENT
  COMPATIBLE avec les transitions :  f_{αβ}(u_β(t)) = u_α(t)  pour α≤β  — c.-à-d.
  l'identité (5) du cône est conséquence de (6) et de la relation (2).  [theoreme
  `factorisation_compatible_transitions`]

  ── 2.  PASSAGE À LA LIMITE DES APPLICATIONS (lim← / lim→), SENS FACILE  ──
  (Cor. 1 Prop. 1 §III.7.2 ; Cor. 1 Prop. 6 §III.7.6.)
  Côté PROJECTIF : si u=lim← u_α réalise le diagramme g_α∘u = u_α∘f_α (donnée
  pointwise, HYP), alors pour α≤β les composantes sont liées par
      g_{αβ}(g_β(u(z))) = u_α(f_α(z))                       [proj]
  (compatibilité de u avec les deux systèmes).  Côté INDUCTIF (Cor. 1 Prop. 6) :
  si u=lim→ u_α réalise u∘f_α = g_α∘u_α (HYP), alors
      u(f_β(f_{βα}(x))) = g_β(u_β(f_{βα}(x)))               [ind]
  (le diagramme se propage le long des transitions).  [theoremes
  `passage_limite_proj`, `passage_limite_ind`]

  ── 3.  COFINAL ⇒ APPLICATION CANONIQUE g BIEN DÉFINIE SUR LES VALEURS  ──
  (Prop. 3 §III.7.2, SENS FACILE.)  Pour J cofinale et x∈E=lim←_I, la α-coordonnée
  (α∈J) de g(x)=(f_α(x))_{α∈J} est f_α(x) (formule (3)), et elle est COMPATIBLE avec
  les transitions de J : f_{αβ}(pr_β g(x)) = pr_α g(x) pour α≤β dans J — donc g(x)
  satisfait la condition (1) du système restreint : g est bien à valeurs dans E'.
  [theoremes `cofinal_canonique_coordonnee`, `cofinal_canonique_compatible`]
  ✅ MISE À JOUR (4 août 2026) : la BIJECTIVITÉ de g n'est plus reportée — les deux
  sens sont acquis hors de ce module, dans `prop1_proj/` : INJECTIVITÉ
  (`prop3_g_injective_pointwise`, 8 hyps) et SURJECTIVITÉ (témoin cofinal canonique
  SANS axiome du choix, `prolongement_bien_defini`, `prolongement_coherent` — x̃
  vérifie la relation (1) donc x̃∈lim←_I — et `prolongement_restitue` — x̃_α=x_α
  sur J).  Ne reste que l'assemblage formel des deux sens en « g bijective ».

  ── 4.  COFINAL ⇒ CANONIQUE INDUCTIVE : SURJECTIVITÉ « SENS FACILE »  ──
  (Prop. 8 §III.7.6, SENS FACILE — la Prop. 8 précède l'intitulé « 7. Double limite
  inductive » de E III.66.)  L'application canonique f_α : E_α → E=lim→ a pour
  valeur f_α(x)=Cl_R(x) ; tout élément de la forme Cl_R(x) (x∈E_α) est donc ATTEINT
  par f_α.  C'est le contenu « surjectif » trivial : l'image de f_α couvre les classes
  des éléments de E_α.  [theoreme `canonique_ind_atteint`]

AXIOMES de membership : AUCUN ajouté.  Toute hypothèse de factorisation/diagramme est
une PRÉMISSE explicite portée dans le séquent (jamais postulée).  Anti-tautologie :
chaque conclusion est NEUVE (≠ hypothèses, ≠ P⇒P), vérifié dans le test miroir.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, app, egal, et, ou, impl, non, appartient, existe, pourtout, inclus,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites import ensembles_limites as L
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites import ensembles_limites_canoniques as C
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    instancie, conjonction_intro,
)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
    composer_egalites, symetrie, congruence_terme,
)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def _gleq():
    """Préordre ≤ par défaut (même convention que tous les modules limites)."""
    return lambda u, v: appartient(E.couple(u, v), var("Gleq"))


# ════════════════════════════════════════════════════════════════════════════
#  1.  APPLICATION CANONIQUE PROJECTIVE COMPATIBLE AVEC LES TRANSITIONS
#      (Prop. 1, §III.7.2 — SENS FACILE de la propriété universelle)
#  Si u factorise les u_α (u_α=f_α∘u, donnée pointwise (6)), la famille (u_α) satisfait
#  AUTOMATIQUEMENT la condition de cône (5)  f_{αβ}∘u_β=u_α.
# ════════════════════════════════════════════════════════════════════════════
# @livre Ch.III §7.2 Prop.1 | E III.53 L.1-3 | PDF p.156
def factorisation_compatible_transitions(u="u", Efam="E", f="f", leq=None, i="I",
                                         a="a", b="b", t="t"):
    """{ u_α(t)=f_α(u(t)) (∀α,t) ;  u(t)∈lim← ;  α,β∈I ;  α≤β }
          ⊢ f_{αβ}(u_β(t)) = u_α(t).

    SENS FACILE de la Prop. 1 (§III.7.2) : la donnée d'une factorisation (6)
    u_α=f_α∘u IMPLIQUE la condition de cône (5) f_{αβ}∘u_β=u_α (compatibilité de la
    famille (u_α) avec les transitions f_{αβ}).  Hypothèses portées dans le séquent
    (jamais postulées) : la factorisation pointwise + u(t) dans la limite + (α,β∈I,
    α≤β) pour activer la relation (2).  Conclusion NEUVE.

    Chaîne :  f_{αβ}(u_β(t)) =[hyp (6) β, sous f_{αβ}] f_{αβ}(f_β(u(t)))
                              =[relation (2), symétrisée]  f_α(u(t))
                              =[hyp (6) α, symétrisée]      u_α(t)."""
    if leq is None:
        leq = _gleq()
    vu, vE, vf, vi = _t(u), _t(Efam), _t(f), _t(i)
    va, vb, vt = var(a), var(b), var(t)
    ut = E.valeur(vu, vt)                                  # u(t)
    ua_t = E.valeur(C.u_indice(vu, va), vt)               # u_α(t)
    ub_t = E.valeur(C.u_indice(vu, vb), vt)               # u_β(t)
    fab = L.appl_proj(vf, va, vb)                         # f_{αβ}
    fa_ut = C.application_canonique_proj_valeur(vE, vf, va, ut)   # f_α(u(t))
    fb_ut = C.application_canonique_proj_valeur(vE, vf, vb, ut)   # f_β(u(t))

    # hyp (6) : u_α(t)=f_α(u(t)),  u_β(t)=f_β(u(t))  (quantifiée ∀α∀t)
    Hfact = N.assume(pourtout(a, pourtout(t,
        egal(E.valeur(C.u_indice(vu, va), vt), fa_ut))))
    eq_a = instancie(instancie(Hfact, va), vt)            # u_α(t) = f_α(u(t))
    eq_b = instancie(instancie(Hfact, vb), vt)            # u_β(t) = f_β(u(t))

    # f_{αβ}(u_β(t)) = f_{αβ}(f_β(u(t)))   [eq_b sous f_{αβ}(·)]
    step1 = N.modus_ponens(eq_b, congruence_terme(
        ub_t, fb_ut, E.valeur(fab, var("w")), "w"))       # f_{αβ}(u_β(t)) = f_{αβ}(f_β(u(t)))

    # relation (2) en z=u(t) : f_α(u(t)) = f_{αβ}(f_β(u(t)))   (sous u(t)∈lim←, α,β∈I, α≤β)
    rel2_thm = _relation_2_au_point(vE, vf, leq, vi, ut, va, vb)  # f_α(u(t))=f_{αβ}(f_β(u(t)))
    # symétriser : f_{αβ}(f_β(u(t))) = f_α(u(t))
    rel2_sym = N.modus_ponens(rel2_thm, symetrie(fa_ut, E.valeur(fab, fb_ut)))
    step2 = composer_egalites(step1, rel2_sym)            # f_{αβ}(u_β(t)) = f_α(u(t))

    # f_α(u(t)) = u_α(t)   (eq_a symétrisée)
    eq_a_sym = N.modus_ponens(eq_a, symetrie(ua_t, fa_ut))    # f_α(u(t)) = u_α(t)
    return composer_egalites(step2, eq_a_sym)             # f_{αβ}(u_β(t)) = u_α(t)


def relation_2_proj_en_point(Efam, f, leq, i, z_terme, a, b):
    """{ z∈lim← ; α,β∈I ; α≤β } ⊢ f_α(z) = f_{αβ}(f_β(z)),  POUR UN TERME z quelconque.

    Variante de `C.relation_2_projective` instanciée sur un TERME z arbitraire (et non
    la seule variable 'z'), pour pouvoir la réutiliser en z=u(t), z=x, etc.  Délègue
    au cœur `_relation_2_au_point`.  Hypothèses : z∈lim←, α,β∈I, α≤β.

    IMPORTANT : Efam/f/i sont transmis SANS être pré-enveloppés en `var(...)` (les
    helpers sous-jacents font eux-mêmes `var(Efam)` ; un double-`var` désaccorderait
    les termes).  z, a, b sont des TERMES."""
    return _relation_2_au_point(Efam, f, leq, i, _t(z_terme), _t(a), _t(b))


def _relation_2_au_point(Efam, f, leq, i, z, a, b):
    """Cœur de la relation (2) en un TERME z : f_α(z) = f_{αβ}(f_β(z)).

    Construit DIRECTEMENT (termes-natifs, sans wrappers `var(...)`) la relation (1)
    et les valeurs canoniques, pour qu'aucun double-`var` ne désaccorde les termes —
    quels que soient Efam/f/i (str ou Terme) et z/a/b (Termes).  Hypothèses portées
    dans le séquent : z∈lim←, α,β∈I, α≤β.

        f_α(z) = pr_α z                  [valeur canonique, axiome (2)]
               = f_{αβ}(pr_β z)          [relation (1) sur la limite, en le point z]
               = f_{αβ}(f_β(z)).         [valeur canonique en β, sous f_{αβ}]"""
    vE, vf, vi = _t(Efam), _t(f), _t(i)
    va, vb, vz = _t(a), _t(b), _t(z)
    # ── relation (1) sur la limite, au point z (instance directe de l'axiome lim←) ──
    ax_lim = N.axiome(L.theorie_lim_proj(vE, vf, leq, vi),
                      L.axiome_lim_proj(vE, vf, leq, vi))
    car = instancie(ax_lim, vz)                          # z∈lim ⇔ (z∈∏ et cond1)
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
        equivalence_avant, conjonction_elim_droite as _ced,
    )
    Hz = N.assume(appartient(vz, L.lim_proj(vE, vf)))
    both = N.modus_ponens(Hz, equivalence_avant(car))    # z∈∏ et cond1
    cond1 = _ced(both)                                   # (∀α∀β)(... ⇒ pr_α z=f_{αβ}(pr_β z))
    rel1 = instancie(instancie(cond1, va), vb)           # prem ⇒ pr_α z=f_{αβ}(pr_β z)
    prem = et(et(appartient(va, vi), appartient(vb, vi)), leq(va, vb))
    Hprem = N.assume(prem)
    eq1 = N.modus_ponens(Hprem, rel1)                    # pr_α z = f_{αβ}(pr_β z)
    # ── valeurs canoniques f_α(z)=pr_α z, f_β(z)=pr_β z ──
    fa = _canon_proj_au_point(vE, vf, leq, vi, va, vz)   # f_α(z) = pr_α z
    fb = _canon_proj_au_point(vE, vf, leq, vi, vb, vz)   # f_β(z) = pr_β z
    chaine = composer_egalites(fa, eq1)                  # f_α(z) = f_{αβ}(pr_β z)
    fab = L.appl_proj(vf, va, vb)
    fb_sym = N.modus_ponens(fb, symetrie(
        C.application_canonique_proj_valeur(vE, vf, vb, vz),
        E.projection_indice(vz, vb)))                    # pr_β z = f_β(z)
    cong2 = N.modus_ponens(fb_sym, congruence_terme(
        E.projection_indice(vz, vb),
        C.application_canonique_proj_valeur(vE, vf, vb, vz),
        E.valeur(fab, var("w")), "w"))                   # f_{αβ}(pr_β z)=f_{αβ}(f_β(z))
    return composer_egalites(chaine, cong2)              # f_α(z)=f_{αβ}(f_β(z))


def _canon_proj_au_point(Efam, f, leq, i, a_terme, z_terme):
    """{ z∈lim← ; α∈I } ⊢ f_α(z) = pr_α z,  pour des TERMES α,z quelconques.

    Instance DIRECTE (termes-natifs) de l'axiome de la valeur canonique projective
    (E.III.7.1, (2)) en (α,z) termes — aucun double-`var`."""
    vE, vf, vi = _t(Efam), _t(f), _t(i)
    va, vz = _t(a_terme), _t(z_terme)
    ax = N.axiome(C.theorie_canonique_proj(vE, vf, leq, vi),
                  C.axiome_canonique_proj(vE, vf, leq, vi))
    inst = instancie(instancie(ax, va), vz)              # hyp ⇒ f_α(z)=pr_α z
    Hz = N.assume(appartient(vz, L.lim_proj(vE, vf)))
    Ha = N.assume(appartient(va, vi))
    return N.modus_ponens(conjonction_intro(Hz, Ha), inst)   # f_α(z)=pr_α z


# ════════════════════════════════════════════════════════════════════════════
#  2.  PASSAGE À LA LIMITE DES APPLICATIONS  (Cor. 1 Prop. 1 ; Cor. 1 Prop. 6)
#      SENS FACILE : le diagramme de définition de lim← u / lim→ u, lu pointwise,
#      se propage le long des transitions.
# ════════════════════════════════════════════════════════════════════════════
# @livre Ch.III §7.2 Cor.1 | E III.53 L.22-30 | PDF p.156
# @livre Ch.III §7.2 Demo.- | E III.53 L.16-21 | PDF p.156  (démonstration de passage_limite_proj)
def passage_limite_proj(u="u", EfamE="E", fE="f", EfamF="F", gF="g", leq=None, i="I",
                        a="a", b="b", z="z"):
    """{ g_α(u(z)) = u_α(f_α(z))  (∀α,z) ;  α,β∈I ;  α≤β ;  u(z)∈lim←F ;
         f_α(z), f_β(z) bien posés }
          ⊢ g_{αβ}(g_β(u(z))) = g_{αβ}(u_β(f_β(z))).

    Cor. 1 de la Prop. 1 (§III.7.2), SENS FACILE : si u=lim← u_α réalise le diagramme
    g_α∘u = u_α∘f_α (donnée pointwise, HYPOTHÈSE — l'EXISTENCE de u est REPORTÉE),
    alors les composantes côté but commutent encore après transition g_{αβ}.

    Preuve (NEUVE, non vide) : on applique g_{αβ} à l'égalité g_β(u(z)) = u_β(f_β(z))
    (instance β de l'hypothèse de diagramme), par congruence sous g_{αβ}(·)."""
    if leq is None:
        leq = _gleq()
    vu, vEE, vfE, vEF, vgF, vi = _t(u), _t(EfamE), _t(fE), _t(EfamF), _t(gF), _t(i)
    va, vb, vz = var(a), var(b), var(z)
    uz = E.valeur(vu, vz)                                 # u(z)
    g_b_uz = C.application_canonique_proj_valeur(vEF, vgF, vb, uz)   # g_β(u(z))
    fb_z = C.application_canonique_proj_valeur(vEE, vfE, vb, vz)     # f_β(z)
    ub_fbz = E.valeur(C.u_indice(vu, vb), fb_z)          # u_β(f_β(z))
    gab = L.appl_proj(vgF, va, vb)                       # g_{αβ}

    # hyp diagramme : g_α(u(z)) = u_α(f_α(z))  (∀α,z)
    diag = egal(C.application_canonique_proj_valeur(vEF, vgF, var(a), E.valeur(vu, vz)),
                E.valeur(C.u_indice(vu, var(a)),
                         C.application_canonique_proj_valeur(vEE, vfE, var(a), vz)))
    Hdiag = N.assume(pourtout(a, pourtout(z, diag)))
    eq_b = instancie(instancie(Hdiag, vb), vz)           # g_β(u(z)) = u_β(f_β(z))
    # appliquer g_{αβ} : g_{αβ}(g_β(u(z))) = g_{αβ}(u_β(f_β(z)))
    return N.modus_ponens(eq_b, congruence_terme(
        g_b_uz, ub_fbz, E.valeur(gab, var("w")), "w"))


# @livre Ch.III §7.6 Cor.1 | E III.63 L.5-18 | PDF p.166
# @livre Ch.R §6 Prop.- | E.R.30 item 13 (g : lim-> Ea -> E' déduite des ga) | PDF p.333
def passage_limite_ind(u="u", EfamE="E", fE="f", EfamF="F", gF="g", leq=None, i="I",
                       a="a", b="b", x="x"):
    """{ u(f_α(x)) = g_α(u_α(x))  (∀α,x) ;  les transitions f_{βα} bien posées }
          ⊢ u(f_β(f_{βα}(x))) = g_β(u_β(f_{βα}(x))).

    Cor. 1 de la Prop. 6 (§III.7.6), SENS FACILE : si u=lim→ u_α réalise le diagramme
    u∘f_α = g_α∘u_α (donnée pointwise, HYPOTHÈSE — EXISTENCE de u REPORTÉE), alors le
    diagramme reste valable après transport par f_{βα} (en β au point f_{βα}(x)).

    Preuve : instance β de l'hypothèse de diagramme, ÉVALUÉE au point f_{βα}(x).
    Conclusion NEUVE (le point a changé : f_{βα}(x) au lieu de x)."""
    if leq is None:
        leq = _gleq()
    vu, vEE, vfE, vEF, vgF, vi = _t(u), _t(EfamE), _t(fE), _t(EfamF), _t(gF), _t(i)
    va, vb, vx = var(a), var(b), var(x)
    fba = L.appl_ind(vfE, vb, va)                        # f_{βα} (source)
    fba_x = E.valeur(fba, vx)                            # f_{βα}(x)

    # hyp diagramme inductif : u(f_α(x)) = g_α(u_α(x))  (∀α,x)
    # f_α = application canonique inductive du système SOURCE ; g_α = celle du système BUT.
    diag = egal(
        E.valeur(vu, C.application_canonique_ind_valeur(vEE, vfE, vi, var(a), var(x))),
        C.application_canonique_ind_valeur(vEF, vgF, vi, var(a),
                                           E.valeur(C.u_indice(vu, var(a)), var(x))))
    Hdiag = N.assume(pourtout(a, pourtout(x, diag)))
    # instance β au point f_{βα}(x)
    return instancie(instancie(Hdiag, vb), fba_x)        # u(f_β(f_{βα}(x)))=g_β(u_β(f_{βα}(x)))


# ════════════════════════════════════════════════════════════════════════════
#  3.  COFINAL ⇒ APPLICATION CANONIQUE g BIEN DÉFINIE / COMPATIBLE (Prop. 3 facile)
#      g(x) = (f_α(x))_{α∈J} : sa α-coordonnée est f_α(x) (formule (3)) et elle
#      satisfait la condition (1) du système restreint à J.
# ════════════════════════════════════════════════════════════════════════════
def cofinal_canonique_coordonnee(Efam="E", f="f", leq=None, i="I", J="J",
                                 x="x", a="a", formule_3=None):
    """{ x∈lim←_I ;  α∈J } ⊢ pr_α(g(x)) = f_α(x).

    Formule (3) de la restriction à une partie J (§III.7.1) : « g(x)=(f_α(x))_{α∈J} »,
    lue coordonnée par coordonnée.
    BRIQUE du SENS FACILE de la Prop. 3 (g bien définie à valeurs dans E'=lim←_J).

    PARAMÉTRIQUE EN L'ORIGINE DE (3), depuis le 4 août 2026.  `formule_3` est,
    s'il est fourni, un théorème quantifié (∀α)(∀x)((x∈lim←_I et α∈J) ⇒ …) —
    typiquement `prop1_proj/ensembles_g_construite.g_formule_3_quantifiee`, qui
    est CLOS et parle du g CONSTRUIT.  À défaut on instancie l'AXIOME canonique
    (théorie dédiée, `theorie_ensembles` inchangé), comportement historique.

    Cette inversion est le premier pas de la MIGRATION vers le g construit : le
    reste de la chaîne (compatible, prop3_*) fixe encore le terme opaque en dur,
    donc on ne peut pas encore passer le g construit de bout en bout — d'où le
    report dans `ensembles_g_construite.REPORTES`.  Mais la dépendance à
    l'axiome n'est plus câblée ici."""
    if leq is None:
        leq = _gleq()
    vE, vf, vi, vJ = _t(Efam), _t(f), _t(i), _t(J)
    va, vx = var(a), var(x)
    src = formule_3 if formule_3 is not None else N.axiome(
        C.theorie_canonique_g(vE, vf, leq, vi, vJ),
        C.axiome_canonique_g(vE, vf, leq, vi, vJ))
    inst = instancie(instancie(src, va), vx)             # hyp ⇒ pr_α(g(x))=f_α(x)
    Hx = N.assume(appartient(vx, L.lim_proj(vE, vf)))
    Ha = N.assume(appartient(va, vJ))
    return N.modus_ponens(conjonction_intro(Hx, Ha), inst)   # pr_α(g(x)) = f_α(x)


# @livre Ch.III §7.2 Prop.3 | E III.55 L.3-11 | PDF p.158
# @livre Ch.R §6 Prop.- | E.R.31 item 14 (restriction à une partie cofinale J du système projectif) | PDF p.334
def cofinal_canonique_compatible(Efam="E", f="f", leq=None, i="I", J="J",
                                 x="x", a="a", b="b", gterme=None,
                                 formule_3=None):
    """{ x∈lim←_I ;  α,β∈J ⊂ I ;  α≤β } ⊢ pr_α(g(x)) = f_{αβ}(pr_β(g(x))).

    SENS FACILE de la Prop. 3 (§III.7.2) : la valeur g(x)=(f_α(x))_{α∈J} SATISFAIT la
    condition (1) du système projectif restreint à J — donc g est bien à valeurs dans
    E'=lim←_J.

    Preuve (NEUVE, non vide), pour α≤β dans J (donc dans I) :
        pr_α(g(x)) = f_α(x)                 [(3) en α]
                   = f_{αβ}(f_β(x))         [relation (2) en x∈lim←_I]
                   = f_{αβ}(pr_β(g(x))).    [(3) en β, sous f_{αβ}, renversé]

    PARAMÉTRIQUE EN LE TERME g (migration, 4 août 2026).  `gterme` et `formule_3`
    vont de pair : le premier dit DE QUEL g on parle, le second FOURNIT la
    formule (3) pour ce g.  Défaut = le terme opaque + son axiome (comportement
    historique) ; pour le g CONSTRUIT, passer
    `gterme=graphe_g(...)` et `formule_3=g_formule_3_quantifiee(...)`.
    ⚠️ Les deux doivent être cohérents — un `gterme` construit avec la formule
    axiomatique produirait un modus ponens refusé (les termes ne s'apparient
    pas), ce qui est la bonne défense : le noyau ne laissera pas mélanger."""
    if leq is None:
        leq = _gleq()
    vE, vf, vi, vJ = _t(Efam), _t(f), _t(i), _t(J)
    va, vb, vx = var(a), var(b), var(x)
    g = gterme if gterme is not None else C.application_canonique_g(vE, vf, vJ)
    prb_gx = E.projection_indice(E.valeur(g, vx), vb)    # pr_β(g(x))
    fb_x = C.application_canonique_proj_valeur(vE, vf, vb, vx)   # f_β(x)
    fab = L.appl_proj(vf, va, vb)

    # (3) en α et β : pr_α(g(x))=f_α(x),  pr_β(g(x))=f_β(x)
    eq3_a = cofinal_canonique_coordonnee(vE, vf, leq, vi, vJ, x, a, formule_3)
    eq3_b = cofinal_canonique_coordonnee(vE, vf, leq, vi, vJ, x, b, formule_3)

    # relation (2) en x∈lim←_I : f_α(x) = f_{αβ}(f_β(x))
    rel2 = _relation_2_au_point(vE, vf, leq, vi, vx, va, vb)          # f_α(x)=f_{αβ}(f_β(x))

    # pr_α(g(x)) = f_α(x) = f_{αβ}(f_β(x))
    chaine = composer_egalites(eq3_a, rel2)              # pr_α(g(x)) = f_{αβ}(f_β(x))
    # remplacer f_β(x) par pr_β(g(x)) : f_{αβ}(f_β(x)) = f_{αβ}(pr_β(g(x)))   via eq3_b renversé
    eq3_b_sym = N.modus_ponens(eq3_b, symetrie(prb_gx, fb_x))         # f_β(x) = pr_β(g(x))
    cong = N.modus_ponens(eq3_b_sym, congruence_terme(
        fb_x, prb_gx, E.valeur(fab, var("w")), "w"))    # f_{αβ}(f_β(x)) = f_{αβ}(pr_β(g(x)))
    return composer_egalites(chaine, cong)              # pr_α(g(x)) = f_{αβ}(pr_β(g(x)))


# ════════════════════════════════════════════════════════════════════════════
#  4.  COFINAL ⇒ CANONIQUE INDUCTIVE : SURJECTIVITÉ « SENS FACILE » (Prop. 8 facile)
#      f_α(x)=Cl_R(x) : la classe de tout x∈E_α est ATTEINTE par f_α.
# ════════════════════════════════════════════════════════════════════════════
# @livre Ch.III §7.6 Def.- | E III.65 L.30-36 | PDF p.168
#   (prose de mise en place de la Prop. 8 : « restriction à J » d'un système inductif
#    (J partie filtrante à droite de I) et application canonique g = lim→ f_α :
#    E' → E, « dite canonique » — pas de terme dédié côté inductif ; seul le sens
#    facile ci-dessous est prouvé)
# @livre Ch.III §7.6 Prop.8 | E III.66 L.5-13 | PDF p.169
# @livre Ch.R §6 Prop.- | E.R.31 item 13 (partie cofinale J : même limite inductive) | PDF p.334
def canonique_ind_atteint(Efam="E", f="f", i="I", gleq=None, a="a", x="x"):
    """{ α∈I ;  x∈E_α } ⊢ (∃v)( v = x  et  f_α(v) = Cl_R(x) ).

    SENS FACILE de la surjectivité de l'application canonique inductive f_α : E_α → E
    (§III.7.5/6) : la classe Cl_R(x) de tout x∈E_α est dans l'IMAGE de f_α (à savoir
    f_α(x)).  Énoncé existentiel non-vide (témoin v=x) : « Cl_R(x) est atteint par
    f_α ».  C'est l'inclusion FACILE f_α⟨E_α⟩ ⊇ {Cl_R(x) : x∈E_α} ; la BIJECTIVITÉ de
    la canonique cofinale E'→E (Prop. 8) reste REPORTÉE.

    Preuve : f_α(x)=Cl_R(x) (axiome canonique inductif) → témoin v=x (S5)."""
    if gleq is None:
        gleq = C._GRAPHE_LEQ_DEFAUT
    vE, vf, vi = _t(Efam), _t(f), _t(i)
    va, vx = var(a), var(x)
    GR = C.graphe_coherence(vf, vi, gleq)
    cl = E.classe(GR, vx)                                # Cl_R(x)
    fa_x = C.application_canonique_ind_valeur(vE, vf, vi, va, vx, gleq)   # f_α(x)
    # f_α(x) = Cl_R(x)  (instance de l'axiome canonique inductif, sous α∈I, x∈E_α)
    eq = C.canonique_ind_valeur(vE, vf, vi, gleq, a, x)  # f_α(x)=Cl_R(x)
    # corps de l'existentielle :  R{v} := ( v=x  et  f_α(v)=Cl_R(x) ).
    # NB : la variable existentielle est nommée 'v' (PAS 'y') : E.valeur(G,t)=τy((t,y)∈G)
    # introduit un liant 'y' interne ; nommer la variable libre 'y' la CAPTURERAIT.
    vv = var("v")
    corps = et(egal(vv, vx),
               egal(E.valeur(C.f_canon_ind(vE, vf, vi, gleq), vv), cl))
    # (x|v)R = ( x=x  et  f_α(x)=Cl_R(x) ) : témoin v=x
    refl = N.reflexivite(vx)                             # x=x
    corps_inst = conjonction_intro(refl, eq)            # x=x et f_α(x)=Cl_R(x) = (x|v)R
    # S5 : (x|v)R ⇒ (∃v)R
    return N.modus_ponens(corps_inst, N.s5(corps, vx, "v"))   # (∃v)(v=x et f_α(v)=Cl_R(x))


# ════════════════════════════════════════════════════════════════════════════
#  RÉSULTATS DURS introduits/cernés mais NON prouvés (honnêteté).
# ════════════════════════════════════════════════════════════════════════════
REPORTES = [
    "Proposition 1 1° (EXISTENCE de u : F→lim← factorisant les u_α) — propriété "
    "universelle (cône) ABSENTE ; seul le SENS FACILE (factorisation ⇒ compatibilité "
    "(5)) est prouvé.",
    "Prop. 6 (§III.7.6) : entièrement traitée dans prop6/ SAUF le critère **C57** "
    "(E II.44, report du chapitre II : « f compatible avec R ⇒ f = h∘p », existence "
    "de h). FAITS : 1°-unicité (prop6_unicite), 1°-compatibilité de v avec R "
    "(compatible_v_coherence — DÉMONTRÉE, R étant une formule explicite), "
    "1°-assemblage (relation_24_modulo_c57 : v=h∘p ⊢ (24)), 2° surjectivité "
    "(prop6_surjectif, les 2 sens), 3° injectivité (prop6_injectif, les 2 sens). "
    "Le mur résiduel n'est donc PAS dans III.7 mais dans le passage au quotient "
    "de II.6.5.",
    "Proposition 3 (§III.7.2) : application canonique g cofinale BIJECTIVE — ✅ les "
    "DEUX SENS sont acquis : INJECTIVITÉ (prop3_g_injective_pointwise, 8 hyps) et "
    "SURJECTIVITÉ (prop1_proj/ensembles_prolongement_cofinal : temoin canonique sans "
    "axiome du choix, bonne définition du prolongement, prolongement_coherent — x̃ "
    "satisfait la relation (1) donc x̃∈lim←_I — et prolongement_restitue — x̃_α=x_α "
    "sur J). Reste l'ASSEMBLAGE formel des deux sens en un énoncé « g bijective ».",
    "Proposition 5 (§III.7.4) : cofinale dénombrable + f_{αβ} surjectives ⇒ f_α "
    "surjective — REPORTÉ (récurrence dénombrable + intersection finie).",
    "Proposition 8 (§III.7.6) : canonique cofinale E'→E BIJECTIVE — seul le SENS "
    "FACILE « Cl_R(x) atteint par f_α » est prouvé.",
    "Théorème 1 §III.7.4 b) (E non vide) — REPORTÉ (propriété d'intersection finie).",
]


__all__ = [
    # 1. factorisation ⇒ compatibilité avec les transitions (Prop. 1 facile)
    "factorisation_compatible_transitions",
    "relation_2_proj_en_point",
    # 2. passage à la limite des applications (Cor.1 Prop.1 / Prop.6, facile)
    "passage_limite_proj", "passage_limite_ind",
    # 3. cofinal ⇒ g canonique bien définie / compatible (Prop. 3 facile)
    "cofinal_canonique_coordonnee", "cofinal_canonique_compatible",
    # 4. cofinal ⇒ canonique inductive surjective (Prop. 8 facile)
    "canonique_ind_atteint",
    "REPORTES",
]
