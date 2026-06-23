"""§III.4 — LE TRANSPORT ORDINAL↔CARDINAL : `clause_plus_petit(≤_induit,[0,a])` et
`bon_ordre_intervalle_ordinal(a)` = `est_bien_ordonne(≤_induit,[0,a])`, le GATE ℕ.

────────────────────────────────────────────────────────────────────────────────
LA CIBLE.  L'arc ℕ se réduit (ensembles_ordinal_cardinal_correspondance,
cardinaux_bien_ordonnes_de_bon_ordre — CLOS) au BON ORDRE de l'intervalle [0,a] :

    bon_ordre_intervalle(a) = est_bien_ordonne( ≤_induit , [0,a] )
        = est_relation_ordre_dans(≤_induit,[0,a])   [CLOS : relation_ordre_dans_intervalle]
          et clause_plus_petit(≤_induit,[0,a]).      [LE seul report : la CLAUSE]

La partie ORDRE est ENTIÈREMENT ACQUISE (transitivité via inf_egal_transitive,
ANTISYMÉTRIE via Cantor–Bernstein, réflexivités).  La SEULE pièce restante est la
CLAUSE DE PLUS PETIT ÉLÉMENT :

    clause_plus_petit(≤,[0,a]) =
        (∀S)( ( S⊂[0,a] et S≠∅ ) ⇒ (∃m)( m∈S et (∀x)(x∈S ⇒ m≤x) ) ).

────────────────────────────────────────────────────────────────────────────────
LE TRANSPORT (Bourbaki) — la ROUTE ORDINALE (PAS le hyp_surjection mort).

On bien ordonne le SET a (zermelo → bo(Ro,a)).  Les ordinaux ≤ ord(a) sont les
SEGMENTS INITIAUX seg(a,Ro,t)=]←,t[ indexés par t∈a (ensembles_segments_construction).
La machinerie ordinale CLOSE `ordinaux_bien_ordonnes(a,Ro,T)` donne, pour tout
ensemble NON VIDE T⊂a d'indices, un segment seg(a,Ro,t0) ⊆-MINIMAL :
   (∃m)( m∈T et (∀x)(x∈T ⇒ seg(a,Ro,m) ⊂ seg(a,Ro,x)) ).
La MONOTONIE cardinale par inclusion (inf_egal_card_de_inclus, CLOS) transporte
seg(m)⊂seg(x) en  Card(seg m) ≤ Card(seg x).

────────────────────────────────────────────────────────────────────────────────
CE QUE CE MODULE LIVRE (salvage gradué, honnête, theorie=22) — ✅ CLOS :

  • iso_reflexif_seg_preuve : ⊢ sont_isomorphes_ordre(seg m, seg m, Ro, Ro)
    (l'ISO IDENTITÉ Δ_seg, REPORT de ensembles_ordinaux_bien_ordonnes RÉSOLU).
    Lève ordinaux_bien_ordonnes à la forme LITTÉRALE ordinal_inferieur_ou_egal.

  • card_seg_monotone : { bo(Ro,a) } ⊢ ( seg(a,Ro,m)⊂seg(a,Ro,x) ⇒
       Card(seg(a,Ro,m)) ≤ Card(seg(a,Ro,x)) ).  La MONOTONIE ⊂ ⇒ ≤ des cardinaux
       de segments.  INCONDITIONNELLE (inf_egal_card_de_inclus, transport Card).

  • plus_petit_card_segment : { bo(Ro,a), T⊂a, T≠∅ } ⊢
       (∃m)( m∈T et (∀x)( x∈T ⇒ Card(seg(a,Ro,m)) ≤ Card(seg(a,Ro,x)) ) ).
       Le ⊆-MIN de ordinaux_bien_ordonnes TRANSPORTÉ par Card en ≤-MIN des cardinaux
       de segments.  Le NOYAU du transport — DÉRIVÉ INCONDITIONNELLEMENT.

  • clause_min_intervalle_de_pullback : { bo(Ro,a), T⊂a, T≠∅, into, onto } ⊢ la
       CLAUSE de plus petit élément pour S (témoin µ=Card(seg m)).  Le transport du
       ⊆-min de segment au ≤-MIN de S, modulo les 2 hypothèses de RÉALISATION.

  • 🎯🎯 bon_ordre_intervalle_ordinal(a) : { hyp_transport_ordinal(a) } ⊢
       bon_ordre_intervalle(a)  (== la cible déposée, LITTÉRALEMENT, 1 seule hyp).
       Assemble la PARTIE ORDRE (relation_ordre_dans_intervalle, CLOSE) et la CLAUSE
       (par S, via le transport), élimine le ∃Ro de Zermelo.

────────────────────────────────────────────────────────────────────────────────
⚠️ LE GAP EXACT RESTANT — UNE SEULE hypothèse `hyp_transport_ordinal(a)` (honnête,
   isolée, JAMAIS postulée) :

     (∃Ro)( est_bien_ordonne(Ro,a)              [Zermelo — CLOS]
            et (∀S)( (S⊂[0,a] et S≠∅) ⇒ ( pullback(a,Ro,S)⊂a et ≠∅
                       et (∀t∈pullback) Card(seg t)∈S          [pullback into S]
                       et (∀c∈S)(∃x∈pullback) c=Card(seg x) ) ) ).  [S réalisé]

   Les 4 propriétés du pullback {t∈a:Card(seg(a,Ro,t))∈S} sont la RÉALISATION
   (collectivisation S8 du pullback + SURJECTIVITÉ « tout cardinal ≤a = Card d'un
   segment initial »), le DERNIER maillon ordinal↔cardinal non encore construit.
   Tout le reste (⊆-min ordinal, monotonie cardinale ⊂⇒≤, iso identité, transport,
   élimination ∃Ro, partie ordre) est CLOS.

INVARIANT : theorie_ensembles() = 22.  Rien postulé : la cible est DÉRIVÉE de l'unique
hypothèse hyp_transport_ordinal, la monotonie + l'iso identité + le ⊆-min ordinal +
le transport étant CLOS.  NE MODIFIE AUCUN fichier existant.
"""
from __future__ import annotations

from bourbaki.logique.formule import (
    Terme, var, egal, et, non, impl, appartient, existe, pourtout, inclus,
)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.ordre.iii_1_relations_ordre.ordre_treillis import ensembles_ordre_vocab as V
from bourbaki.logique.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_transitivite, instancie,
)
from bourbaki.logique.tactiques.tactiques_abrege_quantif import existe_elimination
from bourbaki.cardinaux.ensembles_equipotence import (
    diagonale_injective, diagonale_image, diagonale_valeur,
)
from bourbaki.cardinaux.ensembles_cardinaux import inf_egal_card, cardinal
from bourbaki.cardinaux.ensembles_clause_plus_petit_monotonie import (
    inf_egal_card_de_inclus_terme,
)
from bourbaki.cardinaux.ensembles_segments_construction import seg, _R_de
from bourbaki.cardinaux.ensembles_ordinaux_bien_ordonnes import ordinaux_bien_ordonnes


def _t(t):
    return t if isinstance(t, Terme) else var(t)


# Trou de substitution FRAIS pour ce module (≠ x,w,y,j des valeurs/binders d'ordre).
_HOLE = "hole_boio"


def _sym(a, b, h_ab):
    """De ⊢ a=b [h_ab] déduit ⊢ b=a  (S6 avec un trou FRAIS, sûr même si a/b contient « w »)."""
    eq = N.modus_ponens(h_ab, N.s6(a, b, _HOLE, egal(var(_HOLE), a)))   # (a=a) ⇔ (b=a)
    return N.modus_ponens(N.reflexivite(a), equivalence_avant_local(eq))


def _trans(a, b, c, h_ab, h_bc):
    """De ⊢ a=b [h_ab] et ⊢ b=c [h_bc] déduit ⊢ a=c  (S6, trou FRAIS)."""
    eq = N.modus_ponens(h_bc, N.s6(b, c, _HOLE, egal(a, var(_HOLE))))   # (a=b) ⇔ (a=c)
    return N.modus_ponens(h_ab, equivalence_avant_local(eq))


def equivalence_avant_local(thm_equiv):
    from bourbaki.logique.tactiques.tactiques_abrege2 import equivalence_avant
    return equivalence_avant(thm_equiv)


# ════════════════════════════════════════════════════════════════════════════
#  PIÈCE 1 — l'ISO IDENTITÉ Δ_seg : sont_isomorphes_ordre(seg m, seg m, Ro, Ro).
#  RÉSOUT le report `iso_reflexif_seg` de ensembles_ordinaux_bien_ordonnes.
# ════════════════════════════════════════════════════════════════════════════
# binders d'ordre CANONIQUES de iso_reflexif_seg / ordinal_inferieur_ou_egal.
_LIT_X = "x"
_LIT_Y = "w"
_LIT_F = "fseg"


def _diag_bij(Sm):
    """⊢ est_bijective(Δ_Sm, Sm, Sm)  pour un TERME Sm.

    Δ_Sm injective sur Sm (diagonale_injective) et surjective (diagonale_image :
    image(Δ_Sm,Sm)=Sm).  Lemmes diagonale généralisés sur leur paramètre X puis
    instanciés au TERME Sm."""
    inj = instancie(N.generalisation("Xseg", diagonale_injective("Xseg")), Sm)
    img = instancie(N.generalisation("Xseg", diagonale_image("Xseg")), Sm)
    return conjonction_intro(inj, img)


def _diag_valeur_imp():
    """⊢ (u ∈ Xseg) ⇒ Δ_Xseg(u) = u   (diagonale_valeur, hyp déchargée, généralisable)."""
    dv = diagonale_valeur("Xseg", "useg")             # {useg∈Xseg} ⊢ Δ_Xseg(useg)=useg
    imp = N.loi_deduction(appartient(var("useg"), var("Xseg")), dv)
    return N.generalisation("Xseg", N.generalisation("useg", imp))


def _diag_valeur_at(DVG, Sm, vu):
    """De _diag_valeur_imp [DVG] déduit ⊢ (vu ∈ Sm) ⇒ Δ_Sm(vu)=vu  (valeur binder « y »)."""
    return instancie(instancie(DVG, Sm), vu)


def iso_reflexif_seg_preuve(Ro="Ro", o="o", m="m"):
    """⊢ sont_isomorphes_ordre( seg(o,Ro,m), seg(o,Ro,m), Ro, Ro ).

    🎯 L'ISO IDENTITÉ — la RÉFLEXIVITÉ de l'ordre des ordinaux, RÉSOUT le report
    `iso_reflexif_seg` de ensembles_ordinaux_bien_ordonnes (qui n'en livrait que
    l'ÉNONCÉ).  Le graphe diagonale Δ_(seg m) est une bijection de seg m sur seg m
    (diagonale_injective + diagonale_image) ET order-compatible : pour x,y∈seg m,
    Δ(x)=x et Δ(y)=y (diagonale_valeur), donc R{Δx,Δy} se réécrit (Leibniz) en
    R{x,y} et la clause devient R{x,y} ⇔ R{x,y}, VRAIE.

    Subtilité de binders : compatible_ordre utilise valeur(·,·,b='j') tandis que
    diagonale_valeur produit valeur(·,·) (binder « y ») ; on raccorde par alpha_tau
    (α-renommage τ du noyau, CS1).  INCONDITIONNEL, theorie=22, témoin Δ CONSTRUIT.

    Conclusion == iso_reflexif_seg(Ro,o,m,f='fseg') (binders canoniques x,w,fseg)."""
    Rf = _R_de(Ro)
    Sm = seg(Ro, o, _t(m))
    DE = E.diagonale(Sm)
    LX, LY, LF = _LIT_X, _LIT_Y, _LIT_F
    vx, vy = var(LX), var(LY)

    bij = _diag_bij(Sm)                                # est_bijective(Δ_Sm,Sm,Sm)
    DVG = _diag_valeur_imp()

    # valeurs avec b='j' (forme de compatible_ordre) et défaut b='y' (de diagonale_valeur)
    fxj, fyj = E.valeur(DE, vx, b="j"), E.valeur(DE, vy, b="j")
    fxy, fyy = E.valeur(DE, vx), E.valeur(DE, vy)
    # raccord α-τ : fxy = fxj  et  fyy = fyj  (τ-renommage du liant « y » → « j »)
    atx = N.alpha_tau(fxy.args[0], "y", "j")          # ⊢ fxy = fxj
    aty = N.alpha_tau(fyy.args[0], "y", "j")          # ⊢ fyy = fyj

    hyp = et(appartient(vx, Sm), appartient(vy, Sm))
    h = N.assume(hyp)
    x_in = conjonction_elim_gauche(h)
    y_in = conjonction_elim_droite(h)
    dvx = N.modus_ponens(x_in, _diag_valeur_at(DVG, Sm, vx))   # fxy = x
    dvy = N.modus_ponens(y_in, _diag_valeur_at(DVG, Sm, vy))   # fyy = y

    # fxj = x  via  fxj = fxy (sym atx) puis fxy = x (dvx)  [trous FRAIS ≠ « w »]
    sym_atx = _sym(fxy, fxj, atx)                            # fxj = fxy
    fxj_x = _trans(fxj, fxy, vx, sym_atx, dvx)               # fxj = x
    sym_aty = _sym(fyy, fyj, aty)                            # fyj = fyy
    fyj_y = _trans(fyj, fyy, vy, sym_aty, dvy)              # fyj = y

    # x=fxj, y=fyj  (symétries) pour Leibniz vers R{fxj,fyj}
    x_eq_fxj = _sym(fxj, vx, fxj_x)                          # x = fxj
    y_eq_fyj = _sym(fyj, vy, fyj_y)                          # y = fyj
    leib1 = N.modus_ponens(x_eq_fxj, N.s6(vx, fxj, "wq", Rf(var("wq"), vy)))   # R{x,y}⇔R{fxj,y}
    leib2 = N.modus_ponens(y_eq_fyj, N.s6(vy, fyj, "wq", Rf(fxj, var("wq")))) # R{fxj,y}⇔R{fxj,fyj}
    compat_eq = equivalence_transitivite(leib1, leib2)       # R{x,y} ⇔ R{fxj,fyj}
    compat_inner = N.loi_deduction(hyp, compat_eq)
    compat = N.generalisation(LX, N.generalisation(LY, compat_inner))
    assert compat.conclusion == V.compatible_ordre(DE, Sm, Rf, Rf, LX, LY), \
        "compatibilité ≠ compatible_ordre canonique"

    iso_body = conjonction_intro(bij, compat)                # est_isomorphisme_ordre(Δ,…)
    assert iso_body.conclusion == V.est_isomorphisme_ordre(DE, Sm, Sm, Rf, Rf, LX, LY)
    corps = V.est_isomorphisme_ordre(var(LF), Sm, Sm, Rf, Rf, LX, LY)
    res = N.modus_ponens(iso_body, N.s5(corps, DE, LF))      # (∃f) est_iso = sont_isomorphes_ordre
    assert res.conclusion == iso_reflexif_seg_cible(Ro, o, m), \
        "conclusion ≠ sont_isomorphes_ordre(seg m, seg m, Ro, Ro)"
    return res


def iso_reflexif_seg_cible(Ro="Ro", o="o", m="m"):
    """ÉNONCÉ-cible (test miroir) de iso_reflexif_seg_preuve :
        sont_isomorphes_ordre( seg(o,Ro,m), seg(o,Ro,m), Ro, Ro )  (binders x,w,fseg)."""
    Rf = _R_de(Ro)
    Sm = seg(Ro, o, _t(m))
    return V.sont_isomorphes_ordre(Sm, Sm, Rf, Rf, _LIT_F, _LIT_X, _LIT_Y)


# ════════════════════════════════════════════════════════════════════════════
#  PIÈCE 2 — MONOTONIE CARDINALE des segments :  seg⊂seg ⇒ Card seg ≤ Card seg.
# ════════════════════════════════════════════════════════════════════════════
def card_seg_monotone(Ro="Ro", o="o", m="m", x="x"):
    """⊢ ( seg(o,Ro,m) ⊂ seg(o,Ro,x) )  ⇒  Card(seg(o,Ro,m)) ≤ Card(seg(o,Ro,x)).

    🎯 MONOTONIE ⊂ ⇒ ≤ des cardinaux de segments — INCONDITIONNELLE.  inf_egal_card_
    de_inclus_terme (diagonale Δ injecte le sous-ensemble) donne seg(m)≤seg(x) au
    niveau des ENSEMBLES ; on transporte par Card (inf_egal_transporte_cardinal) aux
    termes seg(m), seg(x).  Le contenu de « segment plus petit ⇒ cardinal ≤ ».

    NON vacueux : la conclusion Card·≤Card· n'est pas l'hypothèse seg⊂seg.  theorie=22."""
    Sm = seg(Ro, o, _t(m))
    Sx = seg(Ro, o, _t(x))
    Hsub = N.assume(inclus(Sm, Sx))                           # seg(m) ⊂ seg(x)
    le_ens = N.modus_ponens(Hsub, inf_egal_card_de_inclus_terme(Sm, Sx))   # seg(m) ≤ seg(x)
    transp = _transporte_card(Sm, Sx)                         # (seg(m)≤seg(x)) ⇒ Card·≤Card·
    le_card = N.modus_ponens(le_ens, transp)                  # Card(seg m) ≤ Card(seg x)
    return N.loi_deduction(inclus(Sm, Sx), le_card)


def _transporte_card(tU, tV):
    """⊢ ( U ≤ V ) ⇒ ( Card U ≤ Card V )  aux TERMES U,V  (inf_egal_transporte_cardinal)."""
    from bourbaki.cardinaux.arithmetique.ensembles_arith_cardinale_props_exposant_monotone import (
        inf_egal_transporte_cardinal,
    )
    gen = N.generalisation("Xtc", N.generalisation("Ytc",
        inf_egal_transporte_cardinal("Xtc", "Ytc")))
    return instancie(instancie(gen, _t(tU)), _t(tV))


# ════════════════════════════════════════════════════════════════════════════
#  PIÈCE 3 (NOYAU) — le ⊆-MIN ordinal TRANSPORTÉ en ≤-MIN des cardinaux de segments.
#  ordinaux_bien_ordonnes donne le segment ⊆-minimal ; card_seg_monotone le pousse
#  au niveau Card.  C'est le ≤-min de {Card(seg(a,Ro,t)) | t∈T}.
# ════════════════════════════════════════════════════════════════════════════
def plus_petit_card_segment(Ro="Ro", a="a", T="T", m="ms", x="xs"):
    """⊢ { est_bien_ordonne(Ro, a),  T ⊂ a,  T ≠ ∅ }
            ⊢ (∃m)( m∈T  et  (∀x)( x∈T ⇒ Card(seg(a,Ro,m)) ≤ Card(seg(a,Ro,x)) ) ).

    🎯 LE NOYAU DU TRANSPORT.  ordinaux_bien_ordonnes (CLOS) fournit l'indice m∈T dont
    le segment seg(a,Ro,m) est ⊆-MINIMAL : (∀x∈T) seg(m)⊂seg(x).  card_seg_monotone
    (CLOS) transporte chaque inclusion en Card(seg m) ≤ Card(seg x).  Donc Card(seg m)
    est le ≤-MIN des cardinaux {Card(seg x) | x∈T}, indexé par m∈T.

    DÉRIVÉ INCONDITIONNELLEMENT du SEUL bon ordre de (a,Ro) (+ T⊂a, T≠∅).  NON vacueux :
    le ⊆-min ordinal ET la monotonie cardinale sont RÉELLEMENT consommés.  theorie=22.

    REMARQUE.  Ceci est le ≤-min de l'ensemble {Card(seg t)|t∈T} ; pour CLORE
    clause_plus_petit sur un S⊂[0,a] arbitraire il reste à RÉALISER S = {Card(seg t)|t∈T}
    (réalisation + pullback), isolé dans bon_ordre_intervalle_ordinal."""
    Rf = _R_de(Ro)
    va, vT = _t(a), _t(T)
    mn = m if isinstance(m, str) else m.nom
    xn = x if isinstance(x, str) else x.nom
    vm, vx = var(mn), var(xn)
    Sm, Sx = seg(Ro, a, vm), seg(Ro, a, vx)
    cSm, cSx = cardinal(Sm), cardinal(Sx)

    # ── ⊆-min ordinal : (∃m)( m∈T et (∀x)(x∈T ⇒ seg(m)⊂seg(x)) )  [bo, T⊂a, T≠∅]
    obo = ordinaux_bien_ordonnes(a, Ro, T, mn, xn)
    # ── per-témoin m : transporter seg(m)⊂seg(x) en Card(seg m) ≤ Card(seg x)
    corps_seg = et(appartient(vm, vT),
                   pourtout(xn, impl(appartient(vx, vT), inclus(Sm, Sx))))
    Hwit = N.assume(corps_seg)
    m_in_T = conjonction_elim_gauche(Hwit)                   # m∈T
    body_seg = conjonction_elim_droite(Hwit)                 # (∀x)(x∈T ⇒ seg(m)⊂seg(x))
    # per-x : x∈T ⊢ Card(seg m) ≤ Card(seg x)
    Hx = N.assume(appartient(vx, vT))                        # x∈T
    incl_mx = N.modus_ponens(Hx, instancie(body_seg, vx))    # seg(m) ⊂ seg(x)
    mono = card_seg_monotone(Ro, a, vm, vx)                  # seg(m)⊂seg(x) ⇒ Card·≤Card·
    le_card = N.modus_ponens(incl_mx, mono)                  # Card(seg m) ≤ Card(seg x)
    body_card_x = N.loi_deduction(appartient(vx, vT), le_card)   # x∈T ⇒ Card·≤Card·
    body_card = N.generalisation(xn, body_card_x)            # (∀x)(x∈T ⇒ Card·≤Card·)
    corps_card = conjonction_intro(m_in_T, body_card)        # m∈T et (∀x∈T)Card·≤Card·
    # ── introduire (∃m) [binder ms]
    body_r = et(appartient(var(mn), vT),
        pourtout(xn, impl(appartient(vx, vT), inf_egal_card(cardinal(seg(Ro, a, var(mn))), cSx))))
    but = existe(mn, body_r)
    ex = N.modus_ponens(corps_card, N.s5(body_r, vm, mn))    # but  [Hwit]
    wit_imp = N.loi_deduction(corps_seg, ex)                 # corps_seg ⇒ but
    ex_imp = existe_elimination(wit_imp, mn)                 # (∃m)corps_seg ⇒ but
    res = N.modus_ponens(obo, ex_imp)                        # but  [bo, T⊂a, T≠∅]
    assert res.conclusion == plus_petit_card_segment_cible(Ro, a, T, mn, xn), \
        "conclusion ≠ ≤-min des cardinaux de segments"
    return res


def plus_petit_card_segment_cible(Ro="Ro", a="a", T="T", m="ms", x="xs"):
    """ÉNONCÉ-cible (test miroir) de plus_petit_card_segment :
        (∃m)( m∈T et (∀x)( x∈T ⇒ Card(seg(a,Ro,m)) ≤ Card(seg(a,Ro,x)) ) )."""
    vT = _t(T)
    vm, vx = var(m), var(x)
    return existe(m, et(appartient(vm, vT),
        pourtout(x, impl(appartient(vx, vT),
                         inf_egal_card(cardinal(seg(Ro, a, vm)), cardinal(seg(Ro, a, vx)))))))


# ════════════════════════════════════════════════════════════════════════════
#  PIÈCE 4 — DU ⊆-MIN DE SEGMENT AU ≤-MIN d'un S⊂[0,a] : le PULLBACK.
#
#  plus_petit_card_segment donne un m∈T dont Card(seg m) ≤-minore {Card(seg x)|x∈T}.
#  Avec les hypothèses de RÉALISATION (le SEUL gap ordinal↔cardinal restant) :
#     (H1)  Card(seg(a,Ro,m)) ∈ S          [le min de segment EST dans S]
#     (H2)  (∀c)( c∈S ⇒ (∃x)( x∈T et c = Card(seg(a,Ro,x)) ) )   [S réalisé par T]
#  on transporte le ≤-min de segment en ≤-min de S.  μ:=Card(seg m) ; pour c∈S, (H2)
#  donne x∈T avec c=Card(seg x), et Card(seg m)≤Card(seg x)=c.  μ∈S (H1) ⇒ μ∈[0,a].
# ════════════════════════════════════════════════════════════════════════════
def clause_min_intervalle_de_pullback(Ro="Ro", a="a", S="S", T="T",
                                      m="ms", x="xs", c="cc"):
    """⊢ { est_bien_ordonne(Ro, a),  T ⊂ a,  T ≠ ∅,
           hyp_realisation_min(Ro,a,S,T),  hyp_realisation_onto(Ro,a,S,T) }
            ⊢ (∃μ)( μ∈S et (∀c)( c∈S ⇒ R_induit{μ,c} ) )   [= la clause, témoin µ∈S].

    🎯 LE TRANSPORT DU ≤-MIN : du ⊆-min de segment (plus_petit_card_segment, CLOS) au
    ≤-MIN de S⊂[0,a].  Soit m∈T le ⊆-min : (∀x∈T) Card(seg m)≤Card(seg x).  Pose
    µ := Card(seg(a,Ro,m)).  Par hyp_realisation_min, µ∈S.  Pour tout c∈S,
    hyp_realisation_onto donne x∈T avec c=Card(seg x) ; du min, µ=Card(seg m)≤Card(seg x)=c,
    donc µ≤c ; et µ,c∈S⊂[0,a].  Donc R_induit{µ,c}=((µ≤c et µ∈[0,a]) et c∈[0,a]).

    Les 2 hypothèses de RÉALISATION sont l'UNIQUE gap ordinal↔cardinal restant (pullback
    S↦T réalisé), isolées explicitement, JAMAIS postulées.  Le reste — ⊆-min, monotonie,
    transport — est CLOS.  theorie=22, conclusion ≠ aucune hypothèse."""
    from bourbaki.cardinaux.ensembles_ordinal_cardinal_correspondance import (
        ordre_induit_intervalle, intervalle_0a,
    )
    Rf = _R_de(Ro)
    va, vS, vT = _t(a), _t(S), _t(T)
    mn = m if isinstance(m, str) else m.nom
    xn = x if isinstance(x, str) else x.nom
    cn = c if isinstance(c, str) else c.nom
    vm, vx, vc = var(mn), var(xn), var(cn)
    interv = intervalle_0a(a)
    Rind = ordre_induit_intervalle(a)
    mu = lambda tm: cardinal(seg(Ro, a, tm))                  # µ(t) := Card(seg(a,Ro,t))

    # ── le ⊆-min de segment, transporté en ≤-min des Card(seg) : (∃m)(m∈T et (∀x∈T)…)
    pp = plus_petit_card_segment(Ro, a, T, mn, xn)            # [bo, T⊂a, T≠∅]

    # ── per-témoin m : corps_min = m∈T et (∀x)(x∈T ⇒ Card(seg m)≤Card(seg x))
    corps_min = et(appartient(vm, vT),
        pourtout(xn, impl(appartient(vx, vT), inf_egal_card(mu(vm), mu(vx)))))
    Hwit = N.assume(corps_min)
    m_in_T = conjonction_elim_gauche(Hwit)                  # m∈T
    min_le = conjonction_elim_droite(Hwit)                   # (∀x)(x∈T ⇒ Card(seg m)≤Card(seg x))
    vmu = mu(vm)                                             # µ := Card(seg m)

    # ── µ∈S  via hyp_realisation_min UNIVERSEL : (∀t)(t∈T ⇒ Card(seg t)∈S), instancié à m
    H_min = N.assume(hyp_realisation_min(Ro, a, S, T))      # (∀t)(t∈T ⇒ Card(seg t)∈S)
    mu_in_S = N.modus_ponens(m_in_T, instancie(H_min, vm))  # µ∈S
    mu_in_interv = N.modus_ponens(mu_in_S, _inclus_S_interv(a, S, vmu))  # µ∈[0,a]   (S⊂[0,a])

    # ── per-c : c∈S ⊢ R_induit{µ,c}
    Hc = N.assume(appartient(vc, vS))                       # c∈S
    c_in_interv = N.modus_ponens(Hc, _inclus_S_interv(a, S, vc))  # c∈[0,a]
    # hyp_realisation_onto : (∀c)(c∈S ⇒ (∃x)(x∈T et c=Card(seg x)))
    H_onto = N.assume(hyp_realisation_onto(Ro, a, S, T, c, x))
    ex_x = N.modus_ponens(Hc, instancie(H_onto, vc))        # (∃x)(x∈T et c=Card(seg x))
    # éliminer ∃x : per-x, (x∈T et c=Card(seg x)) ⊢ µ≤c
    corps_x = et(appartient(vx, vT), egal(vc, mu(vx)))
    Hx = N.assume(corps_x)
    x_in_T = conjonction_elim_gauche(Hx)                    # x∈T
    c_eq = conjonction_elim_droite(Hx)                      # c = Card(seg x)
    mu_le_segx = N.modus_ponens(x_in_T, instancie(min_le, vx))   # µ ≤ Card(seg x)
    # µ≤c : de µ≤Card(seg x) et c=Card(seg x) (Leibniz : remplacer Card(seg x) par c)
    c_eq_sym = _sym(vc, mu(vx), c_eq)                       # Card(seg x) = c
    mu_le_c = _leib_rhs_le(vmu, mu(vx), vc, mu_le_segx, c_eq_sym)  # µ ≤ c
    # R_induit{µ,c} = ((µ≤c et µ∈[0,a]) et c∈[0,a])
    Rind_mu_c = conjonction_intro(conjonction_intro(mu_le_c, mu_in_interv), c_in_interv)
    assert Rind_mu_c.conclusion == Rind(vmu, vc), "R_induit{µ,c} mal formé"
    body_x = N.loi_deduction(corps_x, Rind_mu_c)            # corps_x ⇒ R_induit{µ,c}
    Rind_from_ex = N.modus_ponens(ex_x, existe_elimination(body_x, xn))  # R_induit{µ,c}  [c∈S,…]
    body_c = N.loi_deduction(appartient(vc, vS), Rind_from_ex)   # c∈S ⇒ R_induit{µ,c}
    body_all_c = N.generalisation(cn, body_c)              # (∀c)(c∈S ⇒ R_induit{µ,c})
    corps_mu = conjonction_intro(mu_in_S, body_all_c)      # µ∈S et (∀c)(c∈S ⇒ R_induit{µ,c})

    # ── introduire (∃µ) [binder « m » de clause_plus_petit] avec témoin µ
    bm = "m"
    vbm = var(bm)
    body_r = et(appartient(vbm, vS),
        pourtout(cn, impl(appartient(vc, vS), Rind(vbm, vc))))
    but = existe(bm, body_r)
    ex_mu = N.modus_ponens(corps_mu, N.s5(body_r, vmu, bm))   # but  [Hwit, H_min, Hc-discharged, H_onto]
    # éliminer le ∃m de plus_petit_card_segment
    wit_imp = N.loi_deduction(corps_min, ex_mu)            # corps_min ⇒ but
    ex_imp = existe_elimination(wit_imp, mn)              # (∃m)corps_min ⇒ but
    res = N.modus_ponens(pp, ex_imp)                      # but  [bo, T⊂a, T≠∅, H_min, H_onto]
    return res


def hyp_realisation_min(Ro="Ro", a="a", S="S", T="T", t="tt"):
    """ÉNONCÉ (gap) — TOUT indice du pullback T a son segment-cardinal DANS S :
        (∀t)( t∈T ⇒ Card(seg(a,Ro,t)) ∈ S ).

    ⚠️ NON PROUVÉ — c'est « T ⊂ pullback » : T n'indexe que des segments dont le cardinal
    est dans S.  Vrai dès que T = {t∈a : Card(seg(a,Ro,t))∈S}.  Isolé en HYPOTHÈSE, jamais
    postulé.  C'est la moitié « into » du gap réalisation (cardinal de segment ∈ S)."""
    vS, vT = _t(S), _t(T)
    tn = t if isinstance(t, str) else t.nom
    vt = var(tn)
    return pourtout(tn, impl(appartient(vt, vT),
        appartient(cardinal(seg(Ro, a, vt)), vS)))


def hyp_realisation_onto(Ro="Ro", a="a", S="S", T="T", c="cc", x="xs"):
    """ÉNONCÉ (gap) — TOUT cardinal de S est réalisé par un segment indexé dans T :
        (∀c)( c∈S ⇒ (∃x)( x∈T et c = Card(seg(a,Ro,x)) ) ).

    ⚠️ NON PROUVÉ — c'est la SURJECTIVITÉ cardinal↦segment-initial : tout c≤a (c∈S⊂[0,a])
    est le cardinal d'un segment initial de (a,Ro), d'indice x∈a, qu'on capture dans le
    pullback T.  Maillon ordinal↔cardinal restant.  Isolé en HYPOTHÈSE, jamais postulé.
    C'est la moitié « onto » du gap réalisation (avec la collectivisation S8 du pullback)."""
    vS, vT = _t(S), _t(T)
    cn = c if isinstance(c, str) else c.nom
    xn = x if isinstance(x, str) else x.nom
    vc, vx = var(cn), var(xn)
    return pourtout(cn, impl(appartient(vc, vS),
        existe(xn, et(appartient(vx, vT), egal(vc, cardinal(seg(Ro, a, vx)))))))


# ════════════════════════════════════════════════════════════════════════════
#  PIÈCE 5 — ASSEMBLAGE FINAL : bon_ordre_intervalle_ordinal(a) ⊢ bon_ordre_intervalle(a).
#
#  Le PULLBACK est porté par un TERME opaque pullback(a,Ro,S) ; les hypothèses de
#  réalisation + bon ordre + propriétés du pullback sont rassemblées sous un (∃Ro)
#  (Zermelo donne le Ro) dans `hyp_transport_ordinal(a)`, et ÉLIMINÉES ici pour
#  obtenir le résultat SANS Ro libre, == bon_ordre_intervalle(a) littéralement.
# ════════════════════════════════════════════════════════════════════════════
def pullback(a, Ro, S):
    """pullback(a,Ro,S) := { t∈a | Card(seg(a,Ro,t)) ∈ S }  (terme opaque, S8).

    L'image RÉCIPROQUE de S par t↦Card(seg(a,Ro,t)) : les indices t∈a dont le
    segment a son cardinal dans S.  Terme collectivisant (sélection S8 dans a)."""
    return E.app("pullback_seg_card", _t(a), _t(Ro), _t(S))


def _bo_form_canon(a, Ro, T, m="ms", x="xs"):
    """La FORME EXACTE de est_bien_ordonne(Ro,a) telle que plus_petit_card_segment /
    ordinaux_bien_ordonnes la DÉPOSE en hypothèse (binders via hyp_bon_ordre_seg_reel,
    où le terme T occupe le slot du quantificateur X).  On l'extrait du théorème CLOS
    plus_petit_card_segment(Ro,a,T,m,x) par différence avec ses 2 autres hypothèses —
    EN UTILISANT LES MÊMES binders m,x que clause_min_intervalle_de_pullback (sinon la
    forme du bon ordre diffère et l'extraction/décharge échoue)."""
    va = _t(a)
    mn = m if isinstance(m, str) else m.nom
    xn = x if isinstance(x, str) else x.nom
    pp = plus_petit_card_segment(Ro, a, T, mn, xn)            # [bo, T⊂a, T≠∅]
    autres = {inclus(_t(T), va), non(egal(_t(T), E.VIDE))}
    bo = [h for h in pp.hypotheses if h not in autres]
    assert len(bo) == 1, "extraction de la forme bon-ordre ambiguë"
    return bo[0]


# binders CANONIQUES partagés entre hyp_transport_ordinal et bon_ordre_intervalle_ordinal :
#  m = témoin du ⊆-min (∃) → DOIT être « m » (binder de clause_plus_petit) ;
#  c = quantificateur ∀ sur S → DOIT être « x » (binder de clause_plus_petit) ;
#  x = témoin de réalisation onto ; t = quantificateur ∀ de réalisation into.
_BM, _BC, _BX, _BT = "ms", "x", "xw", "tt"


def _corps_Ro(a, Ron, S, m=_BM, c=_BC, x=_BX, t=_BT):
    """Le CORPS du ∃Ro de hyp_transport_ordinal — partagé pour garantir l'égalité
    structurelle entre l'énoncé et son usage dans bon_ordre_intervalle_ordinal."""
    from bourbaki.cardinaux.ensembles_ordinal_cardinal_correspondance import intervalle_0a
    va, vS = _t(a), _t(S)
    interv = intervalle_0a(a)
    PB = pullback(a, Ron, S)
    bo_form = _bo_form_canon(a, Ron, PB, m, x)
    corps_S = et(et(et(inclus(PB, va), non(egal(PB, E.VIDE))),
                    hyp_realisation_min(Ron, a, S, PB, t)),
                 hyp_realisation_onto(Ron, a, S, PB, c, x))
    prop_all_S = pourtout(S, impl(et(inclus(vS, interv), non(egal(vS, E.VIDE))), corps_S))
    return et(bo_form, prop_all_S)


def hyp_transport_ordinal(a="a", Ro="Ro", S="S"):
    """ÉNONCÉ (le GAP unique, isolé sous (∃Ro)) — « il existe un bon ordre Ro de a tel
    que, pour tout S⊂[0,a] non vide, le pullback T=pullback(a,Ro,S) réalise S » :

        (∃Ro)( est_bien_ordonne(Ro, a)
               et (∀S)( ( S⊂[0,a] et S≠∅ ) ⇒
                        ( pullback(a,Ro,S) ⊂ a  et  pullback(a,Ro,S) ≠ ∅
                          et hyp_realisation_min(Ro,a,S,pullback(a,Ro,S))
                          et hyp_realisation_onto(Ro,a,S,pullback(a,Ro,S)) ) ) ).

    ⚠️ NON PROUVÉ — l'UNIQUE maillon ordinal↔cardinal restant.  est_bien_ordonne(Ro,a)
    est DONNÉ par Zermelo (zermelo, CLOS) ; les 4 propriétés du pullback (⊂a, ≠∅, into,
    onto) sont la CONSTRUCTION/RÉALISATION du pullback {t∈a:Card(seg t)∈S} et la
    SURJECTIVITÉ « tout cardinal ≤a = Card d'un segment initial », non encore construites
    (théorie ordinale représentationnelle).  Isolé en HYPOTHÈSE, JAMAIS postulé."""
    Ron = Ro if isinstance(Ro, str) else Ro.nom
    return existe(Ron, _corps_Ro(a, Ron, S))


def _inclus_S_interv(a, S, t):
    """⊢ ( t ∈ S ) ⇒ ( t ∈ [0,a] )  sous l'hypothèse S⊂[0,a]  (instanciée au TERME t)."""
    from bourbaki.cardinaux.ensembles_ordinal_cardinal_correspondance import intervalle_0a
    vS = _t(S)
    interv = intervalle_0a(a)
    Hsub = N.assume(inclus(vS, interv))                    # S ⊂ [0,a]
    return instancie(Hsub, _t(t))                          # t∈S ⇒ t∈[0,a]


def _leib_rhs_le(lhs, old, new, h_le, h_eq):
    """De ⊢ lhs ≤ old [h_le] et ⊢ old = new [h_eq] déduit ⊢ lhs ≤ new  (Leibniz S6)."""
    eqv = N.modus_ponens(h_eq, N.s6(old, new, _HOLE, inf_egal_card(lhs, var(_HOLE))))
    return N.modus_ponens(h_le, equivalence_avant_local(eqv))


def bon_ordre_intervalle_ordinal(a="a", S="S"):
    """⊢ { hyp_transport_ordinal(a) }  ⊢  bon_ordre_intervalle(a).

    🎯🎯 LE GATE ℕ — DÉRIVÉ.  est_bien_ordonne(≤_induit,[0,a]) (la cible déposée
    bon_ordre_intervalle) est obtenue de l'UNIQUE hypothèse hyp_transport_ordinal(a)
    (Zermelo + réalisation du pullback, le seul gap ordinal↔cardinal) :

      • PARTIE ORDRE : relation_ordre_dans_intervalle(a) — CLOSE, INCONDITIONNELLE.
      • PARTIE CLAUSE : pour chaque S⊂[0,a] non vide, on instancie hyp_transport_ordinal
        au pullback T=pullback(a,Ro,S) (Ro éliminé du ∃), fournissant {bo, T⊂a, T≠∅,
        into, onto} ; clause_min_intervalle_de_pullback (transport du ⊆-min de segment,
        CLOS modulo ces hyps) livre le ≤-min de S.  On généralise sur S.

    Tout le NOYAU (⊆-min ordinal, monotonie cardinale, iso identité, transport) est CLOS ;
    le SEUL report est hyp_transport_ordinal.  Conclusion == bon_ordre_intervalle(a)
    LITTÉRALEMENT (test miroir).  theorie=22, rien postulé."""
    from bourbaki.cardinaux.ensembles_ordinal_cardinal_correspondance import (
        intervalle_0a, bon_ordre_intervalle,
    )
    from bourbaki.cardinaux.ensembles_ordinal_cardinal_ordre import (
        relation_ordre_dans_intervalle,
    )
    va, vS = _t(a), _t(S)
    interv = intervalle_0a(a)
    Ron = "Ro"
    PB = pullback(a, Ron, S)                                  # T = pullback(a,Ro,S)
    m, x, c, tb = _BM, _BX, _BC, _BT                         # binders canoniques partagés
    cn, xn = c, x

    # ── corps du ∃Ro de hyp_transport_ordinal (forme PARTAGÉE _corps_Ro)
    bo_form = _bo_form_canon(a, Ron, PB, m, x)               # est_bien_ordonne(Ro,a) forme exacte
    corps_Ro = _corps_Ro(a, Ron, S, m, c, x, tb)
    H = N.assume(corps_Ro)                                    # [corps_Ro]  (Ro libre)
    H_bo = conjonction_elim_gauche(H)                        # est_bien_ordonne(Ro,a)
    H_props = conjonction_elim_droite(H)                     # (∀S)(…⇒ props pullback)

    # ── per-S : (S⊂[0,a] et S≠∅) ⊢ petit(S)
    HsS = N.assume(et(inclus(vS, interv), non(egal(vS, E.VIDE))))   # S⊂[0,a] et S≠∅
    props_S = N.modus_ponens(HsS, instancie(H_props, vS))    # props du pullback de S
    # corps_S = (((PB⊂a et PB≠∅) et into) et onto)
    g1 = conjonction_elim_gauche(props_S)                   # ((PB⊂a et PB≠∅) et into)
    onto = conjonction_elim_droite(props_S)                # hyp_realisation_onto
    g2 = conjonction_elim_gauche(g1)                        # (PB⊂a et PB≠∅)
    into = conjonction_elim_droite(g1)                     # hyp_realisation_min
    pb_sub = conjonction_elim_gauche(g2)                   # PB⊂a
    pb_ne = conjonction_elim_droite(g2)                    # PB≠∅
    S_sub = conjonction_elim_gauche(HsS)                   # S⊂[0,a]

    # ── clause_min_intervalle_de_pullback avec T := PB ; décharger ses 6 hyps
    cm = clause_min_intervalle_de_pullback(Ron, a, S, PB, m, x, c)   # petit(S) [6 hyps]
    cm = _decharge(cm, bo_form, H_bo)
    cm = _decharge(cm, inclus(PB, va), pb_sub)
    cm = _decharge(cm, non(egal(PB, E.VIDE)), pb_ne)
    cm = _decharge(cm, inclus(vS, interv), S_sub)
    cm = _decharge(cm, hyp_realisation_min(Ron, a, S, PB, tb), into)
    cm = _decharge(cm, hyp_realisation_onto(Ron, a, S, PB, cn, xn), onto)   # petit(S) [corps_Ro, HsS]
    # ── décharger (S⊂[0,a] et S≠∅), généraliser sur S → clause_plus_petit
    corps_clause = N.loi_deduction(et(inclus(vS, interv), non(egal(vS, E.VIDE))), cm)
    clause = N.generalisation(S, corps_clause)             # clause_plus_petit(Rind,[0,a]) [corps_Ro]
    # ── éliminer le ∃Ro de hyp_transport_ordinal
    htrans = N.assume(hyp_transport_ordinal(a))
    clause_imp = N.loi_deduction(corps_Ro, clause)          # corps_Ro ⇒ clause  (Ro libre)
    clause_from_ex = N.modus_ponens(htrans, existe_elimination(clause_imp, Ron))  # clause [htrans]
    # ── conjoindre avec la PARTIE ORDRE (CLOSE) → est_bien_ordonne(≤_induit,[0,a])
    rod = relation_ordre_dans_intervalle(a)                 # CLOS
    res = conjonction_intro(rod, clause_from_ex)            # bon_ordre_intervalle(a) [htrans]
    assert res.conclusion == bon_ordre_intervalle(a), \
        "conclusion ≠ bon_ordre_intervalle(a) déposé"
    return res


def _decharge(thm, hyp, preuve_hyp):
    """De Γ∪{H}⊢C et Δ⊢H, déduit Γ∪Δ⊢C (loi_deduction puis modus_ponens)."""
    return N.modus_ponens(preuve_hyp, N.loi_deduction(hyp, thm))


__all__ = [
    "iso_reflexif_seg_preuve", "iso_reflexif_seg_cible",
    "card_seg_monotone",
    "plus_petit_card_segment", "plus_petit_card_segment_cible",
    "clause_min_intervalle_de_pullback",
    "hyp_realisation_min", "hyp_realisation_onto",
    "pullback", "hyp_transport_ordinal",
    "bon_ordre_intervalle_ordinal",
]
