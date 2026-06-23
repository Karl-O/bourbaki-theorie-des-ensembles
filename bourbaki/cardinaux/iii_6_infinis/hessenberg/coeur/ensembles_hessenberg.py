"""§III.6.3 — Théorème 2 (HESSENBERG) : 𝔞·𝔞 = 𝔞 pour 𝔞 INFINI.

« Théorème 2 (E.III.6.3) : si 𝔞 est un cardinal infini, alors 𝔞² = 𝔞. »
  (avec 𝔞² := 𝔞·𝔞 = produit_cardinal_binaire(𝔞, 𝔞) = Card(𝔞 × 𝔞).)

C'est le plus PROFOND des théorèmes cardinaux restants (arithmétique cardinale
INFINIE).  La preuve classique :

  (≤, FACILE)   𝔞 ≤ 𝔞·𝔞   : l'application DIAGONALE u ↦ (u, u) injecte 𝔞 dans 𝔞×𝔞.
                            ÉTABLI ICI, INCONDITIONNEL (`diag_inf_egal_produit`,
                            `cardinal_inf_egal_carre`).

  (≥, PROFOND)  𝔞·𝔞 ≤ 𝔞   : par récurrence transfinie sur le BON ORDRE de 𝔞
                            (Zermelo), via l'ORDRE MAXIMAL ⪯ sur 𝔞×𝔞 :
                              (x,y) ⪯ (x',y')  ⟺  max(x,y) < max(x',y'), puis lex.
                            Tout segment propre [←,(x,y)[ ⊂ S×S avec S un segment
                            propre de 𝔞 ; |S×S|=|S|²<𝔞 (hypothèse de récurrence,
                            base finie / ℵ₀) ; d'où le type d'ordre de (𝔞×𝔞,⪯) ≤ 𝔞.

  Cantor–Bernstein (les deux ≤) ⇒ 𝔞·𝔞 = 𝔞.

────────────────────────────────────────────────────────────────────────────────
ÉTAT (HONNÊTE).  La direction FACILE (𝔞 ≤ 𝔞·𝔞) et la RÉDUCTION par Cantor–Bernstein
sont CLOSES (0 hypothèse, ou hypothèse honnête `est_infini`/`𝔞·𝔞 ≤ 𝔞`).  La direction
PROFONDE (𝔞·𝔞 ≤ 𝔞) reste un CHANTIER ouvert (la construction de l'ordre maximal sur
𝔞×𝔞 et la récurrence transfinie sur les cardinaux de segments ne sont pas assemblées) :
elle est ISOLÉE en une hypothèse honnête `est_infini(a) ⇒ a·a ≤ a` (cf.
`enonce_hard_aa_inf_egal_a`) et JAMAIS postulée.

  • `diag_*`                  — l'injection diagonale u↦(u,u) (fonctionnelle, dom=A,
                                injective, image ⊂ A×A) ;  CLOS.
  • `diag_inf_egal_produit`   ⊢ A ≤ A×A                                CLOS (0 hyp).
  • `cardinal_inf_egal_carre` ⊢ Card(A) ≤ Card(A)·Card(A) = a ≤ a·a    CLOS (0 hyp).
  • `carre_inf_egal_si_hard`  ⊢ (a ≤ a·a et a·a ≤ a) ⇒ a·a = a   (Cantor–Bernstein
                                + Prop. 1) ;  CLOS (0 hyp).
  • `hessenberg_si_hard`      ⊢ (a·a ≤ a) ⇒ a·a = a               CLOS (≥ branche
                                fournie ⇒ on referme via la diagonale + CB).
  • `enonce_hessenberg`       — l'énoncé est_infini(a) ⇒ a·a=a  (FORMULE, but final).
  • `enonce_hard_aa_inf_egal_a` — l'énoncé est_infini(a) ⇒ a·a≤a (FORMULE, le ≥ dur).

INVARIANT : theorie_ensembles() reste = 22.  Aucun axiome ajouté ; tout est dérivé.
NOTATIONS : a·a := produit_cardinal_binaire(a,a) := Card(a×a).
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (Terme, var, egal, et, impl, existe, appartient)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege import a_implique_a, syllogisme
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, instancie)
from bourbaki.logique.i_4_egalitaires.tactiques_abrege_egalite import (
    symetrie, composer_egalites)
from bourbaki.logique.i_3_quantifies.tactiques_abrege_quantif import existe_elimination

from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_theoremes import egalite_par_extension
from bourbaki.ensembles.ii_2_couples_produit.ensembles_couples import couple_egal_implique_composantes
from bourbaki.ensembles.fonctions.ii_3_6_fonction_terme.ensembles_fonction_terme import (
    membre_graphe_terme, graphe_terme_fonctionnel)
from bourbaki.ensembles.fonctions.ii_3_4_fonctions_valeur.ensembles_fonctions import valeur_caracterisation

from bourbaki.cardinaux.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    cardinal, inf_egal_card, est_injection_de)
from bourbaki.cardinaux.arithmetique.iii_3_3_produit.ensembles_arith_cardinale import (
    produit_cardinal_binaire, _prop1_direct_t)
from bourbaki.cardinaux.ensembles_cantor_bernstein_final._recollement import cantor_bernstein
from bourbaki.entiers.iii_6_infinis.iii_6_3_infinis_denombrables.ensembles_infinis import est_infini


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# ════════════════════════════════════════════════════════════════════════════
#  L'INJECTION DIAGONALE  F = (u ↦ (u, u))  sur A,  graphe_terme(A, (d0,d0))
# ════════════════════════════════════════════════════════════════════════════
# Variable C54 (liée méta-théoriquement dans l'assemblage de F) : « d0 », comme
# pour l'injection gauche de ensembles_cardinaux_bornes (pas de renommage en @… qui
# casserait l'appariement MP).  T(d0) = (d0, d0) = la diagonale.
_CV = "d0"


def _T_diag():
    """Terme T(d0) = (d0, d0)  (le couple diagonal)."""
    return E.couple(var(_CV), var(_CV))


def _F(a):
    """F = graphe_terme(A, (d0,d0)).   (graphe de l'application u ↦ (u,u).)"""
    return E.graphe_terme(_t(a), _T_diag(), _CV)


def diag_fonctionnel(a="A"):
    """⊢ est_fonctionnel(F),  F = graphe_terme(A,(d0,d0)).   (C54, générique en T.)"""
    return graphe_terme_fonctionnel(_t(a), _T_diag(), _CV, "yb")


def _inst_dom_F(f, x):
    """⊢ (x ∈ dom F) ⇔ (∃y)((x,y)∈F).   (instance de AXIOME_DOM en F, x.)"""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_DOM)
    return instancie(instancie(ax, f), x)


def diag_domaine(a="A"):
    """⊢ dom(F) = A,  F = graphe_terme(A,(d0,d0)).   (la diagonale est définie sur A.)

    z∈dom F ⇔ (∃y)((z,y)∈F) [AXIOME_DOM] ; (z,(z,z))∈F donne le témoin pour z∈A,
    réciproquement un témoin y donne z∈A (via _membre).  Extension (A1), liant z."""
    vA = _t(a)
    F = _F(vA)
    vz, vy = var("z"), var("y")
    Tz = E.couple(vz, vz)                                # (z,z)
    dom_car = _inst_dom_F(F, vz)                         # z∈dom F ⇔ (∃y)((z,y)∈F)
    mem_zy = membre_graphe_terme(vA, _T_diag(), "z", "y", _CV, "yb")   # ((z,y)∈F)⇔(z∈A et y=(z,z))
    # ⇒ : (∃y)((z,y)∈F) ⇒ z∈A
    hzy = N.assume(appartient(E.couple(vz, vy), F))
    z_inA = conjonction_elim_gauche(N.modus_ponens(hzy, equivalence_avant(mem_zy)))
    fwd_inner = existe_elimination(
        N.loi_deduction(appartient(E.couple(vz, vy), F), z_inA), "y")
    fwd = syllogisme(equivalence_avant(dom_car), fwd_inner)   # z∈dom F ⇒ z∈A
    # ⇐ : z∈A ⇒ z∈dom F   (témoin y:=(z,z))
    hzA = N.assume(appartient(vz, vA))
    # ((z,(z,z))∈F) ⇐ (z∈A et (z,z)=(z,z))
    mem_zTz = membre_graphe_terme(vA, _T_diag(), "z", "yb", _CV, "ycc")  # ((z,yb)∈F)⇔(z∈A et yb=(z,z))
    inst_Tz = instancie(N.generalisation("yb", mem_zTz), Tz)            # ((z,(z,z))∈F)⇔(z∈A et (z,z)=(z,z))
    zT_in = N.modus_ponens(conjonction_intro(hzA, N.reflexivite(Tz)),
                           equivalence_arriere(inst_Tz))               # (z,(z,z))∈F
    ex_y = N.modus_ponens(zT_in, N.s5(appartient(E.couple(vz, vy), F), Tz, "y"))  # (∃y)(z,y)∈F
    z_dom = N.modus_ponens(ex_y, equivalence_arriere(dom_car))   # z∈dom F
    bwd = N.loi_deduction(appartient(vz, vA), z_dom)
    char = N.generalisation("z", conjonction_intro(fwd, bwd))   # (∀z)(z∈dom F ⇔ z∈A)
    self_A = N.generalisation("z", conjonction_intro(
        a_implique_a(appartient(vz, vA)), a_implique_a(appartient(vz, vA))))
    return egalite_par_extension(char, self_A, E.dom(F), vA, "z")


def diag_valeur(a="A", u="u"):
    """⊢_{u∈A}  F(u) = (u, u),   F = graphe_terme(A,(d0,d0)).

    (u,(u,u))∈F (car u∈A et (u,u)=(u,u)) ; valeur_caracterisation (C46) instanciée à
    (u,u) donne (u,u)=F(u) sous {F fonctionnel, (∃y)(u,y)∈F} ; on décharge les deux
    hypothèses (F fonctionnel clos, domaine via le témoin)."""
    vA, vu = _t(a), _t(u)
    F = _F(vA)
    Tu = E.couple(vu, vu)                                # (u,u)
    unom = vu.nom if vu.tag == "var" else "u"            # nom de la variable u (ou « u » si terme)
    mem_uTu = membre_graphe_terme(vA, _T_diag(), unom, "yb", _CV, "ycc")  # ((u,yb)∈F)⇔(u∈A et yb=(u,u))
    inst_Tu = instancie(N.generalisation("yb", mem_uTu), Tu)            # ((u,(u,u))∈F)⇔(u∈A et (u,u)=(u,u))
    huA = N.assume(appartient(vu, vA))                   # u∈A
    uTu_in = N.modus_ponens(conjonction_intro(huA, N.reflexivite(Tu)),
                            equivalence_arriere(inst_Tu))   # (u,(u,u))∈F
    ex_y = N.modus_ponens(uTu_in, N.s5(appartient(E.couple(vu, var("y")), F), Tu, "y"))  # (∃y)(u,y)∈F
    vc = valeur_caracterisation(F, vu)                   # ((u,y)∈F)⇔(y=F(u))   [hyps func+dom]
    vc_T = instancie(N.generalisation("y", vc), Tu)      # ((u,(u,u))∈F)⇔((u,u)=F(u))
    Tu_eq_Fu = N.modus_ponens(uTu_in, equivalence_avant(vc_T))   # (u,u)=F(u)
    Fu_eq_Tu = N.modus_ponens(Tu_eq_Fu, symetrie(Tu, E.valeur(F, vu)))   # F(u)=(u,u)
    # décharge {F fonctionnel, (∃y)(u,y)∈F}
    out = N.modus_ponens(diag_fonctionnel(vA),
        N.loi_deduction(E.est_fonctionnel(F),
            N.modus_ponens(ex_y, N.loi_deduction(
                existe("y", appartient(E.couple(vu, var("y")), F)), Fu_eq_Tu))))
    return N.loi_deduction(appartient(vu, vA), out)      # u∈A ⇒ F(u)=(u,u)


def diag_injective(a="A"):
    """⊢ injective_dans(F, A),  F = graphe_terme(A,(d0,d0)).

    Forme : (∀u)(∀u')(((u∈A et u'∈A) et F(u)=F(u')) ⇒ u=u').  F(u)=(u,u), F(u')=(u',u')
    (diag_valeur sous u∈A / u'∈A) ; de F(u)=F(u') on tire (u,u)=(u',u'), donc
    (Prop. 1 sur les couples) u=u'.  Liants u, up (= ceux de injective_dans)."""
    vA = _t(a)
    F = _F(vA)
    vu, vup = var("u"), var("up")
    Tu, Tup = E.couple(vu, vu), E.couple(vup, vup)
    ante = et(et(appartient(vu, vA), appartient(vup, vA)),
              egal(E.valeur(F, vu), E.valeur(F, vup)))
    h = N.assume(ante)
    u_inA = conjonction_elim_gauche(conjonction_elim_gauche(h))     # u∈A
    up_inA = conjonction_elim_droite(conjonction_elim_gauche(h))    # u'∈A
    Fu_Fup = conjonction_elim_droite(h)                            # F(u)=F(u')
    Fu_eq = N.modus_ponens(u_inA, diag_valeur(vA, vu))             # F(u)=(u,u)
    Fup_eq = N.modus_ponens(up_inA, diag_valeur(vA, vup))          # F(u')=(u',u')
    Tu_eq_Fu = N.modus_ponens(Fu_eq, symetrie(E.valeur(F, vu), Tu))    # (u,u)=F(u)
    Tu_eq_Tup = composer_egalites(composer_egalites(Tu_eq_Fu, Fu_Fup), Fup_eq)   # (u,u)=(u',u')
    comps = N.modus_ponens(Tu_eq_Tup, couple_egal_implique_composantes(vu, vu, vup, vup))
    u_eq_up = conjonction_elim_gauche(comps)                       # u=u'
    inner = N.loi_deduction(ante, u_eq_up)
    return N.generalisation("u", N.generalisation("up", inner))


def diag_image_inclus(a="A"):
    """⊢ image(F, A) ⊂ A×A,   F = graphe_terme(A,(d0,d0)).

    z∈F⟨A⟩ ⇔ (∃x)(x∈A et (x,z)∈F) [AXIOME_IMAGE].  Sous le corps, (u,z)∈F donne
    (u∈A et z=(u,u)) (_membre), et u∈A donne (u,u)∈A×A (AXIOME_PRODUIT, témoins
    p:=u, q:=u) ; Leibniz z=(u,u) ↦ z donne z∈A×A.  ∃-élim → F⟨A⟩ ⊂ A×A.  Liant z."""
    vA = _t(a)
    F = _F(vA)
    P = E.produit(vA, vA)                                # A×A
    vz, vx = var("z"), var("x")
    ax_img = N.axiome(E.theorie_ensembles(), E.AXIOME_IMAGE)
    img_car = instancie(instancie(instancie(ax_img, F), vA), vz)   # z∈F⟨A⟩ ⇔ (∃x)(x∈A et (x,z)∈F)
    vu = vx                                                       # témoin = « x » (≠ d0)
    body = et(appartient(vu, vA), appartient(E.couple(vu, vz), F))
    hb = N.assume(body)
    u_inA = conjonction_elim_gauche(hb)                  # u∈A
    uz_inF = conjonction_elim_droite(hb)                 # (u,z)∈F
    mem_uz = membre_graphe_terme(vA, _T_diag(), vu.nom, "z", _CV, "yb")   # ((u,z)∈F)⇔(u∈A et z=(u,u))
    z_eq_Tu = conjonction_elim_droite(N.modus_ponens(uz_inF, equivalence_avant(mem_uz)))  # z=(u,u)
    # (u,u)∈A×A   via AXIOME_PRODUIT (témoins p:=u, q:=u)
    Tu = E.couple(vu, vu)
    Tu_inP = _couple_diag_dans_produit(vu, vA)           # u∈A ⇒ (u,u)∈A×A  (décharge u∈A)
    Tu_in = N.modus_ponens(u_inA, Tu_inP)                # (u,u)∈A×A
    # z∈A×A via z=(u,u) (Leibniz)
    Tu_eq_z = N.modus_ponens(z_eq_Tu, symetrie(vz, Tu))  # (u,u)=z
    z_inP = N.modus_ponens(Tu_in, equivalence_avant(N.modus_ponens(
        Tu_eq_z, N.s6(Tu, vz, "w", appartient(var("w"), P)))))   # z∈A×A
    inner = existe_elimination(N.loi_deduction(body, z_inP), "x")   # (∃x)body ⇒ z∈A×A
    z_in_imp = syllogisme(equivalence_avant(img_car), inner)        # z∈F⟨A⟩ ⇒ z∈A×A
    return N.generalisation("z", z_in_imp)               # F⟨A⟩ ⊂ A×A


def _couple_diag_dans_produit(vu, vA):
    """⊢ u∈A ⇒ (u,u)∈A×A.   (AXIOME_PRODUIT, témoins p:=u, q:=u.)"""
    vp, vq = var("p"), var("q")
    Tu = E.couple(vu, vu)
    axp = N.axiome(E.theorie_ensembles(), E.AXIOME_PRODUIT)
    instp = instancie(instancie(instancie(axp, vA), vA), Tu)   # (u,u)∈A×A ⇔ (∃p)(∃q)(((u,u)=(p,q) et p∈A) et q∈A)
    def prod_corps(t1, t2):
        return et(et(egal(Tu, E.couple(t1, t2)), appartient(t1, vA)),
                  appartient(t2, vA))
    huA = N.assume(appartient(vu, vA))                   # u∈A
    built = conjonction_intro(conjonction_intro(N.reflexivite(Tu), huA), huA)  # = prod_corps(u,u)
    ex_q = N.modus_ponens(built, N.s5(prod_corps(vu, vq), vu, "q"))   # (∃q)prod_corps(u,q)
    ex_pq = N.modus_ponens(ex_q, N.s5(existe("q", prod_corps(vp, vq)), vu, "p"))  # (∃p)(∃q)...
    to_prod = N.modus_ponens(ex_pq, equivalence_arriere(instp))      # (u,u)∈A×A
    return N.loi_deduction(appartient(vu, vA), to_prod)


# ════════════════════════════════════════════════════════════════════════════
#  DIRECTION FACILE :  A ≤ A×A   (la diagonale)   et   a ≤ a·a   (cardinaux)
# ════════════════════════════════════════════════════════════════════════════
def diag_inf_egal_produit(a="A"):
    """⊢ A ≤ A×A.   (« a ≤ a·a », E.III.3.2 ; injection diagonale u↦(u,u).)

    Témoin = F = graphe_terme(A,(d0,d0)).  est_injection_de(F, A, A×A) tient par ses
    quatre conjoints (diag_fonctionnel/domaine/injective/image_inclus) ; S5 témoin F."""
    vA = _t(a)
    F = _F(vA)
    P = E.produit(vA, vA)                                # A×A
    func = diag_fonctionnel(vA)                          # F fonctionnel
    domeq = diag_domaine(vA)                             # dom F = A
    inj = diag_injective(vA)                             # injective_dans(F, A)
    img = diag_image_inclus(vA)                          # image(F,A) ⊂ A×A
    injection = conjonction_intro(conjonction_intro(conjonction_intro(
        func, domeq), inj), img)                         # est_injection_de(F, A, A×A)
    return N.modus_ponens(injection,
        N.s5(est_injection_de(var("F"), vA, P), F, "F"))   # A ≤ A×A


def cardinal_inf_egal_carre(a="A"):
    """⊢ Card(A) ≤ produit_cardinal_binaire(Card A, Card A).   (= a ≤ a·a.)

    Direction FACILE de Hessenberg, sur les VRAIS cardinaux : a·a := Card(a×a).
    Chaîne (a := Card A) :
      (1) a ≤ a×a            — la diagonale (diag_inf_egal_produit instancié à a) ;
      (2) Eq(a×a, Card(a×a)) — tout ensemble est équipotent à son cardinal ;
          d'où a×a ≤ Card(a×a)  (Eq ⇒ ≤) ;
      (3) transitivité ⇒ a ≤ Card(a×a) = a·a.
    CLOS (0 hypothèse)."""
    from bourbaki.cardinaux.iii_3_equipotence_cardinaux.props_restantes.ensembles_cardinaux_props_restantes import (
        _inf_egal_transitive_t, _eq_implique_inf_egal_t, _eq_son_cardinal_t)
    vA = _t(a)
    a_card = cardinal(vA)                                # a = Card A
    prod = E.produit(a_card, a_card)                     # a×a  (ensemble)
    aa = produit_cardinal_binaire(a_card, a_card)        # a·a = Card(a×a)
    gen = N.generalisation("A", diag_inf_egal_produit("A"))   # (∀A)(A ≤ A×A)
    le1 = instancie(gen, a_card)                         # a ≤ a×a
    eq_prod = _eq_son_cardinal_t(prod)                   # Eq(a×a, Card(a×a))
    le2 = N.modus_ponens(eq_prod, _eq_implique_inf_egal_t(prod, aa))   # a×a ≤ Card(a×a)
    trans = _inf_egal_transitive_t(a_card, prod, aa)     # (a≤a×a et a×a≤a·a) ⇒ a≤a·a
    return N.modus_ponens(conjonction_intro(le1, le2), trans)   # a ≤ a·a


# ════════════════════════════════════════════════════════════════════════════
#  RÉDUCTION par CANTOR–BERNSTEIN :  (a≤a·a et a·a≤a) ⇒ a·a = a
# ════════════════════════════════════════════════════════════════════════════
def carre_inf_egal_si_hard(a="A"):
    """⊢ (a ≤ a·a et a·a ≤ a) ⇒ a·a = a,   a := Card(A),  a·a := Card(A×A).

    Cantor–Bernstein donne Eq(a, a·a) sous les deux inégalités ; la Proposition 1
    (sens direct, version TERME) conclut Card(a)=Card(a·a), i.e. a = a·a, d'où a·a=a
    par symétrie.  CLOS (0 hypothèse — les deux ≤ sont DANS l'antécédent)."""
    vA = _t(a)
    a_card = cardinal(vA)                                # a = Card(A)
    aa = produit_cardinal_binaire(a_card, a_card)        # a·a = Card(a×a)
    # Cantor–Bernstein, version TERME (généralise puis instancie, comme prop9/prop10 :
    # évite la capture des noms internes f,g de la machinerie Knaster–Tarski).
    cb_nom = cantor_bernstein("A", "B", "f", "g")        # (A≤B et B≤A) ⇒ Eq(A,B)
    cb_gen = N.generalisation("A", N.generalisation("B", cb_nom))
    cb = instancie(instancie(cb_gen, a_card), aa)        # (a≤a·a et a·a≤a) ⇒ Eq(a,a·a)
    hyp = et(inf_egal_card(a_card, aa), inf_egal_card(aa, a_card))
    h = N.assume(hyp)
    eq_a_aa = N.modus_ponens(h, cb)                      # Eq(a, a·a)
    # Prop. 1 (sens direct) : Eq(a, a·a) ⇒ Card(a) = Card(a·a)
    prop1 = _prop1_direct_t(a_card, aa)                  # Eq(a,a·a) ⇒ Card a = Card(a·a)
    card_eq = N.modus_ponens(eq_a_aa, prop1)             # Card(a) = Card(a·a)
    # Card(a) = a  (a = Card A est un cardinal : Card(Card A) = Card A, idempotence)
    from bourbaki.cardinaux.iii_3_equipotence_cardinaux.props_restantes.ensembles_cardinaux_props_restantes import _cardinal_idempotent_t
    idem = _cardinal_idempotent_t(vA)                    # Card(Card A) = Card A = a
    # idem : Card(a) = a   ; réécrit Card(a)=Card(a·a) → a = Card(a·a)
    a_eq_caa = composer_egalites(N.modus_ponens(idem, symetrie(cardinal(a_card), a_card)),
                                 card_eq)                 # a = Card(a·a)
    # Card(a·a) = a·a  (a·a = Card(a×a) est un cardinal ; idempotence sur le terme a×a)
    idem_aa = _cardinal_idempotent_t(E.produit(a_card, a_card))   # Card(Card(a×a)) = Card(a×a)
    # a = Card(a·a) = Card(Card(a×a)) = Card(a×a) = a·a
    a_eq_aa = composer_egalites(a_eq_caa, idem_aa)        # a = a·a
    aa_eq_a = N.modus_ponens(a_eq_aa, symetrie(a_card, aa))   # a·a = a
    return N.loi_deduction(hyp, aa_eq_a)


def hessenberg_si_hard(a="A"):
    """⊢ (a·a ≤ a) ⇒ a·a = a,   a := Card(A).

    La direction FACILE a ≤ a·a est ICI (cardinal_inf_egal_carre, CLOS) ; sous
    l'hypothèse de la direction PROFONDE a·a ≤ a, Cantor–Bernstein conclut a·a = a.
    CLOS (l'unique hypothèse résiduelle est le ≥ dur, dans l'antécédent)."""
    vA = _t(a)
    a_card = cardinal(vA)
    aa = produit_cardinal_binaire(a_card, a_card)
    le1 = cardinal_inf_egal_carre(vA)                    # a ≤ a·a   (CLOS, la diagonale)
    h_hard = N.assume(inf_egal_card(aa, a_card))         # a·a ≤ a   (hyp dure)
    both = conjonction_intro(le1, h_hard)                # a≤a·a et a·a≤a
    red = carre_inf_egal_si_hard(vA)                     # (a≤a·a et a·a≤a) ⇒ a·a=a
    concl = N.modus_ponens(both, red)                    # a·a = a
    return N.loi_deduction(inf_egal_card(aa, a_card), concl)


# ════════════════════════════════════════════════════════════════════════════
#  ÉNONCÉS (formules-cibles) — frontière HONNÊTE
# ════════════════════════════════════════════════════════════════════════════
def enonce_hard_aa_inf_egal_a(a="A"):
    """FORMULE : est_infini(Card A) ⇒ (Card A · Card A ≤ Card A).

    L'inégalité PROFONDE (≥) de Hessenberg, ISOLÉE comme hypothèse honnête.  C'est
    le seul verrou restant : sa preuve (ordre maximal sur a×a + récurrence transfinie
    sur les cardinaux de segments) n'est PAS assemblée.  JAMAIS postulée."""
    vA = _t(a)
    a_card = cardinal(vA)
    aa = produit_cardinal_binaire(a_card, a_card)
    return impl(est_infini(a_card), inf_egal_card(aa, a_card))


def enonce_hessenberg(a="A"):
    """FORMULE : est_infini(Card A) ⇒ (Card A · Card A = Card A).

    Théorème 2 (E.III.6.3), but FINAL : pour 𝔞 infini, 𝔞·𝔞 = 𝔞.  La direction ≤ et
    la réduction Cantor–Bernstein sont closes ; reste à fournir enonce_hard."""
    vA = _t(a)
    a_card = cardinal(vA)
    aa = produit_cardinal_binaire(a_card, a_card)
    return impl(est_infini(a_card), egal(aa, a_card))


def hessenberg_depuis_hard(a="A"):
    """⊢ (est_infini(a) ⇒ a·a≤a)  ⇒  (est_infini(a) ⇒ a·a=a),   a := Card A.

    PONT FINAL : si l'on dispose de la direction PROFONDE (sous est_infini), on
    referme Hessenberg complet via la diagonale + Cantor–Bernstein.  CLOS — l'unique
    hypothèse est exactement enonce_hard_aa_inf_egal_a (le ≥ dur), JAMAIS supposée
    vraie ici, seulement transportée.  Donne le THÉORÈME COMPLET dès que le ≥ tombe."""
    vA = _t(a)
    a_card = cardinal(vA)
    aa = produit_cardinal_binaire(a_card, a_card)
    h_imp = N.assume(impl(est_infini(a_card), inf_egal_card(aa, a_card)))   # hyp : a infini ⇒ a·a≤a
    h_inf = N.assume(est_infini(a_card))                 # a infini
    hard = N.modus_ponens(h_inf, h_imp)                  # a·a ≤ a
    si_hard = hessenberg_si_hard(vA)                     # (a·a≤a) ⇒ a·a=a
    concl = N.modus_ponens(hard, si_hard)                # a·a = a
    inner = N.loi_deduction(est_infini(a_card), concl)   # a infini ⇒ a·a=a
    return N.loi_deduction(impl(est_infini(a_card), inf_egal_card(aa, a_card)), inner)


__all__ = [
    # injection diagonale
    "diag_fonctionnel", "diag_domaine", "diag_valeur", "diag_injective",
    "diag_image_inclus",
    # direction facile (CLOS)
    "diag_inf_egal_produit", "cardinal_inf_egal_carre",
    # réduction Cantor–Bernstein (CLOS)
    "carre_inf_egal_si_hard", "hessenberg_si_hard", "hessenberg_depuis_hard",
    # énoncés-frontière
    "enonce_hard_aa_inf_egal_a", "enonce_hessenberg",
]
