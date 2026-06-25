# DESIGN — Théorème 3 §III.2 (trichotomie des ordinaux) : blueprint fidèle

> Cartographie produite par l agent lecteur R1 (effort trichotomie wei6v14cm, 2026-06-11).
> R2/architecte/prouveurs perdus sur session limit ; ce doc PRÉSERVE le blueprint exécutable.
> Verrou dur unique restant pour N-inconditionnel (avec L5 récurrence). Voir memory/n-bien-ordre-route.md.

## Findings R1

CARTOGRAPHIE FIDÈLE Théorème 3 §III.2 (Bourbaki, Théorie des ensembles, E.III.2.6) + Lemme 4 + Cor 1/2/3, et raccordement EXACT aux pièces déjà closes du projet.

═══════════════════════════════════════════════════════════════════════
A. ÉNONCÉS VERBATIM (ROADMAP_chap2-4.md lignes 197-201) — invariants à respecter
═══════════════════════════════════════════════════════════════════════
- Th3 (l.197) : « Soient E et F deux ensembles bien ordonnés ; l'une au moins des propositions suivantes est vraie : 1) il existe un isomorphisme et un seul de E sur un segment de F ; 2) il existe un isomorphisme et un seul de F sur un segment de E. »
- Lemme 4 (l.198) : « Soient E, F deux ensembles bien ordonnés, f, g deux applications croissantes de E dans F telles que f(E) soit un segment de F et que g soit strictement croissante ; on a alors f(x) ≤ g(x) pour tout x ∈ E. »
- Cor 1 (l.199) : « Le seul isomorphisme d'un ensemble bien ordonné E sur un segment de E est l'application identique de E sur lui-même. »
- Cor 2 (l.200) : iso E→T segment de F et iso F→S segment de E ⇒ S=E, T=F et f,g réciproques.
- Cor 3 (l.201) : tout sous-ensemble A d'un bon ordre E est isomorphe à un segment de E.

⚠️ NOTE DE FIDÉLITÉ IMPORTANTE : l'énoncé du projet déjà posé (trichotomie_ordinaux, ensembles_ordinaux.py:198) est la forme AFFAIBLIE « ordinal_inferieur_ou_egal(E,R,E',R') OU ordinal_inferieur_ou_egal(E',R',E,R) » (existence seule de l'iso à un segment). Le Th3 VERBATIM dit DAVANTAGE : l'iso est UNIQUE (« un et un seul ») et il y a un SENS PRIVILÉGIÉ (l'iso va de l'un sur un segment de l'autre — non les deux à la fois sauf E≅F). Pour fermer la cible posée (le OU d'existence), il SUFFIT de la partie existence ; l'unicité est le sous-produit (c) ci-dessous et le contenu des Corollaires. Recommandation : prouver la cible posée (OU d'existence) via la construction (d) ; l'unicité tombe comme corollaire séparé.

═══════════════════════════════════════════════════════════════════════
B. SQUELETTE DÉDUCTIF FIDÈLE — 4 étapes (a)(b)(c)(d)
═══════════════════════════════════════════════════════════════════════

────────── (a) LEMME 4 §III.2 — « f croissante ⇒ x ≤ f(x) » (version simplifiée pré-Th3) ──────────
La consigne du superviseur retient la forme TRACTABLE du Lemme 4 : f:E→E STRICTEMENT croissante pour le bon ordre R ⇒ (∀x∈E) R{x,f(x)} (x ≤ f(x)). C'est le cas particulier de l'énoncé verbatim avec E=F, g=f strict croissante, f=identité (f(E)=E segment).
ÉNONCÉ TRACTABLE : { est_bien_ordonne(R,E), f:E→E (∀t∈E f(t)∈E), est_strictement_croissante(G_R,G_R,f,E,E) } ⊢ (∀x)(x∈E ⇒ R{x, f(x)}).
SCHÉMA DE PREUVE (fidèle Bourbaki, par minimalité) :
  1. Poser A = { x∈E : f(x) <_R x } = { x∈E : R{f(x),x} et f(x)≠x }. C'est une partie de E (collectivisante par S8).
  2. Raisonner par l'absurde : supposer A≠∅. A⊂E et A≠∅ ⇒ (bon ordre) A a un PLUS PETIT élément m : m∈A et (∀w)(w∈A ⇒ R{m,w}). [PIÈCE : plus_petit_de_bon_ordre, ensembles_ordinal_cardinal_bon_ordre.py:79, CLOS INCONDITIONNEL — instancier sur X:=A].
  3. m∈A ⇒ f(m) <_R m, i.e. R{f(m),m} et f(m)≠m.
  4. f strict croissante + f(m)<_R m ⇒ f(f(m)) <_R f(m). [instancie est_strictement_croissante sur (f(m),m) : hyp f(m)∈E, m∈E, f(m)<m ⇒ f(f(m))<f(m)].
  5. Donc f(m)∈A (car f(f(m)) <_R f(m), et f(m)∈E car f:E→E). Avec f(m) <_R m, ceci contredit m=min(A) (qui force R{m,f(m)}, donc avec antisymétrie f(m)=m, contredisant f(m)≠m).
  6. Donc A=∅ : (∀x∈E) ¬(f(x)<_R x). Par totalité du bon ordre (comparabilité de x et f(x)) ⇒ R{x,f(x)}. [La comparabilité x,f(x) est le lemme L1b — application de la clause de plus petit élément à la paire {x,f(x)} ; déjà schématisée comme `comparables_dans` dans lemme_1_segments].
PIÈCES PROJET : plus_petit_de_bon_ordre (CLOS) ; est_strictement_croissante (ensembles_ordre_monotone.py:123, DÉFINIE, instanciable) ; _proprietes_ordre_de_bon_ordre (extrait transitif+antisym de est_bien_ordonne, motif réutilisable lemme_1_segments.py:117) ; ex_falso / refute_self / leib_transport (helpers locaux déjà éprouvés dans segments_construction.py:212-229). TRACTABLE — même squelette « min(A) contredit » que hyp_bon_ordre_seg_reel.

────────── (b) COROLLAIRE 1 — « aucun bon ordre n'est isomorphe à un de ses segments INITIAUX PROPRES » ──────────
ÉNONCÉ : { est_bien_ordonne(R,E), a∈E, g:E→S_a iso d'ordre où S_a=segment_extremite(R,E,a)=]←,a[ } ⊢ FAUX (contradiction). Forme positive utile (= Cor1 verbatim) : le seul iso d'un bon ordre E sur un segment de E est l'identité.
SCHÉMA : si g:E≅S_a (a∈E, S_a segment propre), alors g est strictement croissante de E dans E (un iso d'ordre est strict croissant) et g(a)∈S_a donc g(a) <_R a. Or Lemme 4 (a) donne a ≤_R g(a), i.e. R{a,g(a)}. Avec g(a)<_R a (R{g(a),a} et g(a)≠a) et antisymétrie : a=g(a), contredisant g(a)≠a. Donc pas d'iso E≅segment propre.
PIÈCES : Lemme 4 (a) ci-dessus ; est_isomorphisme_ordre / compatible_ordre (ensembles_ordre_vocab.py:162,150) pour extraire « g strict croissant » d'un iso (via isomorphisme_ordre_compatible) ; membre_segment (segments_construction.py:106) pour g(a)∈S_a ⇒ g(a)<_R a ; antisymétrie depuis est_bien_ordonne.

────────── (c) UNICITÉ de l'iso entre deux bons ordres ──────────
ÉNONCÉ : { est_bien_ordonne(R,E), f,g deux iso d'ordre E→E' } ⊢ f=g (donc l'iso de Th3, quand il existe, est UNIQUE — c'est le « et un seul »).
SCHÉMA : f∘g⁻¹ est un iso d'ordre E'→E' (composée de deux iso), donc strict croissant E'→E'. Par Cor1 (b) appliqué à E', f∘g⁻¹ = id_{E'}. Donc f=g (post-composer par g). [Symétriquement g∘f⁻¹=id.]
PIÈCES : Cor1 (b) sur E' ; composée d'iso (composee_bijection déjà utilisée pour Prop8 successeur — cf MEMORY ; à raccorder à compatible_ordre pour la composée d'iso d'ordre) ; application_egale_par_valeurs (ensembles_application_valeur, extensionnalité des applications) pour conclure f=g depuis « mêmes valeurs ».

────────── (d) TRICHOTOMIE elle-même — construction de l'iso MAXIMAL (back-and-forth / Knaster-Tarski) ──────────
C'est le cœur du Th3. STRATÉGIE FIDÈLE Bourbaki (= union des couples de segments isomorphes) :
  1. Considérer la famille Φ des couples (S, T) où S est un segment de E, T un segment de F, et S ≅ T (iso d'ordre). Par Cor1+(c) UNICITÉ, l'iso S≅T, quand il existe, est UNIQUE — donc à chaque tel couple correspond UN graphe d'iso bien défini h_{S,T}.
  2. Ces iso sont COMPATIBLES : si (S,T) et (S',T') ∈ Φ avec S⊂S', alors h_{S,T} = restriction de h_{S',T'} à S (par unicité, les deux iso coïncident sur S∩S'=S, qui est un segment des deux). [Contenu de la cohérence Lemme 1 §III.2 — déjà schématisé : lemme_1_segments « ossature iso t↦seg_ext », commit 6092039 / ensembles_bien_ordonne_lemme_1_segments.py].
  3. Poser h := UNION (recollement) de tous les graphes h_{S,T}. Par compatibilité (étape 2) + domaines emboîtés, h est un graphe FONCTIONNEL et INJECTIF (un iso). [PIÈCE MAÎTRESSE : ensembles_recollement_bijection.py — reunion_graphes_fonctionnelle, reunion_graphes_injective, valeur_reunion_gauche/droite, image_reunion_graphes ; généralise à une union indexée le recollement utilisé pour Cantor-Bernstein]. dom(h) = S₀ = union des segments S = un segment de E ; image(h) = T₀ = union des T = un segment de F (la réunion de segments est un segment — Lemme 2 §III.2).
  4. h:S₀≅T₀ est l'iso MAXIMAL entre un segment de E et un segment de F.
  5. ARGUMENT DE MAXIMALITÉ (le « l'un des deux est le tout ») : montrer S₀=E OU T₀=F. Par l'absurde : si S₀≠E ET T₀≠F, alors (Prop1 §III.2 : tout segment propre d'un bon ordre est un ]←,a[) S₀=S_a (a=min(E∖S₀), existe par bon ordre) et T₀=S_b (b=min(F∖T₀)). On ÉTEND h en h∪{(a,b)} : c'est encore un iso d'ordre entre les segments S_a∪{a}=]←,a] et S_b∪{b}=]←,b] (a au sommet de son segment, b au sommet — adjonction du plus grand élément, ensembles_ordre_vocab.relation_adjoint:216). Donc (S_a∪{a}, S_b∪{b})∈Φ STRICTEMENT plus grand que (S₀,T₀) : contredit la maximalité (S₀=union de TOUS les segments isomorphes). Donc S₀=E ou T₀=F.
  6. Si S₀=E : h:E≅T₀ avec T₀ segment de F ⇒ alternative 1) du Th3 (E iso à un segment de F). Si T₀=F : h⁻¹:F≅S₀ segment de E ⇒ alternative 2). DONC le OU (= cible trichotomie_ordinaux posée). ∎

═══════════════════════════════════════════════════════════════════════
C. RACCORDEMENT AUX PIÈCES DU PROJET (résumé opérationnel)
═══════════════════════════════════════════════════════════════════════
DÉFINITIONS (toutes existantes, à réutiliser SANS dupliquer) :
- est_bien_ordonne(R,e) : ensembles_abrege.py:690 = est_relation_ordre_dans ∧ (∀X non vide ⊂E)(∃ min).
- est_segment(S,R,e) : ensembles_abrege.py:711 = S⊂E ∧ clôture-bas.
- segment_extremite(R,e,x)=S_x=]←,x[ : ensembles_abrege.py:724 (terme opaque, axiome_segment_extremite, theorie=22).
- est_plus_petit_element : ensembles_abrege.py:579.
- est_isomorphisme_ordre / compatible_ordre / sont_isomorphes_ordre : ensembles_ordre_vocab.py:162/150/173. ⚠️ l'iso utilise E.valeur(f,x) (graphe) — cohérent avec le « pont valeur d'application » déjà construit (MEMORY : application_egale_par_valeurs, valeur_application_dans_but).
- est_croissante / est_strictement_croissante : ensembles_ordre_monotone.py:90/123.
- strictement_croissante_implique_croissante : ensembles_ordre_monotone.py:241 (CLOS, sous est_ordre(G',E')+f:E→E').
- relation_adjoint / ensemble_adjoint / est_adjonction_plus_grand : ensembles_ordre_vocab.py:209-246 (pour l'extension h∪{(a,b)} étape 5d).

THÉORÈMES/ENGINES CLOS réutilisables :
- plus_petit_de_bon_ordre : ensembles_ordinal_cardinal_bon_ordre.py:79 — CLOS INCONDITIONNEL. Sert dans (a) [min(A)], (d.5) [min(E∖S₀)].
- seg_strict_monotone / seg_strict_monotone_de_bon_ordre : segments_construction.py:144, lemme_1_segments.py:141 — monotonie t↦seg(t), CLOS sur bon ordre. Sert à la cohérence (d.2).
- segment_extremite_est_segment : lemme_1_segments.py:182 — CLOS, chaque S_t est un vrai segment. Sert (d.3,d.5).
- seg_reflechit_ordre : lemme_1_segments.py:268 — sens order-reflecting (cond. comparabilité). Brique de l'iso t↦seg(t).
- hyp_bon_ordre_seg_reel : segments_construction.py:297 — ⊂-min des segments, CLOS sur bon ordre. Réutilisable pour structurer la famille Φ.
- INFRA RECOLLEMENT (PIÈCE MAÎTRESSE de d.3) : ensembles_recollement_bijection.py — reunion_graphes_fonctionnelle/injective, valeur_reunion_gauche(:138)/droite(:147), image_reunion_graphes(:154), reunion_graphes_injective(:257). Exactement l'infra Knaster-Tarski/back-and-forth déjà validée pour Cantor-Bernstein.
- cantor_bernstein, comparabilite_cardinaux, zermelo, recollement_bijection : CLOS (MEMORY), disponibles si la route cardinale est préférée.
- Helpers de preuve éprouvés (à copier localement) : _leib_transport, _ex_falso, _refute_self (segments_construction.py:212-229 et lemme_1_segments.py:97-114), _proprietes_ordre_de_bon_ordre (lemme_1_segments.py:117), _decharge.

═══════════════════════════════════════════════════════════════════════
D. PROPOSITIONS-SUPPORT NÉCESSAIRES (déjà énoncées dans ROADMAP, à mobiliser)
═══════════════════════════════════════════════════════════════════════
- Prop 1 §III.2 (l.184) : dans un bon ordre, tout segment ≠E est un ]←,a[. NÉCESSAIRE à (d.5) pour écrire S₀=S_a. Statut : énoncée, à prouver (a=min(E∖S₀) via plus_petit_de_bon_ordre ; S₀=]←,a[ via est_segment + minimalité).
- Lemme 2 §III.2 (l.188) : la réunion de segments est un segment (1° clôture par réunion). NÉCESSAIRE à (d.3) pour dom(h)=S₀ segment, image(h)=T₀ segment.
- Lemme 1 §III.2 (l.187) : cohérence d'une famille filtrante d'ordres compatibles ⇒ ordre unique recollé. C'est le cadre de (d.2-d.3) ; ossature partielle = ensembles_bien_ordonne_lemme_1_segments.py.
- Comparabilité (totalité du bon ordre) L1b : R{t,s} ou R{s,t} pour t,s∈E. Schématisée comparables_dans (lemme_1_segments.py:259) ; à fermer par plus_petit_de_bon_ordre sur la paire {t,s}. NÉCESSAIRE à (a.6) et au sens order-reflecting.

## Énoncés exacts
- Th3 (E.III.2.6, ROADMAP l.197, VERBATIM) : « Soient E et F deux ensembles bien ordonnés ; l'une au moins des propositions suivantes est vraie : 1) il existe un isomorphisme et un seul de E sur un segment de F ; 2) il existe un isomorphisme et un seul de F sur un segment de E. »
- Cible projet déjà posée (ensembles_ordinaux.py:198, trichotomie_ordinaux) : ⊢ ou( ordinal_inferieur_ou_egal(E,R,E',R') , ordinal_inferieur_ou_egal(E',R',E,R) ) où ordinal_inferieur_ou_egal(E,R,E',R') := (∃S)( est_segment(S,R',E') et sont_isomorphes_ordre(E,S,R,R') ).
- Lemme 4 VERBATIM (ROADMAP l.198) : « Soient E, F deux ensembles bien ordonnés, f, g deux applications croissantes de E dans F telles que f(E) soit un segment de F et que g soit strictement croissante ; on a alors f(x) ≤ g(x) pour tout x ∈ E. »
- Lemme 4 forme TRACTABLE (à prouver) : { est_bien_ordonne(R,E), (∀t)(t∈E ⇒ valeur(f,t)∈E), est_strictement_croissante(R,R,f,E,E) } ⊢ (∀x)( x∈E ⇒ R{x, valeur(f,x)} ).
- Cor 1 VERBATIM (ROADMAP l.199) : « Le seul isomorphisme d'un ensemble bien ordonné E sur un segment de E est l'application identique de E sur lui-même. »
- Cor 1 forme négative (à prouver) : { est_bien_ordonne(R,E), a∈E } ⊢ ¬ sont_isomorphes_ordre(E, segment_extremite(R,E,a), R, R)   [pas d'iso d'un bon ordre sur un de ses segments PROPRES ]←,a[ ].
- Cor 2 VERBATIM (ROADMAP l.200) : « Soient E et F deux ensembles bien ordonnés ; s'il existe un isomorphisme de E sur un segment T de F et un isomorphisme de F sur un segment S de E, on a nécessairement S = E, T = F et f et g sont réciproques l'un de l'autre. »
- Cor 3 VERBATIM (ROADMAP l.201) : « Tout sous-ensemble A d'un ensemble bien ordonné E est isomorphe à un segment de E. »
- Unicité (c) (à prouver, = le « un et un seul » de Th3) : { est_bien_ordonne(R,E), est_isomorphisme_ordre(f,E,E',R,R'), est_isomorphisme_ordre(g,E,E',R,R') } ⊢ f = g.
- Engine déjà CLOS (plus_petit_de_bon_ordre, ensembles_ordinal_cardinal_bon_ordre.py:79) : { est_bien_ordonne(R,E), X⊂E, X≠∅ } ⊢ (∃a)( a∈X et (∀w)(w∈X ⇒ R{a,w}) ).
- Définition est_segment (ensembles_abrege.py:711) : est_segment(S,R,E) := S⊂E et (∀x)(∀y)( (x∈S et y∈E et R{y,x}) ⇒ y∈S ).
- Définition est_strictement_croissante (ensembles_ordre_monotone.py:123) : (∀x)(∀y)( (x∈E et y∈E et (x,y)∈G et x≠y) ⇒ ((f(x),f(y))∈G' et f(x)≠f(y)) ).
- Définition iso d'ordre (ensembles_ordre_vocab.py:162) : est_isomorphisme_ordre(f,E,E',R,R') := est_bijective(f,E,E') et (∀x)(∀y)( (x∈E et y∈E) ⇒ (R{x,y} ⇔ R'{valeur(f,x),valeur(f,y)}) ).
- Prop 1 §III.2 (ROADMAP l.184, support nécessaire à d.5) : « Dans un ensemble bien ordonné E, tout segment de E distinct de E est un intervalle ]←, a[ où a ∈ E. »
- Lemme 2 §III.2 (ROADMAP l.188, support nécessaire à d.3, 1° clause) : toute réunion de segments d'un bon ordre est un segment.
- Comparabilité/totalité L1b (étape 0, à prouver) : { est_bien_ordonne(R,E), t∈E, s∈E } ⊢ ( R{t,s} ou R{s,t} )  [via plus_petit_de_bon_ordre sur X={t,s}].

## Gap / route
ROUTE D'IMPLÉMENTATION RECOMMANDÉE (ordre des sous-lemmes, du plus tractable au plus dur) :

ÉTAPE 0 (préalable, TRACTABLE — débloque (a) et (d)) : COMPARABILITÉ/TOTALITÉ du bon ordre. Prouver `comparables_dans(R,E,t,s)` pour t,s∈E : appliquer plus_petit_de_bon_ordre à la paire X={t,s} (∈𝔓(E), non vide) ⇒ min∈{t,s} minore {t,s} ⇒ R{t,s} ou R{s,t}. CLOS attendu inconditionnel sur est_bien_ordonne. C'est le L1b déjà identifié, hypothèse de seg_reflechit_ordre — le fermer rend ce dernier inconditionnel.

ÉTAPE 1 (TRACTABLE — confiance haute) : LEMME 4 forme tractable (b) « f strict croissante E→E ⇒ x≤f(x) ». Squelette min(A) ci-dessus, copié sur hyp_bon_ordre_seg_reel. Dépend de : plus_petit_de_bon_ordre (CLOS), est_strictement_croissante (déf), antisymétrie+transitivité (extraites), comparabilité (étape 0). RISQUE : modéré (la définition A={x:f(x)<x} est collectivisante S8 ; instancier est_strictement_croissante sur (f(m),m) demande f(m)∈E — fourni par l'hyp f:E→E).

ÉTAPE 2 (TRACTABLE après 1) : COR 1 (no-iso-segment-propre). Court : Lemme4 + iso⇒strict croissant (isomorphisme_ordre_compatible) + g(a)∈S_a⇒g(a)<a (membre_segment) + antisymétrie ⇒ contradiction.

ÉTAPE 3 (MOYEN) : UNICITÉ (c). Demande la composée de deux iso d'ordre = iso d'ordre (raccorder composee_bijection — déjà utilisé Prop8 — à compatible_ordre) + Cor1 sur E' + application_egale_par_valeurs.

ÉTAPE 4 (DUR — magnitude Cantor-Bernstein) : TRICHOTOMIE (d). Verrou réel. 3 sous-pièces à fermer AVANT l'assemblage :
  (i) Prop 1 §III.2 (segment propre = ]←,a[) — TRACTABLE via plus_petit_de_bon_ordre.
  (ii) Lemme 2 §III.2 (réunion de segments = segment) — TRACTABLE (clôture-bas se transmet à la réunion).
  (iii) Assemblage back-and-forth : réifier la famille Φ des couples de segments isomorphes, recoller via ensembles_recollement_bijection (reunion_graphes_fonctionnelle/injective), prouver la maximalité par extension h∪{(a,b)} (relation_adjoint) ⇒ S₀=E ou T₀=F. C'est l'analogue Knaster-Tarski déjà réussi pour Cantor-Bernstein (phi_point_fixe, sans récurrence) — la même infra recollement s'applique. DIFFICULTÉ PRINCIPALE : indexer/quantifier la famille Φ (passer du recollement de DEUX graphes à une union indexée par les segments) ; le projet n'a pour l'instant que le recollement binaire — il faudra soit (α) une union sur l'ensemble des segments via AXIOME_REUNION d'une famille, soit (β) reformuler à la Knaster-Tarski : définir directement h comme plus grand iso (point fixe d'un opérateur d'extension de segment), évitant l'union indexée — RECOMMANDÉ car calque exact de cantor_bernstein/phi_point_fixe qui a fonctionné SANS récurrence.

GAP RÉSIDUEL : aucune pièce manquante bloquante au niveau infrastructure — toutes les briques (plus_petit_de_bon_ordre, monotonie segments, recollement, adjonction, iso d'ordre, application_egale_par_valeurs) existent et sont closes ou définies. Le seul vrai gap est la GÉNÉRALISATION du recollement binaire à la construction du point fixe maximal (étape 4.iii), à mener en style Knaster-Tarski (route β) plutôt qu'union indexée. Effort estimé : 3-6 rounds (magnitude Cantor-Bernstein), parallélisable (étapes 0/1/2 indépendantes de 4.i/4.ii).

INVARIANTS À TENIR : theorie_ensembles()=22 (aucun axiome ajouté ; segment_extremite/adjonction déjà axiomatisés hors theorie_ensembles) ; PROUVE==.est_clos ; jamais postuler un théorème ; binders α-cohérents partagés entre plus_petit_de_bon_ordre et ses consommateurs (cf. hyp_bon_ordre_seg_reel.py:320 qui partage S,ms,xs). FIDÉLITÉ : la cible posée trichotomie_ordinaux (OU d'existence) est PLUS FAIBLE que Th3 verbatim (« un et un seul ») ; prouver d'abord le OU d'existence (d), puis l'unicité (c) en corollaire — ne PAS affaiblir l'énoncé verbatim dans la docstring finale.