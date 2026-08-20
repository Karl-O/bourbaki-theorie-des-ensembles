# -*- coding: utf-8 -*-
"""NOTATIONS — quelle notation est employée avant d'avoir été introduite ?

LE MANQUE QUE CET OUTIL COMBLE. Le 20 août 2026, Karl a relevé trois fautes de
la même famille dans A1 : « = » employé hors d'une théorie égalitaire, « τx(A) »
écrit comme s'il contenait encore x, et « ⊢ » utilisé 162 lignes avant son
introduction — « ⊬ » n'étant, lui, jamais défini du tout. Les trois ont été
corrigées une par une. C'était traiter les instances et non la classe : rien ne
garantissait qu'il n'en restait pas dix autres. D'où ce balayage.

CE QU'IL FAIT. Pour chaque notation apparaissant en mode mathématique, il donne
la ligne de PREMIÈRE APPARITION et cherche, autour d'elle, un INDICE
D'INTRODUCTION — « nous écrivons », « on note », « we write », « désigne »,
« := », ou un environnement de définition. Il classe ensuite :

    JAMAIS      aucun indice d'introduction dans tout le document ;
    APRÈS       le premier indice arrive APRÈS la première utilisation ;
    OK          un indice précède ou accompagne la première utilisation.

⚠️ CE QU'IL NE SAIT PAS FAIRE, et qu'il ne faut pas lui demander. Il ne
comprend pas le texte : un « JAMAIS » sur `\\forall` ou `\\cup` est un faux
positif — ces notations n'ont pas à être introduites, tout lecteur les connaît.
C'est pourquoi il porte une liste `STANDARD` de notations exemptées, et
pourquoi il RANGE plutôt qu'il ne TRANCHE. Le jugement reste humain ; l'outil
garantit seulement qu'aucune notation n'échappe à l'examen.

⚠️ Il ne voit pas non plus les notations écrites en toutes lettres (« the
turnstile »), qui référencent en avant tout autant. Cette faute-là se trouve à
la lecture.

Usage :
    python article/scripts/notations.py article/main.tex
    python article/scripts/notations.py article/main_fr.tex article/goldbach/main_fr.tex
    python article/scripts/notations.py --tout article/main.tex   # sans le filtre STANDARD
"""
from __future__ import annotations

import io
import re
import sys

BS = chr(92)

#: notations que tout lecteur d'un article de logique connaît : ne pas exiger
#: qu'elles soient introduites. Liste volontairement LARGE — mieux vaut un faux
#: négatif ici qu'un rapport noyé sous le bruit.
STANDARD = frozenset("""
forall exists in notin subseteq subset cup cap emptyset neg wedge vee to
Rightarrow Leftrightarrow rightarrow leftrightarrow implies iff times cdot
leq geq neq equiv approx sim mapsto circ dots ldots cdots quad qquad
alpha beta gamma delta epsilon varepsilon zeta eta theta iota kappa lambda mu
nu xi pi rho sigma tau upsilon phi varphi chi psi omega
Gamma Delta Theta Lambda Xi Pi Sigma Upsilon Phi Psi Omega
mathbb mathcal mathrm mathit mathsf mathbf text textbf textit emph
frac sum prod int sqrt le ge ne pm mp infty partial nabla
left right big Big bigl bigr Bigl Bigr langle rangle lvert rvert
colon semicolon ast star dagger prime bmod pmod
""".split())

#: [!] Les tournures d'introduction REELLEMENT employees. La premiere version
#: de cette liste ignorait « let X be » et « Write X for » — les deux formes
#: que A1 utilise partout — et classait donc « jamais introduites » des
#: notations posees en bonne et due forme (mesure : la justification et le
#: tourniquet nie, tous deux definis sur place). Une liste d'indices trop
#: courte ne rend pas l'outil prudent, elle le rend bavard — et un rapport
#: bavard finit ignore.
CUES = re.compile(
    r"(nous écrivons|on écrit|on note|nous notons|on désigne|désigne|noté"
    r"|notons|soit\b.{0,40}\ble\b|posons|on pose|appelons|la négation"
    r"|we write|write\b.{0,40}\bfor\b|let\b.{0,40}\bbe\b|we denote|denote"
    r"|denoted|written|is defined|we set|we call|the negation"
    r"|:=|\begin\{definition\})", re.I)

#: fenêtre (en lignes) autour d'une occurrence où l'on cherche un indice
FENETRE = 3

MATH = re.compile(r"\$\$?(.+?)\$\$?|\\\[(.*?)\\\]", re.S)
#: un backslash LITTÉRAL suivi d'un nom — d'où re.escape : « BS + "(" » ferait
#: du backslash un échappement de la parenthèse (erreur payée à l'écriture).
MACRO = re.compile(re.escape(BS) + r"([a-zA-Z]+)")

#: ⚠️ LE VRAI GISEMENT. Les notations PROPRES à un article ne sont pas des macros
#: LaTeX mais des noms enveloppés — \mathit{Infid}, \mathrm{Ax}, \mathcal{T} — ou
#: des identifiants nus de plusieurs lettres. Ne chercher que les macros les rate
#: entièrement, alors que ce sont elles qui risquent le plus d'être employées
#: avant d'être posées : personne n'oublie d'introduire ∀, tout le monde oublie
#: d'introduire Vac_T.
ENVELOPPE = re.compile(re.escape(BS) + r"math(?:it|rm|cal|sf|bf|bb)\{([A-Za-z][A-Za-z_]*)\}")
PROSE = re.compile(re.escape(BS) + r"(?:text|texttt|textit|textbf|textsf|emph|mbox|hbox|url)\{[^{}]*\}")
NU = re.compile(r"(?<![A-Za-z\\])([A-Z][a-z]{2,}|[a-z]{3,})(?![A-Za-z])")


INLINE = re.compile(r"(?<!\\)\$([^$]+?)(?<!\\)\$")
BLOC_DEB = re.compile(re.escape(BS) + r"begin\{(align|equation|gather)\*?\}")
BLOC_FIN = re.compile(re.escape(BS) + r"end\{(align|equation|gather)\*?\}")
DISPLAY = re.compile(re.escape(BS) + r"\[(.*?)" + re.escape(BS) + r"\]")


def segments_math(lignes):
    """Rend [(no_ligne, contenu_math)] pour un document LaTeX.

    ⚠️ LE POINT DÉLICAT : un `$...$` peut s'étendre sur PLUSIEURS lignes.
    Apparier les `$` ligne par ligne décale alors tout d'un cran et fait prendre
    la PROSE pour des mathématiques — c'est ainsi que « its failure class » s'est
    retrouvé signalé comme notation. On suit donc la parité des `$` d'une ligne à
    l'autre, en ignorant les `\\$` échappés.

    ⚠️ Les lignes de `tikzpicture` sont ignorées : leurs ancres de dessin
    (`north`, `center`, `east`) ne sont pas des notations.
    """
    out = []
    dans_bloc = dans_tikz = False
    #: le PRÉAMBULE n'est pas du texte : ses options de paquets ne sont pas des
    #: notations. Sans ce filtre, l'outil signalait « inputenc », « graphicx »...
    corps = False
    for i, ligne in enumerate(lignes, 1):
        if not corps:
            corps = (BS + 'begin{document}') in ligne
            continue
        if BS + 'begin{tikzpicture}' in ligne:
            dans_tikz = True
        if BS + 'end{tikzpicture}' in ligne:
            dans_tikz = False
            continue
        if dans_tikz:
            continue
        nu = '' if ligne.lstrip().startswith('%') else ligne.split('%')[0]

        if dans_bloc:
            out.append((i, nu))
            if BLOC_FIN.search(nu):
                dans_bloc = False
            continue
        if BLOC_DEB.search(nu):
            dans_bloc = True
            continue

        #: ⚠️ DÉCISION D'INGÉNIERIE, à ne pas « améliorer » sans mesurer.
        #: Suivre la parité des `$` d'une ligne à l'autre a été essayé et
        #: ABANDONNÉ : `$$`, les `\$` et les `$...$` multilignes la
        #: désynchronisent, et une désynchronisation fait prendre des pages
        #: entières de prose pour des mathématiques — l'outil devient
        #: silencieusement faux (mesuré : 1 387 fausses alarmes sur 1 470).
        #: On ne retient donc que les `$...$` OUVERTS ET FERMÉS SUR LA MÊME
        #: LIGNE, ce qui couvre l'immense majorité des cas.
        #: CONSÉQUENCE ASSUMÉE : une formule `$...$` coupée en fin de ligne est
        #: MANQUÉE. L'outil sous-signale plutôt qu'il n'invente — c'est le bon
        #: sens de l'erreur pour un outil d'audit, mais il faut le savoir.
        for m in INLINE.finditer(nu):
            seg = m.group(1)
            #: [!] GARDE ANTI-PROSE. Faute de suivi inter-lignes, un `$`
            #: fermant la formule de la ligne precedente s'apparie avec le
            #: `$` suivant et capture la PHRASE entre les deux. Un segment
            #: qui contient trois mots minuscules ou plus est de la prose,
            #: pas une formule. Heuristique assumee : elle raterait une
            #: formule faite de trois identifiants minuscules separes par
            #: des espaces, ce qui ne se produit pas dans ces articles.
            mots = [t for t in seg.split() if t.isalpha() and t.islower()]
            if len(mots) >= 3:
                continue
            out.append((i, seg))
        for m in DISPLAY.finditer(nu):
            out.append((i, m.group(1)))
    return out


def analyse(chemin, tout=False):
    lignes = io.open(chemin, encoding='utf-8').read().split('\n')
    #: lignes portant un indice d'introduction
    indices = [i for i, l in enumerate(lignes, 1) if CUES.search(l)]
    premiere, occurrences = {}, {}
    for no, contenu in segments_math(lignes):
        trouves = [(BS + n, n) for n in MACRO.findall(contenu)]
        #: les noms enveloppés et les identifiants nus — le vrai gisement
        trouves += [(n, n) for n in ENVELOPPE.findall(contenu)]
        #: [!] retirer d'abord la PROSE : les commandes de texte contiennent des \emph{...} contiennent des
        #: MOTS et des identifiants de CODE, pas des notations. Sans ça l'outil signale « five », « its »,
        #: « relation »... et noie les vraies trouvailles (mesuré : 50 alarmes
        #: sur 73 notations, dont la moitié étaient des mots anglais).
        sans_prose = PROSE.sub(' ', contenu)
        sans_macro = MACRO.sub(' ', sans_prose)
        trouves += [(n, n) for n in NU.findall(sans_macro)]
        for affiche, nom in trouves:
            if not tout and nom in STANDARD:
                continue
            if affiche not in premiere:
                premiere[affiche] = no
            occurrences.setdefault(affiche, []).append(no)
    res = []
    for nom, no in premiere.items():
        #: ⚠️ LE TEST QUI COMPTE. « un indice d'introduction existe plus haut dans
        #: le document » ne prouve RIEN sur CETTE notation-ci : les « := » et les
        #: « denote » sont partout. La première version classait ainsi 73
        #: notations sur 73 en « OK » — un rapport qui ne dit jamais rien.
        #: On exige que la notation elle-même figure sur une ligne portant un
        #: indice (à une ligne près, les formules débordant souvent).
        introduites = [i for i in occurrences[nom]
                       if any(abs(i - j) <= 1 for j in indices)]
        if not introduites:
            etat, ou = 'JAMAIS', 0
        elif min(introduites) > no + FENETRE:
            etat, ou = 'APRES', min(introduites)
        else:
            etat, ou = 'OK', min(introduites)
        res.append((etat, nom, no, ou))
    ordre = {'JAMAIS': 0, 'APRES': 1, 'OK': 2}
    res.sort(key=lambda r: (ordre[r[0]], r[2]))
    return res


def main(argv):
    tout = '--tout' in argv
    fichiers = [a for a in argv if not a.startswith('--')]
    if not fichiers:
        print(__doc__.splitlines()[0])
        print('usage : python article/scripts/notations.py <fichier.tex> [...]')
        return 1
    for f in fichiers:
        res = analyse(f, tout)
        alarmes = [r for r in res if r[0] in ('JAMAIS', 'APRES')]
        print('=' * 74)
        print(' %s  —  %d notations, %d a examiner' % (f, len(res), len(alarmes)))
        print('=' * 74)
        for etat, nom, no, ou in alarmes:
            detail = ('introduite l.%d' % ou) if etat == 'APRES' else 'aucun indice'
            print('  %-7s %-18s 1re utilisation l.%-5d %s'
                  % (etat, nom, no, detail))
        if not alarmes:
            print('  (rien a examiner)')
        print('  -> APRES et JAMAIS sont des PISTES : la liste STANDARD exempte les')
        print('     notations usuelles, le reste demande un jugement humain.')
        print('')
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
