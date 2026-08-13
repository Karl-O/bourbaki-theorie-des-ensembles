#!/usr/bin/env python3
"""Manifestes de couverture livre : un ``LIVRE.md`` PAR DOSSIER + remontée racine.

But (exigé par l'utilisateur, 2026-07-04). Chaque dossier de ``bourbaki/`` reçoit
un fichier ``LIVRE.md`` généré qui répond localement à « qu'est-ce qui est calé
sur le livre ici, et qu'est-ce qui ne l'est pas ? » :

  * les notions annotées ``@livre``, triées par PAGE IMPRIMÉE du livre (le
    repère « E III.10 » en haut de page) puis par lignes ;
  * les fichiers SANS marqueur (= pas encore calés — les ``__init__.py`` et
    ``outil_*.py``, hors-livre par convention, sont exclus du reproche) ;
  * le cumul des sous-dossiers (roll-up), remonté récursivement jusqu'à
    ``bourbaki/LIVRE.md`` qui donne, par chapitre, les pages du livre couvertes
    et les pages MANQUANTES entre la première et la dernière annotée.

*La citation est le détecteur de trous* : le manifeste racine dit honnêtement
si « on n'a rien oublié » — et sinon, où.

Usage :
    python outils_ia/audit/gen_livre_manifestes.py [racine=bourbaki]

Régénération idempotente : chaque LIVRE.md est réécrit entièrement (ne pas
éditer à la main). Les LIVRE.md ne comptent PAS dans la règle « ≤10 entrées
par dossier » (fichiers générés).
"""
from __future__ import annotations

import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
from gen_trous_livre import _RE, _RE_ITEM, _ORDRE_CHAP, _notion_suivante  # noqa: E402

# Page imprimée depuis le repère : « E III.10 » / « E.R.28 » / « E II.18-19 ».
_RE_PAGE = re.compile(r"E[.\s]*(?P<liv>R|[IVX]+)[.\s]*(?P<p1>\d+)(?:-(?P<p2>\d+))?")

HORS_LIVRE = re.compile(r"^(__init__|outil_.*|assemblage)\.py$")  # façades/ingénierie


class Notion:
    __slots__ = ("chap", "sec", "type", "num", "repere", "l1", "l2",
                 "livre", "page", "page2", "fichier", "nom")

    def __init__(self, m, fichier, nom, avec_lignes):
        self.chap, self.sec = m["chap"], m["sec"]
        self.type, self.num = m["type"], m["num"]
        self.repere = m["repere"].strip()
        self.l1 = int(m["l1"]) if avec_lignes else None
        self.l2 = int(m["l2"]) if avec_lignes else None
        pg = None
        for pg in _RE_PAGE.finditer(self.repere):   # garde la DERNIÈRE occurrence
            pass
        self.livre = pg["liv"] if pg else "?"
        self.page = int(pg["p1"]) if pg else 0
        self.page2 = int(pg["p2"]) if pg and pg["p2"] else self.page
        self.fichier = fichier
        self.nom = nom

    @property
    def cle_tri(self):
        return (_ORDRE_CHAP.get(self.livre, 99), self.page,
                self.l1 if self.l1 is not None else 0)

    @property
    def lignes(self):
        return f"L.{self.l1}-{self.l2}" if self.l1 is not None else "(item)"


def scanner_fichier(f: Path) -> tuple[list[Notion], list[str]]:
    """(notions parsées, marqueurs bruts non conformes) d'un .py."""
    notions, rebelles = [], []
    lignes = f.read_text(encoding="utf-8").splitlines()
    for i, l in enumerate(lignes):
        # tentative de marqueur = « @livre Ch.… » ; une simple MENTION de
        # @livre dans la prose d'un commentaire n'est pas comptée.
        if not re.search(r"@livre\s+Ch\.", l):
            continue
        m = _RE.search(l)
        if m:
            notions.append(Notion(m, f, _notion_suivante(lignes, i), True))
            continue
        m = _RE_ITEM.search(l)
        if m:
            notions.append(Notion(m, f, _notion_suivante(lignes, i), False))
        else:
            rebelles.append(f"{f.name}:{i + 1}: {l.strip()[:90]}")
    return notions, rebelles


class Dossier:
    """Agrégat d'un dossier : contenu propre + cumul des enfants."""

    def __init__(self, chemin: Path):
        self.chemin = chemin
        self.notions: list[Notion] = []          # fichiers de CE dossier
        self.a_caler: list[str] = []             # .py sans @livre (hors façades)
        self.rebelles: list[str] = []
        self.enfants: list[Dossier] = []

    # cumuls récursifs -------------------------------------------------------
    def cum_notions(self):
        return self.notions + [n for e in self.enfants for n in e.cum_notions()]

    def cum_a_caler(self):
        return len(self.a_caler) + sum(e.cum_a_caler() for e in self.enfants)

    def cum_rebelles(self):
        return len(self.rebelles) + sum(e.cum_rebelles() for e in self.enfants)

    def pages_par_livre(self):
        """{livre (I..IV,R): ensemble des pages imprimées couvertes (cumul)}."""
        pages: dict[str, set[int]] = {}
        for n in self.cum_notions():
            pages.setdefault(n.livre, set()).update(range(n.page, n.page2 + 1))
        return pages

    def pages_texte_par_livre(self):
        """Comme pages_par_livre mais SANS les marqueurs de type Ex (exemples/
        exercices) : sert à borner l'intervalle du détecteur de trous — un
        ancrage honnête dans les pages d'EXERCICES (ex. ω_α en E III.87) ne doit
        pas faire apparaître les pages d'exercices comme « manquantes »."""
        pages: dict[str, set[int]] = {}
        for n in self.cum_notions():
            if n.type == "Ex":
                continue
            pages.setdefault(n.livre, set()).update(range(n.page, n.page2 + 1))
        return pages


def construire(racine: Path) -> Dossier:
    d = Dossier(racine)
    for entree in sorted(racine.iterdir()):
        if entree.name == "__pycache__":
            continue
        if entree.is_dir():
            d.enfants.append(construire(entree))
        elif entree.suffix == ".py":
            notions, rebelles = scanner_fichier(entree)
            d.notions.extend(notions)
            d.rebelles.extend(rebelles)
            if not notions and not HORS_LIVRE.match(entree.name):
                d.a_caler.append(entree.name)
    return d


def _plages(pages: set[int]) -> str:
    """{2,3,4,7} -> '2-4, 7'."""
    out, xs = [], sorted(pages)
    while xs:
        a = b = xs.pop(0)
        while xs and xs[0] == b + 1:
            b = xs.pop(0)
        out.append(f"{a}-{b}" if b > a else f"{a}")
    return ", ".join(out)


def _manquantes(pages: set[int], borne: set[int] | None = None) -> set[int]:
    """Pages absentes de `pages` dans l'intervalle [min, max] de `borne`
    (par défaut : de `pages` elle-même)."""
    ref = borne if borne else pages
    return set(range(min(ref), max(ref) + 1)) - pages if ref else set()


def ecrire_manifeste(d: Dossier, racine: Path) -> None:
    rel = d.chemin.relative_to(racine.parent).as_posix()
    out = [f"# LIVRE — couverture livre de `{rel}`", "",
           "> Généré par `python outils_ia/audit/gen_livre_manifestes.py` — NE PAS ÉDITER À LA MAIN.",
           "> Page livre = pagination imprimée en haut de page (repère « E III.10 »), pas la page du PDF.", ""]

    if d.notions:
        out += ["## Notions de ce dossier (calées sur le livre)", "",
                "| Page livre | Lignes | § | Type | Notion | Fichier |",
                "|---|---|---|---|---|---|"]
        for n in sorted(d.notions, key=lambda n: n.cle_tri):
            out.append(f"| E {n.livre}.{n.page}"
                       + (f"-{n.page2}" if n.page2 != n.page else "")
                       + f" | {n.lignes} | {n.sec} | {n.type}.{n.num}"
                         f" | `{n.nom}` | `{n.fichier.name}` |")
        out.append("")

    if d.a_caler:
        out += ["## Fichiers À CALER (aucun `@livre`)", ""]
        out += [f"- `{f}`" for f in d.a_caler] + [""]

    if d.rebelles:
        out += ["## Marqueurs NON CONFORMES (à corriger)", ""]
        out += [f"- `{r}`" for r in d.rebelles] + [""]

    if d.enfants:
        out += ["## Sous-dossiers (cumul)", "",
                "| Dossier | Notions | À caler | Non conformes | Pages livre |",
                "|---|---|---|---|---|"]
        for e in d.enfants:
            pg = e.pages_par_livre()
            desc = " ; ".join(f"E {liv}: {_plages(ps)}"
                              for liv, ps in sorted(pg.items(),
                              key=lambda kv: _ORDRE_CHAP.get(kv[0], 99)))
            out.append(f"| `{e.chemin.name}/` | {len(e.cum_notions())} "
                       f"| {e.cum_a_caler()} | {e.cum_rebelles()} | {desc or '—'} |")
        out.append("")

    # bilan cumulé (le « remonté jusqu'en haut »)
    cn, ca, cr = d.cum_notions(), d.cum_a_caler(), d.cum_rebelles()
    out += ["## Bilan cumulé (ce dossier + descendants)", "",
            f"- Notions calées : **{len(cn)}**",
            f"- Fichiers à caler : **{ca}**",
            f"- Marqueurs non conformes : **{cr}**"]
    txt = d.pages_texte_par_livre()
    for liv, ps in sorted(d.pages_par_livre().items(),
                          key=lambda kv: _ORDRE_CHAP.get(kv[0], 99)):
        mq = _manquantes(ps, txt.get(liv))
        ligne = f"- Livre **E {liv}** : pages couvertes {_plages(ps)}"
        ligne += (f" — **pages manquantes : {_plages(mq)}**" if mq
                  else " — aucune page manquante dans l'intervalle")
        out.append(ligne)
    verdict = ("RIEN D'OUBLIÉ (sur l'intervalle annoté)"
               if not ca and not cr and
               not any(_manquantes(ps, txt.get(liv))
                       for liv, ps in d.pages_par_livre().items())
               else "COUVERTURE INCOMPLÈTE — voir ci-dessus")
    out += ["", f"**Verdict : {verdict}**", ""]

    (d.chemin / "LIVRE.md").write_text("\n".join(out), encoding="utf-8")
    for e in d.enfants:
        ecrire_manifeste(e, racine)


def main(argv: list[str]) -> int:
    racine = Path(argv[0]) if argv else Path("bourbaki")
    if not racine.exists():
        print(f"racine introuvable : {racine}", file=sys.stderr)
        return 2
    arbre = construire(racine)
    ecrire_manifeste(arbre, racine)
    n_manifestes = sum(1 for _ in racine.rglob("LIVRE.md"))
    cn = arbre.cum_notions()
    print(f"{n_manifestes} manifestes LIVRE.md écrits — "
          f"{len(cn)} notions, {arbre.cum_a_caler()} fichiers à caler, "
          f"{arbre.cum_rebelles()} marqueurs non conformes")
    txt = arbre.pages_texte_par_livre()
    for liv, ps in sorted(arbre.pages_par_livre().items(),
                          key=lambda kv: _ORDRE_CHAP.get(kv[0], 99)):
        mq = _manquantes(ps, txt.get(liv))
        print(f"  Livre E {liv} : couvert {_plages(ps)}"
              + (f" | MANQUE {_plages(mq)}" if mq else " | complet sur l'intervalle"))
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
