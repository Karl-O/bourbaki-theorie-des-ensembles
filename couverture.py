"""Tableau de couverture — « a-t-on oublié quelque chose du livre ? »

Pour garantir la complétude, on confronte un INVENTAIRE des résultats nommés du
livre (extrait des 154 sections LaTeX de V7) à ce que V9 vérifie RÉELLEMENT par
le noyau. Les manques sont affichés explicitement : rien n'est masqué.

Honnêteté : on est au stade FONDATIONS — noyau strict + une poignée de théorèmes
dérivés. La très grande majorité des critères/théorèmes du livre reste à couvrir.
Ce tableau est la carte du chemin restant.

  python V9/couverture.py
"""
from __future__ import annotations

# ── Inventaire du livre (résultats NOMMÉS, miné depuis V7) ────────────────────
INVENTAIRE = {
    "S (schémas)": list(range(1, 9)),       # S1..S8
    "CS (substitution)": list(range(1, 13)),  # CS1..CS12
    "CF (formatifs)": list(range(1, 14)),     # CF1..CF13
    "C (critères logiques)": list(range(1, 64)),  # C1..C63
    "A (axiomes ensembles)": list(range(1, 5)),   # A1..A4
}

# ── Ce que V9 VÉRIFIE par le noyau (primitive sûre ou dérivée prouvée) ─────────
VERIFIE = {
    "S (schémas)": {1, 2, 3, 4, 5, 6, 7},      # primitives du noyau (S8 absent)
    "CS (substitution)": {1, 2, 3, 4, 5},        # identités d'assemblages (méta), test_criteres_CS
    "CF (formatifs)": set(range(1, 14)),          # CF1–CF13 complet (formation, couche lecture)
    # Phase A couverte (C7–C25, re-vérifiés par criteres_C.py) + fondations.
    "C (critères logiques)": {1, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18,
                              20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32,
                              33, 34, 35, 38, 39, 40, 41, 42, 43, 44},
    "A (axiomes ensembles)": set(),               # chap. II non entamé
}

# Réserves d'honnêteté sur certains critères « couverts » :
NOTES = {
    "C14": "primitive de confiance (= C6/déduction), non dérivée de S1–S4",
    "C23": "vérifié pour le cas négation seulement (5 équivalences au total)",
    "C23": "5/5 équivalences verrouillées (criteres_C + criteres_C_suite)",
    "C24": "11/13 équivalences verrouillées ; reste assoc-ou + 2 distributivités workflow-vérifiées (lock-in à finir)",
    "C25": "2/2 cas verrouillés",
    "C28": "verrouillé (dé-Morgan ∀/∃, par double négation)",
    "CS1–CS5": "méta-identités de substitution (pas des théorèmes noyau), vérifiées par égalité d'assemblages",
    "CF1–CF13": "critères de formation COMPLETS, vérifiés via la couche lecture (est_terme/est_relation)",
    "C30": "généralisé à un terme T quelconque (tactiques_egalite.instanciation), pas seulement T=x",
    "C43": "= littéralement le schéma S6 du noyau",
    "C29, C31": "DÉBLOQUÉS : congruence sous quantificateur (congruence_quantif.py), route ∃ directe via C30-général + témoin τx(R) + S5",
    "C32–C42": "VÉRIFIÉS (sauf C36/C37 métathéorèmes) grâce à la congruence. Verrouillés suite : C34,C35,C38-1. Workflow-vérifiés (lock-in à finir) : C32,C33,C38-2,C39,C40,C41,C42",
    "C36, C37": "métathéorèmes (R théorème de T∪{A} / T' contradictoire) — hors fragment objet",
    "C44": "substitutivité de = pour les termes, via réflexivité des termes composés (reflexivite_terme)",
    "RESTE chap. I": "C2–C5/C19/C36/C37 = métathéorèmes (transport/comparaison) hors fragment ; C45/C46 = univocité/fonctionnalité (machinerie lourde, à faire)",
    "C45/C46": "univocité/fonctionnalité — relations universellement quantifiées en hypothèse, infrastructure à étendre",
    "C9/C13/C15/C18/C22": "règles (prémisses→conséquent), vérifiées sur instances closes",
    "MANQUE C2–C5, C19": "métathéorèmes (transport de preuve / comparaison de théories) "
                          "hors du fragment objet du noyau ; nécessitent CS1–CS5",
}

# Théorèmes nommés dérivés et vérifiés (hors numérotation C/CS/CF).
THEOREMES_VERIFIES = [
    "Th1 réflexivité  x = x",
    "Th2 symétrie  (x=y) ⇒ (y=x)",
    "Th3 transitivité  ((x=y) et (y=z)) ⇒ (x=z)",
    "double négation  A⇒¬¬A, ¬¬A⇒A",
    "contraposition  (A⇒B) ⇒ (¬B⇒¬A)",
    "syllogisme  (A⇒B),(B⇒C) ⊢ A⇒C",
    "tiers exclu  A ∨ ¬A",
]


def rapport() -> str:
    lignes = ["TABLEAU DE COUVERTURE — Bourbaki, Théorie des ensembles", "=" * 56]
    tot_inv = tot_ok = 0
    for cat, items in INVENTAIRE.items():
        ok = VERIFIE.get(cat, set())
        manquants = [n for n in items if n not in ok]
        tot_inv += len(items); tot_ok += len(ok & set(items))
        pct = 100 * len(ok & set(items)) / len(items)
        lignes.append(f"\n{cat} : {len(ok & set(items))}/{len(items)} ({pct:.0f}%)")
        lignes.append(f"  vérifiés : {sorted(ok & set(items)) or '—'}")
        lignes.append(f"  MANQUE   : {manquants if manquants else '✓ complet'}")
    lignes.append("\n" + "-" * 56)
    lignes.append(f"Critères/schémas nommés : {tot_ok}/{tot_inv} "
                  f"({100*tot_ok/tot_inv:.0f}%)")
    lignes.append(f"Théorèmes nommés vérifiés (hors numérotation) : {len(THEOREMES_VERIFIES)}")
    for t in THEOREMES_VERIFIES:
        lignes.append(f"  ✓ {t}")
    lignes.append("\nRéserves d'honnêteté :")
    for k, v in NOTES.items():
        lignes.append(f"  • {k} : {v}")
    lignes.append("\nChapitre I (logique) : bien avancé. Chap. II–IV (ensembles, ordres,")
    lignes.append("cardinaux, structures) : non entamés — exigent d'étendre le noyau (∈, Coll…).")
    return "\n".join(lignes)


if __name__ == "__main__":
    print(rapport())
