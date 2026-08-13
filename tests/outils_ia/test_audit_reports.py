# -*- coding: utf-8 -*-
"""Tests — outil d'audit des reports périmés (outils_ia/audit/audit_reports.py)."""
import importlib.util
import pathlib

_SRC = pathlib.Path(__file__).resolve().parents[2] / "outils_ia" / "audit" / "audit_reports.py"
_spec = importlib.util.spec_from_file_location("audit_reports", _SRC)
audit = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(audit)


def test_repere_inclut_la_section():
    """Un repère cité sans section n'est jamais localisable (silence prudent)."""
    assert audit.repere_du_report("Proposition 5 : blabla") is None
    assert audit.repere_du_report("Proposition 5 (§III.7.4) : x") == ("III", "7.4", "Prop", "5")


def test_sections_distinctes_ne_matchent_pas():
    """🎯 La section fait partie de la clé : Prop.5 de §III.7.4 ≠ Prop.5 de §III.1."""
    a = audit.repere_du_report("Proposition 5 (§III.7.4) : x")
    b = audit.repere_du_report("Proposition 5 (§III.1) : y")
    assert a != b


def test_audit_tourne_sur_le_depot():
    """L'audit s'exécute sur le dépôt réel et trouve des reports."""
    assert len(audit.collecte_reports()) > 0
    assert len(audit.index_livre()) > 0
    assert audit.main([]) == 0
