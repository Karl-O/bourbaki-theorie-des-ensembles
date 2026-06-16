import sys, os
sys.path.insert(0, os.path.dirname(__file__))


def pytest_configure(config):
    # marqueur « slow » : théorèmes lourds (τ-cardinaux imbriqués, N_existe / Prop 8).
    config.addinivalue_line("markers", "slow: test lent (cardinaux profonds, N_existe)")
