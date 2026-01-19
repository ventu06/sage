import subprocess

import pytest

from sage.interfaces.gap import gap
from sage.interfaces.gp import gp
from sage.interfaces.interface import Interface
from sage.interfaces.kash import kash
from sage.interfaces.magma import magma
from sage.interfaces.mathematica import mathematica
from sage.interfaces.maxima import maxima
from sage.interfaces.octave import octave
from sage.interfaces.singular import singular

COERCION_CASES = [
    pytest.param(gp, "PARI/GP interpreter", id="gp"),
    pytest.param(gap, "Gap", id="gap"),
    pytest.param(maxima, "Maxima", id="maxima"),
    pytest.param(singular, "Singular", id="singular"),
]


@pytest.mark.parametrize(
    ("interface", "expected_parent"),
    COERCION_CASES,
)
def test_coercions(interface: Interface, expected_parent: str):
    result = 2 * interface("2")

    assert result == 4
    assert str(result.parent()) == expected_parent


STDERR_COMMANDS = [
    pytest.param("gap", {0, 1}, id="gap"),
    pytest.param("gp", {0}, id="gp"),
    pytest.param("ipython", {0, 1, 120}, id="ipython"),
    pytest.param("Singular", {0}, id="singular"),
]


@pytest.mark.parametrize("command, acceptable_exit_codes", STDERR_COMMANDS)
def test_stderr_write_errors_are_handled(command, acceptable_exit_codes):
    exit_code = subprocess.call(
        "syntax error", executable=command
    )
    assert exit_code in acceptable_exit_codes


MANYVARS_INTERFACES = [
    pytest.param(kash, id="kash"),
    pytest.param(magma, id="magma"),
    pytest.param(octave, id="octave"),
    pytest.param(maxima, id="maxima"),
    pytest.param(mathematica, id="mathematica"),
    pytest.param(singular, id="singular"),
]

@pytest.mark.slow
@pytest.mark.parametrize("interface", MANYVARS_INTERFACES)
def test_manyvars(interface):
    """
    Test that > 65,000 variable names works in each system.
    """
    try:
        interface("1")
    except Exception:
        pytest.skip(f"{interface} is not available")

    num = 70000
    result = []
    for i in range(num):
        name = f"v{i}"
        result.append(interface(name))
