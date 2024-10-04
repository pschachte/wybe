from complex.utils import *

WYBE_QUINE:str = r"""["[","]=?L;?q=34:char;if{L=[?a,?b|_]::for _ in L{!print a;!print q};!print',';for _ in L{!print q;!print b}}"]=?L;?q=34:char;if{L=[?a,?b|_]::for _ in L{!print a;!print q};!print',';for _ in L{!print q;!print b}}"""

@test_case
def quine(ctx: Context) -> None:
    ctx.save_file("quine.wybe", WYBE_QUINE)
    _ = ctx.wybe_build_target("quine", False, False, check=True)
    _, output = ctx.execute_program("./quine", check=True)
    ctx.write_section("program - output", "\n".join([WYBE_QUINE, output]))

    assert WYBE_QUINE == output

