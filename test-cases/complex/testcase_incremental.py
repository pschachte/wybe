from complex.utils import *


@test_case
def case_1(ctx: Context) -> None:
    # dependency graph can be found here: https://github.com/pschachte/wybe/issues/68
    # write codes
    ctx.save_file("main.wybe", WYBE_MAIN)
    ctx.save_file("top.wybe", WYBE_TOP)
    ctx.save_file("ca.wybe", WYBE_CA)
    ctx.save_file("cb.wybe", WYBE_CB_1)
    ctx.save_file("down.wybe", WYBE_DOWN_1)
    # first build
    _ = ctx.wybe_build_target("main", False, False, check=True)
    # first execute
    _, output = ctx.execute_program("./main", check=True)
    ctx.write_section("first execution", output)
    # record current files
    ctx.update_files_hash(["main.o", "top.o", "ca.o", "cb.o", "down.o"])

    ctx.write_note("Rebuild, everything should be reused")
    _ = ctx.wybe_build_target("main", False, False, check=True)
    assert not ctx.is_file_changed("main.o", update_hash=True)
    assert not ctx.is_file_changed("top.o", update_hash=True)
    assert not ctx.is_file_changed("ca.o", update_hash=True)
    assert not ctx.is_file_changed("cb.o", update_hash=True)
    assert not ctx.is_file_changed("down.o", update_hash=True)

    ctx.write_note(
        "Change comments in cb.wybe. main.o, top.o, down.o should be reused")
    ctx.save_file("cb.wybe", WYBE_CB_2)
    _ = ctx.wybe_build_target("main", False, False, check=True)
    # XXX Currently main.o and top.o are changed. Fix this later.
    # assert not ctx.is_file_changed("main.o", update_hash=True)
    # assert not ctx.is_file_changed("top.o", update_hash=True)
    assert not ctx.is_file_changed("down.o", update_hash=True)
    _, output = ctx.execute_program("./main", check=True)
    ctx.write_section("second execution", output)


    ctx.write_note(
        "Change a inline proc in down.wybe, final executable should contain this change.")
    ctx.save_file("down.wybe", WYBE_DOWN_2)
    _ = ctx.wybe_build_target("main", False, False, check=True)
    _, output = ctx.execute_program("./main", check=True)
    ctx.write_section("third execution", output)


WYBE_MAIN = """
use top

!c_test() 
!down_test()
"""

WYBE_TOP = """
use down, ca

pub def c_test() use !io {
    ?a = position(0, 1)
    ?b = position(0, 2)
    !println("=============")
    !foo1(a, b, 3)
}

pub def down_test() use !io {
    !println("=============")
    !inline_test()
}
"""

WYBE_CA = """
use cb

pub type position { pub position(x:int, y:int) }

pub def printPosition(pos:position) use !io {
    !print(" (")
    !print(pos^x)
    !print(",")
    !print(pos^y)
    !println(")")
}

pub def modifyAndPrint(pos:position, v:int) use !io {
    x(!pos, v)
    !printPosition(pos)
}

pub def foo1(x1:position, x2:position, n:int) use !io {
    ?n = n - 1
    if { n < 0 :: 
            !modifyAndPrint(x1, 111)
            !modifyAndPrint(x2, 222)
        | otherwise ::
            !foo2(x2, x1, n)
    }
}
"""

WYBE_CB_1 = """
use ca, down

pub def foo2(x1:position, x2:position, n:int) use !io {
    ?n = n - 1
    !inline_test()
    if { n < 0 :: 
            !modifyAndPrint(x1, 111)
            !modifyAndPrint(x2, 222)
        | otherwise ::
            !foo1(x2, x1, n)
    }
}
"""

WYBE_CB_2 = WYBE_CB_1 + "\n # random comments\n"

WYBE_DOWN_1 = """
pub def inline_test() use !io {
    !println("[Down] inline test.")
}
"""

WYBE_DOWN_2 = """
pub def inline_test() use !io {
    !println("[Down] inline test. Updated.")
}
"""
