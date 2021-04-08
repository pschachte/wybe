from complex.utils import *


# Multiple specialization and CTGC with dead cell reusing
@test_case
def int_list(ctx: Context) -> None:
    ctx.save_file("int_list.wybe", WYBE_INT_LIST)
    ctx.save_file("int_list_test.wybe", WYBE_INT_LIST_TEST)
    # build & execute without multiple specialization
    _ = ctx.wybe_build_target("int_list_test", False, False,
                              check=True, no_multi_specz=True)
    _, output = ctx.execute_program("./int_list_test", check=True)
    ctx.write_section("build & execute without multiple specialization", output)

    # build & execute with multiple specialization
    _,final_dump = ctx.wybe_build_target("int_list_test", force_all=True,
                                         final_dump=True, check=True)
    _, output = ctx.execute_program("./int_list_test", check=True)
    ctx.write_section("build & execute with multiple specialization", output)
    ctx.write_section("final dump (with multiple specialization)", final_dump)


WYBE_INT_LIST = r"""
# contains the def of a int list and some helper functions
# (similar to the python list)
pub type int_list { pub [] | [|](head:int, tail:int_list) }


pub def print(x:int_list) use !io {
    if { x = [ ?h | ?t] :: 
        !print(h)
        !print(' ')
        !print(t)
    }
}


pub def println(x:int_list) use !io {
    !print(x)
    !nl
}


# Returns an `int_list`, starting from `start`, and increments by `step`,
# and stops before `stop`
pub def range(start:int, stop:int, step:int, ?result:int_list) {
    ?result = []
    do {
        while start < stop
        ?result = [start | result]
        ?start = start + step
    }
    reverse(!result)
}

# Add an item to the end of the list.
pub def append(lst:int_list, v: int):int_list = extend(lst, [v])


# Extend the first list by appending all the items from the second list.
pub def extend(lst1:int_list, lst2:int_list):int_list = 
    if {lst1 = [?h | ?t]:: [h | extend(t, lst2)] | else:: lst2 }


# Insert an item at a given position.
pub def insert(lst:int_list, idx:int, v:int):int_list = 
    if {idx = 0::
        [v | lst]
    | else::
        if {lst = [?h | ?t]::
            [h | insert(t, idx-1, v)]
        | else::
            # list not long enough
            insert(lst, idx-1, v)
        }
    }


# Remove the first item from the list whose value is equal to v.
pub def remove(lst:int_list, v:int):int_list =
    if {lst = [?h | ?t]::
        if h = v::
            t
        | else::
            [h | remove(t, v)]
        }
    | else::
        []
    }

# Remove the item at the given position in the list
pub def pop(lst:int_list, idx:int):int_list = 
    if {lst = [?h | ?t]::
        if {idx = 0::
            t
        | else::
            [h | pop(t, idx-1)]
        }
    | else::
        []
    }


# Return the number of times x appears in the list.
pub def count(lst:int_list, x:int):int =
    if {lst = [?h | ?t]::
        count(t, x) + if {h = x:: 1 | else:: 0}
    | else::
        0
    }

# Return zero-based index in the list of the first item whose value is equal to x.
pub def index(lst:int_list, x:int):int = index_helper(lst, 0, x)

def index_helper(lst:int_list, idx:int, x:int):int = 
    if {lst = [?h | ?t]::
        if {h = x::
            idx
        | else::
            index_helper(t, idx+1, x)
        }
    | else::
        -1
    }


# Sort the items of the list
pub def sort(lst:int_list):int_list =
    if {lst = [?h | ?t]::
        extend(sort(lesser(t, h)), [h | sort(greater(t, h))])
    | else::
        []
    }

def lesser(lst:int_list, v:int):int_list =
    if {lst = [?h | ?t]::
        if {h < v::
            [h | lesser(t, v)]
        | else::
            lesser(t, v)
        }
    | else::
        []
    }

def greater(lst:int_list, v:int):int_list =
    if {lst = [?h | ?t]::
        if {h >= v::
            [h | greater(t, v)]
        | else::
            greater(t, v)
        }
    | else::
        []
    }


# Reverse the elements of the list.
pub def reverse(lst:int_list):int_list = reverse_helper(lst, [])

def reverse_helper(lst:int_list, acc:int_list):int_list =
    if {lst = [?h | ?t]:: reverse_helper(t, [h|acc]) | else:: acc}
"""

WYBE_INT_LIST_TEST = """
use int_list


def test_int_list(x:int_list, y:int_list, z:int_list) use !io {
    reverse(!x)
    reverse(!z)
    ?y = append(y, 99)
    !println("-")
    !println(x)
    !println(y)
    !println(z)

    ?l = extend(x, y)
    ?l = extend(l, z)
    !println("-")
    !println(l)

    ?l = insert(l, 4, 78)
    ?l = pop(l, 20)
    ?l = remove(l, 2)
    !println("-")
    !println(l)

    sort(!l)
    !println("-")
    !println(l)
}

# build list
!malloc_count(?mc1)
?x = range(1, 10, 1)
?y = range(2, 20, 2)
?z = range(3, 30, 3)
!println("x y z:")
!println(x)
!println(y)
!println(z)
!malloc_count(?mc2)
?mc_build = mc2 - mc1



!println("--------------------")
!println("tests with alias")
!malloc_count(?mc1)
!test_int_list(x, y, z)
!malloc_count(?mc2)
?mc_test_aliased = mc2 - mc1
!println("original x y z:")
!println(x)
!println(y)
!println(z)
!println("--------------------")


!println("--------------------")
!println("tests without alias")
!malloc_count(?mc1)
!test_int_list(x, y, z)
!malloc_count(?mc2)
?mc_test_not_aliased = mc2 - mc1
!println("--------------------")


!print(" ** malloc count of building lists: ")
!println(mc_build)
!print(" ** malloc count of test(aliased): ")
!println(mc_test_aliased)
!print(" ** malloc count of test(non-aliased): ")
!println(mc_test_not_aliased)

"""


# Multiple specialization and CTGC with destructive mutate instruction
@test_case
def drone(ctx: Context) -> None:
    ctx.save_file("drone.wybe", WYBE_DRONE)
    # build & execute without multiple specialization
    _ = ctx.wybe_build_target("drone", False, False,
                              check=True, no_multi_specz=True)
    _, output = ctx.execute_program("./drone", check=True, input=WYBE_DRONE_IN)
    ctx.write_section("build & execute without multiple specialization", output)

    # build & execute with multiple specialization
    _,final_dump = ctx.wybe_build_target("drone", force_all=True,
                                         final_dump=True, check=True)
    _, output = ctx.execute_program("./drone", check=True, input=WYBE_DRONE_IN)
    ctx.write_section("build & execute with multiple specialization", output)
    ctx.write_section("final dump (with multiple specialization)", final_dump)


WYBE_DRONE = r"""
type drone_info { pub drone_info(x:int, y:int, z:int, count:int) }

def drone_init():drone_info = drone_info(0, 0, 0, 0)

def print_info(d:drone_info) use !io {
    !print("(")
    !print(x(d))
    !print(", ")
    !print(y(d))
    !print(", ")
    !print(z(d))
    !print(") #")
    !print(count(d))
    !nl
}

def do_action(!d:drone_info, action:char, ?success:bool) {
    ?success = true
    if { action = 'n' ::
        y(!d, y(d)-1)
    | action = 's' ::
        y(!d, y(d)+1)
    | action = 'w' ::
        x(!d, x(d)-1)
    | action = 'e' ::
        x(!d, x(d)+1)
    | action = 'u' ::
        z(!d, z(d)+1)
    | action = 'd' ::
        z(!d, z(d)-1)
    | otherwise ::
        ?success = false
    }
    if { success ::
        count(!d, count(d)+1)
    }
}

def loop(d:drone_info, ch:char) use !io {
    if { ch ~= ' ' && ch ~= '\n' ::
        if { ch = 'p' ::
            !print_info(d)
        | otherwise ::
            do_action(!d, ch, ?success)
            if { success = false ::
                !println("invalid action!")
            }
        }
    }
    !read(?ch:char)
    if { ch ~= eof ::
        !loop(d, ch)
    }
}

?d = drone_init()
!read(?ch:char)
if { ch ~= eof ::
    !loop(d, ch)
}
!malloc_count(?mc)
!print("** malloc count: ")
!println(mc)

# XXX: does not work due to https://github.com/pschachte/wybe/issues/87
# ?d = drone_init()
# do {
#     !read(?ch:char)
#     until ch = eof
#     if { ch ~= ' ' && ch ~= '\n' ::
#         if { ch = 'p' ::
#             !print_info(d)
#         | otherwise ::
#             do_action(!d, ch, ?success)
#             if { success = false ::
#                 !println("invalid action!")
#             }
#         }
#     }
# }
"""

WYBE_DRONE_IN = """
p
uuuuewunwundwensssneuudwnuwnsnuddwndunwusnnwewwenssdddweusdsenddndenwsnudueuuuewwddenneedsdsuedusnwu
p
"""
