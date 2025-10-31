# Naive reverse benchmark

We evaluate the efficiency of reversing a linked list by repeatedly appending
the first element of a list to the end of a reversed list.  Since the cost of
append is linear in the length of the first list, this algorithm is quadratic.
Obviously a list can be reversed in linear time in any of these languages; the
point of this benchmark is to repeatedly chase down a list and add to the end.

These test programs are designed to test each language's ability to implement a
linked list type and some basic operations, so we avoid using any language's
built-in list type.

There may be multiple versions of this benchmark for each language:

  1. `nrev`: a recursive implementation of all algorithms
  2. `nrev_destr`: where possible, an iterative implementation that
      repeatedly destructively appends each element to the end of the list.

Each test program name begins with the language name and follows with one of the
above suffixes.

Because they create so many garbage list cells that the program runs out of
memory, the C versions use the Boehm–Demers–Weiser garbage collector for memory
management (the same GC used by Wybe).  In the case of C, there is also a
`c_nrev_fast` version, which is the same as `c_nrev_destr`, except that it
instead uses the standard `malloc` function.
