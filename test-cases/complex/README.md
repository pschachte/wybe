# Complex Tests

A generic testing framework for Wybe written in Python.
Similar to *execution tests* and *final-dump tests*, each test case generates an output which will be compared with an expected value.
However, Python script is used to describe test cases of *complex test*.
So one can use it to simulate much more complex use cases.

## Writing a complex test case

Create a new python file under `/test-cases/complex/` using the template below:

```python
from complex.utils import *

@test_case
def case_1(ctx: Context) -> None:
    # Add script here
    pass
```
File name and function name can be arbitrary and each test case will be named as `{file_name}-{func_name}`.
A file can contain multiple test cases, the `@test_case` decorator is used to distinguish test function from normal function.

Each test case is executed with a brand new temp directory.
The argument `ctx` contains information such as the temp directory and provides many helper functions. One should always try to use those functions.
For more detail, please check out existing test cases and the definition of class `Context` in `/test-case/complex/utils.py`.

To include something in the output, `ctx.write_section(title, data)` and `ctx.write_note(data)` can be used.
Also, any exception raised during the execution will be added into the output, so things like `assert` can be used for some simple check.

Do not write to the `stdout` and `stderr` (using `print()`). 

Expected outputs are stored as `/test-case/complex/exp/{file_name}-{func_name}.exp`. `./update-exp` can still be used.
