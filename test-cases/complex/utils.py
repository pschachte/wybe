from io import TextIOWrapper
import os

TEST_CASES = []

def test_case(func) -> None:
    # register test case
    filename = os.path.basename(func.__globals__['__file__'])
    TEST_CASES.append((func.__name__, filename, func))
    return func

class Context:
    def __init__(self, tmp_dir: str, out_file: TextIOWrapper) -> None:
        self.tmp_dir = tmp_dir
        self.out_file = out_file

    def write_section(self, section_name: str, data: str) -> None:
        self.out_file.write("-" * 70 + "\n")
        self.out_file.write("- " + section_name + "\n")
        self.out_file.write("-" * 70 + "\n")
        self.out_file.write(data)
        self.out_file.write("\n")
        self.out_file.write("-" * 70 + "\n\n\n")

