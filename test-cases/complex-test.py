import os
import tempfile
from complex import utils


def main() -> None:
    # set work directory
    root_path = os.path.dirname(os.path.realpath(__file__))
    os.chdir(root_path)

    for test_name, test_file, test_func in utils.TEST_CASES:
        # write an empty wybe file as a placeholder for "update-exp"
        with open("./complex/exp/{}.wybe".format(test_name), "w") as f:
            f.write("# Complex test case: {} File: {}\n".format(
                test_name, test_file))

        # with open("./complex/exp/{}.out".format)
        # with tempfile.TemporaryDirectory() as tmp_dir:
        #     print(tmp_dir)


if __name__ == "__main__":
    main()
