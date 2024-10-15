import os
import sys
import tempfile
import traceback
import subprocess
from complex import utils


def main() -> None:
    # set work directory
    root_path = os.path.dirname(os.path.realpath(__file__))
    os.chdir(root_path)
    failed_cases = []
    new_cases = []

    for test_func_name, test_file, test_func in utils.TEST_CASES:
        test_name = "{}-{}".format(os.path.splitext(test_file)[0], test_func_name)
        # write an empty wybe file as a placeholder for "update-exp"
        with open("./complex/exp/{}.wybe".format(test_name), "w") as f:
            f.write("# Complex test case: {} File: {}\n".format(
                test_name, test_file))

        out_file_path = "./complex/exp/{}.out".format(test_name)
        exp_file_path = "./complex/exp/{}.exp".format(test_name)
        with open(out_file_path, "w") as out_file:
            with tempfile.TemporaryDirectory() as tmp_dir:
                ctx = utils.Context(tmp_dir, os.path.dirname(root_path), out_file)
                # execute test case
                try:
                    test_func(ctx)
                except Exception as _:
                    ctx.write_section(
                        "Error occurred during test execution", traceback.format_exc())
        # diff results
        if not os.path.exists(exp_file_path):
            new_cases.append(out_file_path)
            print("[31m?[39m", end="")
        else:
            # XXX For now, we use "diff" and "dwdiff" in shell to match
            # the behavior of other scripts. We should consider using
            # things like "filecmp.cmp" for portability and efficiency.
            code = subprocess.run(
                ["diff", "-q", 
                    "-I", "^source_filename *=.*",
                    "-I", "^target triple *=.*", 
                    out_file_path, exp_file_path],
                stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL).returncode
            if code == 0:
                print(".", end="")
            else:
                failed_cases.append(out_file_path)
                subprocess.run("dwdiff -c -d '()<>~!@:?.%#' '{}' '{}' >> ../ERRS 2>&1".format(
                    exp_file_path, out_file_path), shell=True)
                print("[31mX[39m", end="")
    print()

    if failed_cases:
        print("Failed:")
        for c in failed_cases:
            print("    ", c)
        print("\nSee ERRS for differences.")
        sys.exit(1)
    else:
        print("ALL TESTS PASS")
    
    if new_cases:
        print("New tests:")
        for c in new_cases:
            print("    ", c)
        print("\nDo .\\update-exp to specify expected output")

if __name__ == "__main__":
    main()
