from io import TextIOWrapper
import os
import sys
import hashlib
import re
from collections import defaultdict
import subprocess
from typing import *

TEST_CASES = []


def test_case(func) -> None:
    # register test case
    filename = os.path.basename(func.__globals__['__file__'])
    TEST_CASES.append((func.__name__, filename, func))
    return func


class Context:
    def __init__(self, tmp_dir: str, root_dir: str, out_file: TextIOWrapper) -> None:
        self.tmp_dir = tmp_dir
        self.root_dir = root_dir
        self.out_file = out_file
        self.files_hash = defaultdict(str)

    def write_section(self, section_name: str, data: str) -> None:
        self.out_file.write("-" * 70 + "\n")
        self.out_file.write("- " + section_name + "\n")
        self.out_file.write("-" * 70 + "\n")
        self.out_file.write(data)
        self.out_file.write("\n")
        self.out_file.write("-" * 70 + "\n\n\n")

    def write_note(self, note: str) -> None:
        self.out_file.write("-" * 70 + "\n")
        self.out_file.write(note + "\n")
        self.out_file.write("-" * 70 + "\n\n\n")

    def save_file(self, filename: str, data: str) -> None:
        with open(os.path.join(self.tmp_dir, filename), "w") as f:
            f.write(data)
    
    def delete_file(self, filename: str) -> None:
        os.remove(os.path.join(self.tmp_dir, filename))

    def _get_file_hash(self, filename: str) -> str:
        BUF_SIZE = 65536
        with open(os.path.join(self.tmp_dir, filename), 'rb') as f:
            sha1 = hashlib.sha1()
            while True:
                data = f.read(BUF_SIZE)
                if not data:
                    break
                sha1.update(data)
            return sha1.hexdigest()

    def update_files_hash(self, files: List[str]) -> None:
        for filename in files:
            hash = self._get_file_hash(filename)
            self.files_hash[filename] = hash

    def is_file_changed(self, filename: str, update_hash: bool) -> bool:
        hash = self._get_file_hash(filename)
        changed = self.files_hash[filename] != hash
        if changed and update_hash:
            self.files_hash[filename] = hash
        return changed

    def wybe_build_target(self, target: str, force_all: bool, final_dump: bool,
            check: bool, no_multi_specz: bool = False) -> Tuple[int, str]:
        """
        Args:
            target (str):         Name of the target
            final_dump (bool):    A flag used to log the final dump
            force_all (bool):     force-all flag of wybe
            check (bool):         If check is true, and the process exits with a
                                  non-zero exit code, a CalledProcessError
                                  exception will be raised.
            no_multi_specz(bool): Disable multiple specialization
        Returns:
            exit code and outputs (stdin && stdout)
        """
        TIMEOUT = 50  # sec
        wybe_path = os.path.abspath("../wybemk")
        lib_path = os.path.abspath("../wybelibs")
        args = [wybe_path, "-L", lib_path]
        if final_dump:
            args.append("--log=FinalDump")
        if force_all:
            args.append("--force-all")
        if no_multi_specz:
            args.append("--opt=no-multi-specz")
        args.append(target)

        r = subprocess.run(args, timeout=TIMEOUT,
                           stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                           cwd=self.tmp_dir)
        if check:
            if r.returncode != 0:
                self.write_section("ERROR OUTPUT", r.stdout.decode("utf-8"))
                r.check_returncode()

        return (r.returncode, self.normalise(r.stdout.decode("utf-8")))
    
    def normalise(self, output: str) -> str:
        output = re.sub(r"@([A-Za-z_]\w*):[0-9:]*", r"@\1:nn:nn", output)
        output = re.sub(r"\[ [0-9][0-9]* x i8 \]", "[ ?? x i8 ]", output)
        output = re.sub(r"(target triple *= *).*", r"\1???", output)
        output = output.replace(self.tmp_dir, "!TMP!")
        output = output.replace(self.root_dir, "!ROOT!")
        return output

    def execute_program(self, exe: str, check: bool,
            input: Optional[str] = None,
            timeout: float = 5.0) -> Tuple[int, str]:
        if input:
            input = input.encode("utf-8")
        r = subprocess.run([exe], timeout=timeout, input=input,
                           stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                           cwd=self.tmp_dir)
        if check:
            if r.returncode != 0:
                self.write_section("ERROR OUTPUT", r.stdout.decode("utf-8"))
                r.check_returncode()
        return (r.returncode, r.stdout.decode("utf-8"))