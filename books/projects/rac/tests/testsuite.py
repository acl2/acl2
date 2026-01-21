from argparse import ArgumentParser
from pathlib import Path
from difflib import unified_diff
from termcolor import colored

import re
import subprocess as sp
import yaml
import os
import sys

test_dir_path = 'yaml_test/'

def preprocess(working_dir, input):
    cpp = sp.run(['g++', '-D__RAC__', '-C', '-E', '-std=c++14', '-I../../../include',
        input, '-o', input + '.i'], capture_output=True, text=True, cwd=working_dir)
    assert cpp.returncode == 0, 'Preprocessor failed:\n' + cpp.stderr

def run_parser(bin_path, working_dir, input, timeout, env):

    # Remove potential old generated code.
    sp.run(['rm', '-f', input + '.ast.lsp'], cwd=working_dir)

    preprocess(working_dir, input)

    return sp.run(['../../../' / bin_path, input, '-acl2', '-pedantic'], capture_output=True, text=True,
        timeout=timeout, cwd=working_dir, env=env)

def run_parser_raw(bin_path, working_dir, args, timeout, env):
    return sp.run([bin_path, *args],
            capture_output=True, text=True,
            timeout=timeout,
            cwd=working_dir,
            env=env)


def diff(ref, out):

    ref = ref.splitlines(keepends=True)
    out = out.splitlines(keepends=True)
    return ''.join(unified_diff(ref, out, n=1, fromfile="ref", tofile="out"))

def load(path, allow_empty):
    try:
        with open(path, "r") as f:
            content = f.read()
            content = '\n(funcdef'.join(content.split("(funcdef"))
            content = '\n  (block'.join(content.split("(block"))
            content = '\n    (declare'.join(content.split("(declare"))
            content = '\n    (assign'.join(content.split("(assign"))
            return content

    except OSError as err:
        if allow_empty:
            return ""
        else:
            raise err


def test(bin_path, dir_path, testcase, timeout):

    input = testcase.get("input", testcase.get("name") + ".cpp")

    out = None
    args = testcase.get("args")
    env = testcase.get("env", {})

    if args is None:
        out = run_parser(bin_path, dir_path, input, timeout, env)
    else:
        file_to_preprocess = testcase.get("preprocess")
        if file_to_preprocess:
            preprocess(dir_path, file_to_preprocess)
        out = run_parser_raw(bin_path, dir_path, args, timeout, env)

    disabled_checks = testcase.get("disabled-checks", [])
    if not "should_report_error" in disabled_checks:
        if testcase.get("should_report_error", False):
            assert out.returncode == 1, f"expected one as returncode but got {out.returncode}"
        else:
            assert out.returncode == 0, f"expected a zero returncode but got {out.returncode}"

    if not "stdout" in disabled_checks:
        stdout_path = testcase.get("ref_stdout", testcase.get("name") + ".ref.stdout")
        ref = load(dir_path + stdout_path, allow_empty=True)
        assert out.stdout == ref, f"stdout differs:\n{(diff(ref, out.stdout))}"

    if not "stderr" in disabled_checks:
        if testcase.get("stderr_not_empty", False):
            assert out.stderr != "", "expected something written on stderr, but got nothing"
        else:
            stderr_path = testcase.get("ref_stderr", testcase.get("name") + ".ref.stderr")
            ref = load(dir_path + stderr_path, allow_empty=True)
            assert out.stderr == ref, f"stderr differs:\n{(diff(ref, out.stderr))}"

    # If the test should fails, don't test the output: there is none.
    if not "generated_code" in disabled_checks and not testcase.get("should_report_error", False):

        ref = ""
        try:
            generated_path = testcase.get("ref_generated", testcase.get("name") + ".cpp.ref.ast.lsp")
            ref = load(dir_path + generated_path, allow_empty=False)
        except OSError as err:
            raise OSError(f"Reference `{generated_path}` not found")

        try:
            out_path = dir_path + testcase.get("out_generated", input + ".ast.lsp")
            out = load(out_path, allow_empty=False)
            assert out == ref, f"generated code differs:\n{diff(ref, out)}"
        except OSError as err:
            raise AssertionError("Code not generated")


def run_tests(bin_path, category, file, timeout, quiet, show_bugs):

    dir_path = test_dir_path + category + '/'
    with open(dir_path + file, "r") as test_file:
        content = yaml.safe_load(test_file)

    for testcase in content:

        descr = testcase.get("description")
        try:
            test(bin_path, dir_path, testcase, timeout)

        except AssertionError as err:
            print(f"[{colored('KO', 'red')}]", testcase["name"], f"(from {category})")
            if not quiet:
                print(f"{colored('Test description:', 'yellow')} ", descr)
            print(err)
            print('--------------------------------------------------------------------------------')

        except Exception as err:
            print(f"[{colored('KO', 'yellow')}]", testcase["name"], f"(from {category})")
            if not quiet:
                print(f"{colored('Test description:', 'yellow')} ", descr)
            print(err)
            print('--------------------------------------------------------------------------------')

        else:
            if testcase.get("bug", False) and show_bugs:
                print(f"[{colored('OK', 'magenta')}] (Bug)", testcase["name"], f"(from {category})")
                print(f"{colored('Test description:', 'yellow')} ", descr)
                print('--------------------------------------------------------------------------------')
            elif not quiet:
                print(f"[{colored('OK', 'green')}]", testcase["name"], f"(from {category})")
                print(f"{colored('Test description:', 'yellow')} ", descr)
                print('--------------------------------------------------------------------------------')


def print_categories():
    for dirs in os.listdir(test_dir_path):
        print(' - ', dirs)

if __name__ == "__main__":

    parser = ArgumentParser(description='')
    parser.add_argument('bin', metavar='BIN', nargs="?", type=str, \
            help='The path of the binary path to test')
    parser.add_argument('--timeout', nargs='?', default=None, type=float,\
            help='Add a timeout (in seconds)')
    parser.add_argument('--quiet', action='store_true', \
            help='Only print failed tests without description')
    parser.add_argument('--list', action='store_true', \
            help='Print every categories available')
    parser.add_argument('--categories', nargs='+', default=None, \
            help='Select categories to test, by default test every categories')
    parser.add_argument('--hide-bugs', action='store_true', \
            help='Don\'t show the tests taggesed as bug when the test suceed')
    args = parser.parse_args()

    test_dir_path = os.path.dirname(os.path.abspath(__file__)) + '/yaml_test/'

    if args.list:
        print_categories()
        sys.exit()

    if args.bin is None:
        args.bin = ""

    if not args.bin or not os.path.isfile(args.bin) or not os.access(args.bin, os.X_OK):
        raise Exception(f'`{args.bin}` is not an executable file')
    bin_path = Path(args.bin).absolute()

    categories = args.categories
    if categories == None:
        categories = os.listdir(test_dir_path)

    if args.timeout and args.timeout <= 0:
        raise Exception("A timeout should always be positive")

    for cat in categories:
        if (not os.path.exists(test_dir_path + cat)):
            raise Exception(f"category `{cat}` doesn't exist")

        dir = os.listdir(test_dir_path + cat)

        for file in dir:

            if file[-4:] != '.yml':
                continue

            run_tests(bin_path, cat, file, args.timeout, args.quiet, not args.hide_bugs)
