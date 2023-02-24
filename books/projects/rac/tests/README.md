This testsuite aims to prevent regression and track known bugs. For now, it
only checks the "--acl2" output since it is the more critical (and if it is
correct, --rac should also be correct). Most of the code the code responsible
of generating the acl2 output is covered (> 93%). For the bits left, I'm not
sure they are use...

# Tests structure:

All the test are under `yaml_tests`: testsuite.py will search for every
directory inside (category) and inside each category, one or multiple .yml file
will declare each test, the inputs, the expcted behaviour and if it is that
should be fixed in the future.

To add a new test, we just need to declare it in a yml file of its category
(for more details on the available options and keys, please see the `no-checks`
test in `program_structure/basics.yml`) and add all the file needed for the
test (for example, the input and expected output)

To declare a new category, we need to add a new directory inside `yaml_tests`
with a yaml file (no constraint on the name, it just need to have the .yml
extension). 

# Setup

* Generate python virtual env: `python -m venv env`
* Activate virtual env: `source env/bin/activate`
* Install dependencies `pip install -r tests/requirements.txt`

# Code coverage

We will be using gcov and all those command are type in the src/ directory:

* Add `-fprofile-arcs -ftest-coverage` to the gcc command line and the
  Makefile, this will generate an instrumented binary and run `make`
* Run `python ../tests/testsuite.py parse` (this will run the binary multiple
  and each run will save the coverage information under gcno files).
* Generate the report: `gcovr . --html --html-details -o report.html`.

# TODO

* Operator precedence
* Error check parser
