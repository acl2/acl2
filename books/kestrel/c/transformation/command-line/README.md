This directory contains a command-line interface to the Kestrel C-to-C transformations.

Setup:

0. Build and install ACL2.  (See https://www.cs.utexas.edu/~moore/acl2/manuals/latest/?topic=ACL2____INSTALLATION)

1. Ensure you can run cert.pl.  (See https://www.cs.utexas.edu/~moore/acl2/manuals/latest/?topic=BUILD____PRELIMINARIES)

2. Certify the books in this directory: cert.pl -j8 *.lisp

 where 8 is the number of cores to use (adjust to fit your machine).  This may take a while, depending on how many cores you use.

Usage:

3. To run a transformation, create a .json file containing the name of the transformation and the arguments.  Follow the form of the examples in tests/splitgso.json and tests/simpadd0.json.  The .json file should contain a JSON object (a map), whose keys are exactly "command" and "arguments", where the value of the command is a string that names the transformation, such as "simpadd0", and the value of argument is a map from argument names (strings) to values.  Values that are lists should be given as JSON arrays.

4. Run the transformation by calling transform-c.sh:

  Example: transform-c.sh splitgso.json

  The first invocation of transform-c.sh will be slow because it will save an ACL2 image with all the tools built-in. Subsequent invocations of transform-c.sh should be fast.

Updating:

After pulling in updates to ACL2, follow the steps starting from Step 0 above to rebuild ACL2, re-certify books, etc.