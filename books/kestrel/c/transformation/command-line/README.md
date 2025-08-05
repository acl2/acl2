This directory contains a command-line interface to the Kestrel C-to-C transformations.

Setup:

0. Build and install ACL2.  (See https://acl2.org/doc/?topic=ACL2____INSTALLATION.  You probably want to install the latest development snapshot, not a release tarball, so you can easily get access to updated transformations).

1. Ensure you can run cert.pl.  (See https://acl2.org/doc/?topic=BUILD____PRELIMINARIES)

2. Certify the books in this directory: cert.pl -j8 *.lisp

 where 8 is the number of cores to use (adjust to fit your machine).  This may take a while, depending on how many cores you use.

Usage:

3. To run a transformation, create a .json file containing the name of the transformation and the arguments.  Follow the form of the examples in tests/splitgso.json and tests/simpadd0.json.  The .json file should contain a JSON object (a map), whose keys are exactly "command" and "arguments", where the value of "command" is a string that names the transformation, such as "simpadd0", and the value of "arguments" is a map from argument names (strings) to values.  Values that are lists (e.g., lists of files to process) should be given as JSON arrays.  Again, see the examples in the tests/ directory.

4. Run the transformation by calling transform-c.sh:

  Example: transform-c.sh splitgso.json

  The first invocation of transform-c.sh will be slow because it will save an ACL2 image with all the tools built-in.  Subsequent invocations of transform-c.sh should be fast.

Updating:

After updating ACL2 (e.g., by doing a 'git pull'), follow the Setup steps starting from Step 0 above to rebuild ACL2, re-certify books, etc.

Usage of individual transformations:

The transformations are documented here: https://www.cs.utexas.edu/~moore/acl2/manuals/latest/?topic=C2C____TRANSFORMATION-TOOLS.  However, usage from the command line is somewhat different.  In the JSON file, all arguments are represented in a map, where the keys of the map may derive from the keywords that name the arguments, except the map keys are strings and do not start with colons (as the keywords do).  For example, the :split-members argument becomes the JSON string "split-members".  Also, the standard arguments CONST-OLD and CONST-NEW for each transformation are replaced by the standard arguments "old-dir", "new-dir", and "files".