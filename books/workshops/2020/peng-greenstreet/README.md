# Book certification
* make -j xx ACL2=/path/to/acl2 ACL2_SYSTEM_BOOKS=/path/to/books ACL2_BUILD_DIR=/path/to/books/build

# Book organization
The three clause-processors are type-judge-cp in type-inference-bottomup.lisp, type-unify-cp in type-inference-topdown.lisp and term-rectify-cp in term-rectify.lisp.

The file test-inference.lisp contains several examples testing the functionality of the three clause-processors. Feel free to run them and have fun.

# Note
* Note that currently the correctness theorem of the clause-processors are skip-proofed. We are working on verifying them. We expect to finish the proof before the camera-ready deadline.
* We are also working on integrating them into the Smtlink workflow. A newer version of these three clause-processors will appear in Smtlink in books/projects/smtlink.
