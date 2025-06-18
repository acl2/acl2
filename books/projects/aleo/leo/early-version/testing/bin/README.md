# ACL2 Theorem Generation and Checking for Leo Compilation

Theorem Generation and Checking (tgc) is used to prove that
a Leo compiler phase has preserved the semantics of the Leo program being compiled

See the `leo-acl2-bin` repository for releases of `tgc` and some documentation about how to use it.

## Building a tgc image from an existing acl2 build using ccl on ubuntu.

The reason this is done on ubuntu is because the tgc CI is being run on ubuntu.
Additional platforms will be added later.

1. Certify the needed books.
```
   cd /path/to/leo-acl2
#   cert.pl top
   cert.pl working
```
   Check if that finished normally.  If so,

2. Build an ACL2 image containing leo-acl2.

   You can write it to a scratch directory
```
   cd /path/to/leo-acl2
   ACL2_CUSTOMIZATION=NONE $ACL2

   # ACL2 !> (include-book "top")
   ACL2 !> (include-book "working")
   ACL2 !> :q

   Exiting the ACL2 read-eval-print loop.  To re-enter, execute (LP).
   ? (save-exec "/path/to/scratchdir/leo-acl2" "Included leo-acl2/top")
```
  The preceding creates the script `leo-acl2`, which we do not need
  and should be deleted, and the heap `leo-acl2.lx86cl64`, which we need.

## Testing the new leo-acl2 image.

1. For best compatibility, run a shell without any of the environment variables
   related to CCL or ACL2.

  One way to do this is to strip those environment variables and PATH entries from
  your normal shell, so that you have the other things that you are used to having.
  For example:
```
   unset CCL_DEFAULT_DIRECTORY
   unset ACL2
   unset ACL2_SYSTEM_BOOKS
   unset ACL2_ROOT
   export PATH=/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin
```

2. In that same shell, make a testing directory and copy what you need to it.
   Here we copy the same items that we later put into leo-acl2-releases.
```
   mkdir /path/to/leo-acl2-tests
   cd /path/to/leo-acl2-tests
   cp /path/to/scratchdir/leo-acl2.lx86cl64 .
#   cp /path/to/leo-acl2/testing/bin/{lx86cl64,tgc,theorem-template-parsing.tl,theorem-template-canonicalization.tl,theorem-template-type-inference.tl} .
   cp /path/to/leo-acl2/testing/bin/{lx86cl64,tgc,theorem-template-parsing.tl} .
```
   Note: it probably makes sense to change all these references to lx86cl64 so that it comes from the same ccl that you are building acl2 on.

3. (NOTE: this is old)  cd to an output directory that was created by `cargo run -p leo-test-framework --bin tgc -- -f test_name`
   and then run tgc.  For example,
```
   cd /path/to/leo/tmp/tgc/compiler_tuples_destructured.leo_574
   /path/to/leo-acl2-tests/tgc canonicalization initial_ast.json canonicalization_ast.json canonicalization-theorem.lisp
   /path/to/leo-acl2-tests/tgc type-inference canonicalization_ast.json type_inferenced_ast.json type-inference-theorem.lisp
```

3. Newer version of (3).
```
   cd /path/to/json-files
   /path/to/leo-acl2-tests/tgc parsing src/main.leo outputs/initial_ast.json parsing-theorem.lisp
```

## Making the leo-acl2-bin release.

1. Gather commit levels for acl2 and leo-acl2.

   Make sure you are on the `master` branch (or on an official ACL2 release).
   Record your acl2 commit level.
```
   cd /path/to/acl2
   git branch -v
```
   Record the hex number that is on the line after `* master`.

   Do the same thing for `leo-acl2` to record the commit level.

2. Look at leo-acl2-bin/README.md to decide what the next release version should be,
   and to see what information you will need to fill in.  Let's call the version
   vM.m.p for now.

3. Copy the needed bundle files to a release directory (not under version control) and make the tarball.
```
   cd /path/to/leo-acl2-releases/
   mkdir vM.m.p
   cd vM.m.p
   cp /path/to/scratchdir/leo-acl2.lx86cl64 .
   cp /path/to/leo-acl2/testing/bin/{lx86cl64,tgc,theorem-template-parsing.tl} .
#   cp /path/to/leo-acl2/testing/bin/{lx86cl64,tgc,theorem-template-parsing.tl,theorem-template-canonicalization.tl,theorem-template-type-inference.tl} .
   tar czf leo-acl2--vM.m.p.tgz leo-acl2.lx86cl64 lx86cl64 tgc theorem-template-parsing.tl
#   tar czf leo-acl2--vM.m.p.tgz leo-acl2.lx86cl64 lx86cl64 tgc theorem-template-parsing.tl theorem-template-canonicalization.tl theorem-template-type-inference.tl
```

4. Test the tarball.

   A good way to do this is to have forks of `leo` and `leo-acl2-bin`.
   Then, in your fork of `leo`, modify `.github/workflows/acl2.yml` in a branch
   (call the branch BR) so that it gets the `leo-acl2-bin` tarball from your
   fork of `leo-acl2-bin`.

   Create a release of `vM.m.p` in your fork of `leo-acl2-bin` and upload the tarball.

   In your `leo` fork, using the github web interface, go to "Actions",
   choose "Leo-ACL2", and manually dispatch the action choosing branch BR from
   the dropdown menu.

   Take a look at the results.  As of 2021-09-16 there were 2 canon failures and
   21 type failures.  If it is much worse than that it is good to fix the issues
   and rebuild the release.

5. Go to `github.com/AleoHQ/leo-acl2-bin` and create the `vM.m.p` release.
   Upload the tarball to the release.

6. Final test.

   Now in `github.com/AleoHQ/leo`, not in your fork.  Using the github web interface,
   under `Actions`, there is a workflow named `Leo-ACL2`.
   Manually trigger this.  When you trigger it, it will
   download the "latest" release of `leo-acl2-bin` which is the one most recently created.
   If you did the testing above then you should get the same results.
