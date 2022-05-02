# ACL2s Interface

The ACL2s interface is a library for querying the ACL2 theorem prover
from inside of "raw Lisp", a Common Lisp process that has ACL2
loaded. This can be achieved by starting an ACL2 REPL and running
`:q`. Despite its name, the interface is not limited to use with the
ACL2 Sedan system.

The ACL2s interface is under continuing development in an external
repository: https://gitlab.com/acl2s/external-tool-support/interface

## Usage

We only officially support the library running under SBCL. There is
preliminary CCL support implemented, but we need to do more testing
before we can confidently say that CCL is supported.

To use this library, you should first certify it, either by running
`make` in this directory or by calling `cert.pl` on `top.lisp`. To use
the provided Makefile, one must either set the `ACL2_SYSTEM_BOOKS`
environment variable to the path of their ACL2 installation's system
books directory, or set the `ACL2_CERT_PL` environment variable to the
path to their ACL2 installation's `cert.pl` script and the
`ACL2_CLEAN_PL` environment variable to the path to their ACL2
installation's `clean.pl` script.

Once the library is certified, run `(include-book "top")` in this
directory to load it. Then, you will have access to the ACL2s
interface functions. Note that the ACL2s interface functions are only
accessible from raw Lisp.

## Documentation

HTML XDOC documentation for the interface functions can be generated
by running the following after including `top`:
```
(include-book "xdoc/save" :dir :system)
(xdoc::save "./doc" :error t :redef-okp t)
```

Alternatively, one can access the XDOC documentation for the ACL2s
interface functions as normal after including `top`, e.g. by running
`:doc acl2s-interface-internal::acl2s-interface` inside of the ACL2
REPL.

## Examples
Some examples are provided in the `examples` directory. These examples
all rely on the ACL2s utilities library being certified. This can be
done by running `make acl2s-utils-cert` from the root directory of
this repository, or by calling `cert.pl` on `acl2s-utils/top.lisp`.

The examples are expected to be run from an ACL2 REPL started within
the `examples` directory. Note that they cannot be run using `ld`
since they contain the `:q` command to break into raw Lisp; instead,
the commands in each file must be run in an ACL2 REPL either by
directly entering them or by piping the file into a running ACL2
process.
