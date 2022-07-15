Shellpool Platforms
===================

Shellpool is meant to be very portable.  It currently depends on the following
Common Lisp libraries.  Normally you can install these automatically using
[quicklisp](http://www.quicklisp.org):

  - [trivial-features](http://www.cliki.net/trivial-features) for identifying OS
  - [cl-fad](http://weitz.de/cl-fad/) for handling temporary files
  - [bordeaux-threads](http://common-lisp.net/project/bordeaux-threads/) for multithreading
  - [bt-semaphore](https://github.com/rmoritz/bt-semaphore) for semaphores

Beyond these libraries Shellpool just needs `bash` and `pgrep`, which are
available on many systems.


## Supported Platforms

Shellpool has a reasonably good [test suite](test/) that can be used to help
ensure compatibility with your system.

 - **Linux**.  All tests should pass on CCL, SBCL, CMUCL, ABCL, Allegro, and
   Lispworks.  Note that for Lispworks you may need to run
   `(bt:start-multiprocessing)` before using Shellpool.

 - **FreeBSD**.  All tests should pass on CCL, SBCL, CMUCL, and ABCL.  Note
   that SBCL must be compiled with `--with-sb-thread`.

 - **MacOS**.  All tests should pass on CCL, SBCL, CMUCL, and ABCL.  Note
   that SBCL must be compiled with `--with-sb-thread`.

 - **Windows**.  All tests should pass on 32-bit CCL trunk on a Windows XP
   system with Cygwin installed and the Cygwin `procps` package installed (for
   `pgrep`).

   It is likely that there are problems that the test suite does not cover,
   e.g., interrupting native Windows applications will probably not work well.
   I have not tested other Lisps, msys, etc., but the CCL port may make such a
   task much easier.

 - **OpenBSD**.  All tests should pass on ABCL.  SBCL 1.2.7 doesn't compile for
   me when I try to enable threading, so it probably won't work.  I don't know
   of other Common Lisps for this platform.

When I re-run the test suite on various platforms, I often use Git tags to mark
the commits.  You can [inspect these
tags](https://github.com/jaredcdavis/shellpool/tags) to see detailed
information on the testing platforms, such as the Lisp and OS versions
involved.


## Not Supported

Shellpool will not currently work on CLISP or ECL because their `run-program`
commands lack `stderr` support.  (Shellpool currently depends on being able to
use both stderr and stdout to function.  It is probably not too difficult to
rework this to avoid needing stderr.)

It would likely be very easy to port shellpool to other Unix-like operating
systems that can run supported Lisps.  I would welcome patches that provide or
improve support for particular Lisps or operating systems, or for adding
additional test cases.

