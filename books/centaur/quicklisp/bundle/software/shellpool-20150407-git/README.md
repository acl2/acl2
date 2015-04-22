Shellpool
=========

Shellpool is a way to run external programs from within a Common Lisp
program.  It features:

 - **Forking control**.  Sub-programs are launched with a separate shell, so
   you can avoid
   [forking](http://en.wikipedia.org/wiki/Fork_%28operating_system%29) your
   Lisp image, which may be unreliable you have dozens of GB of memory
   allocated or are running multiple threads.

 - **Output handling**.  You can easily stream, filter, or collect output from
   the command.  You can access both stdout and stderr lines as they are
   produced, and can tell the difference between them.

 - **Exit code**.  You get it.

 - **Interruption**.  Interrupts are handled gracefully.  After you interrupt
   (e.g., Control C), you can `:continue` to keep running the program, or `:q`
   to terminate the sub-program and return to Lisp as normal.

 - **Multithreading**.  You can safely launch multiple programs from multiple
   threads.  Threading support is based on the
   [bordeaux-threads](http://common-lisp.net/project/bordeaux-threads/)
   library.

 - **Portability**.  It runs on [many Lisps and operating
   systems](PLATFORMS.md), installs via [Quicklisp](http://www.quicklisp.org),
   and has few external dependencies.

Note: Shellpool is **not** suitable for running sub-commands that need access
to command-line input from the user or for
[TTY](https://en.wikipedia.org/wiki/Terminal_emulator)-based programs.


## Resources

 - [Github Project](https://github.com/jaredcdavis/shellpool) -- This is the
   main shellpool homepage.  Please feel free to use the issue tracker, etc.
   Note that the **master** branch is the stable version, while the **devel**
   branch is the under-development version and may be unstable.

 - [Installation](INSTALL.md)

 - [API Documentation](DOC.md)


## Related Lisp Libraries

If shellpool isn't quite right for you, here are some related Lisp libraries.

 - [inferior-shell](http://common-lisp.net/projects/qitab/) is allegedly very
   complete and portable for synchronous shells.  It has fancy features like
   support for remote execution (via ssh) and a domain specific language for
   constructing pipelines of shell commands.

 - [trivial-shell](http://common-lisp.net/project/trivial-shell/) is less full
   featured than `inferior-shell,` but is apparently highly portable.

 - [ASDF](http://common-lisp.net/project/asdf/asdf.html) has `run-program`
   shell-command with many options.

 - [external-program](https://github.com/sellout/external-program) is a wrapper
   for `run-program` functionality.


## License and History

Shellpool is Copyright (C) 2014-2015 [Kookamara LLC](http://www.kookamara.com/)
and released under an [MIT style license](LICENSE).

Shellpool is a successor to "tshell", a mechanism for running external programs
from [Clozure Common Lisp](http://ccl.clozure.com/).  Tshell was developed by
[Centaur Technology](http://www.centtech.com/) and was distributed as a library
for [ACL2](http://www.cs.utexas.edu/users/moore/acl2), and was also released
under the MIT license.

Shellpool was written by [Jared Davis](mailto:jared@centtech.com).
