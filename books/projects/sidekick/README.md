ACL2 Sidekick
=============

The **ACL2 Sidekick** is a graphical add-on for
[ACL2](http://www.cs.utexas.edu/users/moore/acl2/).

It extends your ACL2 session with a [web
server](http://weitz.de/hunchentoot/) so that you can interact with
ACL2 through your browser.

You use the Sidekick **along with**---not instead of---Emacs or your
favorite ACL2 development environment.  Here's a screenshot of using
it with Emacs:

![Screenshot](screenshots/emacs.png?raw=true)

Note: the Sidekick is **highly experimental** software.  It doesn't do
much yet, and at this point is mostly a proof of concept.


## Basic Setup

I use Linux/x86 with Firefox or Chromium as the browser, and
[CCL](http://ccl.clozure.com) as my host Lisp for ACL2.  Other
platforms may not work.

You'll need to use the [development version of
ACL2](http://acl2-devel.googlecode.com) and [its
books](http://acl2-books.googlecode.com).

Build **ACL2(h)** as usual, then certify at least the **basic** and
**quicklisp** books, e.g.,:

```Shell
    $ cd acl2
    $ make LISP=ccl ACL2_HONS=h
    $ cd acl2/books
    $ make USE_QUICKLISP=1 basic quicklisp
```

Finally, get a copy of the Sidekick and certify its top book, e.g.,:

```Shell
    $ git clone https://github.com/jaredcdavis/sidekick.git
    $ cd sidekick
    $ cert.pl top     # should produce top.cert
```

The Sidekick should now be ready.  To try it out, go to the **demo**
directory and follow along with **demo.lsp**.


### Sidekick Images

For instant startup times, you can build an ACL2 image with the
Sidekick built in.

```Shell
    $ cd sidekick
    $ make           # should produce a 'sidekick' executable
    $ ./sidekick
```

You can then use this **sidekick** instead of invoking your normal
**saved_acl2h** image when doing interactive development.


### Browser Launching

You can tell the Sidekick to automatically launch a web browser when
it boots up by setting the **SIDEKICK_BROWSER** environment variable.
For instance:

```Shell
    $ export SIDEKICK_BROWSER="firefox"
```

Whatever command you supply will simply be invoked, in the background,
with the argument "http://localhost:9000/" (or similar).


### Other Ports

The Sidekick will try to listen on port 9000 by default, but this can
be adjusted using SIDEKICK_PORT.  For instance:

```Shell
    $ export SIDEKICK_PORT=9001
```

You can also explicitly start the sidekick on a different port by
using, e.g., (sidekick::start 9001).

