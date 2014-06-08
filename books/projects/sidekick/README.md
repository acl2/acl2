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

![Screenshot](screenshot.png?raw=true)

Note: the Sidekick is **highly experimental** software.  It doesn't do
much yet, and at this point is mostly a proof of concept.

## Installation

I use Linux/x86 with Firefox or Chromium as the browser, and
[CCL](http://ccl.clozure.com) as my host Lisp for ACL2.  Other
platforms may not work.

You'll need to use the [development version of
ACL2](http://acl2-devel.googlecode.com) and [its
books](http://acl2-books.googlecode.com).  Build ACL2 as usual, then
certify at least the **basic** and **quicklisp** books, e.g.,:

```Shell
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



