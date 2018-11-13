---------------------------------------------------
HTML-TEMPLATE - Use HTML templates from Common Lisp
---------------------------------------------------

HTML-TEMPLATE is a portable library for Common Lisp which can be used
to fill templates with arbitrary (string) values at runtime.
(Actually, it doesn't matter whether the result is HTML. It's just
very likely that this will be what the library is mostly used for.)

It is loosely modeled after the Perl module HTML::Template and
partially compatible with a its syntax, though both libraries contain
some extensions that the other does not support.

HTML-TEMPLATE translates templates into efficient closures which can
be re-used as often as needed. It uses an intelligent cache mechanism
so you can nevertheless update templates while your program is running
and have the changes take effect immediately.

Complete documentation for HTML-TEMPLATE can be found in the `docs`
directory or at the [project documentation
site](https://edicl.github.io/html-template/).