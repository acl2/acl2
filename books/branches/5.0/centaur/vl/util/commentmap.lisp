; VL Verilog Toolkit
; Copyright (C) 2008-2011 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "VL")
(include-book "echars")

(defsection vl-commentmap-p
  :parents (modules)
  :short "Representation of comments within a module."

  :long "<p>We might try to leave comments in the token stream and then try to
preserve them as we parse by attaching them to various parse-tree structures.
But since comments can occur anywhere, this would really complicate how parsing
is done and would also be bothersome to our transformations, where we would
need to worry about when comments are present and whether they should be
copied, etc.</p>

<p>On the other hand, we do not want to just throw all the comments away.  They
might be valuable to a human who is trying to read and understand the
translated source code, and we really want the translated code to be as
readable, complete, and helpful as possible to the verification person who is
trying to work on it.</p>

<p>So, rather than throw comments away, our loading functions set them aside
into a <b>comment map</b>, which is an alist that maps @(see vl-location-p)
objects to strings.</p>

<p>By construction, each of these strings is known to be a valid Verilog
comment, i.e., it begins with <tt>//</tt> and ends with a newline, or begins
with <tt>/*</tt> and ends with <tt>*/</tt>.  But in the
<tt>vl-commentmap-p</tt> definition, we only require <tt>stringp</tt>, and it
can occasionally be useful to put non-comments into the map, e.g., see @(see
vl-commentmap-entry-sort).</p>

<h3>Special Notes about Comment Shifting</h3>

<p>BOZO this comment applies to the behavior of
<tt>vl-kill-whitespace-and-comments-core</tt> which is part of the lexer.  It
probably makes sense NOT to shift the comments in the lexer, but to instead
move this to the pretty-printer.</p>

<p>When I originally developed the comment map, I imagined associating every
comment with its exact starting location in the file, hoping that this would
allow me to recreate the comments after transforming the module.  But my new
approach is to say that every comment begins at Column 0, regardless of where
it actually occurs in the line.</p>

<p>Why?  First, let me identify three commenting styles:</p>

<p>Style 1:</p>

<code>
    /* the following decodes the controller signal from
       the such-and-so unit.  the valid values are blah
       blah blah blah ... */
    wire ctrl_sig = ~w[0] &amp; ...;
</code>

<p>Style 2:</p>

<code>
    // decode controller signal from such-and-so unit
    wire ctrl_sig = ~w[0] &amp; ...;
</code>

<p>Style 3:</p>

<code>
    wire ctrl_sig = ~w[0] &amp; ...;  // decode controller signal
</code>

<p>If we record the exact positions of the comments, then we get perfectly good
behavior when Styles 1 and Styles 2 are used.  However, we get a very BAD
behavior for comments of Style 3.  In particular, the translation of ctrl_sig
will be some litany of wire declarations and gate/module instances, which are
all said to be at Line L on column C.  However, this comment will be at Line L
on Column C+X.  The net result is that the translation will look something
like:</p>

<code>
    wire ctrl_sig;                    }
    wire _gen_37;                     }   Line L, Col C
    wire _gen_38;                     }
    buf(_gen_37, w[0]);               }
    ...                               }
    and(ctrl_sig, _gen_38, _gen_39);  }

    // decode controller signal       }   Line L, Col C+X
</code>

<p>Having the comment come after this big mess of stuff is really unfortunate,
and, even worse, it makes it look like the comment refers to whatever comes
NEXT.  This could lead the reader to think that comments are about wires which
they are not, and is really bad.</p>

<p>So, instead, I now switch all comments to use Column 0.  We have taken great
care in the writer to ensure that (1) the mergesort is stable, and (2) comments
are given before module items, so that this approach essentially forces all
comments to act as though they occur at the start of their line.</p>

<p>The current approach is pretty bad w.r.t. internal comments, e.g., if I
write an expression with lots of <tt>/* blah */</tt>-style comments, inside of
it, then these all get moved over to the front.  Bad stuff.  But such comments
seem relatively rare anyway, and I am not too worried about trying to support
them.</p>"

  (defund vl-commentmap-p (x)
    (declare (xargs :guard t))
    (if (consp x)
        (and (consp (car x))
             (vl-location-p (caar x))
             (stringp (cdar x))
             (vl-commentmap-p (cdr x)))
      (not x)))

  (defthm vl-commentmap-p-when-not-consp
    (implies (not (consp x))
             (equal (vl-commentmap-p x)
                    (not x)))
    :hints(("Goal" :in-theory (enable vl-commentmap-p))))

  (defthm vl-commentmap-p-of-cons
    (equal (vl-commentmap-p (cons a x))
           (and (consp a)
                (vl-location-p (car a))
                (stringp (cdr a))
                (vl-commentmap-p x)))
    :hints(("Goal" :in-theory (enable vl-commentmap-p))))

  (defthm vl-commentmap-p-of-cdr
    (implies (vl-commentmap-p x)
             (vl-commentmap-p (cdr x))))

  (defthm vl-location-p-of-caar-when-vl-commentmap-p
    (implies (vl-commentmap-p x)
             (equal (vl-location-p (caar x))
                    (consp x))))

  (defthm stringp-of-cdar-when-vl-commentmap-p
    (implies (vl-commentmap-p x)
             (equal (stringp (cdar x))
                    (consp x))))

  (defthm consp-of-car-when-vl-commentmap-p
    (implies (vl-commentmap-p x)
             (equal (consp (car x))
                    (consp x)))
    :rule-classes ((:rewrite :backchain-limit-lst 1)))

  (defthm vl-commentmap-p-of-append
    (implies (and (force (vl-commentmap-p x))
                  (force (vl-commentmap-p y)))
             (vl-commentmap-p (append x y)))
    :hints(("Goal" :induct (len x))))

  (defthm vl-commentmap-p-of-rev
    (implies (vl-commentmap-p x)
             (vl-commentmap-p (rev x)))
    :hints(("Goal" :induct (len x)))))