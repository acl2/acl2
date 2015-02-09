; VL 2014 -- VL Verilog Toolkit, 2014 Edition
; Copyright (C) 2008-2015 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "VL2014")
(include-book "echars")
(include-book "std/util/defalist" :dir :system)



(fty::defalist vl-commentmap
  :parents (syntax)
  :short "Representation of comments within a top-level design elements."
  :key-type vl-location-p
  :val-type stringp
  :keyp-of-nil nil
  :valp-of-nil nil

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
comment, i.e., it begins with @('//') and ends with a newline, or begins with
@('/*') and ends with @('*/').  But in the @('vl-commentmap-p') definition, we
only require @('stringp'), and it can occasionally be useful to put
non-comments into the map, e.g., see @(see vl-commentmap-entry-sort).</p>

<h3>Special Notes about Comment Shifting</h3>

<p>BOZO this comment applies to the behavior of
@('vl-kill-whitespace-and-comments-core') which is part of the lexer.  It
probably makes sense NOT to shift the comments in the lexer, but to instead
move this to the pretty-printer.</p>

<p>When I originally developed the comment map, I imagined associating every
comment with its exact starting location in the file, hoping that this would
allow me to recreate the comments after transforming the module.  But my new
approach is to say that every comment begins at Column 0, regardless of where
it actually occurs in the line.</p>

<p>Why?  First, let me identify three commenting styles:</p>

<p>Style 1:</p>

@({
    /* the following decodes the controller signal from
       the such-and-so unit.  the valid values are blah
       blah blah blah ... */
    wire ctrl_sig = ~w[0] & ...;
})

<p>Style 2:</p>

@({
    // decode controller signal from such-and-so unit
    wire ctrl_sig = ~w[0] & ...;
})

<p>Style 3:</p>

@({
    wire ctrl_sig = ~w[0] & ...;  // decode controller signal
})

<p>If we record the exact positions of the comments, then we get perfectly good
behavior when Styles 1 and Styles 2 are used.  However, we get a very BAD
behavior for comments of Style 3.  In particular, the translation of ctrl_sig
will be some litany of wire declarations and gate/module instances, which are
all said to be at Line L on column C.  However, this comment will be at Line L
on Column C+X.  The net result is that the translation will look something
like:</p>

@({
    wire ctrl_sig;                    }
    wire _gen_37;                     }   Line L, Col C
    wire _gen_38;                     }
    buf(_gen_37, w[0]);               }
    ...                               }
    and(ctrl_sig, _gen_38, _gen_39);  }

    // decode controller signal       }   Line L, Col C+X
})

<p>Having the comment come after this big mess of stuff is really unfortunate,
and, even worse, it makes it look like the comment refers to whatever comes
NEXT.  This could lead the reader to think that comments are about wires which
they are not, and is really bad.</p>

<p>So, instead, I now switch all comments to use Column 0.  We have taken great
care in the writer to ensure that (1) the mergesort is stable, and (2) comments
are given before module items, so that this approach essentially forces all
comments to act as though they occur at the start of their line.</p>

<p>The current approach is pretty bad w.r.t. internal comments, e.g., if I
write an expression with lots of @('/* blah */')-style comments, inside of it,
then these all get moved over to the front.  Bad stuff.  But such comments seem
relatively rare anyway, and I am not too worried about trying to support
them.</p>")

(defthm consp-of-car-when-vl-commentmap-p
  ;; Not sure whether we need this, but it was something we previously had when
  ;; I converted comment maps into a defalist.
  (implies (vl-commentmap-p x)
           (equal (consp (car x))
                  (consp x)))
  :rule-classes ((:rewrite :backchain-limit-lst 1)))

