; An Implementation of Formatted Printing for ACL2
; Copyright (C) 2014 Kookamara LLC
;
; Contact:
;
;   Kookamara LLC
;   11410 Windermere Meadows
;   Austin, TX 78759, USA
;   http://www.kookamara.com/
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
; Original author: Jared Davis <jared@kookamara.com>

(in-package "STR")
(include-book "centaur/fty/deftypes" :dir :system)
(include-book "centaur/fty/basetypes" :dir :system)
(include-book "decimal")
(include-book "octal")
(include-book "binary")
(include-book "hex")
(include-book "charset")
(include-book "std/basic/two-nats-measure" :dir :system)
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "arithmetic"))

(local (defthm unsigned-byte-p-5-when-print-base-p
         (implies (print-base-p x)
                  (unsigned-byte-p 5 x))))

(defsection pretty-printing
  :parents (std/strings)
  :short "A fast, @(see state)-free, @(see logic)-mode re-implementation of
much of ACL2's built-in pretty-printing capabilities."

  :long "<h3>Introduction</h3>

<p>This is a two pass, linear time, \"exact\" pretty printer for ACL2 objects.
My implementation is substantially based on the pretty-printing algorithm from
ACL2 6.4, and offers many similar features.</p>

<p>Why not just use ACL2's built-in pretty-printer?  As of ACL2 6.4, the
built-in pretty-printer is a program-mode function that makes heavy use of
@(see state); it gets its configuration settings (margins, arithmetic base,
etc.) out of state globals and does its printing via functions like @(see
princ$) which write to an output channel.  This can be inconvenient:</p>

<ul>

<li>You can't use ACL2's pretty-printer from logic-mode functions.</li>

<li>You need @(see state) available any time you want to create a string using
the printing functions.</li>

<li>The printing routines are generally not thread-safe.</li>

<li>Functions like @(see fmt-to-string) aren't usable outside of the ACL2
read-eval-print loop.</li>

</ul>

<p>My new pretty-printer has none of these problems.  Instead of incrementally
printing to an output stream, it builds up a character list in reverse order,
then reverses it with @(see rchars-to-string).  This uses more memory than
ACL2's pretty printer, but the overhead is linear in the size of the output.
Moreover, it appears to perform well---I measured it at about <b>5.5x
faster</b> than ACL2's pretty printer on one <i>possibly</i> realistic
benchmark; see @('std/strings/pretty-tests.lisp') for details.</p>


<h3>Quick Start</h3>

<p>The most convenient, high-level functions to use are:</p>

<ul>
<li>@(see pretty) - convert any ACL2 object into a string.</li>

<li>@(see revappend-pretty) - pretty print onto an accumulator, in reverse
order, which is useful for building strings as described in @(see
revappend-chars).</li>

</ul>

<p>There are many available settings that you can tune to customize the way
that objects are printed; see @(see printconfig-p) for details.  The defaults
are sensible and are mostly compatible with the way that ACL2 normally prints
things.</p>

<p>We also implement our own @(see eviscerate), which is more limited than
ACL2's and does not, for instance, support @(see acl2::iprinting).</p>


<h3>Limitations</h3>

<p>I do not reimplement the format-string style functions such as @(see fmt)
and @(see cw), although something like this is available as part of the @(see
vl::printer).  Instead, my focus here is on ACL2's @('ppr') functionality that
is at the heart of ACL2's s-expression printing.  In other words, this is an
implementation of something like the @('~x') @(see fmt) directive.</p>

<p>Even with respect to @('ppr'), there is some @(see missing-functionality).
I don't implement @(see acl2::iprinting) or include any infix printing support.
Various complex and unhelpful printer-control variables are also omitted.</p>


<h3>Implementation Details</h3>

<p>More details about the algorithm and implementation can be found in @(see
pretty-printing-implementation).</p>")

(defxdoc pretty-printing-implementation
  :parents (pretty-printing)
  :short "Implementation details of our @(see pretty-printing) support."

  :long "<p>My implementation is very much based on ACL2's pretty printer.  The
pretty printer operates in two linear passes: the first pass builds a data
structure that tells the second pass how to print.  The basic algorithm dates
from about 1971 and was used in the earliest Edinburgh Pure Lisp Theorem
Prover.  It is described in:</p>

<box><p>Robert S. Boyer.  <a
href='http://www.cs.utexas.edu/~boyer/pretty-print.pdf'>Pretty-Print.</a> Memo
number 64.  Department of Computational Logic, School of Artificial
Intelligence, University of Edinburgh.  1973.</p></box>

<p>Some general principles of pretty-printer are:</p>

<ul>

<li>Print flat whenever possible, unless argument lists of length over (say)
40; since they become hard to parse.</li>

<li>Atoms and eviscerated things (which print like atoms, e.g., @('<world>'))
may be printed on a single line.</li>

<li>Parenthesized expressions should not be printed on a line with any other
argument (unless the whole form fits on the line).</li>

</ul>

<p>For instance:</p>

@({
          'GOOD'                            'BAD'

     (foo (bar a) b c d)   |            (foo (bar a) b |
                                             c d)      |
     (foo a b  |
          c d) |                          ^^ we think it's too easy to
                                             miss 'b' when reading this
     (foo (bar a)   |
          b c d)    |
})")

(local (xdoc::set-default-parents pretty-printing-implementation))




(define print-base-fix ((x print-base-p))
  :returns (x-fix print-base-p)
  :inline t
  (mbe :logic (if (print-base-p x)
                  x
                10)
       :exec x)
  ///
  (defthm print-base-fix-when-print-base-p
    (implies (print-base-p x)
             (equal (print-base-fix x)
                    x))))

(fty::deffixtype print-base
  :pred print-base-p
  :fix print-base-fix
  :equiv print-base-equiv
  :define t
  :forward t
  :topic print-base-p)

(fty::defprod printconfig
  :tag :printconfig
  :layout :tree
  :short "Options that govern various aspects of pretty-printing, e.g., the
margins, numeric base, home package for printing symbols, etc."

  ((flat-right-margin posp
                      :rule-classes :type-prescription
                      :default 40
                      "Soft limit that influences how s-expressions get split
                       up into chunks.")

   (hard-right-margin posp
                      :rule-classes :type-prescription
                      :default 77
                      "Column to use for \"hard\" line wrapping, where lines
                       are forcibly broken up, usually with backslashes.")

   ;; Don't need this because it's only used by FMT.
   ;; (soft-right-margin posp
   ;;                    :rule-classes :type-prescription
   ;;                    :default 65
   ;;                    "Column to use for \"soft\" line wrapping.  Lines will be
   ;;                     broken up somewhere after this limit.  Generally should
   ;;                     be somewhat less than the hard margin.")

   (print-base        print-base-p
                      :default 10
                      "Controls whether numbers will be printed in base 2, 8,
                       10, or 16.")

   (print-radix       booleanp
                      :rule-classes :type-prescription
                      "When set, printed numbers will include a leading base
                       specifier, @('#b'), @('#o'), or @('#x') for base 2, 8,
                       or 16.  Base-10 numbers are printed with a trailing
                       radix point, @('.'), i.e., @('123') would print as
                       @('123.').")

   (home-package      symbolp
                      :rule-classes :type-prescription
                      :default (pkg-witness "ACL2")
                      "Controls which symbols will be printed with package prefixes.
                       Typically this should be set to the pkg-witness for the
                       current package.  Symbols from the home package, or that
                       have been imported into the home package, are printed
                       without leading package prefixes.")

   (print-lowercase   booleanp
                      :rule-classes :type-prescription
                      :default nil
                      "When set, package and symbol names to be printed in
                       lower case, which may improve readability."))

  :long "<p>In ACL2's pretty-printer, many of these parameters are part of the
@(see state).  We pull them out into a configuration object so that we can
avoid this dependency.</p>")

(defconst *default-printconfig*
  (make-printconfig))

(defxdoc missing-functionality
  :short "Notes about some ACL2 pretty-printer settings that are not
implemented in our @(see printconfig-p) objects."

  :long "<h5>@('print-escape') and @('print-readably')</h5>

<p>ACL2's take on print-readably:</p>
<ul>
 <li>it binds print-readably to nil by default</li>
 <li>it offers set-print-readably</li>
 <li>it binds it to nil in princ$</li>
 <li>it consults it in needs-slashes -- along with print-escape</li>
 <li>it formerly marked it as untouchable</li>
</ul>

<p>ACL2's take on print-escape</p>
<ul>
<li>PROVE binds it to T when #+write-arithmetic-goals... er, wtf?</li>
<li>bound to t by default</li>
<li>controllable with set-print-escape</li>
<li>potentially important for princ$ that it be bound to nil</li>
<li>consulted by needs-slashes -- along with print-readably</li>
<li>bound in prin1$ to put |s on symbols</li>
</ul>

<p>CLHS regarding print-escape:</p>
<ul>
<li>If false, escape characters and package prefixes are not
    output when expressions are printed</li>
<li>if true, an attempt is made to print an expression in such a way
    that it can be read back in to produce an equal expression.
    but this is only a guideline.</li>
</ul>

<p>CLHS regarding print-readably:</p>
<ul>
<li>when true, special rules go into effect:
    <ul>
    <li>printing any object O1 produces a printed representation that,
        when seen by the Lisp reader with the standard readtable in
        effect, will produce an object O2 that is SIMILAR to O1.</li>
    <li>printing proceeds as if *print-escape*, *print-array* and
        *print-gensym* are true and as if *print-length*, *print-level*,
        and *print-lines* are false.</li>
    </ul></li>
</ul>

<p>After a lot of investigation and consideration, I don't think any of this is
anything we should care about.  I can't imagine why someone would want to hide
the package names for symbols from other packages.  The two options seem
perhaps entirely redundant in the context of ACL2 where there aren't arrays and
gensyms, so I don't know why ACL2 provides both.  At any rate, it seems much
better to just drop this complicated nonsense and have the printer do something
reasonable by default.</p>


<h5>write-for-read</h5>

<p>ACL2 also has another parameter named @('write-for-read'), which is somewhat
similar to @('print-readably') but affects different things.</p>

<p>It is used in @('fmt-tilde-s1') to decide whether to split up symbols after
the soft margin.  This can be nice for keeping the proof long word wrapped in a
nice style.  However, it can be troublesome for trying to copy/paste rule
names.  It's also consulted in maybe-newline, which is used in @(see fmt) code.
Functions like fmt1! and fmt!  and fms! bind it to true.</p>

<p>None of that matters yet because, at least at the moment, I am only
implementing PPR, not FMT, and all of that is FMT-level stuff.</p>

<p>@('write-for-read') also influences ACL2's @('spaces1') function.  When
@('write-for-read') is disabled, it prints @('\<newline>') sequences and then
continues printing spaces on the next line.  I don't think this is a
\"feature\" that I will miss, so I am not going to implement it.</p>")


; ----------------------------------------------------------------------------
;
;                          Basic Printing of Atoms
;
; ----------------------------------------------------------------------------

; Summary of ACL2's atom-printing routines:
;
;   explode-atom -- convert any atom into a character list
;     for numbers, assumes print-radix is nil but knows about print bases
;     for symbols, prints just the symbol name, no packages, no escaping
;     for strings, just prints the contents, no escaping
;     for chars, just prints the character itself, no escaping/translation
;
;   explode-atom+ -- unless print radix, identical to explode-atom
;     for numbers, adds radix stuff around what explode-atom does
;     for strings/symbols/chars, identical to explode-atom
;
;   princ$ -- most basic way to print an atom to a stream
;     very complex: streams, wormholes, live states, printer controls
;     for symbols -- if downcasing, prints (string-downcase (symbol-name x))
;     for anything else, idental to explode-atom+: no packages/escaping
;
;   prin1$ -- for printing out things that can be read in
;     numbers: identical to princ$
;     characters: prints #\c for most characters, but also #\Newline, etc
;     strings: prints "foo", escaping as necessary
;     symbols: prints [pkg::]foo, escaping as necessary; printing package
;              depends on current package; prints lowercase if print-case
;              :downcase
;
; We now implement:
;
;    print-atom -- similar to princ$
;    print-escaped-atom - similar to prin1$
;
; Except that our versions don't deal with channels/state, they just accumulate
; characters in reverse order.

(define basic-print-nat
  :short "Print a natural number in a particular print base, no radix."
  ((x    natp         :type unsigned-byte)
   (base print-base-p :type (unsigned-byte 5))
   (acc))
  :split-types t
  :returns (new-acc character-listp :hyp (character-listp acc))
  (case base
    (10        (revappend-nat-to-dec-chars x acc))
    (16        (revappend-nat-to-hex-chars x acc))
    (8         (revappend-nat-to-oct-chars x acc))
    (otherwise (revappend-nat-to-bin-chars x acc))))

(define basic-print-int
  :short "Print an integer in a particular print base, no radix."
  ((x    integerp     :type integer)
   (base print-base-p :type (unsigned-byte 5))
   (acc))
  :inline t
  :split-types t
  :returns (new-acc character-listp :hyp (character-listp acc))
  (if (< x 0)
      (basic-print-nat (the unsigned-byte (- x)) base (cons #\- acc))
    (basic-print-nat x base acc)))

(define basic-print-rat
  :short "Print a (non-integer) rational in a particular print base, no radix."
  ((x    rationalp    :type ratio)
   (base print-base-p :type (unsigned-byte 5))
   (acc))
  :guard (not (integerp x))
  :split-types t
  :returns (new-acc character-listp :hyp (character-listp acc))
  (b* ((acc (basic-print-int (numerator x) base acc))
       (acc (cons #\/ acc)))
    (basic-print-nat (denominator x) base acc)))

(define basic-print-complex
  :short "Print a complex rational in a particular print base, no radix."
  ((x    complex-rationalp :type complex)
   (base print-base-p      :type (unsigned-byte 5))
   (acc))
  :split-types t
  :returns (new-acc character-listp :hyp (character-listp acc))
  (b* ((acc  (list* #\( #\C #\# acc))
       (real (realpart x))
       (acc  (if (integerp real)
                 (basic-print-int real base acc)
               (basic-print-rat real base acc)))
       (acc  (cons #\Space acc))
       (imag (imagpart x))
       (acc  (if (integerp imag)
                 (basic-print-int imag base acc)
               (basic-print-rat imag base acc))))
    (cons #\) acc)))

(define radix-print-int
  :short "Print an integer in a particular print base, with radix."
  ((x    integerp    :type integer)
   (base print-base-p :type (unsigned-byte 5))
   (acc))
  :split-types t
  :returns (new-acc character-listp :hyp (character-listp acc))
  (case base
    (10
     (cons #\. (if (< x 0)
                   (revappend-nat-to-dec-chars (- x) (cons #\- acc))
                 (revappend-nat-to-dec-chars x acc))))
    (16
     (let ((acc (list* #\x #\# acc)))
       (if (< x 0)
           (revappend-nat-to-hex-chars (- x) (cons #\- acc))
         (revappend-nat-to-hex-chars x acc))))
    (8
     (let ((acc (list* #\o #\# acc)))
       (if (< x 0)
           (revappend-nat-to-oct-chars (- x) (cons #\- acc))
         (revappend-nat-to-oct-chars x acc))))
    (otherwise
     (let ((acc (list* #\b #\# acc)))
       (if (< x 0)
           (revappend-nat-to-bin-chars (- x) (cons #\- acc))
         (revappend-nat-to-bin-chars x acc))))))

(define radix-print-rat
  :short "Print a (non-integer) rational in a particular print base, with radix."
  ((x    rationalp    :type ratio)
   (base print-base-p :type (unsigned-byte 5))
   (acc))
  :guard (not (integerp x))
  :split-types t
  :returns (new-acc character-listp :hyp (character-listp acc))
  (case base
    (10        (basic-print-rat x base (list* #\r #\0 #\1 #\# acc)))
    (16        (basic-print-rat x base (list* #\x #\# acc)))
    (8         (basic-print-rat x base (list* #\o #\# acc)))
    (otherwise (basic-print-rat x base (list* #\b #\# acc)))))

(define radix-print-complex
  :short "Print a complex rational in a particular print base, with radix."
  ((x    complex-rationalp :type complex)
   (base print-base-p      :type (unsigned-byte 5))
   (acc))
  :split-types t
  :returns (new-acc character-listp :hyp (character-listp acc))
  (b* ((acc  (list* #\( #\C #\# acc))
       (real (realpart x))
       (acc  (if (integerp real)
                 (radix-print-int real base acc)
               (radix-print-rat real base acc)))
       (acc  (cons #\Space acc))
       (imag (imagpart x))
       (acc  (if (integerp imag)
                 (radix-print-int imag base acc)
               (radix-print-rat imag base acc))))
    (cons #\) acc)))

(define print-atom-aux
  :parents (print-atom)
  :short "Goofy helper function to handle the number case."
  ((x     (and (atom x)
               (not (symbolp x))
               (not (stringp x))
               (not (characterp x)))
          "This very weird guard is because we can't just assume it's an
           acl2-numberp due to bad atoms.")
   (config printconfig-p)
   (acc))
  :returns (new-acc character-listp :hyp (character-listp acc))
  :inline t
  (b* (((printconfig config) config)
       ((when (integerp x))
        (if config.print-radix
            (radix-print-int x config.print-base acc)
          (basic-print-int x config.print-base acc)))
       ((when (rationalp x))
        (if config.print-radix
            (radix-print-rat x config.print-base acc)
          (basic-print-rat x config.print-base acc)))
       ((when (complex-rationalp x))
        (if config.print-radix
            (radix-print-complex x config.print-base acc)
          (basic-print-complex x config.print-base acc))))
    (raise "Bad atom")
    acc))

(define print-atom
  :short "Print any arbitrary atom with no escaping, but obeying print-base,
          print-radix, and (for symbols) print-lowercase."
  ((x      atom)
   (config printconfig-p)
   (acc))
  :returns (new-acc character-listp :hyp (character-listp acc))
  (b* (((when (symbolp x))
        (let ((name (symbol-name x)))
          (if (printconfig->print-lowercase config)
              (downcase-string-aux name 0 (length (the string name)) acc)
            (revappend-chars name acc))))
       ((when (characterp x))
        (cons x acc))
       ((when (stringp x))
        (revappend-chars x acc)))
    (print-atom-aux x config acc)))

(define print-escaped-charlist
  :short "Print a character list, escaping backslashes and some other character."
  ((x          character-listp "Characters in the name to be printed.")
   (slash-char characterp "Extra character to escape.  When printing escaped strings
                           this is typically the @('\"') character; for printing
                           symbol names it would typically be the @('|') character.")
   (acc))
  :returns (new-acc character-listp
                    :hyp (and (character-listp acc)
                              (character-listp x)))
  :long "<p>This is a logically nice definition for @(see print-escaped-str).</p>"
  (if (atom x)
      acc
    (print-escaped-charlist (cdr x)
                            slash-char
                            (if (or (eql (car x) #\\)
                                    (eql (car x) slash-char))
                                (list* (car x) #\\ acc)
                              (cons (car x) acc))))
  ///
  (defthm print-escaped-charlist-when-atom
    (implies (atom x)
             (equal (print-escaped-charlist x slash-char acc) acc)))

  (defthm len-of-print-escaped-charlist-weak
    (<= (len acc)
        (len (print-escaped-charlist x slash-char acc)))
    :rule-classes ((:rewrite) (:linear)))

  (defthm len-of-print-escaped-charlist-strong
    (implies (consp x)
             (< (len acc)
                (len (print-escaped-charlist x slash-char acc))))
    :rule-classes ((:rewrite) (:linear)))

  (local (defthm l0
           (implies (not (atom x))
                    (not (equal (print-escaped-charlist x slash-char acc) acc)))
           :hints(("Goal"
                   :do-not-induct t
                   :in-theory (disable len-of-print-escaped-charlist-strong)
                   :use ((:instance len-of-print-escaped-charlist-strong))))))

  (defthm equal-with-print-escaped-charlist
    (equal (equal (print-escaped-charlist x slash-char acc) acc)
           (atom x))
    :hints(("Goal" :cases ((equal (len (print-escaped-charlist x slash-char acc))
                                  (len acc)))))))

(define print-escaped-str-aux
  :parents (print-escaped-str)
  :short "Implementation of @(see print-escaped-str)."
  ((x          :type string)
   (n          :type unsigned-byte)
   (xl         :type unsigned-byte)
   (slash-char :type character)
   (acc))
  :measure (nfix (- (length x) (nfix n)))
  :guard (and (eql xl (length x))
              (<= n xl))
  (b* (((when (mbe :logic (zp (- (length x) (nfix n)))
                   :exec (eql n xl)))
        acc)
       ((the character c1) (char x n))
       ((the unsigned-byte n)
        (+ 1 (the unsigned-byte (mbe :logic (nfix n)
                                     :exec n)))))
    (print-escaped-str-aux x n xl slash-char
                                      (if (or (eql c1 #\\)
                                              (eql c1 slash-char))
                                          (list* c1 #\\ acc)
                                        (cons c1 acc))))
  ///
  (local (in-theory (enable print-escaped-charlist)))

  (defthm print-escaped-str-aux-removal
    (implies (and (stringp x)
                  (natp n)
                  (equal xl (length x))
                  (<= n xl))
             (equal (print-escaped-str-aux x n xl slash-char acc)
                    (print-escaped-charlist (nthcdr n (explode x)) slash-char acc)))
    :hints(("Goal"
            :induct (print-escaped-str-aux x n xl slash-char acc)
            :expand ((:free (slash-char)
                      (print-escaped-charlist (nthcdr n (explode x))
                                              slash-char acc)))
            :do-not '(generalize fertilize)
            :do-not-induct t))))

(define print-escaped-str
  :short "Print a string, escaping backslashes and some other character."
  ((x          stringp    "String or symbol name to be printed.")
   (slash-char characterp "Extra character to escape.  When printing escaped strings
                           this is typically the @('\"') character; for printing
                           symbol names it would typically be the @('|') character.")
   (acc))
  :returns (new-acc character-listp :hyp (character-listp acc))
  :inline t
  (mbe :logic
       (print-escaped-charlist (explode x) slash-char acc)
       :exec
       (print-escaped-str-aux x 0 (length (the string x)) slash-char acc)))

(define my-needs-slashes ((x      stringp)
                          (config printconfig-p))
  :inline t
  :long "<p>ACL2's similar function only checks whether we need symbols when
print-escape or print-readably are set.  I'm not going to bother with that, and
just assume that we always want to escape symbols that need escaping.</p>"
  (acl2::may-need-slashes-fn x (printconfig->print-base config)))

;; Eventually we may want to rip out acl2::may-need-slashes-fn and write
;; something ourselves...  first steps toward that...

;; (defcharset slashable
;;   (if (member x acl2::*slashable-chars*)
;;       t
;;     nil))

;; ; (slashable-chars) == 31901471824561578593433265577547273216

;; (declaim (inline my-identity))
;; (defun my-identity (x) x)

;; (let ((chars (loop for i from 0 to 255 collect (code-char i))))
;;   (time (loop for i fixnum from 1 to 10000000 do
;;               (loop for c in chars do
;;                     (my-identity c))))
;;   (time (loop for i fixnum from 1 to 10000000 do
;;               (loop for c in chars do
;;                     (str::char-in-charset-p c (str::slashable-chars)))))
;;   (time (loop for i fixnum from 1 to 10000000 do
;;               (loop for c in chars do
;;                     (svref *slashable-array* (char-code c)))))
;;   (loop for c in chars do
;;         (unless (equal (str::char-in-charset-p c (str::slashable-chars))
;;                        (svref *slashable-array* (char-code c)))
;;           (error "oops: ~a" c))))

(define in-home-package-p ((sym symbolp)
                           (config printconfig-p))
  :inline t
  (b* ((pkg-name      (symbol-package-name sym))
       (home-pkg-sym  (printconfig->home-package config)))
    (or (equal (symbol-package-name home-pkg-sym) pkg-name)
        ;; Ugh, expensive check.  Hopefully rare.
        (eq sym (intern-in-package-of-symbol (symbol-name sym) home-pkg-sym)))))

(define print-escaped-symbol
  ((x      symbolp)
   (config printconfig-p)
   (acc))
  :inline t
  :returns (new-acc character-listp :hyp (character-listp acc))
  (b* ((name        (symbol-name x))
       (lowercase-p (printconfig->print-lowercase config))
       ;; Symbol package part ---------------------
       (acc (b* (((when (keywordp x))
                  (cons #\: acc))
                 ((when (in-home-package-p x config))
                  ;; Don't need to print any package part.
                  acc)
                 (pkg-name (symbol-package-name x))
                 ((when (my-needs-slashes pkg-name config))
                  (let* ((acc (cons #\| acc))
                         (acc (print-escaped-str pkg-name #\| acc)))
                    (list* #\: #\: #\| acc)))
                 ((when lowercase-p)
                  (let* ((acc (downcase-string-aux pkg-name 0 (length pkg-name) acc)))
                    (list* #\: #\: acc))))
              (let* ((acc (str::revappend-chars pkg-name acc)))
                (list* #\: #\: acc))))
       ;; Symbol name part -------------------------
       ((when (my-needs-slashes name config))
        (let* ((acc (cons #\| acc))
               (acc (print-escaped-str name #\| acc)))
          (cons #\| acc)))
       ((when lowercase-p)
        (downcase-string-aux name 0 (length name) acc)))
    (str::revappend-chars name acc)))

(define print-escaped-atom
  :short "Print any arbitrary atom with suitable escaping, obeying the print-base,
          print-radix, print-lowercase, and home package settings."
  ((x      atom)
   (config printconfig-p)
   (acc))
  :returns (new-acc character-listp :hyp (character-listp acc))
  (b* (((when (symbolp x))
        (print-escaped-symbol x config acc))
       ((when (characterp x))
        (b* ((acc (list* #\\ #\# acc)))
          (case x
            (#\Newline (revappend-chars "Newline" acc))
            (#\Space   (revappend-chars "Space" acc))
            (#\Page    (revappend-chars "Page" acc))
            (#\Tab     (revappend-chars "Tab" acc))
            (#\Rubout  (revappend-chars "Rubout" acc))
            (#\Return  (revappend-chars "Return" acc))
            (otherwise (cons x acc)))))
       ((when (stringp x))
        (b* ((acc (cons #\" acc))
             (acc (print-escaped-str x #\" acc)))
          (cons #\" acc))))
    ;; Numbers get printed just as in print-atom, so no special handling is needed.
    (print-atom-aux x config acc)))



; ----------------------------------------------------------------------------
;
;             Size Estimation for "Flat" (all in one line) Printing
;
; ----------------------------------------------------------------------------

(define nat-size
  :short "How many characters are required to represent a natural number?"
  ((x          natp)
   (print-base print-base-p))
  :returns (size posp :rule-classes :type-prescription)
  :inline t
  (case (the (unsigned-byte 5) print-base)
    (10        (natsize x))
    (16        (natsize16 x))
    (8         (natsize8 x))
    (otherwise (natsize2 x))))

(define int-size
  :short "How many characters are required to represent an integer?"
  ((x integerp)
   (print-base print-base-p))
  :returns (size posp :rule-classes :type-prescription)
  (if (< x 0)
      (+ 1 (nat-size (- x) print-base))
    (nat-size x print-base)))

(define atom-size
  :short "How many characters are required to print an atom? (BOZO: roughly)"
  ((x      atom)
   (config printconfig-p))
  :returns (size posp :rule-classes :type-prescription)
  :long "<p>BOZO this doesn't seem quite right in certain cases.</p>

<p>Symbols: I don't think we're properly accounting for the empty symbol's
bars, or for any escape characters that we need for a symbol.</p>

<p>Complex rationals: I don't think we're accounting for the @('#c()')
parts.</p>"

  (cond ((symbolp x)
         ;; For symbols we add together the length of the "package part" and
         ;; the symbol name part.  We include the colons in the package part.
         (b* ((name      (symbol-name x))
              (name-size (if (my-needs-slashes name config)
                             ;; BOZO I don't understand this.  It seems like
                             ;; we aren't accounting for whatever escaping
                             ;; we're actually going to do.
                             (+ 2 (length name))
                           (length name)))
              ((when (keywordp x))
               (+ 1 name-size))
              (pkg-name     (symbol-package-name x))
              (home-package (printconfig->home-package config))
              ((when (or (equal (symbol-package-name home-package) pkg-name)
                         ;; Ugh, expensive case.  Hopefully rare.  BOZO this
                         ;; looks to be much faster than ACL2's approach.
                         ;; Mention this to Matt.
                         (eq x (intern-in-package-of-symbol name home-package))))
               name-size)
              (pkg-size (if (my-needs-slashes pkg-name config)
                            (+ 4 (length pkg-name))
                          (+ 2 (length pkg-name)))))
           (+ name-size pkg-size)))

        ((integerp x)
         (b* ((base   (printconfig->print-base config))
              (radixp (printconfig->print-radix config))
              (size   (int-size x base))
              ((unless radixp)
               size)
              ((when (eql base 10))
               ;; `.' suffix
               (+ 1 size)))
           ;; #b, #o, or #x prefix
           (+ 2 size)))

        ((characterp x)
         (case x
           (#\Newline 9)
           (#\Rubout 8)
           (#\Return 8)
           (#\Space 7)
           (#\Page 6)
           (#\Tab 5)
           (otherwise 3)))

        ((stringp x)
         (+ 2 (length x)))

        ((rationalp x)
         (b* ((base   (printconfig->print-base config))
              (radixp (printconfig->print-radix config))
              (size   (int-size (numerator x) base))
              (size   (+ size (int-size (denominator x) base)))
              ((unless radixp) ;; Add 1 for the / character
               (+ 1 size))
              ((when (eql base 10)) ;; #10r prefix and / character
               (+ 5 size)))
           ;; #b, #o, or #x prefix
           (+ 3 size)))

        ((complex-rationalp x)
         ;; BOZO I don't understand this either.  Shouldn't we be accounting
         ;; for the #c( ) stuff?
         (+ (atom-size (realpart x) config)
            (atom-size (imagpart x) config)))

        (t
         (progn$
          (raise "Bad atom.")
          1)))

  :prepwork
  ((local (defthm l0
            (implies (and (stringp x)
                          (not (my-needs-slashes x config)))
                     (posp (len (explode x))))
            :hints(("Goal"
                    :in-theory (e/d (my-needs-slashes)
                                    ;; Speed hint
                                    (acl2::member-of-cons
                                     acl2::subsetp-of-cons
                                     subsetp-equal
                                     member-equal))))))))

; Evisceration.
;
; ACL2's notion of evisceration is basically that parts of the term to be
; printed can be replaced with (:evisceration-mark . "replacement text").  In
; various places, ACL2's printer relies on the replacement text being a string,
; but ACL2's evisceratedp macro doesn't check for this.  We'll be sure to
; check.
;
; I hard-code *evisceration-mark* to avoid a special lookup everywhere.

(local (assert-event (equal acl2::*evisceration-mark* :EVISCERATION-MARK)))

(define evisceratedp (x)
  :inline t
  (declare (xargs :guard (consp x)))
  (and (eq (car x) :evisceration-mark)
       (stringp (cdr x))))

(define eviscerated->guts ((x (and (consp x)
                                   (evisceratedp x))))
  :inline t
  :returns (guts stringp :rule-classes :type-prescription)
  :prepwork ((local (in-theory (enable evisceratedp))))
  (mbe :logic (str-fix (cdr x))
       :exec (cdr x)))

(define obj-size
  :short "How many characters are required to print an object. (bounded)"
  ((x                     "Object whose size we are counting.")
   (size    natp          "Size we've counted up so far.")
   (max     natp          "Limit on how large of a size to compute.")
   (eviscp  booleanp      "Is evisceration enabled?")
   (config  printconfig-p "For settings like print-base, etc."))
  :returns (size posp :rule-classes :type-prescription)
  :verify-guards nil
  (b* ((size (lnfix size))
       (max  (lnfix max))
       ((when (> size max))
        size)
       ((when (atom x))
        (+ size (atom-size x config)))
       ((when (and eviscp (evisceratedp x)))
        ;; SUBTLE: If we don't know the eviscerated guts are non-nil, we can
        ;; only get a NATP type prescription instead of a POSP.  It seems safe
        ;; to fudge it.  We should never see empty eviscerations, right?
        (+ size (max 1 (length (eviscerated->guts x)))))
       ((when (atom (cdr x)))
        (if (not (cdr x))
            ;; (a . NIL) --> (a), so sizeof(a)+2 for the parens
            (obj-size (car x) (+ 2 size) max eviscp config)
          ;; (a . b) --> (a . b), so sizeof(a)+sizeof(b)+5 for the parens and dots
          (obj-size (cdr x)
                    (obj-size (car x) (+ 5 size) max eviscp config)
                    max eviscp config)))
       ((when (and (eq (car x) 'quote)
                   (consp (cdr x))
                   (null (cddr x))))
        ;; (QUOTE a) --> 'a, so sizeof(a)+1 for the quote mark
        (obj-size (cadr x) (+ 1 size) max eviscp config)))
    ;; (A B ...); we don't count parens because they get accounted for when we reach
    ;; the atom of cdr case.  Just add one for the space.
    (obj-size (cdr x)
              (obj-size (car x) (+ 1 size) max eviscp config)
              max eviscp config))
  ///
  (verify-guards obj-size))


; ----------------------------------------------------------------------------
;
;                       Pretty Printer Instructions
;
; ----------------------------------------------------------------------------

(define keyword-fix ((x keywordp))
  :returns (x-fix keywordp)
  (mbe :logic (if (keywordp x)
                  x
                :default)
       :exec x)
  ///
  (defthm keyword-fix-when-keywordp
    (implies (keywordp x)
             (equal (keyword-fix x)
                    x))))

(fty::deffixtype keyword
  :pred keywordp
  :fix keyword-fix
  :equiv keyword-equiv
  :define t
  :forward t
  :topic keywordp)

(fty::defprod pflat
  :parents (printer-instructions)
  :short "Print some objects all on one line."
  :tag nil
  :layout :tree
  ((width posp "The width of what will be printed.")
   (what       "The object(s) to print flat."))

  :long "<p>Think of @('what') as a (perhaps improper) list.  This instruction
means to print the elements of @('what'), and its final cdr, separated
appropriately by spaces or dot.</p>

<p>Usually @('what') is a proper list, say @('(X1 ... XN)').  In this case, we
print these elements, separated by spaces, all on one line.</p>

<p>When @('what') is instead an improper list, say @('(X1 ... XN . LAST)'), we
again print the Xi separated by spaces, but then also print @('. LAST').
Here @('last') might be some (non-nil) atom or an eviscerated object.</p>

<p>When @('what') is a single, non-NIL atom, we print @('. WHAT').  Note that
this doesn't correspond to any actual Lisp object in isolation.  That is, no
Lisp object prints as @('. FOO').</p>")

(fty::deftypes printer-instructions
  :short "Internal \"instruction\" data structure used by our pretty-printing
algorithm."

  :long "<p>Our pretty-printing algorithm operates in two linear passes.  The
first pass builds a list of <i>printer instructions</i> (\"pinst\" structures)
that tell the second pass how to print.  (In ACL2's pretty-printer, these
structures are referred to as \"ppr tuples\".)</p>

<p>We now define the valid kinds of printer instructions.  To understand these,
it is very helpful to start with @(see print-instruction), the <i>second</i>
pass of pretty-printing, which follows these instructions to produce its
output.  You can basically think of @('print-instruction') as an evaluator that
gives these instructions their semantics.</p>"

  (fty::deftagsum pinst
    (:flat
     :layout :tree
     ;:short "Tagged version of a flat instruction; see @(see pflat-p)."
     ((guts pflat-p)))

    (:keyline ;; in ACL2's ppr tuples, this is a matched-keyword
     :layout :tree
     ;; KEYWORD(WIDTH, KWD) prints exactly like FLAT(WIDTH, (KWD)), i.e., we just
     ;; print KWD.  This is a special kind of instruction used for alternating
     ;; :keyword value lists.  KWD is always a keyword and will always appear on
     ;; a line by itself.  Its associated value will appear below it in the
     ;; column because we tried to put them on the same line but we did not have
     ;; room.
     ((guts pflat-p)))

    (:dot
     :layout :tree
     ;; DOT(WIDTH) prints a dot.  The WIDTH should always be 1.
     ((width posp)))

    (:quote
     :layout :tree
     ;; QUOTE(WIDTH, GUTS) - Print a single-quote followed by pretty printing the
     ;; printer instruction GUTS.
     ((width posp)
      (guts  pinst-p)))

    (:wide
     :layout :tree
     ;; WIDE(WIDTH, FIRST, REST).  Here FIRST is a FLAT instruction. We print an
     ;; open paren, the contents of first, a space, and then we prettyprint each
     ;; of the REST instructions in a column.  When we're done, we print a close
     ;; paren.  The width of the longest line we will print is width.
     ((width posp)
      (first pflat-p)
      (rest  pinstlist-p)))

    (:keypair
     :layout :tree
     ;; KEYPAIR(WIDTH, KWD, VALUE).  Here, KWD is a FLAT instruction.  We print
     ;; it, a space, and then print VALUE.  The length of the longest line we
     ;; will print is width.
     ((width posp)
      (kwd   pflat-p)
      (value pinst-p)))

    (:indent
     :layout :tree
     ;; INDENT(I, WIDTH, FIRST, REST) We print an open paren, prettyprint
     ;; FIRST, then do a newline.  Then we prettyprint the remaining REST in
     ;; the column that is i to the right of the paren.  We conclude with a
     ;; close paren.  The width of the longest line we will print is n.
     ((amount natp)
      (width  posp)
      (first  pinst-p)
      (rest   pinstlist-p)))
    )

  (fty::deflist pinstlist
    :elt-type pinst-p))

(std::deflist pinstlist-p (x)
  (pinst-p x)
  :already-definedp t)

(define pinst->width ((x pinst-p))
  :returns (width posp :rule-classes :type-prescription)
  (pinst-case x
    :flat    (pflat->width x.guts)
    :keyline (pflat->width x.guts)
    :dot     x.width
    :quote   x.width
    :wide    x.width
    :keypair x.width
    :indent  x.width))

(define pinstlist->max-width ((x pinstlist-p) (maximum integerp))
  :returns (maximum integerp :rule-classes :type-prescription)
  (b* (((when (atom x))
        (acl2::lifix maximum))
       (width1 (pinst->width (car x)))
       ((when (> width1 maximum))
        (pinstlist->max-width (cdr x) width1)))
    (pinstlist->max-width (cdr x) maximum)))

(define pprdot ()
  :inline t
  (make-pinst-dot :width 1))


; ----------------------------------------------------------------------------
;
;                     Printing Instructions (Pass 2)
;
; ----------------------------------------------------------------------------

(defines print-flat

  ;; This is based on acl2's flpr1.

  (define print-flat (x
                      (config printconfig-p)
                      (eviscp booleanp)
                      acc)
    :measure (acl2::two-nats-measure (acl2-count x) (if x 3 0))
    :returns (new-acc character-listp :hyp (character-listp acc))
    (cond ((atom x)
           (print-escaped-atom x config acc))
          ((and eviscp (evisceratedp x))
           (print-atom (eviscerated->guts x) config acc))
          ((and (eq (car x) 'quote)
                (consp (cdr x))
                (not (cddr x)))
           (print-flat (second x) config eviscp (cons #\' acc)))
          (t
           (print-flat-aux x config eviscp (cons #\( acc)))))

  (define print-flat-aux ((x consp)
                          (config printconfig-p)
                          (eviscp booleanp)
                          acc)
    :measure (acl2::two-nats-measure (acl2-count x) (if x 2 1))
    :returns (new-acc character-listp :hyp (character-listp acc))
    (b* ((acc (print-flat (car x) config eviscp acc))
         ((when (not (cdr x)))
          (cons #\) acc))
         ((when (or (atom (cdr x))
                    (and eviscp (evisceratedp (cdr x)))))
          (b* ((acc (list* #\Space #\. #\Space acc))
               (acc (print-flat (cdr x) config eviscp acc)))
            (cons #\) acc)))
         (acc (cons #\Space acc)))
      (print-flat-aux (cdr x) config eviscp acc))))

(define print-flat-objs (x
                         (config printconfig-p)
                         (eviscp booleanp)
                         acc)
  :short "We print the elements of @('x'), separated by spaces.  If @('x') is a
          non-nil atom, we print a dot and then @('x')."
  :long "<p>See the discussion in @(see pflat-p): @('x') here is the @('what')
         field from some pflat object.</p>"
  :returns (new-acc character-listp :hyp (character-listp acc))
  (cond ((not x) acc)
        ((or (atom x)
             (and eviscp (evisceratedp x)))
         (b* ((acc (cons #\. acc))
              (acc (cons #\Space acc)))
           (print-flat x config eviscp acc)))
        (t
         (b* ((acc (print-flat (car x) config eviscp acc))
              ((unless (cdr x))
               acc)
              (acc (cons #\Space acc)))
           (print-flat-objs (cdr x) config eviscp acc)))))

(define spaces1 ((n                 natp)
                 (col               natp)
                 (hard-right-margin posp)
                 (acc))
  :returns (new-acc character-listp :hyp (character-listp acc))
  :measure (acl2::two-nats-measure (nfix n)
                                   (nfix (- (nfix col)
                                            (acl2::pos-fix hard-right-margin))))
  (b* ((n                 (nfix n))
       (col               (nfix col))
       (hard-right-margin (acl2::pos-fix hard-right-margin)))
    (cond ((zp n) acc)
          ((> col hard-right-margin)
           (spaces1 n 0 hard-right-margin (cons #\Newline acc)))
          (t
           (spaces1 (- n 1) (+ 1 col) hard-right-margin (cons #\Space acc))))))

(define spaces ((n      natp)
                (col    natp)
                (config printconfig-p)
                acc)
  :returns (new-acc character-listp :hyp (character-listp acc))
  (b* (((printconfig config) config)
       (result-col (+ n col))
       ((when (<= result-col config.hard-right-margin))
        (make-list-ac n #\Space acc)))
    (spaces1 n col config.hard-right-margin acc)))


(defines print-instruction

;; print-column is like acl2's ppr2-column
;; print-instruction is like acl2's ppr2

  (define print-column
    :short "Print a list of instructions in a column."
    ((x      pinstlist-p      "Instructions to print in a column.")
     (loc    natp             "Current location we're at.")
     (col    natp             "Location to indent to.")
     (config printconfig-p)
     (eviscp booleanp)
     acc)
    :returns (new-acc character-listp :hyp (character-listp acc))
    :measure (pinstlist-count x)
    :flag :col
    :guard (<= loc col)
    (declare (type unsigned-byte loc col))
    ;; uncomment for better tracing
    ;; (declare (notinline print-instruction print-column))
    :split-types t
    (b* (((when (atom x))
          acc)
         (acc (spaces (the unsigned-byte (- col loc)) loc config acc))
         (acc (print-instruction (car x) col config eviscp acc))
         ((when (atom (cdr x)))
          acc)
         (acc (cons #\Newline acc)))
      (print-column (cdr x) 0 col config eviscp acc)))

  (define print-instruction
    :short "Print as directed by a printing instruction."
    ((x      pinst-p)
     (col    natp)
     (config printconfig-p)
     (eviscp booleanp)
     (acc))
    :returns (new-acc character-listp :hyp (character-listp acc))
    :measure (pinst-count x)
    :flag :inst
    :split-types t
    (declare (type unsigned-byte col))
    ;; uncomment for better tracing
    ;; (declare (notinline print-instruction print-column))
    (pinst-case
     x
     :flat    (print-flat-objs (pflat->what x.guts) config eviscp acc)
     :keyline (print-flat-objs (pflat->what x.guts) config eviscp acc)
     :dot     (cons #\. acc)
     :quote   (print-instruction x.guts
                                 (the unsigned-byte (+ 1 col))
                                 config eviscp (cons #\' acc))
     :keypair (b* ((acc (print-flat-objs (pflat->what x.kwd) config eviscp acc))
                   (acc (cons #\Space acc)))
                (print-instruction x.value
                                   (the unsigned-byte
                                        (+ col (+ 1 (the unsigned-byte (pflat->width x.kwd)))))
                                   config eviscp acc))
     :wide    (b* ((acc (cons #\( acc))
                   (acc (print-flat-objs (pflat->what x.first) config eviscp acc))
                   ((the unsigned-byte width) (pflat->width x.first))
                   ((the unsigned-byte col)
                    (+ col (the unsigned-byte (+ 1 (the unsigned-byte width)))))
                   (acc (print-column x.rest col (the unsigned-byte (+ 1 col))
                                      config eviscp acc)))
                (cons #\) acc))
     :indent  (b* ((acc (cons #\( acc))
                   ((the unsigned-byte col) (+ col (the unsigned-byte x.amount)))
                   (acc (print-instruction x.first col config eviscp acc))
                   ((unless x.rest)
                    (cons #\) acc))
                   (acc (cons #\Newline acc))
                   ;; bozo recomputing sum
                   (acc (print-column x.rest 0 col config eviscp acc)))
                (cons #\) acc)))))



; ----------------------------------------------------------------------------
;
;                     Generating Instructions (Pass 1)
;
; ----------------------------------------------------------------------------

(define keyword-param-valuep
  :short "Does a pretty-printer instruction represent a single object, which
          could plausibly be the value of a keyword parameter?"
  ((x      pinst-p)
   (eviscp booleanp))
  :returns bool
  :long "<p>The only kinds of instructions we don't match are:</p>
<ul>
<li>KEYPAIR instructions,</li>
<li>FLAT instructions representing dotted objects `. atm',</li>
<li>FLAT instructions representing several objects `a b c', and</li>
<li>KEYWORD instructions, which represent keywords whose associated
    values are on the next line.  These wouldn't be provided as the
    value of a keyword argument.</li>
</ul>"
  :guard-hints(("Goal" :in-theory (enable pinst-p)))
  (case (pinst-kind x)
    (:flat
     ;; FLAT tuples could represent one or many objects.  Does it represent
     ;; exactly one object?
     (b* ((what (pflat->what (pinst-flat->guts x)))
          ((when (or (atom what)
                     (and eviscp (evisceratedp what))))
           ;; FLAT instruction representing ``. FOO'', not a single object.
           nil))
       ;; Flat object representing (x1 x2 ... xn . final-cdr)
       ;; represents one object iff it has the shape (x1 . nil)
       (not (cdr what))))
    ((:quote :wide :indent)
     t)
    (otherwise
     nil)))



; Notes about CONS-PPR from ACL2:
;
; We want to build a tuple to print a given list form, like a function call.
; We basically get the tuple for the car and a list of tuples for the cdr and
; then use cons-ppr1 to combine them.  The resulting list of tuples will be
; embedded in either a WIDE or an indent tuple.  Thus, this list of tuples we
; will create describes a column of forms.  The number of items in that column
; is not necessarily the same as the number of arguments of the function call.
; For example, the term (f a b c) might be pretty-printed as
; (f a
;    b c)
; where b and c are printed flat on a single line.  Thus, the three arguments
; of f end up being described by a list of two tuples, one for a and another
; for b and c.

; To form lists of tuples we just use cons-ppr1 to combine the tuples we get
; for each element.

; Let x and lst be, respectively, a ppr tuple for an element and a list of
; tuples for list of elements.  Think of lst as describing a column of forms.
; Either x can become another item that column, or else x can be incorporated
; into the first item in that column.  For example, suppose x will print as X
; and lst will print as a column containing y1, y2, etc.  Then we have this
; choice for printing x and lst:

; lengthened column          lengthened first row
; x                          x y1
; y1                         y2
; ...                        ...

; We get the `lengthened column' behavior if we just cons x onto lst.  We get
; the `lengthened row' behavior if we merge the tuples for x and y1.  But we
; only merge if they both print flat.

; Essay on the Printing of Dotted Pairs and

; It is instructive to realize that we print a dotted pair as though it were a
; list of length 3 and the dot was just a normal argument.

; In the little table below I show, for various values of d, two things: the
; characters output by

; (ppr2 (ppr1 `(xx . yy) (print-base) (print-radix) d 0 state nil)
;       0 *standard-co* state nil)

; and the ppr tuple produced by the ppr1 call.
;
; d         output                 ppr tuple

;        |<-  9  ->|

; 9       (XX . YY)              (FLAT 9 (XX . YY))

; 8       (XX                    (3 8 (FLAT 2 XX) (FLAT 5 . YY))
;            . YY)

; 7       (XX                    (2 7 (FLAT 2 XX) (FLAT 5 . YY))
;           . YY)

; 6       (XX                    (1 6 (FLAT 2 XX) (FLAT 5 . YY))
;          . YY)

; 5       (XX                    (2 5 (FLAT 2 XX) (DOT 1) (FLAT 3 YY))
;           .
;           YY)

; 4       (XX                    (1 4 (FLAT 2 XX) (DOT 1) (FLAT 3 YY))
;          .
;          YY)

; The fact that the dot is not necessarily connected to (on the same line as)
; the atom following it is the reason we have the (DOT 1) tuple.  We have to
; represent the dot so that its placement is first class.  So when we're
; assembling the tuple for a list, we cdr down the list using cons-ppr1 to put
; together the tuple for the car with the tuple for the cdr.  If we reach a
; non-nil cdr, atm, we call cons-ppr1 on the dot tuple and the tuple
; representing the atm.  Depending on the width we have, this may produce (FLAT
; n . atm) which attaches the dot to the atm, or ((DOT 1) (FLAT n atm)) which
; leaves the dot on a line by itself.

; We want keywords to appear on new lines.  That means if the first element of
; lst is a keyword, don't merge (unless x is one too).

; BUG
; ACL2 p!>(let ((x '(foo bigggggggggggggggg . :littlllllllllllllle)))
;          (ppr2 (ppr1 x (print-base) (print-radix) 40 0 state nil)
;                0 *standard-co* state nil))
; (x   = (DOT 1)
; lst = ((FLAT 21 :LITTLLLLLLLLLLLLLLE))
; val = ((FLAT 23 . :LITTLLLLLLLLLLLLLLE)))
;
; HARD ACL2 ERROR in CONS-PPR1:  I thought I could force it!

;; BOZO rename column to ROWS.

(define maybe-merge-flat
  :short "Basic merging of flat singleton objects into rows."
  ((x      pinst-p     "Instruction for the car of the list.")
   (rows   pinstlist-p "Instructions for the cdr of the list.")
   (width  natp        "Width we're trying to stay within.")
   (config printconfig-p))
  :guard (and (eq (pinst-kind x) :flat)
              (let ((what (pflat->what (pinst-flat->guts x))))
                (and (consp what)
                     (not (cdr what))))
              (consp rows))
  :returns (new-rows pinstlist-p)
  (b* ((x    (pinst-fix x))
       (rows (pinstlist-fix rows))
       (row1 (car rows))
       ((unless (eq (pinst-kind row1) :flat))
        ;; Don't merge into complex rows.
        (cons x rows))
       (x.guts       (pinst-flat->guts x))
       (row1.guts    (pinst-flat->guts row1))
       ((the unsigned-byte row1.width)   (pflat->width row1.guts))
       ((the unsigned-byte x.width)      (pflat->width x.guts))
       ((the unsigned-byte merged-width) (+ 1 (the unsigned-byte (+ x.width row1.width))))
       ((the unsigned-byte flat-right-margin)
        (printconfig->flat-right-margin config))
       ((unless (and (<= merged-width flat-right-margin)
                     (<= merged-width width)))
        ;; The result would be either (1) wider than we like, or (2) too wide
        ;; to fit into the width that we're trying to stay within.  So, don't
        ;; do the merge.
        (cons x rows))
       (x.what       (pflat->what x.guts))
       (row1.what    (pflat->what row1.guts))
       (merged-guts  (make-pflat :width merged-width
                                 :what  (cons (car x.what) row1.what)))
       (merged-inst  (make-pinst-flat :guts merged-guts)))
    (cons merged-inst (rest rows))))

(local (in-theory (disable keywordp)))


(define cons-ppr1
  ((x                 pinst-p
                      "A single printer instruction, representing either a DOT
                       or a single object.  Intuitively this is the instruction
                       for the @('car') of the list we're trying to print.")
   (rows              pinstlist-p
                      "A list of printer instructions that will be printed as a
                       column.  Intuitively these are the instructions for the
                       @('cdr') of the list we're trying to print.")
   (width             posp)
   (config            printconfig-p)
   (eviscp            booleanp))
  :guard (case (pinst-kind x)
           (:flat (let ((what (pflat->what (pinst-flat->guts x))))
                    (and (consp what)
                         (not (cdr what)))))
           (otherwise
            t))
  :returns (new-rows pinstlist-p)
  :guard-debug t

  :long "<p>The goal here is to add @('x') to @('rows') by either merging it
with the first row or&mdash;if that won't work because it's too wide&mdash;by
putting it into a new row.  For instance, @('x') might be @('(FLAT 3 ABC)') and
@('rows') could be @('((FLAT 7 DEF GHI) ...)').  In this case we need to decide
to either:</p>

@({
    add a new row                   merge with the first row
    ABC                    -or-     ABC DEF GHI
    DEF GHI                         ...
    ...
})

<p>The default behavior is always to add a new row, i.e., to just cons @('x')
onto @('rows').  But if the first row is flat, and we can fit @('x') onto it
without using up too many characters, then we should extend the first row.</p>

<p>It is also here that we deal specially with keywords.  If @('x') is @('(FLAT
3 :ABC)') and column is @('((...) (...))') then we have the choice:</p>

@({
    add a new row                   merge with the first row
    :ABC                   -or-     :ABC (...)
    (...)                           (...)
    (...)
})"

  (b* ((x (pinst-fix x))
       (rows (pinstlist-fix rows))
       ((when (atom rows))
        ;; Can't lengthen the first row since there aren't any rows yet.
        (cons x rows))
       (xkind (pinst-kind x))
       ((when (eq xkind :flat))
        (b* ((x.guts (pinst-flat->guts x))
             (x.what (pflat->what x.guts))
             (x.obj  (first x.what))
             ((unless (or (atom x.obj)
                          (and eviscp (evisceratedp x.obj))))
              ;; Not atomic, don't merge it.
              (cons x rows))
             (row1 (first rows))
             ((unless (and (keywordp x.obj)
                           (keyword-param-valuep row1 eviscp)))
              ;; Doesn't look like :foo value, merge using normal rules
              (maybe-merge-flat x rows width config))
             ;; At this point, we've found what looks like a key/value pair,
             ;; x/row1.  If the rest of the rows look like keyword/value pairs,
             ;; then we should associate x/row1 together.  But if not, then we
             ;; want to treat key just as any other atom.  How can we tell
             ;; whether the rest of the rows are keyword/value pairs?  It's
             ;; enough to check row2, because if there were any non
             ;; keyword/value pairs later on, we would have not created a
             ;; keyword/keypair instruction here.)
             ((unless (or (atom (rest rows))
                          (eq (pinst-kind (second rows)) :keypair)
                          (eq (pinst-kind (second rows)) :keyline)))
              ;; The rest is NOT an alternating keyword/value list, so just
              ;; treat keyword like a normal atom.
              (maybe-merge-flat x rows width config))
             ((the unsigned-byte x.width)    (pflat->width x.guts))
             ((the unsigned-byte row1.width) (pinst->width row1))
             ;; We consider making a keypair of width n = width of key, plus
             ;; space, plus width of widest line in row1.  Note that we don't
             ;; mind this running over the standard 40 character max line
             ;; length because it is so iconic.
             (keypair-width (+ 1 x.width row1.width))
             ((when (<= keypair-width width))
              (cons (make-pinst-keypair :width keypair-width
                                        :kwd x.guts
                                        :value row1)
                    (cdr rows))))
          ;; Otherwise, we put x on a newline and leave the rows as they were.
          ;; Note that we convert x from a FLAT to a KEYLINE, so insure that it
          ;; stays on a line by itself and to keyword/value pairs encountered
          ;; above us in the bottom-up processing to be paired with KEYPAIR.
          (cons (make-pinst-keyline :guts x.guts) rows)))
       ((when (eq xkind :dot))
        (b* ((row1 (first rows))
             ((unless (eq (pinst-kind row1) :flat))
              (cons x rows))
             ;; Claim: In this case we know row1's first object is an atom or
             ;; an eviscerated object.
             (row1.guts         (pinst-flat->guts row1))
             (row1.width        (pflat->width row1.guts))
             (merged-width      (+ 2 row1.width)) ;; Dot plus space
             (flat-right-margin (printconfig->flat-right-margin config))
             ((unless (and (<= merged-width flat-right-margin)
                           (<= merged-width width)))
              (cons x rows))
             (new-guts (make-pflat :width merged-width
                                   :what
                                   (ec-call (car (pflat->what row1.guts))))))
          (cons (make-pinst-flat :guts new-guts)
                (cdr rows)))))
    (cons x rows)))


(defines ppr1

  (define ppr1
    ((x           "The object to be pretty printed.")
     (rpc natp    "Right paren count -- number of right parens that will follow
                   the printed version of x.  For example, in printing the x
                   in (f (g (h x)) u) there will always be 2 right parens after
                   it.  So we cannot let x use the entire available width, only
                   the width-2.  Rpc would be 2.")
     (width  posp)
     (config printconfig-p)
     (eviscp booleanp))
    :returns (inst pinst-p)
    :verify-guards nil
    :measure (acl2::two-nats-measure (acl2-count x) 0)
    (b* (((printconfig config) config)
         (size (obj-size x rpc width eviscp config))

         ((when (or (atom x)
                    (and eviscp (evisceratedp x))
                    (and (<= size width)
                         (<= size config.flat-right-margin))))
          (make-pinst-flat :guts (make-pflat :width size :what (list x))))

         (width-1
          ;; Stupid hack to make sure width always stays positive.
          (max 1 (- width 1)))

         ((when (and (eq (car x) 'quote)
                     (consp (cdr x))
                     (not (cddr x))))
          (let* ((guts (ppr1 (second x) rpc width-1 config eviscp)))
            (make-pinst-quote :width (+ 1 (pinst->width guts))
                              :guts  guts)))

         ;; When printing the cdr of x, give each argument the full width
         ;; (minus 1 for the minimal amount of indenting).  Note that x2
         ;; contains the ppr tuples for the car and the cdr.
         (first (ppr1 (car x) (if (cdr x) 0 (+ 1 rpc)) width-1 config eviscp))
         (rest  (ppr1-lst (cdr x) (+ 1 rpc) width-1 config eviscp))

         ((unless (or (atom (car x))
                      (and eviscp (evisceratedp (car x)))))
          ;; Not a function basic kind of call -- could be a lambda or any
          ;; other kind of Lisp object whose car is compound.
          (b* ((maximum (pinstlist->max-width rest (pinst->width first))))
            (make-pinst-indent :amount 1
                               :width  (+ 1 maximum)
                               :first  first
                               :rest   rest)))

         ;; Otherwise the CAR is an atom and we can print in the usual way.
         ;; Get the max width of any single argument, not counting the function
         ;; symbol.
         (maximum (pinstlist->max-width rest
                                        ;; ACL2 uses -1 here.  If rest happens to be NIL,
                                        ;; then this -1 goes through??? wtf is going on here?
                                        -1))

         (first.guts ;; why do we know this is flat????
          (pinst-flat->guts first))

         ;; We can print WIDE if we have room for an open paren, the fn, a
         ;; space, and the widest argument.
         (wide-width (+ (pinst->width first) (+ 2 maximum)))
         ((when (<= wide-width width))
          (make-pinst-wide :width wide-width
                           :first first.guts
                           :rest  rest))

         ((when (< maximum width))
          ;; If the maximum is less than the width, we can do exact indenting
          ;; of the arguments to make the widest argument come out on the right
          ;; margin.  This exactness property is one of the things that makes
          ;; this algorithm produce such beautiful output: we get the largest
          ;; possible indentation, which makes it easy to identify peer
          ;; arguments.  How much do we indent?  width-maximum will guarantee
          ;; that the widest argument ends on the right margin.  However, we
          ;; believe that it is more pleasing if argument columns occur at
          ;; regular indents.  So we limit our indenting to 5 and just give up
          ;; the white space over on the right margin.  Note that we compute
          ;; the width of the whole term accordingly.
          (b* ((amount (min 5 (- width maximum)))
               ;(?test1 (the (satisfies posp) amount))
               (?test2 (the (satisfies posp) (+ maximum amount)))
               )
            (make-pinst-indent :amount amount
                               :width  (+ maximum amount)
                               :first  first
                               :rest   rest))))
      ;; If maximum is not less than width, we indent by 1.
      (make-pinst-indent :amount 1
                         :width  (+ 1 maximum)
                         :first  first
                         :rest   rest)))

  (define ppr1-lst
    ((lst)
     (rpc    natp)
     (width  posp)
     (config printconfig-p)
     (eviscp booleanp))
    :returns (insts pinstlist-p)
    ;; The next function computes a ppr tuple for each element of lst.
    ;; Typically these are all arguments to a function.  But of course, we
    ;; prettyprint arbitrary constants and so have to handle the case that the
    ;; list is not a true-list.
    :measure (acl2::two-nats-measure (acl2-count lst) 1)
    (cond ((atom lst)
           ;; If the list is empty and null, then nothing is printed (besides
           ;; the parens which are being accounted for otherwise).  If the list
           ;; is terminated by some non-nil atom, we will print a dot and the
           ;; atom.  We do that by merging a dot tuple into the flat for the
           ;; atom, if there's room on the line, using cons-ppr1.  Where this
           ;; merged flat will go, i.e., will it be indented under the car as
           ;; happens in the Essay on the Printing of Dotted Pairs, is the
           ;; concern of ppr1-lst, not the cons-ppr1.  The cons-ppr1 below just
           ;; produces a merged flat containing the dot, if the width permits.
           (and lst
                (cons-ppr1 (pprdot)
                           (list (ppr1 lst rpc width config eviscp))
                           width config eviscp)))
          ((and eviscp (evisceratedp lst))
           ;; The case for an eviscerated terminal cdr is handled the same way.
           (cons-ppr1 (pprdot)
                      (list (ppr1 lst rpc width config eviscp))
                      width config eviscp))
          ((null (cdr lst))
           ;; If the list is a true singleton, we just use ppr1 and we pass it
           ;; the rpc that was passed in because this last item will be
           ;; followed by that many parens on the same line.
           (list (ppr1 (car lst) rpc width config eviscp)))
          (t
           ;; Otherwise, we know that the car is followed by more elements.  So
           ;; its rpc is 0.
           (cons-ppr1 (ppr1 (car lst) 0 width config eviscp)
                      (ppr1-lst (cdr lst) rpc width config eviscp)
                      width config eviscp)))))

(local (in-theory (enable ppr1 ppr1-lst)))

(defthm lower-bound-of-pinstlist->max-width
  (<= (ifix maximum) (pinstlist->max-width x maximum))
  :rule-classes ((:rewrite) (:linear))
  :hints(("Goal" :in-theory (enable pinstlist->max-width))))

(defthm pinst->width-of-make-pinst-flat
  (equal (pinst->width (make-pinst-flat :guts guts))
         (pflat->width guts))
  :hints(("Goal" :in-theory (enable pinst->width))))

(defthm pinstlist->max-width-negative
  (implies (and (consp x)
                (integerp maximum))
           (< 0 (pinstlist->max-width x maximum)))
  :hints(("Goal" :in-theory (enable pinstlist->max-width))))

(defthm pinstlist->max-width-negative-1
  (equal (equal (pinstlist->max-width x -1) -1)
         (atom x))
  :hints(("Goal" :in-theory (enable pinstlist->max-width))))

(defthm lower-bound-of-pinstlist->max-width-alt
  (implies (integerp maximum)
           (<= maximum (pinstlist->max-width x maximum)))
  :rule-classes ((:rewrite) (:linear))
  :hints(("Goal" :in-theory (enable pinstlist->max-width))))

(defthm atom-of-ppr1-lst
  (equal (consp (ppr1-lst x rpc width config eviscp))
         (if x t nil))
  :hints(("Goal" :expand (ppr1-lst x rpc width config eviscp))))

(local (in-theory (disable (force))))

(defthm flat-constraint
  (let ((inst (ppr1 x rpc width config eviscp)))
    (implies (equal (pinst-kind inst) :flat)
             (and (consp (pflat->what (pinst-flat->guts inst)))
                  (not (cdr (pflat->what (pinst-flat->guts inst)))))))
  :hints(("Goal"
          :expand (ppr1 x rpc width config eviscp)
          :do-not '(generalize fertilize eliminate-destructors)
          :do-not-induct t)))

(verify-guards ppr1
  :hints(("Goal"
          :do-not '(generalize fertilize eliminate-destructors)
          :do-not-induct t)))



; ----------------------------------------------------------------------------
;
;                      Top-Level Pretty Printing
;
; ----------------------------------------------------------------------------


(define ppr
  :short "Low-level routine to do both passes of pretty-printing."
  ((x                    "Any ACL2 object to be printed.")
   (col    natp          "Current column number.")
   (config printconfig-p)
   (eviscp booleanp)
   (acc))
  :returns (new-acc character-listp :hyp (character-listp acc))
  :long "<p>If eviscp is nil, then we pretty print x as given.  Otherwise, x
has been eviscerated and we give special importance to the *evisceration-mark*.
NOTE WELL: This function does not eviscerate -- it assumes the evisceration has
been done if needed.</p>"
  (b* (((printconfig config) config)
       (col
        ;; ACL2's pretty-printer requires that col < config.hard-right-margin.
        ;; If this isn't satisfied, it just causes a hard error.  To avoid this
        ;; hard error, I'll just say if we're currently past the right-margin,
        ;; we'll print a newline.
        (if (>= col (the unsigned-byte config.hard-right-margin))
            0
          col))
       (inst (ppr1 x 0 (- config.hard-right-margin col) config eviscp)))
    (print-instruction inst col config eviscp acc)))

(define pretty
  :parents (pretty-printing)
  :short "Pretty-print any ACL2 object into a string."
  ((x "The ACL2 object to pretty-print.")
   &key
   ((config printconfig-p "Optional pretty-printer configuration options.")  '*default-printconfig*)
   ((col    natp          "Optional starting column number.")                '0)
   ((eviscp booleanp      "Optional flag for use with eviscerated objects.") 'nil))
  :returns (pretty-x stringp :rule-classes :type-prescription)
  :long "<p>This is our simplest @(see pretty-printing) function.</p>

<h3>Examples:</h3>

@({
    ACL2 !>(str::pretty '(1 2 3))
    \"(1 2 3)\"

    ACL2 !>(str::pretty (make-list 30 :initial-element 'str::hello))
    \"(STR::HELLO STR::HELLO STR::HELLO
                 STR::HELLO STR::HELLO STR::HELLO
                 STR::HELLO STR::HELLO STR::HELLO
                 STR::HELLO STR::HELLO STR::HELLO
                 STR::HELLO STR::HELLO STR::HELLO
                 STR::HELLO STR::HELLO STR::HELLO
                 STR::HELLO STR::HELLO STR::HELLO
                 STR::HELLO STR::HELLO STR::HELLO
                 STR::HELLO STR::HELLO STR::HELLO
                 STR::HELLO STR::HELLO STR::HELLO)\"

    ACL2 !>(str::pretty (make-list 30 :initial-element 'str::hello)
                        :config (make-printconfig
                                  :home-package (pkg-witness \"STR\")
                                  :print-lowercase t))
    \"(hello hello hello hello hello hello
            hello hello hello hello hello hello
            hello hello hello hello hello hello
            hello hello hello hello hello hello
            hello hello hello hello hello hello)\"
})"

  (str::rchars-to-string (ppr x col config eviscp nil)))

(define revappend-pretty
  :parents (pretty-printing)
  :short "Pretty-print any ACL2 object, in reverse order, onto a reverse-order
character list."
  ((x   "The ACL2 object to pretty-print.")
   (acc "The reverse-order character list to print to.")
   &key
   ((config printconfig-p "Optional pretty-printer configuration options.")  '*default-printconfig*)
   ((col    natp          "Optional starting column number.")                '0)
   ((eviscp booleanp      "Optional flag for use with eviscerated objects.") 'nil))
  :returns (new-acc character-listp :hyp (character-listp acc))
  :long "<p>This is very similar to @(see pretty), except that it can be used
to extend existing character lists.  See for instance the discussion in @(see
revappend-chars).</p>"
  (ppr x col config eviscp acc))


(define pretty-list
  :parents (pretty-printing)
  :short "Pretty-print a list of ACL2 objects, creating a list of strings."
  ((x "The ACL2 objects to pretty-print.")
   &key
   ((config printconfig-p "Optional pretty-printer configuration options.")  '*default-printconfig*)
   ((col    natp          "Optional starting column number.")                '0)
   ((eviscp booleanp      "Optional flag for use with eviscerated objects.") 'nil))
  :returns (pretty-x string-listp)
  (if (atom x)
      nil
    (cons (pretty      (car x) :config config :col col :eviscp eviscp)
          (pretty-list (cdr x) :config config :col col :eviscp eviscp))))


; ----------------------------------------------------------------------------
;
;                              Evisceration
;
; ----------------------------------------------------------------------------

(local (xdoc::set-default-parents eviscerate))

(fty::defprod eviscconfig
  :tag :eviscconfig
  :layout :fulltree
  :short "Controls how to eviscerate a term&mdash;our alternative to ACL2's
          @(see acl2::evisc-tuple)s."
  ((print-level  acl2::maybe-natp :rule-classes :type-prescription
                 "Similar to the Common Lisp @('*print-level*').  If set, this
                  limits how deeply to descend into subterms before we
                  eviscerate them.")
   (print-length acl2::maybe-natp :rule-classes :type-prescription
                 "Similar to the Common lisp @('*print-length*').  If set, this
                  limits how many elements of a list to print (at any level).")
   (replacement-alist t
                      "Ordinary (non-fast) alist.  Binds subterms either to
                       strings (which are interpreted as the eviscerated
                       replacement text for the subterms) or else to
                       replacement terms (which are not to be recursively
                       eviscerated).")
   (hiding-cars  t
                 "Should be a fast alist.  Binds symbols to T.  Any subterm
                  whose @('car') is bound in @('hiding-cars') will be
                  eviscerated with @('<hidden>').")))

; Macros instead of constants to avoid special lookups

(defmacro evisceration-hash-mark ()
  ''(:evisceration-mark . "#"))

(defmacro list-of-evisceration-ellipsis-mark ()
  ;; We do the (list ...) ahead of time
  ''((:evisceration-mark . "...")))

(defmacro anti-evisceration-mark ()
  ''(:evisceration-mark . ":EVISCERATION-MARK"))

(defmacro evisceration-hiding-mark ()
  ''(:evisceration-mark . "<hidden>"))

(local (assert-event (equal acl2::*evisceration-hash-mark* (evisceration-hash-mark))))
(local (assert-event (equal (list acl2::*evisceration-ellipsis-mark*) (list-of-evisceration-ellipsis-mark))))
(local (assert-event (equal acl2::*anti-evisceration-mark* (anti-evisceration-mark))))
(local (assert-event (equal acl2::*evisceration-hiding-mark* (evisceration-hiding-mark))))


(defines eviscerate1
  :short "Main function for eviscerating a term."
  :long "<p>These are adapted from ACL2's functions of the same names,
basically by consolidating the arguments into an eviscconfig and removing
support for iprinting.</p>"

  (define eviscerate1 ((x "The object to eviscerate.")
                       (v natp "Depth we are currently at.")
                       (config eviscconfig-p))
    :measure (acl2::two-nats-measure (acl2-count x) 1)
    (b* (((eviscconfig config))
         ;; Subtle.  We use hons-assoc-equal instead of hons-get because it
         ;; means we do not have to hons X.
         (temp (hons-assoc-equal x config.replacement-alist))
         ((when (cdr temp))
          (cond ((stringp (cdr temp))
                 (cons :evisceration-mark (cdr temp)))
                (t (cdr temp))))
         ((when (atom x))
          (cond ((eq x :evisceration-mark) (anti-evisceration-mark))
                (t x)))
         ((when (and config.print-level
                     (>= (lnfix v) config.print-level)))
          (evisceration-hash-mark))
         ((when (and (consp config.hiding-cars)
                     (hons-get (car x) config.hiding-cars)))
          (evisceration-hiding-mark)))
      ;; Note that this recurs on all of X, which is why we're not consing
      ;; the car onto something.
      (eviscerate1-lst x (+ 1 (lnfix v)) 0 config)))

  (define eviscerate1-lst ((x "List of objects to eviscerate, including its car.")
                           (v   natp "Depth we are currently at.")
                           (n   natp "Length we are currently at.")
                           (config eviscconfig-p))
    :measure (acl2::two-nats-measure (acl2-count x) 0)
    (b* (((eviscconfig config))
         ;; Subtle.  We use hons-assoc-equal instead of hons-get because it
         ;; means we do not have to hons X.
         (temp (hons-assoc-equal x config.replacement-alist))
         ((when (cdr temp))
          (cond ((stringp (cdr temp))
                 (cons :evisceration-mark (cdr temp)))
                (t (cdr temp))))
         ((when (atom x))
          (cond ((eq x :evisceration-mark) (anti-evisceration-mark))
                (t x)))
         ((when (and config.print-length
                     (>= (lnfix n) config.print-length)))
          (list-of-evisceration-ellipsis-mark)))
      (cons (eviscerate1 (car x) v config)
            (eviscerate1-lst (cdr x) v (+ 1 (lnfix n)) config)))))

(defines eviscerate1p
  :short "Helper function for avoiding consing when evisceration will not
          change a term."

  (define eviscerate1p ((x "Term to perhaps eviscerate.")
                        (config eviscconfig-p))
    :returns (needs-to-be-eviscerated-p)
    :measure (acl2::two-nats-measure (acl2-count x) 1)
    (b* (((eviscconfig config))
         (temp (hons-assoc-equal x config.replacement-alist))
         ((when (cdr temp))
          t)
         ((when (atom x))
          (eq x :evisceration-mark))
         ((when (and (consp config.hiding-cars)
                     (hons-get (car x) config.hiding-cars)))
          t))
      (eviscerate1p-lst x config)))

  (define eviscerate1p-lst ((x "List to perhaps eviscerate.")
                            (config eviscconfig-p))
    :measure (acl2::two-nats-measure (acl2-count x) 0)
    (b* (((eviscconfig config))
         (temp (hons-assoc-equal x config.replacement-alist))
         ((when (cdr temp))
          t)
         ((when (atom x))
          (eq x :evisceration-mark)))
      (or (eviscerate1p (car x) config)
          (eviscerate1p-lst (cdr x) config)))))

(define eviscerate ((x "The term to eviscerate")
                    (config eviscconfig-p))
  :parents (pretty-printing)
  :short "Elide portions of a term, for use with @(see str::pretty)."
  :returns (eviscerated-x "A new version of @('x'), perhaps with some subterms
                           replaced.")
  (b* (((eviscconfig config))
       ((when (or config.print-level
                  config.print-length
                  (eviscerate1p x config)))
        (eviscerate1 x 0 config)))
    x)

  :long #{"""<p>Sometimes terms are too big to practically print.  Much like
ACL2's built-in pretty-printer, our @(see pretty-printing) functions have
special support for printing ``eviscerated'' terms where, e.g., some particular
subterms are elided in certain ways.</p>

<p>The pretty-printer itself does not do any elision.  Instead, @('eviscerate')
is a separate function that can be used, ahead of time, to elide certain
sub-terms.  Typically the result of @('eviscerate') is then given to, e.g.,
@(see str::pretty), along with a special @(':eviscp') flag) to indicate that
elisions have been made.</p>

<p>ACL2 has its own, built-in evisceration functions that support fancy
features such as @(see acl2::iprinting).  However, much like ACL2's pretty printer
itself, these functions are in program mode and take @(see state), which is
sometimes inconvenient.  So, here, we (re)implement a simple evisceration
function that provides fewer features but avoids state.</p>

<p>Our function is very much styled after ACL2's and should be familiar if you
know about ACL2's @(see evisc-tuple)s, except that instead of evisc-tuples we
use @(see eviscconfig) structures.</p>

<h3>Examples</h3>

<p>Suppose we want to pretty-print the following constant:</p>

@({
    ACL2 !> (defconst *demo* '(foo (bar aaa bbb ccc (baz 1 2 3))
                                   1 2 3 4 5 6
                                   (baz 3 2 1)))
})

<p>To print without evisceration we can just use @(see str::pretty)
directly (with its default @(see printconfig):</p>

@({
    ACL2 !> (str::pretty *demo*)
    "(FOO (BAR AAA BBB CCC (BAZ 1 2 3))
         1 2 3 4 5 6 (BAZ 3 2 1))"
})

<p>To print with evisceration, we (1) eviscerate the term and then (2) tell
@(see str::pretty) to print it with evisceration enabled.  For example:</p>

@({
    ACL2 !> (let* ((econfig (str::make-eviscconfig
                             :print-level 100
                             :print-length 2)))
              (str::pretty (str::eviscerate *demo* econfig)
                           :eviscp t))
    "(FOO (BAR AAA ...) ...)"
})

<p>Above the use of @('print-length') truncates the printing after two items in
each list.  Extending the print-length lets us see more of the term:</p>

@({
    ACL2 !> (let* ((econfig (str::make-eviscconfig
                             :print-level 100
                             :print-length 4)))
              (str::pretty (str::eviscerate *demo* econfig)
                           :eviscp t))
    "(FOO (BAR AAA BBB CCC ...) 1 2 ...)"
})

<p>There are also other options for hiding all subterms with a certain car, and
for making particular replacements of particular subterms; see @(see eviscconfig)
for details.</p>

"""})
