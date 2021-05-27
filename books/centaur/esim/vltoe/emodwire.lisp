; ESIM Symbolic Hardware Simulator
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
(include-book "centaur/vl2014/util/defs" :dir :system)
(include-book "centaur/fty/deftypes" :dir :system)
(local (include-book "std/testing/assert-bang" :dir :system))
(local (include-book "centaur/vl2014/util/arithmetic" :dir :system))
(local (include-book "centaur/vl2014/util/position" :dir :system))
(local (include-book "std/basic/intern-in-package-of-symbol" :dir :system))

(defxdoc exploding-vectors
  :parents (e-conversion)
  :short "How we convert Verilog wires (which might be vectors) into E
wires (which are just bits)."

  :long "<p>A significant difference between E and Verilog is that there are no
vectors in E.  Whereas our Verilog module might have a vector like @('wire
[7:0] w'), our E module will instead have eight individual wires, whose names
are @('ACL2::|w[7]|') through @('ACL2::|w[0]|').</p>

<p>There is a fair bit of code geared towards making this bit-level conversion
safe and efficient.  As a quick summary:</p>

<ul>

<li>We represent each of these \"exploded\" wires like @('ACL2::|w[0]|') as an
@(see vl-emodwire-p).  This representation includes an encoding scheme that
usually produces readable names and avoids name clashes, even when escaped
identifiers are used.</li>

<li>The E wires for all of a module's net and register declarations can be
bundled into a @(see vl-wirealist-p).  A wire alist is generally constructed
with @(see vl-module-wirealist), which provides certain uniqueness
guarantees.</li>

<li>Certain \"simple\" expressions (similar to <see topic='@(url
expr-slicing)'>sliceable</see> expressions) can be converted into wires using
@(see vl-msb-expr-bitlist), which does lots of sanity checking to ensure that
the sizes and bounds of the expressions are correct and that only defined wires
are being used.</li>

</ul>

<p>BOZO much of this code predates the exprsesion slicing code.  We may wish to
eventually redo significant portions of the wirealist stuff to instead be based
on the expression-slicing code.</p>")

(local (defthm equal-of-string-and-nil-string
         (implies (force (stringp str))
                  (equal (equal str "NIL")
                         (equal (explode str)
                                '(#\N #\I #\L))))
         :hints(("Goal"
                 :in-theory (disable str::equal-of-explodes)
                 :use ((:instance str::equal-of-explodes
                                  (acl2::x str)
                                  (acl2::y "NIL")))))))

#!ACL2
(local (defthm intern-in-package-of-symbol-not-nil
         (implies (and (force (stringp str))
                       (force (not (equal str "NIL"))))
                  (intern-in-package-of-symbol str 'acl2::rewrite))
         :hints(("Goal"
                 :in-theory (disable equal-of-intern-in-package-of-symbols)
                 :use ((:instance equal-of-intern-in-package-of-symbols
                                  (a "NIL")
                                  (b str)
                                  (in-pkg 'acl2::rewrite)))))))

(local (defthm member-of-make-character-list
         (implies (and (characterp a)
                       (member-equal a chars))
                  (member-equal a (make-character-list chars)))
         :hints(("Goal" :in-theory (enable make-character-list)))))

(local (defthm implode-is-not-nil-bracket-char
         (implies (member #\[ chars)
                  (not (equal (implode chars) "NIL")))
         :hints(("Goal"
                 :in-theory (disable member-of-make-character-list)
                 :use ((:instance member-of-make-character-list
                                  (a #\[)
                                  (chars chars)))))))


(local
 (defsection no-specials-in-natstr

   (local (defthm c0
            (and (not (equal (str::digit-to-char x) #\!))
                 (not (equal (str::digit-to-char x) #\.))
                 (not (equal (str::digit-to-char x) #\/)))
            :hints(("Goal" :in-theory (enable digit-to-char)))))

   (local (defthm c1
            (and (not (member-equal #\! (str::basic-natchars x)))
                 (not (member-equal #\. (str::basic-natchars x)))
                 (not (member-equal #\/ (str::basic-natchars x))))
            :hints(("Goal" :in-theory (enable str::basic-natchars)))))

   (local (defthm c2
            (and (not (member-equal #\! (str::natchars x)))
                 (not (member-equal #\. (str::natchars x)))
                 (not (member-equal #\/ (str::natchars x))))
            :hints(("Goal" :in-theory (enable str::natchars)))))

   (defthm no-specials-in-natstr
     (and (not (member-equal #\! (explode (natstr x))))
          (not (member-equal #\. (explode (natstr x))))
          (not (member-equal #\/ (explode (natstr x)))))
     :hints(("Goal" :in-theory (enable natstr))))))


(local (defthm dec-digit-char-listp-encoding-help
         (implies (str::dec-digit-char-listp x)
                  (and (not (member-equal #\] x))
                       (not (member-equal #\[ x))
                       (not (member-equal #\{ x))))
         :hints(("Goal" :in-theory (enable str::dec-digit-char-listp)))))



(defsection emodwire-encoding
  :parents (exploding-vectors)
  :short "A simple encoding scheme to basenames that are free of certain
special characters."

  :long "<p>Usually Verilog wire names do not have special characters in them,
but with escaped identifiers it is possible to have names that include
brackets, dots, etc.</p>

<p>These special characters could pose certain problems.  The most obvious is
in a module such as this:</p>

@({
  wire [7:0] w ;
  wire \w[3] ;
})

<p>Here, the E wires corresponding to @('w') would be @('ACL2::|w[7]|') on down
to @('ACL2::|w[0]|').  But if we naively translate @('\w[3] ') into
@('ACL2::|w[3]|') then there could be a name clash.</p>

<p>To avoid this kind of problem, we use a simple encoding scheme that ensures
there are no brackets in the basename of a @(see vl-emodwire-p).  We originally
used the following, trivial encoding scheme:</p>

<ul>
<li>@('[ ---> {1')</li>
<li>@('] ---> {2')</li>
<li>@('{ ---> {3')</li>
</ul>

<p>But later we decided to slightly extend this scheme, to ensure that the
special characters @('.'), @('!'), and @('/') also do not occur.  Why?  We
think having @('.') in a name could be confusing to some tools since it is used
as a hierarchical identifier in Verilog.  Meanwhile, @('!') is used as a
hierarchical identifier in E (e.g., see @('mod-state')).  And we have
occasionally seen other Verilog tools that use @('/') as a hierarchical
separator.</p>

<p>To ensure these characters also do not occur, we extend our encoding scheme
in a simple way:</p>

<ul>
<li>@('. ---> {4')</li>
<li>@('! ---> {5')</li>
<li>@('/ ---> {6')</li>
</ul>

<p>This encoding is done automatically by the @(see vl-emodwire) constructor
and the appropriate decoding is done by the @(see vl-emodwire->basename)
accessor.  Usually no encoding is necessary, so these functions are optimized
for the case that there are no bracket or { characters.</p>

<p>Note that we actually implement the encoding and decoding functions in
raw-lisp for better performance.</p>"

  (defund vl-emodwire-encode-chars (x)
    ;; Slow. We don't expect this to ever really be called in practice.
    (declare (xargs :guard (character-listp x)))
    (if (atom x)
        nil
      (let ((rest (vl-emodwire-encode-chars (cdr x))))
        (case (car x)
          (#\[ (list* #\{ #\1 rest))
          (#\] (list* #\{ #\2 rest))
          (#\{ (list* #\{ #\3 rest))
          (#\. (list* #\{ #\4 rest))
          (#\! (list* #\{ #\5 rest))
          (#\/ (list* #\{ #\6 rest))
          (otherwise
           (cons (car x) rest))))))

  (local (in-theory (enable vl-emodwire-encode-chars)))

  (defthm character-listp-of-vl-emodwire-encode-chars
    (implies (force (character-listp x))
             (character-listp (vl-emodwire-encode-chars x))))

  (defthm no-special-chars-in-vl-emodwire-encode-chars
    (and (not (member-equal #\[ (vl-emodwire-encode-chars x)))
         (not (member-equal #\] (vl-emodwire-encode-chars x)))
         (not (member-equal #\. (vl-emodwire-encode-chars x)))
         (not (member-equal #\! (vl-emodwire-encode-chars x)))
         (not (member-equal #\/ (vl-emodwire-encode-chars x)))))

  (defthm vl-emodwire-encode-chars-identity
    (implies (and (not (member-equal #\[ x))
                  (not (member-equal #\] x))
                  (not (member-equal #\{ x))
                  (not (member-equal #\. x))
                  (not (member-equal #\! x))
                  (not (member-equal #\/ x)))
             (equal (vl-emodwire-encode-chars x)
                    (list-fix x))))


  (defund vl-emodwire-encoding-valid-p (x)
    ;; Slow. We don't expect this to ever really be called in practice.
    (declare (xargs :guard (character-listp x)))
    (cond ((atom x)
           t)
          ((eql (car x) #\{)
           (and (consp (cdr x))
                (or (eql (cadr x) #\1)
                    (eql (cadr x) #\2)
                    (eql (cadr x) #\3)
                    (eql (cadr x) #\4)
                    (eql (cadr x) #\5)
                    (eql (cadr x) #\6))
                (vl-emodwire-encoding-valid-p (cddr x))))
          (t
           (vl-emodwire-encoding-valid-p (cdr x)))))

  (local (in-theory (enable vl-emodwire-encoding-valid-p)))

  (defthm vl-emodwire-encoding-valid-p-of-vl-emodwire-encode-chars
    (vl-emodwire-encoding-valid-p (vl-emodwire-encode-chars x)))

  (defthm vl-emodwire-encoding-valid-p-typical
    (implies (not (member-equal #\{ x))
             (vl-emodwire-encoding-valid-p x)))

  (defthm vl-emodwire-encoding-valid-p-of-append
    (implies (and (force (vl-emodwire-encoding-valid-p x))
                  (force (vl-emodwire-encoding-valid-p y)))
             (vl-emodwire-encoding-valid-p (append x y))))




  (defund vl-emodwire-decode-chars (x)
    ;; Slow. We don't expect this to ever really be called in practice.
    (declare (xargs :guard (character-listp x)))
    (cond ((atom x)
           nil)
          ((and (eql (car x) #\{)
                (consp (cdr x)))
           (let ((rest (vl-emodwire-decode-chars (cddr x))))
             (case (cadr x)
               (#\1 (cons #\[ rest))
               (#\2 (cons #\] rest))
               (#\3 (cons #\{ rest))
               (#\4 (cons #\. rest))
               (#\5 (cons #\! rest))
               (otherwise (cons #\/ rest)))))
          (t
           (cons (car x) (vl-emodwire-decode-chars (cdr x))))))

  (local (in-theory (enable vl-emodwire-decode-chars)))

  (defthm vl-emodwire-decode-chars-under-iff
    (iff (vl-emodwire-decode-chars x)
         (consp x)))

  (defthm character-listp-of-vl-emodwire-decode-chars
    (implies (force (character-listp x))
             (character-listp (vl-emodwire-decode-chars x))))

  (defthm vl-emodwire-decode-chars-of-vl-emodwire-encode-chars
    (implies (force (character-listp x))
             (equal (vl-emodwire-decode-chars (vl-emodwire-encode-chars x))
                    (list-fix x))))

  (defthm vl-emodwire-decode-chars-identity
    (implies (case-split (not (member-equal #\{ x)))
             (equal (vl-emodwire-decode-chars x)
                    (list-fix x))))


  (defsection equal-of-vl-emodwire-decode-chars

    (local (defun my-induct (x y)
             (if (and (atom x)
                      (atom y))
                 t
               (if (or (atom x)
                       (atom y))
                   nil
                 (if (eql (car x) #\{)
                     (if (eql (car y) #\{)
                         (my-induct (cddr x) (cddr y))
                       nil)
                   (my-induct (cdr x) (cdr y)))))))

    ;; All this junk is just to make the proof fast.

    (local (defthm c0
             (implies (vl-emodwire-encoding-valid-p x)
                      (vl-emodwire-encoding-valid-p (cdr x)))))

    (local (defthm c1
             (implies (and (EQUAL (LIST-FIX (cdr X)) (LIST-FIX (cdr Y)))
                           (consp x)
                           (consp y))
                      (equal (EQUAL (LIST-FIX X) (LIST-FIX Y))
                             (equal (car x) (car y))))))

    (local (defthm c2
             (implies (not (equal (LIST-FIX (cdr X)) (LIST-FIX (cdr Y))))
                      (not (equal (LIST-FIX X) (LIST-FIX Y))))))

    (local (defthm c3
             (implies (not (member-equal a x))
                      (equal (equal (first x) a)
                             (and (atom x)
                                  (not a))))))

    (local (defthm c4
             (implies (and (not (equal (car x) (car y)))
                           (or (consp x)
                               (consp y)))
                      (not (equal (list-fix x) (list-fix y))))))

    (local (defthm c5
             (implies (atom x)
                      (equal (list-fix x) nil))))

    (local (defthm c6
             (implies (atom x)
                      (equal (vl-emodwire-decode-chars x)
                             nil))))

    (defthm equal-of-vl-emodwire-decode-chars
      (implies (and (vl-emodwire-encoding-valid-p x)
                    (vl-emodwire-encoding-valid-p y)
                    (not (member-equal #\[ x))
                    (not (member-equal #\] x))
                    (not (member-equal #\. x))
                    (not (member-equal #\! x))
                    (not (member-equal #\/ x))
                    (not (member-equal #\[ y))
                    (not (member-equal #\] y))
                    (not (member-equal #\. y))
                    (not (member-equal #\! y))
                    (not (member-equal #\/ y)))
               (equal (equal (vl-emodwire-decode-chars x)
                             (vl-emodwire-decode-chars y))
                      (equal (list-fix x)
                             (list-fix y))))
      :hints(("Goal"
              :induct (my-induct x y)
              :do-not '(generalize fertilize eliminate-destructors)
              :in-theory (disable vl-emodwire-decode-chars
                                  vl-emodwire-encoding-valid-p
                                  vl-emodwire-decode-chars-identity
                                  ACL2::TRUE-LISTP-MEMBER-EQUAL
                                  ACL2::LIST-FIX-WHEN-TRUE-LISTP
                                  double-containment
                                  MEMBER-EQUAL-WHEN-MEMBER-EQUAL-OF-CDR-UNDER-IFF
                                  acl2::MEMBER-EQUAL-WHEN-ALL-EQUALP
                                  acl2::subsetp-trans
                                  acl2::subsetp-trans2

                                  )
              :expand ((vl-emodwire-decode-chars x)
                       (vl-emodwire-decode-chars y)
                       (vl-emodwire-encoding-valid-p x)
                       (vl-emodwire-encoding-valid-p y))))))

  (defund vl-emodwire-encode-aux (x)
    ;; Slow. We don't expect this to ever really be called in practice.  We keep
    ;; this in a separate function to minimize expansion from inlining the main
    ;; function.
    (declare (type string x))
    (b* ((chars   (explode x))
         (encoded (vl-emodwire-encode-chars chars)))
      (implode encoded)))

  (defund vl-emodwire-decode-aux (x)
    ;; Slow. We don't expect this to ever really be called in practice.  We keep
    ;; this in a separate function to minimize expansion from inlining the main
    ;; function.
    (declare (type string x))
    (b* ((chars   (explode x))
         (decoded (vl-emodwire-decode-chars chars)))
      (implode decoded)))

  (local (in-theory (enable vl-emodwire-encode-aux
                            vl-emodwire-decode-aux)))

  ;; We seem to be able to do a lot better in raw lisp.  It seems worth the
  ;; effort to optimize these under the hood, since we may need to generate
  ;; millions of emodwires.
  ;;
  ;; Encoding with no inlining:
  ;;   ACL2 version: 7.60 seconds   (no inlining)
  ;;   Raw version:  0.68 seconds   (no inlining)
  ;;
  ;; Decoding with no inlining:
  ;;   ACL2 version: 1.27 seconds   (no inlining)
  ;;   Raw version:  0.39 seconds   (no inlining)

  #||
  (time$
   (loop for i from 1 to 10000000 do
         (vl2014::vl-emodwire-encode "looksLikeAVerilogWire")))

  (time$
   (loop for i from 1 to 10000000 do
         (vl2014::vl-emodwire-decode "looksLikeAVerilogWire")))
  ||#


  (defund vl-emodwire-encode (x)
    (declare (type string x))
    (mbe :logic (vl-emodwire-encode-aux x)
         :exec (if (or (position #\[ (the string x))
                       (position #\] (the string x))
                       (position #\{ (the string x))
                       (position #\. (the string x))
                       (position #\! (the string x))
                       (position #\/ (the string x)))
                   (vl-emodwire-encode-aux x)
                 x)))

  (defund vl-emodwire-decode (x)
    (declare (type string x))
    (mbe :logic (vl-emodwire-decode-aux x)
         :exec (if (position #\{ x)
                   (vl-emodwire-decode-aux x)
                 x)))

  (defttag vl-optimize)
  (progn!
   (set-raw-mode t)

   (declaim (inline vl-emodwire-encode))
   (declaim (inline vl-emodwire-decode))

   (defun vl-emodwire-encode (x)
     (declare (type string x))
     (let ((xl (length (the simple-string x))))
       (loop for i fixnum from 0 below xl do
             (let ((c (schar x i)))
               (case c
                 ((#\[ #\] #\{ #\. #\! #\/)
                  (return-from vl-emodwire-encode
                    (vl2014::vl-emodwire-encode-aux x)))
                 (otherwise
                  nil))))
       x))

   (defun vl-emodwire-decode (x)
     (declare (type string x))
     (let ((xl (length (the simple-string x))))
       (loop for i fixnum from 0 below xl do
             (let ((c (schar x i)))
               (when (eql c #\{)
                 (return-from vl-emodwire-decode
                   (vl2014::vl-emodwire-decode-aux x)))))
       x)))

  (defttag nil))





(defsection vl-emodwire-encode-chars-nil

  ;; N: if there are no special chars, then NIL is the only string whose encoding
  ;; is "NIL"

  (local (defthmd n0
           (implies (and (not (member-equal #\[ x))
                         (not (member-equal #\] x))
                         (not (member-equal #\{ x))
                         (not (member-equal #\. x))
                         (not (member-equal #\! x))
                         (not (member-equal #\/ x)))
                    (equal (vl-emodwire-encode-chars x)
                           (list-fix x)))))

  (local (defthm n1
           (implies (and (not (member-equal #\[ x))
                         (not (member-equal #\] x))
                         (not (member-equal #\{ x))
                         (not (member-equal #\. x))
                         (not (member-equal #\! x))
                         (not (member-equal #\/ x))
                         (character-listp x))
                    (equal (equal (vl-emodwire-encode-chars x) '(#\N #\I #\L))
                           (equal x '(#\N #\I #\L))))))

  ;; M: if there are special chars, then it doesn't get encoded as NIL because
  ;; its encoding has a { character in it.

  (local (defthmd m0
           (implies (or (member-equal #\[ x)
                        (member-equal #\] x)
                        (member-equal #\{ x)
                        (member-equal #\. x)
                        (member-equal #\! x)
                        (member-equal #\/ x))
                    (member #\{ (vl-emodwire-encode-chars x)))
           :hints(("Goal" :in-theory (enable vl-emodwire-encode-chars)))))

  (local (defthmd m1
           (implies (member #\{ x)
                    (not (equal x '(#\N #\I #\L))))))

  (local (defthm m2
           (implies (or (member-equal #\[ x)
                        (member-equal #\] x)
                        (member-equal #\{ x)
                        (member-equal #\. x)
                        (member-equal #\! x)
                        (member-equal #\/ x))
                    (not (equal (vl-emodwire-encode-chars x) '(#\N #\I #\L))))
           :hints(("Goal"
                   :use ((:instance m0)
                         (:instance m1 (x (vl-emodwire-encode-chars x))))))))

  (defthm vl-emodwire-encode-chars-nil
    (implies (character-listp x)
             (equal (equal (vl-emodwire-encode-chars x) '(#\N #\I #\L))
                    (equal x '(#\N #\I #\L))))
    :hints(("Goal"
            :use ((:instance n1)
                  (:instance m2))))))


(defsection vl-emodwire-encode-nil

  (local (defthm l0
           (implies (force (stringp str))
                    (equal (equal str "NIL")
                           (equal (explode str)
                                  '(#\N #\I #\L))))
           :hints(("Goal"
                   :in-theory (disable str::equal-of-explodes)
                   :use ((:instance str::equal-of-explodes
                                    (acl2::x str)
                                    (acl2::y "NIL")))))))

  (defthm vl-emodwire-encode-nil
    (implies (stringp x)
             (equal (equal (vl-emodwire-encode x) "NIL")
                    (equal x "NIL")))
    :hints(("Goal"
            :in-theory (enable vl-emodwire-encode
                               vl-emodwire-encode-aux))))

  (defthm vl-emodwire-encode-nil-alt
    (implies (stringp x)
             (equal (equal (explode (vl-emodwire-encode x)) '(#\N #\I #\L))
                    (equal x "NIL")))
    :hints(("Goal"
            :in-theory (enable vl-emodwire-encode
                               vl-emodwire-encode-aux)))))



(defsection vl-emodwire-p
  :parents (exploding-vectors)
  :short "@(call vl-emodwire-p) recognizes symbols that VL generates as wire
names for E modules."

  :long "<p>E uses a permissive pattern system that allows almost any atom to
be used as a wire name.  But when VL is used to translate Verilog modules, we
always produce wire names that are symbols, whose names are either <b>simple
names</b> like @('\"reset\"') or <b>indexed names</b> like
@('\"opcode[3]\"').</p>

<p>We always generate wire names in the @('ACL2') package.  This is due to
historic convention, but also is a good idea for efficiency: we can control the
size of the ACL2 package at the time we build ACL2, but we have no
method (well, ttags I suppose) to construct a new package with a larger size.
See the efficiency considerations in @(see vl-wirealist-p) for more
details.</p>"

  (definline vl-emodwire-scan (name)
    "We optimize this under the hood to make vl-emodwire-p faster.  This
     logical definition never gets executed."
    (declare (type string name))
    (b* ((open    (position #\[ name))
         (close   (position #\] name))
         (escape  (if (position #\{ name) t nil))
         (illegal (if (or (position #\. name)
                          (position #\! name)
                          (position #\/ name))
                      t
                    nil)))
      (mv open close escape illegal)))

  (defttag vl-optimize)
  (progn!
   (set-raw-mode t)

   (defun vl-emodwire-scan$inline (name)
     (declare (type string name))
     (let ((open    nil)
           (close   nil)
           (escape  nil)
           (illegal nil)
           (len     (length (the simple-string name))))
       (loop for i fixnum from 0 below len do
             (let ((c (schar name i)))
               (case c
                 (#\[ (unless open (setq open i)))
                 (#\] (unless close (setq close i)))
                 ((#\. #\! #\/) (setq illegal t))
                 (#\{ (setq escape t))
                 (otherwise nil))))
       (mv open close escape illegal))))



  ;; Without scan optimization: 15.8 seconds, 480 MB allocated
  ;; With scan optimization: 8.65 seconds, 480 MB allocated

  #||
  (time (loop for i fixnum from 1 to 10000000 do
  (vl2014::vl-emodwire-p 'acl2::|LooksLikeAVerilogWire[3]|)))
  ||#


; We could do even better:
;
; I think the MBE optimization in vl-emodwire-get-index here is legitimate, but
; proving it is hard.  Using skip-proofs to get it admitted, the loop goes down
; to 6.81 seconds and we get rid of all the allocation.  So this could be a
; very nice optimization, if only we could get the proof completed.

  (definline vl-emodwire-get-index (name open close)
    (declare (xargs :guard (and (stringp name)
                                (natp open)
                                (natp close)
                                (< open close)
                                (= close (- (length name) 1)))))
    ;; (mbe :logic
    (b* ((index-str (subseq name (+ open 1) close))
         ((mv index-val len)
          (str::parse-nat-from-string index-str 0 0 0 (length index-str)))
         (ok1 (= len (length index-str)))
         (ok2 (equal index-str (natstr index-val))))
      (mv (and ok1 ok2) index-val))
    ;; :exec
    ;;(b* ((start (+ open 1))
    ;;     ((mv index-val len)
    ;;      (str::parse-nat-from-string name 0 0 start (length name)))
    ;;     (ok1 (= len (- close start)))
    ;;     (ok2 (or (not (eql (char name start) #\0))
    ;;              (= len 1))))
    ;;  (mv (and ok1 ok2) index-val)))
    )

; Here is a fledgling effort toward verifying the guards.  Lemmas C3 and C4
; show that INDEX-VAL and LEN are correct in the :exec definition.  But doing
; the proofs for ok1 and ok2 seemed too hard, and I didn't want to spend the
; necessary time.

; If you ever get this working, probably optimize vl-emodwire->index to take
; advantage of it.

  ;; (defthm c0
  ;;   (equal (cdr (nthcdr n x))
  ;;          (nthcdr (+ 1 (nfix n)) x)))

  ;; (in-theory (disable nthcdr-of-increment))

  ;; (defthm str::take-leading-dec-digit-chars-of-replicate
  ;;   (equal (str::take-leading-dec-digit-chars (replicate n char))
  ;;          (if (str::digitp char)
  ;;              (replicate n char)
  ;;            nil))
  ;;   :hints(("Goal" :in-theory (enable str::take-leading-dec-digit-chars
  ;;                                     replicate))))


  ;; (defthm c1
  ;;   (implies (not (str::digitp (nth n x)))
  ;;            (equal (str::take-leading-dec-digit-chars (take n x))
  ;;                   (str::take-leading-dec-digit-chars x)))
  ;;   :hints(("Goal" :in-theory (enable str::take-leading-dec-digit-chars
  ;;                                     nth))))

  ;; (defthm c2
  ;;   (IMPLIES
  ;;    (AND (NATP OPEN)
  ;;         (< OPEN (+ -1 (LEN X)))
  ;;         (NOT (STR::DIGITP (NTH (+ -1 (LEN X)) X)))
  ;;         (<= 2 (+ (- OPEN) (LEN X))))
  ;;    (EQUAL
  ;;     (STR::DIGIT-LIST-VALUE
  ;;      (STR::TAKE-LEADING-DEC-DIGIT-CHARS (TAKE (+ -2 (- OPEN) (LEN X))
  ;;                                               (NTHCDR (+ 1 OPEN) X))))
  ;;     (STR::DIGIT-LIST-VALUE
  ;;      (STR::TAKE-LEADING-DEC-DIGIT-CHARS (NTHCDR (+ 1 OPEN) X))))))

  ;; (defthm c3
  ;;   (implies (and (stringp name)
  ;;                 (natp open)
  ;;                 (natp close)
  ;;                 (< open close)
  ;;                 (= close (- (length name) 1))
  ;;                 (not (str::digitp (char name close))))
  ;;            (equal
  ;;             (let ((index-str (subseq name (+ open 1) close)))
  ;;               (mv-nth 0 (str::parse-nat-from-string index-str 0 0 0 (length index-str))))
  ;;             (let ((start (+ open 1)))
  ;;               (mv-nth 0 (str::parse-nat-from-string name 0 0 start (length name))))))
  ;;   :hints(("Goal" :in-theory (enable subseq
  ;;                                     subseq-list))))

  ;; (defthm c4
  ;;   (implies (and (stringp name)
  ;;                 (natp open)
  ;;                 (natp close)
  ;;                 (< open close)
  ;;                 (= close (- (length name) 1))
  ;;                 (not (str::digitp (char name close))))
  ;;            (equal
  ;;             (let ((index-str (subseq name (+ open 1) close)))
  ;;               (mv-nth 1 (str::parse-nat-from-string index-str 0 0 0 (length index-str))))
  ;;             (let ((start (+ open 1)))
  ;;               (mv-nth 1 (str::parse-nat-from-string name 0 0 start (length name))))))
  ;;   :hints(("Goal" :in-theory (enable subseq
  ;;                                     subseq-list))))

  ;; ;; (verify-guards vl-emodwire-get-index)


  (defund vl-emodwire-p (x)
    (declare (xargs :guard t))
    (b* (((unless (and (symbolp x) x))
          nil)
         (name (symbol-name x))
         ((unless (eq (intern name "ACL2") x))
          ;; For canonicity
          nil)
         ((mv open close escape illegal)
          (vl-emodwire-scan name))
         ((when (or illegal
                    (and escape
                         (not (vl-emodwire-encoding-valid-p (explode name))))))
          ;; Improper escaping
          nil)
         ((when (and (not open) (not close)))
          ;; Fine, a blank wire with proper escaping
          t)
         ((unless (and open close
                       (< open close)
                       (= close (- (length name) 1))))
          nil)
         ((mv okp ?idx)
          (vl-emodwire-get-index name open close)))
      okp))

  (local (in-theory (enable vl-emodwire-p)))

  (defthm booleanp-of-vl-emodwire-p
    (booleanp (vl-emodwire-p x))
    :rule-classes :type-prescription)

  (defthm type-of-vl-emodwire-p
    (implies (vl-emodwire-p x)
             (and (symbolp x)
                  (not (equal x nil))))
    :rule-classes :compound-recognizer)

  (local
   (progn
     (assert! (vl-emodwire-p 'acl2::foo))
     (assert! (vl-emodwire-p 'acl2::foo[0]))
     (assert! (vl-emodwire-p 'acl2::foo[1]))
     (assert! (vl-emodwire-p 'acl2::foo[10]))
     (assert! (vl-emodwire-p 'acl2::foo[123457]))
     (assert! (not (vl-emodwire-p 'acl2::foo[01])))
     (assert! (not (vl-emodwire-p 'acl2::foo[01345])))
     (assert! (not (vl-emodwire-p 'acl2::fo[o])))
     (assert! (not (vl-emodwire-p 'acl2::fo[o)))
     (assert! (not (vl-emodwire-p 'acl2::f/o[o)))
     (assert! (not (vl-emodwire-p 'acl2::f.o[o)))
     (assert! (not (vl-emodwire-p 'acl2::f]o[o)))
     (assert! (not (vl-emodwire-p 'acl2::f{o[o)))
     (assert! (not (vl-emodwire-p 'acl2::foo])))
     (assert! (not (vl-emodwire-p 'vl2014::foo))))))


(define vl-emodwire-fix ((x vl-emodwire-p))
  :parents (vl-emodwire-p)
  :returns (x-prime vl-emodwire-p)
  :inline t
  :hooks nil
  (mbe :logic (if (vl-emodwire-p x) x 'acl2::bad-default-emodwire)
       :exec x)
  ///
  (defthm vl-emodwire-fix-when-vl-emodwire-p
    (implies (vl-emodwire-p x)
             (equal (vl-emodwire-fix x) x)))

  (fty::deffixtype vl-emodwire :pred vl-emodwire-p :fix vl-emodwire-fix
    :equiv vl-emodwire-equiv :define t))


(fty::deflist vl-emodwirelist :elt-type vl-emodwire
  :elementp-of-nil nil
  :parents (exploding-vectors)
  ///
  (local (in-theory (enable vl-emodwirelist-p)))
  (defthm symbol-listp-when-vl-emodwirelist-p
    (implies (vl-emodwirelist-p x)
             (equal (symbol-listp x)
                    (true-listp x))))

  (defthm member-of-nil-when-vl-emodwirelist-p
    (implies (vl-emodwirelist-p x)
             (not (member-equal nil x)))))


(fty::deflist vl-emodwirelistlist :elt-type vl-emodwirelist
  :elementp-of-nil t
  :parents (exploding-vectors)
  :short "A list of @(see vl-emodwire-p) lists."

  :long "<p>These are notably used as the @(':i') and @(':o') patterns for
modules; see @(see modinsts-to-eoccs) for details.</p>"

  ///
  (local (in-theory (enable vl-emodwirelistlist-p)))
  (defthm vl-emodwirelist-p-of-flatten
    (implies (vl-emodwirelistlist-p x)
             (vl-emodwirelist-p (flatten x)))))


(defsection vl-emodwire
  :parents (vl-emodwire-p)
  :short "Construct an emod wire from a base name and index."
  :long "<p>No restrictions are placed on the base name because we will
automatically encode it if necessary; see @(see emodwire-encoding).</p>

<p>We take special measures to optimize this function: we pre-generate strings
@('\"[0]\"'), @('\"[1]\"'), ..., @('\"[255]\"') so that for indicies under 256
we can avoid some concatenations.  This appears to reduce memory usage by about
half and reduces run-time by about 30% for a simple loop that builds the wire
name @('foo[33]') millions of times, but this timing is based on the fast-cat
book and may change if CCL gets a compiler-macro for CONCATENATE.</p>

<p>Note that we emulate @(see defaggregate) and add @('make-vl-emodwire') and
@('change-vl-emodwire') macros.</p>"

  (defun vl-make-indexed-wire-names-array (n)
    (declare (xargs :ruler-extenders :all))
    (cons (cons n (cat "[" (natstr n) "]"))
          (if (zp n)
              nil
            (vl-make-indexed-wire-names-array (1- n)))))

  (defconst *vl-indexed-wire-name-array*
    ;; Array of pre-computed strings "[0]", "[1]", ..., "[255]"
    (compress1 '*vl-indexed-wire-name-array*
               (cons (list :HEADER
                           :DIMENSIONS (list 256)
                           :MAXIMUM-LENGTH 257
                           :DEFAULT 0
                           :NAME '*vl-indexed-wire-name-array*)
                     (vl-make-indexed-wire-names-array 255))))

  (definlined vl-emodwire-encoded (basename index)
    ;; This is a convenient target for use in wirealist generation; we can
    ;; pre-encode a wire's name and then generate symbols for its bits by
    ;; calling this function directly.
    (declare (type string basename)
             (xargs :guard (and (maybe-natp index)
                                (or index
                                    (not (equal basename "NIL"))))))
    (mbe :logic
         (if (not index)
             (intern basename "ACL2")
           (intern (cat basename "[" (natstr index) "]") "ACL2"))
         :exec
         (cond ((not index)
                (intern basename "ACL2"))
               ((< index 256)
                (intern (cat basename (aref1 '*vl-indexed-wire-name-array*
                                             *vl-indexed-wire-name-array*
                                             index))
                        "ACL2"))
               (t
                (intern (cat basename "[" (natstr index) "]") "ACL2")))))

  (defthm vl-emodwire-p-of-vl-emodwire-encoded
    (implies (and (force (stringp name))
                  (force (maybe-natp index))
                  (force (or index (not (equal name "NIL")))))
             (vl-emodwire-p
              (vl-emodwire-encoded (vl-emodwire-encode name) index)))
    :hints(("Goal" :in-theory (enable vl-emodwire-p
                                      vl-emodwire-encoded
                                      vl-emodwire-encode
                                      vl-emodwire-encode-aux
                                      subseq
                                      subseq-list
                                      string-append))))

  (definlined vl-emodwire-exec (basename index)
    (declare (type string basename)
             (xargs :guard (and (maybe-natp index)
                                (or index (not (equal basename "NIL"))))))
    (vl-emodwire-encoded (vl-emodwire-encode basename) index))

  (defthm vl-emodwire-p-of-vl-emodwire-exec
    (implies (and (force (stringp basename))
                  (force (maybe-natp index))
                  (force (or index (not (equal basename "NIL")))))
             (vl-emodwire-p (vl-emodwire-exec basename index)))
    :hints(("Goal" :in-theory (enable vl-emodwire-exec))))


  (defund vl-emodwire (basename index)
    (declare (type string basename)
             (xargs :guard (and (maybe-natp index)
                                (or index (not (equal basename "NIL"))))
                    :guard-hints(("Goal" :in-theory (enable vl-emodwire-exec
                                                            vl-emodwire-encoded)))))
    (mbe :logic
         (let ((basename (vl-emodwire-encode basename)))
           (if (not index)
               (intern basename "ACL2")
             (intern (cat basename "[" (natstr index) "]") "ACL2")))
         :exec (vl-emodwire-exec basename index)))

  (defthmd vl-emodwire-is-vl-emodwire-exec
    (equal (vl-emodwire basename index)
           (vl-emodwire-exec basename index))
    :hints(("Goal" :in-theory (enable vl-emodwire-exec
                                      vl-emodwire-encoded
                                      vl-emodwire))))

  (local (in-theory (enable vl-emodwire-is-vl-emodwire-exec)))

  (defthm symbolp-of-vl-emodwire
    (symbolp (vl-emodwire basename index))
    :rule-classes :type-prescription)

  (defthm vl-emodwire-p-of-vl-emodwire
    (implies (and (force (stringp basename))
                  (force (maybe-natp index))
                  (force (or index (not (equal basename "NIL")))))
             (vl-emodwire-p (vl-emodwire basename index)))))


#||

(defund vl-emodwire-plain (basename index)
    (declare (type string basename)
             (xargs :guard (maybe-natp index)))
    (let ((basename (vl-emodwire-encode basename)))
      (if (not index)
          (intern basename "ACL2")
        (intern (cat basename "[" (natstr index) "]") "ACL2"))))

:q

(progn
   ;; 7.276 seconds, 1.12 GB allocated
  (gc$)
  (time$ (loop for i fixnum from 1 to 10000000 do
               (vl2014::vl-emodwire "looksLikeAVerilogName" 33))))

(progn
  ;; 10.231 seconds, 2.24 GB allocated
  (gc$)
  (time$ (loop for i fixnum from 1 to 10000000 do
               (vl2014::vl-emodwire-plain "looksLikeAVerilogName" 33))))

||#



(defsection vl-emodwire->basename
  :parents (vl-emodwire-p)
  :short "Returns the name of an @(see vl-emodwire-p), excluding the index, as
a string."

  :long "<p>For instance, the basename of @('|opcode[3]|') is @('\"opcode\"'),
and the basename of @('|reset|') is @('\"reset\"').</p>"

  (local (in-theory (enable vl-emodwire-p)))

  (defund vl-emodwire->basename (x)
    (declare (xargs :guard (vl-emodwire-p x)))
    (b* ((name (symbol-name x))
         (open (position #\[ name)))
      (vl-emodwire-decode (if open
                              (subseq name 0 open)
                            name))))

  (local (in-theory (enable vl-emodwire->basename)))

  (defthm stringp-of-vl-emodwire->basename
    (stringp (vl-emodwire->basename x))
    :rule-classes :type-prescription)

  (defthm vl-emodwire->basename-of-vl-emodwire
    (implies (and (force (stringp basename))
                  (force (maybe-natp index)))
             (equal (vl-emodwire->basename (vl-emodwire basename index))
                    basename))
    :hints(("Goal" :in-theory (enable vl-emodwire
                                      position-equal
                                      vl-emodwire-encode
                                      vl-emodwire-decode
                                      vl-emodwire-encode-aux
                                      vl-emodwire-decode-aux
                                      subseq
                                      subseq-list
                                      string-append)))))



(defsection vl-emodwire->index
  :parents (vl-emodwire-p)
  :short "Return the index of an @(see vl-emodwire-p) as a natural, or @('nil')
if there is no index."

  :long "<p>For instance, the index of @('|opcode[3]|') is @('3'), and the
index of @('|reset|') is @('nil').</p>"

(local (in-theory (enable vl-emodwire-p)))

(defund vl-emodwire->index (x)
    (declare (xargs :guard (vl-emodwire-p x)))
    (and (mbt (vl-emodwire-p x))
         (b* ((name      (symbol-name x))
              (open      (position #\[ name))
              ((when (not open))
               nil)
              (close     (position #\] name))
              (index-str (subseq name (+ open 1) close))
              ((mv index-val ?len)
               (str::parse-nat-from-string index-str 0 0 0 (length index-str))))
           index-val)))

(local (in-theory (enable vl-emodwire->index)))

(defthm type-of-vl-emodwire->index
    (or (not (vl-emodwire->index x))
        (natp (vl-emodwire->index x)))
    :rule-classes :type-prescription)

(defthm vl-emodwire->index-of-vl-emodwire
    (implies (and (force (stringp basename))
                  (force (maybe-natp index))
                  (force (or index (not (equal basename "NIL")))))
             (equal (vl-emodwire->index (vl-emodwire basename index))
                    index))
    :hints(("Goal" :in-theory (e/d (vl-emodwire
                                    position-equal
                                    vl-emodwire-encode
                                    vl-emodwire-decode
                                    vl-emodwire-encode-aux
                                    vl-emodwire-decode-aux
                                    subseq
                                    subseq-list
                                    string-append)
                                   ((force)))))))


;; Introduce defaggregate like make-vl-emodwire and change-vl-emodwire macros.

(make-event (std::da-make-maker 'vl-emodwire '(basename index) nil))
(make-event (std::da-make-changer 'vl-emodwire '(basename index) nil))



(defsection equal-when-vl-emodwire-p

; We now show that emodwires are equal exactly when their basenames and indices
; are equal.  This is a huge pain in the ass to prove, but it is a crucial
; correctness property that shows our wirenames are "canonical" or "reliable."

; Reduction 1.  Equality of emodwires is just equality of symbol names, because
; they always are in the ACL2 package.

  (local
   (defthmd main-lemma-1
     (implies (and (vl-emodwire-p x)
                   (vl-emodwire-p y))
              (equal (equal x y)
                     (equal (symbol-name x) (symbol-name y))))
     :hints(("Goal" :in-theory (union-theories (theory 'minimal-theory)
                                               '(vl-emodwire-p))))))



; Reduction 2.  Symbol-name of an emodwire can be broken down into two parts:
;
;   (1) the "basename without decoding" (everything up to the first [,
;       or the whole thing if there is no ]), and
;
;   (2) the index inside the []s.

  (local
   (defsection main-lemma-2

     (defund vl-emodwire->basename-without-decoding (x)
       ;; A useful abstraction -- just get everything up to the first [ char.
       (declare (xargs :guard (vl-emodwire-p x)
                       :guard-hints (("Goal" :in-theory (enable vl-emodwire-p)))))
       (b* ((name (symbol-name x))
            (open (position #\[ name)))
         (if open
             (subseq name 0 open)
           name)))

     (defthm stringp-of-vl-emodwire->basename-without-decoding
       (implies (vl-emodwire-p x)
                (stringp (vl-emodwire->basename-without-decoding x)))
       :hints(("Goal" :in-theory (enable vl-emodwire-p
                                         vl-emodwire->basename-without-decoding))))

     (local (defthm equal-with-implode
              (implies (and (stringp x)
                            (character-listp y))
                       (equal (equal x (implode y))
                              (equal (explode x) y)))))

     (local (defthm equal-with-append-take-self
              (equal (equal x (append (take n x) y))
                     (and (<= (nfix n) (len x))
                          (equal (nthcdr (nfix n) x) y)))))

     (local (defthm cdr-of-nthcdr
              (equal (cdr (nthcdr n x))
                     (nthcdr (+ 1 (nfix n)) x))))

     (local (in-theory (disable nthcdr-of-increment)))

     (local (defthm equal-of-cons-rewrite
              (equal (equal (cons a b) x)
                     (and (consp x)
                          (equal (car x) a)
                          (equal (cdr x) b)))))

     (defthmd main-lemma-2
       (implies (vl-emodwire-p x)
                (equal (symbol-name x)
                       (if (vl-emodwire->index x)
                           (cat (vl-emodwire->basename-without-decoding x)
                                "[" (natstr (vl-emodwire->index x)) "]")
                         (vl-emodwire->basename-without-decoding x))))
       :hints(("Goal"
               :in-theory (e/d (vl-emodwire-p
                                vl-emodwire->index
                                vl-emodwire->basename-without-decoding
                                subseq
                                subseq-list
                                string-append
                                len
                                nth)
                               (acl2::consp-under-iff-when-true-listp
                                str::explode-under-iff)))))))

; Reduction 3.  Because of the restrictions made in vl-emodwire-p on the name,
; there aren't any special characters except perhaps for { in the basename
; without decoding.  Hence, by the one-to-one nature of our decoder (as
; explained by equal-of-vl-emodwire-decode-chars), we know the real basenames
; are equal exactly when the basenames without decoding are equal.

  (local
   (defsection main-lemma-3

     (local (defthm f1
              (equal (vl-emodwire->basename x)
                     (vl-emodwire-decode (vl-emodwire->basename-without-decoding x)))
              :hints(("Goal" :in-theory (enable vl-emodwire->basename
                                                vl-emodwire->basename-without-decoding)))))

     (local
      (encapsulate
        ()
        (local (defun my-induct (n x)
                 (if (zp n)
                     x
                   (my-induct (- n 1) (cdr x)))))

        (local (defthm f2-help
                 (implies (and (vl-emodwire-encoding-valid-p x)
                               ;; This weird hyp ensures that the list doesn't end on a
                               ;; { escape.  Ugly but effective.
                               (equal (nth n x) #\[))
                          (vl-emodwire-encoding-valid-p (take n x)))
                 :hints(("Goal"
                         :induct (my-induct n x)
                         :in-theory (enable vl-emodwire-encoding-valid-p
                                            acl2::take)))))

        (defthm f2
          (implies (vl-emodwire-p x)
                   (vl-emodwire-encoding-valid-p
                    (explode (vl-emodwire->basename-without-decoding x))))
          :hints(("Goal" :in-theory (enable vl-emodwire-p
                                            vl-emodwire->basename-without-decoding
                                            subseq subseq-list))))))



     (local
      (defthm f3
        (implies (vl-emodwire-p x)
                 (let ((start (explode (vl-emodwire->basename-without-decoding x))))
                   (and (not (member-equal #\[ start))
                        (not (member-equal #\] start))
                        (not (member-equal #\. start))
                        (not (member-equal #\! start))
                        (not (member-equal #\/ start)))))
        :hints(("Goal" :in-theory (enable vl-emodwire-p
                                          vl-emodwire->basename-without-decoding)))))

     (defthmd main-lemma-3
       (implies (and (vl-emodwire-p x)
                     (vl-emodwire-p y))
                (equal (equal (vl-emodwire->basename-without-decoding x)
                              (vl-emodwire->basename-without-decoding y))
                       (equal (vl-emodwire->basename x)
                              (vl-emodwire->basename y))))
       :hints(("Goal"
               :in-theory (e/d (vl-emodwire-decode-aux
                                vl-emodwire-decode)
                               (vl-emodwire-p
                                vl-emodwire->basename
                                vl-emodwire->basename-without-decoding
                                vl-emodwire-decode-chars-identity
                                equal-of-vl-emodwire-decode-chars))
               :use ((:instance equal-of-vl-emodwire-decode-chars
                                (x (explode (vl-emodwire->basename-without-decoding x)))
                                (y (explode (vl-emodwire->basename-without-decoding y))))))))))


; Chaining it all together we see that emodwires are equal when when their
; basename/indexes are equal.

  (local (defthm main-consequence
           (implies (and (vl-emodwire-p x)
                         (vl-emodwire-p y)
                         (equal (vl-emodwire->basename x)
                                (vl-emodwire->basename y))
                         (equal (vl-emodwire->index x)
                                (vl-emodwire->index y)))
                    (equal (equal x y)
                           t))
           :hints(("Goal" :in-theory (enable main-lemma-1
                                             main-lemma-2
                                             main-lemma-3
                                             string-append)))))

; And the other direction is trivial by the functional equality axiom, so we
; can always decompose equality of emodwires into the equalities of their
; components.

  (defthm equal-when-vl-emodwire-p
    (implies (and (vl-emodwire-p x)
                  (vl-emodwire-p y))
             (equal (equal x y)
                    (and (equal (vl-emodwire->basename x)
                                (vl-emodwire->basename y))
                         (equal (vl-emodwire->index x)
                                (vl-emodwire->index y)))))
    :rule-classes ((:rewrite :backchain-limit-lst 0))))



(defprojection vl-emodwirelist->basenames (x)
  (vl-emodwire->basename x)
  :guard (vl-emodwirelist-p x)
  :result-type string-listp
  :nil-preservingp nil)

(defprojection vl-emodwirelist->indices (x)
  (vl-emodwire->index x)
  :guard (vl-emodwirelist-p x)
  :result-type vl-maybe-nat-listp
  :nil-preservingp t)




(defsection vl-emodwirelist-highest
  :parents (vl-emodwire-p)
  :short "@(call vl-emodwirelist-highest) returns a number @('n') that is at
least as large as the index of any wire with this @('basename') in @('x')."

  :long "<p>We use this in a few places during @(see e-conversion) to generate
new, fresh E wires.</p>

<p>The scheme is basically similar to that of a @(see vl-namedb-p) or @(see
vl-namefactory-p): we first find an @('n') that is larger than any @('foo[k]')
currently in use, then start generating @('foo[n]'), @('foo[n+1]'), etc.  We
don't use a namedb or namefactory because we need to generate @(see
vl-emodwire-p)s instead of strings.</p>"

  (defund vl-emodwirelist-highest (basename x)
    (declare (xargs :guard (and (stringp basename)
                                (vl-emodwirelist-p x))))
    (cond ((atom x)
           0)
          ((equal (vl-emodwire->basename (car x)) basename)
           (max (nfix (vl-emodwire->index (car x)))
                (vl-emodwirelist-highest basename (cdr x))))
          (t
           (vl-emodwirelist-highest basename (cdr x)))))

  (local (in-theory (enable vl-emodwirelist-highest)))

  (defthm natp-of-vl-emodwirelist-highest
    (natp (vl-emodwirelist-highest basename x))
    :rule-classes :type-prescription)

  (defthm vl-emodwirelist-highest-correct
    (implies (and (member-equal w x)
                  (equal (vl-emodwire->basename w) basename))
             (<= (nfix (vl-emodwire->index w))
                 (vl-emodwirelist-highest basename x)))))
