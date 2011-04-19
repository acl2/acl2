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
(include-book "str/top" :dir :system)
(include-book "../util/defs")
(local (include-book "make-event/assert" :dir :system))
(local (include-book "../util/arithmetic"))
(local (include-book "../util/position"))


(defsection emodwire-encoding
  :parents (vl-wirealist-p)
  :short "A simple encoding scheme to guarantee bracket-free basenames."

  :long "<p>In our representation of emod wire names, @(see vl-emodwire-p),
we only allow square brackets to represent indexes.  Typically wire names in
Verilog do not have any square bracket characters in them, but in principle
it is possible to use escaped identifiers to introduce such brackets.</p>

<p>To defend against this, we use a simple encoding scheme to eliminate any
<tt>[</tt> characters from a name.  Our encoding scheme is simply this:</p>

<ul>
<li>[ ---&gt; {1</li>
<li>] ---&gt; {2</li>
<li>{ ---&gt; {3</li>
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
          (otherwise
           (cons (car x) rest))))))

  (local (in-theory (enable vl-emodwire-encode-chars)))

  (defthm character-listp-of-vl-emodwire-encode-chars
    (implies (force (character-listp x))
             (character-listp (vl-emodwire-encode-chars x))))

  (defthm no-brackets-in-vl-emodwire-encode-chars
    (and (not (member-equal #\[ (vl-emodwire-encode-chars x)))
         (not (member-equal #\] (vl-emodwire-encode-chars x)))))

  (defthm vl-emodwire-encode-chars-identity
    (implies (and (not (member-equal #\[ x))
                  (not (member-equal #\] x))
                  (not (member-equal #\{ x)))
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
                    (eql (cadr x) #\3))
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
               (otherwise (cons #\{ rest)))))
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

  (local (defun my-induct (x y)
           (if (or (atom x)
                   (atom y))
               nil
             (my-induct (cdr x) (cdr y)))))

  (defthm equal-of-vl-emodwire-decode-chars
    (implies (and (vl-emodwire-encoding-valid-p x)
                  (vl-emodwire-encoding-valid-p y)
                  (not (member-equal #\[ x))
                  (not (member-equal #\] x))
                  (not (member-equal #\[ y))
                  (not (member-equal #\] y)))
             (equal (equal (vl-emodwire-decode-chars x)
                           (vl-emodwire-decode-chars y))
                    (equal (list-fix x)
                           (list-fix y))))
    :hints(("Goal"
            :induct (my-induct x y)
            :expand ((vl-emodwire-decode-chars x)
                     (vl-emodwire-decode-chars y)
                     (vl-emodwire-encoding-valid-p x)
                     (vl-emodwire-encoding-valid-p y))
            :do-not '(generalize fertilize)
            :in-theory (disable vl-emodwire-decode-chars-identity)
            )))

  (defund vl-emodwire-encode-aux (x)
    ;; Slow. We don't expect this to ever really be called in practice.  We keep
    ;; this in a separate function to minimize expansion from inlining the main
    ;; function.
    (declare (type string x))
    (b* ((chars   (coerce x 'list))
         (encoded (vl-emodwire-encode-chars chars)))
      (coerce encoded 'string)))

  (defund vl-emodwire-decode-aux (x)
    ;; Slow. We don't expect this to ever really be called in practice.  We keep
    ;; this in a separate function to minimize expansion from inlining the main
    ;; function.
    (declare (type string x))
    (b* ((chars   (coerce x 'list))
         (decoded (vl-emodwire-decode-chars chars)))
      (coerce decoded 'string)))

  (local (in-theory (enable vl-emodwire-encode-aux
                            vl-emodwire-decode-aux)))

  ;; We seem to be able to do a lot better in raw lisp.
  ;;
  ;; Encoding with no inlining:
  ;;   ACL2 version: 4.137 seconds   (no inlining)
  ;;   Raw version:  0.531 seconds   (no inlining)
  ;;
  ;; Decoding with no inlining:
  ;;   ACL2 version: 1.403 seconds   (no inlining)
  ;;   Raw version:  0.435 seconds   (no inlining)

  ;; (time$
  ;;  (loop for i from 1 to 10000000 do
  ;;        (vl::vl-emodwire-encode "looksLikeAVerilogWire")))

  ;; (time$
  ;;   (loop for i from 1 to 10000000 do
  ;;         (vl::vl-emodwire-decode "looksLikeAVerilogWire")))


  (defund vl-emodwire-encode (x)
    (declare (type string x))
    (mbe :logic (vl-emodwire-encode-aux x)
         :exec (if (or (position #\[ (the string x))
                       (position #\] (the string x))
                       (position #\{ (the string x)))
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
               (when (or (eql c #\[)
                         (eql c #\])
                         (eql c #\{))
                 (return-from vl-emodwire-encode
                              (vl::vl-emodwire-encode-aux x)))))
       x))

   (defun vl-emodwire-decode (x)
     (declare (type string x))
     (let ((xl (length (the simple-string x))))
       (loop for i fixnum from 0 below xl do
             (let ((c (schar x i)))
               (when (or (eql c #\{))
                 (return-from vl-emodwire-decode
                              (vl::vl-emodwire-decode-aux x)))))
       x)))

  (defttag nil))



(local (defthm digit-listp-encoding-help
         (implies (str::digit-listp x)
                  (and (not (member-equal #\] x))
                       (not (member-equal #\[ x))
                       (not (member-equal #\{ x))))
         :hints(("Goal" :in-theory (enable str::digit-listp)))))



(defsection vl-emodwire-p
  :parents (vl-wirealist-p)
  :short "@(call vl-emodwire-p) recognizes symbols that VL generates as wire
names for Emod."

  :long "<p>Emod uses a permissive pattern system that allows almost any atom
to be used as a wire name.  But when VL is used to translate Verilog modules,
we always produce wire names that are symbols, whose names are either <b>simple
names</b> like <tt>\"reset\"</tt> or <b>indexed names</b> like
<tt>\"opcode[3]\"</tt>.</p>

<p>We always generate wire names in the <tt>ACL2</tt> package.  This is due to
historic convention, but also is a good idea for efficiency: we can control the
size of the ACL2 package at the time we build ACL2, but we have no
method (well, ttags I suppose) to construct a new package with a larger size.
See the efficiency considerations in @(see vl-wirealist-p) for more
details.</p>"

  (defund vl-emodwire-p (x)
    (declare (xargs :guard t))
    (b* (((unless (symbolp x))
          nil)
         (name (symbol-name x))
         ((unless (eq (intern name "ACL2") x))
          ;; For canonicity
          nil)
         (open   (position #\[ name))
         (close  (position #\] name))
         (escape (position #\{ name))
         ((when (and escape
                     (not (vl-emodwire-encoding-valid-p (coerce name 'list)))))
          ;; Improper escaping
          nil)
         ((when (and (not open) (not close)))
          ;; Fine, a blank wire with proper escaping
          t)
         ((unless (and open close
                       (< open close)
                       (= close (- (length name) 1))))
          nil)
         (index-str (subseq name (+ open 1) close))
         ((mv index-val len)
          (str::parse-nat-from-string index-str 0 0 0 (length index-str))))
      (and
       ;; Everything between brackets should be digits
       (equal len (length index-str))
       ;; Ensures that the digits are canonical (e.g., no leading zeros)
       (equal index-str (str::natstr index-val)))))

  (local (in-theory (enable vl-emodwire-p)))

  (defthm booleanp-of-vl-emodwire-p
    (booleanp (vl-emodwire-p x))
    :rule-classes :type-prescription)

  (defthm type-of-vl-emodwire-p
    (implies (vl-emodwire-p x)
             (symbolp x))
    :rule-classes :compound-recognizer)

  (local
   (progn
     (assert! (vl-emodwire-p 'acl2::foo))
     (assert! (vl-emodwire-p 'acl2::foo[0]))
     (assert! (vl-emodwire-p 'acl2::foo[1]))
     (assert! (not (vl-emodwire-p 'acl2::foo[01])))
     (assert! (not (vl-emodwire-p 'acl2::fo[o])))
     (assert! (not (vl-emodwire-p 'acl2::fo[o)))
     (assert! (not (vl-emodwire-p 'acl2::foo])))
     (assert! (not (vl-emodwire-p 'vl::foo))))))


(defsection vl-emodwirelist-p
  :parents (vl-wirealist-p)
  :short "A list of @(see vl-emodwire-p)s."

  (deflist vl-emodwirelist-p (x)
    (vl-emodwire-p x)
    :elementp-of-nil t)

  (defthm symbol-listp-when-vl-emodwirelist-p
    (implies (vl-emodwirelist-p x)
             (equal (symbol-listp x)
                    (true-listp x)))
    :hints(("Goal" :induct (len x)))))


(defsection vl-emodwirelistlist-p
  :parents (vl-wirealist-p)
  :short "A list of @(see vl-emodwire-p) lists."
  :long "<p>These are used as the <tt>:i</tt> and <tt>:o</tt> patterns for
modules; see @(see make-defm-command) for details.</p>"

  (deflist vl-emodwirelistlist-p (x)
    (vl-emodwirelist-p x)
    :guard t
    :elementp-of-nil t))

(defthm vl-emodwirelist-p-of-flatten
  (implies (vl-emodwirelistlist-p x)
           (vl-emodwirelist-p (flatten x)))
  :hints(("Goal" :in-theory (enable vl-emodwirelistlist-p))))



(defsection vl-emodwire
  :parents (vl-emodwire-p)
  :short "Construct an emod wire from a base name and index."
  :long "<p>No restrictions are placed on the base name because we will
automatically encode it if necessary; see @(see emodwire-encoding).</p>

<p>We take special measures to optimize this function: we pre-generate strings
<tt>\"[0]\"</tt>, <tt>\"[1]\"</tt>, ..., <tt>\"[255]\"</tt> so that for
indicies under 256 we can avoid some concatenations.  This appears to reduce
memory usage by about half and reduces run-time by about 30% for a simple loop
that builds the wire name <tt>foo[33]</tt> millions of times, but this timing
is based on the fast-cat book and may change if CCL gets a compiler-macro for
CONCATENATE.</p>

<p>Note that we emulate @(see defaggregate) and add <tt>make-vl-emodwire</tt>
and <tt>change-vl-emodwire</tt> macros.</p>"

  (defun vl-make-indexed-wire-names-array (n)
    (declare (xargs :ruler-extenders :all))
    (cons (cons n (str::cat "[" (str::natstr n) "]"))
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
             (xargs :guard (vl-maybe-natp index)))
    (mbe :logic
         (if (not index)
             (intern basename "ACL2")
           (intern (str::cat basename "[" (str::natstr index) "]") "ACL2"))
         :exec
         (cond ((not index)
                (intern basename "ACL2"))
               ((< index 256)
                (intern (str::cat basename (aref1 '*vl-indexed-wire-name-array*
                                                  *vl-indexed-wire-name-array*
                                                  index))
                        "ACL2"))
               (t
                (intern (str::cat basename "[" (str::natstr index) "]") "ACL2")))))

  (defthm vl-emodwire-p-of-vl-emodwire-encoded
    (implies (and (force (stringp basename))
                  (force (vl-maybe-natp index)))
             (vl-emodwire-p
              (vl-emodwire-encoded (vl-emodwire-encode name) index)))
    :hints(("Goal" :in-theory (enable vl-emodwire-p
                                      vl-emodwire-encoded
                                      vl-emodwire-encode
                                      vl-emodwire-encode-aux
                                      subseq
                                      string-append))))

  (definlined vl-emodwire-exec (basename index)
    (declare (type string basename)
             (xargs :guard (vl-maybe-natp index)))
    (vl-emodwire-encoded (vl-emodwire-encode basename) index))

  (defthm vl-emodwire-p-of-vl-emodwire-exec
    (implies (and (force (stringp basename))
                  (force (vl-maybe-natp index)))
             (vl-emodwire-p (vl-emodwire-exec basename index)))
    :hints(("Goal" :in-theory (enable vl-emodwire-exec))))


  (defund vl-emodwire (basename index)
    (declare (type string basename)
             (xargs :guard (vl-maybe-natp index)
                    :guard-hints(("Goal" :in-theory (enable vl-emodwire-exec
                                                            vl-emodwire-encoded)))))
    (mbe :logic
         (let ((basename (vl-emodwire-encode basename)))
           (if (not index)
               (intern basename "ACL2")
             (intern (str::cat basename "[" (str::natstr index) "]") "ACL2")))
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
                  (force (vl-maybe-natp index)))
             (vl-emodwire-p (vl-emodwire basename index)))))

#||

(defund vl-emodwire-plain (basename index)
    (declare (type string basename)
             (xargs :guard (vl-maybe-natp index)))
    (let ((basename (vl-emodwire-encode basename)))
      (if (not index)
          (intern basename "ACL2")
        (intern (str::cat basename "[" (str::natstr index) "]") "ACL2"))))

:q

(progn
   ;; 7.276 seconds, 1.12 GB allocated
  (gc$)
  (time$ (loop for i fixnum from 1 to 10000000 do
               (vl::vl-emodwire "looksLikeAVerilogName" 33))))

(progn
  ;; 10.231 seconds, 2.24 GB allocated
  (gc$)
  (time$ (loop for i fixnum from 1 to 10000000 do
               (vl::vl-emodwire-plain "looksLikeAVerilogName" 33))))

||#



(defsection vl-emodwire->basename
  :parents (vl-emodwire-p)
  :short "Returns the name of an @(see vl-emodwire-p), excluding the index, as
a string."

  :long "<p>For instance, the basename of <tt>|opcode[3]|</tt> is
<tt>\"opcode\"</tt>, and the basename of <tt>|reset|</tt> is
<tt>\"reset\"</tt>.</p>"

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
                  (force (vl-maybe-natp index)))
             (equal (vl-emodwire->basename (vl-emodwire basename index))
                    basename))
    :hints(("Goal" :in-theory (enable vl-emodwire
                                      position-equal
                                      vl-emodwire-encode
                                      vl-emodwire-decode
                                      vl-emodwire-encode-aux
                                      vl-emodwire-decode-aux
                                      subseq
                                      string-append)))))



(defsection vl-emodwire->index
  :parents (vl-emodwire-p)
  :short "Return the index of an @(see vl-emodwire-p) as a natural, or
<tt>nil</tt> if there is no index."

  :long "<p>For instance, the index of <tt>|opcode[3]|</tt> is
<tt>3</tt>, and the index of <tt>|reset|</tt> is <tt>nil</tt>.</p>"

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
                  (force (vl-maybe-natp index)))
             (equal (vl-emodwire->index (vl-emodwire basename index))
                    index))
    :hints(("Goal" :in-theory (e/d (vl-emodwire
                                    position-equal
                                    vl-emodwire-encode
                                    vl-emodwire-decode
                                    vl-emodwire-encode-aux
                                    vl-emodwire-decode-aux
                                    subseq
                                    string-append)
                                   ((force)))))))


(make-event (cutil::da-make-maker-fn 'vl-emodwire '(basename index)))
(make-event (cutil::da-make-maker 'vl-emodwire '(basename index)))
(make-event (cutil::da-make-changer-fn 'vl-emodwire '(basename index)))
(make-event (cutil::da-make-changer 'vl-emodwire '(basename index)))



(defsection equal-when-vl-emodwire-p

; This is a huge pain in the ass to prove, but it is a crucial correctness
; property that shows emod wirenames are "canonical" or "reliable."

  (local (defthmd main-lemma-1
           (implies (and (vl-emodwire-p x)
                         (vl-emodwire-p y))
                    (equal (equal x y)
                           (equal (symbol-name x) (symbol-name y))))
           :hints(("Goal" :in-theory (union-theories (theory 'minimal-theory)
                                                     '(vl-emodwire-p))))))


  (local (defund vl-emodwire->basename-without-decoding (x)
           ;; A useful abstraction
           (declare (xargs :guard (vl-emodwire-p x)
                           :guard-hints (("Goal" :in-theory (enable vl-emodwire-p)))))
           (b* ((name (symbol-name x))
                (open (position #\[ name)))
             (if open
                 (subseq name 0 open)
               name))))

  (local (defthm stringp-of-vl-emodwire->basename-without-decoding
           (implies (vl-emodwire-p x)
                    (stringp (vl-emodwire->basename-without-decoding x)))
           :hints(("Goal" :in-theory (enable vl-emodwire-p
                                             vl-emodwire->basename-without-decoding)))))


  (local
   (defsection main-lemma-2

     (local (defthm equal-with-coerce-string
              (implies (and (stringp x)
                            (character-listp y))
                       (equal (equal x (coerce y 'string))
                              (equal (coerce x 'list) y)))))

     (local (defthm equal-with-append-take-self
              (equal (equal x (append (simpler-take n x) y))
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
                           (str::cat (vl-emodwire->basename-without-decoding x)
                                     "[" (str::natstr (vl-emodwire->index x)) "]")
                         (vl-emodwire->basename-without-decoding x))))
       :hints(("Goal"
               :in-theory (e/d (vl-emodwire-p
                                vl-emodwire->index
                                vl-emodwire->basename-without-decoding
                                subseq
                                string-append
                                len
                                nth)
                               (consp-under-iff-when-true-listp
                                coerce-list-under-iff)))))))


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
                          (vl-emodwire-encoding-valid-p (simpler-take n x)))
                 :hints(("Goal"
                         :induct (my-induct n x)
                         :in-theory (enable vl-emodwire-encoding-valid-p
                                            simpler-take)))))

        (defthm f2
          (implies (vl-emodwire-p x)
                   (vl-emodwire-encoding-valid-p
                    (coerce (vl-emodwire->basename-without-decoding x) 'list)))
          :hints(("Goal" :in-theory (enable vl-emodwire-p
                                            vl-emodwire->basename-without-decoding
                                            subseq))))))

     (local
      (defthm f3
        (implies (vl-emodwire-p x)
                 (not (member-equal #\[ (coerce (vl-emodwire->basename-without-decoding x) 'list))))
        :hints(("Goal" :in-theory (enable vl-emodwire-p
                                          vl-emodwire->basename-without-decoding)))))

     (local
      (defthm f4
        (implies (vl-emodwire-p x)
                 (not (member-equal #\] (coerce (vl-emodwire->basename-without-decoding x) 'list))))
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
                                (x (coerce (vl-emodwire->basename-without-decoding x) 'list))
                                (y (coerce (vl-emodwire->basename-without-decoding y) 'list)))))))))


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



(defsection vl-emodwire-<

  (defund vl-emodwire-< (x y)
    (declare (xargs :guard (and (vl-emodwire-p x)
                                (vl-emodwire-p y))))
    (let ((xn (vl-emodwire->basename x))
          (yn (vl-emodwire->basename y)))
      (or (str::strnat< xn yn)
          (and (equal xn yn)
               (let ((xi (vl-emodwire->index x))
                     (yi (vl-emodwire->index y)))
                 (cond ((and xi yi) (< xi yi))
                       (yi          t)
                       (t           nil)))))))

  (local (in-theory (enable vl-emodwire-<)))

  (defthm vl-emodwire-<-irreflexive
    (not (vl-emodwire-< x x)))

  (defthm vl-emodwire-<-transitive
    (implies (and (vl-emodwire-< x y)
                  (vl-emodwire-< y z)
                  (vl-emodwire-p x)
                  (vl-emodwire-p y)
                  (vl-emodwire-p z))
             (vl-emodwire-< x z))))


(defsection vl-emodwire-sort

  (acl2::defsort :compare< vl-emodwire-<
                 :comparablep vl-emodwire-p
                 :prefix vl-emodwire)

  (defthm vl-emodwire-list-p-removal
    (equal (vl-emodwire-list-p x)
           (vl-emodwirelist-p x))
    :hints(("Goal" :in-theory (enable vl-emodwire-list-p))))

  (defthm vl-emodwire-listp-of-vl-emodwire-sort
    (implies (force (vl-emodwirelist-p x))
             (vl-emodwirelist-p (vl-emodwire-sort x)))
    :hints(("Goal"
            :in-theory (disable vl-emodwire-sort-creates-comparable-listp)
            :use ((:instance vl-emodwire-sort-creates-comparable-listp
                             (acl2::x x)))))))



(defsection vl-match-contiguous-indices
  :parents (vl-verilogify-emodwirelist)
  :short "Identify one strictly increasing segment of a @(see
vl-maybe-nat-listp)."

  :long "<p>@(call vl-match-contiguous-indices) tries to consume the leading
portion of <tt>x</tt> if it counts up from <tt>n</tt>.  It returns <tt>(mv
range-end rest)</tt>.  Here's an illustrative example:</p>

<code>
 (vl-match-contiguous-indices 1 '(2 3 4 5 10 11 12)) --&gt; (mv 5 (10 11 12))
</code>

<p>We use when collapsing emod names into Verilog-style names; see @(see
vl-merge-contiguous-indices).</p>"

  (defund vl-match-contiguous-indices (n x)
    (declare (xargs :guard (and (vl-maybe-natp n)
                                (vl-maybe-nat-listp x))
                    :measure (len x)))
    (if (or (not (natp n))
            (atom x)
            (not (equal (car x) (+ n 1))))
        (mv n x)
      (vl-match-contiguous-indices (+ n 1) (cdr x))))

  (local (in-theory (enable vl-match-contiguous-indices)))

  (defthm vl-maybe-natp-of-vl-match-contiguous-indices
    (implies (and (force (vl-maybe-natp n))
                  (force (vl-maybe-nat-listp x)))
             (vl-maybe-natp (mv-nth 0 (vl-match-contiguous-indices n x)))))

  (defthm vl-maybe-nat-listp-of-vl-match-contiguous-indices
    (implies (and (force (vl-maybe-natp n))
                  (force (vl-maybe-nat-listp x)))
             (vl-maybe-nat-listp (mv-nth 1 (vl-match-contiguous-indices n x)))))

  (defthm len-of-vl-match-contiguous-indices
    (implies (not (equal n (mv-nth 0 (vl-match-contiguous-indices n x))))
             (< (len (mv-nth 1 (vl-match-contiguous-indices n x)))
                (len x)))
    :rule-classes ((:rewrite) (:linear)))

  (defthm vl-match-contiguous-indices-fails-on-nil
    (equal (mv-nth 0 (vl-match-contiguous-indices nil x))
           nil))

  (defthm vl-match-contiguous-indices-monotonic-on-success
    (implies (and (not (equal n (mv-nth 0 (vl-match-contiguous-indices n x))))
                  (force (vl-maybe-natp n))
                  (force (vl-maybe-nat-listp x)))
             (< n (mv-nth 0 (vl-match-contiguous-indices n x))))
    :rule-classes ((:rewrite) (:linear)))

  (defthm vl-match-contiguous-indices-exists-on-success
    (implies (and (not (equal n (mv-nth 0 (vl-match-contiguous-indices n x))))
                  (force (vl-maybe-natp n))
                  (force (vl-maybe-nat-listp x)))
             (natp (mv-nth 0 (vl-match-contiguous-indices n x))))))



(defsection vl-merge-contiguous-indices
  :parents (vl-verilogify-emodwirelist)
  :short "Transform a @(see vl-maybe-nat-listp) by combining contiguous
sequences of indices into <tt>(low . high)</tt> pairs."

  :long "<p>For example:</p>
<code>
 (vl-merge-contiguous-indices '(1 2 3 5 6 7 8 9 10 15 17 18))
  --&gt;
 ((1 . 3) (5 . 10) 15 (17 . 18))
</code>"

  (defund vl-merged-index-p (x)
    (declare (xargs :guard t))
    (or (not x)
        (natp x)
        (and (consp x)
             (natp (car x))
             (natp (cdr x))
             (< (car x) (cdr x)))))

  (deflist vl-merged-index-list-p (x)
    (vl-merged-index-p x)
    :elementp-of-nil t)

  (defund vl-merge-contiguous-indices (x)
    (declare (xargs :guard (vl-maybe-nat-listp x)
                    :measure (len x)))
    (if (atom x)
        nil
      (mv-let (range-end rest)
              (vl-match-contiguous-indices (car x) (cdr x))
              (if (equal (car x) range-end)
                  (cons (car x)
                        (vl-merge-contiguous-indices (cdr x)))
                (cons (cons (car x) range-end)
                      (vl-merge-contiguous-indices rest))))))

  (local (in-theory (enable vl-merge-contiguous-indices
                            vl-merged-index-p)))

  (defthm vl-merged-index-list-p-of-vl-merge-contiguous-indices
    (implies (force (vl-maybe-nat-listp x))
             (vl-merged-index-list-p (vl-merge-contiguous-indices x)))))



(defsection vl-verilogify-merged-indices
  :parents (vl-verilogify-emodwirelist)
  :short "Transform a merged index list into Verilog-style wire names."

  :long "<p>@(call vl-verilogify-merged-indices) takes <tt>name</tt>, which
should be a string, and <tt>x</tt>, a <tt>vl-merged-index-list-p</tt> such as
@(see vl-merge-contiguous-indices) generates.  It produces a list of strings
that represent the Verilog bit- and part-selects of these indices from
<tt>name</tt>.  For instance,</p>

<code>
 (vl-verilogify-merged-indices \"foo\" '(1 (3 . 6) 8))
 --&gt;
 (\"foo[1]\" \"foo[6:3]\" \"foo[8]\")
</code>"

  (local (in-theory (enable vl-merged-index-p)))

  (defund vl-verilogify-merged-indices (name x)
    (declare (xargs :guard (and (stringp name)
                                (vl-merged-index-list-p x))))
    (if (atom x)
        nil
      (cons
       (cond ((not (car x))
              ;; A nil index means the whole wire.
              name)
             ((natp (car x))
              ;; A single index, name[i]
              (str::cat name "[" (str::natstr (car x)) "]"))
             ((consp (car x))
              ;; A merged range, (low . high)
              (let ((low  (caar x))
                    (high (cdar x)))
                (str::cat name "[" (str::natstr high) ":" (str::natstr low) "]"))))
       (vl-verilogify-merged-indices name (cdr x)))))

  (local (in-theory (enable vl-verilogify-merged-indices)))

  (defthm string-listp-of-vl-verilogify-merged-indices
    (implies (and (force (stringp name))
                  (force (vl-merged-index-list-p x)))
             (string-listp (vl-verilogify-merged-indices name x)))))




(defund vl-verilogify-emodwirelist-2 (name x)
; Returns (MV NAME-INDICES REST-X)
;  NAME-INDICES: indices of all wires with NAME at the front of the list.
;  REST-X: remainder of X after the wires with this NAME.
  (declare (xargs :guard (and (stringp name)
                              (vl-emodwirelist-p x))))
  (cond ((atom x)
         (mv nil x))
        ((equal name (vl-emodwire->basename (car x)))
         (mv-let (matches2 rest)
           (vl-verilogify-emodwirelist-2 name (cdr x))
           (mv (cons (vl-emodwire->index (car x)) matches2) rest)))
        (t
         (mv nil x))))

(defthm vl-verilogify-emodwirelist-2-basics
  (implies (and (force (stringp name))
                (force (vl-emodwirelist-p x)))
           (let ((result (vl-verilogify-emodwirelist-2 name x)))
             (and (vl-maybe-nat-listp (mv-nth 0 result))
                  (vl-emodwirelist-p (mv-nth 1 result)))))
  :hints(("Goal" :in-theory (enable vl-verilogify-emodwirelist-2))))

(defthm acl2-count-of-vl-verilogify-emodwirelist-2-weak
  (<= (acl2-count (mv-nth 1 (vl-verilogify-emodwirelist-2 name x)))
      (acl2-count x))
  :rule-classes ((:rewrite) (:linear))
  :hints(("Goal" :in-theory (enable vl-verilogify-emodwirelist-2))))

(defthm acl2-count-of-vl-verilogify-emodwirelist-2-strong
  (implies (and (consp x)
                (equal name (vl-emodwire->basename (car x))))
           (< (acl2-count (mv-nth 1 (vl-verilogify-emodwirelist-2 name x)))
              (acl2-count x)))
  :rule-classes ((:rewrite) (:linear))
  :hints(("Goal" :in-theory (enable vl-verilogify-emodwirelist-2))))



(defund vl-verilogify-emodwirelist-1 (name x)
  ;; Returns (MV STRING-LIST REST-X)
  (declare (xargs :guard (and (stringp name)
                              (vl-emodwirelist-p x))))
  (b* (((mv indices rest-x)
        (vl-verilogify-emodwirelist-2 name x))
       (merged-indices (vl-merge-contiguous-indices indices))
       (verilog-names
        (vl-verilogify-merged-indices name merged-indices)))
    (mv verilog-names rest-x)))

(defthm vl-verilogify-emodwirelist-1-basics
  (implies (and (force (stringp name))
                (force (vl-emodwirelist-p x)))
           (let ((result (vl-verilogify-emodwirelist-1 name x)))
             (and (string-listp (mv-nth 0 result))
                  (vl-emodwirelist-p (mv-nth 1 result)))))
  :hints(("Goal" :in-theory (enable vl-verilogify-emodwirelist-1))))

(defthm acl2-count-of-vl-verilogify-emodwirelist-1-weak
  (<= (acl2-count (mv-nth 1 (vl-verilogify-emodwirelist-1 name x)))
      (acl2-count x))
  :rule-classes ((:rewrite) (:linear))
  :hints(("Goal" :in-theory (enable vl-verilogify-emodwirelist-1))))

(defthm acl2-count-of-vl-verilogify-emodwirelist-1-strong
  (implies (and (consp x)
                (equal name (vl-emodwire->basename (car x))))
           (< (acl2-count (mv-nth 1 (vl-verilogify-emodwirelist-1 name x)))
              (acl2-count x)))
  :rule-classes ((:rewrite) (:linear))
  :hints(("Goal" :in-theory (enable vl-verilogify-emodwirelist-1))))


(defund vl-verilogify-emodwirelist-0 (x)
  ;; Returns a string list
  ;; We assume X is already sorted.
  (declare (xargs :guard (vl-emodwirelist-p x)))
  (if (atom x)
      nil
    (b* ((name (vl-emodwire->basename (car x)))
         ((mv first-strings rest-x)
          (vl-verilogify-emodwirelist-1 name x))
         (rest-strings
          (vl-verilogify-emodwirelist-0 rest-x)))
      (append first-strings rest-strings))))

(defthm string-listp-of-vl-verilogify-emodwirelist-0
  (implies (force (vl-emodwirelist-p x))
           (string-listp (vl-verilogify-emodwirelist-0 x)))
  :hints(("Goal" :in-theory (enable vl-verilogify-emodwirelist-0))))


(defsection vl-verilogify-emodwirelist
  :parents (vl-wirealist-p)
  :short "Merge a list of @(see vl-emodwire-p)s into Verilog-style names."

  (defund vl-verilogify-emodwirelist (x)
    (declare (xargs :guard (vl-emodwirelist-p x)))
    (vl-verilogify-emodwirelist-0 (vl-emodwire-sort (redundant-list-fix x))))

  (defthm string-listp-of-vl-verilogify-emodwirelist
    (implies (force (vl-emodwirelist-p x))
             (string-listp (vl-verilogify-emodwirelist x)))
    :hints(("Goal" :in-theory (enable vl-verilogify-emodwirelist))))

  (local
   (assert! (equal
             (vl-verilogify-emodwirelist
              #!ACL2
              '(|foo[0]| |bar[18]| |foo[3]| |bar[0]|
                |foo[4]| |foo[5]| |bar[5]| |bar[17]|))
             (list "bar[0]" "bar[5]" "bar[18:17]"
                   "foo[0]" "foo[5:3]")))))



(defund vl-verilogify-symbols (x)
  (declare (xargs :guard (symbol-listp x)))
  (if (vl-emodwirelist-p x)
      (vl-verilogify-emodwirelist x)
    (prog2$
     (cw "Note: in vl-verilogify-symbols, symbols are not all emod wires!~%")
     (symbol-list-names x))))

(defthm string-listp-of-vl-verilogify-symbols
  (implies (force (symbol-listp x))
           (string-listp (vl-verilogify-symbols x)))
  :hints(("Goal" :in-theory (enable vl-verilogify-symbols))))

