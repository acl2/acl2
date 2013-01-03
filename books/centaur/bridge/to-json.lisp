; ACL2 Bridge
; Copyright (C) 2012 Centaur Technology
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

(in-package "BRIDGE")
(include-book "misc/definline" :dir :system)
(include-book "str/cat" :dir :system)
(include-book "str/natstr" :dir :system)
(include-book "unicode/two-nats-measure" :dir :system)
(local (include-book "unicode/explode-atom" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "misc/assert" :dir :system))


(defsection json-encoding
  :parents (bridge)
  :short "Simple encoder to convert ACL2 Objects into JSON Objects."

  :long "<p>Sensibly converting ACL2 objects into JSON is not at all
straightforward.</p>

<p>On one hand, JSON is very rich.  Should we try to map association lists into
JSON objects, or should we just treat all cons trees the same and use arrays?
Since JSON has distinct NULL and FALSE values, which should we map NIL
into?</p>

<p>On the other, JSON is missing some types that we would like.  Should we just
map ACL2 symbols and strings into strings, and lose the distinction between
them?  What on earth should we do with rationals and complex numbers?  Should
we assume that the JSON consumer supports bignums, or use a separate bignum
encoding?</p>

<p>Arguably, the \"safe\" approach would be: develop a reliable JSON encoding
that ensures a unique interpretation of each ACL2 object.  For instance, we
should keep symbols and strings separate, record the name/package of each
symbol separately, etc.</p>

<p>But that would suck.  The resulting JSON objects would be full of unwieldy
type information, which most of the time we wouldn't care about.  Usually, we
are hooking up ACL2 to web pages or other interfaces that want to get some
simple, small fragments of data.  In this context, I'd prefer a simple
representation that is easy to work with, even at the cost of losing some
precision.</p>

<h3>Atoms</h3>

<p>I encode every ACL2 atom as a JSON string.  For example:</p>

@({
      Lisp Atom           JSON
    ---------------------------------------
       NIL                \"NIL\"
       T                  \"T\"
       FOO                \"FOO\"
       :FOO               \":FOO\"
       \"foo\"              \"foo\"
       #\\f                \"f\"
       123                \"123\"
       -123               \"-123\"
       -1/2               \"-1/2\"
       #c(17/2 -3/8)      \"#C(17/2 -3/8)\"
    ---------------------------------------
})

<p>This has many quirks.  The main weirdness is that there are many ACL2
objects which, although they are not EQUAL, cannot be told apart from one
another in the JSON world.  For instance, the atoms on each line below have
identical JSON encodings:</p>

<ul>
<li>@('ACL2::FOO,    VL::FOO,     \"FOO\"          ')</li>
<li>@('ACL2::F,      VL::F,       \"F\",      #\\F ')</li>
<li>@('ACL2::|123|,  VL::|123|,   \"123\",    123  ')</li>
<li>@(':FOO,         \":FOO\",    ACL2::|:FOO|     ')</li>
</ul>

<p>Some motivation behind this approach:</p>

<ul>

<li>Why use \"NIL\" and \"T\" instead of, e.g., JSON's null (or false) and
true?  The main reason is that null/true can't be used as keys in JSON objects,
so this would lead to either special handling of alists with nil/t keys, or
alists that have different encoding depending on their keys, and it just seems
simpler to use strings for all atoms.</li>

<li>Why use \"123\" when JSON has integers?  The same reason as for NIL and T
applies, but also: the JSON \"spec\" doesn't mandate what ranges of numbers its
implementations have to support, and practically speaking many of its
implementations don't use bignums.  So, what are the options?  (1) Use integers
for small numbers and do something special for bignums.  But this would be
quite error prone when programming the client.  (2) Assume bignums are
supported and just accept that clients will see garbage in some cases.  But
that is just terrible.  So given all this, just using strings seems like the
best thing to do.</li>

</ul>

<h3>Conses</h3>

<p>With one exception (see below), I encode any true-lists as a JSON arrays
containing its encoded elements, and I encode any \"improper\" list as a JSON
array containing its encoded elements AND its final cdr.  For example:</p>

@({
       Lisp Object                     JSON
    -------------------------------------------------------------
       (a . nil)                       [\"A\"]
       (a . b)                         [\"A\",\"B\"]
       (a b . nil)                     [\"A\",\"B\"]
       (a b . c)                       [\"A\",\"B\",\"C\"]
       (a b c . nil)                   [\"A\",\"B\",\"C\"]
       ((a . b) (c . d) . e)           [[\"A\",\"B\"],[\"C\",\"D\"],\"E\"]
})

<p>This has its own quirks.  For instance, as with atoms, you can't tell the
difference between Lisp objects like: (A B C) and (A B . C).</p>

<p>The exception is that, for proper ALISTS whose every key is an atom, I
instead generate the corresponding JSON Object.  For example:</p>

@({
       Lisp Object                     JSON
    -------------------------------------------------------------
       ((a . b))                      {\"A\":\"B\"}
       ((a . b) (c . d))              {\"A\":\"B\",\"C\":\"D\"}
       ((a . b) (c . d) . e)          [[\"A\",\"B\"],[\"C\",\"D\"],\"E\"]
})

<p>In certain cases, this runs the risk that you might see a different encoding
for an alist, depending on whether or not you have inserted a cons.  But many
alists have atoms as keys, and it seems nice to use a real JSON object here
instead of a nested array of arrays.</p>


<h3>Note about Top-Level JSON Objects</h3>

<p>Top-level @('JSON-text') objects must, according to the JSON grammer, be
either JSON Objects or Arrays.  Note that <b>WE DO NOT OBEY THIS.</b> If the
object we're given is an ordinary ACL2 atom, we just encode it as a JSON
string.</p>

<p>We found this to be useful in our client code.  It's nice to create a JSON
object that says: the return value is such and so, the standard output was such
and so, and the error value was such and so.  In this context, we just want to
stitch our ACL2 object into a larger piece of JSON text, and strings are
okay.</p>")



(defsection json-encode-weird-char
  :parents (json-encoding)
  :long "<p>This accumulates the special \\uXXXX style encoding of a character
whose code is @('code') onto @('acc').  This lets us properly encode weird
things like control characters.  We don't have to escape everything this way,
e.g., using \\n or \\t would be more readable.</p>"

  (local (defthm crock
           (<= (acl2::loghead 4 code) 15)
           :rule-classes ((:rewrite) (:linear))
           :hints(("Goal"
                   :in-theory (disable acl2::unsigned-byte-p-of-loghead)
                   :use ((:instance acl2::unsigned-byte-p-of-loghead
                                    (acl2::size 4)
                                    (acl2::size1 4)
                                    (acl2::i code)))))))

  (local (defthm crock2
           (implies (and (integerp code)
                         (<= 0 code)
                         (< code 256))
                    (<= (acl2::logtail 4 code) 15))
           :rule-classes ((:rewrite) (:linear))
           :hints(("Goal"
                   :in-theory (disable acl2::unsigned-byte-p-of-logtail)
                   :use ((:instance acl2::unsigned-byte-p-of-logtail
                                    (acl2::size 4)
                                    (acl2::size1 4)
                                    (acl2::i code)))))))

  (defund json-encode-weird-char (code acc)
    (declare (type (unsigned-byte 8) code))
    ;; Convert a special character into a \uXXXX sequence, where the Xes are hex
    ;; numbers for the character code.  Since the code is under 256, only two
    ;; digits are actually needed.
    (let* ((lo   (logand code #xF))
           (hi   (logand (ash code -4) #xF))
           (acc  (cons #\\ acc))
           (acc  (cons #\u acc))
           (acc  (cons #\0 acc))
           (acc  (cons #\0 acc))
           (acc  (cons (digit-to-char hi) acc))
           (acc  (cons (digit-to-char lo) acc)))
      acc))

  (local (in-theory (enable json-encode-weird-char)))

  (defthm character-listp-of-json-encode-weird-char
    (implies (character-listp acc)
             (character-listp (json-encode-weird-char x acc))))

  (local (defun test (x)
           (let* ((acc (reverse (coerce "abc " 'list)))
                  (acc (json-encode-weird-char x acc)))
             (reverse (coerce acc 'string)))))

  (local
   (progn
     (assert! (equal (test 0) "abc \\u0000"))
     (assert! (equal (test 1) "abc \\u0001"))
     (assert! (equal (test 2) "abc \\u0002"))
     (assert! (equal (test 15) "abc \\u000F"))
     (assert! (equal (test 16) "abc \\u0010"))
     (assert! (equal (test 17) "abc \\u0011"))
     (assert! (equal (test 18) "abc \\u0012"))
     (assert! (equal (test 253) "abc \\u00FD"))
     (assert! (equal (test 254) "abc \\u00FE"))
     (assert! (equal (test 255) "abc \\u00FF")))))


(defsection json-encode-char
  :parents (json-encoding)

  (definlined json-encode-char (x acc)
    (declare (type character x))
    (cond ((eql x #\\)
           (cons #\\ (cons #\\ acc)))
          ((eql x #\")
           (cons #\" (cons #\\ acc)))
          (t
           (let ((code (char-code x)))
             (declare (type (unsigned-byte 8) code))
             (if (or (<= code 31)
                     (>= code 127))
                 (json-encode-weird-char code acc)
               (cons x acc))))))

  (local (in-theory (enable json-encode-char)))

  (defthm character-listp-of-json-encode-char
    (implies (and (characterp x)
                  (character-listp acc))
             (character-listp (json-encode-char x acc)))))


(defsection json-encode-chars
  :parents (json-encoding)

  (defund json-encode-chars (x acc)
    (declare (xargs :guard (character-listp x)))
    (if (atom x)
        acc
      (let ((acc (json-encode-char (car x) acc)))
        (json-encode-chars (cdr x) acc))))

  (local (in-theory (enable json-encode-chars)))

  (defthm character-listp-of-json-encode-chars
    (implies (and (character-listp x)
                  (character-listp acc))
             (character-listp (json-encode-chars x acc)))))



(defsection json-encode-str
  :parents (json-encoding)
  :short "Fast string encoder that doesn't @(see coerce) the string into a
character list."

  (defund json-encode-str-aux (x n xl acc)
    (declare (type string x)
             (xargs :guard (and (stringp x)
                                (natp n)
                                (natp xl)
                                (<= n xl)
                                (eql xl (length x)))
                    :measure (nfix (- (nfix xl) (nfix n)))))
    (if (mbe :logic (zp (- (nfix xl) (nfix n)))
             :exec (eql n xl))
        acc
      (let ((acc (json-encode-char (char x n) acc)))
        (json-encode-str-aux x
                             (+ 1 (mbe :logic (nfix n) :exec n))
                             xl acc))))

  (local (include-book "unicode/nthcdr" :dir :system))
  (local (include-book "arithmetic/top" :dir :system))

  (local (defthm nthcdr-of-increment
           (implies (natp n)
                    (equal (nthcdr (+ 1 n) x)
                           (cdr (nthcdr n x))))
           :hints(("Goal" :in-theory (enable nthcdr)))))

  (defthm json-encode-str-aux-redef
    (implies (and (stringp x)
                  (natp n)
                  (natp xl)
                  (<= n xl)
                  (eql xl (length x)))
             (equal (json-encode-str-aux x n xl acc)
                    (json-encode-chars (nthcdr n (coerce x 'list)) acc)))
    :hints(("Goal"
            :in-theory (enable json-encode-str-aux
                               json-encode-chars)
            :induct (json-encode-str-aux x n xl acc)
            :expand (json-encode-chars (nthcdr n (coerce x 'list)) acc))))

  (definline json-encode-str (x acc)
    (declare (type string x))
    (mbe :logic (json-encode-chars (coerce x 'list) acc)
         :exec (json-encode-str-aux x 0 (length x) acc))))


(defsection json-encode-atom
  :parents (json-encoding)

  (defund json-encode-atom (x acc)
    (declare (xargs :guard (atom x)))
    (let* ((acc (cons #\" acc))
           (acc (cond ((symbolp x)
                       (json-encode-str (symbol-name x)
                                        (if (keywordp x) (cons #\: acc) acc)))
                      ((integerp x)
                       ;; We know that the digits are all valid characters so
                       ;; there's no need to encode the resulting natchars.
                       (if (< x 0)
                           (revappend (str::natchars (- x)) (cons #\- acc))
                         (revappend (str::natchars x) acc)))
                      ((characterp x)
                       (json-encode-char x acc))
                      ((stringp x)
                       (json-encode-str x acc))
                      ((acl2-numberp x)
                       ;; Don't really care about efficiency
                       (json-encode-chars (explode-atom x 10) acc))
                      (t
                       (prog2$
                        (er hard? 'json-encode-atom "Bad ACL2 object: ~x0" x)
                        acc)))))
      (cons #\" acc)))

  (local (in-theory (enable json-encode-atom)))

  (defthm character-listp-of-json-encode-atom
    (implies (and (atom x)
                  (character-listp acc))
             (character-listp (json-encode-atom x acc))))

  (local (defun test (x)
           (let* ((acc (reverse (coerce "abc " 'list)))
                  (acc (json-encode-atom x acc)))
             (reverse (coerce acc 'string)))))

  (local
   (progn
     (assert! (equal (test nil)   "abc \"NIL\""))
     (assert! (equal (test t)     "abc \"T\""))
     (assert! (equal (test 'foo)  "abc \"FOO\""))
     (assert! (equal (test :foo)  "abc \":FOO\""))
     (assert! (equal (test "foo") "abc \"foo\""))
     (assert! (equal (test #\f)   "abc \"f\""))
     (assert! (equal (test 123)   "abc \"123\""))
     (assert! (equal (test 0)     "abc \"0\""))
     (assert! (equal (test -123)  "abc \"-123\""))
     (assert! (equal (test -1/2)  "abc \"-1/2\""))
     (assert! (equal (test #c(17/2 -3/8)) "abc \"#C(17/2 -3/8)\"")))))


(defsection json-simple-alist-p
  :parents (json-encoding)
  :short "A proper alist whose every key is an atom."

  (defund json-simple-alist-p (x)
    (declare (xargs :guard t))
    (if (atom x)
        (not x)
      (and (consp (car x))
           (atom (caar x))
           (json-simple-alist-p (cdr x))))))


(defsection json-encode-main
  :parents (json-encoding)
  :short "Main function for JSON encoding."

  :long "<p>@(call json-encode) accumulates the JSON encoding of @('x') onto
@('acc').  That is, @('acc') is extended with the reverse-order characters for
@('x')'s encoding in reverse order.</p>

<p>This function <b>does not</b> necessarily produce a valid JSON object.  Per
the JSON RFC, plain JSON values other than arrays and objects are not valid
JSON text.  See @(see json-encode) instead, for a function that does something
to fix up atoms.</p>"

  (local (in-theory (enable json-simple-alist-p)))

  (definline json-comma-and-maybe-newline (acc)
    (declare (xargs :guard t))
    (if (and (consp acc)
             (or (eql (car acc) #\])
                 (eql (car acc) #\})))
        (cons #\Newline (cons #\, acc))
      (cons #\, acc)))

  (local (in-theory (enable json-comma-and-maybe-newline)))

  (mutual-recursion

   (defund json-encode-main (x acc)
     (declare (xargs :guard t
                     :guard-debug t
                     :measure (acl2::two-nats-measure (acl2-count x) 1)))
     (cond ((atom x)
            (json-encode-atom x acc))
           ((json-simple-alist-p x)
            (json-encode-simple-alist x (cons #\{ acc)))
           ((true-listp x)
            (json-encode-true-list x (cons #\[ acc)))
           (t
            (json-encode-improper-cons-list x (cons #\[ acc)))))

   (defund json-encode-simple-alist (x acc)
     (declare (xargs :guard (json-simple-alist-p x)
                     :measure (acl2::two-nats-measure (acl2-count x) 0)))
     (if (atom x)
         (cons #\} acc)
       (let* ((acc (json-encode-atom (caar x) acc))
              (acc (cons #\: acc))
              (acc (json-encode-main (cdar x) acc))
              (acc (if (consp (cdr x))
                       (json-comma-and-maybe-newline acc)
                     acc)))
         (json-encode-simple-alist (cdr x) acc))))

   (defun json-encode-true-list (x acc)
     (declare (xargs :guard (true-listp x)
                     :measure (acl2::two-nats-measure (acl2-count x) 0)))
     (if (atom x)
         (cons #\] acc)
       (let* ((acc (json-encode-main (car x) acc))
              (acc (if (consp (cdr x))
                       (json-comma-and-maybe-newline acc)
                     acc)))
         (json-encode-true-list (cdr x) acc))))

   (defun json-encode-improper-cons-list (x acc)
     (declare (xargs :guard (not (true-listp x))
                     :measure (acl2::two-nats-measure (acl2-count x) 0)))
     (if (atom x)
         (let* ((acc (json-encode-atom x acc)))
           (cons #\] acc))
       (let* ((acc (json-encode-main (car x) acc))
              (acc (json-comma-and-maybe-newline acc)))
         (json-encode-improper-cons-list (cdr x) acc)))))

  (local (include-book "str/strtok" :dir :system))

  (local (defun collapse-newlines (x)
           (string-append-lst (str::strtok x '(#\Newline)))))

  (local (defun test (x)
           (let* ((acc (reverse (coerce "abc " 'list)))
                  (acc (json-encode-main x acc)))
             (collapse-newlines
              (reverse (coerce acc 'string))))))

  ;; Same atom tests as above
  (local
   (progn
     (assert! (equal (test nil)   "abc \"NIL\""))
     (assert! (equal (test t)     "abc \"T\""))
     (assert! (equal (test 'foo)  "abc \"FOO\""))
     (assert! (equal (test :foo)  "abc \":FOO\""))
     (assert! (equal (test "foo") "abc \"foo\""))
     (assert! (equal (test #\f)   "abc \"f\""))
     (assert! (equal (test 123)   "abc \"123\""))
     (assert! (equal (test 0)     "abc \"0\""))
     (assert! (equal (test -123)  "abc \"-123\""))
     (assert! (equal (test -1/2)  "abc \"-1/2\""))
     (assert! (equal (test #c(17/2 -3/8)) "abc \"#C(17/2 -3/8)\""))))

  ;; Basic consp tests
  (local
   (progn

     (assert! (equal (test '(a . nil))   "abc [\"A\"]"))
     (assert! (equal (test '(a . b))     "abc [\"A\",\"B\"]"))
     (assert! (equal (test '(a b . nil)) "abc [\"A\",\"B\"]"))
     (assert! (equal (test '(a b . c))   "abc [\"A\",\"B\",\"C\"]"))
     (assert! (equal (test '(a b c . nil)) "abc [\"A\",\"B\",\"C\"]"))
     (assert! (equal (test '((a . b) (c . d) . e)) "abc [[\"A\",\"B\"],[\"C\",\"D\"],\"E\"]"))
     (assert! (equal (test '((a . b))) "abc {\"A\":\"B\"}"))
     (assert! (equal (test '((a . b) (c . d))) "abc {\"A\":\"B\",\"C\":\"D\"}"))

     (assert! (equal (test '(a ((1 . :foo)
                                (2 . (:foo :bar :baz))
                                (3 . ((:foo . a) (:bar . b) (:baz . c))))
                               15
                               17/2
                               . :end))
                     (concatenate 'string
                                  "abc [\"A\","
                                  "{"
                                  "\"1\":\":FOO\","
                                  "\"2\":[\":FOO\",\":BAR\",\":BAZ\"],"
                                  "\"3\":"
                                  "{"
                                  "\":FOO\":\"A\","
                                  "\":BAR\":\"B\","
                                  "\":BAZ\":\"C\""
                                  "}"
                                  "},"
                                  "\"15\","
                                  "\"17/2\","
                                  "\":END\"]")))))

  (local (include-book "tools/flag" :dir :system))

  (local (flag::make-flag flag-json-encode-main
                          json-encode-main))

  (local
   (defthm-flag-json-encode-main
     (defthm l0
       (implies (character-listp acc)
                (character-listp (json-encode-main x acc)))
       :flag json-encode-main)
     (defthm l1
       (implies (and (character-listp acc)
                     (json-simple-alist-p x))
                (character-listp (json-encode-simple-alist x acc)))
       :flag json-encode-simple-alist)
     (defthm l2
       (implies (character-listp acc)
                (character-listp (json-encode-true-list x acc)))
       :flag json-encode-true-list)
     (defthm l3
       (implies (character-listp acc)
                (character-listp (json-encode-improper-cons-list x acc)))
       :flag json-encode-improper-cons-list)
     :hints(("Goal"
             :expand ((json-encode-main x acc)
                      (json-encode-simple-alist x acc)
                      (json-encode-simple-alist nil acc)
                      (json-encode-true-list x acc)
                      (json-encode-improper-cons-list x acc))))))

  (defthm character-listp-of-json-encode-main
    (implies (character-listp acc)
             (character-listp (json-encode-main x acc)))))


(defsection json-encode
  :parents (json-encoding)
  :short "Top level wrapper for @(see json-encode-main)."

  :long "<p>@(call json-encode) encodes any ACL2 object X into a JSON
representation, which it returns as a string.</p>

<p>This wraps up the accumulator used by @(see json-encode-main) and deals with
getting the characters into the right order.</p>"

  (defund json-encode (x)
    "Gets nreverse optimization in bridge-raw.lsp"
    (let ((acc (json-encode-main x nil)))
      (reverse (coerce acc 'string))))

  (local (in-theory (enable json-encode)))

  (defthm stringp-of-json-encode-simple
    (stringp (json-encode x))
    :rule-classes :type-prescription))


