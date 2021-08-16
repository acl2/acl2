; ACL2 Bridge
; Copyright (C) 2012-2014 Centaur Technology
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

(in-package "BRIDGE")
(include-book "std/util/defines" :dir :system)
(include-book "std/strings/cat" :dir :system)
(include-book "std/strings/decimal" :dir :system)
(include-book "std/basic/two-nats-measure" :dir :system)
(local (include-book "std/strings/explode-atom" :dir :system))
(local (include-book "std/strings/strtok" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "std/testing/assert-bang" :dir :system))
(local (include-book "std/typed-lists/character-listp" :dir :system))


(defsection json-encoding
  :parents (bridge)
  :short "Simple encoder to convert ACL2 Objects into JSON Objects."

  :long "<h3>Introduction</h3>

<p>Sensibly converting ACL2 objects into JSON is not at all
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

<p>Earlier versions of the JSON grammar required top-level @('JSON-text')
instances to be either JSON Objects or Arrays.  This is no longer the case: the
latest JSON grammar allows any values at the top level.  If the object we're
given is an ordinary ACL2 atom, we just encode it as a JSON string.</p>

<p>We found this to be useful in our client code.  It's nice to create a JSON
object that says: the return value is such and so, the standard output was such
and so, and the error value was such and so.  In this context, we just want to
stitch our ACL2 object into a larger piece of JSON text, and strings are
okay.</p>")

(local (xdoc::set-default-parents json-encoding))

(define json-encode-weird-char
  :short "Convert special characters into @('\\uXXXX') sequences."
  ((code :type (unsigned-byte 8)) acc)
  :returns (new-acc character-listp :hyp (character-listp acc))
  :long "<p>This lets us properly encode weird things like control
characters.</p>

<p>BOZO we could use more readable encoding like @('\\n') and @('\\t') in some
cases.  For now we do it dumbly.</p>"

  :prepwork
  ((local (defthm crock
            (<= (acl2::loghead 4 code) 15)
            :rule-classes ((:rewrite) (:linear))
            :hints(("Goal"
                    :in-theory (disable bitops::unsigned-byte-p-of-loghead)
                    :use ((:instance bitops::unsigned-byte-p-of-loghead
                                     (bitops::size 4)
                                     (bitops::size1 4)
                                     (bitops::i code)))))))

   (local (defthm crock2
            (implies (and (integerp code)
                          (<= 0 code)
                          (< code 256))
                     (<= (acl2::logtail 4 code) 15))
            :rule-classes ((:rewrite) (:linear))
            :hints(("Goal"
                    :in-theory (disable bitops::unsigned-byte-p-of-logtail)
                    :use ((:instance bitops::unsigned-byte-p-of-logtail
                                     (bitops::size 4)
                                     (bitops::size1 4)
                                     (bitops::i code))))))))

  (b* ((lo   (logand code #xF))
       (hi   (logand (ash code -4) #xF))
       (acc  (cons #\\ acc))
       (acc  (cons #\u acc))
       (acc  (cons #\0 acc))
       (acc  (cons #\0 acc))
       (acc  (cons (digit-to-char hi) acc))
       (acc  (cons (digit-to-char lo) acc)))
    acc)
  ///
  (local (defun test (x)
           (let* ((acc (reverse (explode "abc ")))
                  (acc (json-encode-weird-char x acc)))
             (str::rchars-to-string acc))))

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


(define json-encode-char
  :parents (json-encoding)
  ((x :type character) acc)
  :returns (new-acc character-listp :hyp (and (characterp x)
                                              (character-listp acc)))
  :inline t
  (b* (((when (eql x #\\))
        (cons #\\ (cons #\\ acc)))
       ((when (eql x #\"))
        (cons #\" (cons #\\ acc)))
       ((the (unsigned-byte 8) code) (char-code x))
       ((when (or (<= code 31)
                  (>= code 127)))
        (json-encode-weird-char code acc)))
    (cons x acc)))

(define json-encode-chars ((x character-listp) acc)
  :returns (new-acc character-listp
                    :hyp (and (character-listp x)
                              (character-listp acc)))
  (b* (((when (atom x))
        acc)
       (acc (json-encode-char (car x) acc)))
    (json-encode-chars (cdr x) acc)))

(define json-encode-str-aux
  :parents (json-encode-str)
  ((x stringp :type string)
   (n natp :type (integer 0 *))
   (xl (equal xl (length x)) :type (integer 0 *))
   acc)
  :measure (nfix (- (nfix xl) (nfix n)))
  :guard (<= n xl)
  :split-types t
  (b* (((when (mbe :logic (zp (- (nfix xl) (nfix n)))
                   :exec (eql n xl)))
        acc)
       (acc (json-encode-char (char x n) acc))
       ((the (integer 0 *) n)
        (+ 1 (the (integer 0 *) (lnfix n)))))
    (json-encode-str-aux x n xl acc))
  ///
  (local (include-book "std/lists/nthcdr" :dir :system))
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
                    (json-encode-chars (nthcdr n (explode x)) acc)))
    :hints(("Goal"
            :in-theory (enable json-encode-str-aux
                               json-encode-chars)
            :induct (json-encode-str-aux x n xl acc)
            :expand (json-encode-chars (nthcdr n (explode x)) acc)))))

(define json-encode-str
  :short "Fast string encoder that doesn't @(see coerce) the string into a
character list."
  :inline t
  :enabled t
  ((x :type string) acc)
  (mbe :logic (json-encode-chars (explode x) acc)
       :exec (json-encode-str-aux x 0 (length x) acc)))


(define json-encode-atom ((x atom) acc)
  :returns (new-acc character-listp :hyp (character-listp acc))
  (let* ((acc (cons #\" acc))
         (acc (cond ((symbolp x)
                     (json-encode-str (symbol-name x)
                                      (if (keywordp x) (cons #\: acc) acc)))
                    ((integerp x)
                     ;; We know that the digits are all valid characters so
                     ;; there's no need to encode the resulting nat-to-dec-chars.
                     (if (< x 0)
                         (revappend (str::nat-to-dec-chars (- x)) (cons #\- acc))
                       (revappend (str::nat-to-dec-chars x) acc)))
                    ((characterp x)
                     (json-encode-char x acc))
                    ((stringp x)
                     (json-encode-str x acc))
                    ((acl2-numberp x)
                     ;; Don't really care about efficiency
                     (json-encode-chars (explode-atom x 10) acc))
                    (t
                     (progn$
                      (raise "Bad ACL2 object: ~x0" x)
                      acc)))))
    (cons #\" acc))
  ///
  (local (defun test (x)
           (let* ((acc (reverse (explode "abc ")))
                  (acc (json-encode-atom x acc)))
             (str::rchars-to-string acc))))

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


(define json-simple-alist-p (x)
  :short "A proper alist whose every key is an atom."
  (if (atom x)
      (not x)
    (and (consp (car x))
         (atom (caar x))
         (json-simple-alist-p (cdr x)))))

(define json-comma-and-maybe-newline (acc)
  (if (and (consp acc)
           (or (eql (car acc) #\])
               (eql (car acc) #\})))
      (cons #\Newline (cons #\, acc))
    (cons #\, acc)))

(defines json-encode-main
  :short "Main function for JSON encoding."

  :long "<p>@(call json-encode) accumulates the JSON encoding of @('x') onto
@('acc').  That is, @('acc') is extended with the reverse-order characters for
@('x')'s encoding in reverse order.</p>

<p>This function <b>does not</b> necessarily produce a valid JSON object.  Per
the JSON RFC, plain JSON values other than arrays and objects are not valid
JSON text.  See @(see json-encode) instead, for a function that does something
to fix up atoms.</p>"

  :prepwork
  ((local (in-theory (enable json-simple-alist-p
                             json-comma-and-maybe-newline))))

  (define json-encode-main ((x "Any arbitrary ACL2 object.")
                            (acc "Accumulator, characters in reverse order."))
    :flag :main
    :guard-debug t
    :measure (acl2::two-nats-measure (acl2-count x) 1)
    (cond ((atom x)
           (json-encode-atom x acc))
          ((json-simple-alist-p x)
           (json-encode-simple-alist x (cons #\{ acc)))
          ((true-listp x)
           (json-encode-true-list x (cons #\[ acc)))
          (t
           (json-encode-improper-cons-list x (cons #\[ acc)))))

  (define json-encode-simple-alist ((x json-simple-alist-p) acc)
    :flag :alist
    :measure (acl2::two-nats-measure (acl2-count x) 0)
    (b* (((when (atom x))
          (cons #\} acc))
         (acc (json-encode-atom (caar x) acc))
         (acc (cons #\: acc))
         (acc (json-encode-main (cdar x) acc))
         (acc (if (consp (cdr x))
                  (json-comma-and-maybe-newline acc)
                acc)))
      (json-encode-simple-alist (cdr x) acc)))

  (define json-encode-true-list ((x true-listp) acc)
    :flag :true-list
    :measure (acl2::two-nats-measure (acl2-count x) 0)
    (b* (((when (atom x))
          (cons #\] acc))
         (acc (json-encode-main (car x) acc))
         (acc (if (consp (cdr x))
                  (json-comma-and-maybe-newline acc)
                acc)))
      (json-encode-true-list (cdr x) acc)))

  (define json-encode-improper-cons-list ((x (not (true-listp x))) acc)
    :flag :improper
    :measure (acl2::two-nats-measure (acl2-count x) 0)
    (b* (((when (atom x))
          (let* ((acc (json-encode-atom x acc)))
            (cons #\] acc)))
         (acc (json-encode-main (car x) acc))
         (acc (json-comma-and-maybe-newline acc)))
      (json-encode-improper-cons-list (cdr x) acc)))

  ///
  (defthm-json-encode-main-flag
    (defthm character-listp-of-json-encode-main
      (implies (character-listp acc)
               (character-listp (json-encode-main x acc)))
      :flag :main)
    (defthm character-listp-of-json-encode-simple-alist
      (implies (and (character-listp acc))
               (character-listp (json-encode-simple-alist x acc)))
      :flag :alist)
    (defthm character-listp-of-json-encode-true-list
      (implies (character-listp acc)
               (character-listp (json-encode-true-list x acc)))
      :flag :true-list)
    (defthm character-listp-of-json-encode-improper-cons-list
      (implies (character-listp acc)
               (character-listp (json-encode-improper-cons-list x acc)))
      :flag :improper)))


(local
 (defsection basic-test

   (defun collapse-newlines (x)
     (string-append-lst (str::strtok x '(#\Newline))))

   (defun test (x)
     (let* ((acc (reverse (explode "abc ")))
            (acc (json-encode-main x acc)))
       (collapse-newlines
        (str::rchars-to-string acc))))

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
                                   "\":END\"]")))))))


(define json-encode
  :short "Top level wrapper for @(see json-encode-main)."
  ((x "Any ACL2 object."))
  :returns (x-json "The JSON-encoded version of @('x')."
                   stringp :rule-classes :type-prescription)
  :long "<p>This wraps up the accumulator used by @(see json-encode-main) and
deals with getting the characters into the right order.</p>"
  (let ((acc (json-encode-main x nil)))
    (str::rchars-to-string acc)))
