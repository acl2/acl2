; VL Verilog Toolkit
; Copyright (C) 2008-2014 Centaur Technology
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

(in-package "VL")

(include-book "centaur/fty/deftypes" :dir :system)
(include-book "std/util/deflist" :dir :system)
(include-book "std/strings/cat" :dir :system)

(defxdoc vl-printedlist
  :parents (printer)
  :short "A list of strings/characters to print in reverse order."
  :long "<p>Useful for formatting a long string to print.  Also the basis of
the @(see ps) printer-state stobj.</p>")



(define vl-printed-p (x)
  :parents (vl-printedlist)
  :short "Recognize a printed object (string or character)."
  (or (characterp x)
      (stringp x))
  ///
  (defthm vl-printed-p-cr
    (equal (vl-printed-p x)
           (or (characterp x)
               (stringp x)))
    :rule-classes :compound-recognizer
    :hints(("Goal" :in-theory (enable vl-printed-p))))

  (defthm vl-printed-p-by-backchaining
    (implies (or (characterp x)
                 (stringp x))
             (vl-printed-p x))))

(define vl-printed-fix
  :parents (vl-printed-p)
  :short "Fixing function for @(see vl-printed-p) objects."
  ((x vl-printed-p))
  :returns (x-fix vl-printed-p)
  :inline t
  (mbe :logic (if (vl-printed-p x)
                  x
                "")
       :exec x)
  ///
  (defthm vl-printed-fix-when-vl-printed-p
    (implies (vl-printed-p x)
             (equal (vl-printed-fix x)
                    x))))

(fty::deffixtype vl-printed
  :pred vl-printed-p
  :fix vl-printed-fix
  :equiv vl-printed-equiv
  :define t
  :forward t)

(fty::deflist vl-printedlist
  :elt-type vl-printed-p)

(defsection vl-printedlist-p
  :parents (vl-printedlist)
  :short "Recognizer for mixed lists of strings and characters."
  (defthm vl-printedlist-p-when-character-listp
    (implies (character-listp x)
             (vl-printedlist-p x)))

  (defthm vl-printedlist-p-when-string-listp
    (implies (string-listp x)
             (vl-printedlist-p x)))

  (defthm vl-printedlist-p-of-make-list-ac
    (implies (and (vl-printed-p x)
                  (force (vl-printedlist-p y)))
             (vl-printedlist-p (make-list-ac n x y))))

  (defthm vl-printedlist-p-of-revappend-chars
    (implies (vl-printedlist-p acc)
             (vl-printedlist-p (str::revappend-chars x acc)))
    :hints(("Goal" :in-theory (enable str::revappend-chars)))))


(define vl-printedlist-length ((x vl-printedlist-p)
                               (acc natp))
  :returns (len natp :rule-classes :type-prescription)
  :parents (vl-printedlist-p)
  :short "Compute the total length of the list, in characters."
  :long "<p>This is different than ordinary @(see len) because any strings
within the list may have their own lengths.</p>"
  (b* (((when (atom x))
        (lnfix acc))
       (x1   (vl-printed-fix (car x)))
       (len1 (if (characterp x1)
                 1
               (length x1))))
    (vl-printedlist-length (cdr x) (+ len1 (lnfix acc)))))



(define vl-printedlist-peek
  ((x vl-printedlist-p "The printed list, which we assume is in reverse order!"))
  :returns (maybe-char (or (not maybe-char)
                           (characterp maybe-char))
                       :rule-classes :type-prescription)
  :parents (vl-printedlist-p)
  :short "Extract the last character that was printed."
  :long "<p>This is generally useful for things like <i>insert a space unless
we just printed a newline</i>, etc.</p>"
  (and (consp x)
       (let ((x1 (vl-printed-fix (car x))))
         (if (characterp x1)
             x1
           (let ((len (length x1)))
             (if (zp len)
                 ;; Degenerate case where we printed an empty string, look
                 ;; further.
                 (vl-printedlist-peek (cdr x))
               (char x1 (1- len))))))))

(define vl-printedlist->chars ((x vl-printedlist-p)
                               acc)
  :returns (chars character-listp :hyp (character-listp acc))
  :parents (vl-ps->chars)
  :short "Convert a printed list (in reverse order) into characters (in proper
  order)."

  (b* (((when (atom x))
        acc)
       (x1 (vl-printed-fix (car x)))
       ((when (characterp x1))
        ;; Prefer to test characterp instead of stringp, since characters are
        ;; immediates in CCL.
        (vl-printedlist->chars (cdr x) (cons x1 acc))))
    ;; Subtle: the printedlist are in reverse order, but the strings within it are
    ;; in proper order, so we need to use append-chars instead of
    ;; revappend-chars here.
    (vl-printedlist->chars (cdr x) (str::append-chars x1 acc))))

(define vl-printedlist->string ((x vl-printedlist-p))
  :returns (str stringp :rule-classes :type-prescription)
  :parents (vl-printedlist)
  :short "@('(vl-printedlist->string)') returns the printed characters as a
string in the proper, non-reversed, printed order."
  :long "<p>This is logically just @('(implode (vl-printedlist->chars))'), but we
install a more efficient definition under the hood in raw Lisp.</p>"
  (implode (vl-printedlist->chars x nil))
  ///
  (defttag vl-optimize)
  (progn!
   (set-raw-mode t)

   (defun vl-printedlist->string (x)

     ;; Optimized PS->STRING routine.  We're going to build the return string in
     ;; two passes.  In the first pass we'll determine how big of an array we
     ;; need.  In the second, we'll fill in its characters with the reverse of
     ;; the elems.

     (let* ((size  (vl-printedlist-length x 0)))
       (unless (typep size 'fixnum)
         (er hard? 'vl-ps->string-fn
             "Printed list will will be longer than a fixnum (~x0).  You don't ~
            actually want to turn it into a string, I think." size))

       ;; Since the elems are in reverse order, we'll work backwards from the end
       ;; of the array.
       (let* ((ret (make-array size :element-type 'character))
              (i   (the fixnum (- (the fixnum size) 1))))
         (declare (type fixnum i))
         (loop while (consp x)
               do
               (let ((elem (car x)))
                 (if (characterp elem)
                     (progn (setf (schar ret i) elem)
                            (decf i))

                   ;; For strings, things are trickier because the characters of
                   ;; the string *are* in the right order.  It's very helpful to
                   ;; think of a concrete example.  Suppose we do:
                   ;;
                   ;;   print #\A
                   ;;   print #\B
                   ;;   print #\C
                   ;;   print "abc"
                   ;;   print #\D
                   ;;   print #\E
                   ;;
                   ;; Then the rchars we'll have are (#\E #\D "abc" #\C #\B #\A).
                   ;; The ret array is 8 entries long and we've already set
                   ;;   ret[7] = #\E
                   ;;   ret[6] = #\D
                   ;; So we now want to set
                   ;;   ret[5] = #\c
                   ;;   ret[4] = #\b
                   ;;   ret[3] = #\a
                   ;;
                   ;; I think it's easiest to just go down from the end of the
                   ;; string so we can (decf i) like before.
                   (loop for j fixnum from (- (length (the string elem)) 1) downto 0 do
                         (setf (schar ret i) (schar elem j))
                         (decf i))))
               (setq x (cdr x)))
         ret))))
  (defttag nil))

