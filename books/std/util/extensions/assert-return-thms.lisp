; ACL2 Standard Library
; Copyright (c) 2008-2015 Centaur Technology
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
; Modified by David Rager <ragerdl@cs.utexas.edu>

(in-package "ACL2")
(include-book "std/util/define" :dir :system)
(include-book "std/util/defconsts" :dir :system)
(include-book "tools/advise" :dir :system)

#!STD
(defun returnspeclist->return-types (x)
  (declare (xargs :mode :program))
  (if (atom x)
      nil
    (cons (returnspec->return-type (car x))
          (returnspeclist->return-types (cdr x)))))


(defun bind-to-nth-values (retnames n)
  (declare (xargs :mode :program))
  (if (atom retnames)
      nil
    (cons (list (car retnames) `(nth ,n acl2::values))
          (bind-to-nth-values (cdr retnames) (+ 1 n)))))

(defun assert-return-advice (fn info)
  ;; Generates the advise we want to give.
  (declare (xargs :mode :program))
  (b* ((__function__ 'assert-return-advice)
       (returns  (cdr (assoc :returns info)))
       (retnames (std::returnspeclist->names returns))
       (rettypes (std::returnspeclist->return-types returns))
       (assertion (cons 'and rettypes))
       ((when (atom retnames))
        (raise "No :returns for ~x0~%" fn)))
    `(let ,(bind-to-nth-values retnames 0)
       (or ,assertion
           (cw "Assertion for ~x0 failed!~%" ',fn)
           (break$)))))

(defmacro assert-return-thms (fn)
  `(b* ((__function__ 'assert-return-thms)
        (fn ',fn)
        (info (cdr (assoc fn (std::get-defines (w state)))))
        ((unless info)
         (raise "No define info for ~x0~%" fn))
        (real-fn (cdr (assoc :fn info)))
        (advice  (assert-return-advice fn info)))
     (advise$ real-fn advice :when :after)))

#|
(local (include-book
        "str/top" :dir :system))

(program)

(define foo ((x natp :type integer)
              (y stringp)
              &key
              (acc character-listp))
   :returns (mv (new-x oddp :hyp :fguard)
                (y stringp :rule-classes :type-prescription)
                (acc "Extended with X."
                     (character-listp acc)
                     :hyp :fguard))
   :mode :program
   (mv x
       (mbe :logic (if (stringp y) y "")
            :exec y)
       (append (str::nat-to-dec-chars x) acc)))

(assert-return-thms foo)

(foo 1 "foo" :acc nil))

(foo 2 "foo" :acc nil))
|#
