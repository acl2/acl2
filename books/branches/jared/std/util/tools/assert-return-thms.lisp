; CUTIL - Centaur Basic Utilities
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
; Modified by David Rager <ragerdl@cs.utexas.edu>

(in-package "ACL2")
(include-book "std/util/define" :dir :system)
(include-book "tools/defconsts" :dir :system)
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
       (append (str::natchars x) acc)))

(assert-return-thms foo)

(foo 1 "foo" :acc nil))

(foo 2 "foo" :acc nil))
|#
