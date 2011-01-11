; Safe-Case Macro
; Copyright (C) 2008-2010 Centaur Technology
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

(in-package "ACL2")

(defmacro safe-case (&rest l)
  ":Doc-Section Case
   Error-checking alternative to `case'.~/
   ~c[;; (include-book \"tools/safe-case\" :dir :system)] ~/
   ~c[Safe-case] is a drop-in replacement for ~il[case], and is logically identical
   to ~c[case].  The only difference is during execution.  When ~c[case] is used and
   none of the cases match, the answer is ~c[nil]:
   ~bv[]
   ACL2 !> (case 3
             (1 'one)
             (2 'two))
   NIL
   ~ev[]

   But when ~c[safe-case] is used and none of the cases match, the result is an
   error:
   ~bv[]
   ACL2 !> (safe-case (+ 0 3)
             (1 'one)
             (2 'two))

   HARD ACL2 ERROR in SAFE-CASE:  No case matched:
   (SAFE-CASE (+ 0 3) (1 'ONE) (2 'TWO)).  Test was 3.
   ~ev[]"
  (declare (xargs :guard (and (consp l)
                              (legal-case-clausesp (cdr l)))))
  (let* ((clauses (cdr l))
         (tests   (strip-cars clauses)))
    (if (or (member t tests)
            (member 'otherwise tests))
        `(case ,@l)
      `(case ,@l
         (otherwise
          (er hard? 'safe-case "No case matched: ~x0.  Test was ~x1.~%"
              '(safe-case ,@l) ,(car l)))))))
