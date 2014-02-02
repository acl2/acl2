; VL Verilog Toolkit
; Copyright (C) 2008-2014 Centaur Technology
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
(include-book "parse-statements-def")
(include-book "parse-statements-error")
(include-book "parse-statements-progress")
(include-book "parse-statements-tokenlist")
(include-book "parse-statements-warninglist")
(include-book "parse-statements-result")
(local (include-book "../../util/arithmetic"))


(local (defthm vl-parse-event-control-value-under-iff
         ;; BOZO not sure why I suddenly need this
         (implies (and (not (mv-nth 0 (vl-parse-event-control)))
                       (force (vl-tokenlist-p tokens)))
                  (mv-nth 1 (vl-parse-event-control)))
         :hints(("Goal"
                 :in-theory (disable vl-parse-event-control-result)
                 :use ((:instance vl-parse-event-control-result))))))

(local (defthm vl-parse-delay-control-value-under-iff
         ;; BOZO not sure why I suddenly need this
         (implies (and (not (mv-nth 0 (vl-parse-delay-control)))
                       (force (vl-tokenlist-p tokens)))
                  (mv-nth 1 (vl-parse-delay-control)))
         :hints(("Goal"
                 :in-theory (disable vl-parse-delay-control-result)
                 :use ((:instance vl-parse-delay-control-result))))))

(with-output
 :off prove
 :gag-mode :goals
 (verify-guards vl-parse-statement-fn))



#|
(logic)

(local
 (encapsulate
  ()

(program)

(include-book "../lexer/lexer")


(let ((tokens (make-test-tokens "foo = bar ;")))
  (mv-let (erp val tokens)
          (vl-parse-statement tokens)
          (list (list :erp erp)
                (list :val val)
                (list :tokens tokens))))

(let ((tokens (make-test-tokens "assign foo = bar ;")))
  (mv-let (erp val tokens)
          (vl-parse-statement tokens)
          (list (list :erp erp)
                (list :val val)
                (list :tokens tokens))))

(let ((tokens (make-test-tokens "force foo = bar ;")))
  (mv-let (erp val tokens)
          (vl-parse-statement tokens)
          (list (list :erp erp)
                (list :val val)
                (list :tokens tokens))))

(let ((tokens (make-test-tokens "deassign foo ;")))
  (mv-let (erp val tokens)
          (vl-parse-statement tokens)
          (list (list :erp erp)
                (list :val val)
                (list :tokens tokens))))

(let ((tokens (make-test-tokens "release foo ;")))
  (mv-let (erp val tokens)
          (vl-parse-statement tokens)
          (list (list :erp erp)
                (list :val val)
                (list :tokens tokens))))

(let ((tokens (make-test-tokens "begin end")))
  (mv-let (erp val tokens)
          (vl-parse-statement tokens)
          (list (list :erp erp)
                (list :val val)
                (list :tokens tokens))))

(let ((tokens (make-test-tokens "(* taco = delicious *) begin end")))
  (mv-let (erp val tokens)
          (vl-parse-statement tokens)
          (list (list :erp erp)
                (list :val val)
                (list :tokens tokens))))

(let ((tokens (make-test-tokens "begin deassign foo ; end")))
  (mv-let (erp val tokens)
          (vl-parse-statement tokens)
          (list (list :erp erp)
                (list :val val)
                (list :tokens tokens))))

(let ((tokens (make-test-tokens "begin foo = bar ; end")))
  (mv-let (erp val tokens)
          (vl-parse-statement tokens)
          (list (list :erp erp)
                (list :val val)
                (list :tokens tokens))))


(defmacro test-parse-integer-declaration (&key input atts names arrdims initvals (successp 't))
    `(assert! (let ((tokens (make-test-tokens ,input)))
                (mv-let (erp val tokens)
                        (vl-parse-integer-declaration ',atts tokens)
                        (declare (ignore tokens))
                        (if erp
                            (prog2$ (cw "ERP is ~x0.~%" erp)
                                    (not ,successp))
                          (prog2$ (cw "VAL is ~x0.~%" val)
                                  (and ,successp
                                       (test-vardecls-fn val :vl-integer ',atts
                                                         ',names ',arrdims ',initvals))))))))
|#