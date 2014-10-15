; Milawa - A Reflective Theorem Prover
; Copyright (C) 2005-2009 Kookamara LLC
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

(in-package "MILAWA")




(defthmd bust-up-logic.function-args-expensive
  (implies (and (ACL2::syntaxp (logic.constantp x))
                (consp x))
           (equal (equal x (logic.function-args y))
                  (and (consp (logic.function-args y))
                       (equal (car x) (car (logic.function-args y)))
                       (equal (cdr x) (cdr (logic.function-args y))))))
  :hints(("Goal" :in-theory (disable FORCING-TRUE-LISTP-OF-LOGIC.FUNCTION-ARGS))))

(defthmd bust-up-cdr-of-logic.function-args-expensive
  (implies (and (ACL2::syntaxp (logic.constantp x))
                (consp x))
           (equal (equal x (cdr (logic.function-args y)))
                  (and (consp (cdr (logic.function-args y)))
                       (equal (car x) (car (cdr (logic.function-args y))))
                       (equal (cdr x) (cdr (cdr (logic.function-args y))))))))

(defthmd bust-up-cdr-of-cdr-of-logic.function-args-expensive
  (implies (and (ACL2::syntaxp (logic.constantp x))
                (consp x))
           (equal (equal x (cdr (cdr (logic.function-args y))))
                  (and (consp (cdr (cdr (logic.function-args y))))
                       (equal (car x) (car (cdr (cdr (logic.function-args y)))))
                       (equal (cdr x) (cdr (cdr (cdr (logic.function-args y)))))))))

(%autoprove bust-up-logic.function-args-expensive (%forcingp nil))
(%autoprove bust-up-cdr-of-logic.function-args-expensive (%forcingp nil))
(%autoprove bust-up-cdr-of-cdr-of-logic.function-args-expensive (%forcingp nil))



;; (DEFTHM CDR-OF-CDR-UNDER-IFF-WHEN-TRUE-LISTP-WITH-LEN-FREE-alt
;;   (IMPLIES (AND (EQUAL n (lEN X))
;;                 (SYNTAXP (ACL2::QUOTEP N))
;;                 (TRUE-LISTP X))
;;            (IFF (CDR (CDR X)) (< 2 N))))

;; (%autoprove CDR-OF-CDR-UNDER-IFF-WHEN-TRUE-LISTP-WITH-LEN-FREE-alt
;;             (%use (%instance (%thm CDR-OF-CDR-UNDER-IFF-WHEN-TRUE-LISTP-WITH-LEN-FREE))))

;; (DEFTHM LOGIC.FUNCTION-ARGS-UNDER-IFF-WITH-LEN-FREE-alt
;;   (IMPLIES (AND (EQUAL N (LEN (LOGIC.FUNCTION-ARGS TERM)))
;;                 (SYNTAXP (ACL2::QUOTEP N))
;;                 (< 0 N))
;;            (IFF (LOGIC.FUNCTION-ARGS TERM) T)))

;; (%autoprove LOGIC.FUNCTION-ARGS-UNDER-IFF-WITH-LEN-FREE-alt)

;; (DEFTHM CDR-OF-CDR-OF-CDR-UNDER-IFF-WHEN-TRUE-LISTP-WITH-LEN-FREE-alt
;;   (IMPLIES (AND (EQUAL n (LEN X))
;;                 (SYNTAXP (ACL2::QUOTEP N))
;;                 (TRUE-LISTP X))
;;            (IFF (CDR (CDR (CDR X))) (< 3 N))))

;; (%autoprove CDR-OF-CDR-OF-CDR-UNDER-IFF-WHEN-TRUE-LISTP-WITH-LEN-FREE-alt
;;             (%use (%instance (%thm CDR-OF-CDR-OF-CDR-UNDER-IFF-WHEN-TRUE-LISTP-WITH-LEN-FREE))))





(defthm logic.term-list-atblp-of-cons-gross
  (implies (ACL2::syntaxp (logic.constantp x))
           (equal (logic.term-list-atblp x atbl)
                  (if (consp x)
                      (and (logic.term-atblp (car x) atbl)
                           (logic.term-list-atblp (cdr x) atbl))
                    t))))

(%autoprove logic.term-list-atblp-of-cons-gross)



(defthm logic.sigma-atblp-of-cons-gross
  (implies (ACL2::syntaxp (logic.constantp x))
           (equal (logic.sigma-atblp x atbl)
                  (if (consp x)
                      (and (consp (car x))
                           (logic.variablep (car (car x)))
                           (logic.term-atblp (cdr (car x)) atbl)
                           (logic.sigma-atblp (cdr x) atbl))
                      t))))

(%autoprove logic.sigma-atblp-of-cons-gross)



(defsection logic.substitute-list-of-cons-gross
  ;; This rule fixes a problem that comes up when we run into terms of the form
  ;; (logic.substitute-list '(x y) ...).  Here, our cons rule does not fire
  ;; because our patmatch code does not allow it do.  We should probably fix
  ;; our pattern matcher in the long run, but for now we can emulate it in a
  ;; kind of gross way using a syntactic restriction.
  (%prove (%rule logic.substitute-list-of-cons-gross
                 :hyps (list (%hyp (consp x)))
                 :lhs (logic.substitute-list x sigma)
                 :rhs (cons (logic.substitute (car x) sigma)
                            (logic.substitute-list (cdr x) sigma))
                 :syntax ((logic.constantp x))))
  (%auto)
  (%qed)
  (%enable default logic.substitute-list-of-cons-gross))

