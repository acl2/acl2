; Making a function non-tail-recursive
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; This book is about converting a general (terminating) tail-recursive
;; function to be head-recursive.  To do so, this tool defines a separate
;; function that counts how many iterations the original function will perform
;; on the given input.  Then it runs the head-recursive version that many
;; steps.

;fixme use verify-termination?
(defun symbol-name-lst-logic-mode (lst)
  (declare (xargs :guard (symbol-listp lst)))
  (cond ((endp lst) nil)
        (t (cons (symbol-name (car lst))
                 (symbol-name-lst-logic-mode (cdr lst))))))

(defun concat-symbols-fn (symbols)
  (declare (xargs :guard (symbol-listp symbols)))
  (intern (string-append-lst (symbol-name-lst-logic-mode symbols))
          "ACL2"))

;fixme use pack?
(defmacro concat-symbols (&rest symbols)
  `(concat-symbols-fn (list ,@symbols)))

;TODO: uncomment but avoid name clashes:
;; (encapsulate
;;  (((exit-test *) => *)
;;   ((base-val *) => *)
;;   ((update *) => *)
;;   ((measure *) => *))
;;  ;;FIXME do the new, head recursive functions need to be added to the signature?
;;  (local (defund exit-test (x) (endp x)))
;;  (local (defund update (x) (cdr x)))
;;  (local (defund measure (x) (len x)))
;;  (local (defund base-val (x) x))

;;  ;;these are the constraints
;;  (defthm measure-decreases
;;    (implies (not (exit-test x))
;;             (o< (measure (update x)) (measure x)))
;;    :hints (("Goal" :in-theory (enable measure exit-test update))))

;;  (defthm measure-o-p
;;    (o-p (measure x))
;;    :hints (("Goal" :in-theory (enable measure))))

;;  ;; a general tail recursive function (of one parameter)
;;  ;; can we use the lambda trick to extend this result to functions of more than one parameter?
;;  (defun foo (x)
;;    (declare (xargs :measure (measure x) ))
;;    (if (exit-test x)
;;        (base-val x) ;bad name?
;;      (foo (update x))))

;;  ;;head recursive
;;  ;;or should this be tail recursive so we can introduce it using defpun?
;;  ;;i guess if foo terminates, then so does this...
;;  (defun reps-until-exit-test (x)
;;    (declare (xargs :measure (measure x)))
;;    (if (exit-test x)
;;        0
;;      (+ 1 (reps-until-exit-test (update x)))))

;;  (defthm reps-until-exit-test-of-update
;;    (implies (not (exit-test x))
;;             (equal (reps-until-exit-test (update x))
;;                    (+ -1  (reps-until-exit-test x))))
;;    :hints (("Goal" :in-theory (enable reps-until-exit-test))))

;;  (defthm exit-test-when-no-more-reps
;;    (iff (equal (reps-until-exit-test x) 0)
;;         (exit-test x))
;;    :hints (("Goal" :in-theory (enable reps-until-exit-test))))

;;  (defthm reps-when-exit
;;    (implies (exit-test x)
;;             (equal (reps-until-exit-test x)
;;                    0))
;;    :hints (("Goal" :in-theory (enable reps-until-exit-test))))

;;  ;;head recursive version of the function:
;;  (defun foo-head-aux (reps x)
;;    (if (zp reps)
;;        x
;;      (update (foo-head-aux (+ -1 reps) x))))

;;  (defun foo-head (x)
;;    (let ((reps (reps-until-exit-test x)))
;;      (base-val (foo-head-aux reps x))))

;;  (defthmd foo-head-peel-off
;;    (implies (not (zp reps))
;;             (equal (foo-head-aux reps x)
;;                    (foo-head-aux (+ -1 reps) (update x))
;;                    ))
;;    :hints (("Goal" :induct t)))

;;  (local
;;   (defthm arith-hack
;;     (implies (integerp x)
;;              (equal (+ -1 1 x)
;;                     x))))

;; ;goal theorem to export:

;;  (defthmd foo-becomes-foo-head
;;    (equal (foo x)
;;           (foo-head x))
;;    :hints (("Subgoal *1/2" :use (:instance foo-head-peel-off (reps (reps-until-exit-test x))))
;;            ("Goal" :do-not '(generalize eliminate-destructors)
;;             :expand (foo-head-aux 0 x)
;;             :in-theory (disable (:definition foo-head-aux)))))

;;  )
;;end encapsulate

(defun convert-to-head-recursive-events (original-function-name
                                         exit-test-function-name
                                         measure-function-name
                                         update-function-name
                                         base-val-function-name
                                         reps-hints)
  (declare (ignore base-val-function-name))
  (let* ((head-function-name (concat-symbols original-function-name '-head))
         (reps-function-name (concat-symbols original-function-name '-reps))
         (aux-function-name (concat-symbols head-function-name '-aux))
         )
    `(
      ;;head recursive
      ;;or should this be tail recursive so we can introduce it using defpun?
      ;;i guess if foo terminates, then so does this...
      (skip-proofs ;fixme remove skip-proofs
       (defun ,reps-function-name (x)
         (declare (xargs :measure (,measure-function-name x)
                         :hints ,reps-hints
                         ))
         (if (,exit-test-function-name x)
             0
           (+ 1 (,reps-function-name (,update-function-name x))))))

      ;this loops with the -when-not-exit theorem
      (defthmd ,(concat-symbols reps-function-name '-of-update)
        (implies (not (,exit-test-function-name x))
                 (equal (,reps-function-name (,update-function-name x))
                        (+ -1 (,reps-function-name x))))
        :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                                                   '(,reps-function-name)))))

      (defthm ,(concat-symbols exit-test-function-name '-when-no-more-reps)
        (iff (equal (,reps-function-name x) 0)
             (,exit-test-function-name x))
        :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                                                   '(,reps-function-name
                                                     (:type-prescription ,reps-function-name)
                                                     NATP-MEANS-NON-NEG)))))

      (defthm ,(concat-symbols reps-function-name '-when-exit)
        (implies (,exit-test-function-name x)
                 (equal (,reps-function-name x)
                        0))
        :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                                                   '(,reps-function-name)))))

      (defthm ,(concat-symbols reps-function-name '-when-not-exit)
        (implies (not (,exit-test-function-name x))
                 (equal (,reps-function-name x)
                        (+ 1
                           (,reps-function-name (,update-function-name x)))))
        :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                                                   '(,reps-function-name)))))

      ;;head recursive
      (defun ,aux-function-name (reps x)
        (if (zp reps)
            x
          (,update-function-name (,aux-function-name (+ -1 reps) x))))

      (defun ,head-function-name (x)
        (let ((reps (,reps-function-name x)))
;;          (,base-val-function-name (,aux-function-name reps x))
          (,aux-function-name reps x)))

      ;;new
      (defthm ,(concat-symbols aux-function-name '-base-case)
        (implies (zp reps)
                 (equal (,aux-function-name reps x)
                        x)))

      (defthmd ,(concat-symbols head-function-name '-peel-off)
        (implies (not (zp reps))
                 (equal (,aux-function-name reps x)
                        (,aux-function-name (+ -1 reps) (,update-function-name x))
                        ))
        :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                                                   '(,aux-function-name))
                 :induct t)))

;drop?
      (local
       (defthm arith-hack
         (implies (integerp x)
                  (equal (+ -1 1 x)
                         x))))

;goal theorem to export:

      (defthmd ,(concat-symbols original-function-name '-becomes- head-function-name)
        (equal (,original-function-name x)
               (,head-function-name x))
        :hints (("Subgoal *1/2" :use (:instance ,(concat-symbols head-function-name '-peel-off) (reps (,reps-function-name x))))
                ("Goal" :do-not '(generalize eliminate-destructors)
                 :expand (,aux-function-name 0 x)
                 ;;                  :in-theory (e/d (,original-function-name) ((:definition ,aux-function-name)))
                 :induct (,reps-function-name X)
                 :in-theory (union-theories (theory 'minimal-theory)
                                            '(arith-hack
                                              zp
                                              ,aux-function-name
                                              ,original-function-name
                                              ,reps-function-name
                                              ,head-function-name
                                              (:type-prescription ,reps-function-name)))))))))

;right now, this is for a unary function only
;this seems pretty restrictive...
(defmacro convert-to-head-recursive (original-function-name
                                     exit-test-function-name
                                     measure-function-name
                                     update-function-name
                                     base-val-function-name
                                     &key (reps-hints 'nil)
                                     )
  `(progn ,@(convert-to-head-recursive-events original-function-name exit-test-function-name measure-function-name update-function-name base-val-function-name reps-hints)))
