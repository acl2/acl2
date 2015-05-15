; SVEX - Symbolic, Vector-Level Hardware Description Library
; Copyright (C) 2014 Centaur Technology
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
; Original author: Sol Swords <sswords@centtech.com>

(in-package "GL")
(include-book "centaur/gl/symbolic-arithmetic" :dir :system)
(include-book "tools/templates" :dir :system)
(local (include-book "centaur/misc/arith-equivs" :dir :system))
(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "centaur/gl/arith-lemmas" :dir :system))

;; Goal: a more or less complete set of functions for doing arithmetic
;; on a symbolic bitvector representation consisting of lists of AIGs.

;; We almost already have this with gl/symbolic-arithmetic.  Frustratingly, we
;; can't quite reuse it because it does its computations in terms of BFRs,
;; i.e., it will do AIG or BDD operations depending on the current attachment
;; to bfr-mode.  But we need to be able to do these with AIGs even in the midst
;; of a GL BDD proof -- unfortunate.

;; In order to reuse the formulations & proofs we've already done in
;; symbolic-arithmetic, this book uses a hack -- in symbolic-arithmetic, we
;; record in a table the defsymbolic events that we use to create these
;; bfr-based functions and their correctness proofs.  We then replicate the
;; events here, basically replacing occurrences of "BFR-" with "AIG-".  Very
;; ugly, but, we hope, effective.


(defmacro sv::aig-sterm (x) `(gl::bfr-sterm ,x))
(defmacro sv::aig-scons (x y) `(gl::bfr-scons ,x ,y))
(defmacro sv::aig-ucons (x y) `(gl::bfr-ucons ,x ,y))

(defun sv::aig-list->s (x env)
  (declare (xargs :guard t))
  (b* (((mv first rest end) (first/rest/end x)))
    (if end
        (bool->sign (sv::aig-eval first env))
      (logcons (sv::bool->bit (sv::aig-eval first env))
               (sv::aig-list->s rest env)))))

(defun sv::aig-list->u (x env)
  (declare (xargs :guard t))
  (if (atom x)
      0
    (logcons (sv::bool->bit (sv::aig-eval (car x) env))
             (sv::aig-list->u (cdr x) env))))

(defun defsymbolic-formals-pair-with-evals-aig (x)
  (if (atom x)
      nil
    (cons (cons (caar x)
                (case (cadar x)
                  (n `(nfix ,(caar x)))
                  (i `(ifix ,(caar x)))
                  (p `(acl2::pos-fix ,(caar x)))
                  (b `(sv::aig-eval ,(caar x) env))
                  (u `(sv::aig-list->u ,(caar x) env))
                  (s `(sv::aig-list->s ,(caar x) env))))
          (defsymbolic-formals-pair-with-evals-aig (cdr x)))))

(defun defsymbolic-return-specs-aig (x formal-evals)
  (if (atom x)
      nil
    (append (case (cadar x)
              ((n i p) (and (third (car x))
                            `((equal ,(caar x)
                                     ,(sublis formal-evals (third (car x)))))))
              (b `((equal (sv::aig-eval ,(caar x) env)
                          ,(sublis formal-evals (third (car x))))))
              (u `((equal (sv::aig-list->u ,(caar x) env)
                          ,(sublis formal-evals (third (car x))))))
              (s `((equal (sv::aig-list->s ,(caar x) env)
                          ,(sublis formal-evals (third (car x)))))))
            (defsymbolic-return-specs-aig (cdr x) formal-evals))))

(defmacro sv::aig-and* (&rest args)
  (xxxjoin 'sv::aig-and args))

(defmacro sv::aig-or* (&rest args)
  (xxxjoin 'sv::aig-or args))

(table bfr-aig-subst nil
       '((bfr-list->u . sv::aig-list->u)
         (bfr-ite-fn . sv::aig-ite)
         (bfr-list->s . sv::aig-list->s)
         (bfr-eval . sv::aig-eval)
         (bfr-binary-and . sv::aig-and)
         (bfr-binary-or . sv::aig-or)
         (bfr-not . sv::aig-not)
         (bfr-xor . sv::aig-xor)
         (bfr-iff . sv::aig-iff))
       :clear)

(defun bfr-aig-functional-subst (world)
  (let ((alist (table-alist 'bfr-aig-subst world)))
    (pairlis$ (strip-cars alist) (pairlis$ (strip-cdrs alist) nil))))

(local #!acl2
       (defthm aig-ite-of-const-conditions
         (and (equal (aig-ite t y z) y)
              (equal (aig-ite nil y z) z))
         :hints(("Goal" :in-theory (enable aig-ite aig-and aig-or aig-not)))))

(local (def-ruleset defsymbolic-aig-functions nil))

(defun defsymbolic-aig-fn (name args subst)
  (declare (xargs :mode :program))
  (b* (((mv & args)
        (acl2::template-subst-rec args
                                  (acl2::make-tmplsubst :atoms subst
                                                        :strs '(("BFR" "AIG" . sv::pkg))
                                                        :pkg-sym 'sv::pkg)))
       ((mv kwd-alist other-kws other-args)
        (extract-some-keywords
         '(:spec :returns :correct-hints :depends-hints :correct-hyp :abstract) args nil))
       ((unless (eql (len other-args) 2))
        (er hard? 'defsymbolic-fn "Need formals and body in addition to keyword args"))
       (formals (car other-args))
       (body (cadr other-args))
       (returns (cdr (assoc :returns kwd-alist)))
       ((unless (consp returns))
        (er hard? 'defsymbolic-aig-fn "Need a returns list"))
       (returns (if (eq (car returns) 'mv)
                    (cdr returns)
                  (list returns)))
       (- (defsymbolic-check-formals formals))
       (- (defsymbolic-check-returns returns))
       ((when (intersectp-eq (strip-cars formals)
                             (strip-cars returns)))
        (er hard? 'defsymbolic-aig-fn "Formals and returns overlap"))
       (return-binder (if (consp (cdr returns))
                          `(mv . ,(strip-cars returns))
                        (caar returns)))
       (formal-vars (strip-cars formals))
       (exec-name (acl2::tmpl-sym-sublis '(("BFR" "AIG" . sv::pkg)) name 'sv::pkg))
       (abstractp (std::getarg :abstract nil kwd-alist))
       (old-exec-name (if abstractp
                          (intern-in-package-of-symbol
                           (concatenate 'string (symbol-name name) "-EXEC")
                           name)
                        name))
       (old-correct (intern-in-package-of-symbol
                     (concatenate 'string (symbol-name old-exec-name) "-CORRECT")
                     old-exec-name)))
    `(progn
       (define ,exec-name ,(defsymbolic-define-formals formals)
         ,@other-kws
         :returns ,(defsymbolic-define-returns returns)
         :progn t
         ,body
         ///
         (table bfr-aig-subst ',old-exec-name ',exec-name)

         (defthm ,(intern-in-package-of-symbol
                   (concatenate 'string (symbol-name exec-name) "-CORRECT")
                   exec-name)
           (b* ((,return-binder (,exec-name . ,formal-vars)))
             ,(let ((concl `(and . ,(defsymbolic-return-specs-aig returns
                                      (defsymbolic-formals-pair-with-evals-aig formals))))
                    (correct-hyp (cdr (assoc :correct-hyp kwd-alist))))
                (if correct-hyp
                    `(implies ,correct-hyp ,concl)
                  concl)))
           :hints ((let ((subst (bfr-aig-functional-subst world)))
                     `(:use ((:functional-instance
                              ,',old-correct
                              (bfr-mode (lambda () t))
                              . ,subst))))
                   (and stable-under-simplificationp
                        '(:in-theory (enable* defsymbolic-aig-functions
                                              sv::aig-list->s
                                              sv::aig-list->u))))))
       (local (in-theory (disable ,exec-name)))
       (local (add-to-ruleset defsymbolic-aig-functions ,exec-name)))))

(defun defsymbolic-aig-table-events (table acc subst)
  (declare (xargs :mode :program))
  (if (atom table)
      acc
    (defsymbolic-aig-table-events (cdr table)
      (cons (defsymbolic-aig-fn (caar table) (cdar table) subst) acc)
      subst)))

(defmacro sv::aig-ite-bvv (c v1 v0)
  `(let ((sv::aig-ite-bvv-test ,c))
     (if sv::aig-ite-bvv-test
         (if (eq sv::aig-ite-bvv-test t)
             ,v1
           (sv::aig-ite-bvv-fn sv::aig-ite-bvv-test ,v1 ,v0))
       ,v0)))

(defmacro sv::aig-ite-bss (c v1 v0)
  `(let ((sv::aig-ite-bss-test ,c))
     (if sv::aig-ite-bss-test
         (if (eq sv::aig-ite-bss-test t)
             ,v1
           (sv::aig-ite-bss-fn sv::aig-ite-bss-test ,v1 ,v0))
       ,v0)))


(local (defmacro no-op-event (&rest args)
         (declare (ignore args))
         '(progn)))

(local (in-theory (e/d* (bitops::ihsext-redefs
                         bitops::ihsext-inductions))))


(local (defthm integer-length-bound-s-correct-aig
         (< (integer-length (sv::aig-list->s x env))
            (integer-length-bound-s x))
         :hints(("Goal" :in-theory (enable integer-length-bound-s)))
         :rule-classes :linear))

(defthm integer-length-bound-s-correct-aig
  (< (integer-length (sv::aig-list->s x env))
     (integer-length-bound-s x))
  :hints(("Goal" :in-theory (enable integer-length-bound-s)))
  :rule-classes :linear)

(defmacro sv::aig-ite* (x y z)
  (cond ((and (or (quotep y) (atom y))
              (or (quotep z) (atom z)))
         `(sv::aig-ite ,x ,y ,z))
        (t
         `(mbe :logic (sv::aig-ite ,x ,y ,z)
               :exec (let ((sv::aig-ite-x-do-not-use-elsewhere ,x))
                       (cond
                        ((eq sv::aig-ite-x-do-not-use-elsewhere nil) ,z)
                        ((eq sv::aig-ite-x-do-not-use-elsewhere t) ,y)
                        (t
                         (sv::aig-ite sv::aig-ite-x-do-not-use-elsewhere
                                        ,y ,z))))))))

(encapsulate nil
  (make-event
   (cons 'progn
         (defsymbolic-aig-table-events
           (table-alist 'defsymbolic-forms (w state)) nil
           '((bfr-list->u . sv::aig-list->u)
             (bfr-ite-fn . sv::aig-ite)
             (bfr-ite . sv::aig-ite*)
             (bfr-list->s . sv::aig-list->s)
             (bfr-eval . sv::aig-eval)
             (bfr-binary-and . sv::aig-and)
             (bfr-binary-or . sv::aig-or)
             (bfr-and . sv::aig-and*)
             (bfr-or . sv::aig-or*)
             (bfr-not . sv::aig-not)
             (bfr-xor . sv::aig-xor)
             (bfr-iff . sv::aig-iff)
             (add-bfr-pat . no-op-event))))))
