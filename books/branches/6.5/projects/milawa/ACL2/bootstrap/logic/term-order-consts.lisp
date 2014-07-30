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
(include-book "terms")
(%interactive)


(%autoadmit logic.fast-constant-size)

;; (defsection logic.fast-constant-size
;;   ;; BOZO make autoadmit respect :export and switch to autoadmit
;;   (%defun logic.fast-constant-size (x acc)
;;           (cond ((symbolp x) (+ 1 acc))
;;                 ((natp x) (+ x acc))
;;                 (t (logic.fast-constant-size (cdr x) (logic.fast-constant-size (car x) (+ 1 acc)))))
;;           :measure (rank x))
;;   (%auto)
;;   (%admit))

(defmacro %logic.fast-constant-size-induction (x acc)
  `(%induct (rank ,x)
            ((symbolp ,x) nil)
            ((natp ,x) nil)
            ((consp ,x)
             (((x (car ,x)) (acc (+ 1 ,acc)))
              ((x (cdr ,x)) (acc (logic.fast-constant-size (car ,x) (+ 1 ,acc))))))))

(%autoprove forcing-natp-of-logic.fast-constant-size
            (%logic.fast-constant-size-induction x acc)
            (%restrict default logic.fast-constant-size (equal x 'x)))

(%autoadmit logic.constant-size)

(%autoadmit logic.slow-constant-size)

;; (defsection logic.slow-constant-size
;;   ;; BOZO make autoadmit respect :export and switch to autoadmit
;;   (%defun logic.slow-constant-size (x)
;;           (cond ((symbolp x) 1)
;;                 ((natp x) x)
;;                 (t (+ 1 (+ (logic.slow-constant-size (car x))
;;                            (logic.slow-constant-size (cdr x))))))
;;           :measure (rank x))
;;   (%auto)
;;   (%admit))

(%autoprove natp-of-logic.slow-constant-size
            (%car-cdr-induction x)
            (%restrict default logic.slow-constant-size (equal x 'x)))

(%autoprove lemma-for-definition-of-logic.constant-size
            (%logic.fast-constant-size-induction x acc)
            (%restrict default logic.fast-constant-size (equal x 'x))
            (%restrict default logic.slow-constant-size (equal x 'x))
            (%auto)
            (%fertilize (logic.fast-constant-size x1 (+ '1 acc))
                        (+ '1 (+ acc (logic.slow-constant-size x1)))))

(defsection definition-of-logic.constant-size
  ;; NOTE: This defsection is okay and we don't want to replace it with autoprove.
  ;; The ACL2-version of this rule includes a special compatibility hack for bad
  ;; objects, and we don't need it for our Milawa rule.
  (%prove (%rule definition-of-logic.constant-size
                 :lhs (logic.constant-size x)
                 :rhs (cond ((symbolp x) 1)
                            ((natp x) x)
                            (t
                             (+ 1 (+ (logic.constant-size (car x))
                                     (logic.constant-size (cdr x))))))))
  (local (%enable default logic.constant-size))
  (local (%restrict default logic.slow-constant-size (equal x 'x)))
  (local (%enable default lemma-for-definition-of-logic.constant-size))
  (%auto)
  (%qed))

(%autoprove forcing-fast-constant-size-removal
            (%enable default logic.constant-size lemma-for-definition-of-logic.constant-size))

(%autoprove natp-of-logic.constant-size
            (%car-cdr-induction x)
            (%restrict default definition-of-logic.constant-size (equal x 'x)))




(%autoadmit logic.flag-count-constant-sizes)
(%autoadmit logic.count-constant-sizes)
(%autoadmit logic.count-constant-sizes-list)
(%autoadmit logic.slow-count-constant-sizes)

(defmacro %logic.flag-count-constant-sizes-induction (flag x acc)
  `(%induct (rank ,x)
            ((and (equal ,flag 'term)
                  (logic.constantp ,x))
             nil)
            ((and (equal flag 'term)
                  (logic.variablep ,x))
             nil)
            ((and (equal ,flag 'term)
                  (logic.functionp ,x))
             (((,flag 'list)
               (,x    (logic.function-args ,x))
               (,acc  ,acc))))
            ((and (equal ,flag 'term)
                  (logic.lambdap ,x))
             (((,flag 'list)
               (,x    (logic.lambda-actuals ,x))
               (,acc  ,acc))))
            ((and (equal ,flag 'term)
                  (not (logic.constantp ,x))
                  (not (logic.variablep ,x))
                  (not (logic.functionp ,x))
                  (not (logic.lambdap ,x)))
             nil)
            ((and (not (equal ,flag 'term))
                  (not (consp ,x)))
             nil)
            ((and (not (equal ,flag 'term))
                  (consp ,x))
             (((,flag 'term)
               (,x (car ,x))
               (acc ,acc))
              ((,flag 'list)
               (,x (cdr ,x))
               (,acc (logic.flag-count-constant-sizes 'term (car ,x) ,acc)))))))

(%autoprove forcing-natp-of-logic.flag-count-constant-sizes
            (%logic.flag-count-constant-sizes-induction flag x acc)
            (%auto :strategy (cleanup split urewrite crewrite))
            (%restrict default logic.flag-count-constant-sizes (equal x 'x)))

(%autoprove natp-of-logic.slow-count-constant-sizes
            (%logic.term-induction flag x)
            (%auto :strategy (cleanup split urewrite crewrite))
            (%restrict default logic.slow-count-constant-sizes (equal x 'x)))

(%autoprove lemma-forcing-logic.flag-count-constant-sizes-removal
            (%logic.flag-count-constant-sizes-induction flag x acc)
            (%auto :strategy (cleanup split urewrite crewrite))
            (%restrict default logic.flag-count-constant-sizes (equal x 'x))
            (%restrict default logic.slow-count-constant-sizes (equal x 'x))
            (%auto)
            (%fertilize (logic.flag-count-constant-sizes 'term x1 acc)
                        (+ acc (logic.slow-count-constant-sizes 'term x1))))

(%autoprove definition-of-logic.count-constant-sizes
            (%enable default logic.count-constant-sizes
                     logic.count-constant-sizes-list
                     lemma-forcing-logic.flag-count-constant-sizes-removal
                     )
            (%restrict default logic.slow-count-constant-sizes (equal x 'x)))

(%autoprove definition-of-logic.count-constant-sizes-list
            (%enable default logic.count-constant-sizes
                     logic.count-constant-sizes-list
                     lemma-forcing-logic.flag-count-constant-sizes-removal
                     )
            (%restrict default logic.slow-count-constant-sizes (equal x 'x)))

(%autoprove logic.flag-count-constant-sizes-removal
            (%enable default lemma-forcing-logic.flag-count-constant-sizes-removal
                             logic.count-constant-sizes
                             logic.count-constant-sizes-list)
            (%restrict default logic.slow-count-constant-sizes (equal x 'x)))

(%autoprove logic.count-constant-sizes-list-when-not-consp
            (%restrict default definition-of-logic.count-constant-sizes-list (equal x 'x)))

(%autoprove logic.count-constant-sizes-list-of-cons
            (%restrict default definition-of-logic.count-constant-sizes-list (equal x '(cons a x))))

(%autoprove lemma-for-natp-of-logic.count-constant-sizes
            (%logic.term-induction flag x)
            (%auto :strategy (cleanup split urewrite crewrite))
            (%restrict default definition-of-logic.count-constant-sizes (equal x 'x)))

(%autoprove natp-of-logic.count-constant-sizes
            (%use (%instance (%thm lemma-for-natp-of-logic.count-constant-sizes)
                             (flag 'term))))

(%autoprove natp-of-logic.count-constant-sizes-list
            (%use (%instance (%thm lemma-for-natp-of-logic.count-constant-sizes)
                             (flag 'list))))

