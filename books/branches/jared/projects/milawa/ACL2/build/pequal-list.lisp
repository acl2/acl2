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
(include-book "prop-list")
(include-book "pequal")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)

(dd.open "pequal-list.tex")

(defund build.reflexivity-list (x)
  ;; BOZO update the defderiv table with the axiom?
  (declare (xargs :guard (logic.term-listp x)))
  (if (consp x)
      (cons (build.reflexivity (car x))
            (build.reflexivity-list (cdr x)))
    nil))

(defobligations build.reflexivity-list
  (build.reflexivity))

(encapsulate
 ()
 (local (in-theory (enable build.reflexivity-list)))

 (defthm forcing-logic.appeal-listp-of-build.reflexivity-list
   (implies (force (logic.term-listp x))
            (equal (logic.appeal-listp (build.reflexivity-list x))
                   t)))

 (defthm forcing-logic.strip-conclusions-of-build.reflexivity-list
   (implies (force (logic.term-listp x))
            (equal (logic.strip-conclusions (build.reflexivity-list x))
                   (logic.pequal-list x x))))

 (defthm@ forcing-logic.proof-listp-of-build.reflexivity-list
   (implies (force (and (logic.term-listp x)
                        (logic.term-list-atblp x atbl)
                        (@obligations build.reflexivity-list)))
            (equal (logic.proof-listp (build.reflexivity-list x) axioms thms atbl)
                   t))))



(defund build.pequal-by-args (f as)
  ;; Derive (f t1 ... tn) = (f s1 ... sn) from t1 = s1, ..., tn = sn.
  (declare (xargs :guard (and (logic.function-namep f)
                              (logic.appeal-listp as)
                              (logic.all-atomicp (logic.strip-conclusions as)))
                  :guard-hints (("Goal" :in-theory (enable logic.functional-axiom)))))
  (let* ((conclusions (logic.strip-conclusions as)) ;; (t1 = s1, ..., tn = sn)
         (t*          (logic.=lhses conclusions))   ;; (t1, ..., tn)
         (s*          (logic.=rhses conclusions)))  ;; (s1, ..., sn)
    (cond ((equal t* s*)
           ;; Optimization.  We can just use reflexivity.
           (build.reflexivity (logic.function f t*)))
          (t
           ;; Otherwise, take the functional equality axiom,
           ;;    t1 = s1 -> ... -> tn = sn -> (f t1 ... tn) = (f s1 ... sn),
           ;; and apply repeated modus ponens.
           (build.modus-ponens-list (logic.pequal (logic.function f t*) (logic.function f s*))
                                    as
                                    (build.functional-equality f t* s*))))))

(defobligations build.pequal-by-args
  (build.reflexivity build.modus-ponens-list build.functional-equality))

(encapsulate
 ()
 (local (in-theory (enable logic.functional-axiom build.pequal-by-args)))

 (defthm forcing-build.pequal-by-args-under-iff
   (iff (build.pequal-by-args f as)
        t))

 (defthm forcing-logic.appealp-of-build.pequal-by-args
   (implies (force (and (logic.function-namep f)
                        (logic.appeal-listp as)
                        (logic.all-atomicp (logic.strip-conclusions as))))
            (equal (logic.appealp (build.pequal-by-args f as))
                   t)))

 (defthm forcing-logic.conclusion-of-build.pequal-by-args
   (implies (force (and (logic.function-namep f)
                        (logic.appeal-listp as)
                        (logic.all-atomicp (logic.strip-conclusions as))))
            (equal (logic.conclusion (build.pequal-by-args f as))
                   (logic.pequal (logic.function f (logic.=lhses (logic.strip-conclusions as)))
                                 (logic.function f (logic.=rhses (logic.strip-conclusions as))))))
   :rule-classes ((:rewrite :backchain-limit-lst 0)))

 (defthm@ forcing-logic.proofp-of-build.pequal-by-args
   (implies (force (and (logic.function-namep f)
                        (logic.appeal-listp as)
                        (logic.all-atomicp (logic.strip-conclusions as))
                        (logic.proof-listp as axioms thms atbl)
                        (equal (len as) (cdr (lookup f atbl)))
                        (@obligations build.pequal-by-args)))
            (equal (logic.proofp (build.pequal-by-args f as) axioms thms atbl)
                   t))))



(defund build.disjoined-pequal-by-args (f p as)
  ;; Derive P v (f t1 ... tn) = (f s1 ... sn) from P v t1 = s1, ..., P v tn = sn
  (declare (xargs :guard (and (logic.function-namep f)
                              (logic.formulap p)
                              (logic.appeal-listp as)
                              (let ((aconcs (logic.strip-conclusions as)))
                                (and (logic.all-disjunctionsp aconcs)
                                     (all-equalp p (logic.vlhses aconcs))
                                     (logic.all-atomicp (logic.vrhses aconcs)))))
                  :guard-hints(("Goal" :in-theory (enable logic.functional-axiom)))))
  (let* ((ti=si* (logic.vrhses (logic.strip-conclusions as)))  ;; (t1 = s1, ..., tn = sn)
         (t*     (logic.=lhses ti=si*))                        ;; (t1, ..., tn)
         (s*     (logic.=rhses ti=si*)))                       ;; (s1, ..., sn)
     (cond ((equal t* s*)
            ;; Optimization.  We can just use reflexivity and expansion.
            (build.expansion P (build.reflexivity (logic.function f t*))))
           (t
            ;; Otherwise, take the functional equality axiom,
            ;;    t1 = s1 -> ... -> tn = sn -> (f t1 ... tn) = (f s1 ... sn),
            ;; expand it with P,
            ;;    P v t1 = s1 -> ... -> tn = sn -> (f t1 ... tn) = (f s1 ... sn),
            ;; and apply repeated disjoined modus ponens.
            (build.disjoined-modus-ponens-list (logic.pequal (logic.function f t*) (logic.function f s*))
                                               as
                                               (build.expansion p (build.functional-equality f t* s*)))))))

(defobligations build.disjoined-pequal-by-args
  (build.expansion build.reflexivity build.disjoined-modus-ponens-list build.functional-equality))

(encapsulate
 ()
 (local (in-theory (enable logic.functional-axiom build.disjoined-pequal-by-args)))

 (defthm forcing-build.disjoined-pequal-by-args-under-iff
   (iff (build.disjoined-pequal-by-args f p as)
        t))

 (defthm forcing-logic.appealp-of-build.disjoined-pequal-by-args
   (implies (force (and (logic.function-namep f)
                        (logic.formulap p)
                        (logic.appeal-listp as)
                        (logic.all-disjunctionsp (logic.strip-conclusions as))
                        (all-equalp p (logic.vlhses (logic.strip-conclusions as)))
                        (logic.all-atomicp (logic.vrhses (logic.strip-conclusions as)))))
            (equal (logic.appealp (build.disjoined-pequal-by-args f p as))
                   t)))

 (defthm forcing-logic.conclusion-of-build.disjoined-pequal-by-args
   (implies (force (and (logic.function-namep f)
                        (logic.formulap p)
                        (logic.appeal-listp as)
                        (logic.all-disjunctionsp (logic.strip-conclusions as))
                        (all-equalp p (logic.vlhses (logic.strip-conclusions as)))
                        (logic.all-atomicp (logic.vrhses (logic.strip-conclusions as)))))
            (equal (logic.conclusion (build.disjoined-pequal-by-args f p as))
                   (logic.por p (logic.pequal (logic.function f (logic.=lhses (logic.vrhses (logic.strip-conclusions as))))
                                              (logic.function f (logic.=rhses (logic.vrhses (logic.strip-conclusions as))))))))
   :rule-classes ((:rewrite :backchain-limit-lst 0)))

 (defthm@ forcing-logic.proofp-of-build.disjoined-pequal-by-args
   (implies (force (and (logic.function-namep f)
                        (logic.formulap p)
                        (logic.appeal-listp as)
                        (logic.all-disjunctionsp (logic.strip-conclusions as))
                        (all-equalp p (logic.vlhses (logic.strip-conclusions as)))
                        (logic.all-atomicp (logic.vrhses (logic.strip-conclusions as)))
                        (logic.formula-atblp p atbl)
                        (logic.proof-listp as axioms thms atbl)
                        (equal (cdr (lookup f atbl)) (len as))
                        (@obligations build.disjoined-pequal-by-args)))
            (equal (logic.proofp (build.disjoined-pequal-by-args f p as) axioms thms atbl)
                   t))))

(dd.close)