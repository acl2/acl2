; Standard Utilities Library
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

(in-package "STD")
(include-book "../define")
(include-book "utils")
(include-book "std/testing/assert" :dir :system)
(include-book "std/testing/eval" :dir :system)

(define foo ()
  :returns (ans integerp)
  3)

(assert-disabled foo)
(assert-guard-verified foo)

(define foo2 ()
  :enabled t
  (mv 3 "hi"))

(assert-enabled foo2)
(assert-guard-verified foo2)

(define foo3 ()
  (mv 3 "hi"))

(define foo4 ()
  :returns (ans integerp)
  44)

(assert! (equal (defguts->name (cdr (assoc 'foo4 (get-define-guts-alist (w state)))))
                'foo4))

(define foo5 ((x oddp :type integer))
  :returns (ans integerp :hyp :guard)
  (- x 1))

(assert-guard-verified foo5)

(define foo6 ((x oddp :type (integer 0 *)))
  :returns (ans natp :hyp :guard)
  (- x 1))

(define foo7
  :parents (|look ma, parents before formals, even!|)
  (x)
  (consp x))

(assert-guard-verified foo7)

(encapsulate
  ()
  (logic)
  (define foo8 (x)
    :mode :program
    (+ 1 x)))

(encapsulate
  ()
  (logic)
  (define foo9 (x)
    (declare (xargs :mode :program))
    (+ 2 x)))

(encapsulate
  ()
  (program)
  (define foo10 ((x natp))
    (declare (xargs :mode :logic))
    (+ 2 x))
  (assert-guard-verified foo10))

(encapsulate
  ()
  (program)
  (define foo11 (x)
    (declare (xargs :mode :program))
    (+ 3 x)))

(encapsulate
  ()
  (program)
  (define foo12 (x)
    :mode :program
    (+ 3 x)))




(encapsulate
  ()
  (logic)
  (define bar8 (x &optional y)
    :mode :program
    (+ 1 x y)))

(encapsulate
  ()
  (logic)
  (define bar9 (x &optional y)
    (declare (xargs :mode :program))
    (+ 2 x y)))

(encapsulate
  ()
  (program)
  (define bar10 ((x natp) &optional (y natp))
    (declare (xargs :mode :logic))
    (+ 2 x y)))

(encapsulate
  ()
  (program)
  (define bar11 (x &optional y)
    (declare (xargs :mode :program))
    (+ 3 x y)))

(encapsulate
  ()
  (program)
  (define bar12 (x &optional y)
    :mode :program
    (+ 3 x y)))




(define m0 (x)
  (consp x))

(assert-guard-verified m0)

(assert! (let ((topic (xdoc::find-topic 'm0 (xdoc::get-xdoc-table (w state)))))
           (not topic)))

(xdoc::set-default-parents foo bar)

(define m1 (x)
  (consp x))

(assert! (let ((topic (xdoc::find-topic 'm1 (xdoc::get-xdoc-table (w state)))))
           (and topic
                (equal (cdr (assoc :parents topic))
                       '(foo bar)))))

(define m2 (x)
  (consp x)
  :parents (bar))

(assert! (let ((topic (xdoc::find-topic 'm2 (xdoc::get-xdoc-table (w state)))))
           (and topic
                (equal (cdr (assoc :parents topic))
                       '(bar)))))

(define m3 (x)
  (consp x)
  :parents nil)

(assert! (let ((topic (xdoc::find-topic 'm3 (xdoc::get-xdoc-table (w state)))))
           (not topic)))








; Test case from bug reported in Issue 270:

(defsection foo
  :short "foo bar")

(define check0 (x)
  :non-executable t
  :returns (mv (a natp) (b natp))
  (mv (nfix x) (1+ (nfix x))))

(define check1 (x)
  :non-executable t
  :returns (mv (a natp) (b natp))
  :short "testing"
  (mv (nfix x) (1+ (nfix x))))

(define check2 (x)
  :non-executable t
  :returns (mv (a natp) (b natp))
  :short "testing"
  (mv (nfix x) (1+ (nfix x))))



;; Testing new doc fragment stuff.

(define frags (x)
  (if (atom x)
      1
    (+ 1 (frags (cdr x))))
  ///
  "<p>This would be better written as a type-prescription rule:</p>"
  (defthm posp-of-frags
    (posp (frags x)))
  "<p>But this would not make a good type prescription rule:</p>"
  (defthm frags-of-cons
    (equal (frags (cons a x)) (+ 1 (frags x)))))

(assert-guard-verified frags)



;; tests of evaluation of short/long strings

(define test-shortcat (x)
  :short (concatenate 'string "Test of evaluation of " "short strings for define.")
  x)

(assert! (stringp (cdr (assoc :short (xdoc::find-topic 'test-shortcat (xdoc::get-xdoc-table (w state)))))))

(define test-longcat (x)
  :long (concatenate 'string "Test of evaluation of " "long strings for define.")
  x)

(assert! (stringp (cdr (assoc :long (xdoc::find-topic 'test-longcat (xdoc::get-xdoc-table (w state)))))))



; Testing of fancy RET binder.


(define mathstuff ((a natp)
                   (b natp))
  :returns (mv (sum natp :rule-classes :type-prescription)
               (prod natp :rule-classes :type-prescription))
  (b* ((a (nfix a))
       (b (nfix b)))
    (mv (+ a b)
        (* a b))))

(assert-guard-verified mathstuff)

;; (def-b*-binder mathstuff-ret
;;   :decls
;;   ((declare (xargs :guard (and (eql (len forms) 1)
;;                                (consp (car forms))
;;                                (symbolp (caar forms))))))
;;   :body
;;   (patbind-ret-fn '((sum . nil) (prod . nil))
;;                   '(a b)
;;                   args forms rest-expr))

(define do-math-stuff ((a natp)
                       (b natp))
  (b* ((a (nfix a))
       (b (nfix b))
       ((ret stuff) (mathstuff a b)))
    (list :sum stuff.sum
          :prod stuff.prod))
  ///
  (assert! (equal (do-math-stuff 1 2) (list :sum 3 :prod 2))))



(defstobj foost (foo-x))

(defstobj barst (bar-x) :congruent-to foost)

(define modify-foo (x &key (foost 'foost))
  :returns (foo-out)
  (update-foo-x x foost))

;; (def-b*-binder modify-foo-ret
;;   :decls
;;   ((declare (xargs :guard (and (eql (len forms) 1)
;;                                (consp (car forms))
;;                                (symbolp (caar forms))))))
;;   :body
;;   (patbind-ret-fn '((foo . foo))
;;                   '(x &key (foo 'foo))
;;                   args forms rest-expr))

(define use-bar (x barst)
  (b* (((ret) (modify-foo x :foost barst)))
    barst))



;; Test of return value arity checking (Issue 365)

(must-fail
 (define rva-1 (x)
   :returns (mv a b)
   x))

(must-fail
 (define rva-2 (x)
   :returns ans
   (mv x x)))

(must-fail
 (define rva-3 (x state)
   :returns state
   (mv x state)))

(must-fail
 (define rva-4 (x state)
   :returns (mv a b c)
   (mv x state)))

(define rva-5 (x)
  :non-executable t
  :returns (mv a b c)
  x)

(define rva-6 (x)
  :non-executable t
  :returns ans
  (mv x x x))


(must-fail
 (define rvap-1 (x)
   :returns (mv a b)
   :mode :program
   x))

(must-fail
 (define rvap-2 (x)
   :returns ans
   :mode :program
   (mv x x)))

(must-fail
 (define rvap-3 (x state)
   :returns state
   :mode :program
   (mv x state)))

(must-fail
 (define rvap-4 (x state)
   :returns (mv a b c)
   :mode :program
   (mv x state)))




;; Basic testing of hook installation/removal

(defun my-hook (guts opts state)
  (declare (xargs :mode :program :stobjs state))
  (declare (ignore guts opts))
  (value '(value-triple :invisible)))

(defun my-hook2 (guts opts state)
  (declare (xargs :mode :program :stobjs state))
  (declare (ignore guts opts))
  (value '(value-triple :invisible)))

(assert! (not (get-post-define-hooks-alist (w state))))
(add-post-define-hook :foo my-hook)
(assert! (equal (get-post-define-hooks-alist (w state)) '((:foo . my-hook))))
(add-post-define-hook :bar my-hook2)
(assert! (equal (get-post-define-hooks-alist (w state)) '((:bar . my-hook2)
                                                          (:foo . my-hook))))
(remove-post-define-hook :foo)
(assert! (equal (get-post-define-hooks-alist (w state)) '((:bar . my-hook2))))
(add-post-define-hook :foo my-hook)
(assert! (equal (get-post-define-hooks-alist (w state)) '((:foo . my-hook)
                                                          (:bar . my-hook2))))

(assert! (let ((guts (make-defguts :name 'myfun)))
           (equal (post-hook-make-events '(:foo (:bar 3) (:foo 5))
                                         (get-post-define-hooks-alist (w state))
                                         guts)
                  `((make-event (my-hook ',guts 'nil state))
                    (make-event (my-hook2 ',guts '(3) state))
                    (make-event (my-hook ',guts '(5) state))))))


(assert! (not (get-default-post-define-hooks (w state))))
(add-default-post-define-hook :bar)
(assert! (equal (get-default-post-define-hooks (w state))
                '((:bar . NIL))))
(add-default-post-define-hook :foo 3)
(assert! (equal (get-default-post-define-hooks (w state))
                '((:foo . (3))
                  (:bar))))
(remove-default-post-define-hook :bar)
(assert! (equal (get-default-post-define-hooks (w state))
                '((:foo . (3)))))
(remove-default-post-define-hook :foo)
(assert! (not (get-default-post-define-hooks (w state))))


(remove-post-define-hook :foo)
(remove-post-define-hook :bar)
(assert! (not (get-post-define-hooks-alist (w state))))




(defun my-hook-1 (guts opts state)
  ;; Trivial, stupid hook test.
  ;; To test user-defined options, opts is expected to have a hyp for the theorem.
  (declare (xargs :mode :program :stobjs state))
  (b* (((defguts guts) guts)
       (mksym-package-symbol guts.name)
       (- (cw "My-hook-1: Proving dumb theorem about ~x0.~%" guts.name))
       ((unless (tuplep 1 opts))
        (er soft 'my-hook-1 "Expected a single option (a hyp for the theorem), but got: ~x0." opts))
       (hyp (first opts))
       (event `(defthm ,(mksym guts.name '-silly-thm)
                 (implies ,hyp
                          (equal (,guts.name-fn . ,guts.raw-formals)
                                 (,guts.name-fn . ,guts.raw-formals)))
                 :rule-classes nil)))
    (value event)))

(add-post-define-hook :silly my-hook-1)

(define hooktest1 (x)
  :hooks ((:silly (consp a)))
  x
  :verbosep nil)

(encapsulate
  ()
  (set-enforce-redundancy t)
  (defthm hooktest1-silly-thm
    (implies (consp a)
             (equal (hooktest1 x) (hooktest1 x)))
    :rule-classes nil))

(define hooktest2 (x)
  :hooks ((:silly t))
  x
  :verbosep nil)

(encapsulate
  ()
  (set-enforce-redundancy t)
  (defthm hooktest2-silly-thm
    (implies t
             (equal (hooktest2 x) (hooktest2 x)))
    :rule-classes nil))

(add-default-post-define-hook :silly (integerp b))

(define hooktest3 (x) x)

(encapsulate
  ()
  (set-enforce-redundancy t)
  (defthm hooktest3-silly-thm
    (implies (integerp b)
             (equal (hooktest3 x) (hooktest3 x)))
    :rule-classes nil))

(define hooktest4 (x)
  ;; Make sure we can defeat default hooks
  :hooks nil
  x)

(assert! (acl2::logical-namep 'hooktest3-silly-thm (w state)))
(assert! (not (acl2::logical-namep 'hooktest4-silly-thm (w state))))

(define my-make-alist (keys)
  :returns (alist alistp)
  (if (atom keys)
      nil
    (cons (cons (car keys) nil)
          (my-make-alist (cdr keys))))
  ///
  (more-returns
   (alist true-listp :rule-classes :type-prescription)
   (alist (equal (len alist) (len keys))
          :name len-of-my-make-alist)))

(local (in-theory (enable my-make-alist)))

(include-book "std/lists/list-fix" :dir :system)

(more-returns my-make-alist
  (alist (equal (strip-cars alist) (list-fix keys))
         :name strip-cars-of-my-make-alist))



(define my-make-alist-and-len (keys)
  :returns (mv (len natp :rule-classes :type-prescription)
               (alist alistp))
  (b* (((when (atom keys))
        (mv 0 nil))
       ((mv cdr-len cdr-alist) (my-make-alist-and-len (cdr keys))))
    (mv (+ 1 cdr-len)
        (cons (cons (car keys) nil) cdr-alist)))
  ///
  (more-returns
   (len (equal len (len keys))
        :name my-make-alist-and-len.len-removal)
   (alist (integer-listp (strip-cars alist))
          :hyp (integer-listp keys)
          :name integer-listp-strip-cars-my-make-alist-and-len)
   (alist true-listp :rule-classes :type-prescription)))

(remove-default-post-define-hook :silly)


(define inline-test (x)
  :inline t
  x)

(define notinline-test (x)
  :inline nil
  x)

(assert! (equal (inline-test$inline 1) 1))
(assert! (equal (inline-test 1) 1))

(assert! (equal (notinline-test$notinline 2) 2))
(assert! (equal (notinline-test 2) 2))



;; Alessandro Coglio reported a bug to do with giving hints when using :t-proof.
;; The following is a modified version of his example.  Previously, ac-g2 failed
;; basically because it ended up generating multiple hints xargs:
;;
;;      (DEFUND AC-G2 (X)
;;        (DECLARE (XARGS :HINTS (("Goal" :IN-THEORY (ENABLE AC-F)))))
;;        (DECLARE (XARGS :HINTS ('(:BY ACL2::AC-G2-T))
;;                                 :VERIFY-GUARDS NIL))
;;         ...
;;
;; Now we work harder to try to sensibly extract :hints from the xargs and the
;; top-level keywords for use in the t-proof.

(defund ac-f (x) (- x 1))

; Matt K.: Avoid ACL2(p) error in ac-g1 below pertaining to override hints.
(local (set-waterfall-parallelism nil))

(define ac-g1 (x)
  :verify-guards nil
  :t-proof t
  :hints (("Goal" :in-theory (enable ac-f)))
  (if (zp x)
      nil
    (ac-g1 (ac-f x))))

(assert-guard-unverified ac-g1)

(define ac-g2 (x)
  :verify-guards nil
  :t-proof t
  :verbosep t
  (declare (xargs :hints (("Goal" :in-theory (enable ac-f)))))
  (if (zp x)
      nil
    (ac-g2 (ac-f x))))

(assert-guard-unverified ac-g2)

(define another-guard-test-1 (x)
  (declare (type integer x))
  x)

(define another-guard-test-2 ((x integerp))
  x)

(define another-guard-test-3 ((x :type integer))
  x)

(define another-guard-test-4 (x)
  (declare (xargs :guard (integerp x)))
  x)

(define another-guard-test-5 (x state)
  (declare (xargs :stobjs state))
  (declare (ignorable state))
  x)

(define another-guard-test-6 (x state)
  (declare (ignorable state))
  x)

;; Should be able to :PE these functions and see that no (declare (xargs :guard
;; t)) are added except for 5/6 (stobjs aren't good enough to trigger guard
;; verif.)
(assert-guard-verified another-guard-test-1)
(assert-guard-verified another-guard-test-2)
(assert-guard-verified another-guard-test-3)
(assert-guard-verified another-guard-test-4)
(assert-guard-verified another-guard-test-5)
(assert-guard-verified another-guard-test-6)

;; [Shilpi] Added some basic config and :after-returns related tests below.

(make-define-config
 :inline t
 :no-function t)

(define inline-and-no-function ((x natp))
  :returns (new-x natp :hyp :guard)
  (+ x 54))

(define not-inline-and-no-function ((x natp))
  ;; config object's :inline directive overridden.
  :inline nil
  :returns (new-x natp :hyp :guard)
  (+ x 54))

(make-define-config :inline t :no-function nil
                    :ruler-extenders (cons)
                    :verify-guards :after-returns)

(define guards-after-ret ((x natp))
  :returns (ret natp :hyp :guard)
  (+ x 54)
  ///
  (defret natp-of-qux-alt
    (implies (and (integerp x) (<= -54 x))
             (natp ret))))
