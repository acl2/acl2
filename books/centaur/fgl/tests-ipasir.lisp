; FGL - A Symbolic Simulation Framework for ACL2
; Copyright (C) 2019 Centaur Technology
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

(in-package "FGL")

(include-book "top")

(include-book "centaur/ipasir/ipasir-backend" :dir :system)
(include-book "std/testing/eval" :dir :system)
(value-triple (acl2::tshell-ensure))


(defun 32* (x y)
  (logand (* x y) (1- (expt 2 32))))

(defun fast-logcount-32* (v)
  (let* ((v (- v (logand (ash v -1) #x55545555)))
         (v (+ (logand v #x33333333)
               (logand (ash v -2) #x33333333))))
    (ash (32* (logand (+ v (ash v -4))
                      #xF0F0F0F)
              #x1010101)
         -24)))

(make-event
 (b* (((mv err ?val state)
       (fgl-thm
        :hyp t
        :concl
        ;; (if (unsigned-byte-p 32 x)
        (b* ((x (loghead 32 xx))
             (impl (fast-logcount-32* x))
             (spec (logcount x))
             (eq (equal impl spec))
             (params  (make-fgl-ipasir-config))
             (?uneq-sat (fgl-sat-check params (not eq))))
          (show-counterexample params "unequal"))))
      ((unless err)
       (er soft 'ctrex-test "Expected this to fail!~%")))
   (value '(value-triple :ok))))

(make-event
 (b* (((mv err ?val state)
       (fgl-thm
        :hyp (unsigned-byte-p 32 x)
        :concl
        ;; (if (unsigned-byte-p 32 x)
        (b* (;; (x (loghead 32 xx))
             (impl (fast-logcount-32* x))
             (spec (logcount x))
             (eq (equal impl spec)))
          (fgl-sat-check/print-counterexample
           (make-fgl-ipasir-config) "unequal" (not eq)))))
      ((unless err)
       (er soft 'ctrex-test "Expected this to fail!~%")))
   (value '(value-triple :ok))))



(define pythag-triple-p ((x natp) (y natp) (z natp))
  (and (< 0 (lnfix x))
       (<= (lnfix x) (lnfix y))
       (equal (* (lnfix z) (lnfix z))
              (+ (* (lnfix x) (lnfix x))
                 (* (lnfix y) (lnfix y))))))



(def-fgl-program find-all-pythag-triples (x y z found found-cond)
  (b* ((cond (narrow-equiv '(iff)
                           (and (not found-cond)
                                (pythag-triple-p x y z))))
       (config  (make-fgl-ipasir-config))
       (sat-res (fgl-sat-check config cond))
       (unsat (syntax-interp (not sat-res)))
       ((when unsat)
        found)
       ((list (list error bindings ?vars) &)
        (syntax-interp (show-counterexample-bind config interp-st state)))
       ((when error)
        (cw "Error: ~x0~%" error))
       (xval (cdr (assoc 'x bindings)))
       (yval (cdr (assoc 'y bindings)))
       (zval (cdr (assoc 'z bindings)))
       (list (list xval yval zval))
       ((unless (and (pythag-triple-p xval yval zval)
                     (not (member-equal list found))))
        (fgl-prog2 (syntax-interp (cw "Bad: result: ~x0 found: ~x1~%" list found))
                   nil)))
    (find-all-pythag-triples x y z (cons list found) (or (and (equal x xval)
                                                              (equal y yval)
                                                              (equal z zval))
                                                         found-cond))))

(fgl-thm
 :hyp (and (unsigned-byte-p 7 x)
           (unsigned-byte-p 7 y)
           (unsigned-byte-p 7 z))
 :concl (fgl-prog2 (b* ((trips (find-all-pythag-triples x y z nil nil)))
                     (fgl-prog2 (syntax-interp
                                 (let ((interp-st 'interp-st))
                                   (interp-st-put-user-scratch :pythag-triples trips interp-st)))
                                ;; (add-scratch-pair :pythag-triples trips)
                                (cw "trips: ~x0~%" trips)))
                   t))

(make-event
 (b* ((trips (g-concrete->val (cdr (hons-get :pythag-triples (interp-st->user-scratch interp-st))))))
   `(def-fgl-thm 7-bit-pythag-trips
      :hyp (and (unsigned-byte-p 7 x)
                (unsigned-byte-p 7 y)
                (unsigned-byte-p 7 z))
      :concl (implies (not (member-equal (list x y z) ',trips))
                      (not (pythag-triple-p x y z))))))


(def-fgl-program find-all-satisfying-inputs (input condition accumulator unseen-cond)
   (b* ((cond (narrow-equiv '(iff) (and unseen-cond condition)))
        (config (make-fgl-ipasir-config))
        (sat-res (fgl-sat-check config cond))
        (unsat (syntax-interp (eq sat-res nil)))
        ((when unsat) accumulator)
        ((mv err input-val) (syntax-interp (get-counterexample-value input config interp-st state)))
        ((when err) (fgl-prog2 (cw "Error: ~x0~%" err) accumulator))
        (accumulator (cons input-val accumulator))
        (unseen-cond (and (not (equal input input-val)) unseen-cond)))
     (find-all-satisfying-inputs input condition accumulator unseen-cond)))

;; (def-fgl-program add-scratch-pair (key val)
;;   (syntax-interp
;;    (interp-st-put-user-scratch key val interp-st)))

;; (fancy-ev-add-primitive interp-st->user-scratch$inline t)
;; (fancy-ev-add-primitive interp-st-put-user-scratch t)
;; (def-fancy-ev-primitives mine)

(fgl-thm
 :hyp (and (unsigned-byte-p 7 x)
           (unsigned-byte-p 7 y)
           (unsigned-byte-p 7 z))
 :concl (b* ((input (list x y z))
             (test (pythag-triple-p x y z)))
          (fgl-prog2 (b* ((trips (find-all-satisfying-inputs input test nil t)))
                       (fgl-prog2 (syntax-interp
                                   (let ((interp-st 'interp-st))
                                     (interp-st-put-user-scratch :pythag-triples trips interp-st)))
                                  ;; (add-scratch-pair :pythag-triples trips)
                                  (cw "trips: ~x0~%" trips)))
                   t)))

(make-event
 (b* ((trips (g-concrete->val (cdr (hons-get :pythag-triples (interp-st->user-scratch interp-st))))))
   `(def-fgl-thm 7-bit-pythag-trips2
      :hyp (and (unsigned-byte-p 7 x)
                (unsigned-byte-p 7 y)
                (unsigned-byte-p 7 z))
      :concl (implies (not (member-equal (list x y z) ',trips))
                      (not (pythag-triple-p x y z))))))





;; (skip-proofs
;; (define enumerate-pythag-trips ((n :type (unsigned-byte 27)) (found-acc))
;;   :measure (nfix (- (ash 1 27) (nfix n)))
;;   (b* (((when (mbe :logic (zp (- (ash 1 27) (nfix n)))
;;                    :exec (eql n (ash 1 27)))) found-acc)
;;        (x (logand #x1ff n))
;;        (y (logand #x1ff (ash n -9)))
;;        (z (logand #x1ff (ash n -18)))
;;        (found-acc (if (pythag-triple-p x y z)
;;                       (cons (list x y z) found-acc)
;;                     found-acc)))
;;     (enumerate-pythag-trips (1+ (lnfix n)) found-acc))))


;; (fgl-thm
;;  :hyp (and (unsigned-byte-p 12 x)
;;            (unsigned-byte-p 12 y)
;;            (unsigned-byte-p 12 z))
;;  :concl (fgl-prog2 (b* ((trips (find-all-pythag-triples x y z nil)))
;;                      (fgl-prog2 (syntax-interp
;;                                  (let ((interp-st 'interp-st))
;;                                    (interp-st-put-user-scratch :pythag-triples trips interp-st)))
;;                                 ;; (add-scratch-pair :pythag-triples trips)
;;                                 (cw "trips: ~x0~%" trips)))
;;                    t))




(include-book "greedy-max-sat")

(include-book "centaur/bitops/merge" :dir :system)

(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "centaur/bitops/equal-by-logbitp" :dir :system))

(defun make-buggy-paddb-lanes (n)
  (if (zp n)
      nil
    (let ((n (1- n)))
      (cons `(let ((x1 (acl2::nth-slice8 ,n x))
                   (y1 (acl2::nth-slice8 ,n y)))
               (loghead 8 (+ ,(if (member n '(1 3 6))
                                  `(if (eql x1 ,n) (+ 1 x1) x1)
                                'x1)
                             y1)))
            (make-buggy-paddb-lanes n)))))

(make-event
 `(defun buggy-paddb (x y)
    (acl2::merge-8-u8s . ,(make-buggy-paddb-lanes 8))))


(defun make-paddb-lanes (n)
  (if (zp n)
      nil
    (let ((n (1- n)))
      (cons `(let ((x1 (acl2::nth-slice8 ,n x))
                   (y1 (acl2::nth-slice8 ,n y)))
               (loghead 8 (+ x1 y1)))
            (make-paddb-lanes n)))))

(make-event
 `(defun paddb (x y)
    (acl2::merge-8-u8s . ,(make-paddb-lanes 8))))

(defthm paddb-size
  (unsigned-byte-p 64 (paddb x y)))

(defthm buggy-paddb-size
  (unsigned-byte-p 64 (buggy-paddb x y)))

(local (in-theory (disable paddb buggy-paddb)))


(defun all-nil (x)
  (if (atom x)
      t
    (and (not (car x))
         (all-nil (cdr x)))))

  
(define bytes-diff-list (n x y)
  :verify-guards nil
  (if (zp n)
      nil
    (cons (not (equal (loghead 8 x) (loghead 8 y)))
          (bytes-diff-list (1- n) (logtail 8 x) (logtail 8 y))))
  ///
  (local (defthm loghead-of-8n-expand
           (implies (and (not (zp n))
                         (syntaxp (equal n 'n)))
                    (equal (loghead (* 8 n) x)
                           (logapp 8 x (loghead (+ -8 (* 8 n)) (logtail 8 x)))))
           :hints ((acl2::logbitp-reasoning))))

  (local (defthm equal-of-logapp
           (equal (equal (logapp n x1 y1) (logapp n x2 y2))
                  (and (equal (loghead n x1) (loghead n x2))
                       (equal (ifix y1) (ifix y2))))
           :hints ((acl2::logbitp-reasoning :prune-examples nil))))

  (defthm bytes-diff-list-when-equal
    (iff (all-nil (bytes-diff-list n x y))
         (equal (loghead (* (nfix n) 8) x)
                (loghead (* (nfix n) 8) y)))
    :hints(("Goal" :in-theory (enable all-nil)))))


(defthm non-indices-all-false-implies-cdr
  (implies (non-indices-all-false nil x)
           (non-indices-all-false nil (cdr x)))
  :hints (("goal" :use ((:instance non-indices-all-false-necc
                         (indices nil)
                         (idx (+ 1 (nfix (non-indices-all-false-witness nil (cdr x)))))))
           :expand ((non-indices-all-false nil (cdr x)))
           :in-theory (disable non-indices-all-false-necc non-indices-all-false))))

(defthm non-indices-all-false-implies-all-nil
  (implies (non-indices-all-false nil x)
           (all-nil x))
  :hints (("goal" :induct (all-nil x)
           :in-theory (e/d (all-nil) (non-indices-all-false
                                      non-indices-all-false-necc)))
          (and stable-under-simplificationp
               '(:use ((:instance non-indices-all-false-necc
                        (indices nil) (idx 0)))
                 :expand ((nth 0 x))))))

(defthm len-equal-0
  (equal (equal (len x) 0)
         (not (consp x))))

(local (defthm all-nils-by-greedy-max-sat
         (implies (not (greedy-max-sat ans x sat-config))
                  (all-nil x))
         :hints(("Goal" :in-theory (e/d (greedy-max-sat)
                                        (non-indices-all-false))
                 :expand ((numlist 0 1 (len x)))
                 :do-not-induct t))))

(define compare-paddbs (x y)
  :verify-guards nil
  (equal (paddb x y)
         (buggy-paddb x y))
  ///
  ;; (disable-definition compare-paddbs)
  (def-fgl-rewrite compare-paddbs-impl
    (equal (compare-paddbs x y)
           (let ((ans (greedy-max-sat! ans (bytes-diff-list 8 (paddb x y) (buggy-paddb x y)) (make-fgl-ipasir-config))))
             (if (not ans)
                 t
               (fgl-prog2 (fgl-prog2 (cw "Ans: ~x0~%" ans)
                                     (syntax-interp (interp-st-put-user-scratch
                                                     :buggy-lanes (g-concrete->val ans) 'interp-st)))
                          (abort-rewrite (compare-paddbs x y))))))
    :hints (("goal" :use ((:instance all-nils-by-greedy-max-sat
                           (x (bytes-diff-list 8 (paddb x y) (buggy-paddb x y)))
                           (sat-config (make-fgl-ipasir-config))))
             :in-theory (disable paddb buggy-paddb
                                 all-nils-by-greedy-max-sat)))))



(make-event
 (b* (((mv err ?val state)
       (fgl-thm (compare-paddbs x y)))
      ((unless err)
       (er soft 'test-greedy-max-sat "Event succeeded!"))
      (buggy-lanes (cdr (assoc :buggy-lanes (interp-st->user-scratch interp-st))))
      ((unless (and buggy-lanes
                    (equal buggy-lanes '(1 3 6))))
       (er soft 'test-greedy-max-sat "Didn't work? buggy-lanes: ~x0" buggy-lanes)))
   (value '(value-triple :ok))))


