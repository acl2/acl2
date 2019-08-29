; SVL - Listener-based Hierachical Symbolic Vector Hardware Analysis Framework
; Copyright (C) 2019 Centaur Technology
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
; Original author: Mertcan Temel <mert@utexas.edu>


(in-package "SVL")

(include-book "sv-to-svl")
(include-book "centaur/sv/svex/4vec" :dir :system)
(include-book "centaur/sv/svex/eval" :dir :system)
(include-book "std/util/defines" :dir :system)
(include-book "std/basic/two-nats-measure" :dir :system)
(include-book "bits-sbits-defs")
(include-book "macros")
(include-book "svex-eval2")

(defthm wire-listp-implies-alistp
  (implies (and
            (wire-list-p wires))
           (alistp wires))
  :rule-classes :type-prescription)

(encapsulate
  nil
  (local
   (in-theory (enable measure-lemmas)))

  (local
   (defthm svl-env-measure-lemma
     (implies (and (< a x)
                   (natp z)
                   (natp y))
              (< a
                 (+ x y z)))))

  (local
   (defthm lemma1
     (implies
      (and (consp x) (consp (car x)))
      (< (cons-countw (cdr (car x)) 2)
         (cons-countw x 2)))
     :hints (("goal"
	      :in-theory (e/d (cons-countw) ())))))

  (local
   (defthm lemma2-lemma
     (implies (and (natp a)
                   (natp b)
                   (natp x))
              (< x
                 (+ 1 a x b)))))

  (local
   (defthm lemma2-lemma2
     (implies (and (natp a))
              (< 2
                 (+ 3 a)))))

  (local
   (defthm lemma2
     (< (cons-countw (cadr x) 2)
        (+ 1 (cons-countw x 2)))
     :otf-flg t
     :hints (("goal"
              :expand ((cons-countw x 2)
                       (cons-countw (cdr x) 2))
              :in-theory (e/d () ())))))

  (local
   (defthm lemma3-lemma1
     (implies (natp w)
              (<= w (cons-countw x w)))
     :hints (("Goal"
              :induct (cons-countw x w)
              :in-theory (e/d (cons-countw) ())))))

  (local
   (defthm lemma3-lemma2
     (implies
      (and (<= 2 a)
           (<= 2 b))
      (< (1+ x)
         (+ a b x)))))

  (local
   (defthm lemma3
     (implies (and (consp x) (consp (car x)))
              (< (+ 1 (cons-countw (cdr (car x)) 2))
                 (cons-countw x 2)))
     :hints (("Goal"
              :expand ((cons-countw x 2)
                       (CONS-COUNTW (CAR X) 2))
              :in-theory (e/d () ())))))

  (fty::deftypes
   svl-env
   (fty::defprod svl-env
                 ((wires sv::svex-env-p)
                  (modules svl-env-alist-p))
                 :tag nil
                 :count nil
                 :measure (+ 1 (cons-countw x 2))
                 :layout :list)

   (fty::defalist svl-env-alist
                  :count nil
                  :measure (cons-countw x 2)
                  :val-type svl-env)))

(defun queue-p (queue)
  (declare (xargs :guard t))
  (occ-name-list-p queue))

(defun loose-alistp (lst)
  (declare (xargs :guard t))
  (cond ((atom lst) t)
        (t (and (consp (car lst))
                (loose-alistp (cdr lst))))))

(defun strip-cars-2 (acl2::x)
  (declare (xargs :guard (loose-alistp acl2::x)))
  (cond ((atom acl2::x) nil)
        (t (cons (car (car acl2::x))
                 (strip-cars-2 (cdr acl2::x))))))

(defun strip-cdrs-2 (acl2::x)
  (declare (xargs :guard (loose-alistp acl2::x)))
  (cond ((atom acl2::x) nil)
        (t (cons (cdr (car acl2::x))
                 (strip-cdrs-2 (cdr acl2::x))))))

(defun queue-mem-p (queue-mem)
  (declare (xargs :guard t))
  (and (loose-alistp queue-mem)
       (occ-name-list-p (strip-cars-2 queue-mem))
       (boolean-listp (strip-cdrs-2 queue-mem))))

(local
 (encapsulate
   nil

   (defthm guard-lemma1 (implies (natp start)
                                 (sv::4vec-p start))
     :hints (("goal"
              :in-theory (e/d (sv::4vec-p) ()))))

   (defthm guard-lemma2
     (implies (and (or (stringp occ-outs3)
                       (symbolp occ-outs3))
                   (not (booleanp occ-outs3)))
              (sv::svar-p occ-outs3))
     :hints (("goal"
              :in-theory (e/d (sv::svar-p) ()))))))

(define svl-run-add-to-queue (occs queue queue-mem)
  :parents (svl-run)
  :prepwork
  ((local
    (in-theory
     (e/d () ((:rewrite acl2::symbolp-of-car-when-symbol-listp)
              (:definition symbol-listp)
              (:rewrite acl2::boolean-listp-when-not-consp)
              (:rewrite acl2::symbol-listp-when-not-consp)
              (:rewrite default-cdr)
              (:type-prescription hons-assoc-equal)
              (:rewrite default-car))))))

  :returns (mv (queue-ret queue-p :hyp (and (queue-p queue)
                                            (occ-name-list-p occs)))
               (queue-mem-ret queue-mem-p :hyp (and (queue-p queue)
                                                    (occ-name-list-p occs)
                                                    (queue-mem-p queue-mem))))
  ;; occs is a list of names for occurances that are to be added to the queue
  ;; to be run.
  ;; updates queue and queue-mem
  ;; other-queue-mem is just for reading and  blocking out adding elements to queue.

  :short "Adds occurances to the queue if they are not already as the existence
  is determined by queue-mem and other-queue-mem boolean-valued alists"

  (cond
   ((atom occs)
    (mv queue queue-mem))
   ((or (cdr (hons-get (car occs) queue-mem)));; already in the queue skip
    (svl-run-add-to-queue (cdr occs) queue queue-mem ))
   (t
    (svl-run-add-to-queue (cdr occs)
                          (cons (car occs) queue)
                          (hons-acons (car occs) t queue-mem)))))

(defthm svar-p-of-var-string-delay
  (implies (and (stringp occ-delayed-ins1)
                (svl-env-p delayed-env)
                (cdr (hons-assoc-equal occ-delayed-ins1
                                       (svl-env->wires delayed-env))))
           (sv::svar-p (list* :var occ-delayed-ins1 1)))
  :hints (("goal"
           :in-theory (e/d (sv::svar-p) ()))))

(define svl-run-add-delayed-ins
  ((env-wires sv::svex-env-p)
   (delayed-env svl-env-p)
   (occ-delayed-ins occ-name-list-p))
  :short "For assignments that uses values from previous cycle, expand the
  environment with the delayed values"
  :parents (svl-run)
  :prepwork
  ((local
    (in-theory (enable sv::svar-p))))
  :returns (wire-env-res sv::svex-env-p :hyp (and (sv::svex-env-p env-wires)
                                                  (svl-env-p delayed-env)))
  (if (atom occ-delayed-ins)
      env-wires
    (b* ((prev-val (cdr (hons-get (car occ-delayed-ins)
;(STD::DA-NTH 0 delayed-env)
                                  (svl-env->wires delayed-env)
                                  )))
         ((unless prev-val)
          (svl-run-add-delayed-ins env-wires delayed-env (cdr occ-delayed-ins))))
      (svl-run-add-delayed-ins (hons-acons `(:var ,(car occ-delayed-ins)
                                                  . 1)
                                           prev-val
                                           env-wires)
                               delayed-env
                               (cdr occ-delayed-ins)))))

(define svl-update-wire
  ((wire wire-p)
   (new-val sv::4vec-p)
   (env-wires sv::svex-env-p))
  :returns (res sv::svex-env-p :hyp (and (wire-p wire)
                                         (sv::svex-env-p env-wires)
                                         (sv::4vec-p new-val)))
  :parents (svl-run)
  :short "Overwrites a wire with new value"
  ;; remove a center piece from old-full-val and replace it with new-val. The
  ;; boundries of that inner-piece is defined by start and size.
  (b* (((mv wire.name wire.start wire.size)
        (mv (wire-name wire)
            (wire-start wire)
            (wire-size wire))))
    (cond
     ((consp (cdr wire))
      (b* ((old-val (hons-get wire.name env-wires))
           (old-val (if old-val (cdr old-val) '(-1 . 0)))
           ;;TODO get rid of this if statement.
           (updated-val (sbits wire.start wire.size new-val old-val)))
        (hons-acons wire.name updated-val env-wires)))
     (t (hons-acons wire.name new-val env-wires))))

  ///

  (defthmd svl-update-wire-unsized-wire
    (implies (atom (cdr wire))
             (equal (svl-update-wire wire new-val env-wires)
                    (hons-acons (wire-name wire) new-val env-wires))))

  (defthmd svl-update-wire-sized-wire
    (equal (svl-update-wire `(,wire.name ,wire.size . ,wire.start) new-val env-wires)
           (b* ((old-val  (hons-get wire.name env-wires))
                (old-val (if old-val (cdr old-val) '(-1 . 0)))
                (updated-val (sbits wire.start wire.size new-val old-val)))
             (hons-acons wire.name updated-val env-wires)))))

 ;; (define svl-update-wires
;; ;; function to use when creating the rewrite rules. Updates multiple wires
;; for
;;   ...)

(define svl-run-save-assign-result
  ((result sv::4vec-p)
   (occ-outs wire-list-p)
   (env-wires sv::svex-env-p))
  :parents (svl-run)
  :returns (result-env-wires
            sv::svex-env-p
            :hyp (and (sv::svex-env-p env-wires)
                      (wire-list-p occ-outs)
                      (sv::4vec-p result)))
  :short "Saves an assignment result in env-wires"
  (if (atom occ-outs)
      env-wires
    (b* ((wire (car occ-outs))
         #|(signame (wire-name wire))||#
         (size (wire-size wire))
         #|(start (wire-start wire))||#
         (size (if size size 1))
         #|(start (if start start 0))||#
         #|(old-val (cdr (hons-get signame env-wires)))||#
         (env-wires (svl-update-wire wire result env-wires))
         #|(env-wires (hons-acons signame new-val env-wires))||#)
      (svl-run-save-assign-result (sv::4vec-rsh size result)
                                  (cdr occ-outs)
                                  env-wires))))

(define svl-run-get-module-occ-inputs
  ((env-wires sv::svex-env-p)
   #|(occ-input-vals-acc sv::4veclist-p)||#
   (occ-ins module-occ-wire-list-p))
  ;; read env and bind signals, then add them to occ-env.
  :returns (res sv::4veclist-p
                :hyp (and (sv::svex-env-p env-wires)
                          #|(sv::4veclist-p occ-input-vals-acc)||#
                          (module-occ-wire-list-p occ-ins)))
  :parents (svl-run)
  :short "Extends an occurance of a module's environment before running it."
  (if (atom occ-ins)
      nil
    (b* ((cur-in (car occ-ins))
         (wire (cdr cur-in))
         (wire.name (wire-name wire))
         (wire.size (wire-size wire))
         (wire.start (wire-start wire))
         (val (hons-get wire.name env-wires))
         ;; TODO get rid of this if as well.
         (val (if val
                  (if  wire.start
                      (bits wire.start wire.size (cdr val))
                    (cdr val))
                '(-1 . 0))))
      (cons val
            (svl-run-get-module-occ-inputs env-wires (cdr occ-ins))))))

(define svl-run-save-module-result
  ((env-wires sv::svex-env-p)
   (occ-res-vals sv::4veclist-p)
   (occ-outs module-occ-wire-list-p))
  :parents (svl-run)
  :short "Extracts output values of a module occurance and saves the new wire
  values in the current environment"
  ;; :returns (res sv::svex-env-p
  ;;               :hyp (and (sv::svex-env-p env-wires)
  ;;                         (sv::svex-env-p occ-res-alist)
  ;;                         (module-occ-wire-list-p occ-outs)))
  :guard-hints (("Goal"
                 :in-theory (e/d () (wire-p))))
  :returns (res-env-wires sv::svex-env-p
                          :hyp (and (sv::svex-env-p env-wires)
                                    (sv::4veclist-p occ-res-vals)
                                    (module-occ-wire-list-p occ-outs)))
  (if (atom occ-outs)
      env-wires
    (b* ((wire (cdar occ-outs))
         (new-val (if (consp occ-res-vals) (car occ-res-vals) '(-1 . 0))))
      (svl-run-save-module-result
       (svl-update-wire wire new-val env-wires)
       (cdr occ-res-vals)
       (cdr occ-outs)))))

(define svl-run-initialize-wires
  ((env-wires sv::svex-env-p)
   (wires wire-list-p))
  :parents (svl-run)
  :returns (res sv::svex-env-p
                :hyp (and (sv::svex-env-p env-wires)
                          (wire-list-p wires)))
  :short "Initializes all the wires to don't care with respect to their size"
  (if (atom wires)
      env-wires
    (b* ((wire (car wires)))
      (if (hons-get (wire-name wire) env-wires)
          (svl-run-initialize-wires env-wires (cdr wires))
        (hons-acons (wire-name wire)
                    (sv::4vec-part-select 0 (ifix (wire-size wire)) '(-1 . 0))
                    (svl-run-initialize-wires env-wires (cdr wires)))))))

(defun hons-gets (keys fast-alist)
  (declare (xargs :guard t))
  (if (atom keys)
      nil
    (cons (hons-get (car keys) fast-alist)
          (hons-gets (cdr keys) fast-alist))))

(defun hons-gets-vals (keys fast-alist)
  (declare (xargs :guard t))
  (if (atom keys)
      nil
    (cons (cdr (hons-get (car keys) fast-alist))
          (hons-gets-vals (cdr keys) fast-alist))))

(define svl-get-outputs (sigs wires alist)
  (declare (xargs :guard (and (svl::wire-list-p wires)
                              (sv::svex-env-p alist))))
  :returns (res sv::4veclist-p
                :hyp (sv::svex-env-p alist)
                :hints (("Goal"
                         :in-theory (e/d (bits) ()))))
  (if (atom sigs)
      nil
    (b* ((res (hons-get (car sigs) alist))
         ((unless res)
          (cons (sv::4vec-x) (svl-get-outputs (cdr sigs) wires alist)))
         (wire (assoc-equal (car sigs) wires))
         (size (cadr wire)))
      (cons (if (and size res) (bits 0 size (cdr res)) (cdr res))
            (svl-get-outputs (cdr sigs) wires alist)))))

(define hons-gets-fast-alist (keys fast-alist)
  (declare (xargs :guard t))
  (if (atom keys)
      nil
    (let ((res (hons-get (car keys) fast-alist)))
      (hons-acons (car keys)
                  ;; TODO rid of this if as well.
                  (if res (cdr res) (sv::4vec-x))
                  (hons-gets-fast-alist (cdr keys) fast-alist)))))

(define start-env (input-names input-vals)
  (declare (xargs :guard (and (string-listp input-names)
                              (sv::4veclist-p input-vals))))
  :returns (res SVEX-ENV-P
                :hyp (and (string-listp input-names)
                          (sv::4veclist-p input-vals))
                :hints (("Goal"
                         :in-theory (e/d (SV::SVAR-P) ()))))
  (if (or (atom input-names)
          (atom input-vals))
      nil
    (hons-acons (car input-names)
                (car input-vals)
                (start-env (cdr input-names)
                           (cdr input-vals)))))

(encapsulate
  nil

  (define occ-assign->svex2 (x)
    :inline t
    :guard (true-listp x)
    (STD::DA-NTH 3 x)
    ///

    (defthm occ-assign->svex2-is-occ-assign->svex
      (implies (and (occ-p (cons ':assign x)))
               (equal (occ-assign->svex2 x)
                      (occ-assign->svex (cons ':assign x))))
      :hints (("Goal"
               :in-theory (e/d (occ-p occ-assign->svex
                                      OCC-NAME-LIST-P
                                      OCC-KIND) ())))))

  (define occ-assign->outputs2 (x)
    :inline t
    :guard (true-listp x)
    (std::da-nth 2 x)
    ///

    (local
     (defthm lemma1
       (implies (WIRE-LIST-P x)
                (equal (WIRE-LIST-FIX x)
                       x))
       :hints (("Goal"
                :in-theory (e/d (wire-list-fix
                                 wire-list-p) ())))))

    (defthm occ-assign->outputs2-is-occ-assign->outputs
      (implies (and (occ-p (cons ':assign x)))
               (equal (occ-assign->outputs2 x)
                      (occ-assign->outputs (cons ':assign x))))
      :hints (("Goal"
               :in-theory (e/d (occ-p occ-assign->outputs
                                      OCC-NAME-LIST-P
                                      WIRE-LIST-FIX
                                      SVEX-P
                                      WIRE-LIST-P
                                      OCC-KIND) ())))))

  (define occ-module->inputs2 (x)
    :inline t
    :guard (true-listp x)
    (STD::DA-NTH 0 x)
    ///

    (defthm occ-module->inputs2-is-occ-module->inputs
      (implies (and (occ-p (cons ':module x)))
               (equal (occ-module->inputs2 x)
                      (occ-module->inputs (cons ':module x))))
      :otf-flg t
      :hints (("Goal"
               :in-theory (e/d (occ-p OCC-MODULE->INPUTS
                                      MODULE-OCC-WIRE-LIST-FIX
                                      MODULE-OCC-WIRE-LIST-P
                                      OCC-NAME-LIST-P
                                      OCC-KIND) ())))))

  (define occ-module->outputs2 (x)
    :inline t
    :guard (true-listp x)
    (STD::DA-NTH 1 x)
    ///

    (defthm occ-module->outputs2-is-occ-module->outputs
      (implies (and (occ-p (cons ':module x)))
               (equal (occ-module->outputs2 x)
                      (occ-module->outputs (cons ':module x))))
      :otf-flg t
      :hints (("Goal"
               :in-theory (e/d (occ-p occ-module->outputs
                                      MODULE-OCC-WIRE-LIST-FIX
                                      MODULE-OCC-WIRE-LIST-P
                                      OCC-NAME-LIST-P
                                      OCC-KIND) ())))))

  (define occ-module->name2 (x)
    :inline t
    :guard (true-listp x)
    (STD::DA-NTH 2 x)
    ///

    (defthm occ-module->name2-is-occ-module->name
      (implies (and (occ-p (cons ':module x)))
               (equal (occ-module->name2 x)
                      (occ-module->name (cons ':module x))))
      :otf-flg t
      :hints (("Goal"
               :in-theory (e/d (occ-p occ-module->name
                                      MODULE-OCC-WIRE-LIST-FIX
                                      MODULE-OCC-WIRE-LIST-P
                                      OCC-NAME-LIST-P
                                      OCC-KIND) ())))))

  (define occ-module2 (x)
    :inline t
    :guard (true-listp x)
    :enabled t
    (mv (occ-module->inputs2 x)
        (occ-module->outputs2 x)
        (occ-module->name2 x))))

(encapsulate
  nil

  (defconst *big-num*
    (expt 2 20))

  (local
   (defthm occ-module-name-count-count
     (implies (and (occ-p occ)
                   (equal (occ-kind occ) :module))
              (<  (cons-count (occ-module->name occ))
                  (cons-count occ)))
     :hints (("goal"
              :in-theory (e/d (cons-count
                               occ-module->name) ())))))

  (local
   (defthm cons-count-cdar
     (implies (consp x)
              (< (cons-count (cdar x))
                 (cons-count x)))
     :hints (("goal"
              :in-theory (e/d (cons-count) ())))))

  (local
   (defthm cound-count-hons-get
     (implies (consp occs)
              (< (cons-count (cdr (hons-assoc-equal queue1 (cdr occs))))
                 (cons-count occs)))
     :hints (("goal"
              :in-theory (e/d (cons-count
                               hons-assoc-equal) ())))))

  (local
   (defthm cound-count-hons-get-lemma2
     (implies (case-split (consp occs))
              (< (cons-count (cdr (hons-assoc-equal queue1 occs)))
                 (cons-count occs)))
     :hints (("goal"
              :in-theory (e/d (cons-count
                               hons-assoc-equal) ())))))

  (local
   (defthm cound-count-hons-get-lemma3

     (<= (cons-count (cdr (hons-assoc-equal queue1 occs)))
         (cons-count occs))
     :hints (("goal"
              :in-theory (e/d (cons-count
                               hons-assoc-equal) ())))))

  (local
   (in-theory (enable measure-lemmas)))

  (define get-module-rank ((module-name stringp)
                           (svl-modules svl-module-alist-p))
    (if (and module-name
             (not (equal module-name ""))
             (hons-get module-name svl-modules))
        (nfix (svl-module->rank (cdr (hons-get module-name svl-modules))))
      0))

  (local
   (defthm cons-assign-cdr-occ-is-occ
     (implies (and (EQUAL (OCC-KIND OCC) :ASSIGN)
                   (OCC-P OCC))
              (equal (CONS :ASSIGN (CDR OCC))
                     occ))
     :hints (("Goal"
              :in-theory (e/d (occ-p
                               occ-kind) ())))))

  (local
   (defthm cons-module-cdr-occ-is-occ
     (implies (and (EQUAL (OCC-KIND OCC) :module)
                   (OCC-P OCC))
              (equal (CONS :module (CDR OCC))
                     occ))
     :hints (("Goal"
              :in-theory (e/d (occ-p
                               occ-kind) ())))))

  (define get-occ-rank
    ((occ occ-p)
     (svl-modules svl-module-alist-p))
    (if (and ;(occ-p occ)
         (equal (occ-kind occ) ':module))
        (get-module-rank (occ-module->name2 (cdr occ)) svl-modules)
      0)
    :prepwork
    ((Local
      (defthm occ-p-implies-1
        (implies (occ-p occ)
                 (true-listp occ))
        :hints (("Goal"
                 :in-theory (e/d (occ-p) ())))
        :rule-classes :forward-chaining))))

  (defthm get-occ-rank-natp
    (and (integerp (get-occ-rank occ svl-modules))
         (<= 0 (get-occ-rank occ svl-modules)))
    :rule-classes :type-prescription
    :hints (("Goal"
             :in-theory (e/d (get-occ-rank) ()))))

  (define get-max-occ-rank
    ((occs occ-alist-p)
     (svl-modules svl-module-alist-p))
    (cond
     ((atom occs)
      0)
     (t (max (get-max-occ-rank (cdr occs) svl-modules)
             (get-occ-rank (cdar occs) svl-modules)))))

  (defthm measure-occs-rank-natp
    (and (integerp (get-max-occ-rank occ svl-modules))
         (<= 0 (get-max-occ-rank occ svl-modules)))
    :rule-classes :type-prescription
    :hints (("Goal"
             :in-theory (e/d (get-max-occ-rank) ()))))

  (define well-ranked-module
    ((module-name stringp)
     (svl-modules svl-module-alist-p))
    :guard (hons-get module-name svl-modules)
    :enabled t
    (> (get-module-rank module-name svl-modules)
       (get-max-occ-rank (svl-module->occs (cdr (hons-get module-name
                                                          svl-modules)))
                         svl-modules)))


  #|(local
  (defthmd svl-run-cycle-measure-lemma1-lemma
  (implies (and (equal (occ-kind occ) ':module)
  (not (occ-p occ)))
  (and (EQUAL (get-module-rank (occ-module->name occ) svl-modules)
  (get-occ-rank OCC SVL-MODULES))
  #|(EQUAL (get-module-rank (occ-module->name2 (cdr OCC)) SVL-MODULES)
  (get-occ-rank OCC SVL-MODULES))||#))
  :hints (("Goal"
  :cases ((occ-p occ))
  :in-theory (e/d (get-occ-rank
  ;                             occ-p ;
   ;                            OCC-KIND ;
    ;                           OCC-MODULE->NAME ;
     ;                          ACL2::STR-FIX ;
      ;                         OCC-MODULE->NAME2 ;
  get-module-rank) ())))))||#

  #|(local
  (defthm svl-run-cycle-measure-lemma1
  (implies (and (equal (occ-kind occ) ':module)
;(case-split (occ-p occ)) ;
  )
  (and (EQUAL (get-module-rank (OCC-MODULE->NAME OCC) SVL-MODULES)
  (get-occ-rank OCC SVL-MODULES))
  (EQUAL (get-module-rank (OCC-MODULE->NAME2 (cdr OCC)) SVL-MODULES)
  (get-occ-rank OCC SVL-MODULES))))
  :hints (("Goal"
  :cases ((occ-p occ))
  :in-theory (e/d (get-occ-rank
  get-module-rank) ())))))||#

  #|(local
  (defthm svl-run-cycle-measure-lemma1-v2-lemma
  (implies (and (equal (occ-kind occ) ':module)
  (not (occ-p occ))
  (<= (GET-OCC-RANK OCC SVL-MODULES)
  (GET-MODULE-RANK (OCC-MODULE->NAME2 (CDR OCC))
  SVL-MODULES))
  )
  (and #|(EQUAL (get-module-rank (OCC-MODULE->NAME OCC) SVL-MODULES)
  (get-occ-rank OCC SVL-MODULES))||#
  (EQUAL (get-module-rank (occ-module->name2 (cdr OCC)) SVL-MODULES)
  (get-occ-rank OCC SVL-MODULES))))
  :hints (("Goal"
  :in-theory (e/d (get-occ-rank
  occ-p
  OCC-KIND
  occ-module->name2
  get-module-rank) ())))))||#

  (local
   (defthm svl-run-cycle-measure-lemma1-v2
     (implies (and (equal (occ-kind occ) ':module)
                   )
              (and #|(EQUAL (get-module-rank (OCC-MODULE->NAME OCC) SVL-MODULES)
               (get-occ-rank OCC SVL-MODULES))||#
               (EQUAL (get-module-rank (OCC-MODULE->NAME2 (cdr OCC)) SVL-MODULES)
                      (get-occ-rank OCC SVL-MODULES))))
     :hints (("Goal"
              :cases ((occ-p occ))
              :in-theory (e/d (get-occ-rank
                               get-module-rank) ())))))

  (local
   (defthm svl-run-cycle-measure-lemma2-lemma
     (<= (GET-OCC-RANK NIL SVL-MODULES) 0)
     :hints (("Goal"
              :in-theory (e/d (GET-OCC-RANK) ())))))

  (local
   (defthm svl-run-cycle-measure-lemma2
     (<= (get-occ-rank (cdr (HONS-ASSOC-EQUAL occ-name occs)) svl-modules)
         (get-max-occ-rank occs svl-modules))
     :hints (("Goal"
              :in-theory (e/d (get-max-occ-rank) ())))))

  (local
   (defthm svl-run-cycle-measure-lemma3
     (implies (and (natp a)
                   (natp b)
                   (<= a b)
                   (<= b a))
              (equal (equal a b) t))))

  (local
   (defthm svl-run-cycle-measure-lemma4
     (implies (not (consp occs))
              (equal (get-max-occ-rank OCCS SVL-MODULES)
                     (get-occ-rank NIL SVL-MODULES)))
     :hints (("Goal"
              :in-theory (e/d (get-occ-rank
                               SVL-MODULE->RANK
                               get-max-occ-rank) ())))))

  (local
   (defthm svl-run-cycle-measure-lemma5
     (IMPLIES (and (EQUAL (OCC-KIND OCC) :MODULE))
              (and (< (CONS-COUNT (OCC-MODULE->NAME OCC))
                      (CONS-COUNT OCC))
                   (< (CONS-COUNT (OCC-MODULE->NAME2 (cdr OCC)))
                      (CONS-COUNT OCC))))
     :hints (("Goal"
	      :in-theory (e/d (cons-count
                               OCC-MODULE->NAME OCC-MODULE->NAME2 OCC-KIND) ())))))

  (local
   (in-theory (disable RP::CONS-COUNT-ATOM)))

  (acl2::defines
   svl-run-cycle

   (define svl-run-cycle
     ((module-name stringp "Module to run")
      (inputs sv::4veclist-p "Input values in order")
      (delayed-env svl-env-p "Environment with necessary signal values from previous cycle")
      (svl-modules svl-module-alist-p "SVL design"))
     :verify-guards nil
     ;; :returns (mv outputs new-env)
     ;; old-env and env must be a fast-alist
     ;; svl-modules must be fast-alist
     :short "Run a cycle of svl module"
     :measure (acl2::nat-list-measure
               (list (get-module-rank module-name svl-modules)
                     (cons-count module-name)
                     (1+ *big-num*)))

     (let ((module (cdr (hons-get module-name svl-modules))))
       (cond
        ((or (not module)
             (not (well-ranked-module module-name svl-modules)))
         (mv
          (cw "Either Module ~p0 is missing or it has invalid ranks~%"
              module-name)
          (make-svl-env)))
        (t
         (b* (((svl-module module) module)
              ;; create the initial queue of occurances.
              ((mv queue queue-mem)
               (svl-run-add-to-queue
                (cdr (hons-get ':initial module.listeners))
                nil
                (* 4 (len module.occs)) ;; queue size hint
                ))
              ;; initialize unassigned wires to don't care with respect to
              ;; their size.
              (env-wires (start-env module.inputs inputs))
;(env-wires (svl-run-initialize-wires env-wires module.wires))
              (env-wires
               (svl-run-add-delayed-ins env-wires delayed-env module.delayed-inputs))
              ;; run the queue.
              ((mv  env-wires next-delayed-env.modules)
               (svl-run-queue queue queue-mem delayed-env nil
                              env-wires module.occs module.listeners
                              svl-modules
                              *big-num*))
              (next-delayed-env (make-svl-env
                                 :wires (hons-gets-fast-alist
                                         module.delayed-inputs
                                         env-wires)
                                 :modules next-delayed-env.modules))
              (outputs (svl-get-outputs module.outputs module.wires
                                        env-wires))
              (- (fast-alist-free env-wires)))
           (mv outputs next-delayed-env))))))

   (define svl-run-occ
     ((occ-name occ-name-p "Name of the occ to run")
      (occ occ-p "The occurance to run")
      (new-queue queue-p "The queue that's being formed as a result of the
     current queue")
      (queue-mem queue-mem-p "Queue-mem for the current queue will be run.")
      (delayed-env svl-env-p "Delayed environment for occurances with delayed
     inputs")
      (next-delayed-env.modules svl-env-alist-p)
      (env-wires sv::svex-env-p "Current environment for wires")
      (listeners occ-name-alist-p "SVL-listeners for the occurances. Used to
     determine what to add to the queue.")
      (svl-modules svl-module-alist-p "SVL design"))
     :measure (acl2::nat-list-measure
               (list (get-occ-rank occ svl-modules)
                     (cons-count occ)
                     0))
     (b* ((occ-type (occ-kind occ))
          ;; mark the occurances as visited:
          (queue-mem (hons-acons occ-name nil queue-mem)))
       (cond
        ((eq occ-type ':assign)
         (b* (;((occ-assign occ) occ)
              ((mv occ.svex occ.outputs)
               (mv
                (mbe :exec (occ-assign->svex occ)
                     :logic (occ-assign->svex2 (cdr occ)))
                (mbe :exec (occ-assign->outputs occ)
                     :logic (occ-assign->outputs2 (cdr occ)))))

              ;; evaluate the assignment
              (result (mbe :exec (sv::svex-eval occ.svex env-wires)
                           :logic (svex-eval2 occ.svex env-wires)))
              ;; save the result in the environment. A separate function
              ;; because assignment output can be more than one signal.
              (env-wires (svl-run-save-assign-result result occ.outputs  env-wires))
              ;; add the next occurances to be executed to the new queue.
              (occ-listeners (cdr (hons-get occ-name listeners)))
              ((mv new-queue queue-mem)
               (svl-run-add-to-queue occ-listeners
                                     new-queue queue-mem )))
           (mv env-wires  new-queue #|rest-queue-mem||# queue-mem next-delayed-env.modules)))
        ((eq occ-type ':module)
         (b* (;((occ-module occ) occ) ;;TODO replace with something without
              ;;guard.
              ((mv occ.inputs occ.outputs occ.name)
               (mbe :exec
                    (mv (occ-module->inputs occ)
                        (occ-module->outputs occ)
                        (occ-module->name occ))
                    :logic (occ-module2 (cdr occ))))
              (occ-delayed-env
               (hons-get occ-name (svl-env->modules delayed-env)))
              (occ-delayed-env
               (if occ-delayed-env (cdr occ-delayed-env) (make-svl-env)))

              ;; create a new environment for the module occurance whose
              ;; entries are values for it input signals.
              (occ-inputs-vals
               (svl-run-get-module-occ-inputs env-wires occ.inputs))

              ;; run the module
              ((mv outputs module-next-delayed-env)
               (svl-run-cycle occ.name
                              occ-inputs-vals
                              occ-delayed-env
                              svl-modules))
              (env-wires (svl-run-save-module-result env-wires
                                                     outputs
                                                     occ.outputs))
              (next-delayed-env.modules
               (if (not (equal module-next-delayed-env (make-svl-env)))
                   (hons-acons occ-name module-next-delayed-env next-delayed-env.modules)
                 next-delayed-env.modules))

              ;; add the next occurances to be executed to the new queue.
              (occ-listeners (cdr (hons-get occ-name listeners)))
              ((mv new-queue queue-mem)
               (svl-run-add-to-queue occ-listeners new-queue
                                     queue-mem )))
           (mv env-wires new-queue
               queue-mem next-delayed-env.modules)))
        (t
         (progn$
          (hard-error 'svl-run-this-queue "Unexpected occurance type ~%" nil)
          (mv env-wires nil queue-mem next-delayed-env.modules))))))

   (define svl-run-this-queue
     ((queue queue-p "List of occ-names to run")
      (queue-mem queue-mem-p "An alist to check membership in queue")
      (delayed-env svl-env-p "Environment for values from previous cycle")
      (next-delayed-env.modules svl-env-alist-p)
      (env-wires sv::svex-env-p "Current environment, an alist")
      (occs occ-alist-p "All the occurances of the module being run, an alist")
      (listeners occ-name-alist-p "All the listeners of the module being run,
     an alist")
      (svl-modules svl-module-alist-p "SVL design")
      (limit natp "Limit for termination. When reached it may mean there is a
     loop between modules"))
     :measure (acl2::nat-list-measure
               (list (get-max-occ-rank occs svl-modules)
                     (cons-count occs)
                     limit))
     (cond
      ((atom queue)
       (mv env-wires nil queue-mem next-delayed-env.modules))
      ((zp limit)
       (progn$
        (hard-error
         'svl-run-this-queue
         "Limit Reached! Possibly a combinational loop between modules. ~%"
         nil)
        (mv env-wires nil queue-mem next-delayed-env.modules)))
      (t
       (b* (((mv env-wires new-queue queue-mem next-delayed-env.modules)
             (svl-run-this-queue
              (cdr queue) queue-mem delayed-env next-delayed-env.modules  env-wires occs listeners
              svl-modules (1- limit)))
            (occ-name (car queue))
            (occ-entry (hons-get occ-name occs)))
         (if occ-entry
             (svl-run-occ occ-name (cdr occ-entry) new-queue
                          queue-mem
                          delayed-env next-delayed-env.modules
                          env-wires listeners svl-modules)
           (progn$
            (hard-error
             'svl-run-this-queue
             "The occ found in the queue does not exist in the occ list ~%"
             nil)
            (mv env-wires nil queue-mem next-delayed-env.modules)))))))

   (define svl-run-queue
     ((queue queue-p "The current queue to run")
      (queue-mem queue-mem-p "An alist to check membership in queue.")
      (delayed-env svl-env-p "Environment for values from previous cycle")
      (next-delayed-env.modules svl-env-alist-p)
      (env-wires sv::svex-env-p "Current environment, an alist")
      (occs occ-alist-p  "All the occurances of the module being run, an alist")
      (listeners occ-name-alist-p "All the listeners of the module being run,
     an alist")
      (svl-modules svl-module-alist-p "SVL Design")
      (limit natp "Limit for termination"))
     ;; calls svl-run-this-queue for growing queues.
     :measure (acl2::nat-list-measure
               (list (get-max-occ-rank occs svl-modules)
                     (cons-count occs)
                     limit))
     :short "A wrapper for svl-run-this-queue."
     :long "svl-run-queue calls svl-run-this-queue for the current queue.
            It runs that queue, returns a new one and svl-run-queue runs it again."
     (cond
      ((atom queue)
       (progn$
        ;; everything ran smoothly now exit.
        (fast-alist-free queue-mem)
        (mv env-wires next-delayed-env.modules)))
      ((zp limit)
       (progn$
        (hard-error
         'svl-run-queue
         "Limit Reached! Possibly a combinational loop between modules. ~%"
         nil)
        (mv  env-wires next-delayed-env.modules)))
      (t
       (b* (((mv env-wires new-queue queue-mem next-delayed-env.modules)
             (svl-run-this-queue queue queue-mem delayed-env
                                 next-delayed-env.modules env-wires occs
                                 listeners svl-modules (1- limit))))
         (svl-run-queue new-queue
                        queue-mem
                        delayed-env next-delayed-env.modules env-wires
                        occs listeners svl-modules (1- limit)))))))

  (make-flag svl-run-cycle :defthm-macro-name defthm-svl-run-cycle))

(mutual-recursion
 ;; destroy fast-alists in an instance of svl-env
 (defun svl-free-env (module-name env svl-design limit)
   (declare (xargs
             :guard (and (svl-env-p env)
                         (svl-module-alist-p svl-design)
                         (natp limit))
             :measure (nfix limit)))
   (cond
    ((zp limit)
     0)
    ((not (hons-get module-name svl-design))
     0)
    (t
     (b* (((svl-env env) env)
          (- (fast-alist-free env.wires))
          (res (svl-free-env-occs
                (svl-module->occs (cdr (hons-get module-name svl-design)))
                env.modules
                svl-design
                (1- limit)))
          (- (fast-alist-free env.modules)))
       (+ res 2)))))

 (defun svl-free-env-occs (occs env-modules svl-design limit)
   (declare (xargs
             :guard (and (svl-env-alist-p env-modules)
                         (occ-alist-p occs)
                         (svl-module-alist-p svl-design)
                         (natp limit))
             :measure (nfix limit)))
   (if (or (atom occs)
           (zp limit))
       0
     (b* ((occ-entry (car occs))
          (occ-name (car occ-entry))
          (occ (cdr occ-entry))
          ((unless (equal (occ-kind occ) ':module))
           (svl-free-env-occs (cdr occs)
                              env-modules svl-design
                              (1- limit)))
          (occ-env (cdr (hons-get occ-name
                                  env-modules))))
       (+ (if occ-env
              (svl-free-env (occ-module->name occ)
                            occ-env
                            svl-design
                            (1- limit))
            0)
          (svl-free-env-occs (cdr occs) env-modules svl-design (1- limit)))))))

(defun svl-run-fast-alist-append (keys vals alist)
  (if (atom keys)
      alist
    (hons-acons (car keys)
                (cond ((atom vals) '(-1 . 0))
                      ((or (equal (car vals) "_")
                           (equal (car vals) '_)
                           (equal (car vals) 'X)
                           (not (sv::4vec-p (car vals)))
                           (equal (car vals) "X")
                           (equal (car vals) "x"))
                       '(-1 . 0))
                      (t (car vals)))
                (svl-run-fast-alist-append (cdr keys) (cdr vals) alist))))

#|(defun svl-run-cycles-output (out-env-wires rest)
  (declare (xargs :mode :program))
  (cond
   ((atom out-env-wires)
    rest)
   ((or (equal (caar out-env-wires) "_")
        (equal (caar out-env-wires) '_)
        (equal (caar out-env-wires) 'X)
        (equal (caar out-env-wires) "X")
        (equal (caar out-env-wires) "x"))
    (svl-run-cycles-output (cdr out-env-wires) rest))
   (t (cons (car out-env-wires)
            (svl-run-cycles-output (cdr out-env-wires) rest)))))

(defun svl-run-cycles (module-name in-names in-vals out-sigs delayed-env svl-modules)
  (declare (xargs :mode :program))
  (if (atom (car in-vals))
      (progn$
       (svl-free-env module-name delayed-env svl-modules)
       (mv t nil))
    (b* ((env-wires (svl-run-fast-alist-append in-names (strip-cars in-vals)
                                               nil))
         (module.outputs (svl-module->outputs (cdr (hons-get module-name
                                                             svl-modules))))
         (out-wire-pairs (pairlis$ module.outputs (pairlis$ (strip-cars out-sigs) nil)))
         ((mv valid out-env-wires next-delayed-env)
          (svl-run-cycle module-name delayed-env env-wires nil out-wire-pairs
                         svl-modules))
         (- (svl-free-env module-name delayed-env svl-modules))
         (- (fast-alist-free out-env-wires))
         ((unless valid)
          (mv nil nil))

         ((mv valid rest)
          (svl-run-cycles module-name in-names (strip-cdrs in-vals)
                          (strip-cdrs out-sigs) next-delayed-env svl-modules)))
      (mv valid (svl-run-cycles-output out-env-wires rest)))))

(defun svl-run1 (module-name inputs outputs svl-design)
  (declare (xargs :mode :program))
  (b* (((mv valid outs) (svl-run-cycles module-name
                                           (strip-cars inputs)
                                           (strip-cdrs inputs)
                                           outputs
                                           nil
                                           svl-design
                                           ))
       #|((svl-env env) env)||#
       #|(outputs (hons-gets (svl-module->outputs (cdr (hons-get module-name
       svl-design)))
       env.wires))||#)
    (mv valid outs)))||#

(defun svl-run (module-name inputs  svl-design)
;(declare (xargs :mode :program))
  (b* (((mv res next-delayed-env)
        (svl-run-cycle module-name
                       inputs
                       (make-svl-env)
                       svl-design))
       (- (svl-free-env module-name next-delayed-env svl-design 1000000)))
    (mv  res next-delayed-env)))

(encapsulate
  nil

  (defun svl-fix-fast-alists-module (module)
    (b* (((svl-module module) module))
      (progn$
       (make-fast-alist module.listeners)
       (make-fast-alist module.occs)
       nil)))

  (defun svl-fix-fast-alists-design (svl-design)
    (if (atom svl-design)
        nil
      (progn$
       (svl-fix-fast-alists-module (cdar svl-design))
       (svl-fix-fast-alists-design (cdr svl-design)))))

  (defun svl-fix-fast-alists (svl-design)
    (progn$
     (svl-fix-fast-alists-design svl-design)
     (make-fast-alist svl-design))))

(encapsulate
  nil

  (defun svl-copy-module (module)
    (b* (((svl-module module) module))
      (change-svl-module
       module
       :occs (svl-to-fast-alist module.occs)
       :listeners (svl-to-fast-alist module.listeners))))

  (defun svl-copy-design (svl-design)
    (if (atom svl-design)
        nil
      (hons-acons
       (caar svl-design)
       (svl-copy-module (cdar svl-design))
       (svl-copy-design (cdr svl-design))))))

#|

(time$
 (svl-run
  "Multiplier_15_0_1000"
 '(45 55)
 (svl-copy-design *mult-svl-design*))) ;;33,847,616: 0.13 sec; new= 0.02 sec 11,583,120

(time$
 (svl-run "mul_test1"
 '(6 5)
 (svl-copy-design *booth-svl-design*)))

(svl-run1 "mul_test1"
 '(("mr"  6 7 8)
   ("md" 5 6 8))
 '((out1 out2 out3))
 *booth-svl-design*)

(svl-run1 "COUNTER"
 '(("Clock"  0 1 0 1 0 1)
   ("Reset" 1 1 0 1 1 1)
   ("Enable" 0 0 0 0 0 0)
   ("Load" 0 1 0 0 1 1)
   ("Mode" 0 0 0 0 0 0)
   ("Data" 10 20 30 40 50 60))
 '((out1 out2 out3 out4 out5 out6))
 *counter-svl-design*)

(time$
 (svl-run "booth2_reduction_dadda_17x65_97"
 '(0 0 0)
 (svl-copy-design *big-svl-design*)))

(time$

 (b* (((mv & res &) (svl-run "booth2_reduction_dadda_17x65_97"
                             '(2047 2047 2047)
                          (svl-copy-design *big-svl-design*))))
  (bits 9 1 (car res))))

(time$
 (svl-run "Mult_64_64"
 '(45 55)
 (svl-copy-design *signed64-svl-design*))) ;;0.11 42,714,944

(time$
 (svl-run "Mult_128_128"
  '(45 55)
   ;'(("Out" "result"))
   (svl-copy-design *signed128-svl-design*))) ;;0,42 sec: 176,864,400

(svl-run-cycle "COUNTER"
               (svl-to-fast-alist '(("Clock" . 0)
                                    ("Reset" . 1)
                                    ("Enable" . 0)
                                    ("Load" . 1)
                                    ("Mode" . 0)
                                    ("Count" . 35)
                                    ("Data" . 100)))
               (svl-to-fast-alist '(("Clock" . 1)
                                    ("Reset" . 1)
                                    ("Enable" . 0)
                                    ("Load" . 1)
                                    ("Mode" . 0)
                                    ("Data" . 100)))
               *counter-svl-design*)

(svl-run-cycle "test"
               nil
               (svl-to-fast-alist '(("data" . 255)))
               *test-svl-design*)

(b* (((mv valid env)
      (svl-run-cycle "mul_test1"
                     nil
                     (svl-to-fast-alist '(("mr" . 6)
                                          ("md" . 5)))
                     *booth-svl-design*)))
  (mv valid (hons-get "result" env)))

(svl-run-cycle "booth_encoder"
               nil
               (svl-to-fast-alist '(("mr" . 3)
                                    ("md" . 3)))
               *booth-svl-design*)

(svl-run-cycle "wallace"
               nil
               (svl-to-fast-alist '(("r0" . 205)
                                    ("r1" . 14)
                                    ("r2" . 12)
                                    ("r3" . 0)))
               *booth-svl-design*)

(time$
 (b* (((mv valid env)
      (svl-run-cycle "Multiplier_15_0_1000"
                     nil
                     (svl-to-fast-alist '(("IN1" . -45)
                                          ("IN2" . 55)))
                     *mult-svl-design*)))
  (mv valid (hons-get "P" env))))

(time$
 (b* (((mv valid env)
      (svl-run-cycle "Mult_64_64"
                     nil
                     (svl-to-fast-alist '(("IN1" . 45)
                                          ("IN2" . 55)))
                     *signed64-svl-design*)))
  (mv valid (hons-get "Out" env))))

(time$
 (b* (((mv valid env)
      (svl-run-cycle "Mult_128_128"
                     nil
                     (svl-to-fast-alist '(("IN1" . 45)
                                          ("IN2" . 55)))
                     *signed128-svl-design*)))
  (mv valid (hons-get "Out" env))))

(time$
 (b* (((mv valid env)
      (svl-run-cycle "booth2_reduction_dadda_17x65_97"
                     nil
                     (svl-to-fast-alist '(("partial_products" . 0)
                                          ("partial_product_increments" . 0)
                                          ("partial_product_signs" . 0)))
                     *big-svl-design*)))
  (mv valid (hons-get "product_terms" env))))

(time$
 (b* (((mv valid env)
      (svl-run-cycle "booth2_reduction_dadda_17x65_97"
                     nil
                     (svl-to-fast-alist '(("partial_products" . 13221312312321)
                                          ("partial_product_increments" . 43423423432432)
                                          ("partial_product_signs" . 423432432)))
                     *big-svl-design*)))
  (mv valid (hons-get "product_terms" env))))

(gl::gl-thm booth-svl-correct
    :hyp (and (booth-test-vector-autohyps))
    :concl (equal (cdr (assoc 'res (sv::svtv-run (booth-test-vector)
                                             (booth-test-vector-autoins))))
                  (cdr (b* (((mv & env)
                             (svl-run-cycle "mul_test1"
                                            nil
                                            (svl-to-fast-alist '(("mr" . IN1)
                                                                 ("md" . IN2)))
                                            *booth-svl-design*)))
                         (hons-get "result" env))))
    :g-bindings (booth-test-vector-autobinds))

||#

#|(skip-proofs
 (progn
   (verify-termination SVL-UPDATE-VALUE)
   (verify-termination SVL-RUN-SAVE-ASSIGN-RESULT)
   (verify-termination SVL-RUN-SAVE-MODULE-RESULT)
   (verify-termination SVL-RUN-ADD-DELAYED-INS)
   (verify-termination SVL-RUN-EXTEND-OCC-ENV)
   (verify-termination SVL-RUN-INITIALIZE-WIRES)
   (verify-termination SVL-RUN-ADD-TO-QUEUE)
   (verify-termination svl-run-get-queue)
   (verify-termination svl-run-cycle)))||#

(defun find-dont-care-bits (val size)
  (if (zp size)
      nil
    (b* ((size (1- size))
         (bit-val (sv::4vec-part-select size 1 val))
         (rest (find-dont-care-bits val size)))
      (if (equal bit-val '(1 . 0))
          (cons size rest)
        rest))))

(defun hons-get-val (key alist)
  (declare (xargs :guard t))
  (cdr (hons-get key alist)))

(memoize 'svl-module-alist-p)
