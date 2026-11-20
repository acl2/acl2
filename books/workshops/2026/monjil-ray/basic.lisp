; MIT License
;
; Copyright (c) 2026 Mohammad Bin Monjil and Sandip Ray
;
; Permission is hereby granted, free of charge, to any person obtaining a copy
; of this software and associated documentation files (the "Software"), to deal
; in the Software without restriction, including without limitation the rights
; to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
; copies of the Software, and to permit persons to whom the Software is
; furnished to do so, subject to the following conditions:
;
; The above copyright notice and this permission notice shall be included in all
; copies or substantial portions of the Software.
;
; THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
; IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
; FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
; AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
; LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
; OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
; SOFTWARE.


(in-package "ACL2")
(include-book "model")



(defthm memberp-of-remove1-equal-when-uniquep
  (implies
   (and
    (uniquep xs)
    (memberp a xs))
   (not
    (memberp a
             (remove1-equal a xs)))))


(defthm memberp-of-remove1-equal-implies-memberp
  (implies
   (memberp a
            (remove1-equal b xs))
   (memberp a xs)))






(defthm memberp-remove1-equal-different
  (implies
   (and
    (memberp a xs)
    (not (equal a b)))
   (memberp a
            (remove1-equal b xs))))



(defthm memberp-self-remove1-equal-impossible-when-uniquep
  (implies
   (uniquep xs)
   (not
    (memberp a
             (remove1-equal a xs)))))



(defthm not-equal-when-memberp-and-not-memberp-same-list
  (implies
   (and
    (memberp x xs)
    (not (memberp y xs)))
   (not (equal x y)))
  :hints
  (("Goal"
    :cases ((equal x y)))))



(defthm uniquep-of-cdr
  (implies
   (uniquep xs)
   (uniquep (cdr xs))))


(defthm not-memberp-car-cdr-when-uniquep
  (implies
   (and
    (consp xs)
    (uniquep xs))
   (not (memberp (car xs) (cdr xs)))))


(defthm memberp-cdr-when-memberp-and-not-equal-car
  (implies
   (and
    (memberp x xs)
    (not (equal x (car xs))))
   (memberp x (cdr xs))))


(defthm memberp-when-memberp-and-subset
  (implies
   (and
    (memberp x xs)
    (subset xs ys))
   (memberp x ys)))


(defthm cut-not-taken-remove1-member-implies-different
  (implies
   (and
    (not (memberp i xs))
    (memberp k
             (remove1-equal k xs)))
   (not (equal k i))))



(defthm memberp-subset
    (implies (and (memberp j x)
		  (subsetp x y))
	     (memberp j y)))





(defthm memberp-of-remove1-equal-implies-memberp
  (implies
   (memberp a
            (remove1-equal b xs))
   (memberp a xs)))


(defthm memberp-remove1-equal-different
  (implies
   (and
    (memberp a xs)
    (not (equal a b)))
   (memberp a
            (remove1-equal b xs))))



(defthm memberp-self-remove1-equal-impossible-when-uniquep
  (implies
   (uniquep xs)
   (not
    (memberp a
             (remove1-equal a xs)))))



(defthm memberp-of-remove1-equal-when-uniquep
  (implies
   (and
    (uniquep xs)
    (memberp a xs))
   (not
    (memberp a
             (remove1-equal a xs)))))


(defthm not-memberp-after-remove1-equal-when-uniquep
  (implies
   (uniquep xs)

   (not
    (memberp
     x
     (remove1-equal x xs)))))

(defthm
  not-memberp-of-remove1-equal-when-not-memberp

  (implies
   (and
    (true-listp xs)
    (not (memberp j xs)))

   (not
    (memberp j
             (remove1-equal i xs)))))

;; ------------------------------------------------------------
;; Removing one occurrence from a proper list produces another
;; proper list.
;; ------------------------------------------------------------

(defthm
  cl-true-listp-of-remove1-equal

  (implies
   (true-listp xs)

   (true-listp
    (remove1-equal x xs))))


(defthm
  uniquep-of-remove1-equal

  (implies
   (uniquep xs)

   (uniquep
    (remove1-equal x xs))))


(defthm subset-of-remove1-equal
  (implies
   (subset x y)
   (subset (remove1-equal a x)
           y)))


(defthm cl-not-memberp-of-remove1-equal-same
  (implies
   (uniquep xs)
   (not (memberp a
                 (remove1-equal a xs)))))


(defthm cl-memberp-from-subset
  (implies
   (and
    (subset xs ys)
    (memberp x xs))
   (memberp x ys)))


(defthm not-memberp-of-remove-from-list-when-not-memberp
  (implies
   (not (memberp y xs))
   (not (memberp y
                 (remove-from-list xs x)))))


(defthm uniquep-of-remove-from-list
  (implies
   (uniquep xs)
   (uniquep (remove-from-list xs x))))

;; ------------------------------------------------------------
;; Reading :NBRS-FROM after replacing one process.
;; ------------------------------------------------------------

(defthm nbrs-from-of-g-of-set-proc
  (equal
   (g :nbrs-from
      (g k
         (s i p procs)))

   (if (equal k i)
       (g :nbrs-from p)
     (g :nbrs-from
        (g k procs))))

  :hints
  (("Goal"
    :cases
    ((equal k i)))))




(defthm proc-ids-of-system-step
  (equal
   (proc-ids
    (system-step st input))
   (proc-ids st)))


(defthm nbrs-from-of-g-of-system-step
  (equal
   (nbrs-from
    (g k
       (procs
        (system-step st input))))

   (nbrs-from
    (g k
       (procs st)))))



(defun no-recovery-step-p (input st)
  (and
   (not (any-process-recovering-p st))
   (not (equal (ttype input) :recover))
   (implies
    (equal (ttype input) :receive)
    (not
     (equal
      (msg-type
       (get-msg-from-channel
        (sender input)
        (pid input)
        (channels st)))
      :recovery)))))

(defun no-recovery-segment-p (inputs st)
  (if (endp inputs)
      t
    (let* ((input   (first inputs))
           (st-next (system-step st input)))
      (and
       (no-recovery-step-p input st)
       (no-recovery-segment-p
        (rest inputs)
        st-next)))))



;; ------------------------------------------------------------
;; Read :PROC-STATUS after updating FIELD of process I.
;; ------------------------------------------------------------

(defthm proc-status-of-g-after-proc-field-update
  (equal
   (g :proc-status
      (g k
         (s i
            (s field
               value
               (g i procs))
            procs)))

   (if (equal k i)
       (if (equal field :proc-status)
           value
         (g :proc-status
            (g i procs)))
     (g :proc-status
        (g k procs))))

  :hints
  (("Goal"
    :cases
    ((equal k i)
     (equal field :proc-status)))))


;; ------------------------------------------------------------
;; Updating one field of one process cannot introduce a
;; ------------------------------------------------------------

(defthm
  any-proc-recovering-p-preserved-by-non-recovering-proc-update

  (implies
   (and
    (not
     (any-proc-recovering-p
      ids
      procs))

    (or
     (not
      (equal field
             :proc-status))

     (not
      (equal value
             :recovering))))

   (not
    (any-proc-recovering-p
     ids
     (s i
        (s field
           value
           (g i procs))
        procs)))))



;; ------------------------------------------------------------
;; Reading :PROC-STATUS after replacing process I.
;; ------------------------------------------------------------

(defthm proc-status-of-g-of-set-proc
  (equal
   (g :proc-status
      (g k
         (s i p procs)))

   (if (equal k i)
       (g :proc-status p)
     (g :proc-status
        (g k procs))))

  :hints
  (("Goal"
    :cases
    ((equal k i)))))


;; ------------------------------------------------------------
;; Replacing process I does not affect whether any process is recovering, provided the replacement has the same :PROC-STATUS as the old process.
;; ------------------------------------------------------------

(defthm
  any-proc-recovering-p-of-set-proc-same-status

  (implies
   (equal
    (g :proc-status p)
    (g :proc-status
       (g i procs)))

   (equal
    (any-proc-recovering-p
     ids
     (s i p procs))

    (any-proc-recovering-p
     ids
     procs))))


;; ------------------------------------------------------------
;; A step classified as NO-RECOVERY-STEP-P cannot introduce a recovering process.
;; ------------------------------------------------------------

(defthm no-recovery-step-p-preserves-no-proc-recovering
  (implies
   (no-recovery-step-p
     input
     st)

   (not
    (any-proc-recovering-p
     (proc-ids st)
     (procs
      (system-step st input))))))




;; ------------------------------------------------------------
;; RUN-IMP preserves process IDs.
;; ------------------------------------------------------------

(defthm proc-ids-of-run-imp
  (equal
   (proc-ids
    (run-imp st inputs))
   (proc-ids st)))




;; ------------------------------------------------------------
;; Running an appended sequence is the same as first running
;; the prefix and then running the suffix.
;; ------------------------------------------------------------

(defthm run-imp-of-append
  (equal
   (run-imp st (append xs ys))

   (run-imp
    (run-imp st xs)
    ys))

  :hints
  (("Goal"
    :induct
    (run-imp st xs)

    :in-theory
    (disable system-step))))


(defthm
  legal-input-sequencep-of-append-implies-second

  (implies
   (legal-input-sequencep
    st
    (append inputs-1 inputs-2))

   (legal-input-sequencep
    (run-imp st inputs-1)
    inputs-2))
  :hints
  (("Goal"
    :in-theory (disable
		system-step
		legal-inputp))))
