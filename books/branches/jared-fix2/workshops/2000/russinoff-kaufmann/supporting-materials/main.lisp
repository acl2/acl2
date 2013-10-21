(in-package "ACL2")

; Need to define the "*" package, before (certify-book "main" 7):
; (ld "packages.lisp")

; Include the "*" model.
(include-book "constants")

; Include input-assumptions.
(include-book "inputs")

; Here is the desired relation between input and output, given appropriate
; constraints on other signals.
(defun result (in out)
  (equal out
         (logand (logand (bitn in 0) (bitn in 1))
                 (logand (bitn in 2) (bitn in 3)))))

; We sometimes assume the following relationships between inputs in our two
; models.  Eventually we will functionally instantiate the "*" functions with
; the "ACL2" functions, removing any such assumption from our main result.
(defmacro bindings (n)
  `(and (equal (*::longop) (longop ,n))
        (equal (*::in) (in ,n))))

; The following definition of spec states what must be true of the inputs in
; the "*" model in order to prove the desired result for the "*" model
; (spec-lemma-2 below).  It should be straightforward that spec holds of the
; "ACL2" model inputs (spec-lemma-1).

(defun spec (in longop)
  (declare (ignore in))
  (equal longop 1))

; This should be easy.
(defthm spec-lemma-1
  (implies (input-assumptions n)
           (spec (in n) (longop n))))

; Here is where all the effort goes, in general.  For our toy model the proof
; is very easy simply by enabling all the "*" functions.
(defthm spec-lemma-2
  (implies (spec (*::in) (*::longop))
           (result (*::in) (*::out)))
  :hints (("Goal" :in-theory
           (enable *::S01 *::S01_MUXED *::S01_MUXED_FLOPPED
                   *::S23 *::S23_FLOPPED *::S0123
                   *::LONGOP_FLOPPED *::OUT))))

; The rest of our development requires only the above facts about the functions
; we now disable, together with pipeline-lemma below.
(in-theory (disable result input-assumptions spec))

(encapsulate
 ()
 (local (include-book "pipe"))
 (defthm pipeline-lemma
   (implies (and (input-assumptions n)
                 (bindings n))
            (equal (out (+ 2 n)) (*::out)))
   :hints (("Goal"
            :use ((:definition input-assumptions*))))))

(defthm lemma-to-be-instantiated
  (implies (and (input-assumptions n)
                (bindings n)
                (spec (*::in) (*::longop)))
           (result (*::in)
                   (out (+ 2 n)))))

(defthm correctness-of-pipeline
  (implies (input-assumptions n)
           (result (in n)
                   (out (+ 2 n))))
  :hints (("Goal" :use ((:instance
                         (:functional-instance
                          lemma-to-be-instantiated
                          (*::in     (lambda () (in k)))
                          (*::longop (lambda () (longop k))))
                         (k n))))))
