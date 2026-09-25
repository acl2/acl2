; ARM32 model test harness
; for running the ARM32 model on concrete test vectors
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric McCarthy (mccarthy@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ARM")

;; This book runs the ARM32 model on test vectors (see vectors.lisp).  For each
;; vector, it puts the state into the vector's initial configuration, executes
;; one instruction, and compares the result with the vector's expectations.
;; The entry point is run-vectors, at the end.  See smoke.lisp for examples.

(include-book "../../top") ; the ARM32 model
(include-book "vectors")
(include-book "unknown-values")
(include-book "std/util/bstar" :dir :system)
(local (include-book "kestrel/bv/unsigned-byte-p" :dir :system))
(local (include-book "kestrel/bv-lists/unsigned-byte-listp" :dir :system))
(local (include-book "kestrel/alists-light/alistp" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Loading a vector into the state.

;; Sets registers I through 15 to 0.
(defun clear-regs (i arm)
  (declare (xargs :guard (and (natp i) (<= i 16))
                  :stobjs arm
                  :measure (nfix (- 16 i))))
  (if (zp (- 16 i))
      arm
    (let ((arm (set-reg i 0 arm)))
      (clear-regs (+ 1 i) arm))))

;; Sets the registers given in ALIST.
(defun set-regs (alist arm)
  (declare (xargs :guard (reg-alistp alist) :stobjs arm))
  (if (endp alist)
      arm
    (let ((arm (set-reg (caar alist) (cdar alist) arm)))
      (set-regs (cdr alist) arm))))

;; Stores WORDS at consecutive addresses starting at ADDR.
(defun write-words (addr words arm)
  (declare (xargs :guard (and (addressp addr)
                              (acl2::unsigned-byte-listp 32 words))
                  :stobjs arm))
  (if (endp words)
      arm
    (let ((arm (write 4 addr (car words) arm)))
      (write-words (bvplus 32 4 addr) (cdr words) arm))))

;; Stores each (address size value) triple in TRIPLES.
(defun write-mem-triples (triples arm)
  (declare (xargs :guard (mem-triple-listp triples) :stobjs arm))
  (if (endp triples)
      arm
    (let* ((triple (car triples))
           (arm (write (second triple) (first triple) (third triple) arm)))
      (write-mem-triples (cdr triples) arm))))

;; Puts the state into the initial configuration described by VEC, with FILLING
;; as the source of UNKNOWN values (see unknown-values.lisp).  Every field of
;; the state except memory is set (see load-vector-of-update-nth), so the state
;; need not be fresh, but memory must be zero except where VEC stores to it
;; (see unload-vector).
(defun load-vector (vec filling arm)
  (declare (xargs :guard (and (test-vectorp vec) (unsigned-byte-p 32 filling))
                  :stobjs arm))
  (b* ((arm (clear-regs 0 arm))
       (arm (set-regs (vec-get :regs vec nil) arm))
       (arm (set-reg *pc* (vec-get :pc vec 0) arm))
       (arm (update-apsr (vec-get :apsr vec 0) arm))
       (arm (update-isetstate *InstrSet_ARM* arm))
       (arm (update-itstate 0 arm))
       (arm (update-endianstate 0 arm))
       (arm (update-error nil arm))
       (arm (update-arch-version (vec-get :arch vec 7) arm))
       (arm (update-library-map nil arm))
       (arm (set-unknown-filling filling arm))
       (arm (write-words (vec-get :pc vec 0) (vec-get :code vec nil) arm))
       (arm (write-mem-triples (vec-get :mem vec nil) arm)))
    arm))

;; Zeroes the memory described by TRIPLES.
(defun zero-mem-triples (triples arm)
  (declare (xargs :guard (mem-triple-listp triples) :stobjs arm))
  (if (endp triples)
      arm
    (let* ((triple (car triples))
           (arm (write (second triple) (first triple) 0 arm)))
      (zero-mem-triples (cdr triples) arm))))

;; Zeroes the memory VEC mentions: its code and the addresses of its :mem
;; triples, initial and expected.  This makes all of memory zero again unless
;; the model stored somewhere else, which the checks below do not detect.
(defun unload-vector (vec arm)
  (declare (xargs :guard (test-vectorp vec) :stobjs arm))
  (b* ((arm (write (* 4 (len (vec-get :code vec nil))) (vec-get :pc vec 0) 0 arm))
       (arm (zero-mem-triples (vec-get :mem vec nil) arm))
       (arm (zero-mem-triples (vec-get :mem (vec-get :expect vec nil) nil) arm)))
    arm))

;; Load-vector sets every field of the state except memory, so its result does
;; not depend on the other fields of its input, which is what lets all the
;; vectors in a run share one state.  If a field is added to the state, the
;; proof below fails until load-vector sets that field too.
(encapsulate ()
  (local (include-book "kestrel/lists-light/take" :dir :system))
  (local (include-book "kestrel/lists-light/append" :dir :system))
  (local (include-book "kestrel/lists-light/repeat" :dir :system))
  (local (include-book "kestrel/lists-light/update-nth" :dir :system))

  (local
    (defthm true-listp-when-registersp
      (implies (registersp x)
               (true-listp x))
      :hints (("Goal" :in-theory (enable registersp)))))

  ;; The facts the proof needs from armp, stated for a variable so that armp
  ;; is never opened on an update-nth (which splits on every field).
  (local
    (defthm armp-facts
      (implies (armp x)
               (and (equal (len x) 10)
                    (true-listp (nth *registersi* x))
                    (equal (len (nth *registersi* x)) 16)))
      :rule-classes nil
      :hints (("Goal" :in-theory (enable armp)))))

  (local
    (defthm clear-regs-rewrite
      (implies (and (natp k)
                    (<= k 16)
                    (true-listp (nth *registersi* arm))
                    (equal (len (nth *registersi* arm)) 16))
               (equal (clear-regs k arm)
                      (update-nth *registersi*
                                  (append (take k (nth *registersi* arm))
                                          (acl2::repeat (- 16 k) 0))
                                  arm)))
      :hints (("Goal" :in-theory (enable set-reg update-registersi
                                         acl2::repeat-opener)))))

  ;; Moves an update of a variable field outward past an update of a constant
  ;; field, or drops it if the fields are the same.  The rules below carry it
  ;; on outward until the operation that sets that field drops it.
  (local
    (defthm update-nth-of-update-nth-when-quotep
      (implies (and (syntaxp (and (quotep j) (not (quotep i))))
                    (natp i)
                    (natp j))
               (equal (update-nth j x (update-nth i v l))
                      (if (equal i j)
                          (update-nth j x l)
                        (update-nth i v (update-nth j x l)))))))

  ;; It would move updates the other way.
  (local (in-theory (disable acl2::update-nth-of-update-nth-diff)))

  (local
    (defthm set-regs-of-update-nth
      (implies (and (natp i) (not (equal i *registersi*)))
               (equal (set-regs alist (update-nth i v arm))
                      (update-nth i v (set-regs alist arm))))
      :hints (("Goal" :in-theory (enable set-reg update-registersi)))))

  (local
    (defthm write-of-update-nth
      (implies (and (natp i) (not (equal i *memoryi*)))
               (equal (write n addr val (update-nth i v arm))
                      (update-nth i v (write n addr val arm))))
      :hints (("Goal" :in-theory (enable write write-byte update-memoryi)))))

  (local
    (defthm write-words-of-update-nth
      (implies (and (natp i) (not (equal i *memoryi*)))
               (equal (write-words addr words (update-nth i v arm))
                      (update-nth i v (write-words addr words arm))))))

  (local
    (defthm write-mem-triples-of-update-nth
      (implies (and (natp i) (not (equal i *memoryi*)))
               (equal (write-mem-triples triples (update-nth i v arm))
                      (update-nth i v (write-mem-triples triples arm))))))

  (defthm load-vector-of-update-nth
    (implies (and (armp arm)
                  (armp (update-nth i v arm))
                  (natp i)
                  (not (equal i *memoryi*)))
             (equal (load-vector vec filling (update-nth i v arm))
                    (load-vector vec filling arm)))
    :rule-classes nil
    :hints (("Goal" :use ((:instance armp-facts (x arm))
                          (:instance armp-facts (x (update-nth i v arm))))
             :cases ((equal i *registersi*))
             :in-theory (e/d (set-reg update-registersi
                              update-apsr update-isetstate update-itstate
                              update-endianstate update-error
                              update-arch-version update-library-map
                              update-oracle)
                             (acl2::update-nth-becomes-append
                              acl2::cdr-of-update-nth
                              len default-car default-cdr))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Checking the state after the step.

;; A mismatch is a list (FIELD :expected EXPECTED :actual ACTUAL), where FIELD
;; is :error, :pc, :apsr, (:reg I), or (:mem ADDR).  The checks below return
;; lists of mismatches, which are therefore alists from fields.

;; Returns a list of the mismatch on FIELD, or nil if EXPECTED and ACTUAL agree.
(defun compare-field (field expected actual)
  (declare (xargs :guard t))
  (if (equal expected actual)
      nil
    (list (list field :expected expected :actual actual))))

;; The expected value of register I after the step: its entry in
;; EXPECT-REGS if there is one, else its entry in INITIAL-REGS, else 0.
(defun expected-reg (i expect-regs initial-regs)
  (declare (xargs :guard (and (natp i)
                              (reg-alistp expect-regs)
                              (reg-alistp initial-regs))))
  (let ((pair (assoc i expect-regs)))
    (if (consp pair)
        (cdr pair)
      (let ((pair (assoc i initial-regs)))
        (if (consp pair)
            (cdr pair)
          0)))))

;; Compares registers I through 14 against their expected values.  The program
;; counter is checked separately.
(defun check-regs (i expect-regs initial-regs arm)
  (declare (xargs :guard (and (natp i)
                              (<= i 15)
                              (reg-alistp expect-regs)
                              (reg-alistp initial-regs))
                  :stobjs arm
                  :measure (nfix (- 15 i))))
  (if (zp (- 15 i))
      nil
    (append (compare-field (list :reg i)
                           (expected-reg i expect-regs initial-regs)
                           (reg i arm))
            (check-regs (+ 1 i) expect-regs initial-regs arm))))

(defthm alistp-of-check-regs
  (alistp (check-regs i expect-regs initial-regs arm)))

;; Compares memory against the expected (address size value) triples.
(defun check-mem (triples arm)
  (declare (xargs :guard (mem-triple-listp triples) :stobjs arm))
  (if (endp triples)
      nil
    (let ((triple (car triples)))
      (append (compare-field (list :mem (first triple))
                             (third triple)
                             (read (second triple) (first triple) arm))
              (check-mem (cdr triples) arm)))))

(defthm alistp-of-check-mem
  (alistp (check-mem triples arm)))

;; Compares the state after the step against the :expect part of VEC.
;; Returns a list of mismatches; nil means the test passed.
(defund check-vector (vec arm)
  (declare (xargs :guard (test-vectorp vec) :stobjs arm))
  (b* ((expect (vec-get :expect vec nil))
       (expected-error (vec-get :error expect nil))
       ((when (or expected-error (error arm)))
        (compare-field :error expected-error (error arm)))
       (mask (vec-get :apsr-mask expect #xF0000000)))
    (append (compare-field :pc (vec-get :pc expect nil) (pc arm))
            (check-regs 0 (vec-get :regs expect nil) (vec-get :regs vec nil) arm)
            (compare-field :apsr
                           (bvand 32 mask (vec-get :apsr expect 0))
                           (bvand 32 mask (apsr arm)))
            (check-mem (vec-get :mem expect nil) arm))))

(defthm alistp-of-check-vector
  (alistp (check-vector vec arm))
  :hints (("Goal" :in-theory (enable check-vector))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Running vectors.

;; The state is the arm stobj, which is declared :non-executable because its
;; memory is 4GB.  Even so, with-local-stobj can create a live one inside a
;; function (see run-vectors), and the memory is allocated lazily, so creating
;; one is cheap.  Retiring one costs the garbage collector about 5
;; milliseconds, though, so all the vectors in a run share one state, and
;; unload-vector erases each vector's memory before the next is loaded.

;; Runs the single instruction described by VEC under FILLING.  Returns (mv
;; mismatches arm).
(defun run-vector (vec filling arm)
  (declare (xargs :guard (and (test-vectorp vec) (unsigned-byte-p 32 filling))
                  :stobjs arm))
  (b* ((arm (load-vector vec filling arm))
       (arm (step arm))
       (mismatches (check-vector vec arm))
       (arm (unload-vector vec arm)))
    (mv mismatches arm)))

(local
  (defthm alistp-of-set-difference-equal
    (implies (alistp x)
             (alistp (set-difference-equal x y)))))

;; Splits the mismatches from two runs of one vector.  Returns (mv real
;; unknown-dependent): a mismatch reported identically by both runs is real,
;; and any other field that mismatched in either run depends on an UNKNOWN.
(defun classify-mismatches (mismatches-a mismatches-b)
  (declare (xargs :guard (and (alistp mismatches-a) (alistp mismatches-b))))
  (mv (intersection-equal mismatches-a mismatches-b)
      (union-equal (strip-cars (set-difference-equal mismatches-a mismatches-b))
                   (strip-cars (set-difference-equal mismatches-b mismatches-a)))))

;; Runs each vector in VECS under two fillings whose UNKNOWN values differ in
;; every bit (see unknown-values.lisp), and classifies the mismatches.  Returns
;; (mv real unknown-dependent arm), where REAL maps the :id of each vector with
;; real mismatches to those mismatches, and UNKNOWN-DEPENDENT maps the :id of
;; each vector with fields that depend on an UNKNOWN to those fields.
(defun run-vectors-aux (vecs arm)
  (declare (xargs :guard (test-vector-listp vecs) :stobjs arm))
  (if (endp vecs)
      (mv nil nil arm)
    (b* ((vec (car vecs))
         ((mv mismatches-a arm) (run-vector vec 0 arm))
         ((mv mismatches-b arm) (run-vector vec #xFFFFFFFF arm))
         ((mv real unknown) (classify-mismatches mismatches-a mismatches-b))
         ((mv reals unknowns arm) (run-vectors-aux (cdr vecs) arm))
         (id (vec-get :id vec "")))
      (mv (if real (cons (cons id real) reals) reals)
          (if unknown (cons (cons id unknown) unknowns) unknowns)
          arm))))

;; Runs VECS on a fresh state.  Returns (mv real unknown-dependent) as for
;; run-vectors-aux; all vectors passed if both are nil.
(defun run-vectors (vecs)
  (declare (xargs :guard (test-vector-listp vecs)))
  (with-local-stobj arm
    (mv-let (real unknown-dependent arm)
      (run-vectors-aux vecs arm)
      (mv real unknown-dependent))))
