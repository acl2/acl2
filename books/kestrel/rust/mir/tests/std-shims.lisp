; Rust Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "RUST")

(include-book "aes-constructs") ; for the interpreter and
                                ; the body-building macros

; Known-answer tests of the standard library shims:
; unit-level tests calling the shims on values directly
; (with a small fixture frame stack where references are involved),
; and a whole-program test whose MIR body drives
; a for-loop through the Range iterator shims.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro u32v (n)
  `(value-uint ,n (uint-type-u32)))

(defmacro u8v (n)
  `(value-uint ,n (uint-type-u8)))

(defmacro usizev (n)
  `(value-uint ,n (uint-type-usize)))

; A fixture: one frame whose local 0 holds an array of four u32s,
; and a slice reference covering all of it.

(defconst *fix-array*
  (value-array (list (u32v 10) (u32v 20) (u32v 30) (u32v 40))))

(defconst *fix-frames*
  (list (make-frame :fn "fixture"
                    :locals (list *fix-array*)
                    :cur-block 0
                    :cur-stmt 0
                    :dest (irr-place)
                    :target 0)))

(defconst *fix-addr*
  (make-address :frame 0 :local 0 :path nil))

(defconst *fix-sref*
  (value-slice-ref *fix-addr* 0 4))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Machine integers.

(assert-event
 (equal (mv-list 2 (exec-shim "u32::wrapping_add"
                              (list (u32v 4294967295) (u32v 2))
                              nil))
        (list (u32v 1) nil)))

(assert-event
 (equal (mv-list 2 (exec-shim "u32::wrapping_sub"
                              (list (u32v 0) (u32v 1))
                              nil))
        (list (u32v 4294967295) nil)))

(assert-event
 (equal (mv-list 2 (exec-shim "u32::rotate_right"
                              (list (u32v 1) (u32v 8))
                              nil))
        (list (u32v 16777216) nil)))

(assert-event
 (equal (mv-list 2 (exec-shim "u32::from_le_bytes"
                              (list (value-array (list (u8v 1) (u8v 2)
                                                       (u8v 3) (u8v 4))))
                              nil))
        (list (u32v 67305985) nil)))

(assert-event
 (equal (mv-list 2 (exec-shim "u32::to_le_bytes"
                              (list (u32v 67305985))
                              nil))
        (list (value-array (list (u8v 1) (u8v 2) (u8v 3) (u8v 4))) nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Slices: length, element indexing (with a bounds panic),
; range indexing, and window copying.

(assert-event
 (equal (mv-list 2 (exec-shim "slice::len" (list *fix-sref*) *fix-frames*))
        (list (usizev 4) *fix-frames*)))

; slice::index returns a reference to the element;
; loading it yields the element.

(assert-event
 (b* (((mv result &) (exec-shim "slice::index"
                                (list *fix-sref* (usizev 2))
                                *fix-frames*))
      ((when (fty::reserrp result)) nil)
      ((unless (value-case result :ref)) nil))
   (equal (load-address (value-ref->address result) *fix-frames*)
          (u32v 30))))

(assert-event
 (b* (((mv result &) (exec-shim "slice::index"
                                (list *fix-sref* (usizev 9))
                                *fix-frames*)))
   (and (fty::reserrp result)
        (eq (car (fty::reserr->info result)) :panic))))

; slice::index_range yields a subwindow; its elements check out.

(assert-event
 (b* (((mv result &) (exec-shim "slice::index_range"
                                (list *fix-sref*
                                      (value-variant 0 (list (usizev 1)
                                                             (usizev 3))))
                                *fix-frames*))
      ((when (fty::reserrp result)) nil))
   (equal (slice-window-elems result *fix-frames*)
          (list (u32v 20) (u32v 30)))))

; copy_from_slice overwrites the destination window in place.

(assert-event
 (b* ((dest-frames
       (list (make-frame :fn "fixture"
                         :locals (list (value-array (list (u32v 0) (u32v 0)
                                                          (u32v 0) (u32v 0)))
                                       *fix-array*)
                         :cur-block 0
                         :cur-stmt 0
                         :dest (irr-place)
                         :target 0)))
      (dest-sref (value-slice-ref (make-address :frame 0 :local 0 :path nil)
                                  0 4))
      (src-sref (value-slice-ref (make-address :frame 0 :local 1 :path nil)
                                 0 4))
      ((mv result new-frames)
       (exec-shim "slice::copy_from_slice"
                  (list dest-sref src-sref)
                  dest-frames))
      ((when (fty::reserrp result)) nil))
   (equal (load-address (make-address :frame 0 :local 0 :path nil)
                        new-frames)
          *fix-array*)))

; try_into_array4 and unwrap.

(assert-event
 (equal (mv-list 2 (exec-shim "slice::try_into_array4"
                              (list *fix-sref*)
                              *fix-frames*))
        (list (value-variant 0 (list *fix-array*)) *fix-frames*)))

(assert-event
 (equal (mv-list 2 (exec-shim "Result::unwrap"
                              (list (value-variant 0 (list (u32v 7))))
                              nil))
        (list (u32v 7) nil)))

(assert-event
 (b* (((mv result &) (exec-shim "Result::unwrap"
                                (list (value-variant 1 (list (value-unit))))
                                nil)))
   (and (fty::reserrp result)
        (eq (car (fty::reserr->info result)) :panic))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The iterator protocol at the unit level:
; a (2..4) range held in a frame local, advanced through a reference.

(defconst *range-frames*
  (list (make-frame :fn "fixture"
                    :locals (list (value-variant 0 (list (usizev 2)
                                                         (usizev 4))))
                    :cur-block 0
                    :cur-stmt 0
                    :dest (irr-place)
                    :target 0)))

(defconst *range-ref*
  (value-ref (make-address :frame 0 :local 0 :path nil)))

(assert-event
 (b* (((mv result new-frames)
       (exec-shim "Range::next" (list *range-ref*) *range-frames*))
      ((when (fty::reserrp result)) nil)
      ((unless (equal result (mk-some (usizev 2)))) nil)
      ((mv result new-frames)
       (exec-shim "Range::next" (list *range-ref*) new-frames))
      ((when (fty::reserrp result)) nil)
      ((unless (equal result (mk-some (usizev 3)))) nil)
      ((mv result &)
       (exec-shim "Range::next" (list *range-ref*) new-frames)))
   (equal result (mk-none))))

; step_by: (8..72).step_by(32) yields 8, 40, then None
; (the key-schedule fold shape).

(assert-event
 (b* (((mv stepby &) (exec-shim "Iterator::step_by"
                                (list (value-variant 0 (list (usizev 8)
                                                             (usizev 72)))
                                      (usizev 32))
                                nil))
      ((when (fty::reserrp stepby)) nil)
      (frames (list (make-frame :fn "fixture"
                                :locals (list stepby)
                                :cur-block 0
                                :cur-stmt 0
                                :dest (irr-place)
                                :target 0)))
      (sref (value-ref (make-address :frame 0 :local 0 :path nil)))
      ((mv r1 frames1) (exec-shim "StepBy::next" (list sref) frames))
      ((when (fty::reserrp r1)) nil)
      ((unless (equal r1 (mk-some (usizev 8)))) nil)
      ((mv r2 frames2) (exec-shim "StepBy::next" (list sref) frames1))
      ((when (fty::reserrp r2)) nil)
      ((unless (equal r2 (mk-some (usizev 40)))) nil)
      ((mv r3 &) (exec-shim "StepBy::next" (list sref) frames2)))
   (equal r3 (mk-none))))

; rev over a range: (0..3).rev() yields 2, 1, 0.

(assert-event
 (b* ((frames (list (make-frame :fn "fixture"
                                :locals (list (value-variant
                                               0
                                               (list (usizev 0) (usizev 3))))
                                :cur-block 0
                                :cur-stmt 0
                                :dest (irr-place)
                                :target 0)))
      (rref (value-ref (make-address :frame 0 :local 0 :path nil)))
      ((mv r1 frames1) (exec-shim "Rev::next" (list rref) frames))
      ((unless (equal r1 (mk-some (usizev 2)))) nil)
      ((mv r2 frames2) (exec-shim "Rev::next" (list rref) frames1))
      ((unless (equal r2 (mk-some (usizev 1)))) nil)
      ((mv r3 frames3) (exec-shim "Rev::next" (list rref) frames2))
      ((unless (equal r3 (mk-some (usizev 0)))) nil)
      ((mv r4 &) (exec-shim "Rev::next" (list rref) frames3)))
   (equal r4 (mk-none))))

; Slice iteration: iter over the fixture array yields
; references to 10, 20, 30, 40.

(assert-event
 (b* (((mv iter &) (exec-shim "slice::iter" (list *fix-sref*) *fix-frames*))
      ((when (fty::reserrp iter)) nil)
      (frames (list (make-frame :fn "fixture"
                                :locals (list *fix-array* iter)
                                :cur-block 0
                                :cur-stmt 0
                                :dest (irr-place)
                                :target 0)))
      (iref (value-ref (make-address :frame 0 :local 1 :path nil)))
      ((mv r1 frames1) (exec-shim "Iter::next" (list iref) frames))
      ((when (fty::reserrp r1)) nil)
      ((unless (and (value-case r1 :variant)
                    (equal (value-variant->index r1) 1))) nil)
      (elem-ref (nth 0 (value-variant->fields r1)))
      ((unless (value-case elem-ref :ref)) nil))
   (equal (load-address (value-ref->address elem-ref) frames1)
          (u32v 10))))

; bitxor_assign writes through its reference.

(assert-event
 (b* ((frames (list (make-frame :fn "fixture"
                                :locals (list (u32v 5))
                                :cur-block 0
                                :cur-stmt 0
                                :dest (irr-place)
                                :target 0)))
      (xref (value-ref (make-address :frame 0 :local 0 :path nil)))
      ((mv result new-frames)
       (exec-shim "u32::bitxor_assign" (list xref (u32v 3)) frames))
      ((when (fty::reserrp result)) nil))
   (equal (load-address (make-address :frame 0 :local 0 :path nil)
                        new-frames)
          (u32v 6))))

; The panic entry points panic.

(assert-event
 (b* (((mv result &) (exec-shim "core::panicking::panic" nil nil)))
   (and (fty::reserrp result)
        (eq (car (fty::reserr->info result)) :panic))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; A whole program driving the shims through call terminators:
;
;   fn sum4() -> usize {
;       let mut s = 0;
;       for i in 0..4 { s += i; }
;       s
;   }
;
; in the MIR shape of a for loop: construct the Range,
; call Range::next through a &mut borrow each iteration,
; switch on the Option's discriminant,
; and read the payload through a downcast.
;
; Locals: _0: usize (s), _1: Range (the iterator),
;         _2: &mut Range, _3: Option<usize>,
;         _4: usize (discriminant), _5: usize (i).

(defconst *sum4-body*
  (make-body
   :locals (list (usize)
                 (ty-adt "Range")
                 (ty-ref (mutability-mut) (ty-adt "Range"))
                 (ty-adt "Option")
                 (usize)
                 (usize))
   :arg-count 0
   :blocks
   (list
    ;; bb0: _0 = 0; _1 = Range { 0, 4 }; goto bb1
    (make-basic-block
     :statements
     (list (assign-local 0 (rvalue-use (const-usize 0)))
           (assign-local 1
                         (rvalue-aggregate (agg-kind-adt "Range" 0)
                                           (list (const-usize 0)
                                                 (const-usize 4)))))
     :terminator (terminator-goto 1))
    ;; bb1: _2 = &mut _1; _3 = call Range::next(move _2) -> bb2
    (make-basic-block
     :statements
     (list (assign-local 2 (rvalue-ref (mutability-mut) (local-place 1))))
     :terminator (terminator-call
                  (operand-constant (const-fn "Range::next"))
                  (list (move-local 2))
                  (make-place :local 3 :projection nil)
                  2))
    ;; bb2: _4 = discriminant(_3); switch [1 -> bb3] otherwise bb4
    (make-basic-block
     :statements
     (list (assign-local 4 (rvalue-discriminant (local-place 3))))
     :terminator (terminator-switch-int
                  (move-local 4)
                  (make-switch-targets :values (list 1)
                                       :targets (list 3)
                                       :otherwise 4)))
    ;; bb3: _5 = ((_3 as Some).0); _0 = _0 + _5; goto bb1
    (make-basic-block
     :statements
     (list (assign-local 5
                         (rvalue-use
                          (operand-copy
                           (local-place 3
                                        (proj-elem-downcast 1)
                                        (proj-elem-field 0)))))
           (assign-local 0
                         (rvalue-binary-op (bin-op-add)
                                          (copy-local 0)
                                          (copy-local 5))))
     :terminator (terminator-goto 1))
    ;; bb4: return
    (make-basic-block
     :statements nil
     :terminator (terminator-return)))))

(defconst *sum4-program*
  (make-mir-program :funs (omap::update "sum4" *sum4-body* nil)
                    :adts nil))

(assert-event (mir-programp *sum4-program*))

; 0 + 1 + 2 + 3 = 6.

(assert-event
 (equal (run-fn "sum4" nil *sum4-program* 100000)
        (runout-done (usizev 6))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; A whole program reading through a slice window whose start
; is not zero -- the place shape (*w)[i] where w came from
; a range-indexing call, so the window start must offset the index:
;
;   fn win() -> u32 {
;       let a = [10u32, 20, 30, 40];
;       let s: &[u32] = &a;
;       let w: &[u32] = &s[1..3];
;       w[1]                        // a[2] = 30
;   }
;
; Locals: _0: u32, _1: [u32; 4] (a), _2: &[u32; 4] (&a),
;         _3: &[u32] (s), _4: Range (1..3), _5: &[u32] (w),
;         _6: usize (the index).

(defconst *win-body*
  (make-body
   :locals (list (u32)
                 (ty-array (u32) 4)
                 (ty-ref (mutability-not) (ty-array (u32) 4))
                 (ty-ref (mutability-not) (ty-slice (u32)))
                 (ty-adt "Range")
                 (ty-ref (mutability-not) (ty-slice (u32)))
                 (usize))
   :arg-count 0
   :blocks
   (list
    ;; bb0: build a, s, and the range; call slice::index_range -> bb1
    (make-basic-block
     :statements
     (list (assign-local 1
                         (rvalue-aggregate (agg-kind-array (u32))
                                           (list (const-u32 10)
                                                 (const-u32 20)
                                                 (const-u32 30)
                                                 (const-u32 40))))
           (assign-local 2 (rvalue-ref (mutability-not) (local-place 1)))
           (assign-local 3
                         (rvalue-cast (cast-kind-unsize)
                                      (copy-local 2)
                                      (ty-ref (mutability-not)
                                              (ty-slice (u32)))))
           (assign-local 4
                         (rvalue-aggregate (agg-kind-adt "Range" 0)
                                           (list (const-usize 1)
                                                 (const-usize 3)))))
     :terminator (terminator-call
                  (operand-constant (const-fn "slice::index_range"))
                  (list (copy-local 3) (move-local 4))
                  (make-place :local 5 :projection nil)
                  1))
    ;; bb1: _6 = 1; _0 = (*_5)[_6]; return
    (make-basic-block
     :statements
     (list (assign-local 6 (rvalue-use (const-usize 1)))
           (assign-local 0
                         (rvalue-use
                          (operand-copy
                           (local-place 5
                                        (proj-elem-deref)
                                        (proj-elem-index 6))))))
     :terminator (terminator-return)))))

(defconst *win-program*
  (make-mir-program :funs (omap::update "win" *win-body* nil)
                    :adts nil))

(assert-event (mir-programp *win-program*))

(assert-event
 (equal (run-fn "win" nil *win-program* 100000)
        (runout-done (u32v 30))))

; Indexing at the window length is out of the window --
; undefined behavior at the machine level -- even though
; the underlying array continues past it.

(defconst *win-oob-body*
  (change-body *win-body*
               :blocks
               (list (car (body->blocks *win-body*))
                     (make-basic-block
                      :statements
                      (list (assign-local 6 (rvalue-use (const-usize 2)))
                            (assign-local 0
                                          (rvalue-use
                                           (operand-copy
                                            (local-place
                                             5
                                             (proj-elem-deref)
                                             (proj-elem-index 6))))))
                      :terminator (terminator-return)))))

(defconst *win-oob-program*
  (make-mir-program :funs (omap::update "win" *win-oob-body* nil)
                    :adts nil))

(assert-event
 (equal (runout-kind (run-fn "win" nil *win-oob-program* 100000))
        :ub))
