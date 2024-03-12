; Lowering IFs when appropriate
;
; Copyright (C) 2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; It seems that certain instruction semantic functions can introduce IFs, so we use this machinery to try to avoid splitting the simulation.

(include-book "flags")
(include-book "register-readers-and-writers64")
(include-book "readers-and-writers")
(include-book "read-and-write")

;; We can merge 2 states (push IFs into the individual state components) when they have the same PC and neither is faulted.
;; todo: make a 32-bit version
(defun-nx mergeable-states64p (x86a x86b)
  (declare (xargs :guard (and (x86p x86a)
                              (x86p x86b))))
  (and (equal (rip x86a) (rip x86b))
       (not (ms x86a))
       (not (fault x86a))
       (not (ms x86b))
       (not (fault x86b))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd if-of-set-flag-arg2-64
  (implies (and (mergeable-states64p x86_1 x86_2)
                (member-equal flag *flags*))
           (equal (if test (set-flag flag val x86_1) x86_2) (set-flag flag (if test val (get-flag flag x86_2)) (if test x86_1 x86_2)))) )

(defthmd if-of-set-flag-arg3-64
  (implies (and (mergeable-states64p x86_1 x86_2)
                (member-equal flag *flags*))
           (equal (if test x86_1 (set-flag flag val x86_2)) (set-flag flag (if test (get-flag flag x86_1) val) (if test x86_1 x86_2)))) )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;todo: more like this
(defthmd if-of-set-rax-arg2-64 (implies (mergeable-states64p x86_1 x86_2) (equal (if test (set-rax rax x86_1) x86_2) (set-rax (if test rax (rax x86_2)) (if test x86_1 x86_2)))))
(defthmd if-of-set-rbx-arg2-64 (implies (mergeable-states64p x86_1 x86_2) (equal (if test (set-rbx rbx x86_1) x86_2) (set-rbx (if test rbx (rbx x86_2)) (if test x86_1 x86_2)))))
(defthmd if-of-set-rcx-arg2-64 (implies (mergeable-states64p x86_1 x86_2) (equal (if test (set-rcx rcx x86_1) x86_2) (set-rcx (if test rcx (rcx x86_2)) (if test x86_1 x86_2)))))
(defthmd if-of-set-rdx-arg2-64 (implies (mergeable-states64p x86_1 x86_2) (equal (if test (set-rdx rdx x86_1) x86_2) (set-rdx (if test rdx (rdx x86_2)) (if test x86_1 x86_2)))))

;todo: more like this
(defthmd if-of-set-rax-arg3-64 (implies (mergeable-states64p x86_1 x86_2) (equal (if test x86_1 (set-rax rax x86_2)) (set-rax (if test (rax x86_1) rax) (if test x86_1 x86_2)))))
(defthmd if-of-set-rbx-arg3-64 (implies (mergeable-states64p x86_1 x86_2) (equal (if test x86_1 (set-rbx rbx x86_2)) (set-rbx (if test (rbx x86_1) rbx) (if test x86_1 x86_2)))))
(defthmd if-of-set-rcx-arg3-64 (implies (mergeable-states64p x86_1 x86_2) (equal (if test x86_1 (set-rcx rcx x86_2)) (set-rcx (if test (rcx x86_1) rcx) (if test x86_1 x86_2)))))
(defthmd if-of-set-rdx-arg3-64 (implies (mergeable-states64p x86_1 x86_2) (equal (if test x86_1 (set-rdx rdx x86_2)) (set-rdx (if test (rdx x86_1) rdx) (if test x86_1 x86_2)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd if-of-set-undef-arg2-64 (implies (mergeable-states64p x86_1 x86_2) (equal (if test (set-undef undef x86_1) x86_2) (set-undef (if test undef (undef x86_2)) (if test x86_1 x86_2)))))
(defthmd if-of-set-undef-arg3-64 (implies (mergeable-states64p x86_1 x86_2) (equal (if test x86_1 (set-undef undef x86_2)) (set-undef (if test (undef x86_1) undef) (if test x86_1 x86_2)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd if-of-set-mxcsr-arg2-64 (implies (mergeable-states64p x86_1 x86_2) (equal (if test (set-mxcsr mxcsr x86_1) x86_2) (set-mxcsr (if test mxcsr (mxcsr x86_2)) (if test x86_1 x86_2)))) :hints (("Goal" :in-theory (enable set-mxcsr))))
(defthmd if-of-set-mxcsr-arg3-64 (implies (mergeable-states64p x86_1 x86_2) (equal (if test x86_1 (set-mxcsr mxcsr x86_2)) (set-mxcsr (if test (mxcsr x86_1) mxcsr) (if test x86_1 x86_2)))) :hints (("Goal" :in-theory (enable set-mxcsr))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; todo: add rules for write-byte, etc.
(defthmd if-of-write-arg2-64
  (implies (mergeable-states64p x86_1 x86_2)
           (equal (if test (write n ad val x86_1) x86_2)
                  (write n ad (if test val (read n ad x86_2)) (if test x86_1 x86_2)))))

(defthmd if-of-write-arg3-64
  (implies (mergeable-states64p x86_1 x86_2)
           (equal (if test x86_1 (write n ad val x86_2))
                  (write n ad (if test (read n ad x86_1) val) (if test x86_1 x86_2)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd if-of-write-byte-arg2-64
  (implies (mergeable-states64p x86_1 x86_2)
           (equal (if test (write-byte ad val x86_1) x86_2)
                  (write-byte ad (if test val (read-byte ad x86_2)) (if test x86_1 x86_2)))))

(defthmd if-of-write-byte-arg3-64
  (implies (mergeable-states64p x86_1 x86_2)
           (equal (if test x86_1 (write-byte ad val x86_2))
                  (write-byte ad (if test (read-byte ad x86_1) val) (if test x86_1 x86_2)))))
