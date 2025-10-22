; A scheme for clearing out shadowed writes.
;
; Copyright (C) 2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "R")

;; WARNING: Keep in sync with the analogous scheme for x86.

(include-book "read-and-write")
(include-book "../axe-syntax")
(include-book "../axe-syntax-functions")
(include-book "syntax-functions")
(local (include-book "kestrel/bv/unsigned-byte-p" :dir :system))

;; An alias of clear
(defund clear-extend (n addr stat)
  (declare (xargs :guard (and (natp n)
                              (unsigned-byte-p 32 addr)
                              (stat32ip stat))))
  (write n addr 0 stat))

;; An alias of clear
(defund clear-retract (n addr stat)
  (declare (xargs :guard (and (natp n)
                              (unsigned-byte-p 32 addr)
                              (stat32ip stat))))
  (write n addr 0 stat))

;; Introduces the clear when there is a write in STAT to be cleared.
;; For Axe only
(defthmd write-becomes-write-of-clear-extend-axe
  (implies (and (axe-syntaxp (write-with-addr-and-size-presentp-axe n ad stat acl2::dag-array))
               ; (integerp ad)
                (unsigned-byte-p 32 n))
           (equal (write n ad val stat)
                  (write n ad val (clear-extend n ad stat))))
  :hints (("Goal" :in-theory (enable clear-extend))))

;; Copies the clear inside a write that is not its target
;; For Axe only
(defthmd clear-extend-of-write-continue-axe
  (implies (and (axe-syntaxp (and (syntactic-call-of 'write stat dag-array) ; avoid loops and undesired patterns
                                  (not (and (acl2::dargs-equalp n1 n2 dag-array)
                                            (acl2::dargs-equalp ad1 ad2 dag-array)))))
                ;(integerp ad1)
                (unsigned-byte-p 32 n1)
                ;(integerp ad2)
                (unsigned-byte-p 32 n2))
           (equal (clear-extend n1 ad1 (write n2 ad2 val stat))
                  (clear-extend n1 ad1 (write n2 ad2 val (clear-extend n1 ad1 stat)))))
  :hints (("Goal" :cases ((integerp ad1)) ; todo: generalize write-of-write-of-write-same
           :in-theory (enable clear-extend))))

;; We've found the write to be cleared
(defthmd clear-extend-of-write-finish
  (implies (and ;(integerp ad)
                (unsigned-byte-p 32 n))
           (equal (clear-extend n ad (write n ad val stat))
                  (clear-retract n ad stat)))
  :hints (("Goal" :in-theory (enable clear-extend clear-retract))))

(defthmd clear-extend-of-write-of-clear-retract
  (implies (and; (integerp ad1)
                (unsigned-byte-p 32 n1)
                ;(integerp ad2)
                (unsigned-byte-p 32 n2))
           (equal (clear-extend n1 ad1 (write n2 ad2 val (clear-retract n1 ad1 stat)))
                  (clear-retract n1 ad1 (write n2 ad2 val stat))))
  :hints (("Goal" :cases ((integerp ad1))
           :in-theory (enable clear-retract clear-extend))))

(defthmd write-of-clear-retract ; add -same to name
  (implies (and ;(integerp ad)
                (unsigned-byte-p 32 n))
           (equal (write n ad val (clear-retract n ad stat))
                  (write n ad val stat)))
  :hints (("Goal" :in-theory (enable clear-retract))))
