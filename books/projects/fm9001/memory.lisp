;; Copyright (C) 2016, Regents of the University of Texas
;; Written by Cuong Chau (derived from earlier work of Brock and Hunt)
;; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

;; See the README for historical information.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; February 2021

(in-package "FM9001")

(include-book "hard-spec")

;; ======================================================================

;; This file defines a tree-based formalization of memory.  This tree-based
;; memory offers advantages over a linear-list formalization.  Specifically,
;; reading and writing the memory take O(log n) time and CONS operations
;; respectively, where n is the number of words in the memory.  Also, we are
;; able to "stub-out", or leave unspecified, large sections of the memory.

;; Memory is modeled as a CONS tree, where the leaves of the tree are instances
;; of one of three parts: ROM tags read-only locations of the memory, while RAM
;; tags read-write locations and STUB represents ``unimplemented'' portions.
;; Each instance of the memory parts includes a value, which is returned when
;; that memory location is read.  RAM cells may be overwritten, but writing to
;; a ROM or STUB cell does not change the memory.  ROM and RAM cells may only
;; appear at the leaves of the tree, whereas STUB cells may appear anywhere.
;; Although our basic definitions restrict the types of data stored in memory
;; to be four-valued vectors, we assume throughout the specification of the
;; FM9001 (and enforce) the restriction that only bit-vectors are stored in
;; memory.

;; The bit-vector that specifies the address is used in an obvious way to
;; search the memory tree for the addressed location.  Note, however, that the
;; address is reversed prior to the search.  This allows for more compact
;; storage for sequences of data.  If the address were not reversed, then the
;; memory trees would be subject to branching near the root of the tree.  With
;; reversed addresses, the branching is localized near the leaves. This is an
;; especially important consideration for the main memory of the FM9001.
;; There, each path through the memory tree to a leaf cell is constructed from
;; 32 CONS cells.

(defun romp (mem)
  (declare (xargs :guard t))
  (and (true-listp mem)
       (equal (len mem) 2)
       (equal (car mem) 'rom)
       (4v-listp (cadr mem))))

(defun rom-guts (mem)
  (declare (xargs :guard t))
  (if (equal (len mem) 2)
      (cadr mem)
    nil))

(defun ram (value)
  (declare (xargs :guard t))
  (list 'ram (v-fourfix value)))

(defun ramp (mem)
  (declare (xargs :guard t))
  (and (true-listp mem)
       (equal (len mem) 2)
       (equal (car mem) 'ram)
       (4v-listp (cadr mem))))

(defun ram-guts (mem)
  (declare (xargs :guard t))
  (if (equal (len mem) 2)
      (cadr mem)
    nil))

(defun stubp (mem)
  (declare (xargs :guard t))
  (and (true-listp mem)
       (equal (len mem) 2)
       (equal (car mem) 'stub)
       (4v-listp (cadr mem))))

(defun stub-guts (mem)
  (declare (xargs :guard t))
  (if (equal (len mem) 2)
      (cadr mem)
    nil))

(defthmd romp-is-not-ramp-nor-stubp
  (implies (romp mem)
           (and (not (ramp mem))
                (not (stubp mem)))))

(defthm 4v-listp-rom-guts-of-romp
  (implies (romp x)
           (4v-listp (rom-guts x))))

(local
 (defthm 4v-listp=>true-listp
   (implies (4v-listp x) (true-listp x))
   :rule-classes :forward-chaining))

(defthm true-listp-rom-guts-of-romp
  (implies (romp x)
           (true-listp (rom-guts x)))
  :rule-classes :type-prescription)

(defthmd rom-guts-of-romp
  (implies (romp x)
           (equal (rom-guts x)
                  (cadr x))))

(defthm ramp-ram
  (ramp (ram x)))

(defthm ram-guts-ram
  (equal (ram-guts (ram value))
         (v-fourfix value)))

(defthmd ramp-is-not-romp-nor-stubp
  (implies (ramp mem)
           (and (not (romp mem))
                (not (stubp mem)))))

(defthm 4v-listp-ram-guts-of-ramp
  (implies (ramp x)
           (4v-listp (ram-guts x))))

(defthm true-listp-ram-guts-of-ramp
  (implies (ramp x)
           (true-listp (ram-guts x)))
  :rule-classes :type-prescription)

(defthmd ram-guts-of-ramp
  (implies (ramp x)
           (equal (ram-guts x)
                  (cadr x))))

(defthmd stubp-is-not-romp-nor-ramp
  (implies (stubp mem)
           (and (not (romp mem))
                (not (ramp mem)))))

(defthm 4v-listp-stub-guts-of-stubp
  (implies (stubp x)
           (4v-listp (stub-guts x))))

(defthm true-listp-stub-guts-of-stubp
  (implies (stubp x)
           (true-listp (stub-guts x)))
  :rule-classes :type-prescription)

(defthmd stub-guts-of-stubp
  (implies (stubp x)
           (equal (stub-guts x)
                  (cadr x))))

(defun memp (mem)
  (declare (xargs :guard t))
  (or (romp mem)
      (ramp mem)
      (stubp mem)))

(defthm memp=>consp
  (implies (memp x) (consp x))
  :rule-classes :forward-chaining)

(deftheory mem-theory
  '(romp rom-guts ram ramp ram-guts stubp stub-guts))

;; MEMORY-PROPERP -- All memory cells are proper lists of length WIDTH.

(defun memory-properp (n width mem)
  (declare (xargs :guard (natp n)))
  (if (stubp mem)
      (and (true-listp (stub-guts mem))
           (equal (len (stub-guts mem)) width))
    (if (zp n)
        (cond
         ((ramp mem) (and ;;(true-listp (ram-guts mem))
                          (equal (len (ram-guts mem)) width)))
         ((romp mem) (and ;;(true-listp (rom-guts mem))
                          (equal (len (rom-guts mem)) width)))
         (t nil))
      (and (not (romp mem))
           (not (ramp mem))
           (consp mem)
           (memory-properp (1- n) width (car mem))
           (memory-properp (1- n) width (cdr mem))))))

;; MEMORY-OKP -- All memory cells are BVP lists with length WIDTH.

(defun memory-okp (n width mem)
  (declare (xargs :guard (natp n)))
  (if (stubp mem)
      (and (bvp (stub-guts mem))
           (equal (len (stub-guts mem)) width))
    (if (zp n)
        (cond
         ((ramp mem) (and (bvp (ram-guts mem))
                          (equal (len (ram-guts mem)) width)))
         ((romp mem) (and (bvp (rom-guts mem))
                          (equal (len (rom-guts mem)) width)))
         (t nil))
      (and (not (romp mem))
           (not (ramp mem))
           (consp mem)
           (memory-okp (1- n) width (car mem))
           (memory-okp (1- n) width (cdr mem))))))

;; ALLOC-MEM & ALLOC-FULL-MEM

(local (in-theory (enable bvp)))

(defun alloc-mem1 (v-addr type v-val mem)
  (declare (xargs :guard (and (bvp v-addr)
                              (member type '(rom ram stub))
                              (bvp v-val))))
  (if (atom v-addr)
      (list type v-val)
    (if (not (listp mem))
        mem
      (if (car v-addr)
          (cons (car mem)
                (alloc-mem1 (cdr v-addr) type v-val (cdr mem)))
        (cons (alloc-mem1 (cdr v-addr) type v-val (car mem))
              (cdr mem))))))

(defun alloc-mem (addr type val mem)
  (declare (xargs :guard (and (unsigned-byte-p 32 addr)
                              (member type '(rom ram stub))
                              (unsigned-byte-p 32 val))))
  (alloc-mem1 (reverse (nat-to-v addr 32))
              type
              (nat-to-v val 32)
              mem))

(defun alloc-full-mem1 (n type)
  (declare (xargs :guard (and (natp n)
                              (member type '(rom ram stub)))))
  (if (zp n)
      (list type nil)
    (cons (alloc-full-mem1 (1- n) type)
          (alloc-full-mem1 (1- n) type))))

(defun alloc-full-mem (type)
  (declare (xargs :guard (member type '(rom ram stub))))
  (alloc-full-mem1 32 type))

;; READ-MEM

(defun read-mem1 (v-addr mem)
  (declare (xargs :guard t))
  (if (stubp mem)
      (stub-guts mem)
    (if (atom v-addr)
        (cond ((ramp mem) (ram-guts mem))
              ((romp mem) (rom-guts mem))
              (t nil))
      (if (atom mem)
          nil
        (if (car v-addr)
            (read-mem1 (cdr v-addr) (cdr mem))
          (read-mem1 (cdr v-addr) (car mem)))))))

(defun read-mem (v-addr mem)
  (declare (xargs :guard (true-listp v-addr)))
  (read-mem1 (reverse v-addr) mem))

;; WRITE-MEM

(defun write-mem1 (v-addr mem value)
  (declare (xargs :guard t))
  (if (stubp mem)
      mem
    (if (atom v-addr)
        (cond ((ramp mem) (ram value))
              (t mem))
      (if (atom mem)
          mem
        (if (car v-addr)
            (cons (car mem)
                  (write-mem1 (cdr v-addr) (cdr mem) value))
          (cons (write-mem1 (cdr v-addr) (car mem) value)
                (cdr mem)))))))

(defthm true-listp-write-mem1
  (implies (true-listp mem)
           (true-listp (write-mem1 v-addr mem value)))
  :rule-classes :type-prescription)

(defthm true-listp-write-mem1=>true-listp-mem
  (implies (true-listp (write-mem1 v-addr mem value))
           (true-listp mem))
  :rule-classes :forward-chaining)

(defthm len-write-mem1
  (equal (len (write-mem1 v-addr mem value))
         (len mem)))

(defthm 4v-listp-of-write-mem1
  (equal (4v-listp (write-mem1 v-addr mem value))
         (4v-listp mem))
  :hints (("Goal" :in-theory (e/d (4vp)
                                  (romp-is-not-ramp-nor-stubp
                                   ramp-is-not-romp-nor-stubp
                                   stubp-is-not-romp-nor-ramp
                                   romp
                                   bvp-is-true-listp)))))

(defthm 4v-listp-of-car-write-mem1
  (equal (4v-listp (car (write-mem1 v-addr mem value)))
         (4v-listp (car mem))))

(defthm romp-write-mem1
  (equal (romp (write-mem1 v-addr mem value))
         (romp mem)))

(defthm romp-cons-write-mem1-1
  (equal (romp (cons (car mem)
                     (write-mem1 v-addr (cdr mem) value)))
         (romp mem)))

(defthm romp-cons-write-mem1-2
  (equal (romp (cons (write-mem1 v-addr (car mem) value)
                     (cdr mem)))
         (romp mem)))

(defthm ramp-write-mem1
  (equal (ramp (write-mem1 v-addr mem value))
         (ramp mem)))

(defthm ramp-cons-write-mem1-1
  (equal (ramp (cons (car mem)
                     (write-mem1 v-addr (cdr mem) value)))
         (ramp mem)))

(defthm ramp-cons-write-mem1-2
  (equal (ramp (cons (write-mem1 v-addr (car mem) value)
                     (cdr mem)))
         (ramp mem)))

(defthm stubp-write-mem1
  (equal (stubp (write-mem1 v-addr mem value))
         (stubp mem)))

(defthm stubp-cons-write-mem1-1
  (equal (stubp (cons (car mem)
                      (write-mem1 v-addr (cdr mem) value)))
         (stubp mem)))

(defthm stubp-cons-write-mem1-2
  (equal (stubp (cons (write-mem1 v-addr (car mem) value)
                      (cdr mem)))
         (stubp mem)))

(defun write-mem (v-addr mem value)
  (declare (xargs :guard (true-listp v-addr)))
  (write-mem1 (reverse v-addr) mem value))

(defthm true-listp-write-mem
  (implies (true-listp mem)
           (true-listp (write-mem v-addr mem value)))
  :rule-classes :type-prescription)

(defthm true-listp-write-mem=>true-listp-mem
  (implies (true-listp (write-mem v-addr mem value))
           (true-listp mem))
  :rule-classes :forward-chaining)

(defthm len-write-mem
  (equal (len (write-mem v-addr mem value))
         (len mem)))

(defthm romp-write-mem
  (equal (romp (write-mem v-addr mem value))
         (romp mem)))

(defthm romp-cons-write-mem-1
  (equal (romp (cons (car mem)
                     (write-mem v-addr (cdr mem) value)))
         (romp mem)))

(defthm romp-cons-write-mem-2
  (equal (romp (cons (write-mem v-addr (car mem) value)
                     (cdr mem)))
         (romp mem)))

(defthm ramp-write-mem
  (equal (ramp (write-mem v-addr mem value))
         (ramp mem)))

(defthm ramp-cons-write-mem-1
  (equal (ramp (cons (car mem)
                     (write-mem v-addr (cdr mem) value)))
         (ramp mem)))

(defthm ramp-cons-write-mem-2
  (equal (ramp (cons (write-mem v-addr (car mem) value)
                     (cdr mem)))
         (ramp mem)))

(defthm stubp-write-mem
  (equal (stubp (write-mem v-addr mem value))
         (stubp mem)))

(defthm stubp-cons-write-mem-1
  (equal (stubp (cons (car mem)
                      (write-mem v-addr (cdr mem) value)))
         (stubp mem)))

(defthm stubp-cons-write-mem-2
  (equal (stubp (cons (write-mem v-addr (car mem) value)
                      (cdr mem)))
         (stubp mem)))

;; RAMP-MEM  --  A particular address is RAM.

(defun ramp-mem1 (v-addr mem)
  (declare (xargs :guard t))
  (if (stubp mem)
      nil
      (if (atom v-addr)
          (ramp mem)
          (if (atom mem)
              nil
              (if (car v-addr)
                  (ramp-mem1 (cdr v-addr) (cdr mem))
                (ramp-mem1 (cdr v-addr) (car mem)))))))

(defun ramp-mem (v-addr mem)
  (declare (xargs :guard (true-listp v-addr)))
  (ramp-mem1 (reverse v-addr) mem))

;; ALL-RAMP-MEM  --  The entire memory is RAM.

(defun all-ramp-mem (n mem)
  (declare (xargs :guard (natp n)))
  (if (stubp mem)
      nil
    (if (zp n)
        (ramp mem)
      (if (atom mem)
          nil
        (and (all-ramp-mem (1- n) (car mem))
             (all-ramp-mem (1- n) (cdr mem)))))))

;; CONSTANT-RAM  --  Sets all RAM cells to VALUE.

(defun constant-ram (mem value)
  (declare (xargs :guard t))
  (if (ramp mem)
      (ram value)
    (if (atom mem)
        mem
      (cons (constant-ram (car mem) value)
            (constant-ram (cdr mem) value)))))

(defthm true-listp-constant-ram
  (implies (true-listp mem)
           (true-listp (constant-ram mem value)))
  :rule-classes :type-prescription)

(defthm true-listp-constant-ram=>true-listp-mem
  (implies (true-listp (constant-ram mem value))
           (true-listp mem))
  :rule-classes :forward-chaining)

(defthm len-constant-ram
  (equal (len (constant-ram mem value))
         (len mem)))

(local
 (defthmd constant-ram-of-4vp
   (implies (or (4vp mem)
                (4vp (constant-ram mem value)))
            (equal (constant-ram mem value)
                   mem))
   :hints (("Goal" :in-theory (enable 4vp)))))

(defthm 4v-listp-of-constant-ram
  (equal (4v-listp (constant-ram mem value))
         (4v-listp mem))
  :hints (("Subgoal *1/3"
           :use (:instance constant-ram-of-4vp
                           (mem (car mem))))))

(defthm 4v-listp-of-car-constant-ram
  (equal (4v-listp (car (constant-ram mem value)))
         (4v-listp (car mem))))

(defthm romp-constant-ram
  (equal (romp (constant-ram mem value))
         (romp mem))
  :hints (("Goal" :in-theory (disable stubp bvp-is-true-listp))))

(defthm ramp-constant-ram
  (equal (ramp (constant-ram mem value))
         (ramp mem))
  :hints (("Goal" :in-theory (disable stubp bvp-is-true-listp))))

(defthm stubp-constant-ram
  (equal (stubp (constant-ram mem value))
         (stubp mem))
  :hints (("Goal" :in-theory (disable bvp-is-true-listp))))

;; LEMMAS

(defthm memory-properp-if
  (implies (and (memory-properp n width a)
                (memory-properp n width b))
           (memory-properp n width (if c a b))))

(defthm memory-okp-if
  (implies (and (memory-okp n width a)
                (memory-okp n width b))
           (memory-okp n width (if c a b))))

(defthm memory-properp-constant-ram
  (implies (and (memory-properp n width mem)
                (true-listp value)
                (equal width (len value)))
           (memory-properp n width (constant-ram mem value))))

(defthm memory-properp-after-write-mem1
  (implies (and (memory-properp n width mem)
                (true-listp value)
                (equal width (len value))
                (equal n (len v-addr)))
           (memory-properp n width (write-mem1 v-addr mem value))))

(defthm memory-properp-after-write-mem
  (implies (and (memory-properp n width mem)
                (true-listp value)
                (equal width (len value))
                (equal n (len v-addr)))
           (memory-properp n width (write-mem v-addr mem value)))
  :hints (("Goal"
           :use (:instance memory-properp-after-write-mem1
                           (v-addr (reverse v-addr))))))

(defthm memory-okp-after-write-mem1
  (implies (and (memory-okp n width mem)
                (bvp value)
                (equal width (len value))
                (equal n (len v-addr)))
           (memory-okp n width (write-mem1 v-addr mem value)))
  :hints (("Goal" :in-theory (enable bvp))))

(defthm memory-okp-after-write-mem
  (implies (and (memory-okp n width mem)
                (bvp value)
                (equal width (len value))
                (equal n (len v-addr)))
           (memory-okp n width (write-mem v-addr mem value)))
  :hints (("Goal"
           :use (:instance memory-okp-after-write-mem1
                           (v-addr (reverse v-addr))))))

(defthm v-iff-v-addr1-v-addr2-read-mem1-write-mem1
  (implies (and (v-iff v-addr1 v-addr2)
                (ramp-mem1 v-addr2 mem)
                (equal (len v-addr1) (len v-addr2)))
           (equal (read-mem1 v-addr1 (write-mem1 v-addr2 mem value))
                  (v-fourfix value)))
  :hints (("Goal"
           :in-theory (enable v-iff))))

(defthm v-iff-v-addr1-v-addr2-read-mem1-write-mem1-not-ram
  (implies (and (not (ramp-mem1 v-addr2 mem))
                (equal (len v-addr1) (len v-addr2)))
           (equal (read-mem1 v-addr1 (write-mem1 v-addr2 mem value))
                  (read-mem1 v-addr1 mem))))

(defthm not-v-iff-v-addr1-v-addr2-read-mem1-write-mem1
  (implies (not (v-iff v-addr1 v-addr2))
           (equal (read-mem1 v-addr1 (write-mem1 v-addr2 mem value))
                  (read-mem1 v-addr1 mem)))
  :hints (("Goal"
           :in-theory (enable v-iff))))

(defthm read-mem-write-mem
  (implies (equal (len v-addr1) (len v-addr2))
           (equal (read-mem v-addr1 (write-mem v-addr2 mem value))
                  (if (and (v-iff v-addr1 v-addr2)
                           (ramp-mem v-addr2 mem))
                      (v-fourfix value)
                    (read-mem v-addr1 mem))))
  :hints (("Goal"
           :in-theory (enable v-iff))))

(defthm true-listp-read-mem1-of-memory-properp
  (implies (memory-properp (len v-addr) size mem)
           (true-listp (read-mem1 v-addr mem)))
  :rule-classes (:rewrite :type-prescription))

(defthm len-read-mem1-of-memory-properp
  (implies (memory-properp (len v-addr) size mem)
           (equal (len (read-mem1 v-addr mem))
                  size)))

(defthm true-listp-read-mem-of-memory-properp
  (implies (memory-properp (len v-addr) size mem)
           (true-listp (read-mem v-addr mem)))
  :hints (("Goal"
           :use (:instance true-listp-read-mem1-of-memory-properp
                           (v-addr (reverse v-addr)))))
  :rule-classes (:rewrite :type-prescription))

(defthm true-listp-read-mem-of-memory-properp-32
  (implies (memory-properp (len v-addr) 32 mem)
           (true-listp (read-mem v-addr mem)))
  :rule-classes (:rewrite :type-prescription))

(defthm len-read-mem-of-memory-properp
  (implies (memory-properp (len v-addr) size mem)
           (equal (len (read-mem v-addr mem))
                  size))
  :hints (("Goal"
           :use (:instance len-read-mem1-of-memory-properp
                           (v-addr (reverse v-addr))))))

(defthm len-read-mem-of-memory-properp-32
  (implies (memory-properp (len v-addr) 32 mem)
           (equal (len (read-mem v-addr mem))
                  32))
  :hints (("Goal" :in-theory (disable read-mem))))

(defthm bvp-read-mem1-of-memory-okp
  (implies (memory-okp (len v-addr) size mem)
           (bvp (read-mem1 v-addr mem)))
  :rule-classes (:rewrite :type-prescription))

(defthm len-read-mem1-of-memory-okp
  (implies (memory-okp (len v-addr) size mem)
           (equal (len (read-mem1 v-addr mem))
                  size)))

(defthm bvp-read-mem-of-memory-okp
  (implies (memory-okp (len v-addr) size mem)
           (bvp (read-mem v-addr mem)))
  :hints (("Goal"
           :use (:instance bvp-read-mem1-of-memory-okp
                           (v-addr (reverse v-addr)))))
  :rule-classes (:rewrite :type-prescription))

(defthm bvp-read-mem-of-memory-okp-32
  (implies (memory-okp (len v-addr) 32 mem)
           (bvp (read-mem v-addr mem)))
  :rule-classes (:rewrite :type-prescription))

(defthm len-read-mem-of-memory-okp
  (implies (memory-okp (len v-addr) size mem)
           (equal (len (read-mem v-addr mem))
                  size))
  :hints (("Goal"
           :use (:instance len-read-mem1-of-memory-okp
                           (v-addr (reverse v-addr))))))

(defthm all-ramp-mem->ramp-mem1
  (implies (all-ramp-mem (len v-addr) mem)
           (ramp-mem1 v-addr mem)))

(defthm all-ramp-mem->ramp-mem
  (implies (all-ramp-mem (len v-addr) mem)
           (ramp-mem v-addr mem))
  :hints (("Goal"
           :use (:instance all-ramp-mem->ramp-mem1
                           (v-addr (reverse v-addr))))))

(defthm all-ramp-mem-after-write-mem1
  (implies (and (all-ramp-mem n mem)
                (equal n (len v-addr)))
           (all-ramp-mem n (write-mem1 v-addr mem value))))

(defthm all-ramp-mem-after-write-mem
  (implies (and (all-ramp-mem n mem)
                (equal n (len v-addr)))
           (all-ramp-mem n (write-mem v-addr mem value)))
  :hints (("Goal"
           :use (:instance all-ramp-mem-after-write-mem1
                           (v-addr (reverse v-addr))))))

(defthm all-ramp-mem-constant-ram
  (equal (all-ramp-mem n (constant-ram mem value))
         (all-ramp-mem n mem)))

(defthm memory-okp==>memory-properp
  (implies (memory-okp n m mem)
           (memory-properp n m mem)))

(in-theory (disable mem-theory
                    memory-properp memory-okp
                    read-mem1 read-mem
                    write-mem1 write-mem
                    ramp-mem1 ramp-mem
                    all-ramp-mem constant-ram))

