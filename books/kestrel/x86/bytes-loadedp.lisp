; Asserting that certain bytes are loaded at a certain memory address
;
; Copyright (C) 2024-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

(include-book "read-and-write")
(include-book "kestrel/bv-lists/bv-array-read-chunk-little" :dir :system)
(local (include-book "kestrel/bv-lists/packbv-theorems" :dir :system))
(local (include-book "kestrel/lists-light/take" :dir :system))
(local (include-book "kestrel/lists-light/nth" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus-and-minus" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt2" :dir :system))

;; Similar to program-at but simpler, and easier to connect to read and read-byte, as this just calls read-byte repeatedly.
;; todo: consider making the len a param?
;; todo: why does ACL2 guess the wrong measure here?
;; todo: can we just use (equal (read-byte-list ..) ...) ?
(defund bytes-loadedp (addr bytes x86)
  (declare (xargs :guard (and (integerp addr) ; usually an unsigned-byte 48
                              (byte-listp bytes) ; max length 2^48?
                              )
                  :stobjs x86
                  :measure (len bytes)))
  (if (endp bytes)
      t
    (and (equal (first bytes) (read-byte addr x86))
         (bytes-loadedp (bvplus 48 1 addr) (rest bytes) x86))))

(defthm bytes-loadedp-of-bvchop-48-arg1
  (equal (bytes-loadedp (bvchop 48 addr) bytes x86)
         (bytes-loadedp addr bytes x86))
  :hints (("Goal" :in-theory (enable bytes-loadedp))))

(local
  (defthm read-byte-when-bytes-loadedp-helper
    (implies (and (bytes-loadedp addr2 bytes x86)
                  (bvlt 48 (bvminus 48 addr addr2) (len bytes))
                  (unsigned-byte-p 48 addr)
                  (unsigned-byte-p 48 addr2))
             (equal (read-byte addr x86)
                    (bv-array-read 8 (len bytes) (bvminus 48 addr addr2) bytes)))
    :hints (("Goal"
             :induct t
             :expand (;; (bytes-loadedp addr2 bytes x86)
                      ;; (bytes-loadedp 0 (cdr bytes) x86)
                      ;; (bytes-loadedp 1 (cdr bytes) x86)
                      ;; (bytes-loadedp 2 (cddr bytes) x86)
                      ;; (bytes-loadedp 1 (cddr bytes) x86)
                      ;; (bytes-loadedp (+ 1 addr2) (cdr bytes) x86)
                      (:free (addr2) (bytes-loadedp addr2 bytes x86))
                      )
             :in-theory (enable (:i bytes-loadedp)
                                ;;bv-array-read
                                bvplus
                                bvlt
                                acl2::bvchop-of-sum-cases
                                ;;read-byte
                                acl2::bv-array-read-opener
                                bvuminus
                                )))))

;; often the resulting array can be trimmed down.
(defthm read-byte-when-bytes-loadedp
  (implies (and (bytes-loadedp addr2 bytes x86)
                (bvlt 48 (bvminus 48 addr addr2) (len bytes)))
           (equal (read-byte addr x86)
                  (bv-array-read 8 (len bytes) (bvminus 48 addr addr2) bytes)))
  :hints (("Goal" :use (:instance read-byte-when-bytes-loadedp-helper
                                  (addr (bvchop 48 addr))
                                  (addr2 (bvchop 48 addr2))))))

(local
  (defun ind (addr addr2 bytes n)
    (if (or (endp bytes)
            (zp n))
        (list addr addr2 bytes n)
      (ind (bvplus 48 1 addr)
           addr2 ;(bvplus 48 1 addr2)
           bytes
           (+ -1 n)))))

;todo: if we can't resolve the index, something like bv-array-read might be preferable.  but we would need multi-byte reads...
;compare to read-when-program-at-8-bytes, etc.
(local
  (defthm read-when-bytes-loadedp-helper
    (implies (and (bytes-loadedp addr2 bytes x86)
                  ;; We expect any common addends in ADDR and ADDR2 to be removed when simplifying the difference:
                  (bvlt 48 (bvminus 48 addr addr2) (+ 1 (len bytes) (- n))) ; use bvlt?
                  (unsigned-byte-p 48 addr)
                  (unsigned-byte-p 48 addr2)
;                (unsigned-byte-p 48 n) ; allow 2^48?
                  (unsigned-byte-p 48 (len bytes))
;(<= (len bytes) (expt 2 48))
                  (<= n (len bytes))
                  )
             (equal (read n addr x86)
                    ;; todo: consider what should happen here if ADDR is not a constant?
                    (bv-array-read-chunk-little n 8 (len bytes) (bvminus 48 addr addr2) bytes)))
    :hints (("subgoal *1/1" :cases ((zp n)))
            ("subgoal *1/2" :use read-byte-when-bytes-loadedp
             ;; :cases ((= (len bytes) (expt 2 48)))
             :do-not '(generalize eliminate-destructors)
             :expand ((read n addr x86)
                      (bytes-loadedp 0 bytes x86)
                      (bv-array-read 8 (len bytes) 0 bytes)))
            ("Goal" :induct (ind addr addr2 bytes n)
             :in-theory (e/d ((:i bytes-loadedp)
                              read
                              acl2::bv-array-read-chunk-little
                              ;;acl2::packbv-little ; todo
                              ;;bv-array-read
                              bvlt
                              bvplus
                              bvuminus
                              acl2::bvchop-of-sum-cases
                              )
                             ( ;(:e expt)
                              read-byte-when-bytes-loadedp
                              acl2::bvcat-equal-rewrite   ;looped
                              acl2::bvcat-equal-rewrite-alt ; looped
                              acl2::bv-array-read-chunk-little-unroll
                              ))))))

(defthm read-when-bytes-loadedp
    (implies (and (bytes-loadedp addr2 bytes x86)
                  ;; We expect any common addends in ADDR and ADDR2 to be removed when simplifying the difference:
                  (bvlt 48 (bvminus 48 addr addr2) (+ 1 (len bytes) (- n)))
                  (integerp addr) ; drop?
                  (unsigned-byte-p 48 (len bytes))
                  (<= n (len bytes)))
             (equal (read n addr x86)
                    ;; todo: consider what should happen here if ADDR is not a constant?
                    (bv-array-read-chunk-little n 8 (len bytes) (bvminus 48 addr addr2) bytes)))
  :hints (("Goal" :use (:instance read-when-bytes-loadedp-helper
                                  (addr (bvchop 48 addr))
                                  (addr2 (bvchop 48 addr2)))
           :in-theory (disable read-when-bytes-loadedp-helper))))
