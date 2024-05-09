; Copyright (C) 2023, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; When using books/build/cert.pl, the following forces recertification when
; mem-raw.lsp has changed.
; (depends-on mem-raw.lsp

; This book introduces a stobj, mem, with a single resizable array field, ar.
; See :DOC stobj for relevant background.  It provides a small example to
; illustrate the use of raw Lisp for doing "special" reads and writes as
; described below.  Here we provide read-mem and write-mem functions as
; wrappers for accesses to the stobj array.  This approach is sound (subject to
; the Warning below), but it results in a weaker than usual read-over-write
; theorem (proved near the end of this file).  See
; ../mem-access-unsound/mem.lisp for an unsound variant that modifies the array
; primitives directly, rather than using wrappers.

; With the exceptions noted just below, (read-mem addr mem) reads the memory
; array at address addr, and (write-mem addr val mem) writes val to address
; addr of the memory array.  However, the behavior is as follows if addr is a
; member of the list, (special-address-list mem):

; - (read-mem addr mem) returns a value, possibly with a side effect, as
;   provided by the definition of read-mem-special in mem-raw.lsp; and

; - (write-mem addr val mem) performs the indicated write to the memory array
;   but calls the raw Lisp definition of write-mem-special (also in
;   mem-raw.lsp) for a side effect.

; WARNING: The code in mem-raw.lsp must be consistent with the axioms
; introduced in the partial-encapsulate form below!  Otherwise unsoundness
; could result, i.e., it could be possible to prove nil.

; The following log shows how this works, where 8 is not a special address and
; 10 is a special address.

#|
ACL2 !>(read-mem 8 mem)
0
ACL2 !>(write-mem 8 20 mem)
<mem>
ACL2 !>(read-mem 8 mem)
20
ACL2 !>(read-mem 10 mem)
NOTE: Calling read-mem-special on address 10.

11
ACL2 !>(write-mem 10 100 mem)
NOTE: Calling write-mem-special on address 10.

<mem>
ACL2 !>(read-mem 10 mem) ; no change in what is read at address 10
NOTE: Calling read-mem-special on address 10.

11
ACL2 !>(ari 10 mem)
100
ACL2 !>
|#

(in-package "ACL2")

(defstobj mem
  (ar :type (array (unsigned-byte 8) (1024))
      :resizable t ; optional
      :initially 0)
  :inline t ; optional
  :non-memoizable t ; optional
  )

(defun bounded-nat-listp (lst bound)
  (declare (xargs :guard (natp bound)))
  (cond ((atom lst) (null lst))
        ((and (natp (car lst))
              (< (car lst) bound))
         (bounded-nat-listp (cdr lst) bound))
        (t nil)))

; We use partial-encapsulate so that the axioms for special-address-list,
; read-mem-special, and write-mem-special are implicit -- so when the raw Lisp
; code gives us an answer, it's "explained" by the implicit axioms.  On a
; practical level, functional instantiation is disallowed on functions
; introduced with partial-encapsulate; if we just defun or encapsulate to
; introduce these functions, we could prove nil by clever use of evaluation
; using the raw Lisp counterparts.

(partial-encapsulate
 (((special-address-list mem) => *)
  ((read-mem-special * mem) => *)
  ((write-mem-special * * mem) => *))
 () ; supporters

 (local (defun special-address-list (mem)
          (declare (xargs :stobjs mem)
                   (ignore mem))
          nil))

 (local (defun read-mem-special (addr mem)
          (declare (xargs :stobjs mem)
                   (ignore addr mem))
          0))

 (local (defun write-mem-special (addr val mem)
          (declare (xargs :stobjs mem)
                   (ignore addr val mem))
          nil))

 (defthm bounded-nat-listp-special-address-list
   (bounded-nat-listp (special-address-list mem)
                      (ar-length mem)))

 (defthm read-mem-special-property
   (implies (and (memp mem)
                 (member addr (special-address-list mem)))
            (unsigned-byte-p 8 (read-mem-special addr mem))))

 (defthm special-address-list-write-mem
   (equal (special-address-list (update-ari addr val mem))
          (special-address-list mem)))

; We don't need any properties for write-mem-special, since its value is
; irrelevant (see write-mem below).

)

(defthm bounded-nat-listp-forward-to-nat-listp
  (implies (bounded-nat-listp lst bound)
           (nat-listp lst))
  :rule-classes :forward-chaining)

(defthm nat-listp-special-address-list
  (nat-listp (special-address-list mem))
  :rule-classes ((:forward-chaining :trigger-terms
                                    ((special-address-list mem))))
  :hints (("Goal"
           :in-theory (disable bounded-nat-listp-special-address-list)
           :use bounded-nat-listp-special-address-list)))

(defun read-mem (addr mem)
  (declare (type (integer 0 *) addr)
           (xargs :stobjs mem
                  :guard (< addr (ar-length mem))))
  (if (member addr (special-address-list mem))
      (read-mem-special addr mem)
    (ari addr mem)))

(defun write-mem (addr val mem)
  (declare (type (integer 0 *) addr)
           (type (unsigned-byte 8) val)
           (xargs :stobjs mem
                  :guard (< addr (ar-length mem))))
  (prog2$ (and (member addr (special-address-list mem))
               (write-mem-special addr val mem))
          (update-ari addr val mem)))

(defthm read-over-write-lemma
  (implies (and (natp addr1)
                (natp addr2)
                (not (member-equal addr1 (special-address-list mem))))
           (equal (nth addr1 (car (update-ari addr2 val mem)))
                  (if (equal addr1 addr2)
                      val
                    (nth addr1 (car mem))))))

(defthm read-over-write
  (implies (and (natp addr1)
                (natp addr2)
                (not (member addr1 (special-address-list mem))))
           (equal (read-mem addr1 (write-mem addr2 val mem))
                  (if (equal addr1 addr2)
                      val
                    (read-mem addr1 mem))))
  :hints (("Goal" :in-theory (disable update-ari))))

(include-book "tools/include-raw" :dir :system)

(defttag :mem-special) ; required before calling include-raw

(include-raw "mem-raw.lsp")
