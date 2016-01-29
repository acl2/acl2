; Centaur Miscellaneous Books
; Copyright (C) 2008-2011 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
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
; Original authors: Sol Swords <sswords@centtech.com>
;                   Jared Davis <jared@centtech.com>

(in-package "ACL2")

(include-book "std/util/bstar" :dir :system)
(include-book "std/basic/defs" :dir :system)
(include-book "misc/definline" :dir :system)
(include-book "arith-equivs")
(include-book "u32-listp")
(local (include-book "smm-impl"))
(set-enforce-redundancy t)

;; this is a dumb "memory manager" which can allocate new blocks at will, but
;; only frees any blocks if it frees all blocks.  The blocks each contain some
;; number of unsigned 32-bit integers.  (This makes storage/retrieval efficient
;; in CCL.)

;; We first introduce the logical version.  This is just a list of lists of
;; 32-bit unsigneds.
;; Among the basic operations:
;; (smml-nblocks smm)                 = (len smm)
;; (smml-block-size block smm)        = (len (nth block smm))
;; (smml-read block index smm)        = (nth index (nth block smm))
;; (smml-write block index value smm)
;;      = (update-nth block (update-nth index value (nth block smm)) smm)
;; (smml-addblock size smm)
;;      = (append smm (list (make-list size :initial-element 0)))

;; We want these functions to have certain guards because of the way
;; defabsstobj uses the guards of the logic functions, but we don't want to
;; actually verify them because typically they're not actually sufficient.  But
;; these functions won't really be executed anyway so we'll just use EC-CALL to
;; fudge it.  The following macros help us do that.


;; This defines NAME-NX with the given formals and body and guards unverified,
;; and NAME with the given formals and body and the guard as specified,
;; verified.  Actually, the body is
;; (mbe :logic body :exec (ec-call (name-nx . ,formals))).
;; Only works on non-recursive functions.
(defmacro def-unguarded (name formals &rest decl-body)
  (let ((name-nx (intern-in-package-of-symbol
                  (concatenate 'string (symbol-name name) "-NX")
                  name))
        (decls (butlast decl-body 1))
        (body (car (last decl-body))))
    `(progn (defun ,name-nx ,formals
              (declare (xargs :verify-guards nil))
              . ,decl-body)
            (defun ,name ,formals
              (declare (xargs :guard t))
              ,@decls
              (mbe :logic ,body
                   :exec (ec-call (,name-nx . ,formals)))))))


;; Like def-unguarded, but only works on recursive functions.  Assumes that any
;; occurrence of NAME in the body is a recursive call, so don't use NAME as a
;; variable name or in some fancy macro where it's not actually a recursive call.
(defmacro def-unguarded-rec (name formals &rest decl-body)
  (let ((name-nx (intern-in-package-of-symbol
                  (concatenate 'string (symbol-name name) "-NX")
                  name))
        (decls (butlast decl-body 1))
        (body (car (last decl-body))))
    `(progn (defun ,name-nx ,formals
              (declare (xargs :verify-guards nil))
              ,@decls
              ,(subst name-nx name body))
            (defun ,name ,formals
              (declare (xargs :guard t
                              :verify-guards nil))
              ,@decls
              (mbe :logic ,body
                   :exec (ec-call (,name-nx . ,formals))))
            (encapsulate nil
              (local (defthm def-unguarded-identity
                       (equal (,name-nx . ,formals)
                              (,name . ,formals))
                       :hints (("goal" :in-theory
                                '((:induction ,name-nx)
                                  ,name ,name-nx)))))
              (verify-guards ,name)))))


(def-unguarded smml-nblocks (smm)
  (len smm))

(def-unguarded smml-block-size (n smm)
  (declare (xargs :guard (and (natp n)
                              (< n (smml-nblocks smm)))))
  (len (nth n smm)))

(def-unguarded smml-read (n i smm)
  (declare (xargs :guard (and (natp n)
                              (natp i)
                              (< n (smml-nblocks smm))
                              (< i (smml-block-size n smm)))))
  (nth i (nth n smm)))

(def-unguarded smml-write (n i v smm)
  (declare (xargs :guard (and (natp n)
                              (natp i)
                              (< n (smml-nblocks smm))
                              (< i (smml-block-size n smm))
                              (unsigned-byte-p 32 v))))
  (update-nth n (update-nth i v (nth n smm)) smm))

(def-unguarded smml-addblock (sz smm)
  (declare (xargs :guard (natp sz)))
  (append smm (list (make-list sz :initial-element 0))))

(def-unguarded smml-clear (smm)
  (declare (ignorable smm))
  nil)

(def-unguarded-rec smml-block-start (n smm)
  (declare (xargs :guard (and (natp n)
                              (<= n (smml-nblocks smm)))))
  (if (or (atom smm)
          (zp n))
      0
    (+ (len (car smm))
       (smml-block-start (1- n) (cdr smm)))))

(defcong nat-equiv equal (smml-block-start n smm) 1)


(def-unguarded smml-max-index (smm)
  (smml-block-start (smml-nblocks smm) smm))

(def-unguarded-rec smml-fast-read (a smm)
  (declare (xargs :measure (len smm)
                  :guard (and (natp a)
                              (< a (smml-max-index smm)))))
  (if (atom smm)
      nil
    (if (< (nfix a) (len (car smm)))
        (nth a (car smm))
      (smml-fast-read (- (nfix a) (len (car smm)))
                     (cdr smm)))))


(defcong nat-equiv equal (smml-fast-read a smm) 1)

(def-unguarded-rec smml-fast-write (a v smm)
  (declare (xargs :measure (len smm)
                  :guard (and (natp a)
                              (< a (smml-max-index smm))
                              (unsigned-byte-p 32 v))))
  (if (atom smm)
      nil
    (if (< (nfix a) (len (car smm)))
        (cons (update-nth a v (car smm)) (cdr smm))
      (cons (car smm)
            (smml-fast-write (- (nfix a) (len (car smm))) v
                            (cdr smm))))))

(defcong nat-equiv equal (smml-fast-write a v smm) 1)

(defun smml-create ()
  (declare (xargs :guard t))
  nil)

(defun u32-list-listp (x)
  (declare (xargs :guard t))
  (if (atom x)
      (eq x nil)
    (and (u32-listp (car x))
         (u32-list-listp (cdr x)))))

(defun smmlp (smm)
  (declare (xargs :guard t))
  (u32-list-listp smm))


;; This is the actual implementation.  It has one memory array that contains
;; all the data stored in the blocks, two auxiliary arrays for bookkeeping
;; that record the sizes and starts of the blocks, and one scalar that records
;; how many blocks exist.  We maintain an invariant among blockstarts and
;; blocksizes that:
;; for 0 <= k <= nblocks,
;;     blockstarts[k] = the sum of blocksizes[i] for i=0 to k-1.
;; alternatively:
;; blockstarts[0] = 0, and
;; for 0 < k <= nblocks
;;     blockstarts[k] = blockstarts[k-1] + blocksizes[k-1].
;;
;; blockstarts[nblocks] is the location of the first free block.



(defstobj smme
  (smme-nblocks :type (integer 0 *) :initially 0)
  ;; one larger than smme-blocksizes
  (smme-blockstarts :type (array (integer 0 *) (1))
                   :initially 0
                   :resizable t)
  (smme-blocksizes :type (array (integer 0 *) (0))
                  :initially 0
                  :resizable t)
  (smme-mem :type (array (unsigned-byte 32) (0))
           :initially 0
           :resizable t)
  :inline t)

;; requires that the allocated sizes of the arrays is large enough
(defun smme-sizes-okp (smme)
  (declare (xargs :stobjs smme))
  (and (< (lnfix (smme-nblocks smme))
          (smme-blockstarts-length smme))
       (<= (lnfix (smme-nblocks smme))
           (smme-blocksizes-length smme))
       (<= (lnfix (smme-blockstartsi (smme-nblocks smme) smme))
           (smme-mem-length smme))))

;; accessors for blockstarts and blocksizes that unconditionally produce natps
(definline smme-block-start (n smme)
  (declare (xargs :guard (and (natp n)
                              (<= n (smme-nblocks smme))
                              (smme-sizes-okp smme))
                  :stobjs smme))
  (lnfix (smme-blockstartsi n smme)))

(defcong nat-equiv equal (smme-block-start n smme) 1)

(definline smme-block-size (n smme)
  (declare (xargs :guard (and (natp n)
                              (< n (smme-nblocks smme))
                              (smme-sizes-okp smme))
                  :stobjs smme))
  (lnfix (smme-blocksizesi n smme)))

(defcong nat-equiv equal (smme-block-size n smme) 1)

;; This is the invariant on blockstarts and blocksizes, except for the
;; requirement on (smme-block-start 0 smme).
(defun smme-blocks-wfp (n smme)
  (declare (xargs :guard (and (natp n)
                              (<= n (lnfix (smme-nblocks smme)))
                              (smme-sizes-okp smme))
                  :stobjs smme))
  (or (zp n)
      (and (int= (smme-block-start n smme)
                 (+ (smme-block-start (1- n) smme)
                    (smme-block-size (1- n) smme)))
           (smme-blocks-wfp (1- n) smme))))

;; Well-formedness: array sizes are ok and block invariant holds.
(defun smme-wfp (smme)
  (declare (xargs :stobjs smme))
  (and (smme-sizes-okp smme)
       (int= 0 (smme-block-start 0 smme))
       (smme-blocks-wfp (smme-nblocks smme) smme)))

;; Address in smme-mem of index i of block n.
(definline smme-addr (n i smme)
  (declare (xargs :stobjs smme
                  :guard (and (natp n)
                              (< n (smme-nblocks smme))
                              (smme-wfp smme)
                              (natp i)
                              (< i (smme-block-size n smme)))))
  (+ (lnfix i)
     (smme-block-start n smme)))

(defcong nat-equiv equal (smme-addr n i smme) 1)
(defcong nat-equiv equal (smme-addr n i smme) 2)

(definline smme-read (n i smme)
  (declare (xargs :guard (and (natp n)
                              (< n (smme-nblocks smme))
                              (smme-wfp smme)
                              (natp i)
                              (< i (smme-block-size n smme)))
                  :stobjs smme))
  (smme-memi (smme-addr n i smme) smme))

(definline smme-write (n i v smme)
  (declare (xargs :guard (and (natp n)
                              (< n (smme-nblocks smme))
                              (smme-wfp smme)
                              (natp i)
                              (< i (smme-block-size n smme))
                              (unsigned-byte-p 32 v))
                  :stobjs smme))
  (update-smme-memi (smme-addr n i smme) v smme))


;; Building up to addblock:  resizers for the arrays in case they're full
(definline smme-maybe-resize-sizes (n smme)
  (declare (xargs :stobjs smme
                  :guard (natp n)))
  (if (< (lnfix n) (smme-blocksizes-length smme))
      smme
    (resize-smme-blocksizes (max 16 (* 2 (lnfix n))) smme)))

(definline smme-maybe-resize-starts (n smme)
  (declare (xargs :stobjs smme
                  :guard (natp n)))
  (if (< (lnfix n) (smme-blockstarts-length smme))
      smme
    (resize-smme-blockstarts (max 16 (* 2 (lnfix n))) smme)))

(definline smme-maybe-resize-mem (n smme)
  (declare (xargs :stobjs smme
                  :guard (natp n)))
  (if (< (lnfix n) (smme-mem-length smme))
      smme
    (resize-smme-mem (max 16 (* 2 (lnfix n))) smme)))

;; zero out a block of the memory
(defun smme-mem-clear (n max val smme)
  (declare (xargs :guard (and (natp n)
                              (natp max)
                              (<= n max)
                              (<= max (smme-mem-length smme))
                              (unsigned-byte-p 32 val))
                  :stobjs smme
                  :measure (nfix (- (nfix max) (nfix n)))))
  (if (mbe :logic (zp (- (nfix max) (nfix n)))
           :exec (int= max n))
      smme
    (let ((smme (update-smme-memi n val smme)))
      (smme-mem-clear (+ 1 (lnfix n)) max val smme))))

;; Add a new block of the given size by incrementing nblocks, adding the
;; appropriate entry to blocksizes and blockstarts, and zeroing out the block
;; of the memory (resizing arrays as necesary).
(defun smme-addblock (sz smme)
  (declare (xargs :guard (and (natp sz)
                              (smme-wfp smme))
                  :stobjs smme
                  :guard-hints (("goal" :in-theory (disable smme-wfp
                                                            smme-sizes-okp
                                                            len max resize-list)
                                 :do-not-induct t))))
  (b* ((n (lnfix (smme-nblocks smme)))
       (nstart (smme-block-start n smme))
       (smme (smme-maybe-resize-sizes n smme))
       (smme (smme-maybe-resize-starts (+ 1 n) smme))
       (nsz   (lnfix sz))
       (nextfree (+ nsz nstart))
       (smme (smme-maybe-resize-mem nextfree smme))
       (smme (update-smme-nblocks (+ 1 n) smme))
       (smme (update-smme-blockstartsi (+ 1 n) nextfree smme))
       (smme (update-smme-blocksizesi n nsz smme))
       (smme (smme-mem-clear nstart nextfree 0 smme)))
    smme))

;; Clear the whole memory, basically by zeroing nblocks, and a couple
;; incidental things to make the invariant hold.
(definline smme-clear (smme)
  (declare (xargs :stobjs smme))
  (b* ((smme (update-smme-nblocks 0 smme))
       (smme (smme-maybe-resize-starts 1 smme)))
    (update-smme-blockstartsi 0 0 smme)))

;; starting index of the first free block.
(defun smme-nextfree (smme)
  (declare (xargs :stobjs smme
                  :guard (smme-sizes-okp smme)))
  (smme-block-start (smme-nblocks smme) smme))

;; Abstract stobjs where the smml- functions are the logical story and the smme-
;; functions are executed.
(defabsstobj smm
  :concrete smme
  :recognizer (smmp :logic smmlp :exec smmep)
  :creator (smm-create :logic smml-create :exec create-smme)
  :corr-fn smme-corr
  :exports ((smm-nblocks :logic smml-nblocks :exec smme-nblocks)
            (smm-block-size :logic smml-block-size :exec smme-block-size$inline)
            (smm-read :logic smml-read :exec smme-read$inline)
            (smm-write :logic smml-write :exec smme-write$inline)
            (smm-addblock :logic smml-addblock :exec smme-addblock
                          :protect t)
            (smm-clear :logic smml-clear :exec smme-clear$inline
                       :protect t)
            (smm-block-start :logic smml-block-start :exec smme-block-start$inline)
            (smm-max-index :logic smml-max-index :exec smme-nextfree)
            (smm-fast-read :logic smml-fast-read :exec smme-memi)
            (smm-fast-write :logic smml-fast-write :exec update-smme-memi)))

(defabsstobj smm2
  :concrete smme
  :recognizer (smm2p :logic smmlp :exec smmep)
  :creator (smm2-create :logic smml-create :exec create-smme)
  :corr-fn smme-corr
  :exports ((smm2-nblocks :logic smml-nblocks :exec smme-nblocks)
            (smm2-block-size :logic smml-block-size :exec smme-block-size$inline)
            (smm2-read :logic smml-read :exec smme-read$inline)
            (smm2-write :logic smml-write :exec smme-write$inline)
            (smm2-addblock :logic smml-addblock :exec smme-addblock
                           :protect t)
            (smm2-clear :logic smml-clear :exec smme-clear$inline
                        :protect t)
            (smm2-block-start :logic smml-block-start :exec smme-block-start$inline)
            (smm2-max-index :logic smml-max-index :exec smme-nextfree)
            (smm2-fast-read :logic smml-fast-read :exec smme-memi)
            (smm2-fast-write :logic smml-fast-write :exec update-smme-memi))
  :congruent-to smm)

(defabsstobj smm3
  :concrete smme
  :recognizer (smm3p :logic smmlp :exec smmep)
  :creator (smm3-create :logic smml-create :exec create-smme)
  :corr-fn smme-corr
  :exports ((smm3-nblocks :logic smml-nblocks :exec smme-nblocks)
            (smm3-block-size :logic smml-block-size :exec smme-block-size$inline)
            (smm3-read :logic smml-read :exec smme-read$inline)
            (smm3-write :logic smml-write :exec smme-write$inline)
            (smm3-addblock :logic smml-addblock :exec smme-addblock
                           :protect t)
            (smm3-clear :logic smml-clear :exec smme-clear$inline
                        :protect t)
            (smm3-block-start :logic smml-block-start :exec smme-block-start$inline)
            (smm3-max-index :logic smml-max-index :exec smme-nextfree)
            (smm3-fast-read :logic smml-fast-read :exec smme-memi)
            (smm3-fast-write :logic smml-fast-write :exec update-smme-memi))
  :congruent-to smm)
