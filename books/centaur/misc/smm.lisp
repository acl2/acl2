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
(include-book "u32-listp")
(include-book "std/util/bstar" :dir :system)
(include-book "std/basic/defs" :dir :system)
(include-book "std/basic/arith-equivs" :dir :system)
(include-book "misc/definline" :dir :system)
(include-book "std/stobjs/clone" :dir :system)
(local (include-book "smm-impl"))
(set-enforce-redundancy t)

;; this is a dumb "memory manager" which can allocate new blocks at will, but
;; only frees blocks by deletig all blocks or by deleting all but the first n
;; blocks created.  The blocks each contain some number of unsigned 32-bit
;; integers.  (This makes storage/retrieval efficient in CCL.)

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
  (nfix (nth i (nth n smm))))

(def-unguarded smml-write (n i v smm)
  (declare (xargs :guard (and (natp n)
                              (natp i)
                              (< n (smml-nblocks smm))
                              (< i (smml-block-size n smm))
                              (unsigned-byte-p 32 v))))
  (update-nth n (update-nth i (nfix v) (nth n smm)) smm))

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
      0
    (if (< (nfix a) (len (car smm)))
        (nfix (nth a (car smm)))
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
        (cons (update-nth a (nfix v) (car smm)) (cdr smm))
      (cons (car smm)
            (smml-fast-write (- (nfix a) (len (car smm))) v
                            (cdr smm))))))

(defcong nat-equiv equal (smml-fast-write a v smm) 1)

(def-unguarded smml-rewind (n smm)
  (declare (xargs :guard (and (natp n)
                              (<= n (smml-nblocks smm)))))
  (take n smm))

(def-unguarded smml-resize-last (sz smm)
  (declare (xargs :guard (and (natp sz)
                              (< 0 (smml-nblocks smm)))))
  (b* ((n (1- (len smm))))
    (update-nth n
                (resize-list (nth n smm) sz 0)
                smm)))

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
  (smme-mem :type (array (unsigned-byte 32) (0))
             :initially 0
             :resizable t)
  :inline t
  :renaming ((smme-memi __smme-memi)
             (update-smme-memi __update-smme-memi)
             (smme-nblocks __smme-nblocks)
             (update-smme-nblocks __update-smme-nblocks)))

(define smme-block-start ((n natp) smme)
  :inline t
  :guard (< n (smme-blockstarts-length smme))
  (lnfix (smme-blockstartsi n smme)))

(define update-smme-block-start ((n natp) (val natp) smme)
  :inline t
  :guard (< n (smme-blockstarts-length smme))
  (update-smme-blockstartsi (lnfix n) (lnfix val) smme))

(define smme-memi ((n natp) smme)
  :inline t
  :guard (< n (smme-mem-length smme))
  (lnfix (__smme-memi n smme)))

(define update-smme-memi ((n natp) (val :type (unsigned-byte 32)) smme)
  :inline t
  :guard (and (< n (smme-mem-length smme))
              (unsigned-byte-p 32 val))
  :split-types t
  (__update-smme-memi (lnfix n) (lnfix val) smme))

(define smme-nblocks (smme)
  :inline t
  (lnfix (__smme-nblocks smme)))

(define update-smme-nblocks ((nblocks natp) smme)
  :inline t
  (__update-smme-nblocks (lnfix nblocks) smme))

(define smme-blocks-wfp ((n natp) smme)
  :guard (< n (smme-blockstarts-length smme))
  ;; :guard-hints (("goal" :in-theory (enable smme-sizes-okp)))
  (or (zp n)
      (and (>= (smme-block-start n smme)
               (smme-block-start (1- n) smme))
           (smme-blocks-wfp (1- n) smme))))

(define smme-wfp (smme)
  ;; :guard-hints (("goal" :in-theory (enable smme-sizes-okp)))
  (and (< (smme-nblocks smme)
          (smme-blockstarts-length smme)) ;; (smme-sizes-okp smme)
       (int= 0 (smme-block-start 0 smme))
       (<= (smme-block-start (smme-nblocks smme) smme)
           (smme-mem-length smme))
       (smme-blocks-wfp (smme-nblocks smme) smme)))

(define smme-block-size ((n natp) smme)
  :guard (and (smme-wfp smme)
              (< n (smme-nblocks smme)))
  :inline t
  (lnfix (- (smme-block-start (+ 1 (lnfix n)) smme)
            (smme-block-start n smme))))

(define smme-addr ((n natp) (i natp) smme)
  :guard (and (smme-wfp smme)
              (< n (smme-nblocks smme))
              (< i (smme-block-size n smme)))
  (+ (lnfix i)
     (smme-block-start n smme)))

(define smme-read ((n natp) (i natp) smme)
  :guard (and (smme-wfp smme)
              (< n (smme-nblocks smme))
              (< i (smme-block-size n smme)))
  :inline t
  (smme-memi (smme-addr n i smme) smme))

(define smme-write ((n natp)
                    (i natp)
                    (v :type (unsigned-byte 32))
                    smme)
  :guard (and (smme-wfp smme)
              (< n (smme-nblocks smme))
              (< i (smme-block-size n smme))
              (unsigned-byte-p 32 v))
  :split-types t
  :inline t
  (update-smme-memi (smme-addr n i smme) v smme))

(define smme-maybe-grow-starts ((n natp) smme)
  :inline t
  (if (< (lnfix n) (smme-blockstarts-length smme))
      smme
    (resize-smme-blockstarts (max 16 (* 2 (lnfix n))) smme)))

(define smme-maybe-grow-mem ((n natp) smme)
  :inline t
  (if (< (lnfix n) (smme-mem-length smme))
      smme
    (resize-smme-mem (max 16 (* 2 (lnfix n))) smme)))

(define smme-mem-clear ((n natp) (max natp) (val :type (unsigned-byte 32)) smme)
  :guard (and (<= n max)
              (<= max (smme-mem-length smme))
              (unsigned-byte-p 32 val))
  :split-types t
  :measure (nfix (- (nfix max) (nfix n)))
  (if (mbe :logic (zp (- (nfix max) (nfix n)))
           :exec (int= max n))
      smme
    (let ((smme (update-smme-memi n val smme)))
      (smme-mem-clear (+ 1 (lnfix n)) max val smme))))

(define smme-addblock ((sz natp) smme)
  :guard (smme-wfp smme)
  :returns (new-smme)
  (b* ((n (smme-nblocks smme))
       (nstart (smme-block-start n smme))
       ;; (smme (smme-maybe-grow-sizes n smme))
       (smme (smme-maybe-grow-starts (+ 1 n) smme))
       (sz   (lnfix sz))
       (nextfree (+ sz nstart))
       (smme (smme-maybe-grow-mem nextfree smme))
       (smme (update-smme-nblocks (+ 1 n) smme))
       (smme (update-smme-block-start (+ 1 n) nextfree smme))
       ;; (smme (update-smme-block-size n sz smme))
       (smme (smme-mem-clear nstart nextfree 0 smme)))
    smme))

(define smme-rewind ((n natp) smme)
  :guard (<= n (smme-nblocks smme))
  :returns (new-smme)
  :inline t
  (update-smme-nblocks (lnfix n) smme))

(define smme-resize-last ((sz natp) smme)
  :guard (and (< 0 (smme-nblocks smme))
              (smme-wfp smme))
  :returns (new-smme)
  (b* ((nblocks (smme-nblocks smme))
       (last (1- nblocks))
       (start (smme-block-start last smme))
       (old-end (smme-block-start nblocks smme))
       (sz (lnfix sz))
       (new-end (+ start sz))
       ;; (smme (update-smme-block-size n sz smme))
       (smme (update-smme-block-start (smme-nblocks smme) new-end smme))
       ((when (<= new-end old-end))
        smme)
       (smme (smme-maybe-grow-mem new-end smme)))
    (smme-mem-clear old-end new-end 0 smme)))

(define smme-clear (smme)
  :inline t
  (b* ((smme (update-smme-nblocks 0 smme))
       (smme (smme-maybe-grow-starts 1 smme)))
    (update-smme-block-start 0 0 smme)))

(define smme-max-index (smme)
  :guard (smme-wfp smme)
  :enabled t
  :inline t
  (smme-block-start (smme-nblocks smme) smme))

;; Abstract stobjs where the smml- functions are the logical story and the smme-
;; functions are executed.
(defabsstobj smm
  :foundation smme
  :recognizer (smmp :logic smmlp :exec smmep)
  :creator (smm-create :logic smml-create :exec create-smme)
  :corr-fn smme-corr
  :exports ((smm-nblocks :logic smml-nblocks :exec smme-nblocks$inline)
            (smm-block-size :logic smml-block-size :exec smme-block-size$inline)
            (smm-read :logic smml-read :exec smme-read$inline)
            (smm-write :logic smml-write :exec smme-write$inline)
            (smm-addblock :logic smml-addblock :exec smme-addblock
                          :protect t)
            (smm-clear :logic smml-clear :exec smme-clear$inline
                       :protect t)
            (smm-block-start :logic smml-block-start :exec smme-block-start$inline)
            (smm-max-index :logic smml-max-index :exec smme-max-index$inline)
            (smm-fast-read :logic smml-fast-read :exec smme-memi$inline)
            (smm-fast-write :logic smml-fast-write :exec update-smme-memi$inline)
            (smm-rewind :logic smml-rewind :exec smme-rewind$inline)
            (smm-resize-last :logic smml-resize-last :exec smme-resize-last
                             :protect t)))

(defstobj-clone smm2 smm :suffix "2")
(defstobj-clone smm3 smm :suffix "3")
