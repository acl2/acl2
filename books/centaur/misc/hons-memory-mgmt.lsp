; Centaur Miscellaneous Books
; Copyright (C) 2008-2011 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "ACL2")

; Comments rescued from memoize-raw.lisp

;          Sol Sword's scheme to control GC in CCL
;
; The goal is to get CCL to perform a GC whenever we're using almost
; all the physical memory, but not otherwise.
;
; The usual way of controlling GC on CCL is via LISP-HEAP-GC-THRESHOLD.
; This value is approximately amount of memory that will be allocated
; immediately after GC.  This means that the next GC will occur after
; LISP-HEAP-GC-THRESHOLD more bytes are used (by consing or array
; allocation or whatever.)  But this means the total memory used by the
; time the next GC comes around is the threshold plus the amount that
; remained in use at the end of the previous GC.  This is a problem
; because of the following scenario:
;
;  - We set the LISP-HEAP-GC-THRESHOLD to 3GB since we'd like to be able
;    to use most of the 4GB physical memory available.
;
;  - A GC runs or we say USE-LISP-HEAP-GC-THRESHOLD to ensure that 3GB
;    is available to us.
;
;  - We run a computation until we've exhausted this 3GB, at which point
;    a GC occurs.
;
;  - The GC reclaims 1.2 GB out of the 3GB used, so there is 1.8 GB
;    still in use.
;
;  - After GC, 3GB more is automatically allocated -- but this means we
;    won't GC again until we have 4.8 GB in use, meaning we've gone to
;    swap.
;
; What we really want is, instead of allocating a constant additional
; amount after each GC, to allocate up to a fixed total amount including
; what's already in use.  To emulate that behavior, we use the hack
; below.  This operates as follows (assuming the same 4GB total physical
; memory as in the above example:)
;
; 1. We set the LISP-HEAP-GC-THRESHOLD to (3.5G - used bytes) and call
; USE-LISP-HEAP-GC-THRESHOLD so that our next GC will occur when we've
; used a total of 3.5G.
;
; 2. We set the threshold back to 1GB without calling
; USE-LISP-HEAP-GC-THRESHOLD.
;
; 3. Run a computation until we use up the 3.5G and the GC is called.
; Say the GC reclaims 1.2GB so there's 2.3GB in use.  1GB more (the
; current LISP-HEAP-GC-THRESHOLD) is allocated so the ceiling is 3.3GB.)
;
; 4. A post-GC hook runs which again sets the threshold to (3.5G -
; used bytes), calls USE-LISP-HEAP-GC-THRESHOLD to raise the ceiling to
; 3.5G, then sets the threshold back to 1GB, and the process repeats.
;
; A subtlety about this scheme is that post-GC hooks runs in a separate
; thread from the main execution.  A possible bug is that in step 4,
; between checking the amount of memory in use and calling
; USE-LISP-HEAP-GC-THRESHOLD, more memory might be used up by the main
; execution, which would set the ceiling higher than we intended.  To
; prevent this, we interrupt the main thread to run step 4.




(defun looking-at (str1 str2 &key (start1 0) (start2 0))

;  (LOOKING-AT str1 str2 :start1 s1 :start2 s2) is non-NIL if and only
;  if string STR1, from location S1 to its end, is an initial segment
;  of string STR2, from location S2 to its end.

  (unless (typep str1 'simple-base-string)
    (ofe "looking at:  ~a is not a string." str1))
  (unless (typep str2 'simple-base-string)
    (ofe "looking at:  ~a is not a string." str2))
  (unless (typep start1 'fixnum)
    (ofe "looking at:  ~a is not a fixnum." start1))
  (unless (typep start2 'fixnum)
    (ofe "looking at:  ~a is not a fixnum." start2))
  (locally
    (declare (simple-base-string str1 str2)
             (fixnum start1 start2))
    (let ((l1 (length str1)) (l2 (length str2)))
      (declare (fixnum l1 l2))
      (loop
       (when (>= start1 l1) (return t))
       (when (or (>= start2 l2)
                 (not (eql (char str1 start1)
                           (char str2 start2))))
         (return nil))
       (incf start1)
       (incf start2)))))

(defun meminfo (pat)

;  General comment about PROBE-FILE.  PROBE-FILE, according to Gary
;  Byers, may reasonably cause an error.  He is undoubtedly right.  In
;  such cases, however, Boyer generally thinks and wishes that it
;  returned NIL, and generally, therefore, ensconces a PROBE-FILE
;  within an IGNORE-ERROR in his code.

  (or
   (and
    (ignore-errors (probe-file "/proc/meminfo"))
    (with-standard-io-syntax
     (with-open-file (stream "/proc/meminfo")
       (let (line)
         (loop while (setq line (read-line stream nil nil)) do
               (when (looking-at pat line)
                 (return
                  (values
                   (read-from-string line nil nil
                                     :start (length pat))))))))))
   0))

(let ((physical-memory-cached-answer nil))
  (defun physical-memory ()
    (or physical-memory-cached-answer
        (setq physical-memory-cached-answer
              (meminfo "MemTotal:")))))


(defvar *sol-gc-installed* nil)


#+Clozure
(defun set-and-reset-gc-thresholds ()
  (let ((n (max (- *max-mem-usage* (ccl::%usedbytes))
                *gc-min-threshold*)))
    (cond ((not (eql n (ccl::lisp-heap-gc-threshold)))
           (ccl::set-lisp-heap-gc-threshold n)
           (ofvv "~&; set-and-reset-gc-thresholds: Reserving ~:d additional bytes.~%"
                 n))))
  (ccl::use-lisp-heap-gc-threshold)
; (ofvv "~&; set-and-reset-gc-thresholds: Calling ~
;        ~%(use-lisp-heap-gc-threshold).")
  (cond ((not (eql *gc-min-threshold*
                   (ccl::lisp-heap-gc-threshold)))
         (ccl::set-lisp-heap-gc-threshold *gc-min-threshold*)
         (ofvv "~&; set-and-reset-gc-thresholds: Will reserve ~:d bytes after
next GC.~%"
               *gc-min-threshold*))))


#+Clozure
(defun start-sol-gc ()

; The following settings are highly heuristic.  We arrange that gc
; occurs at 1/8 of the physical memory size in bytes, in order to
; leave room for the gc point to grow (as per
; set-and-reset-gc-thresholds).  If we can determine the physical
; memory; great; otherwise we assume that it it contains at least 4GB,
; a reasonable assumption we think for anyone using the HONS version
; of ACL2.

  (let* ((phys (physical-memory))
         (memsize (cond ((> phys 0) (* phys 1024)) ; to bytes
                        (t (expt 2 32)))))
    (setq *max-mem-usage* (min (floor memsize 8)
                               (expt 2 31)))
    (setq *gc-min-threshold* (floor *max-mem-usage* 4)))

; OLD COMMENT:
; Trigger GC after we've used all but (1/8, but not more than 1 GB) of
; the physical memory.

  (unless *sol-gc-installed*
    (ccl::add-gc-hook
     #'(lambda ()
         (ccl::process-interrupt
          (slot-value ccl:*application* 'ccl::initial-listener-process)
          #'set-and-reset-gc-thresholds))
     :post-gc)
    (setq *sol-gc-installed* t))

  (set-and-reset-gc-thresholds))


;; Use defvar so these aren't clobbered.
(defvar *gc-min-threshold* (expt 2 30))
(defvar *max-mem-usage*    (expt 2 31))

(defvar *last-chance-threshold*
  ;; We'll automatically wash if we get within 1/400 of the max memory usage.
  ;; Examples:
  ;;   If *max-mem-usage* is   8 GB, the cushion is  ~21 MB.
  ;;   If *max-mem-usage* is  16 GB, the cushion is  ~42 MB.
  ;;   If *max-mem-usage* is  32 GB, the cushion is  ~85 MB.
  ;;   If *max-mem-usage* is  64 GB, the cushion is ~171 MB.
  ;;   If *max-mem-usage* is  96 GB, the cushion is ~257 MB.
  ;;   If *max-mem-usage* is 128 GB, the cushion is ~343 MB.
  (ceiling *max-mem-usage* 400))

(defun set-max-mem-usage (max)
  (setf *max-mem-usage* max)
  (setf *last-chance-threshold* (ceiling *max-mem-usage* 400))
  (setf *gc-min-threshold* (floor *max-mem-usage* 5))

  #+Clozure
  (set-and-reset-gc-thresholds)

  nil)

(defun print-quick-memory-summary ()

  #+Clozure
  (multiple-value-bind
      (dynamic-used static-used library-used frozen-size)
      (ccl::%usedbytes)
    (let ((free (ccl::%freebytes))
          (used (+ dynamic-used static-used library-used frozen-size))
          (max  *max-mem-usage*))
      (format t "Max:            ~15:D bytes~%" max)
      (format t "Free:           ~15:D bytes~%" free)
      (format t "Used:           ~15:D bytes~%" used)
      (format t "  - Dynamic:    ~15:D bytes~%" dynamic-used)
      (format t "  - Static:     ~15:D bytes~%" static-used)
      (format t "  - Library:    ~15:D bytes~%" library-used)
      (format t "  - Frozen:     ~15:D bytes~%" frozen-size)
      (format t "Dynamic+Frozen: ~15:D bytes~%" (+ dynamic-used frozen-size))
      (hons-summary)
      (hons-analyze-memory nil)
      ;; Jared changed this to force-output, since finish-output is slow
      ;; on an NFS.
      (force-output)))
  nil)

(defun maybe-wash-memory-fn (n clear)

  #+Clozure
  (when (or (eq n t)
            (< (ccl::%freebytes) (nfix n)))
    (format t "********** maybe-wash-memory started ***********~%~%")
    (format t "Pre-wash memory usage.~%")
    (print-quick-memory-summary)

    (if clear
        (time$ (clear-hash-tables)
               :msg "(clear-hash-tables) took ~st seconds, ~sa bytes.~%~%")
      (time$ (wash-memory)
             :msg "(wash-memory) took ~st seconds, ~sa bytes.~%~%"))

    (format t "Post-wash memory usage:~%")
    (print-quick-memory-summary)

    (format t "********** maybe-wash-memory finished **********~%"))

  nil)

(defun last-chance-wash-memory-fn ()
  #+Clozure
  (when (< (ccl::%freebytes) *last-chance-threshold*)
    (format t "*********** last-chance-wash-memory ************~%")
    (format t "~:D free bytes < ~:D last chance threshold~%"
            (ccl::%freebytes)
            *last-chance-threshold*)
    (maybe-wash-memory-fn t nil))

  nil)

(defun set-max-mem (max)
  (set-max-mem-usage max)
  nil)



; Raw lisp definition of hons-analyze-memory.

#+static-hons
(defun hl-sizeof (thing)

; Highly CCL-specific.  This function computes something like "the size of
; thing in bytes," and was originally developed by Gary Byers in response to a
; question on the CCL mailing list.  Jared only changed the names so it can be
; in the ACL2 package and added this comment.
;
; Note: determining memory usage is subtle and this function does NOT
; necessarily give you the whole story.  For instance, in CCL each hash table
; has a uvector inside of it that holds the data elements.  So, the (hl-sizeof
; ht) for some hash table doesn't actually descend into this field!
;
; The following comment was left by Gary:

  ;; All memory-allocated objects in CCL are either CONSes or
  ;; "UVECTOR"s; a UVECTOR contains a header which describes the
  ;; object's primitive type (represented as an (UNSIGNED-BYTE 8) and
  ;; accessible via the function CCL::TYPECODE) and element-count
  ;; (accessible via the function CCL::UVSIZE.)  A function defined in
  ;; the compiler backend knows how to map from a typecode and
  ;; element-count to a size in octets.  UVECTORs are aligned on
  ;; doubleword boundaries and contain this extra header word, so the
  ;; "physical size" of the uvector is a bit bigger.  On x86-64,
  ;; SYMBOLs and FUNCTIONs have their own tag, but there's an
  ;; underlying UVECTOR.
  (cond ((null thing) 0)
        ((consp thing) #+64-bit-target 16 #+32-bit-target 8)
        #+x8664-target ((symbolp thing)
                        (hl-sizeof (ccl::%symptr->symvector thing)))
        #+x8664-target ((functionp thing)
                        (hl-sizeof (ccl::function-to-function-vector thing)))
        ((ccl::uvectorp thing)
         (let* ((typecode (ccl::typecode thing))
                (element-count (ccl::uvsize thing))
                (sizeof-content-in-octets
                 ;; Call the architecture-specific backend function.
                 (funcall (arch::target-array-data-size-function
                           (ccl::backend-target-arch ccl::*host-backend*))
                          typecode element-count)))
           (logandc2 (+ sizeof-content-in-octets
                           #+64-bit-target (+ 8 15)
                           #+32-bit-target (+ 4 7))
                     #+64-bit-target 15
                     #+32-bit-target 7)))
        (t 0)))


#+static-hons
(defconstant hl-size-of-cons (hl-sizeof (cons nil nil)))

#+static-hons
(defun hl-hash-table-bytes (ht)

; This is Jared's approximation of the actual memory being used by the hash
; table itself.  Note that this does NOT include the memory used by any of the
; keys or values that are currently stored in the hash table; the only things
; we count are the hash table's vector and its header size.  This may be an
; under-approximation if we are missing other uvectors in the hash table
; structure itself.

  (declaim (type hash-table ht))
  (+ (hl-sizeof ht)
     (hl-sizeof (ccl::nhash.vector ht))))


#+static-hons
(defun hl-hash-table-key-bytes (ht)

; This is Jared's approximation of the actual memory being used for the keys of
; a hash table.  This doesn't follow any pointers in the keys, but should work
; for counting up strings, bignums, that sort of thing.

  (let ((size 0))
    (maphash (lambda (key val)
	       (declare (ignore val))
	       (unless (typep key 'fixnum)
		 (incf size (hl-sizeof key))))
	     ht)
    size))


#+static-hons
(defun hl-hash-table-val-bytes (ht)

; This is Jared's approximation of the actual memory being used for the values
; of a hash table.  This doesn't follow any pointers in the values, but should
; work for counting up strings, bignums, that sort of thing.

  (let ((size 0))
    (maphash (lambda (key val)
	       (declare (ignore key))
	       (unless (typep val 'fixnum)
		 (incf size (hl-sizeof val))))
	     ht)
    size))





#+static-hons
(defun hl-hspace-analyze-memory (slowp hs)

; Print a brief report about the memory being used by the hons space.  When
; slowp is set, we generate better information but may require a lot more time
; to do it.

  (declaim (type hl-hspace hs))
  (format t "Analyzing hons-space memory usage.~%~%")

  (format t "SBITS total memory:          ~15:D bytes~%~%"
          (hl-sizeof (hl-hspace-sbits hs)))

  (let* ((addr-ht             (hl-hspace-addr-ht hs))
         (addr-key-bytes      (if slowp
                                  (hl-hash-table-key-bytes addr-ht)
                                0))
         (addr-tbl-bytes      (hl-hash-table-bytes addr-ht))
         (addr-overhead-bytes (+ addr-key-bytes addr-tbl-bytes))
         (addr-data-bytes     (* (hl-sizeof '(1 . 2)) ;; 16
                                 (hash-table-count addr-ht)))
         (addr-total-mem      (+ addr-overhead-bytes addr-data-bytes)))
    (format t "ADDR-HT total memory:        ~15:D bytes~%" addr-total-mem)
    (format t "  - Actual cons data:        ~15:D bytes (~5,2f%)~%"
            addr-data-bytes
            (/ (* addr-data-bytes 100.0) addr-total-mem))
    (if slowp
        (progn
          (format t "  - Total overhead:          ~15:D bytes (~5,2f%)~%"
                  addr-overhead-bytes
                  (/ (* addr-overhead-bytes 100.0) addr-total-mem))
          (format t "     from the table itself:  ~15:D bytes~%" addr-tbl-bytes)
          (format t "     from bignum indicies:   ~15:D bytes~%~%" addr-key-bytes))
      (format t "  - Overhead (approx):       ~15:D bytes (~5,2f%)~%~%"
              addr-overhead-bytes
              (/ (* addr-overhead-bytes 100.0) addr-total-mem))))

  (let* ((str-ht          (hl-hspace-str-ht hs))
         (str-tbl-bytes   (hl-hash-table-bytes str-ht))
         (str-key-bytes   (hl-hash-table-key-bytes str-ht))
         (str-addr-bytes  (* (hl-sizeof '(1 . 2))
                             (hash-table-count str-ht)))
         (str-total-bytes (+ str-tbl-bytes str-key-bytes str-addr-bytes)))
    (format t "STR-HT total memory:         ~15:D bytes~%" str-total-bytes)
    (format t "  - Actual string data:      ~15:D bytes~%" str-key-bytes)
    (format t "  - Total overhead:          ~15:D bytes~%" (+ str-tbl-bytes str-addr-bytes))
    (format t "     from the table itself:  ~15:D bytes~%" str-tbl-bytes)
    (format t "     from address conses:    ~15:D bytes~%~%" str-addr-bytes))

  (let* ((other-ht          (hl-hspace-other-ht hs))
         (other-tbl-bytes   (hl-hash-table-bytes other-ht))
         (other-key-bytes   (hl-hash-table-key-bytes other-ht))
         (other-addr-bytes  (* (hl-sizeof '(1 . 2))
                               (hash-table-count other-ht)))
         (other-total-bytes (+ other-tbl-bytes other-key-bytes other-addr-bytes)))
    (format t "OTHER-HT total memory:       ~15:D bytes~%" other-total-bytes)
    (format t "  - Data for the atoms:      ~15:D bytes~%" other-key-bytes)
    (format t "  - Table overhead:          ~15:D bytes~%" other-tbl-bytes)
    (format t "  - Address overhead:        ~15:D bytes~%~%" other-addr-bytes))
  )




#+static-hons
(defun hl-ponstable-bytes-aux (elem)
  ;; Suppose a pons-table contains (Y . ELEM).  I think that ELEM is either
  ;;   (1) an list of XYC = (X . Y) pairs, where each XYC represents the
  ;;       unique cons for (X . Y) in this pons table, or
  ;;   (2) is a hash table that binds X to XYC.
  ;;
  ;; We'd really like to know something like, "how much space could be freed up
  ;; if we cleared this memo table."  But that's extraordinarily hard to
  ;; measure, because we'd have to know what subtrees of these XYC pairs are
  ;; reachable from other places in the program.  So, this function is really
  ;; only explaining how much space is definitely due to a pons table entry.
  ;;
  ;; In case (1) we charge for each cons in the alist, and for the conses that
  ;; connect the alist together.  For example, if the alist has the form:
  ;;
  ;;   ((A . Y) . (B . Y) . (C . Y) . NIL)
  ;;
  ;; Then we estimate the cost as 6 conses.  This could be a severe
  ;; underapproximation of the actual overhead if A, B, C, or Y was a large
  ;; cons-tree that isn't reachable from anywhere else in the program.
  ;;
  ;; In case (2), we charge for the size of the table itself, and also for the
  ;; each XYC cons.
  (if (listp elem)
      (* (length elem) (* 2 hl-size-of-cons))
    (+ (hl-hash-table-bytes elem)
       (hl-hash-table-val-bytes elem))))

#+static-hons
(defun hl-ponstable-bytes (pt)
  (if (not pt)
      0
    (+ (hl-hash-table-bytes pt)
       (let ((sum 0))
         (maphash (lambda (key val)
                    (declare (ignore key))
                    (incf sum (hl-ponstable-bytes-aux val)))
                  pt)
         sum))))

#+static-hons
(defun memo-table-size-debug1 (fn info)
  ;; (FN -> INFO) is an entry in the *memo-info-ht*.
  (when (natp fn)
    ;; Skip back-pointers from numbers to functions.
    (return-from memo-table-size-debug1 nil))
  (let* ((table-name      (access memoize-info-ht-entry info :tablename))
         (table           (symbol-value table-name))
         (table-size      (if table (hash-table-size table) 0))
         (table-bytes     (if table (hl-hash-table-bytes table) 0))
         (ponstable-name  (access memoize-info-ht-entry info :ponstablename))
         (ponstable       (symbol-value ponstable-name))
         (ponstable-size  (if ponstable (hash-table-size ponstable) 0))
         (ponstable-bytes (hl-ponstable-bytes ponstable))
         (total-bytes     (+ ponstable-bytes table-bytes)))
    (when (or (> ponstable-size 0)
              (> table-size 0)
              (> table-bytes 0)
              (> total-bytes 0))
      (list fn ponstable-size table-size total-bytes))))

#+static-hons
(defun memo-table-size-debug ()
  (cw "Memoize table sizes.  Note: the reported \"overhead\" does NOT include ~
       the sizes of the actual argument/result data stored in the memo ~
       table.~%~%")
  (let ((report nil)
        (indent 0)
        (indent-str nil))
    (maphash (lambda (fn info)
               (let ((entry (memo-table-size-debug1 fn info)))
                 (when entry
                   (push entry report)
                   (setq indent (max indent (length (symbol-name fn)))))))
             *memoize-info-ht*)
    (setq indent-str (format nil "~a" (+ 2 indent)))
    (format t (concatenate 'string "~" indent-str ":@a ~12:@a ~12:@a ~26:@a~%")
            "Function" "PT-Size" "MT-Size" "Approx. Overhead")
    (loop for entry in report do
          (format t (concatenate 'string "~" indent-str ":@a ~12:D ~12:D ~20:D bytes~%")
                  (first entry)
                  (second entry)
                  (third entry)
                  (fourth entry)))
    (format t "~%")))


(defun hons-analyze-memory (slowp)
  (hl-maybe-initialize-default-hs)
  #+static-hons
  (progn
    (hl-hspace-analyze-memory slowp *default-hs*)
    (memo-table-size-debug)
    (print-memo-max-sizes))
  #-static-hons
  (cw "Hons-analyze-memory is only available for static honsing.~%"))


#||

(lp)

(defun my-function (a b c d)
  (declare (xargs :guard t))
  (list a b c d))

(memoize 'my-function)

:q

(loop for i from 1 to 10000 do
      (my-function 1 2 (+ i (ash 1 62)) (+ i (ash 1 100))))

(memoize-table-size-debug)

||#
