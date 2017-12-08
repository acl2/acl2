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
; Original author: Jared Davis <jared@centtech.com>

; Added by Matt K., 12/8/2017: Some of the code to be executed only when
; #+static-hons has symbols ccl::xxx.  I'm thus replacing the static-hons
; readtime conditional with (and static-hons Clozure).  A more fine-grained fix
; might be possible by tracking down dependencies on functions with bodies that
; contain ccl::xxx symbols.

(in-package "ACL2")

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
  (declare (ignorable clear))

  #+Clozure
  (when (or (eq n t)
            (< (ccl::%freebytes) (nfix n)))
    (format t "********** maybe-wash-memory started ***********~%~%")
    (format t "Pre-wash memory usage.~%")
    (print-quick-memory-summary)
    (hons-wash)
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

#+(and static-hons Clozure)
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


#+(and static-hons Clozure)
(defconstant hl-size-of-cons (hl-sizeof (cons nil nil)))

#+(and static-hons Clozure)
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


#+(and static-hons Clozure)
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


#+(and static-hons Clozure)
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





#+(and static-hons Clozure)
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




#+(and static-hons Clozure)
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

#+(and static-hons Clozure)
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

#+(and static-hons Clozure)
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

#+(and static-hons Clozure)
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
  #+(and static-hons Clozure)
  (progn
    (hl-hspace-analyze-memory slowp *default-hs*)
    (memo-table-size-debug)
    (print-memo-max-sizes))
  #-(and static-hons Clozure)
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
