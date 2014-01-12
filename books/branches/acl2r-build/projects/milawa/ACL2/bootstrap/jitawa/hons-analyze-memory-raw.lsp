(in-package "ACL2")

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

(defun hons-analyze-memory (slowp)
  (hl-maybe-initialize-default-hs)
  #+static-hons
  (hl-hspace-analyze-memory slowp *default-hs*)
  #-static-hons
  (cw "Hons-analyze-memory is only available for static honsing.~%"))
