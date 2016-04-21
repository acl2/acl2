;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")

(include-book "x86-ia32e-paging" :dir :machine)
(include-book "clause-processors/find-subterms" :dir :system)
(local (include-book "centaur/gl/gl" :dir :system))

;; ======================================================================

;; For use in gather-paging-structures-thms.lisp:

(def-gl-export pml4-table-entry-addr-and-gather-pml4-table-qword-addresses-helper-1
  :hyp (and (unsigned-byte-p 52 x)
            (equal (loghead 12 x) 0))
  :concl (equal (logand 18446744073709547527 x)
                x)
  :g-bindings `((x (:g-number ,(gl-int 0 1 53)))))

(def-gl-export pml4-table-entry-addr-and-gather-pml4-table-qword-addresses-helper-2
  :hyp (and (canonical-address-p lin-addr)
            (unsigned-byte-p 52 x))
  :concl (< (logior (ash (loghead 9 (logtail 39 lin-addr))
                         3)
                    x)
            (+ 4096 x))
  :g-bindings `((lin-addr (:g-number ,(gl-int 0 2 65)))
                (x        (:g-number ,(gl-int 1 2 65)))))

(def-gl-export page-dir-ptr-table-entry-addr-is-in-a-table-pointed-to-by-a-pml4e-helper-1-1
  :hyp (and (unsigned-byte-p 64 x)
            (canonical-address-p l))
  :concl (<=
          (ash (loghead 40 (logtail 12 x)) 12)
          (logior (ash (loghead 9 (logtail 30 l)) 3)
                  (logand 18446744073709547527
                          (ash (loghead 40 (logtail 12 x)) 12))))
  :g-bindings `((x (:g-number ,(gl-int 0 2 65)))
                (l (:g-number ,(gl-int 1 2 65))))
  :rule-classes :linear)

(def-gl-export page-dir-ptr-table-entry-addr-is-in-a-table-pointed-to-by-a-pml4e-helper-2-1
  :hyp (and (unsigned-byte-p 64 x)
            (canonical-address-p l))
  :concl (<
          (logior (ash (loghead 9 (logtail 30 l)) 3)
                  (ash (loghead 40 (logtail 12 x)) 12))
          (+ 4096 (ash (loghead 40 (logtail 12 x)) 12)))
  :g-bindings `((x (:g-number ,(gl-int 0 2 65)))
                (l (:g-number ,(gl-int 1 2 65))))
  :rule-classes :linear)

(def-gl-export page-directory-entry-addr-is-in-a-table-pointed-to-by-a-pdpte-helper-1
  :hyp (and (unsigned-byte-p 64 x)
            (canonical-address-p l))
  :concl (<
          (logior (ash (loghead 9 (logtail 21 l)) 3)
                  (ash (loghead 40 (logtail 12 x)) 12))
          (+ 4096 (ash (loghead 40 (logtail 12 x)) 12)))
  :g-bindings `((x (:g-number ,(gl-int 0 2 65)))
                (l (:g-number ,(gl-int 1 2 65))))
  :rule-classes :linear)

(def-gl-export page-table-entry-addr-is-in-a-table-pointed-to-by-a-pde-helper-1
  :hyp (and (unsigned-byte-p 64 x)
            (canonical-address-p l))
  :concl (<
          (logior (ash (loghead 9 (logtail 12 l)) 3)
                  (ash (loghead 40 (logtail 12 x)) 12))
          (+ 4096 (ash (loghead 40 (logtail 12 x)) 12)))
  :g-bindings `((x (:g-number ,(gl-int 0 2 65)))
                (l (:g-number ,(gl-int 1 2 65))))
  :rule-classes :linear)

;; For use in paging-basics.lisp and x86-isa32e-paging-alt.lisp:

(def-gl-export 4K-aligned-physical-address-helper
  :hyp (and (unsigned-byte-p 52 x)
            (equal (loghead 12 x) 0))
  :concl (equal (logand 18446744073709547520 x)
                x)
  :g-bindings `((x (:g-number ,(gl-int 0 1 53)))))

(def-gl-export nests-of-set-accessed-bit
  :hyp (unsigned-byte-p 64 e)
  :concl (equal (set-accessed-bit (set-accessed-bit e))
                (set-accessed-bit e))
  :g-bindings `((e (:g-number ,(gl-int 0 1 65)))))

(def-gl-export nests-of-set-dirty-bit
  :hyp (unsigned-byte-p 64 e)
  :concl (equal (set-dirty-bit (set-dirty-bit e))
                (set-dirty-bit e))
  :g-bindings `((e (:g-number ,(gl-int 0 1 65)))))

(def-gl-export pull-out-set-dirty-bit
  :hyp (unsigned-byte-p 64 e)
  :concl (equal (set-accessed-bit (set-dirty-bit e))
                (set-dirty-bit (set-accessed-bit e)))
  :g-bindings `((e (:g-number ,(gl-int 0 1 65)))))

;; For use in paging-*-table-lemmas:

(def-gl-export logand-loghead-and-page-dir-ptr-table-base-addr-helper
  :hyp (unsigned-byte-p 64 x)
  :concl (equal (logand 18446744072635809792 (ash (loghead 22 (logtail 30 x)) 30))
                (ash (loghead 22 (logtail 30 x)) 30))
  :g-bindings `((x (:g-number ,(gl-int 0 1 65)))))

(def-gl-export logand-loghead-and-page-directory-base-addr-helper
  :hyp (unsigned-byte-p 64 x)
  :concl (equal (logand 18446744073709547520 (ash (loghead 40 (logtail 12 x)) 12))
                (ash (loghead 40 (logtail 12 x)) 12))
  :g-bindings `((x (:g-number ,(gl-int 0 1 65)))))


;; ======================================================================

(def-gl-export rm32-rb-system-level-mode-proof-helper
  :hyp (and (n08p a)
            (n08p b)
            (n08p c)
            (n08p d))
  :concl (equal (logior a (ash b 8) (ash (logior c (ash d 8)) 16))
                (logior a (ash (logior b (ash (logior c (ash d 8)) 8)) 8)))
  :g-bindings
  (gl::auto-bindings
   (:mix (:nat a 8) (:nat b 8) (:nat c 8) (:nat d 8))))

(def-gl-export rm64-to-rb-in-system-level-mode-helper
  :hyp (and (n08p a) (n08p b) (n08p c) (n08p d)
            (n08p e) (n08p f) (n08p g) (n08p h))
  :concl (equal
          (logior a
                  (ash (logior b (ash (logior c (ash d 8)) 8)) 8)
                  (ash (logior e (ash (logior f (ash (logior g (ash h 8)) 8)) 8)) 32))
          (logior
           a
           (ash (logior
                 b
                 (ash (logior
                       c
                       (ash (logior d
                                    (ash
                                     (logior e
                                             (ash
                                              (logior f
                                                      (ash (logior g (ash h 8)) 8)) 8)) 8)) 8)) 8)) 8)))
  :g-bindings
  (gl::auto-bindings
   (:mix (:nat a 8) (:nat b 8) (:nat c 8) (:nat d 8)
         (:nat e 8) (:nat f 8) (:nat g 8) (:nat h 8))))

(def-gl-export rm-low-64-and-write-to-physical-memory-equal-helper-2
  :hyp (and (n08p a) (n08p b) (n08p c) (n08p d)
            (n08p e) (n08p f) (n08p g) (n08p h))
  :concl (equal
          (logior (ash b 8)
                  (ash (logior (ash d 8)
                               c)
                       16)
                  (ash (logior (ash f 8)
                               (ash (logior (ash h 8)
                                            g)
                                    16)
                               e)
                       32)
                  a)
          (logior
           a
           (ash
            (logior
             b
             (ash
              (logior
               c
               (ash
                (logior
                 d
                 (ash
                  (logior e
                          (ash (logior f
                                       (ash (logior g
                                                    (ash h 8))
                                            8))
                               8))
                  8))
                8))
              8))
            8)))
  :g-bindings
  (gl::auto-bindings
   (:mix (:nat a 8) (:nat b 8) (:nat c 8) (:nat d 8)
         (:nat e 8) (:nat f 8) (:nat g 8) (:nat h 8))))

(in-theory (e/d () (rm-low-64-and-write-to-physical-memory-equal-helper-2)))

;; ======================================================================

;; Some misc. utils for bind-free, etc.:

(defun get-subterm-from-list-of-terms (n x)
  (declare (xargs :guard (and (natp n) (pseudo-term-listp x))))
  ;; E.g.:
  ;; (get-subterm-from-list-of-terms 1 '((las-to-pas l-addrs-1 r-w-x cpl x86)
  ;;                                     (las-to-pas l-addrs-2 r-w-x cpl x86)
  ;;                                     (las-to-pas l-addrs-2 r-w-x cpl x86)
  ;;                                     (foo x)))
  (if (atom x)
      nil
    (cons (nth n (acl2::list-fix (car x)))
          (get-subterm-from-list-of-terms n (cdr x)))))

(define make-bind-free-alist-lists (var values)
  (if (atom values)
      nil
    (cons (acons var (car values) nil)
          (make-bind-free-alist-lists var (cdr values)))))

(defun find-l-addrs-from-fn
  (fn l-addrs-var mfc state)
  (declare (xargs :stobjs (state) :mode :program)
           (ignorable state))
  (b* ((calls (acl2::find-calls-lst fn (acl2::mfc-clause mfc)))
       ((when (not calls))
        ;; fn term not encountered.
        nil)
       (l-addrs (get-subterm-from-list-of-terms 1 calls))
       (alst-lst (make-bind-free-alist-lists l-addrs-var l-addrs)))
    alst-lst))

(defun find-info-from-program-at-term (thm mfc state)
  (declare (xargs :stobjs (state) :mode :program)
           (ignorable thm state))
  (b* ((call (acl2::find-call-lst 'program-at (acl2::mfc-clause mfc)))
       ((when (not call))
        ;; (cw "~%~p0: Program-At term not encountered.~%" thm)
        nil)
       (addresses (cadr call))
       ((when (not (equal (car addresses)
                          'create-canonical-address-list)))
        ;; (cw "~%~p0: Program-At without Create-Canonical-Address-List encountered.~%" thm)
        nil)
       (n (cadr addresses))
       (prog-addr (caddr addresses))
       (bytes (caddr call)))
    `((n . ,n)
      (prog-addr . ,prog-addr)
      (bytes . ,bytes))))

(defun find-l-addrs-from-las-to-pas
  (l-addrs-var mfc state)
  (declare (xargs :stobjs (state) :mode :program)
           (ignorable state))
  (b* ((calls (acl2::find-calls-lst 'las-to-pas (acl2::mfc-clause mfc)))
       ((when (not calls))
        ;; las-to-pas term not encountered.
        nil)
       (l-addrs (get-subterm-from-list-of-terms 1 calls))
       (alst-lst (make-bind-free-alist-lists l-addrs-var l-addrs)))
    alst-lst))

(defun find-almost-matching-ia32e-la-to-pas-aux (free-r-w-x-var new-arg-lists original-arg-list)
  (if (endp new-arg-lists)
      nil
    (b* ((new-arg-list (car new-arg-lists))
         (matching? (and (equal (first new-arg-list)  (first original-arg-list)) ;; lin-addr
                         (not (equal (second new-arg-list) (second original-arg-list))) ;; r-w-x
                         (equal (third new-arg-list)  (third original-arg-list)) ;; cpl
                         (equal (fourth new-arg-list) (fourth original-arg-list))))) ;; x86
      (if matching?
          (cons (acons free-r-w-x-var ;; original r-w-x
                       (second new-arg-list)
                       nil)
                (find-almost-matching-ia32e-la-to-pas-aux free-r-w-x-var (cdr new-arg-lists) original-arg-list))
        (find-almost-matching-ia32e-la-to-pas-aux free-r-w-x-var (cdr new-arg-lists) original-arg-list)))))

(defun find-almost-matching-ia32e-la-to-pas
  (fn-name free-r-w-x-var original-arg-list mfc state)
  (declare (xargs :stobjs (state) :mode :program)
           (ignorable state))
  (b* ((calls (acl2::find-calls-lst fn-name (acl2::mfc-clause mfc)))
       ((when (not calls))
        ;; ia32e-la-to-pa term not encountered.
        nil)
       (new-arg-lists (strip-cdrs calls)))
    (find-almost-matching-ia32e-la-to-pas-aux free-r-w-x-var new-arg-lists original-arg-list)))

;; ======================================================================
