#|
  Book:    computed-hints
  Copyright: (c) 2005 Galois Connections, Inc.
  Author:    Lee Pike, Galois Connections, Inc. <leepike@galois.com>
|#

(in-package "ACL2")

(include-book "symbol-manip")
(include-book "source_shallow")

;; From Robert Krug via Eric Smith.
(defun get-enabled-structure (pspv)
  (strip-cdrs
   (cdr
    (access enabled-structure
            (access rewrite-constant
                    (access prove-spec-var pspv :rewrite-constant)
                    :current-enabled-structure)
            :theory-array))))

(include-book "misc/priorities" :dir :system)
(set-default-hints (list *priority-phased-simplification*))


(defun disable-hint (enables disables)
  `(:in-theory (e/d ,enables
                    ,(append disables
                             `(true-listp natp reverse nat-rep nth zp take
                                          update-nth car consp)))))

;; enables misc. functions in the current context when stable under
;; simplification.
(defun stable-simp-enable-hint1 (susp pspv)
  (if susp `(:IN-THEORY
             (UNION-THEORIES ',(get-enabled-structure pspv)
                             '(true-listp nat-rep natp reverse
                                          zp update-nth car consp)))
    nil))


;; enables c-word-+, c-word-- in the current context when stable under
;; simplification.  These are "special" mCryptol prims since
;; induction needs to open these up stream invariants (most other
;; prims can be kept disabled).
(defun stable-simp-enable-hint3 (susp pspv)
  (if susp `(:IN-THEORY
             (UNION-THEORIES ',(get-enabled-structure pspv)
                             '(c-word-+ c-word--))) nil))

(defun hint-loghead-0 (id)
  (if (equal (caadr id) 1) `(:in-theory (enable loghead-0)) nil))

;; forces the expansion of some functions
(defun hint-expand (id arg-lst itr-name ind-name inv-name)
  (let ((hist-inv-hlps (join-symbols1 inv-name inv-name '|-hist-inv-hlp|)))
    (if (and (equal (cadar id) 1)
             (> (caadr id) 1)
             (equal (len (cadr id)) 2)
             (equal (cddr id) 0))
        `(:expand ((:free ,`(hist)
                           (,itr-name ,@arg-lst 0 1 hist))
                    (:free ,`(hist)
                           (,itr-name ,@arg-lst 0 0 hist))
                    (:free ,`(hist)
                           (,itr-name ,@arg-lst 1 1 hist))
                    (:free ,`(index-name)
                           (,ind-name ,@arg-lst 1 index-name))
                    (:free ,`(index-name)
                           (,ind-name ,@arg-lst 0 index-name))
                    (:free ,`(index-name)
                           (,ind-name ,@arg-lst i index-name))
                    (:free ,`(i hist)
                           (,hist-inv-hlps hist ,@arg-lst i 1))
                    (:free ,`(hist)
                           (,hist-inv-hlps hist ,@arg-lst (+ 1 i) i))
                    (:free ,`(i hist)
                           (,hist-inv-hlps hist ,@arg-lst i 0))))
      nil)))



(defun stable-simp-enable-hint2 (susp pspv)
  (if susp `(:IN-THEORY
             (UNION-THEORIES ',(get-enabled-structure pspv)
                             '(c-word-+
                               c-word--
                               c-word-*
                               c-word-<<
                               c-word->>
                               c-word-**
                               c-word-gcd
                               c-word-min
                               c-word-max
                               c-word-/
                               c-word-%
                               c-word-&&
                               c-word-or
                               c-word-^^
                               c-word-neg
                               c-lg2
                               c-~
                               c-word-<<
                               c-word->>
                               c-word-padd
                               c-word-pmult
                               nbits
                               c-word-pdiv-pmod
                               c-word-pdiv
                               c-word-pmod
                               c-word-pgcd
                               c-word-pinv
                               c-==
                               c-!=
                               c-^
                               c-word-parity
                               c-word-pirred
                               c-vec-<<
                               c-vec->>
                               c-word-<<<
                               c-word->>>
                               c-vec-<<<
                               c-vec->>>
                               c-word-join
                               c-vec-join
                               c-vec-segment
                               c-word-segment
                               c-word-append
                               c-vec-append
                               make-trans-wd
                               c-word-transpose
                               c-vec-transpose
                               c-word-extract
                               c-vec-extract
                               c-word-split
                               c-vec-split
                               c-word-reverse
                               c-vec-reverse
                               c-update-bit)))
    nil))


;; inlined by translator
;; take drop

;; --------------- MISC ---------------------------------
;;oh yeah, this conversion from words to vecs is probably a bad idea for proofs
;;to the AAMP model, so I'll think leave it in and think about this.
(defun log-rep-hlp (x i)
  (let ((val (if (logbitp i x) T NIL)))
  (if (zp i) (list val)
    (cons val (log-rep-hlp x (- i 1))))))

;; Lil' endian representation of x.
;; This must be in ihs?!?!?
(defun log-rep (x)
  (let ((size (nbits x)))
    (if (zp size) (list NIL)
      (reverse (log-rep-hlp x (- size 1))))))

(defun nat-rep-hlp (bin-list i)
  (if (endp bin-list) 0
    (let ((val (if (nth i bin-list) 1 0)))
      (if (zp i) val
	(+ (* val
	      (expt2 i))
	   (nat-rep-hlp bin-list (- i 1)))))))

(defun nat-rep (bin-lst)
  (nat-rep-hlp bin-lst (- (len bin-lst) 1)))

;; Helper needed by iterators yielding bits
(defun c-update-bit (i b w)
  (let ((hi-bits (logtail (+ i 1) w)))
    (logapp i w (logapp 1 b hi-bits))))

(defun measure-hint (id clause world)
  (declare (xargs :mode :program)
           (ignore id clause world))
  '(:in-theory (enable
                c-word-+ c-word--
                c-word-*
                c-word-<<
                c-word->>
                c-word-**
                c-word-gcd
                c-word-min
                c-word-max
                c-word-/
                c-word-%
                c-word-&&
                c-word-or
                c-word-^^
                c-word-neg
                c-lg2
                c-~
                c-word-<<
                c-word->>
                c-word-padd
                c-word-pmult
                nbits
                c-word-pdiv-pmod
                c-word-pdiv
                c-word-pmod
                c-word-pgcd
                c-word-pinv
                c-==
                c-!=
                c-^
                c-word-parity
                c-word-pirred
                c-vec-<<
                c-vec->>
                c-word-<<<
                c-word->>>
                c-vec-<<<
                c-vec->>>
                c-word-join
                c-vec-join
                c-vec-segment
                c-word-segment
                c-word-append
                c-vec-append
                make-trans-wd
                c-word-transpose
                c-vec-transpose
                c-word-extract
                c-vec-extract
                c-word-split
                c-vec-split
                c-word-reverse
                c-vec-reverse
                c-update-bit)))


;; standard priorities for computed hints
(add-priority 1 disable-hint)
(add-priority 2 stable-simp-enable-hint1)
(add-priority 3 stable-simp-enable-hint2)
(disable-prioritized-runes)
