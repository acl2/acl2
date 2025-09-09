; misc-events.lisp                             Warren A. Hunt, Jr.

; WAH,Jr.

(in-package "ACL2")

; To monitor a rewrite rule <rewrite-rule>:
; :brr t
; :monitor (:rewrite <rewrite-rule>) t


; Read about TYPE-PRESCRIPTION rules.

; (set-gag-mode nil)  ; To get all output.


; Some miscellaneous definitions.

(defmacro ! (x y)
  (declare (xargs :guard (symbolp x)))
  `(assign ,x ,y))

(defmacro !! (variable new-value)
  ;; Assign without printing the result.
  (declare (xargs :guard t))
  `(mv-let
    (erp result state)
    (assign ,variable ,new-value)
    (declare (ignore result))
    (value (if erp 'Error! ',variable))))


; Some help with some arithmetic issues.

(local (include-book "arithmetic-5/top" :dir :system))

(defmacro with-arithmetic-help-5 (&rest forms)
  `(encapsulate
    ()
    (local (include-book "arithmetic-5/top" :dir :system))
    (set-default-hints '((nonlinearp-default-hint
                          stable-under-simplificationp
                          hist
                          pspv)))
    ,@forms))

; Functions repeatedly used in processor definitions:
;   LOGAND, LOGIOR, LOGXOR, LOGNOT, and ASH.

; When using such function, I want to know that the result is a
; bounded, natural number.  In each of the LOGNOT, this isn't true,
; because any positive number become negative; thus, any use of LOGNOT
; will likely be wrapped inside a LOGAND.

; ASH rules

(with-arithmetic-help-5
 (defthm ash-negative-shift-makes-input-smaller

; The syntaxp hypothesis below probably speeds up proofs significantly towards
; the end of y86/read-over-write.lisp.

   (implies (and (syntaxp (and (quotep shift)
                               (integerp (cadr shift))
                               (< (cadr shift) 0)))
                 (integerp x)
                 (< 0 x)
                 (integerp shift)
                 (< shift 0))
            (< (ash x shift) x))
   :rule-classes :linear))

; LOGAND rules.

(with-arithmetic-help-5
 (defthm logand-less-than-or-equal
   ;; Is this rule ever used?
   (implies (natp x)
            (and (<= (binary-logand x y) x)
                 (<= (binary-logand y x) x)))
   :hints (("Goal" :cases ((equal x 0))))
   :rule-classes :linear))

(with-arithmetic-help-5
 (defthm logand-greater-or-equal-to-zero
   ;; (NATP (LOGAND x y))
   (implies (or (natp x) (natp y))
            (and (integerp (binary-logand x y))
                 (<= 0 (binary-logand x y))
                 ;; (integerp (binary-logand y x))
                 ;; (<= 0 (binary-logand y x))
                 ))
   :hints (("Goal" :cases ((equal x 0))))
   :rule-classes :type-prescription))

; LOGIOR rules.

(with-arithmetic-help-5
 (defthm logior-greater-or-equal-to-zero
   ;; (NATP (LOGIOR x y))
   (implies (and (natp x) (natp y))
            (and (integerp (logior x y))
                 (<= 0 (logior x y))
                 ;; (<= 0 (logior y x))
                 ))
   :rule-classes
   (:type-prescription
    (:linear :corollary ; needed for x86-32p-wm16 in x86-state.lisp
             (implies (and (natp x) (natp y))
                      (<= 0 (logior x y)))))))

(encapsulate
 ()
 (local
  (defun ind-hint-3 (x y n)
    (if (or (zp x) (zp y) (zp n))
        42
      (ind-hint-3 (floor x 2) (floor y 2) (+ -1 n)))))

 (local
  (defthm break-logior-apart
    (implies (and (natp x)
                  (natp y))
             (equal (logior x y)
                    (+ (* 2 (logior (floor x 2)
                                    (floor y 2)))
                       (logior (mod x 2)
                               (mod y 2)))))
    :rule-classes nil))

 (defthm logior-less-than-or-equal
   (implies (and (natp x) (natp y)
                 (< x (expt 2 n))
                 (< y (expt 2 n)))
            (< (logior x y) (expt 2 n)))

   :hints (("Goal" :induct (ind-hint-3 x y n))
           ("Subgoal *1/2.10'4'" :use ((:instance break-logior-apart)))
           ("Subgoal *1/2.9'4'" :use ((:instance break-logior-apart)))
           ("Subgoal *1/2.6'4'" :use ((:instance break-logior-apart))))
   :rule-classes :linear))


; LOGXOR rules.

(encapsulate
 ()

 (local
  (defun ind-hint-3 (x y n)
    (if (or (zp x) (zp y) (zp n))
        42
      (ind-hint-3 (floor x 2) (floor y 2) (+ -1 n)))))

 (local
  (defthm break-logxor-apart
    (implies (and (natp x)
                  (natp y))
             (equal (logxor x y)
                    (+ (* 2 (logxor (floor x 2)
                                    (floor y 2)))
                       (logxor (mod x 2)
                               (mod y 2)))))
    :rule-classes nil))

 (local
  (defun ind-hint-2 (x y)
    (if (or (zp x) (zp y))
        42
      (ind-hint-2 (floor x 2) (floor y 2)))))

 (defthm logxor-greater-or-equal-to-zero
   ;; (NATP (LOGXOR x y))
   (implies (and (natp x) (natp y))
            (and (integerp (logxor x y))
                 (<= 0 (logxor x y))
                 ;; (integerp (logxor y x))
                 ;; (<= 0 (logxor y x))
                 ))

   :hints (("Goal" :induct (ind-hint-2 x y)))
   :rule-classes :type-prescription)

 ;; This next rule would be a weird rewrite rule because of the (EXPT
 ;; 2 N) in the conclusion.  As a linear rule, then entire conclusion
 ;; doesn't need to match.

 (defthm logxor-<=-expt-2-to-n
   (implies (and (natp x) (natp y)
                 (< x (expt 2 n))
                 (< y (expt 2 n)))
            (< (logxor x y) (expt 2 n)))

   :hints (("Goal" :induct (ind-hint-3 x y n))
           ("Subgoal *1/2.6'4'" :use ((:instance break-logxor-apart)))
           ("Subgoal *1/2.10'4'" :use ((:instance break-logxor-apart))))
   :rule-classes :linear)

 )

(with-arithmetic-help-5
 (defthm integerp-mod-rewrite
   (implies (and (integerp x)
                 (integerp y))
            (integerp (mod x y)))))


(defun gl-int (start by count)
  (declare (xargs :guard (and (natp start)
                              (natp by)
                              (natp count))))
  (if (zp count)
      nil
    (cons start
          (gl-int (+ by start) by (1- count)))))


; Below are some functions and macros to assist with defining
; bit-field information.

(defun reg-info-alistp (alst position max-size)
  ;; Recongnizer for register information
  (declare (xargs :guard (and (natp position)
                              (natp max-size))))
  (if (atom alst)
      (null alst)
    (let ((entry (car alst)))
      (and (consp entry)
           (consp (cdr entry))
           (consp (cddr entry))
           (null (cdddr entry))
           (let ((key (car entry))
                 (pos (cadr entry))
                 (width (caddr entry)))
             (and (or (keywordp key)
                      (and (natp key)
                           (or (= key 0)
                               (= key 1))))
                  (natp pos)
                  (natp width)
                  (= position pos)
                  (<= (+ pos width) max-size)
                  (reg-info-alistp (cdr alst)
                                   (+ pos width)
                                   max-size)))))))

(defun x86-flg-field-pos-width (flg reg-info)
  (declare (xargs :guard (symbolp flg)))
  (if (atom reg-info)
      (mv 0 (or (cw "x86-flg-field-pos-width:  Unknown flag:   ~p0.~%" flg) 0))
    (let ((entry (car reg-info)))
      (if (not (and (consp entry)
                    (consp (cdr entry))
                    (consp (cddr entry))
                    (null (cdddr entry))
                    (or (symbolp (car entry))
                        (natp    (car entry)))
                    (natp (cadr entry))
                    (natp (caddr entry))))
          (mv 0 (or (cw "x86-flg-field-pos-width:  Entry malformed:   ~p0.~%" entry) 0))
        (let ((name (car entry))
              (pos  (cadr entry))
              (width (caddr entry)))
          (if (eq name flg)
              (mv pos width)
            (x86-flg-field-pos-width flg (cdr reg-info))))))))

(defun x86-reg-slice (flg reg reg-info)
  (declare (xargs :guard (symbolp flg)))
  (mv-let (pos size)
    (x86-flg-field-pos-width flg reg-info)
    (let ((mask (1- (expt 2 size))))
      `(logand ,mask
               (ash ,reg (- ,pos))))))



(defun x86-reg-field (flg reg reg-info)
  (declare (xargs :guard (symbolp flg)))
  (mv-let (pos size)
    (x86-flg-field-pos-width flg reg-info)
    (let ((mask (1- (expt 2 size))))
      `(logand ,reg
               (ash ,mask ,pos)))))

; The N32 truncation below needs to be parameterized.

(defun x86-update-reg-slice (flg val reg reg-info)
  (declare (xargs :guard (symbolp flg)))
  (mv-let (pos size)
    (x86-flg-field-pos-width flg reg-info)
    (let ((mask (1- (expt 2 size))))
      `(n32 ;; Extra mask -- prove away?  Hard because of (ASH ? POS).
        (logior
         ;; The bit(s) to insert
         (ash (logand ,mask ,val) ,pos)
         ;; Register with bit(s) cleared
         (logand ,reg
                 (lognot ,(ash mask pos))))))))


(defun x86-update-reg-field (flg val reg reg-info)
  (declare (xargs :guard (symbolp flg)))
  (mv-let (pos size)
    (x86-flg-field-pos-width flg reg-info)
    (let ((mask (1- (expt 2 size))))
      `(n32 ;; Extra mask -- prove away?  Hard because of (ASH ? POS).
        (logior
         ;; The bit(s) to insert -- already properly aligned
         ,val
         ;; Register with bit(s) cleared
         (logand ,reg
                 (lognot ,(ash mask pos))))))))

; ======================================================================

; Nat-listp and Integer-listp

(defun nat-listp (l)
  (declare (xargs :guard t))
  (cond ((atom l)
         (eq l nil))
        (t (and (natp (car l))
                (nat-listp (cdr l))))))

(defthm nat-listp-forward
  (implies (nat-listp x)
           (integer-listp x))
  :rule-classes :forward-chaining)

(defthm natp-nth
  (implies (and (nat-listp x)
                (integerp i)
                (<= 0 i)
                (< i (len x)))
           (and (integerp (nth i x))
                (<= 0 (nth i x))))
  :rule-classes :type-prescription)

(defthm nat-listp-forward-to-integer-listp
  (implies (nat-listp x)
           (integer-listp x))
  :rule-classes :forward-chaining)

(defthm integerp-nth
  (implies (and (integer-listp x)
                (integerp i)
                (<= 0 i)
                (< i (len x)))
           (integerp (nth i x)))
  :rule-classes :type-prescription)

; =============================================================================

; Convenient forcing idiom:

(defun formal-force-list (x)
  (declare (xargs :guard (true-listp x)))
  (cond ((endp x) nil)
        (t (cons `(force ,(car x))
                 (formal-force-list (cdr x))))))

(defmacro forced-and (&rest x)
  `(and ,@(formal-force-list x)))

; =============================================================================
