; Printing an R1CS in a more human-readable format.
;
; Copyright (C) 2025 Kestrel Institute (https://www.kestrel.edu)
; Copyright (C) 2025 Provable Inc. (https://www.provable.com)
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric McCarthy (bendyarm on GitHub)

(In-package "R1CS")

(include-book "kestrel/crypto/r1cs/sparse/r1cs" :dir :system)

(include-book "std/util/add-io-pairs" :dir :system)

(include-book "kestrel/crypto/primes/bn-254-group-prime" :dir :system)
(acl2::merge-io-pairs
 dm::primep
 (include-book "projects/bls12-377-curves/primes/bls12-377-prime" :dir :system))

(include-book "std/strings/decimal" :dir :system)

;; If you don't do this you get a program-mode-only str::pretty
(include-book "std/strings/pretty" :dir :system)

(local
 (include-book "kestrel/alists-light/assoc-equal" :dir :system)
 )

; These should be in std/lists without a backchain limit
(local
 (defthmd iff-consp-when-true-listp
     (implies (true-listp x)
              (iff (consp x) x)))
 )
(local
 (defthmd true-listp-of-cdr
     (implies (true-listp l)
              (true-listp (cdr l))))
 )

(defmacro fp1 () '(primes::bn-254-group-prime))
(defmacro fp2 () '(primes::bls12-377-scalar-field-prime))

;; returns a list of pairs like (8 "2^3")
;; for all exponents from EXP-FROM up to but not including EXP-TO.
;; Addend must be -1, 0, or 1
(defun powers-of-2-and-strings (fp exp-from exp-to addend)
  (declare (type  (integer -1 1) addend))
  (declare (xargs :guard (and (natp exp-from) (posp exp-to)
                              (<= exp-from exp-to)
                              (member fp (list (fp1) (fp2))))))
  (declare (xargs :measure (nfix (- exp-to exp-from))))
  (if (or (not (natp exp-from)) (not (natp exp-to)) (>= exp-from exp-to))
      nil
      (cons (list (pfield::add (pfield::pow 2 exp-from fp) (mod addend fp) fp)
                  (if (zerop addend)
                      (str::cat "2^" (str::int-to-dec-string exp-from))
                      (str::cat "(2^" (str::int-to-dec-string exp-from) ")"
                                (if (= addend 1) "+1"
                                    (if (= addend -1) "-1"
                                        "error")))))
            (powers-of-2-and-strings fp (+ 1 exp-from) exp-to addend))))

;; returns a list of pairs like
;; (21888242871839275222246405745257275088548364400416034343698204186575808495586 "-(2^5)+1")
;; for all exponents from EXP-FROM up to but not including EXP-TO.
;; Addend must be -1, 0, or 1
(defun negative-powers-of-2-and-strings (fp exp-from exp-to addend)
  (declare (type  (integer -1 1) addend))
  (declare (xargs :guard (and (natp exp-from) (posp exp-to)
                              (<= exp-from exp-to)
                              (member fp (list (fp1) (fp2))))))
  (declare (xargs :measure (nfix (- exp-to exp-from))))
  (if (or (not (natp exp-from)) (not (natp exp-to)) (>= exp-from exp-to))
      nil
      (cons (list (pfield::add (pfield::neg (pfield::pow 2 exp-from fp) fp) (mod addend fp) fp)
                  (if (zerop addend)
                      (str::cat "-(2^" (str::int-to-dec-string exp-from) ")")
                      (str::cat "-(2^" (str::int-to-dec-string exp-from) ")"
                                (if (= addend 1) "+1"
                                    (if (= addend -1) "-1"
                                        "error")))))
            (negative-powers-of-2-and-strings fp (+ 1 exp-from) exp-to addend))))

(defun small-halves-and-strings (fp)
  (declare (xargs :guard (member fp (list (fp1) (fp2)))))
  (list (list (pfield::div 1 2 fp) "1/2")
        (list (pfield::div 3 2 fp) "3/2")
        (list (pfield::div (pfield::neg 1 fp) 2 fp) "-1/2")
        (list (pfield::div (pfield::neg 3 fp) 2 fp) "-3/2")))

;; Returns a list of pairs like
;;  (19152212512859365819465605027100115702479818850364030050735928663253832433665 "1/2^3")
;; for all exponents from EXP-FROM up to but not including EXP-TO.
;; EXP-FROM must be at least 2.
;; Addend may be 0 or 1.
(defun powers-of-1/2-and-strings (fp exp-from exp-to addend)
  (declare (type  (integer 0 1) addend))
  (declare (xargs :guard (and (natp exp-from) (natp exp-to)
                              (< 1 exp-from) (< 2 exp-to)
                              (<= exp-from exp-to)
                              (member fp (list (fp1) (fp2))))))
  (declare (xargs :measure (nfix (- exp-to exp-from))))
  (if (or (not (natp exp-from)) (not (natp exp-to)) (>= exp-from exp-to))
      nil
      (let ((pow (pfield::pow 2 exp-from fp)))
        ;; this can't happen, but the prover doesn't know that
        (if (= pow 0) (list 0 "error")
            (cons (list (pfield::add (pfield::inv pow fp) (mod addend fp) fp)
                        (if (zerop addend)
                            (str::cat "1/2^" (str::int-to-dec-string exp-from))
                            (str::cat "1+(1/2^" (str::int-to-dec-string exp-from) ")")))
                  (powers-of-1/2-and-strings fp (+ 1 exp-from) exp-to addend))))))

;;
;; Returns a list of pairs like when addend is 0:
;;   (2736030358979909402780800718157159386068545550052004292962275523321976061952 "-1/2^3")
;; or addend is 1:
;;   (2736030358979909402780800718157159386068545550052004292962275523321976061953 "1-(1/2^3)")
;; for all exponents from EXP-FROM up to but not including EXP-TO.
;; EXP-FROM must be at least 2.
;; Addend may be 0 or 1.
(defun negative-powers-of-1/2-and-strings (fp exp-from exp-to addend)
  (declare (type  (integer 0 1) addend))
  (declare (xargs :guard (and (natp exp-from) (natp exp-to)
                              (< 1 exp-from) (< 2 exp-to)
                              (<= exp-from exp-to)
                              (member fp (list (fp1) (fp2))))))
  (declare (xargs :measure (nfix (- exp-to exp-from))))
  (if (or (not (natp exp-from)) (not (natp exp-to)) (>= exp-from exp-to))
      nil
      (let ((pow (pfield::pow 2 exp-from fp)))
        ;; this can't happen, but the prover doesn't know that
        (if (= pow 0) (list 0 "error")
            (cons (list (pfield::sub (mod addend fp) (pfield::inv pow fp) fp)
                        (if (zerop addend)
                            (str::cat "-1/2^" (str::int-to-dec-string exp-from))
                            (str::cat "1-(1/2^" (str::int-to-dec-string exp-from) ")")))
                  (negative-powers-of-1/2-and-strings fp (+ 1 exp-from) exp-to addend))))))

;; Generate the nums-to-strings data structure for the given prime.
;; PRIME should be one of the supported primes (currently fp1 and fp2).
(defund nums-to-strings (prime)
  (declare (xargs :guard (member prime (list (fp1) (fp2)))))
  (macrolet ((nums-to-strings-for-prime (fp)
               `(append
                 ;; Display all numbers of the form 2^n, (2^n)+1, (2^n)-1, like that,
                 ;; for 11 <= n < 254.
                 (powers-of-2-and-strings ,fp 11 254 0)
                 (powers-of-2-and-strings ,fp 11 254 1)
                 (powers-of-2-and-strings ,fp 11 254 -1)
                 ;; Similarly for -(2^n), -(2^n)+1, -(2^n)-1
                 (negative-powers-of-2-and-strings ,fp 11 254 0)
                 (negative-powers-of-2-and-strings ,fp 11 254 1)
                 (negative-powers-of-2-and-strings ,fp 11 254 -1)
                 ;; Display 1/2, 3/2, -1/2, -3/2 like that.
                 (small-halves-and-strings ,fp)
                 ;; Display 1/2^n , -1/2^n , 1-(1/2^n) , 1+(1/2^n) like that for 2 <= n < 254
                 (powers-of-1/2-and-strings ,fp 2 254 0)
                 (negative-powers-of-1/2-and-strings ,fp 2 254 0)
                 (powers-of-1/2-and-strings ,fp 2 254 1)
                 (negative-powers-of-1/2-and-strings ,fp 2 254 1))))
    (cond ((equal prime (fp1)) (nums-to-strings-for-prime (fp1)))
          ((equal prime (fp2)) (nums-to-strings-for-prime (fp2)))
          (t (er hard 'nums-to-strings
                 "Unsupported prime: ~x0. Currently supported primes are ~x1 and ~x2."
                 prime (fp1) (fp2))))))

;; Cache the results for the two current primes
(ACL2::add-io-pairs (((nums-to-strings (fp1)) (nums-to-strings (fp1)))
                     ((nums-to-strings (fp2)) (nums-to-strings (fp2)))))

(in-theory (disable (:e nums-to-strings)))

(defthm alistp-of-nums-to-strings-fp1
    (alistp (nums-to-strings (fp1)))
  :hints (("Goal" :in-theory (enable nums-to-strings))))

(defthm alistp-of-nums-to-strings-fp2
    (alistp (nums-to-strings (fp2)))
  :hints (("Goal" :in-theory (enable nums-to-strings))))

;generalized predicate for alist format of nums-to-strings
(defun natural-to-singleton-string-list-alistp (alist)
  (declare (xargs :guard t))
  (if (atom alist)
      (null alist)
    (and (consp (car alist))
         (let ((entry (car alist)))
           (and (consp entry)
                (natp (car entry))
                (consp (cdr entry))
                (stringp (cadr entry))
                (null (cddr entry))))
         (natural-to-singleton-string-list-alistp (cdr alist)))))

;theorem that shows cadr of every entry in this alist format is a string
(defthm nat-single-string-list-alist-implies-stringp-values
  (implies (and (natural-to-singleton-string-list-alistp alist)
                (assoc-equal key alist))
           (stringp (cadr (assoc-equal key alist))))
  :hints (("Goal" :in-theory (enable assoc-equal))))

;;This shows there are no collisions:
;;(assert-equal (len *nums-to-strings*) (len (remove-duplicates (strip-cars *nums-to-strings*))))

(defun p1cs-negative (fp x)
  (declare (xargs :guard (and (natp fp) (< 1 fp) (integerp x))))
  (if (> x (/ fp 2))
      (str::int-to-dec-string (- x fp))
      nil))

(defun p1cs-coefficient (fp term)
  (declare (xargs :guard (and (member fp (list (fp1) (fp2)))
                              (sparse-vector-elementp term))
                  :guard-hints (("Goal" :in-theory (e/d (nums-to-strings) (assoc-equal))))))

  ;; Look up in nums-to-strings for the given prime
  (let ((nums-to-strings-for-prime (nums-to-strings fp)))
    (let ((pair (assoc (first term) nums-to-strings-for-prime)))
      (if pair
          (second pair)
          ;; Next try p1cs-negative
          (let ((possible-negative (p1cs-negative fp (first term))))
            (or possible-negative
                ;; Otherwise just print the integer normally
                (str::int-to-dec-string (first term))))))))
;;  TODO: try Dave Greve's minimal fraction code (ACL2 Workshop 2020).
;;  Does it work for small negative fractions?


(defthm p1cs-neg-string
    (implies (p1cs-negative fp x)
             (stringp (p1cs-negative fp x))))

;these theorems become much more efficient
(defthm stringp-of-nums-to-strings-fp1-values
  (implies (assoc-equal x (nums-to-strings (fp1)))
           (stringp (cadr (assoc-equal x (nums-to-strings (fp1))))))
  :hints (("Goal" :in-theory (enable nums-to-strings))))

(defthm stringp-of-nums-to-strings-fp2-values
  (implies (assoc-equal x (nums-to-strings (fp2)))
           (stringp (cadr (assoc-equal x (nums-to-strings (fp2))))))
  :hints (("Goal" :in-theory (enable nums-to-strings))))

(defun p1cs-var (term)
  (declare (xargs :guard (sparse-vector-elementp term)))
  (if (symbolp (second term))
      ;; Skip the package prefix and the vertical bars.
      ;; This would be unsafe if the vars were not aleady unique
      ;; or did not have print-read equivalence.
      (str::cat (symbol-name (second term)))
      (if (not (equal (second term) 1) ) ; (equal term '(quote 1))))
          "error"
          "" ; we don't want to see 3.1 meaning "3 times 1", so leave off the var
; named "1"
          )))

(defthm p1cs-coefficient-returns-string
    (implies (and (member fp (list (fp1) (fp2)))
                  (sparse-vector-elementp term))
             (stringp (p1cs-coefficient fp term)))
  :hints (("Goal" :in-theory (e/d (nums-to-strings)
                                  (p1cs-negative assoc-equal)))))

(defun p1cs-term (fp term)
  (declare (xargs :guard (and (member fp (list (fp1) (fp2)))
                              (sparse-vector-elementp term))
                  :guard-hints (("Goal" :in-theory (disable p1cs-coefficient
                                                            p1cs-negative)))))
  (let ((coeff-string (p1cs-coefficient fp term))
        (var-or-empty (p1cs-var term)))
    (str::cat
     (if (equal "" var-or-empty)
         ;; This means it is the pseudo-var 1,
         ;; so we just print the coefficient, no dot or var
         coeff-string
         (if (equal coeff-string "1")
             ""
             (if (equal coeff-string "-1")
                 "-"
                 (str::cat coeff-string "."))))
     var-or-empty)))

;; print the rest of an r1cs sparse vector
(defun p1cs-sv-rest (fp sv)
  (declare (xargs :guard (and (member fp (list (fp1) (fp2)))
                              (sparse-vectorp sv))))
  (if (atom sv) ""
      (let* ((term (first sv))
             (printed-term (p1cs-term fp term))
             (operator-and-printed-term
              (if (and (< 0 (length printed-term))
                       (equal #\- (char printed-term 0)))
                  (str::cat " - "
                            (subseq printed-term 1 (length printed-term)))
                  (str::cat " + " printed-term))))
        (str::cat
         operator-and-printed-term
         (p1cs-sv-rest fp (rest sv))))))

;; print a r1cs sparse vector
;; (R1CS::A (coeff var) (coeff var) ..)
(defun p1cs-sv (fp sv)
  (declare (xargs :guard (and (member fp (list (fp1) (fp2)))
                              (sparse-vectorp sv))))
  (if (atom sv) ""
      (let ((term (first sv)))
        (str::cat
         (p1cs-term fp term)
         (p1cs-sv-rest fp (rest sv))))))

;; Note, changing the following margin using
;; !>:redef
;; doesn't seem to work, even with the ":normalize nil" declaration below.
;; For example, you might have a constraint like this:
;; (w1) * (-1207456172096108210275638375738552290546525293551528575469134455422838636547.w756) = (w757 - w756)
;; Then if you redefine this nullary function to return 100 (note: it is in the r1cs package)
;; and rerun the call to p1cs, it still prints it like it the example two lines above.
;; But if you then recompile p1cs1 and rerun the call to p1cs, it is printed correctly:
;; (w1) * (-1207456172096108210275638375738552290546525293551528575469134455422838636547.w756)
;;   = (w757 - w756)
;; IMHO this silent inlining should be considered a bug.

(defun p1cs1-right-margin ()
  (declare (xargs :guard t))
  120)

(defun p1cs1 (fp constraint)
  (declare (xargs :guard (and (member fp (list (fp1) (fp2)))
                              (r1cs-constraintp constraint)
                              (sparse-vectorp (r1cs-constraint->a constraint))
                              (sparse-vectorp (r1cs-constraint->b constraint))
                              (sparse-vectorp (r1cs-constraint->c constraint)))
                  :normalize nil)) ; this is supposed to make a redef of p1cs1-right-margin work
  (let ((a-string (str::cat "(" (p1cs-sv fp (r1cs-constraint->a constraint)) ")"))
        (b-string (str::cat "(" (p1cs-sv fp (r1cs-constraint->b constraint)) ")"))
        (c-string (let ((c-constraint (r1cs-constraint->c constraint)))
                    (if (null c-constraint)
                        "0"
                        (str::cat "(" (p1cs-sv fp c-constraint) ")")))))
    (if (> (+ (length a-string) 3 (length b-string))
           (p1cs1-right-margin))
        ;; If a+b overflow, put each of a,b,c on its own line
        (str::cat a-string (string #\Newline)
                  "  * " b-string (string #\Newline)
                  "  = " c-string)
        (if (> (+ (length a-string) 3 (length b-string) 3 (length c-string))
               (p1cs1-right-margin))
            ;; If the whole thing overflows but not a+b, just put c on its own line
            (str::cat a-string " * " b-string (string #\Newline)
                      "  = " c-string)
            ;; Otherwise just use one line
            (str::cat a-string " * " b-string " = " c-string)))))

(defun p1csn (fp constraints)
  (declare (xargs :guard (and (member fp (list (fp1) (fp2)))
                              (r1cs-constraint-listp constraints))))
  (if (atom constraints)
      nil
      (cons (p1cs1 fp (car constraints))
            (p1csn fp (cdr constraints)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; If linear combination lc has a constant term, returns the coefficient.
; Otherwise returns 0.
(defun lc-constant-term (lc)
  (declare (xargs :guard (sparse-vectorp lc)))
  (if (atom lc)
      0
      (let ((term (first lc)))
        (if (equal (second term) 1)
            ;; return coefficient
            (first term)
            (lc-constant-term (cdr lc))))))

(defthm lc-constant-term-result-is-integer
    (implies (sparse-vectorp lc)
             (integerp (lc-constant-term lc))))

;; This should be moved to the ACL2 community books
;; in acl2/books/kestrel/crypto/r1cs/sparse/r1cs.lisp
(defund lc-termp (l)
  (declare (xargs :guard t))
  (and (true-listp l)
       (= 2 (len l))
       (integerp (first l))
       (pseudo-varp (second l))))

; Returns the first term in lc that is not a constant.
; If there is no term that has a variable, returns nil.
(defun lc-first-var-term (lc)
  (declare (xargs :guard (sparse-vectorp lc)))
  (if (atom lc)
      nil
      (let ((term (first lc)))
        (if (symbolp (second term))
            term
            (lc-first-var-term (rest lc))))))

(defthm lc-first-var-term-result-is-term-or-nil
    (b* ((term  (lc-first-var-term lc)))
      (implies (and (sparse-vectorp lc)
                    term)
               (lc-termp term)))
  :hints (("Goal" :in-theory (enable lc-first-var-term lc-termp)))
  )

(defthmd true-listp-of-lc-first-var-term
    (implies (sparse-vectorp lc)
             (true-listp (lc-first-var-term lc)))
  :hints (("Goal" :in-theory (enable lc-first-var-term lc-termp)))
  )

; A bit constraint a*b=c can have many forms.
; One of a and b has two terms and the other has one term.
; The one that has two terms looks like either x-1 or 1-x.
; Return the var name in this case.
; Otherwise return nil.
(defun bit-1-lc-var (fp lc)
  (declare (xargs :guard (and (sparse-vectorp lc)
                              (member fp (list (fp1) (fp2))))
                  :guard-hints
                  (("Goal" :in-theory (enable sparse-vectorp
                                              iff-consp-when-true-listp
                                              true-listp-of-cdr
                                              true-listp-of-lc-first-var-term)))))
  (and (equal 2 (len lc))
       (or (and (equal (- fp 1) (lc-constant-term lc))
                (let ((var-term (lc-first-var-term lc)))
                  (and var-term
                       (equal 1 (first var-term))
                       (second var-term))))
           (and (equal 1 (lc-constant-term lc))
                (let ((var-term (lc-first-var-term lc)))
                  (and var-term
                       (equal (- fp 1) (first var-term))
                       (second var-term)))))))

; A bit constraint a*b=c can have many forms.
; One of a and b has two terms and the other has one term.
; The one that has one term should have the coefficient 1.
; Return the var name in this case.
; Otherwise return nil.
(defun bit-0-lc-var (lc)
  (declare (xargs :guard (sparse-vectorp lc)
                  :guard-hints (("Goal" :in-theory (enable sparse-vectorp
                                                           iff-consp-when-true-listp
                                                           true-listp-of-cdr
                                                           true-listp-of-lc-first-var-term)))))
  (and (equal 1 (len lc))
       (let ((var-term (lc-first-var-term lc)))
         (and var-term
              (equal 1 (first var-term))
              (second var-term)))))

; It might be that c=0 could be represented as
; a linear combination of zero terms,
; or a single cosntant term of 0*1.
; Any zero coefficients of variables should have been canonicalized out.
(defun zero-lc-p (lc)
  (declare (xargs :guard (sparse-vectorp lc)
                  :guard-hints (("Goal" :in-theory (enable sparse-vectorp
                                                           iff-consp-when-true-listp
                                                           true-listp-of-lc-first-var-term)))))
  (or (null lc)
      (and (= 1 (len lc))
           (let ((var-term (lc-first-var-term lc)))
             (and var-term
                  (equal 0 (first var-term)))))))

(defun bit-constraint-var (fp constraint)
  (declare (xargs :guard (and (member fp (list (fp1) (fp2)))
                              (r1cs-constraintp constraint))))
  ;; If constraint is a bit constraint on a single var,
  ;; this returns the name of that var.
  ;; If not, this returns NIL.
  ;; WARNING: DON'T USE 'NIL as a constraint var.
  (and (zero-lc-p (r1cs-constraint->c constraint))
       (let* ((lc-a (r1cs-constraint->a constraint))
              (lc-b (r1cs-constraint->b constraint)))
         (let ((var1 (bit-0-lc-var lc-a))
               (var2 (bit-1-lc-var fp lc-b)))
           (if (and var1 var2
                    (equal var1 var2))
               var1
               (let ((var1 (bit-1-lc-var fp lc-a))
                     (var2 (bit-0-lc-var lc-b)))
                 (if (and var1 var2
                          (equal var1 var2))
                     var1
                     nil)))))))

; In case we need a T/NIL predicate
(defun bit-constraint-p (fp constraint)
  (declare (xargs :guard (and (member fp (list (fp1) (fp2)))
                              (r1cs-constraintp constraint))))
  (not (null (bit-constraint-var fp constraint))))

; This is mostly superseded by p1cs
; but if you don't even want the bit constraints mentioned,
; you can use this.
(defun p1csn-less-bitconstraints (fp constraints)
  (declare (xargs :guard (and (member fp (list (fp1) (fp2)))
                              (r1cs-constraint-listp constraints))))
  (if (atom constraints)
      nil
      (if (bit-constraint-p fp (car constraints))
          (p1csn-less-bitconstraints fp (cdr constraints))
          (cons (p1cs1 fp (car constraints))
                (p1csn-less-bitconstraints fp (cdr constraints))))))

; Mostly superseded by bit-vars-and-non-bit-constraints,
; but if you just want the vars without the constraints,
; you can use this.
(defun vars-constrained-to-be-bits (fp constraints)
  (declare (xargs :guard (and (member fp (list (fp1) (fp2)))
                              (r1cs-constraint-listp constraints))))
  (if (endp constraints)
      nil
      (let ((var (bit-constraint-var fp (car constraints))))
        (if (null var)
            (vars-constrained-to-be-bits fp (cdr constraints))
            (cons var (vars-constrained-to-be-bits fp (cdr constraints)))))))

; Separates list of constraints into list of bit vars and list of non-bit constraints.
; Will be:
; (define bit-vars-and-non-bit-constraints ((constraints r1cs::r1cs-constraint-listp))
;   :returns (mv (bit-vars symbol-listp) (constraints r1cs::r1cs-constraint-listp))
; For now without guards or type checks.
(defun bit-vars-and-non-bit-constraints (fp constraints)
  (declare (xargs :guard (and (member fp (list (fp1) (fp2)))
                              (r1cs-constraint-listp constraints))))
  (b* (((acl2::when (endp constraints))
        (mv nil nil))
       (first-constraint (car constraints))
       (maybe-bit-var (bit-constraint-var fp first-constraint))
       ((mv rest-bit-vars rest-non-bit-constraints)
        (bit-vars-and-non-bit-constraints fp (rest constraints))))
    (if (null maybe-bit-var)
        (mv rest-bit-vars (cons first-constraint rest-non-bit-constraints))
        (mv (cons maybe-bit-var rest-bit-vars) rest-non-bit-constraints))))

; Output all the constraints to the console, in order.
(defun p1cs-all (fp constraints)
  (declare (xargs :guard (and (member fp (list (fp1) (fp2)))
                              (r1cs-constraint-listp constraints))))
  (if (atom constraints)
      nil
      (b* ((- (cw!+ "~s0~%" (p1cs1 fp (car constraints)))))
        (p1cs-all fp (cdr constraints)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Aggregating bit vars

(defconst *digits* '(#\0 #\1 #\2 #\3 #\4 #\5 #\6 #\7 #\8 #\9))

(defun position-if-digit (char-list next-pos)
  (declare (xargs :guard (and (character-listp char-list)
                              (natp next-pos))))
  (if (endp char-list)
      nil
      (if (member (car char-list) *digits*)
          next-pos
          (position-if-digit (cdr char-list) (+ next-pos 1)))))

(defthm position-if-digit-bounds
    (implies (position-if-digit char-list next-pos)
             (<= (position-if-digit char-list next-pos)
                 (+ next-pos (len char-list))))
  :rule-classes ((:linear :trigger-terms ((position-if-digit char-list next-pos)))))

(defun bit-var-base-and-num (bit-var)
  (declare (xargs :guard t))
  ;; If bit-var symbol name is of the form:  nondigit+ digits+
  ;; then return a list of the base string and the number.
  ;; Otherwise return nil.
  (if (or (null bit-var) (not (symbolp bit-var)))
      nil
      (let* ((base-name (symbol-name bit-var))
             (chars (acl2::explode base-name))
             (first-digit-pos (position-if-digit chars 0)))
        (and (natp first-digit-pos)
             (> first-digit-pos 0)
             (let ((num (str::strval (subseq base-name first-digit-pos (length base-name)))))
               (if num
                   (list (subseq base-name 0 first-digit-pos) num)
                   nil))))))

(defun bit-var-range-starting-with (starting-base-and-num last-num bit-vars)
  (declare (xargs :guard (and (true-listp starting-base-and-num)
                              (= (len starting-base-and-num) 2)
                              (stringp (first starting-base-and-num)) ;base is a string
                              (natp (second starting-base-and-num)) ;start number is natural
                              (natp last-num)
                              (true-listp bit-vars))
                  :measure (len bit-vars)))
  (b* ((base (first starting-base-and-num))
       (start-num (second starting-base-and-num))
       ((acl2::when (endp bit-vars))
        (if (= start-num last-num)
            (mv (concatenate 'string base (str::nat-to-dec-string start-num)) nil) ; back to the original var
            (mv (concatenate 'string base (str::nat-to-dec-string start-num) ".." base (str::nat-to-dec-string last-num)) nil)))
       (next-bit-var (car bit-vars))
       (next-base-and-num (bit-var-base-and-num next-bit-var))
       ((acl2::when (or (null next-base-and-num)
                        (not (equal base (first next-base-and-num)))
                        (not (equal (+ 1 last-num) (second next-base-and-num)))))
        (if (= start-num last-num)
            (mv (concatenate 'string base (str::nat-to-dec-string start-num)) bit-vars)
            (mv (concatenate 'string base (str::nat-to-dec-string start-num) ".." base (str::nat-to-dec-string last-num)) bit-vars))))
    (bit-var-range-starting-with starting-base-and-num (+ last-num 1) (cdr bit-vars))))

; TODO: move remaining code to logic mode
;(program)

;lemmas
(defthm len-of-bit-var-range-starting-with
    (<= (len (mv-nth 1 (bit-var-range-starting-with x y bit-vars)))
        (len bit-vars))
  :rule-classes :linear)

(defthm len-of-bit-var-base-and-num
    (implies (bit-var-base-and-num bit-var)
             (equal (len (bit-var-base-and-num bit-var)) 2)))

(defthm car-of-bit-var-base-and-num-is-string
    (implies (bit-var-base-and-num bit-var)
             (stringp (car (bit-var-base-and-num bit-var)))))

(defthm cadr-of-bit-var-base-and-num-is-natp
    (implies (bit-var-base-and-num bit-var)
             (natp (cadr (bit-var-base-and-num bit-var)))))

(defthm mv-nth-1-of-bit-var-range-starting-with-is-true-listp
    (implies (true-listp bit-vars)
             (true-listp (mv-nth 1 (bit-var-range-starting-with starting-base-and-num last-num bit-vars)))))

(defun bit-var-ranges (bit-vars)
  (declare (xargs :guard (true-listp bit-vars)
                  :measure (len bit-vars)
                  :hints (("Goal" :in-theory (disable
                                              bit-var-range-starting-with
                                              bit-var-base-and-num)))
                  :guard-hints (("Goal" :in-theory (disable
                                                    bit-var-range-starting-with
                                                    bit-var-base-and-num)))))
  (b* (((acl2::when (endp bit-vars)) nil)
       (base-and-num (bit-var-base-and-num (car bit-vars)))
       ((acl2::when (null base-and-num))
        ;; a singleton
        (cons (car bit-vars)
              (bit-var-ranges (cdr bit-vars))))
       ((mv range-string rest-bit-vars)
        (bit-var-range-starting-with
         base-and-num
         (second base-and-num) ; the last of the range so far
         (cdr bit-vars))))
    (cons range-string
          (bit-var-ranges rest-bit-vars))))

(defun concatenate-bit-var-ranges (ranges) ; each range is a string; can be a singleton var
  (declare (xargs :guard (string-listp ranges)))
  (cond ((null ranges) "")
        ((null (cdr ranges)) (car ranges))
        (t (concatenate 'string (car ranges) ", " (concatenate-bit-var-ranges (cdr ranges))))))

(defun bit-vars-message (bit-vars)
  (let* ((ranges (bit-var-ranges bit-vars))
         (comma-separated-ranges (concatenate-bit-var-ranges ranges)))
    (if (equal comma-separated-ranges "")
        "No bit constraints."
        (concatenate 'string "These variables have bit constraints: " comma-separated-ranges))))

; A user-interface-level function that outputs to the console.
; Mention the variables that have bit constraints;
; then output the other constraints to the console.
;
; Note, if you are using this for bn-254-group-prime, do (p1cs (fp1) ...)
; and maybe define p1cs in your own package without the fp argument.
; Similarly, if you are using this for bls12-377 scalar field prime,
; do (p1cs (fp2) ...) and maybe define p1cs in your own package without the fp arg.
(defun p1cs (fp constraints)
  (b* ((- (cw "Total of ~s0 constraints.~%" (len constraints)))
       ((mv bit-vars non-bit-constraints)
        (bit-vars-and-non-bit-constraints fp constraints))
       (- (cw!+ "~s0~%" (bit-vars-message bit-vars)))
       (- (cw "Non-bit constraints:~%")))
    (p1cs-all fp non-bit-constraints)))


;;Possible test cases

;;(include-book "top")

;; simple
;; (p1cs (fp1) (list (make-selection-constraint 'b 'x 'y 'z)))

;; 2^200
;; (p1cs (fp1) (list (r1cs-constraint
;;                            (list (list (expt 2 200) 'x))
;;                            (list (list 1 'y))
;;                            (list (list 1 'z)))))

;; (1/2)^200
;; (defun test-half-power-200-constraint ()
;;   (let* ((fp (fp1))
;;          (inv-2 (/ (+ fp 1) 2))
;;          (half-200 (mod (expt inv-2 200) fp)))
;;     (r1cs-constraint
;;       (list (list half-200 'x))
;;       (list (list 1 'y))
;;       (list (list 1 'z)))))

;; (p1cs (fp1) (list (test-half-power-200-constraint)))

;; (-2)^199
;; (defun test-neg-2-power-199-constraint ()
;;   (let* ((fp (fp1))
;;          (pos-power (mod (expt 2 199) fp))
;;          (neg-power (mod (- fp pos-power) fp)))
;;     (r1cs-constraint
;;       (list (list neg-power 'x))
;;       (list (list 1 'y))
;;       (list (list 1 'z)))))

;; (p1cs (fp1) (list (test-neg-2-power-199-constraint)))
