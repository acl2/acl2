; Semaphore Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (mccarthy@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Note: this code is elliptic-curve-independent.

(include-book "kestrel/crypto/r1cs/sparse/r1cs" :dir :system)
(include-book "std/strings/decimal" :dir :system) ; for str::strval

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Parse Circom JSON format files to extract R1CS.

;; NOTE: in its documentation circom expresses R1CS constraints as A*B + C = 0,
;; so C is opposite of what we are used to.
;; However, in the JSON output that is no longer true!
;; So we don't need to negate C after reading the JSON file.


(defun simple-union (syms1 syms2)
  (declare (xargs :guard (and (symbol-listp syms1)
                              (symbol-listp syms2))))
  (if (atom syms1)
      syms2
    (if (atom syms2)
        syms1
      (if (member-eq (car syms1) syms2)
          (simple-union (cdr syms1) syms2)
        (simple-union (cdr syms1) (cons (car syms1) syms2))))))

(defun cj-extract-signal-names (cj-top)
  ;; case-insensitive assoc test
  ;; returns an alist from names (strings) to signal numbers (integers)
  (third (assoc-string-equal "signalName2Idx" (second cj-top))))

(defun cj-extract-constraints (cj-top)
  ;; case-insensitive.  We could do assoc-equal for case-sensitive.
  ;; returns the constraints with all our json markers
  (third (assoc-string-equal "Constraints" (second cj-top))))

;; In case the signal name is :|one|, change it to 1.
(defun signal-name-or-1 (name)
  (declare (xargs :guard (symbolp name)))
  (if (eq name ':|one|)
      1
    name))

;; Converts list of (stringified-index-number . stringified-coefficient)
;; to list of  (integer-coefficient . var-name)
;  using the signals map, which maps indexes to symbols.
(defun cj-sv-to-r1cs-sv (sv signals acc-pairs acc-vars)
  (if (atom sv)
      (mv (reverse acc-pairs) acc-vars)
    (let* ((cj-pair (car sv))
           (index (str::strval (car cj-pair)))
           (signal-pair (assoc index signals))
           ;; we use 1 instead of ONE for the first witness variable
           (signal-name (signal-name-or-1 (cdr signal-pair))))
      (cj-sv-to-r1cs-sv (cdr sv)
                        signals
                        (cons (list (str::strval (cdr cj-pair)) signal-name)
                              acc-pairs)
                        (if (equal signal-name 1)
                            acc-vars
                          (cons signal-name acc-vars))))))

(defun cj-svs-to-r1cs-svs (svs signals acc-svs acc-vars)
  (if (atom svs)
      (mv (reverse acc-svs) acc-vars)
    (mv-let (next-sv vars)
        (cj-sv-to-r1cs-sv (car svs) signals nil nil)
      (cj-svs-to-r1cs-svs
       (cdr svs)
       signals
       (cons next-sv acc-svs)
       (simple-union vars acc-vars)))))

(defun cj-constraint-to-r1cs-constraint (cj-constraint signals)
  ;; They look like (:ARRAY ( (:OBJECT <sv>) (:OBJECT <sv>) (:OBJECT <sv>) ))
  ;; where the <sv>s are sparse vectors for A_i, B_i and C_i.
  (let* ((objects (second cj-constraint))
         (list-svs (strip-cdrs objects))
         (svs (strip-cars list-svs)))
    ;; Now each sparse vector is a list of of pairs of the form
    ;;   (stringified-index-number . stringified-coefficient)
    ;; We want to convert those to (integer-coefficient var-name).
    ;; Note, there are 3 svs for each constraint.
    (mv-let (svs vars)
        (cj-svs-to-r1cs-svs svs signals nil nil)
      (mv (r1cs::r1cs-constraint
           (first svs) (second svs) (third svs))
          vars))))

(defun raw-constraints-to-r1cs-constraints (raw-constraints
                                            signals
                                            acc-constraints
                                            acc-vars)
  ;; signals is a map from integer to symbol
  (if (atom raw-constraints)
      (mv (reverse acc-constraints)
          (reverse acc-vars))
    (mv-let (next-constraint next-constraint-vars)
        (cj-constraint-to-r1cs-constraint (car raw-constraints) signals)
      (raw-constraints-to-r1cs-constraints
       (cdr raw-constraints)
       signals
       (cons next-constraint acc-constraints)
       (simple-union next-constraint-vars acc-vars)))))

;; Converts (string-name . integer) to (integer . symbol-name).
;; Reverses the conses and interns the strings in the KEYWORD package.
;; If there is more than one string-name that maps to a given integer,
;; the first one is used.
;; Possible future enhancement: consider also returning a synonym map.
(defun invert-cj-signal-strings (remaining-signal-names-to-numbers acc)
  (if (atom remaining-signal-names-to-numbers)
      (reverse acc)
    (let ((cj-pair (car remaining-signal-names-to-numbers)))
      (if (assoc (cdr cj-pair) acc)
          ;; this variable is already in ACC
          ;; At this point we could record it as a synonym and accumulate synonym map as well.
          (invert-cj-signal-strings
           (cdr remaining-signal-names-to-numbers)
           acc)
        (invert-cj-signal-strings
         (cdr remaining-signal-names-to-numbers)
         (cons (cons (cdr cj-pair) (intern (car cj-pair) "KEYWORD")) acc))))))

;; returns (mv <constraint-list> <var-list>)
(defun cj-to-r1cs (cj-top)
  (let ((raw-constraints (cj-extract-constraints cj-top))
        (signal-names-to-numbers (cj-extract-signal-names cj-top)))
    (let ((signal-numbers-to-symbols (invert-cj-signal-strings
                                      signal-names-to-numbers
                                      nil)))
      ;; Note that signal-numbers-to-symbols can include numbers that do not appear
      ;; in the constraints, but in the json in "signals" and maybe elsewhere.
      ;; The vars we return are not these, but the ones that actually appear
      ;; in the constraints.
      (raw-constraints-to-r1cs-constraints
       raw-constraints signal-numbers-to-symbols nil nil))))

;; Note: We no longer need to fix up result by removing :|one|
;; since we filter it out before it gets into the vars.
;; Previously:
;;    ;; :|one| is a special "variable" that means 1 and that we represent as the numeral 1.
;;    (mv constraints
;;        (remove1 ':|one| vars))))))
