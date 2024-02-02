(in-package "ACL2S")
;; This file should be loaded in ACL2s before running the proof checker.

;; Any include-books that are needed
(include-book "acl2s/interface/acl2s-utils/top" :dir :system)
(include-book "kestrel/utilities/system/world-queries" :dir :system)
(include-book "tools/theory-tools" :dir :system)
(include-book "induction-proof-checker")
(include-book "arith-theory")

; Matt K. mod: Avoid ACL2(p) error.
(acl2::set-waterfall-parallelism nil)

;; Put functions that you want to define in ACL2s here

(defunc all-varp (xs)
  :input-contract (true-listp xs)
  :output-contract (booleanp (all-varp xs))
  (if (endp xs)
      t
    (and (varp (car xs))
         (all-varp (cdr xs)))))

;; Determine if the given value represents a contract rule
(definec is-contract-rule (r :all) :boolean
  (and (consp r)
       (consp (cdr r))
       (symbolp (second r))
       (or (str::strsuffixp "-CONTRACT" (str::upcase-string (string (second r))))
           (str::strsuffixp "-CONTRACT-TP" (str::upcase-string (string (second r)))))))

;; Remove any non-contract-rules from the given list
(definec contract-theorems (l :tl) :tl
  (cond ((endp l) nil)
        ((is-contract-rule (car l)) (cons (car l) (contract-theorems (cdr l))))
        (t (contract-theorems (cdr l)))))

(deftheory min-theory
  '(acl2::minimal-theory
    (:executable-counterpart acl2::tau-system)
    ;; Both of the following rules are often useful for reasoning
    ;; about prop logic
    (:compound-recognizer booleanp-compound-recognizer)
    (:definition not)))

;; TODO keep up to date with redefine-theories in acl2s-high-level-interface.lisp
(deftheory type-prescription-theory
  (acl2::rules-of-type :type-prescription (current-theory :here)))

;; TODO keep up to date with redefine-theories in acl2s-high-level-interface.lisp
(deftheory contract-theory
  (union-theories (theory 'min-theory)
                  (union-theories (contract-theorems (current-theory :here))
                                  (theory 'type-prescription-theory))))

;; TODO keep up to date with redefine-theories in acl2s-high-level-interface.lisp
(deftheory executable-theory
  (union-theories '((:executable-counterpart acl2::tau-system))
                  (acl2::rules-of-type :executable-counterpart (current-theory :here))))

;; TODO keep up to date with redefine-theories in acl2s-high-level-interface.lisp
(deftheory min-executable-theory
  '(min-theory executable-theory))

(deftheory arith-theory
  '(acl2::Associativity-of-+
    acl2::Commutativity-of-+
    acl2::Unicity-of-0
    acl2::Inverse-of-+
    acl2::Associativity-of-*
    acl2::Commutativity-of-*
    acl2::Unicity-of-1
    acl2::Inverse-of-*
    acl2::Distributivity
    acl2::Rational-implies2))

(defun valid-acl2s-termp (term state)
  (declare (xargs :mode :program :stobjs state))
  ;; nil below means that we don't want to ensure safe mode when
  ;; translating.
  (b* (((er tterm) (acl2::translate term t nil t 'ctx (w state) state)))
    (mv nil (termp tterm (w state)) state)))

(acl2s-defaults :set cgen-timeout 10)
