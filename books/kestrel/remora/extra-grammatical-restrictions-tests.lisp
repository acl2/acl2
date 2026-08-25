; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "extra-grammatical-restrictions")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Examples of the extra-grammatical restrictions.

; This book exemplifies the extra-grammatical restrictions on CSTs.
; Currently it exemplifies CST-LONGEST-KEYWORDS-P,
; in the violation direction:
; we build CSTs with abutted keywords,
; and prove that the restriction rejects them,
; by exhibiting the adjacent paths and the extension witnesses;
; everything else is proved by evaluation.

; Proving that specific legal CSTs satisfy the restrictions is future work:
; since the restrictions are universally quantified
; and their extensibility tests are existentially quantified,
; those proofs require grammar-level reasoning
; (e.g. that no identifier fringe contains a space),
; not just evaluation.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Helpers to build CSTs concretely.

(define char-rule-cst ((rulename stringp) (code natp))
  :returns (cst abnf::treep)
  :short "CST for a rule matched by a single character,
          e.g. @('id-start') or @('unicode-space')."
  (abnf::tree-nonleaf (abnf::rulename rulename)
                      (list (list (abnf::tree-leafterm (list code))))))

(define id-continue-csts ((codes nat-listp))
  :returns (csts abnf::tree-listp)
  :short "List of @('id-continue') CSTs for a list of characters."
  (cond ((endp codes) nil)
        (t (cons (char-rule-cst "id-continue" (car codes))
                 (id-continue-csts (cdr codes))))))

(define identifier-cst ((codes nat-listp))
  :guard (consp codes)
  :returns (cst abnf::treep)
  :short "CST for an identifier with the given (non-empty) characters."
  (abnf::tree-nonleaf (abnf::rulename "identifier")
                      (list (list (char-rule-cst "id-start" (car codes)))
                            (id-continue-csts (cdr codes)))))

(defrule identifier-cst-example
  (cst-matchp (identifier-cst (string=>nats "t-app$")) "identifier"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Example 1: a 'tapp-exp' whose keyword is abutted by an identifier.
; The extension that makes the keyword non-maximal comes from
; the rest of the construct's own fringe.

(defval *ws-cst-empty*
  :short "CST for empty whitespace."
  (abnf::tree-nonleaf (abnf::rulename "ws") (list nil)))

(defval *ws-cst-space*
  :short "CST for whitespace consisting of one space."
  (abnf::tree-nonleaf
   (abnf::rulename "ws")
   (list (list (abnf::tree-nonleaf
                nil
                (list (list (char-rule-cst "unicode-space" 32))))))))

(defval *type-cst-&y*
  :short "CST for the type @('&y')."
  (abnf::tree-nonleaf
   (abnf::rulename "type")
   (list (list (abnf::tree-nonleaf
                (abnf::rulename "type-var")
                (list (list (abnf::tree-nonleaf
                             (abnf::rulename "atom-type-var")
                             (list (list (abnf::tree-leafterm (list 38)))
                                   (list (identifier-cst
                                          (list 121))))))))))))

(defval *tapp-exp-cst-abutted*
  :short "A grammatical @('tapp-exp') CST with fringe @('t-app$x &y'),
          whose keyword @('t-app') is abutted by the identifier @('$x')."
  (abnf::tree-nonleaf
   (abnf::rulename "tapp-exp")
   (list (list (abnf::tree-leafterm (string=>nats "t-app")))
         (list *ws-cst-empty*)
         (list (abnf::tree-nonleaf
                (abnf::rulename "exp")
                (list (list (identifier-cst (string=>nats "$x"))))))
         (list (abnf::tree-nonleaf
                nil
                (list (list *ws-cst-space*)
                      (list *type-cst-&y*)))))))

(defrule tapp-exp-cst-abutted-is-grammatical
  (cst-matchp *tapp-exp-cst-abutted* "tapp-exp"))

(defval *tapp-exp-cst-abutted-in-context*
  :short "The abutted @('tapp-exp') CST above,
          followed by a closing parenthesis
          (standing for the rest of an enclosing context)."
  (abnf::tree-nonleaf nil
                      (list (list *tapp-exp-cst-abutted*)
                            (list (abnf::tree-leafterm (list 41))))))

(defrule cst-longest-keywords-p-counterexample-tapp
  (not (cst-longest-keywords-p *tapp-exp-cst-abutted-in-context*))
  :use ((:instance cst-longest-keywords-p-necc
                   (cst *tapp-exp-cst-abutted-in-context*)
                   (path1 (list (abnf::make-tree-path-step :conc 0 :rep 0)))
                   (path2 (list (abnf::make-tree-path-step :conc 1 :rep 0))))
        (:instance extensible-to-cst-fringe-p-suff
                   (current (string=>nats "t-app"))
                   (rest (string=>nats "$x &y)"))
                   (rulenames (list "identifier"))
                   (cst (identifier-cst (string=>nats "t-app$")))
                   (ext (list 36)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Example 2: a base-type followed adjacently by a digit,
; as in a bracket type [Int3].
; Here the extension that makes the keyword non-maximal comes from
; the adjacent fringe,
; since the keyword is the whole fringe of the base-type CST.

(defval *base-type-cst-int*
  :short "CST for the base type @('Int')."
  (abnf::tree-nonleaf (abnf::rulename "base-type")
                      (list (list (abnf::tree-leafterm
                                   (string=>nats "Int"))))))

(defrule base-type-cst-int-is-grammatical
  (cst-matchp *base-type-cst-int* "base-type"))

(defval *base-type-cst-int-before-digit*
  :short "The @('Int') CST above, followed by the digit @('3'),
          as in a bracket type @('[Int3]')."
  (abnf::tree-nonleaf nil
                      (list (list *base-type-cst-int*)
                            (list (abnf::tree-leafterm (list 51))))))

(defrule cst-longest-keywords-p-counterexample-base-type
  (not (cst-longest-keywords-p *base-type-cst-int-before-digit*))
  :use ((:instance cst-longest-keywords-p-necc
                   (cst *base-type-cst-int-before-digit*)
                   (path1 (list (abnf::make-tree-path-step :conc 0 :rep 0)))
                   (path2 (list (abnf::make-tree-path-step :conc 1 :rep 0))))
        (:instance extensible-to-cst-fringe-p-suff
                   (current (string=>nats "Int"))
                   (rest (string=>nats "3"))
                   (rulenames (list "identifier"))
                   (cst (identifier-cst (string=>nats "Int3")))
                   (ext (list 51)))))
