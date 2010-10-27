; Matt Kaufmann
; October, 2010

; This book introduces a macro, DEFRULE.  DEFRULE behaves just like defthm,
; except that its intended use is to generate rewrite rules from formulas that
; may involve calls of IF, or of macros like COND, CASE, AND, and OR whose
; expansions introduce IF expressions.

; Note to those who are learning to use MAKE-EVENT to create events by
; expanding macro calls:

; Notice the call below of TRANSLATE.  While TRANSLATE is a "system-level"
; function (used in the ACL2 implementation) which therefore doesn't have a
; documentation topic, one can find it in the ACL2 source code with documention
; in the form of comments.  We figured out how to call TRANSLATE below by
; looking up the definition of DEFTHM in the ACL2 sources, which led to
; DEFTHM-FN and then DEFTHM-FN1, which contained a call of TRANSLATE that was
; easily adapted for the present purpose.

(in-package "ACL2")

(local ; just a lemma needed for guard verification below
 (defthm true-listp-revappend
   (equal (true-listp (revappend x y))
          (true-listp y))))

(defun parse-if-as-implies1 (x hyps)
  (declare (xargs :guard (true-listp hyps)))
  (case-match x
    (('if test tbr ''t) ; Note that 't is the translated form of t.
     (parse-if-as-implies1 tbr (cons test hyps)))
    (&
     (cond ((cdr hyps) `(implies (and ,@(reverse hyps)) ,x))
           (hyps `(implies ,(car hyps) ,x))
           (t x)))))

(defun parse-if-as-implies (x)
  (declare (xargs :guard t))
  (parse-if-as-implies1 x nil))

(defmacro defrule (name form &rest rest)

; Use this exactly like defthm, but the top-level translated IF structure is
; replaced by IMPLIES calls in order to generate a suitable form for a rewrite
; rule.

  `(make-event
    (er-let*
        ((tform ; mimic the call in source function defthm-fn1
          (translate ',form t t t '(defrule . ,name) (w state) state)))
      (value (list* 'defthm ',name
                    (untranslate (parse-if-as-implies tform) t
                                 (w state))
                    ',rest)))))
