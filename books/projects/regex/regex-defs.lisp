; Copyright (C) 2004, Regents of the University of Texas
; Written by Sol Swords
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")
(include-book "xdoc/top" :dir :system)
;; (local (include-book "defsum-thms"))
;; (include-book "defsum")
(include-book "tools/defsum" :dir :system)
(defmacro range-start (x) `(cadr ,x))
(defmacro range-end (x) `(caddr ,x))

#||
;; Depend on arithmetic since defsum uses it.
(include-book "arithmetic/top-with-meta" :dir :system)
||#

;; Checks whether x is a valid element to include in a charset.
;; either a character or ('range char char).

(defun charset-memberp (x)
  (declare (xargs :guard t))
  (cond
   ((characterp  x) t)
   (t (and (consp x)
           (consp (cdr x))
           (consp (cddr x))
           (equal (car x) 'range)
           (characterp (range-start x))
           (characterp (range-end x))))))

;; Is x composed of valid charset-members
;; A little bit less restrictive than we'll use because
;; it allows "not" to occur anywhere; a real parsed regex
;; will only have "not" occurring first
(defun charsetp (x)
  (declare (xargs :guard t))
  (if (atom x)
      (equal x nil)
    (and (or (equal (car x) 'not)
             (charset-memberp (car x)))
         (charsetp (cdr x)))))





(defsum regex
;  :guard :fast
  (r-disjunct (regex-p left) (regex-p right))
  (r-concat (regex-p left) (regex-p right))
  (r-exact (characterp val))
  (r-charset (charsetp set))
  (r-any)
  (r-empty)
  (r-nomatch)
  (r-end)
  (r-begin)
  (r-repeat (regex-p regex) (integerp min) (integerp max))
  (r-group (regex-p regex) (natp index))
  (r-backref (natp index)))

;;(in-theory (enable regex-executable-counterparts))

;; (defmacro regex-match (input &rest clauses)
;;   (make-pattern-match input clauses
;;                       (append *regex-types-pattern-match-alist*
;;                               *basic-constructor-alist*)))

(defun parse-type-p (x)
  (declare (xargs :guard t))
  (and (symbolp x)        ;; GNU regular expressions -- see GNU documentation
       (or (eq x 'bre)    ;; Basic regular expressions
           (eq x 'ere)    ;; Extended regular expressions
           (eq x 'fixed)  ;; Fixed (no character is special) string
           )))

(set-bogus-defun-hints-ok t)  ;; For non-recursive function ignore the (ACL2) hints.

(defsection parse-options
  :parents (regex)
  :short "Generate options for using regular expressions to parse/match
          strings"
  :long "<p>General form:</p>

@({
 (parse-options parse-type
                strict-paren
                strict-brace
                strict-repeat
                case-insensitive)
})

<p><tt>Parse-type</tt> should be one of <tt>'ere</tt>, <tt>'bre</tt>, or
<tt>'fixed</tt>.  Basic regular expressions (BRE's) do not support many of the
features of traditional regular expressions (e.g., parentheses), so you may
wish to consider using extended regular expressions (ERE's).  Fixed indicates
that the pattern should be interpreted as a list of fixed strings, separated by
newlines, any of which is to be matched.</p>

<p><tt>Strict-paren</tt>, <tt>strict-brace</tt>, and <tt>strict-repeat</tt>,
and <tt>case-insensitive</tt> are @('booleanp') values.</p>

<p>BOZO: document strict-paren, strict-brace, and strict-repeat.</p>"

(defsum parse-opts
;  :guard :fast
  (parse-options
   (parse-type-p type)
   (booleanp strict-paren)
   (booleanp strict-brace)
   (booleanp strict-repeat)
   (booleanp case-insensitive))))

; Makes parsing options (parse-opts) structure.

(defmacro make-parse-opts
  (&key (type 'ere)
        strict-paren
        strict-brace
        strict-repeat
        case-insensitive
        )
  `(parse-options ',type
                  ',strict-paren
                  ',strict-brace
                  ',strict-repeat
                  ',case-insensitive))


(defthm parse-opts-type-possibilities
  (implies (and (parse-opts-p x)
                (not (equal (parse-options-type x) 'bre))
                (not (equal (parse-options-type x) 'ere)))
           (equal (parse-options-type x) 'fixed))
  :hints (("Goal" :cases ((parse-options-p x)))
          ("Subgoal 1" :in-theory (disable parse-opts-possibilities))))

(defthm parse-options-parse-opts
  (implies (parse-opts-p x)
           (parse-options-p x)))



;;(in-theory (enable parse-options-executable-counterparts))

;; (defthm len-cdr (<= (len (cdr x)) (len x))
;;   :rule-classes
;;   (:rewrite
;;    (:forward-chaining :trigger-terms ((len (cdr x))))))

