
(in-package "ACL2")

;; (local (include-book "defsum-thms"))
;; (include-book "defsum")
(include-book "tools/defsum" :dir :system)
(defmacro range-start (x) `(cadr ,x))
(defmacro range-end (x) `(caddr ,x))

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
  (and (symbolp x)
       (or (eq x 'bre)
           (eq x 'ere)
           (eq x 'fixed))))

(set-bogus-defun-hints-ok t)

(defsum parse-opts
;  :guard :fast
  (parse-options
   (parse-type-p type)
   (booleanp strict-paren)
   (booleanp strict-brace)
   (booleanp strict-repeat)
   (booleanp case-insensitive)))

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

