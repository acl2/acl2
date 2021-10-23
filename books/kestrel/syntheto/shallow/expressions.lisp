; Syntheto Library
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (mccarthy@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Macros for building expressions.

;; See the UML diagram:
;; https://git.isis.vanderbilt.edu/midas/acl2.xtext/-/blob/devel/abstract-syntax/expressions-uml.png

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "SYNTHETO")

(include-book "type-constructors")

;(include-book "projects/apply/top" :dir :system)
(include-book "std/util/defines" :dir :system)
(include-book "kestrel/alists-light/lookup-eq" :dir :system)
(include-book "std/testing/assert-equal" :dir :system)
(include-book "last1")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Tables of nullary, unary and binary function mappings
(defconst *nullary-fn-alist*
  '((s-literal-true . T)
    (s-literal-false . NIL)
    (s-literal-empty-seq . ())))

(defconst *unary-fn-alist*
  '((s-not . not)
    (s-negate . -)
    ;; names not yet decided
    (s-empty-p . endp)
    (s-head . car)
    (s-last . acl2::last1)
    (s-tail . cdr)
    (s-length . len)
    (s-string-length . length)))

(defconst *binary-fn-alist*
  '((s-equal . equal)
    (s-lt . <)
    (s-gt . >)
    (s-gte . >=)
    (s-lte . <=)
    (s-and . and)
    (s-or . or)
    (s-implies . implies)
    (s-plus . +)
    (s-minus . -)
    (s-times . *)
    (s-div . acl2::truncate)
    (s-rem . acl2::rem)
    (s-cons . cons)
    (cons . cons)
    (s-insert . set::insert)
    (append . append)

    (s-member . member-equal)
    (s-remove-first . remove1-equal)))

(defmacro check-syntheto-args (n)
  `(if (= num-args ,n)
       nil
     (raise "Expected ~x0 args in syntheto term:~%~x1" ,n tm)))

(defmacro check-stringp (s fm)
  `(if (stringp ,s)
       ,fm
     (prog2$ (raise "~x0 not a string in syntheto term:~%~x1" ,s tm)
             t)))

(defmacro check-stringps (strings fm)
  (if (null strings)
      fm
    `(if (stringp ,(car strings))
         (check-stringps ,(cdr strings) ,fm)
       (prog2$ (raise "~x0 not a string in syntheto term:~%~x1" ,(car strings) tm)
               t))))

(defines translate-term-fns
  (define translate-term (tm)           ; syntheto-term-p ?
    ;; :returns (r-val (or (true-listp r-val)
    ;;                     (integerp r-val)
    ;;                     (stringp r-val)
    ;;                     (symbolp r-val)))
    (if (or (integerp tm) ; Let's stick with the regex [0-9]+ for literal integers in base 10.
            (stringp tm)) ; Let's stick with double quotes around literal strings.
        tm
      (b* (((when (atom tm))
            (raise "Bad atom ~x0 in syntheto term." tm)
            t)
           (`(,f . ,args) tm)
           ((unless (true-listp args))
            (raise "Illegal syntheto term:~%~x0" tm)
            nil)
           (num-args (len args))
           ((when (or (eq f 's-var-ref)
                      (eq f 's-varref))) ; allow both for now?
            (check-syntheto-args 1)
            (check-stringp (second tm)
                           (let ((varsymbol (intern-syndef (second tm))))
                             `,varsymbol)))
           ((when (eq f 's-literal-char))
            (check-syntheto-args 1)
            (let ((code-or-string (first args)))
              (cond ((and (natp code-or-string) (< code-or-string 256))
                     (code-char code-or-string))
                    ((and (stringp code-or-string) (= 1 (length code-or-string)))
                     (char code-or-string 0)))))
           ((when (eq f 's-notequal))
            (check-syntheto-args 2)
            `(not (equal ,(translate-term (first args))
                         ,(translate-term (second args)))))
           ((when (eq f 's-conditional))
            (check-syntheto-args 3)
            `(if ,(translate-term (first args))
                 ,(translate-term (second args))
               ,(translate-term (third args))))
           ((when (eq f 's-call))
            (check-stringp (first args)
                           (let ((fnsymbol (intern-syndef (first args)))
                                 (trans-args (translate-terms (cdr args))))
                             `(,fnsymbol ,@trans-args))))
           ((when (eq f 's-let))
            (check-syntheto-args 2)
            (let ((let-bindings (translate-let-bindings (first args))))
              `(let ,let-bindings
                 ,(translate-term (second args)))))

           ;; Product ops
           ((when (eq f 's-prod-make))
            (if (> num-args 0) nil
              (raise "Expected non-empty args in syntheto term:~%~x0" tm))
            (check-stringp (first args)
                           (let ((prodname (first args))
                                 (keyword-val-pairs (keyword-translated-val-pairs (cdr args) tm)))
                             `(,(intern-syndef (concatenate 'string "MAKE-" prodname))
                               ,@keyword-val-pairs))))
           ((when (eq f 's-prod-field-get))
            (check-syntheto-args 3)
            (case-match args
              ((prodname fieldname instance)
               (check-stringps (prodname fieldname)
                               `(,(intern-syndef (concatenate 'string prodname "->" fieldname))
                                 ,(translate-term instance))))))

           ;; Sum ops
           ((when (eq f 's-sum-construct))
            (if (< num-args 2)
                (raise "Expected at least 2 args in syntheto term:~%~x0" tm)
              nil)
            (let ((sum-name (first args))
                  (alt-name (second args)))
              (check-stringps (sum-name alt-name)
                              `(,(intern-syndef (concatenate 'string sum-name "-" alt-name))
                                ,@(translate-terms (cddr args))))))
           ((when (eq f 's-sum-field))
            (check-syntheto-args 4)
            (let ((sum-name (first args))
                  (alt-name (second args))
                  (fld-name (third args)))
              (check-stringps (sum-name alt-name fld-name)
                              `(,(intern-syndef (concatenate 'string sum-name "-" alt-name "->" fld-name))
                                ,@(translate-term (fourth args))))))
           ;; ((when (eq f 's-sum-update)) ; NYI
           ;;  (if (> num-args 1) nil
           ;;    (raise "Expected at least 2 args in syntheto term:~%~x0" tm))
           ;;  (let ((sum-name (first args))
           ;;        (alt-name (second args))
           ;;        (fld-name (third args)))
           ;;    `(,(intern-syndef (concatenate 'string sum-name "-" alt-name))
           ;;      ,@(translate-terms (fourth args)))))
           ((when (eq f 's-sum-test))
            (check-syntheto-args 3)
            (let ((sum-name (first args))
                  (alt-name (second args)))
              (check-stringps (sum-name alt-name)
                              `(equal ',(intern alt-name "KEYWORD")
                                      (,(intern-syndef (concatenate 'string sum-name "-kind"))
                                       ,(translate-term (third args)))))))

           ;; Sequence Ops
           ((when (eq f 's-literal-sequence))
            `(list ,@(translate-terms args)))

           ;; Option ops; polymorphic or monomorphic?!
           ((when (eq f 's-none))
            (if (> num-args 1)
                (raise "Too many args in syntheto term (~x0):~%~x1" num-args tm)
              nil)
            (if (equal num-args 0)
                'nil
             `(,(intern-syndef (concatenate 'string (s-type-to-fty-name-string (first args))
                                            "-NONE")))))
           ((when (eq f 's-some))
            (if (> num-args 2)
                (raise "Too many args in syntheto term (~x0):~%~x1" num-args tm)
              nil)
            (if (equal num-args 1)
                (translate-term (first args))
              `(,(intern-syndef (concatenate 'string (s-type-to-fty-name-string (first args))
                                             "-SOME"))
                ,(translate-term (second args)))))

           (nullary-fn-trans-pr (assoc-eq f *nullary-fn-alist*))
           ((when nullary-fn-trans-pr)
            (check-syntheto-args 0)
            (cdr nullary-fn-trans-pr))

           (unary-fn-trans (acl2::lookup-eq f *unary-fn-alist*))
           ((when unary-fn-trans)
            (check-syntheto-args 1)
            (let ((t-fm `(,unary-fn-trans ,(translate-term (first args)))))
              (or (case-match t-fm
                    (('not ('endp c-tm))
                     `(consp ,c-tm)))
                  t-fm)))

           (binary-fn-trans (acl2::lookup-eq f *binary-fn-alist*))
           ((when binary-fn-trans)
            (check-syntheto-args 2)
            (let ((t1 (translate-term (first args)))
                  (t2 (translate-term (second args))))
              (if (and (eq binary-fn-trans 'and)
                       (eq t1 't))
                  t2
                  (if (and (eq binary-fn-trans 'and)
                           (eq t2 't))
                      t1
                    `(,binary-fn-trans ,t1 ,t2))))))
        (prog2$ (raise "Unrecognized syntheto term:~%~x0" tm)
                t))))

  (define translate-terms (tms)
    (if (null tms)
        ()
      (if (consp tms)
          (cons (translate-term (car tms))
                (translate-terms (cdr tms)))
        (prog2$ (raise "Illegal list of syntheto terms:~%~x0" tms)
                nil))))

  (define translate-let-bindings (prs)
    (if (null prs)
        ()
      (if (and (consp prs)
               (consp (car prs))
               (consp (cdar prs))
               (stringp (first (car prs))))
          (cons (list (intern-syndef (first (car prs)))
                      (translate-term (second (car prs))))
                (translate-let-bindings (cdr prs)))
        (prog2$ (raise "Illegal let bindings:~%~x0" prs)
                  nil))))

  (define keyword-translated-val-pairs (args tm)
    (if (null args)
        ()
      (if (or (not (consp args))
              (not (consp (cdr args)))
              (not (stringp (first args))))
          (prog2$ (raise "Illegal syntheto product constructor term:~%~x0" tm)
                  nil)
        (list* (intern (first args) "KEYWORD")
               (translate-term (second args))
               (keyword-translated-val-pairs (cddr args) tm)))))
    :verify-guards nil
    ///
    (verify-guards translate-term)
  ) ; translate-term-fns


(defmacro e-term (s-tm)
  (translate-term s-tm))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Tests

(acl2::assert-equal (translate-term '(s-notequal (s-literal-true) (s-literal-false)))
                    '(not (equal T NIL)))

;; For now, operators on characters are supposed to be
;; equal, notequal, gt, gte, lt, lte

;; These inequalities don't yet work on characters.
;; The translation of s-lt will have to do a type check at runtime to
;; make that happen.  Something like
;; (if (characterp ..) (char-lessp ..)
;;   (if (integerp ..) (< ..) ..

(acl2::assert-equal (translate-term '(s-notequal (s-literal-char "a") (s-literal-char "A")))
                    '(not (equal #\a #\A)))
(acl2::assert-equal (translate-term '(s-equal (s-literal-char "a") (s-literal-char 97)))
                    '(equal #\a #\a))

(acl2::assert-equal (translate-term '(s-and (s-and (s-not (s-gt 2 2)) (s-gt 3 2))
                                            (s-and (s-gte 2 2) (s-gte 3 2))))
              '(and (and (not (> 2 2)) (> 3 2))
                    (and (>= 2 2) (>= 3 2))))

(acl2::assert-equal (translate-term '(s-and (s-and (s-not (s-lt 2 2)) (s-lt 2 3))
                                            (s-and (s-lte 2 2) (s-lte 2 3))))
              '(and (and (not (< 2 2)) (< 2 3))
                    (and (<= 2 2) (<= 2 3))))

;; bignums: 2^257 + 2^257 = 2^258
(acl2::assert-equal
 (translate-term '(s-equal
                   (s-plus
                    231584178474632390847141970017375815706539969331281128078915168015826259279872
                    (s-minus
                     (s-negate
                      (s-minus
                       (s-negate
                        231584178474632390847141970017375815706539969331281128078915168015826259279872)
                       1))
                     1))
                   463168356949264781694283940034751631413079938662562256157830336031652518559744))
 '(equal (+ 231584178474632390847141970017375815706539969331281128078915168015826259279872
            (- (- (- (- 231584178474632390847141970017375815706539969331281128078915168015826259279872)
                     1))
               1))
         463168356949264781694283940034751631413079938662562256157830336031652518559744))

(acl2::assert-equal (translate-term '(s-and (s-equal (s-div 7 2) 3)
                                            (s-equal (s-div -7 2) -3)))
                    '(and (equal (acl2::truncate 7 2) 3)
                          (equal (acl2::truncate -7 2) -3)))

(acl2::assert-equal (translate-term '(s-and (s-equal (s-rem 7 2) 1)
                                            (s-equal (s-rem -7 2) -1)))
                    '(and (equal (acl2::rem 7 2) 1)
                          (equal (acl2::rem -7 2) -1)))

(acl2::assert-equal (translate-term '(s-equal (s-conditional (s-equal (s-literal-char "a") (s-literal-char 97))
                                                             22
                                                             "abc")
                                              22))
                    '(equal (if (equal #\a #\a)
                                22
                              "abc")
                            22))

(acl2::assert-equal (translate-term '(s-equal (s-conditional (s-equal (s-literal-char "a") (s-literal-char 98))
                                                             22
                                                             "abc")
                                              "abc"))
                    '(equal (if (equal #\a #\b)
                                22
                              "abc")
                            "abc"))

(acl2::assert-equal (translate-term '(s-equal (s-call "DECDEC" (s-plus 2 5)) 5))
                    '(equal (syndef::decdec (+ 2 5)) 5))

(acl2::assert-equal (translate-term '(s-equal 22 (s-let (("X" 12) ("Y" 10)) (s-plus (s-var-ref "X") (s-var-ref "Y")))))
                    '(equal 22 (let ((syndef::x 12) (syndef::y 10)) (+ syndef::x syndef::y))))

(acl2::assert-equal (translate-term '(s-equal 24 (s-let (("X" 12) ("Y" 10))
                                                        (s-let (("X" (s-plus (s-var-ref "X") (s-var-ref "Y")))
                                                                ("Y" (s-minus (s-var-ref "X") (s-var-ref "Y"))))
                                                               (s-plus (s-var-ref "X") (s-var-ref "Y"))))))
                    '(equal 24 (let ((syndef::x 12) (syndef::y 10))
                                 (let ((syndef::x (+ syndef::x syndef::y))
                                       (syndef::y (- syndef::x syndef::y)))
                                   (+ syndef::x syndef::y)))))

;; Test product ops.
;; (make-product-type "acid4"
;;                    ("id" (s-type-integer)))
;; make-product-type not yet defined! Use expansion.

;; (acl2::assert-equal (translate-term '(s-equal 3 (s-let (("ai" (s-prod-make "acid4" "id" 3)))
;;                                                        (s-prod-field-get "acid4" "id" (s-var-ref "ai")))))
;;                     '(equal 3 (let ((syndef::|ai| (syndef::|MAKE-acid4| :|id| 3)))
;;                                 (syndef::|acid4->id| syndef::|ai|))))
