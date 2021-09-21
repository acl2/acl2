; A utility to combine IFs
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/utilities/forms" :dir :system)
(include-book "std/util/bstar" :dir :system)
(include-book "tools/flag" :dir :system)
(include-book "kestrel/utilities/negate-term" :dir :system)
;(include-book "count-ifs-in-term")
;(include-book "count-ifs-in-then-and-else-branches")
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/utilities/acl2-count" :dir :system))

;rename file

(in-theory (disable mv-nth))



;; Returns (mv changep new-term) where if CHANGEP is then NEW-TERM is the new term.
;; If CHANGEP is nil, then NEW-TERM is irrelevant,
(defund combine-if-from-then-part (test then-part else-part)
  (declare (xargs :guard (and (pseudo-termp test)
                              (pseudo-termp then-part)
                              (pseudo-termp else-part))))
  (if (call-of 'if then-part) ;; (if <test> (if <test2> .. ..) ..)
      (if (equal (farg2 then-part) else-part)
          (mv t `(if (if ,test ; an and
                         ,(negate-term (farg1 then-part))
                       'nil)
                     ,(farg3 then-part)
                   ,else-part))
        (if (and (equal (farg3 then-part) else-part) ;; (if <test> (if <test2> .. else-part) else-part)
                 (not (equal *nil* else-part)) ; avoids changing (IF X (IF Y Z 'NIL) 'NIL), which is (and x y z)
                 )
            (mv t `(if (if ,test ; an and
                           ,(farg1 then-part)
                         'nil)
                       ,(farg2 then-part)
                     ,else-part))
          (mv nil nil)))
    (mv nil nil)))

(defthm pseudo-termp-of-mv-nth-1-of-combine-if-from-then-part
  (implies (and (pseudo-termp test)
                (pseudo-termp then-part)
                (pseudo-termp else-part))
           (pseudo-termp (mv-nth 1 (combine-if-from-then-part test then-part else-part))))
  :hints (("Goal" :in-theory (enable combine-if-from-then-part))))

;; Returns (mv changep new-term) where if CHANGEP is then NEW-TERM is the new term.
;; If CHANGEP is nil, then NEW-TERM is irrelevant,
(defund combine-if-from-else-part (test then-part else-part)
  (declare (xargs :guard (and (pseudo-termp test)
                              (pseudo-termp then-part)
                              (pseudo-termp else-part))))
  (if (call-of 'if else-part) ;; (if <test> .. (if <test2> .. ..))
      (if (equal (farg2 else-part) then-part) ;; (if <test> then-part (if <test2> then-part ..))
          (mv t `(if (if ,test ; an or
                         ,test
                         ,(farg1 else-part))
                     ,then-part
                   ,(farg3 else-part)))
        (if (equal (farg3 else-part) then-part) ;; (if <test> then-part (if <test2> .. then-part))
            (mv t `(if (if ,test ; an or
                           ,test
                         ,(negate-term (farg1 else-part)))
                       ,then-part
                     ,(farg2 else-part)))
          (mv nil nil)))
    (mv nil nil)))

(defthm pseudo-termp-of-mv-nth-1-of-combine-if-from-else-part
  (implies (and (pseudo-termp test)
                (pseudo-termp then-part)
                (pseudo-termp else-part))
           (pseudo-termp (mv-nth 1 (combine-if-from-else-part test then-part else-part))))
  :hints (("Goal" :in-theory (enable combine-if-from-else-part))))

(local (in-theory (disable acl2-count)))

;; TODO Get rid of count in favor of a real measure
(mutual-recursion
 (defund combine-ifs-in-then-and-else-branches (term count)
   (declare (xargs :guard (pseudo-termp term)
                   :hints (("Goal" ;; :cases ( ;(EQUAL 'if (CAR TERM))
                                   ;;         )
                            :in-theory (enable ;COMBINE-IF-FROM-THEN-PART
                                        ;;COMBINE-IF-FROM-else-PART
                                        )))
                   :measure ;; (make-ord 2 (+ 1 (count-ifs-in-term term))
                   ;;           (make-ord 1 (+ 1 (count-ifs-in-then-and-else-branches term))
                   ;;                     (acl2-count term)))
                   (nfix (+ 1 count))
                   :verify-guards nil ; done below
                   ))
   (if (zp count)
       term
     (if (variablep term)
         term
       (let ((fn (ffn-symb term)))
         (if (eq 'quote fn)
             term
           (if (and (eq 'if fn)
                    (= 3 (len (fargs term))))
               (b* ((test (combine-ifs-in-then-and-else-branches (farg1 term) (+ -1 count)) ; should we recur here, or not?
                          )
                    (then-part (combine-ifs-in-then-and-else-branches (farg2 term) (+ -1 count)))
                    (else-part (combine-ifs-in-then-and-else-branches (farg3 term) (+ -1 count)))
                    ((mv changep term)
                     (combine-if-from-then-part test then-part else-part))
                    ((when changep) (combine-ifs-in-then-and-else-branches term (+ -1 count)))
                    ((mv changep term)
                     ;; same test, then-part, and else-part as in the call above:
                     (combine-if-from-else-part test then-part else-part))
                    ((when changep) (combine-ifs-in-then-and-else-branches term (+ -1 count))))
                 `(if ,test ,then-part ,else-part))
             ;;it's a function call (maybe a lambda application):
             (cons (if (flambdap fn) ;test for lambda application.  term is: ((lambda (formals) body) ... args ...)
                       `(lambda ,(lambda-formals fn) ,(combine-ifs-in-then-and-else-branches (lambda-body fn) (+ -1 count)))
                     fn)
                   (combine-ifs-in-then-and-else-branches-list (fargs term) (+ -1 count)))))))))

 (defund combine-ifs-in-then-and-else-branches-list (terms count)
   (declare (xargs :guard (pseudo-term-listp terms)
                   :measure ;; (make-ord 2 (+ 1 (count-ifs-in-terms terms))
                   ;;           (make-ord 1 (+ 1 (count-ifs-in-then-and-else-branches-list terms))
                   ;;                     (acl2-count terms)))
                   (nfix (+ 1 count))
                   ))
   (if (zp count)
       terms
     (if (endp terms)
         nil
       (cons (combine-ifs-in-then-and-else-branches (first terms) (+ -1 count))
             (combine-ifs-in-then-and-else-branches-list (rest terms) (+ -1 count)))))))

(make-flag combine-ifs-in-then-and-else-branches)

(defthm-flag-combine-ifs-in-then-and-else-branches
  (defthm fake
    t
    :skip t
    :flag combine-ifs-in-then-and-else-branches)
  (defthm len-of-combine-ifs-in-then-and-else-branches-list
    (equal (len (combine-ifs-in-then-and-else-branches-list terms count))
           (len terms))
    :flag combine-ifs-in-then-and-else-branches-list)
  :hints (("Goal" ;:induct (len terms)
           :expand (combine-ifs-in-then-and-else-branches-list terms count)
           :in-theory (enable (:i len)
                              combine-ifs-in-then-and-else-branches-list))))

(defthm-flag-combine-ifs-in-then-and-else-branches
  (defthm pseudo-termp-of-combine-ifs-in-then-and-else-branches
    (implies (pseudo-termp term)
             (pseudo-termp (combine-ifs-in-then-and-else-branches term count)))
    :flag combine-ifs-in-then-and-else-branches)
  (defthm pseudo-term-listp-of-combine-ifs-in-then-and-else-branches
    (implies (pseudo-term-listp terms)
             (pseudo-term-listp (combine-ifs-in-then-and-else-branches-list terms count)))
    :flag combine-ifs-in-then-and-else-branches-list)
  :hints (("Goal" :in-theory (enable COMBINE-IFS-IN-THEN-AND-ELSE-BRANCHES
                                     COMBINE-IFS-IN-THEN-AND-ELSE-BRANCHES-LIST))))
