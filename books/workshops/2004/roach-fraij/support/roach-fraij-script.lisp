(in-package "ACL2")



                                        ;-------------------------------------------------------------------------
                                        ; A simplified model of the High-Assurance Transformation System (HATS)
                                        ;
                                        ; Abstract:
                                        ;
                                        ; This is a simplified model of the High-Assurance Transformation System
                                        ; (HATS). The goal of this model is to resolve pointers in an input table in a
                                        ; transformational fashion. Such a table consists of finite number of lists,
                                        ; each list has two components. The first components is a natural number and
                                        ; the second is either a string or a natural number that is strictly less than
                                        ; the first components. In this model, the natural numbers play the role of
                                        ; pointers. Thus, each pointer is associated with a string or another pointer
                                        ; and we aim at resolving the second components so that we have ONLY strings.
                                        ;
                                        ; According to our description of a table, the following table, to which we
                                        ; refer as constant-pool, is well-formed:
                                        ;
                                        ;constant-pool'((0 "Zero")
                                        ;       (1 0)
                                        ;       (2 1))
                                        ;
                                        ; To resolve the pointers in the table "constant-pool" in a transformational
                                        ; fashion, we need to relate the two components of each list in "constant-pool"
                                        ; through the use of a transformation rule. For example, the following
                                        ; transformation rule
                                        ;
                                        ; TR1-0 = ((?x 0) -> (?x "Zero"))
                                        ;
                                        ; states that whenever there is a list that has the natural number 0 as its
                                        ; second components, replace that 0 with the string "Zero" and keep the FIRST
                                        ; components as it is.. The question mark "?" at the begining of each sublist
                                        ; in TR1-0 means that x is a variable and can be matched with anything.
                                        ;
                                        ; To reolve the pointers in "constant-pool", we need to generate a
                                        ; transformation rule for every list in that "constant-pool". To generate these
                                        ; rules, we developed a function, namely "generate-rule," that take a
                                        ; "constant-pool" as an input and generates the corresponding transformation
                                        ; rules. The result of applying the function "generate-rule" on the table
                                        ; "constant-pool" is the following transformation rules, to which we refer as
                                        ; rule-list.
                                        ;
                                        ; TR1-0 = ((x 0)-> (x "Zero"))
                                        ; TR1-1 = ((x 1) -> (x 0))
                                        ; TR1-2 = ((x 2) -> (x 1))
                                        ;
                                        ; Thereafter, we need to apply these rules to every list in "constant-pool;"
                                        ; i.e., appying the rule-list to the first list in the constant-pool, then
                                        ; applying them again to the second list, and eventually applying them to the
                                        ; third. We developed a function "once-strategy" that takes as an input a
                                        ; "constant-pool" and a set of transformation rules and does the process. Thus,
                                        ; if we apply the "once-strategy" function to the table "constant-pool" using
                                        ; the rule-list that we have, the result will be as follows.
                                        ;
                                        ; constant-pool = '((0 "Zero")
                                        ;         (1 "Zero")
                                        ;         (2 0))
                                        ;
                                        ; This result shows that there is one unresolved pointer, namely "0" in the
                                        ; list (2 0). This suggests that we have to apply the "once-strategy"
                                        ; exhaustively, until no further application is possible. We developed a
                                        ; function "fix-strategy1" that takes the table "constant-pool" and the
                                        ; corresponding rule-list and applies "once-strategy" repeatedly until no
                                        ; further application is possible. The application of the function
                                        ; "fix-strategy1" to the table "constant-pool" using the rule-list gives the
                                        ; following fully-resolved table.
                                        ;
                                        ; constant-pool = '((0 "Zero")
                                        ;         (1 "Zero")
                                        ;         (2 "Zero"))
                                        ;
                                        ; The last function the I developed was fix-strategy that takes a constant-pool
                                        ; as an input, generates the corresponding rule-list, and call the function
                                        ; fix-strategy1.
                                        ;
                                        ; The main functions that are used in this simplified model are presented below
                                        ; starting with the main function that will be invoked:
                                        ;
                                        ;1 fix-strategy (constant-pool)
                                        ;1.1 generate-trnsf-rules (constant-pool)
                                        ;1.2 fix-strategy1 (rule-list constant-pool)
                                        ;1.2.1 once-strategy (rule-list tail constant-pool)
                                        ;1.2.1.1 apply-rule-list-to-node (rule-list position classfile)
                                        ;1.2.1.1.1 apply-rule-to-node (rule position classfile)
                                        ;
                                        ; Our ultimate goal is to prove the correctness of the function
                                        ; fix-strategy. Thus, we develop a semantic function, namely "get-constant."
                                        ; This function takes a natural number, n, as an input and chases it down a
                                        ; give table, i.e., giving a meaning to the number n. Our main conjecture is to
                                        ; show that:
                                        ;
                                        ; get-constant (n constant-pool) = get-constant (n fix-strategy constant-pool)
                                        ;-------------------------------------------------------------------------

;;------------------------------------------------------
;; Predicates
;;-----------
                                        ;--------------------------------------------------------------
                                        ; well-fomed-classfile-entryp returns true if the input
                                        ; "one-entry"is a valid classfile entry.
                                        ;--------------------------------------------------------------
(defun well-formed-classfile-entryp (one-entry)
  (and (consp one-entry)
       (natp (car one-entry))
       (or (stringp (cadr one-entry))
           (and (natp (cadr one-entry))
                (< (cadr one-entry)
                   (car one-entry))))
       (equal (cddr one-entry) nil)))
;;[x]
                                        ;--------------------------------------------------------------
                                        ; well-formed-classfilep returns true if the input "classfile"
                                        ; is a well-formed classfile.
                                        ;--------------------------------------------------------------
(defun well-formed-classfilep (classfile)
  (if (endp classfile)
      (null classfile)
    (and (well-formed-classfile-entryp (car classfile))
         (well-formed-classfilep (cdr classfile)))))
;;[x]


(defthm example-1
    (let ((classfile '((0 "zero")
                       (1 "one")
                       (2 "two")
                       (3 0)
                       (4 1)
                       (5 2)
                       (6 "six")
                       (7 4)
                       (8 5)
                       (9 6))))
      (well-formed-classfilep classfile))
  :rule-classes nil)

                                        ;--------------------------------------------------------------
                                        ; lhs returns the car of the input transformation rule.
                                        ;--------------------------------------------------------------
(defun lhs (rule)
  (car rule))
;;[x]

                                        ;--------------------------------------------------------------
                                        ; rhs returns the cadr of the input transformation rule.
                                        ;--------------------------------------------------------------
(defun rhs (rule)
  (cadr rule))
;;[x]
                                        ;--------------------------------------------------------------
                                        ; well-formed-rulep returns true if the input "rule"
                                        ; is a well-formed transformation rule.
                                        ;--------------------------------------------------------------
(defun well-formed-rulep (rule)
  (and (consp rule)
       (natp (lhs rule))
       (or (stringp (rhs rule))
           (and (natp (rhs rule))
                (< (rhs rule)
                   (lhs rule))))
       (equal (cddr rule) nil)))
;;[x]

                                        ;--------------------------------------------------------------
                                        ; well-formed-rule-listp returns true if the input "rule-list"
                                        ; is a well-formed list of transformation rule.
                                        ;--------------------------------------------------------------
(defun well-formed-rule-listp (rule-list)
  (if (endp rule-list)
      (null rule-list)
    (and (well-formed-rulep (car rule-list))
         (well-formed-rule-listp (cdr rule-list)))))
;;[x]


(defthm example-2
    (let ((classfile '((0 "zero")
                       (1 "one")
                       (2 "two")
                       (3 0)
                       (4 1)
                       (5 2)
                       (6 "six")
                       (7 4)
                       (8 5)
                       (9 6))))
      (well-formed-rule-listp classfile))
  :rule-classes nil)

;;------------------------------------------------------
;; Functions
;;-----------
                                        ;-------------------------------------------------------------------------
                                        ; The function get-constant repeatedly chases a pointer, n, in the links
                                        ; in the pointer chain starting at n until it arrives at a string and
                                        ; returns it.
                                        ;-------------------------------------------------------------------------
(defun get-constant (n classfile)
  (let ((temp (assoc n classfile)))
    (cond ((null temp) nil)
          ((stringp (cadr temp)) (cadr temp))
          ((or (not (natp n))
               (not (natp (cadr temp)))
               (<= n (cadr temp)))
           nil)
          (t (get-constant (cadr temp) classfile)))))
;;[x]

;;-----------------------------------------------------------------------
;; The function resolve links uses resolve-links1 as a subroutine to
;; iterate down the table replacing each associated value by the terminal
;; value from the original table.
;;-----------------------------------------------------------------------
(defun resolve-links1 (tail classfile)
  (cond ((endp tail) nil)
        (t (cons (list (car (car tail))
                       (get-constant (car (car tail)) classfile))
                 (resolve-links1 (cdr tail) classfile)))))
;;[x]

(defun resolve-links (classfile)
  (resolve-links1 classfile classfile))
;;[x]

;;------------------------------------------------------
;; Theorems
;;---------
(defthm assoc-resolve-links1
    (implies (well-formed-classfilep tail)
             (equal (assoc n (resolve-links1 tail classfile))
                    (if (assoc n tail)
                        (list n (get-constant n classfile))
                      nil))))

;;-------------
;; Main theorem:
;;-------------
;; The main theorem "get-constant-resolve-links" startes that: the result of
;; chacing a pointer n in the table classfile after resolving its pointers will
;; be the same as chacing the same pointer in the original classfile.
                                        ;-------------------------------------------------------------------------
(defthm get-constant-resolve-links
    (implies (well-formed-classfilep classfile)
             (equal (get-constant n (resolve-links classfile))
                    (get-constant n classfile))))

(in-theory (disable resolve-links
                    assoc-resolve-links1
                    get-constant-resolve-links))

;;--------
;; example
;;--------
(defthm example-3
    (let ((classfile '((0 "zero")
                       (1 "one")
                       (2 "two")
                       (3 0)
                       (4 1)
                       (5 2)
                       (6 "six")
                       (7 4)
                       (8 5)
                       (9 6))))
      (and
       (equal (get-constant 8 classfile) "two")
       (equal (get-constant 9 classfile) "six")
       (equal (get-constant 7 classfile) "one")
       (equal (resolve-links classfile)
              '((0 "zero")
                (1 "one")
                (2 "two")
                (3 "zero")
                (4 "one")
                (5 "two")
                (6 "six")
                (7 "one")
                (8 "two")
                (9 "six")))))
  :rule-classes nil)

;;---------------------------------------------------------------
;; Predicates
;;-----------
;;--------------------------------------------------------------
;; sem-ok-rulep returns true if the rule is well-formed wrt
;; classfile
;;--------------------------------------------------------------
(defun sem-ok-rulep (rule classfile)
  (and (well-formed-rulep rule)
       (equal (get-constant (lhs rule) classfile)
              (if (stringp (rhs rule))
                  (rhs rule)
                (get-constant (rhs rule) classfile)))))
;;[x]

;;-------------------------------------------------------------------------
;; sem-ok-rule-listp returns true if the rule-list is well-formed wrt
;; classfile
;;-------------------------------------------------------------------------
(defun sem-ok-rule-listp (rule-list classfile)
  (if (endp rule-list)
      (null rule-list)
    (and (sem-ok-rulep (car rule-list) classfile)
         (sem-ok-rule-listp (cdr rule-list) classfile))))
;;[x]

(defthm example-4
    (let ((classfile '((0 "zero")
                       (1 "one")
                       (2 "two")
                       (3 0)
                       (4 1)
                       (5 2)
                       (6 "six")
                       (7 4)
                       (8 5)
                       (9 6)))
          (rule-list '((0 "zero")
                       (1 "one")
                       (2 "two")
                       (3 "zero")
                       (4 1)
                       (5 2)
                       (6 "six")
                       (7 4)
                       (8 5)
                       (9 6))))
      (sem-ok-rule-listp rule-list classfile))
  :rule-classes nil)


;;------------------------------------------------------
;; Function
;;-----------
(defun matches (rule position classfile)
  (let ((node (assoc position classfile)))
    (and (sem-ok-rulep rule classfile)
         (well-formed-classfile-entryp node)
         (equal (lhs rule)
                (rhs node)))))

(defthm example-5
    (let ((classfile '((0 "zero")
                       (1 "one")
                       (2 "two")
                       (3 0)
                       (4 1)
                       (5 2)
                       (6 "six")
                       (7 4)
                       (8 5)
                       (9 6))))
      (and (matches '(0 "zero") 3 classfile)
           (matches '(5 2) 8 classfile)))
  :rule-classes nil)
;;[x]

;;------------------------------------------------------
;; Predicates
;;------------
(defun matchp (rule-list position classfile)
  (if (endp rule-list)
      nil
    (or (matches(car rule-list) position classfile)
        (matchp (cdr rule-list) position classfile))))
;;[x]

(defun all-matchp (rule-list tail classfile)
  (let ((position (caar tail)))
    (cond ((endp tail) nil)
          (t (or (matchp rule-list position classfile)
                 (all-matchp rule-list (cdr tail) classfile))))))
;;[x]

;;------------------------------------------------------
;; Functions
;;-----------
                                        ;-------------------------------------------------------------------------
                                        ; sum-classfile-entry is a function that accepts one list of a classfile
                                        ; as an input and produces the corresponding weight of the second component
                                        ; of it. Every natural number is assigned its original value plus 1; however,
                                        ; every string is assigned the value 0. We do this to add 0 as a weight for
                                        ; any string and shift evey natural by one to reflect this shift.
                                        ;-------------------------------------------------------------------------
(defun sum-classfile-entry (entry)
  (if (natp (cadr entry))
      (1+ (cadr entry))
    0))
;;[x]

                                        ;-------------------------------------------------------------------------
                                        ; sum-addr-to-resolve is a function that accepts a classfile as an input
                                        ; and produces the corresponding total-weight of the second column of it.
                                        ; It calls sum-classfile-entry repeatedly to get the weight of the second
                                        ; components of each list inb the classfile. This function is necessary to
                                        ; prove the termination of the function fix-strategy function.
                                        ;-------------------------------------------------------------------------
(defun sum-addr-to-resolve (classfile)
  (if (endp classfile)
      0
    (+ (sum-classfile-entry (car classfile))
       (sum-addr-to-resolve (cdr classfile)))))
;;[x]

                                        ;-------------------------------------------------------------------------
                                        ; put-in-place is a function that inserts a node in its correct location
                                        ; in classfile.
                                        ;-------------------------------------------------------------------------
(defun put-in-place (node classfile)
  (let ((temp (assoc (car node) classfile)))
    (if (null temp)
        classfile
      (cond ((endp classfile) nil)
            ((equal (car node) (caar classfile))
             (cons node (cdr classfile)))
            (t (cons (car classfile) (put-in-place node (cdr classfile))))))))
;;[x]

(defthm example-6
    (let ((classfile '((0 "zero")
                       (1 "one")
                       (2 "two")
                       (3 0)
                       (4 3)
                       (5 4)
                       (6 5)
                       (7 4)
                       (8 5)
                       (9 6))))
      (and (equal (put-in-place '(9 "zero") classfile)
                  '((0 "zero")
                    (1 "one")
                    (2 "two")
                    (3 0)
                    (4 3)
                    (5 4)
                    (6 5)
                    (7 4)
                    (8 5)
                    (9 "zero")))))
  :rule-classes nil)

;;-----------------------------------------------------------------------
;; Theorems
;;---------
(defthm well-formed-classfilep-put-in-place
    (implies (and (well-formed-classfilep classfile)
                  (well-formed-classfile-entryp node))
             (well-formed-classfilep (put-in-place node classfile))))
;;[x]

(defthm assoc-put-in-place
    (implies (assoc n classfile)
             (equal (assoc n
                           (put-in-place node classfile))
                    (if (equal n (car node))
                        node
                      (assoc n classfile)))))
;;[x][y]

(defthm get-constant-n-<-x
    (implies (and (natp n)
                  (< n x)
                  (well-formed-classfilep classfile))
             (< (get-constant n classfile) x)))
;;[x][y]


;;-----------------------------------------------------------------------
;; Function
;;---------
                                        ;-------------------------------------------------------------------------
                                        ; The function get-constant-path repeatedly chases a pointer, n, in the links
                                        ; in the pointer chain starting at n until it arrives at a pointer that leads
                                        ; to a string and returns the whole chain.
                                        ;-------------------------------------------------------------------------
(defun get-constant-path (n classfile)
  (let ((temp (assoc n classfile)))
    (cond ((null temp) nil)
          (t (if (or (stringp (cadr temp))
                     (not (natp n))
                     (not (natp (cadr temp)))
                     (<= n (cadr temp)))
                 (list n)
               (cons n (get-constant-path (cadr temp) classfile)))))))

(defthm example-7
    (let ((classfile '((0 "zero")
                       (1 "one")
                       (2 "two")
                       (3 0)
                       (4 1)
                       (5 2)
                       (6 "six")
                       (7 4)
                       (8 5)
                       (9 6))))
      (and
       (equal (get-constant-path 8 classfile) '(8 5 2))
       (equal (get-constant-path 9 classfile) '(9 6))
       (equal (get-constant-path 7 classfile) '(7 4 1))))
  :rule-classes nil)

;;-----------------------------------------------------------------------
;; Theorems
;;---------
(defthm member-n-bounded-in-cf
    (implies (member n (get-constant-path n classfile))
             (assoc n classfile)))
;;[x][y]

(defthm car-assoc-x-classfile
    (implies (assoc x classfile)
             (equal (car (assoc x classfile)) x)))
;;[x]

(defthm assoc-n-classfile-implies
    (implies (and (well-formed-classfilep classfile)
                  (assoc n classfile))
             (and (natp n)
                  (or (and (natp (cadr (assoc n classfile)))
                           (< (cadr (assoc n classfile)) n))
                      (stringp (cadr (assoc n classfile))))))
  :rule-classes :forward-chaining)
;;[x]

(defthm stringp-cadr-assoc-n-classfile
    (implies (and (not (null (assoc n classfile)))
                  (stringp (cadr (assoc n classfile)))
                  (< n x))
             (equal (get-constant n (put-in-place (list x y) classfile))
                    (cadr (assoc n classfile))))
  :hints (("goal" :expand (get-constant n (put-in-place (list x y) classfile)))))
;;[x]

(defthm not-assoc-get-constant-nil
    (implies (not (assoc n classfile))
             (not (get-constant n classfile))))
;;[x]

(defthm not-assoc-n-classfile-not-assoc-n-put-in-place
    (implies (not (assoc n classfile))
             (not (assoc n (put-in-place (list x y) classfile)))))
;;[x]

(defthm get-constant-put-in-place-<
    (implies (and (well-formed-classfilep classfile)
                  (< n x))
             (equal (get-constant n (put-in-place (list x y) classfile))
                    (get-constant n classfile)))
  :hints (("subgoal *1/5'''" :expand (get-constant n (put-in-place (list x y)
                                                                   classfile)))
          ("subgoal *1/3'" :use ((:instance assoc-n-classfile-implies)))))
;;[x]

(defthm get-constant-put-in-place-=
    (implies (and (assoc n classfile)
                  (well-formed-classfilep classfile)
                  (well-formed-classfile-entryp (list n y)))
             (equal (get-constant n (put-in-place (list n y) classfile))
                    (if (stringp y)
                        y
                      (get-constant y classfile)))))
;;[x]

(defthm not-member-position-gc-put-in-place
    (implies (not (member position (get-constant-path n classfile)))
             (equal (get-constant n (put-in-place (list position any) classfile))
                    (get-constant n classfile))))
;;[x]

(defthm member-position-path-get-constant-n-1
    (implies (member position (get-constant-path n classfile))
             (equal (get-constant n classfile)
                    (get-constant position classfile)))
  :hints (("goal" :in-theory (disable get-constant))
          ("subgoal *1/4" :expand (get-constant n classfile))))
;;[x]

(defthm member-position-path-get-constant-n-2
    (implies (member position (get-constant-path n classfile))
             (member position (get-constant-path n (put-in-place (list position
                                                                       any) classfile)))))

(defthm not-null-assoc-n-classfile
    (implies (not (null (assoc n classfile)))
             (assoc n classfile)))
;;[x]

(defthm get-constant-put-in-place-stringp
    (implies (and (well-formed-classfilep classfile)
                  (member position
                          (get-constant-path n classfile))
                  (stringp any)
                  (equal (get-constant position classfile)
                         any))
             (equal (get-constant n
                                  (put-in-place (list position any)
                                                classfile))
                    any))
  :hints (("goal" :induct (get-constant n classfile))))


(defthm get-constant-put-in-place-stringp-1
    (implies (and (well-formed-classfilep classfile)
                  (member position
                          (get-constant-path n classfile))
                  (stringp any)
                  (equal (get-constant position classfile)
                         any))
             (equal (get-constant n
                                  (put-in-place (list position any)
                                                classfile))
                    (get-constant n classfile)))
  :hints (("goal" :in-theory (disable get-constant
                                      get-constant-path
                                      well-formed-classfilep))))

(defthm member-position-gc-put-in-place
    (implies (and (well-formed-classfilep classfile)
                  (well-formed-classfile-entryp (list position any))
                  (member position (get-constant-path n classfile))
                  (equal (get-constant position classfile)
                         (if (stringp any)
                             any
                           (get-constant any classfile))))
             (equal (get-constant n (put-in-place (list position any) classfile))
                    (get-constant n classfile)))
  :hints (("goal" :induct (get-constant n classfile)
                  :in-theory (disable well-formed-classfilep))))


(defthm member-position-gc-put-in-place-general
    (implies (and (well-formed-classfilep classfile)
                  (well-formed-classfile-entryp (list position any))
                  (equal (get-constant position classfile)
                         (if (stringp any)
                             any
                           (get-constant any classfile))))
             (equal (get-constant n (put-in-place (list position any) classfile))
                    (get-constant n classfile)))
  :hints (("goal" :cases ((member position (get-constant-path n classfile))))))


;;------------------------------------------------------
;; Function
;;-----------
                                        ;-------------------------------------------------------------------------
                                        ; apply-rule-to-node is a function that applies a trnasformation rule
                                        ; to a position that corresponds to a node in classfile.
                                        ;-------------------------------------------------------------------------
(defun apply-rule-to-node (rule position classfile)
  (let ((temp (assoc position classfile)))
    (cond ((null temp) classfile)
          ((matches rule position classfile)
           (put-in-place (list (car temp) (rhs rule))
                         classfile))
          (t classfile))))
;;[x][y]

(defthm example-8
    (let ((classfile '((0 "zero")
                       (1 "one")
                       (2 "two")
                       (3 0)
                       (4 1)
                       (5 2)
                       (6 "six")
                       (7 4)
                       (8 5)
                       (9 6))))
      (equal (apply-rule-to-node '(5 2) 8 classfile)
             '((0 "zero")
               (1 "one")
               (2 "two")
               (3 0)
               (4 1)
               (5 2)
               (6 "six")
               (7 4)
               (8 2)
               (9 6))))
  :rule-classes nil)
;;------------------------------------------------------
;; Theorems
;;-----------
(defthm well-formed-apply-rule-to-node
    (implies (well-formed-classfilep classfile)
             (well-formed-classfilep (apply-rule-to-node rule position
                                                         classfile)))
  :hints (("goal" :in-theory (enable rhs
                                     lhs))))

;;[x][y]

(defthm matches-implies-wfcfep
    (implies (matches rule position classfile)
             (well-formed-classfile-entryp
              (list position (rhs rule))))
  :hints (("goal" :in-theory (enable lhs rhs))))
;;[x][y]

(defthm get-constant-apply-rule-to-node
    (implies (well-formed-classfilep classfile)
             (equal (get-constant n (apply-rule-to-node rule position classfile))
                    (get-constant n classfile))))

;;------------------------------------------------------
;; Theorems: proof of termination
;;-------------------------------
(defthm sum-addr-put-in-place-<=
    (implies (and (well-formed-classfilep classfile)
                  (or (stringp x)
                      (< x (cadr (assoc n classfile)))))
             (<= (sum-addr-to-resolve (put-in-place (list n x)
                                                    classfile))
                 (sum-addr-to-resolve classfile))))
;;[x][y]

(defthm sum-addr-apply-rule-to-node-<=
    (implies (well-formed-classfilep classfile)
             (<= (sum-addr-to-resolve (apply-rule-to-node rule n classfile))
                 (sum-addr-to-resolve classfile)))
  :rule-classes :linear)
;;[x][y]

(defthm sum-addr-put-in-place-strictly-<
    (implies (and (well-formed-classfilep classfile)
                  (natp (cadr (assoc n classfile)))
                  (or (stringp x)
                      (< x (cadr (assoc n classfile)))))
             (< (sum-addr-to-resolve (put-in-place (list n x)
                                                   classfile))
                (sum-addr-to-resolve classfile))))
;;[x][y]

(defthm sum-addr-apply-rule-to-node-strictly-<
    (implies (and (matches rule n classfile)
                  (well-formed-classfilep classfile))
             (< (sum-addr-to-resolve (apply-rule-to-node rule n classfile))
                (sum-addr-to-resolve classfile)))
  :rule-classes :linear)

;;[x][main]

;;------------------------------------------------------
;; Function
;;-----------
                                        ;-------------------------------------------------------------------------
                                        ; apply-rule-list-to-node is a function that applies a list of
                                        ; trnasformation rules, namely rule-list, to a position that corresponds
                                        ; to a node in classfile.
                                        ;-------------------------------------------------------------------------
(defun apply-rule-list-to-node (rule-list position classfile)
  (if (endp rule-list)
      classfile
    (apply-rule-list-to-node (cdr rule-list)
                             position
                             (apply-rule-to-node (car rule-list)
                                                 position
                                                 classfile))))

(defthm example-9
    (let ((classfile '((0 "zero")
                       (1 "one")
                       (2 "two")
                       (3 0)
                       (4 1)
                       (5 2)
                       (6 "six")
                       (7 4)
                       (8 5)
                       (9 6))))
      (equal (apply-rule-list-to-node classfile 9 classfile)
             '((0 "zero")
               (1 "one")
               (2 "two")
               (3 0)
               (4 1)
               (5 2)
               (6 "six")
               (7 4)
               (8 5)
               (9 "six"))))
  :rule-classes nil)
;;------------------------------------------------------
;; Theorems
;;-----------
(defthm well-formed-apply-rule-list-to-node
    (implies (well-formed-classfilep classfile)
             (well-formed-classfilep (apply-rule-list-to-node rule-list position classfile))))
;;[x][y]

(defthm get-constant-n-apply-rule-list-to-node
    (implies (well-formed-classfilep classfile)
             (equal (get-constant n (apply-rule-list-to-node rule-list position classfile))
                    (get-constant n classfile)))
  :hints (("goal" :in-theory (disable apply-rule-to-node))))

;;------------------------------------------------------
;; Theorems: proof of termination
;;-------------------------------
(defthm not-matches-apply-rule-to-node
    (implies (not (matches rule n classfile))
             (equal (apply-rule-to-node rule n classfile)
                    classfile)))
;;[x][y]

(in-theory (disable sem-ok-rule-listp
                    well-formed-classfile-entryp
                    sum-classfile-entry
                    sem-ok-rulep
                    matches
                    apply-rule-to-node))
;;[x][y]

(defthm sum-addr-apply-rule-list-to-node-<=
    (implies (well-formed-classfilep classfile)
             (<= (sum-addr-to-resolve (apply-rule-list-to-node rule-list n classfile))
                 (sum-addr-to-resolve classfile)))
  :rule-classes :linear)
;;[x][y]


(defthm sum-addr-apply-rule-list-to-node-strictly-<
    (implies (and (well-formed-classfilep classfile)
                  (matchp rule-list n classfile))
             (< (sum-addr-to-resolve (apply-rule-list-to-node rule-list n classfile))
                (sum-addr-to-resolve classfile)))
  :rule-classes :linear)
;;[x][main]

;;------------------------------------------------------
;; Function
;;---------
                                        ;-------------------------------------------------------------------------
                                        ; once-strategy is a function that applies a set of
                                        ; trnasformation rules, namely rule-list, to the set of nodes within a
                                        ; tail. Note that when once-strategy is called, tail and classfile are
                                        ; identical, however as once-strategy executes tail decreases and classfile
                                        ; stays the same.
                                        ;-------------------------------------------------------------------------
(defun once-strategy (rule-list tail classfile)
  (if (endp tail)
      classfile
    (once-strategy rule-list
                   (cdr tail)
                   (apply-rule-list-to-node rule-list (caar tail) classfile))))

(defthm example-10
    (let ((classfile '((0 "zero")
                       (1 "one")
                       (2 "two")
                       (3 0)
                       (4 1)
                       (5 2)
                       (6 "six")
                       (7 4)
                       (8 5)
                       (9 6))))
      (equal (once-strategy classfile classfile classfile)
             '((0 "zero")
               (1 "one")
               (2 "two")
               (3 "zero")
               (4 "one")
               (5 "two")
               (6 "six")
               (7 1)
               (8 2)
               (9 "six"))))
  :rule-classes nil)

;;------------------------------------------------------
;; Theorems
;;---------
(defthm get-constant-n-once-strategy
    (implies (well-formed-classfilep classfile)
             (equal (get-constant n (once-strategy rule-list tail classfile))
                    (get-constant n classfile))))
;;[x][main]



;;------------------------------------------------------
;; Theorems: proof of termination
;;-------------------------------
(defthm well-formed-once-strategy
    (implies (well-formed-classfilep classfile)
             (well-formed-classfilep (once-strategy rule-list tail classfile))))
;;[x][y]

(defthm sum-addr-once-strategy-<=
    (implies (well-formed-classfilep classfile)
             (<= (sum-addr-to-resolve (once-strategy rule-list tail classfile))
                 (sum-addr-to-resolve classfile)))
  :rule-classes :linear)

(defthm not-matchp-apply-rule-list-to-node
    (implies (not (matchp rule-list (caar tail) classfile))
             (equal (apply-rule-list-to-node rule-list (caar tail) classfile)
                    classfile)))

(defthm sum-addr-once-strategy-strictly-<
    (implies (and (well-formed-classfilep classfile)
                  (all-matchp rule-list tail classfile))
             (< (sum-addr-to-resolve (once-strategy rule-list tail classfile))
                (sum-addr-to-resolve classfile)))
  :rule-classes :linear)
;;[x][main]

(defthm not-all-matchp-once-strategy
    (implies (not (all-matchp rule-list tail classfile))
             (equal (once-strategy rule-list tail classfile)
                    classfile)))

;;[x]

(defthm sum-addr-to-resolve-type
    (and (integerp (sum-addr-to-resolve classfile))
         (<= 0 (sum-addr-to-resolve classfile)))
  :rule-classes :type-prescription
  :hints (("goal" :in-theory (enable sum-classfile-entry))))
;;[x][y]

;;------------------------------------------------------
;; Function
;;---------
                                        ;-------------------------------------------------------------------------
                                        ; fix-strategy1 keeps updating the input classfile by calling
                                        ; once-strategy. It stops when there is no more pointers in the second column
                                        ; of classfile to resolve.
                                        ;-------------------------------------------------------------------------
(defun fix-strategy1 (rule-list classfile)
  (declare (xargs :measure (sum-addr-to-resolve classfile)))
  (if (or                               ;(zp (sum-addr-to-resolve classfile))
       (not (all-matchp rule-list classfile classfile))
       (not (well-formed-classfilep classfile)))
      classfile
    (fix-strategy1 rule-list
                   (once-strategy rule-list classfile classfile))))
;;[x]

(defthm example-11
    (let ((classfile '((0 "zero")
                       (1 "one")
                       (2 "two")
                       (3 0)
                       (4 1)
                       (5 2)
                       (6 "six")
                       (7 4)
                       (8 5)
                       (9 6))))
      (equal (fix-strategy1 classfile classfile)
             '((0 "zero")
               (1 "one")
               (2 "two")
               (3 "zero")
               (4 "one")
               (5 "two")
               (6 "six")
               (7 "one")
               (8 "two")
               (9 "six"))))
  :rule-classes nil)

;;------------------------------------------------------
;; Theorems
;;---------
(defthm get-constant-n-fix-strategy1
    (implies (well-formed-classfilep classfile)
             (equal (get-constant n (fix-strategy1 rule-list classfile))
                    (get-constant n classfile)))
  :hints (("goal" :induct (fix-strategy1 rule-list classfile))))
;;[x][main]

(defthm well-formed-classfilep-fix-strategy1
    (implies (well-formed-classfilep classfile)
             (well-formed-classfilep (fix-strategy1 rule-list classfile))))
;;[x]

;;------------------------------------------------------
;; Functions
;;----------
(defun generate-rules (classfile)
  classfile)
;;[x]

                                        ;-------------------------------------------------------------------------
                                        ; fix-strategy generates a set of transformation rules, namely rule-list,
                                        ; for a given classfile using the function generate-rules. Then, it calls
                                        ; fix-strategy1 with using classfile and the rule-list as inputs.
                                        ;-------------------------------------------------------------------------
(defun fix-strategy (classfile)
  (let ((rule-list (generate-rules classfile)))
    (fix-strategy1 rule-list classfile)))
;;[x]

(defthm example-12
    (let ((classfile '((0 "zero")
                       (1 "one")
                       (2 "two")
                       (3 0)
                       (4 1)
                       (5 2)
                       (6 "six")
                       (7 4)
                       (8 5)
                       (9 6))))
      (equal (fix-strategy classfile)
             '((0 "zero")
               (1 "one")
               (2 "two")
               (3 "zero")
               (4 "one")
               (5 "two")
               (6 "six")
               (7 "one")
               (8 "two")
               (9 "six"))))
  :rule-classes nil)

;;------------------------------------------------------
;; Theorems
;;---------
(defthm well-formed-classfilep-fix-strategy
    (implies (well-formed-classfilep classfile)
             (well-formed-classfilep (fix-strategy classfile))))

;;[x]

(defthm get-constant-n-fix-strategy
    (implies (well-formed-classfilep classfile)
             (equal (get-constant n (fix-strategy classfile))
                    (get-constant n classfile)))
  :hints (("goal" :induct (fix-strategy1 rule-list classfile))))
;;[x]

;;------------------------------------------------------
;; Main theorem
;;-------------
(defthm get-constant-n-fix-strategy-is-get-constant-n-resolve-links
    (implies (well-formed-classfilep classfile)
             (equal (get-constant n (fix-strategy classfile))
                    (get-constant n (resolve-links classfile))))
  :hints (("goal" :in-theory (enable get-constant-resolve-links))))
;;[x]
                                        ;---------------------------------------------------------------
                                        ; End of file
                                        ;---------------------------------------------------------------

