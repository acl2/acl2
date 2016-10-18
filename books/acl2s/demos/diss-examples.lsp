(in-package "ACL2S")
(include-book "acl2s/cgen/top" :dir :system :ttags :all)
(include-book "misc/eval" :dir :system)
;Chapter 1

(acl2s-defaults :set testing-enabled :naive)
(acl2s-defaults :set num-trials 4000)

(defun fermat-prime (n)
  (1+ (expt 2 (expt 2 n))))

;is k a factor of n other than 1 and n?
(defun factorp (k n)
  (and (< 1 k)
       (< k n)
       (natp (/ n k))))

(defun fermat-factor-fixer (k n)
  (1+ (* k (expt 2 (+ 1 n)))))

(cgen::define-rule fermat-factor-fixer
  :hyp (and (posp n)
            (< n '15)
            (posp k))
  :rule (let ((k (fermat-factor-fixer k n)))
          (factorp k (fermat-prime n)))
  :rule-classes :fixer
  :override-check t)

(acl2s-defaults :set use-fixers t)

(must-fail
(test?
 (implies (and (posp k)
               (posp n)
               (< n 15) 
               (factorp k (fermat-prime n)))
          nil)) 
)

;Chapter 3

(acl2s-defaults :set testing-enabled t)
(acl2s-defaults :set verbosity-level 2)
(defdata triple (list pos pos pos))
(defun trianglep (v)
  (and (triplep v)
       (< (third v)  (+ (first v)  (second v)))
       (< (first v)  (+ (second v) (third v)))
       (< (second v) (+ (first v)  (third v)))))
(defun triple-enum (n)
  (b* (((list n1 n2 n3) (split 3 n)))
    (list (1+ n1) (1+ n2) (1+ n3))))

(defun triangle-enum (n)
  (let ((x (triple-enum n)))
    (if (trianglep x)
        x
      '(1 1 1))))
(register-type triangle
  :predicate trianglep
  :enumerator triangle-enum)
(defun shape (v)
    (if (trianglep v)
        (cond ((equal (first v) (second v))
               (if (equal (second v) (third v))
                   "equilateral"
                 "isosceles"))
              ((equal (second v) (third v)) "isosceles")
              ((equal (first v) (third v)) "isosceles")
              (t "scalene"))
      "error"))
(must-fail
(thm
   (implies (and (trianglep x)
                 (= (third x) (* (second x) (first x))))
            (not (equal "isosceles" (shape x))))))

; Chap 4

(defdata RGB (enum (list "red" "green" "blue")))

(defdata loi  (oneof nil (cons integer loi)))

(defdata loi2 (listof integer))
(include-book "acl2s/ccg/ccg" :dir :system)
(set-termination-method :ccg)
(defdata tree (oneof 'Leaf
                     (Node (id . integer)
                           (left  . tree)
                           (right . tree))))
(defdata
  (sexp (oneof symbol integer slist))
  (slist (oneof nil (cons sexp slist))))


;CHap 6

(defdata-attach integer-list
  :constraint (nth i x)
  :constraint-variable x
  :rule (implies (and (natp i)
                      (integerp x.i)
                      (integer-listp x1))
                 (equal x (update-nth i x.i x1)))
  :match-type :subterm-match)

