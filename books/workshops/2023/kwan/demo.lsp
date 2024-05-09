;; Simple examples on how to use LU decomposition / Gaussian elimination
;; Requires:
(include-book "lu")

;; Define a matrix
(defconst *A*
 (list (list 1 5)
       (list 3 1)))

;; Find its LU factorization
(lu *A*)

;; Get the upper triangular part of (lu *A*)
(get-U (lu *A*))

;; Get the unit lower triangular part of (lu *A*)
(get-L (lu *A*))

;; Mulitply the unit lower and upper triangular parts of (lu *A*)
(m* (get-L (lu *A*))
    (get-U (lu *A*)))

;; We get back *A*!
(mbt (equal (m* (get-L (lu *A*))
                (get-U (lu *A*)))
            *A*))


;; Define a matrix
(defconst *B*
 (list (list 1 2 2)
       (list 1 3 1)
       (list 2 1 5)))

;; Take its LU decomposition
(defconst *lu-B* (lu *B*))

;; Multiply upper and lower parts to recover original matrix
(mbt (equal (m* (get-L *lu-B*) (get-U *lu-B*)) *B*))
 

;; Define a larger matrix
(defconst *C*
 (list (list 1 8 7 4 1 29)
       (list 1 3 1 5 1 67)
       (list 4 7 3 1 1 32)
       (list 9 0 0 2 5 40)
       (list 9 0 0 2 6 89)
       (list 9 0 0 2 1 97)))

;; Take its LU decomposition
(defconst *lu-C* (lu *C*))

;; Multiply upper and lower parts to recover original matrix
(mbt (equal (m* (get-L (lu *C*)) (get-U (lu *C*))) *C*))

;; Inspect its row echolon form by performing Gaussian elimination
(mbt (equal (ge *C*) (list (list 1  8  7     4      1       29)
                           (list 0 -5 -6     1      0       38)
                           (list 0  0  5   -20     -3     -274)
                           (list 0  0  0 226/5 251/25 12853/25)
                           (list 0  0  0     0      1       49)
                           (list 0  0  0     0      0      253))))


;; Row echelon form of a nonsquare example
(defconst *D*
 (list (list 1 2 2 9)
       (list 1 3 1 6)
       (list 2 1 5 918375919)))

(mbt (equal (ge *D*) (list (list 1 2  2  9)
                           (list 0 1 -1 -3)
                           (list 0 0 -2 918375892))))


