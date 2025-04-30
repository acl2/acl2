; (include-book "tools/include-raw" :dir :system)

(defttag :z3)
;; taken from ccg.lisp
; (include-book "hacking/hacker" :dir :system)
;(acl2::progn+all-ttags-allowed
; (include-book "hacking/all" :dir :system :ttags :all))
(acl2::subsume-ttags-since-defttag)

;; useful for debugging...
;; (set-debugger-enable t)

;; Some stuff has to be include-raw'ed because it uses packages not known to ACL2.
(acl2::include-raw "z3_raw_code.lsp" :host-readtable t)

(acl2::defun-bridge z3-query-fn (query types)
  :program nil
  :raw
  (progn (z3-solver-init)
         (z3-assert-fn query types)
         (let ((res (z3-check-sat)))
           (if (equal res :sat)
               (z3-get-model-as-assignment)
             res))))

(defmacro z3-query (query types)
  `(z3-query-fn ',query ',types))

;; Let's define some datatypes and functions.
(defintrange val -100 100)
(defdata tuple (list val val val val val))
(definec t-size (l :tuple) :int
  (b* (((list a b c d e) l))
    (+ a b c d e)))

;; ACL2s is able to find a counterexample to this statement.
(test? (=> (tuplep l)
           (not (> (t-size l) 100))))

;; But it can't find a counterexample to this statement.
(test? (=> (tuplep l)
           (not (> (t-size l) 490))))

;; Let's ask Z3 the same questions.
;; It's able to find a counterexample here
(z3-query
 (x :int y :int z :int a :int b :int)
 (and (> x -100) (< x 100)
      (> y -100) (< y 100)
      (> z -100) (< z 100)
      (> a -100) (< a 100)
      (> b -100) (< b 100)
; You can also require some variables are distinct
      (distinct x y z a b)
      (> (+ x y z a b) 100)))

;; And also here.
(z3-query
 (x :int y :int z :int a :int b :int)
 (and (> x -100) (< x 100)
      (> y -100) (< y 100)
      (> z -100) (< z 100)
      (> a -100) (< a 100)
      (> b -100) (< b 100)
      (distinct x y z)
      (distinct a b x)
      (distinct a y x)
      (> (+ x y z a b) 490)))

;; Let's ask a similar question about list lengths.
(test? (=> (^ (listp x) (listp y) (listp z)
              (< (len x) 100)
              (< (len y) 100)
              (< (len z) 100))
           (< (+ (len x) (len y) (len z)) 280)))

;; Z3 does (eventually) find a model.
(z3-query
 (x (:seq :int) y (:seq :int) z (:seq :int))
 (and (< (seq-length x) 100)
      (< (seq-length y) 100)
      (< (seq-length z) 100)
      (>= (+ (seq-length x) (seq-length y) (seq-length z)) 280)))
