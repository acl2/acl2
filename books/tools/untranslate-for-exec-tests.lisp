(in-package "ACL2")
(include-book "untranslate-for-exec")
(include-book "misc/assert" :dir :system)

(defmacro assert-same-stobjs-out (old-fn new-fn)
  `(make-event
    (b* ((world (w state))
         (old-stobjs-out (getprop ',old-fn 'acl2::stobjs-out nil 'acl2::current-acl2-world world))
         (new-stobjs-out (getprop ',new-fn 'acl2::stobjs-out nil 'acl2::current-acl2-world world))
         ((when (equal old-stobjs-out new-stobjs-out))
          (value '(value-triple :success))))
      (er soft ',new-fn
          "Stobjs-out mismatch: expected ~x0, found ~x1.~%"
          old-stobjs-out new-stobjs-out))))

(defun rebuild-function-fn (fn world)
  (b* ((new-fn (intern-in-package-of-symbol
                (concatenate 'string (symbol-name fn) "-NEW")
                fn))
       (new-fn-correct (intern-in-package-of-symbol
                        (concatenate 'string (symbol-name new-fn) "-CORRECT")
                        fn))
       (body       (getprop fn 'acl2::unnormalized-body nil 'acl2::current-acl2-world world))
       (formals    (getprop fn 'acl2::formals nil 'acl2::current-acl2-world world))
       (stobjs-out (getprop fn 'acl2::stobjs-out nil 'acl2::current-acl2-world world))
       (- (cw "Original body:  ~x0~%" body))
       ((mv errmsg new-body)
        (untranslate-for-execution body stobjs-out world))
       ((when errmsg)
        (er hard? 'rebuild-function "Error with untranslate-for-execution for ~x0: ~@1.~%"
            fn errmsg))
       (- (cw "Rewritten body: ~x0~%" new-body)))
    `(progn
       (defun ,new-fn ,formals
         ,new-body)
       (defthm ,new-fn-correct
         (equal (,new-fn . ,formals)
                (,fn . ,formals)))
       (assert-same-stobjs-out ,fn ,new-fn))))

(defmacro rebuild-function (fn)
  `(make-event
    (rebuild-function-fn ',fn (w state))))


;; Basic tests without much MV stuff.

(defun f1 () 5)
(rebuild-function f1)

(defun f2 (x) x)
(rebuild-function f2)

(defun f3 (x) (list x x))
(rebuild-function f3)

(defun f4 (x) (mv x x))
(rebuild-function f4)

(defun f5 (x) (let ((y x)) y))   ;; Basic non-MV lambda.
(rebuild-function f5)

(defun f6 (x) (let* ((y x)       ;; Nested non-MV lambdas.
                     (z y))
                (+ y z)))
(rebuild-function f6)

(defun f7 (x) (f4 x))   ;; Call of an MV function
(rebuild-function f7)

(defun f8 (x)  ;; IF with MVs in the branches
  (if x
      (f4 x)
    (mv x x)))
(rebuild-function f8)


(defun f9 (x)  ;; More IFs
  (cond
   ((equal x 1)
    (f4 x))
   ((equal x 2)
    (mv 1 2))
   (t
    (mv x 3))))

(rebuild-function f9)




;; ;; BOZO want to insert ignorable declarations as appropriate...

;; BOZO blah, we need to extend the convert-subexpressions-to-mv stuff to know
;; about calls of MV that we've already converted...

;; (set-ignore-ok t)
;; (defun f10 (x)  ;; IFs with Lambdas.
;;   (cond
;;    ((equal x 1)
;;     (let ((x 1))
;;       (f4 x)))
;;    ((equal x 2)
;;     (mv-let (x y)
;;       (f4 6)
;;       (mv 1 2)))
;;    (t
;;     (mv x 3))))
;; (rebuild-function f10)





;; (defun f5 (x)
;;   (mv-let (a b)
;;     (f4 x)
;;     (+ a b)))


;; (translate '(mv-let (a b)
;;               (f4 x)
;;               (+ a b))

;; (defmacro test-reincarnate (form)
;;   `(make-event
;;     (b* ((form ',form)
;;          (- (cw "Original:    ~x0~%" form))
;;          ((mv trans-er val state)
;;           )
;;          ((when trans-er)
;;           (mv trans-er val state))
;;          (- (cw "Translation: ~x0~%" val))
;;          ((mv errmsg recovered-form) (reincarnate-mvs val (w state)))
;;          (- (cw "Recovered:   ~x0~%" recovered-form))
;;          ((when errmsg)
;;           (er soft "Error message trying to rebuild form ~x0: ~@1.~%" form errmsg))
;;          ((when (equal recovered-form form))
;;           (value '(value-triple :success))))
;;       (er soft 'test-reincarnate-mvs
;;           "Failed to reincarnate ~x0: got ~x1 instead.~%" form recovered-form))))

;; (test-reincarnate 'x)
;; (test-reincarnate '(quote 1))
;; (test-reincarnate '(let ((x 1)) x))
;; (test-reincarnate '(let ((x 1)) x))


;; (defmacro test-reincarnate-mvs (form)

      
;;   (equal val 
     
;;   (
;;      (
  



;; zz

;; (reincarnate-mvs '((LAMBDA (MV)
;;                            ((LAMBDA (X Y) (H X Y))
;;                             (MV-NTH '0 MV)
;;                             (MV-NTH '1 MV)))
;;                    (CONS (F '1) (CONS (F '2) 'NIL)))
;;                  (w state))

;; (reincarnate-mvs '((LAMBDA (MV)
;;                            ((LAMBDA (X Y) (H X Y))
;;                             (MV-NTH '0 MV)
;;                             (MV-NTH '1 MV)))
;;                    (MV2 (F '1) (F '2)))
;;                  (w state))


;; #||

;; ))))))))))




  
       


;; (define match-cons-nest ((x pseudo-termp))
;;   :short "Matches @('(cons x1 (cons ... (cons xn 'nil)))')."
;;   :returns (mv (matchp booleanp :rule-classes :type-prescription)
;;                (args   pseudo-term-listp :hyp :guard))


;;        ((unless (and (consp body)
;;                      (consp (car body))))
;;         ;; Don't seem to have the right outer lambda structure.
;;         (mv nil nil nil nil))

;;        (

       
;;     (defun f (x) x)
;;     (defun g (x) x)
;;     (trans '(mv-let (x y) (mv (f 1) (f 2)) (list (g x) (g y))))

;;       -->

;;     ((LAMBDA (MV)
;;              ((LAMBDA (X Y)
;;                       (CONS (G X) (CONS (G Y) 'NIL)))
;;               (MV-NTH '0 MV)
;;               (MV-NTH '1 MV)))
;;      (CONS (F '1) (CONS (F '2) 'NIL)))

       


  

  
;;           (and (pseudo-termp x)
;;                (consp x)
;;                (consp (car x))))
;;    (world "ACL2 world for MV lookups."))
;;   :returns (mv (matchp booleanp :rule-classes :type-prescription)
;;                (vars   
;;   (if (and (pseudo-termp x)
;;            (



;; (define fix-mvs ((x pseudo-termp "A pseudo-term to rewrite.")
;;                  state)
;;   :returns (new-x "Rewritten copy of @('x') with @(see mv-let) terms
;;                    restored.")
;;   (b* (((when (atom x))
;;         ;; Just a variable, can't have any MVs involved.
;;         x)
;;        ((when (fquotep x))
;;         ;; Quoted constants, can't have any MVs involved.
;;         x)
;;        ((when (consp (car x)))
;;         ;; Lambda abbreviation.  Try to match the usual MV form.
;;         (
       
;;   (

;;  (defun fix-mvs (term state)




  



;; ; Tests -----------------------------------------------------------------------

;; (defun f1 (x) x)
;; (defun f2 (x) (mv x x))
;; (defun f3 (x) (mv x x x))
;; (defun f4 (x) (mv x x x x))

;; (defun t1 (x)
;;   (mv-let (a b)
;;     (f2 x)
;;     (list a b)))

;; (trans '(mv-let (a b)
;;           (f2 x)
;;           (list a b)))






;; (defun t1 (x)
;;   (let ((y (f1 x)))
;;     (mv-let (y z)
;;       (f2 y)
;;       (mv-let (a b c)
;;         (f3 z)
;;         (mv-let (w x y z)
;;           (f4 a)
;;           (mv a b c w x y z))))))

;; ||#
