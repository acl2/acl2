

(in-package "ACL2")

;; This book defines an event-introducing macro, DEFINED-CONST.  This only
;; really works with the HONS system (in particular, memoize.)

;;  Usage:
;; (defined-const *my-result* (my-expensive (ground-term))

;; This produces the following events:
;; (defconst *my-result* <result>)
;; (defthm *my-result*-def
;;    (equal (my-expensive (ground-term))
;;           *my-result*))

;; where <result> is the value of (my-expensive (ground-term)).
;; The tricky thing that DEFINED-CONST automates is doing this while only
;; running (my-expensive (ground-term)) once.

;; Optional keyword arguments are :thmname (chooses the name of the defthm)
;; and :rule-classes (chooses the rule-classes of the defthm; default is
;; :rewrite.)

;; Note that if you use :rule-classes :rewrite and want the theorem to fire,
;; you'll need to disable the appropriate executable counterparts of functions
;; that appear in the term.  Also, ACL2 may refuse to create rewrite rules
;; targetting certaing ground expressions; Matt Kaufmann provided this example
;; which fails:

;; (defined-const *foo* (+ 2 3))

;; In these cases you can supply :rule-classes nil to allow this to work.




(defmacro defined-const (constname
                         term
                         &key
                         thmname
                         (rule-classes ':rewrite))
  (let ((thmname (or thmname (intern-in-package-of-symbol
                              (concatenate 'string
                                           (symbol-name constname) "-DEF")
                              constname))))
    `(encapsulate nil

       (local
        (progn
          (in-theory nil)
       
          (defun defined-const-memoize-fn1 ()
                (declare (xargs :verify-guards nil))
                ,term)

          (in-theory (disable (defined-const-memoize-fn1)))

          (defun defined-const-memoize-fn ()
                (declare (xargs :guard t))
                (ec-call (defined-const-memoize-fn1)))

          (defthm defined-const-memoize-fn-is-term
            (equal ,term
                   (defined-const-memoize-fn))
            :hints (("goal" :in-theory (disable (defined-const-memoize-fn))))
            :rule-classes nil)

          (memoize 'defined-const-memoize-fn)))

       (make-event
        (let ((val (defined-const-memoize-fn)))
          `(progn (defconst ,',constname ',val)
                  (defthm ,',thmname
                    (equal ,',term ,',constname)
                    :hints (("goal" :use defined-const-memoize-fn-is-term))
                    :rule-classes ,',rule-classes)))))))


