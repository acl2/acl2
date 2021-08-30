

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

(defun defined-const-fn (constname
                         term
                         thmname
                         rule-classes
                         evisc hons)
  (let ((thmname (or thmname (intern-in-package-of-symbol
                              (concatenate 'string
                                           (symbol-name constname) "-DEF")
                              constname))))
    `(with-output
      :off :all :on (error)
      (encapsulate nil

        (local
         (progn
           (in-theory '((:definition hons-copy)))

           (defun defined-const-memoize-fn1 ()
             (declare (xargs :verify-guards nil))
             ,term)

           (in-theory (disable (defined-const-memoize-fn1)))

           (defun defined-const-memoize-fn ()
             (declare (xargs :guard t))
             ,(if hons
                  '(hons-copy (ec-call (defined-const-memoize-fn1)))
                '(ec-call (defined-const-memoize-fn1))))

           (defthm defined-const-memoize-fn-is-term
             (equal ,term
                    (defined-const-memoize-fn))
             :hints (("goal" :in-theory (disable (defined-const-memoize-fn))))
             :rule-classes nil)

           (memoize 'defined-const-memoize-fn)))


        (make-event
         `(make-event
           (let ((val ,(if (eq (getprop 'defined-const-memoize-fn 'formals 'none 'current-acl2-world
                                        (w state))
                               'none)
                           ;; This checks to see whether the local events above
                           ;; were run.  If so, we run defined-const-memoize-fn;
                           ;; if not, it probably means we're in an include-book
                           ;; of an uncertified book, in which case we just run
                           ;; the original term.
                           ',term
                         '(defined-const-memoize-fn))))
             `(progn (with-output
                      :stack :pop
                      (defconst ,',',constname
                        ,,,(if hons
                               ```(hons-copy ',val)
                               ```',val)))
                     (with-output
                      :stack :pop
                      (defthm ,',',thmname
                        (equal ,',',term ,',',constname)
                        :hints (("goal" :use defined-const-memoize-fn-is-term))
                        :rule-classes ,',',rule-classes))
                     (with-output
                      :stack :pop
                      (table defined-const-table
                             ',',',constname ',',',thmname))
                     ,@(and ,,evisc
                            `((with-output
                               :stack :pop
                               (table evisc-table ,',',constname
                                      ,(let ((name (symbol-name ',',constname)))
                                         (if (may-need-slashes name)
                                             (concatenate 'string "#.|" name "|")
                                           (concatenate 'string "#."
                                                        name)))))))
                     ,@(and ,,hons
                            `((with-output
                               :stack :pop
                               (table persistent-hons-table
                                      ,',',constname t))))))))))))


(defmacro defined-const (constname
                         term
                         &key
                         thmname
                         rule-classes
                         evisc hons)
  (defined-const-fn constname term thmname rule-classes evisc hons))


;; Simple tests to make sure it works.

(local (defined-const *foo* 3))
(local (defined-const *bar* 3 :hons t))
(local (defined-const *baz* 3 :evisc t :hons t))
