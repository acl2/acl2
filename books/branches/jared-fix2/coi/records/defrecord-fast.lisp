#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#

(in-package "ACL2")

;Eric's attempt to make a version of this which uses Jared's fast memories
;(bascially replacing g below with mem::load and s below with mem::store.)


(include-book "memory")
(include-book "records")
(include-book "data-structures/memories/memory" :dir :system)

(defun symbol-list-to-string (list)
  (declare (type (satisfies symbol-listp) list))
  (if (consp list)
      (concatenate 'string (symbol-name (car list)) (symbol-list-to-string (cdr list)))
    ""))

(defmacro join-symbols (witness &rest rst)
  `(intern-in-package-of-symbol (symbol-list-to-string (list ,@rst)) ,witness))

(defmacro defrecord-fast (name &key (rd 'nil) (wr 'nil) (clr 'nil) (fix 'ifix) (default 'nil) (typep 'integerp))

  (let* ((base name)
         (default (if (null default) `(,fix nil) default))
         (rd  (if (null rd)  (join-symbols name name '-rd) rd))
         (wr  (if (null wr)  (join-symbols name name '-wr) wr))
         (clr (if (null clr) (join-symbols name name '-clr) clr))
         (wf  (join-symbols name 'wf-  typep))
         (zp  (join-symbols name typep '-zp))
         (wf-forward (join-symbols name wf '-forward))
         )

    `(encapsulate
      ()
      
      (defun ,zp (x)
        (declare (type t x))
        (equal (,fix x) ,default))
      
      (defun ,wf (x)
        (declare (type t x))
        (and (consp x)
             (,typep (car x))
             (not (,zp (car x)))
             (not (,wf (cdr x)))))
      
      (in-theory (disable (,zp) (,wf)))

      (defthm ,wf-forward
        (implies (,wf x)
                 (and (consp x)
                      (,typep (car x))
                      (not (,zp (car x)))
                      (not (,wf (cdr x)))))
        :rule-classes (:forward-chaining))

      (defun ,wr (a v m)
        (declare (type t v)
                 (xargs :guard (and (mem::memory-p m)
                                    (mem::address-p a m)))
                 )
        (let ((x (mem::load a m)))
          (if (,wf x)
              (if (,zp v)
                  (mem::store a (cdr x) m)
                (mem::store a (cons (,fix v) (cdr x)) m))
            (if (,zp v) m
              (mem::store a (cons (,fix v) x) m)))))
      
      (defun ,rd (a m)
        (declare ;(type t a)
                 (xargs :guard (and (mem::memory-p m)
                                    (mem::address-p a m)
                                    )))
        (let ((x (mem::load a m)))
          (if (,wf x) (car x)
            ,default)))
      
      
      (defthm ,(join-symbols base rd '-same- wr '-hyps)
        (implies (equal a b)
                 (equal (,rd a (,wr b v r)) 
                        (,fix v))))
      
      (defthm ,(join-symbols base rd '-diff- wr '-hyps)
        (implies (not (equal a b))
                 (equal (,rd a (,wr b v r))
                        (,rd a r))))
      
      (defthm ,(join-symbols base wr '-same- rd '-hyps)
        (implies (equal a b)
                 (equal (,wr a (,rd b r) r) 
                        r)))
      
      (defthm ,(join-symbols base wr '-diff- wr '-hyps)
        (implies (not (equal a b))
                 (equal (,wr b y (,wr a x r))
                        (,wr a x (,wr b y r))))
        :rule-classes ((:rewrite :loop-stopper ((b a ,wr)))))
      
      (defthm ,(join-symbols base wr '-same- wr '-hyps)
        (implies (equal a b)
                 (equal (,wr a y (,wr b x r))
                        (,wr a y r))))
      
      (defthm ,(join-symbols base rd '-of- wr '-redux)
        (equal (,rd a (,wr b v r))
               (if (equal b a) (,fix v)
                 (,rd a r)))
        :hints (("goal" :in-theory (disable ,fix ,rd ,wr))))
      
      (defthm ,(join-symbols base wr '-same- rd)
        (equal (,wr a (,rd a r) r) 
               r))
      
      (defthm ,(join-symbols base wr '-same- wr)
        (equal (,wr a y (,wr a x r))
               (,wr a y r)))
      
      (defthm ,(join-symbols base typep '- rd)
        (and (,typep (,rd a r))
             (equal (,fix (,rd a r))
                    (,rd a r))))

      (defun ,clr (a m)
        (,wr a ,default m))

      (defthm ,(join-symbols base rd '-over- clr)
        (equal (,rd a1 (,clr a2 r))
               (if (equal a1 a2) (,fix nil)
                 (,rd a1 r)))
        :hints (("goal" :cases ((equal a1 a2))
                 :in-theory (enable g-of-s-redux))))
      
      (defthm ,(join-symbols base clr '-over- wr)
        (equal (,clr a1 (,wr a2 v r))
               (if (equal a1 a2) (,clr a1 r)
                 (,wr a2 v (,clr a1 r)))))
      
      (defthm ,(join-symbols base clr '-over- clr)
        (implies 
         (not (equal a1 a2))
         (equal (,clr a1 (,clr a2 r))
                (,clr a2 (,clr a1 r)))))

      (defthm ,(join-symbols base clr '-of- clr)
        (equal (,clr a (,clr a r))
               (,clr a r)))
    
      (defun ,(join-symbols base wr '==r-hyp) (v a r)
        (declare (type t v)
                 (xargs :guard (and (mem::memory-p r)
                                    (mem::address-p a r)
                                    ))
                 )
        (equal (,fix v) (,rd a r)))

      (defthm ,(join-symbols base wr '==r)
        (implies
         (and 
          (,(join-symbols base wr '==r-hyp) v a r1)
          (equal r2 r1))
         ;(and (equal (equal r1 (,wr a v r2)) 
         ;            t)
              (equal (equal (,wr a v r2) r1) 
                     t)
         ;     )
         ))

      (defun ,(join-symbols base wr '== wr '-hyp) (v1 v2)
        (declare (type t v1 v2))
        (equal (,fix v1) (,fix v2)))

      (in-theory (disable (,(join-symbols base wr '== wr '-hyp))))

      (defthm ,(join-symbols base wr '== wr)
        (implies
         (and 
          (equal a1 a2)
          (,(join-symbols base wr '== wr '-hyp) v1 v2)
          (equal r2 r1))
         (equal (equal (,wr a1 v1 r1) (,wr a2 v2 r2))
                t)))

      (defthm ,(join-symbols base wr '==r!)
        (equal (equal r1 (,wr a v r2))
               (and (tag-location a (equal (,rd a r1) (,fix v)))
                    (equal (,clr a r1)
                           (,clr a r2)))))
      
      (defthm ,(join-symbols base clr '-differential)
        (implies
         (equal (,clr a r1) (,clr a r2))
         (equal (equal r1 r2)
                (equal (,rd a r1)
                       (,rd a r2))))
        :hints (("goal" :do-not '(preprocess))))
      
      (in-theory (disable ;,(join-symbols base wr '==r!)
                  ,(join-symbols base rd '-of- wr '-redux)
                  ,rd ,wr ,clr))
      
      ;; new with the fast-memory implementation:

      (defthm ,(join-symbols base 'memory-p-of- wr)
        (implies (mem::memory-p m)
                 (mem::memory-p (,wr a v m)))
        :hints (("Goal" :in-theory (enable ,wr))))
      
      (defthm ,(join-symbols base 'size-of- wr)
        (implies (mem::memory-p mem)
                 (equal (mem::size (,wr addr elem mem))
                        (mem::size mem)))
        :hints (("Goal" :in-theory (enable ,wr))))
      

      )))

(local
 (encapsulate
  ()

  ;; Try it out!!

  (defund sbp16 (x)
    (declare (xargs :guard t))
    (and
     (integerp x)
     (<= (- (expt 2 15)) x)
     (< x (expt 2 15))))
  
  (defund fix-sbp16 (x)
    (declare (xargs :guard t))
    (if (sbp16 x) x 0))
  
  (defthm sbp16-fix-sbp16
    (sbp16 (fix-sbp16 x))
    :hints (("goal" :in-theory (enable fix-sbp16 sbp16))))

  (defthm fix-sbp16-of-sbp16
    (implies
     (sbp16 x)
     (equal (fix-sbp16 x) x))
    :hints (("goal" :in-theory (enable fix-sbp16 sbp16))))

  (defrecord-fast sbp :rd getbv :wr putbv :fix fix-sbp16 :typep sbp16)

  ))
    

;; Skipped for now (is it used? should it be converted to use fast memories?)


;; (defmacro defthing (name &key (rd 'nil) (wr 'nil) (fix 'ifix) (default 'nil) (typep 'integerp))

;;   (let* ((base name)
;;          (default (if (null default) `(,fix nil) default))
;;          (rd  (if (null rd) (join-symbols name name '-rd) rd))
;;          (wr  (if (null wr) (join-symbols name name '-wr) wr))
;;          (wf  (join-symbols name 'wf-  typep))
;;          (zp  (join-symbols name typep '-zp))
;;          (wf-forward (join-symbols name wf '-forward))
;;          )

;;     `(encapsulate
;;       ()
      
;;       (defun ,zp (x)
;;         (declare (type t x))
;;         (equal (,fix x) ,default))
      
;;       (defun ,wf (x)
;;         (declare (type t x))
;;         (and (consp x)
;;              (,typep (car x))
;;              (not (,zp (car x)))
;;              (not (,wf (cdr x)))))
      
;;       (in-theory (disable (,zp) (,wf)))

;;       (defthm ,wf-forward
;;         (implies (,wf x)
;;                  (and (consp x)
;;                       (,typep (car x))
;;                       (not (,zp (car x)))
;;                       (not (,wf (cdr x)))))
;;         :rule-classes (:forward-chaining))

;;       (defun ,wr (v x)
;;         (declare (type t v x))
;;         (if (,wf x)
;;             (if (,zp v)
;;                 (cdr x)
;;               (cons (,fix v) (cdr x)))
;;           (if (,zp v) x
;;             (cons (,fix v) x))))
      
;;       (defun ,rd (x)
;;         (declare (type t x))
;;         (if (,wf x) (car x)
;;           ,default))
      
      
;;       (defthm ,(join-symbols base rd '-same- wr)
;;         (equal (,rd (,wr v r)) 
;;                (,fix v)))
      
;;       (defthm ,(join-symbols base wr '-same- rd)
;;         (equal (,wr (,rd r) r)
;;                r))
      
;;       (defthm ,(join-symbols base wr '- wr)
;;         (equal (,wr y (,wr x r))
;;                (,wr y r)))
      
;;       (defthm ,(join-symbols base typep '- rd)
;;         (and (,typep (,rd r))
;;              (equal (,fix (,rd r))
;;                     (,rd r))))

;;       (defthm ,(join-symbols base wr '==r)
;;         (implies
;;          (syntaxp (not (equal v '(quote 0))))
;;          ;(and 
;;           (equal (equal r1 (,wr v r2))
;;                      (and (equal (,rd r1) (,fix v))
;;                           (equal (,wr 0 r1) (,wr 0 r2)))) 
;;           ;    (equal (equal (,wr v r2) r1)
;;            ;          (and (equal (,fix v) (,rd r1))
;;             ;              (equal (,wr 0 r2) (,wr 0 r1))))
;;              ; )
;;          ))


;;       (in-theory (disable ,rd ,wr))

;;       )))

