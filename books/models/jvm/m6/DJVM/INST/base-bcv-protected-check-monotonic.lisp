(in-package "BCV")
(include-book "../../BCV/typechecker")
(include-book "../../BCV/bcv-functions")
(include-book "base-bind-free")


(local 
 (encapsulate ()
   (local (include-book "../../BCV/bcv-isAssignable-transitive"))
   (defthm isAssignable-Transitive
     (implies (and (good-bcv-type t1 icl)
                   (good-bcv-type t2 icl)
                   (good-bcv-type t3 icl)
                   (equal (classtableEnvironment env) scl)
                   (good-icl icl)
                   (good-scl scl)
                   (icl-scl-compatible icl scl)
                   (isAssignable t1 t2 env)
                   (isAssignable t2 t3 env))
              (isAssignable t1 t3 env))
     :hints (("Goal" :in-theory (e/d () (isjavaassignable good-scl jvm::primitive-type?))
              :do-not '(generalize fertilize))))))

;;;
;;; note: Tue Jul 12 21:17:01 2005
;;;
;;;  bcv-isAssignable-transitive.lisp need major work to get rid of skip
;;;  proofs!! 
;;;
;;;  Fri Jul 15 13:25:52 2005. Done. after 3 days. 
;;;

;; (local (include-book "base-bcv-check-monotonic-support"))

;;(i-am-here) ;; Fri Jul 15 14:34:21 2005

; Matt K. mod: Avoid raw Lisp error in tau; see similar disable in
; BCV/bcv-isAssignable-transitive.lisp.
(local (in-theory (disable (:e tau-system))))

(defthm passesprotectedfieldcheck-general-then-pass-in-specific
  (implies (and (bind-free (replace-occurance-binding 'sFrame 'gframe s 'g)
                            (g))
                (bind-free (acl2::default-bind-free 'icl 'icl
                                                    (acl2::pkg-witness
                                                     "DJVM")) (icl))
                (BCV::PASSESPROTECTEDFIELDCHECK
                 ENV1
                 fieldclassname
                 fieldname
                 fieldtype
                 g)
                (bcv::isassignable s g env1)
                (bcv::good-bcv-type g icl)
                (bcv::good-bcv-type s icl)
                (bcv::good-bcv-type (bcv::prefix-class
                                     (bcv::classClassname 
                                      (bcv::classenvironment env1)))
                                    icl)
                (bcv::good-icl icl)
                (bcv::good-scl (CLASSTABLEENVIRONMENT ENV1))
                (bcv::icl-scl-compatible icl (bcv::classtableEnvironment env1)))
           (BCV::PASSESPROTECTEDFIELDCHECK
            ENV1
            fieldclassname
            fieldname
            fieldtype
            s))
  :hints (("Goal" :in-theory (e/d ()
                                  (bcv::consistent-sig-stack
                                   bcv::prefix-class
                                   bcv::good-icl
                                   icl-scl-compatible
                                   bcv::classtableEnvironment
                                   bcv::classenvironment
                                   bcv::classClassname
                                   bcv::good-bcv-type
                                   bcv::isassignable))
           :use ((:instance isAssignable-Transitive
                            (t1 s)
                            (t2 g)
                            (t3 (bcv::prefix-class
                                 (bcv::classClassname 
                                  (bcv::classenvironment env1))))
                            (scl (classtableEnvironment env1))
                            (env env1))))))
          

