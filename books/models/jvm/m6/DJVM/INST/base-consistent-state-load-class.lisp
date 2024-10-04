(in-package "DJVM")
(include-book "../../DJVM/consistent-state")
(include-book "../../DJVM/consistent-state-properties")
(include-book "../../M6-DJVM-shared/jvm-bytecode")


(in-theory (disable getArrayClass resolveClassReference state-set-heap update-trace))

(in-theory 
 (disable jvm::load_class-guard
          jvm::load_class
          wff-state
          topStack-guard
          wff-heap
          jvm::arg
          tag-ref-tag
          jvm::load_class2_guard
          consistent-state
          aux pending-exception
          jvm::load_array_class
          popstack-of-thread
          jvm::build-an-array-instance
          jvm::build-a-java-visible-instance-guard
          jvm::load_array_class_guard))


(in-theory (enable current-method-ptr))

;; (defthm can-load-array-class-in-consistent-state
;;   (implies (CONSISTENT-STATE S)
;;            (JVM::LOAD_ARRAY_CLASS_GUARD S))
;;   :hints (("Goal" :in-theory (enable consistent-state
;;                                      jvm::load_array_class_guard))))


;; (defthm can-load-class-in-consistent-state
;;   (implies (CONSISTENT-STATE S)
;;            (JVM::LOAD_CLASS-GUARD S))
;;   :hints (("Goal" :in-theory (enable consistent-state
;;                                      jvm::load_class-guard))))

;; ;; ;; above. 
;; ;; ;; for guard verification. not essential properties of ...
;; ;; ;; ;; moved to base-consistent-state.lisp 
;;  Wed Jun  8 14:43:22 2005


(encapsulate () 
 (local (include-book "base-loader-preserve-consistent-state"))
 (acl2::set-enforce-redundancy t)
 
 (defthm resolveClassReference-preserve-consistency
   (implies (consistent-state s)
            (consistent-state (resolveClassReference any s))))


 (defthm getArrayClass-preserve-consistency
   (implies (consistent-state s)
            (consistent-state (getArrayClass any s)))))


;;;
;;; the following should be in base-load-class-normalize.lisp!! 
;;;