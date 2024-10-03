;; this file comes necessary definitions to introduce the class loading
;; invariant. Which will be introduced in the guard of
;; build-a-java-visible-instance, and load_class2

(in-package "JVM")
(include-book "../M6-DJVM-shared/jvm-loader-primitives")
(include-book "../M6-DJVM-shared/jvm-loader-constant-pool-primitives")

(acl2::set-verify-guards-eagerness 2)

(defun class-is-loaded? (classname class-table)
  (declare (xargs :guard (wff-instance-class-table class-table)))
  (isClassTerm (class-by-name classname class-table)))

;; now class-is-loaded-from only check that classname, superclass, interfaces
;; because we only care about the loader's property that if a class is loaded,
;; its super classes are also loaded.
;;
(defun class-is-loaded-from (class-rep class-rep-static)
  (declare (xargs :guard (and (wff-class-rep class-rep)
                              (wff-class-rep-static class-rep-static))))
  (and (equal (classname  class-rep) (classname-s  class-rep-static))
       (equal (super      class-rep) (super-s      class-rep-static))
       (equal (interfaces class-rep) (interfaces-s class-rep-static))))
       

               ;(wff-class-rep (class-by-name classname class-table))
               ;(wff-class-rep (class-by-name classname class-table))

(defthm loaded-from-wff-implies-wff
  (implies (and (class-is-loaded? classname cl)
                (wff-instance-class-table-strong cl))
           (wff-class-rep (class-by-name classname cl))))


(defthm loaded-from-wff-implies-wff-static
  (implies (and (mv-nth 0 (class-by-name-s classname env-cl))
                (wff-static-class-table-strong env-cl))
           (wff-class-rep-static (mv-nth 1 (class-by-name-s classname env-cl)))))
           

(defun correctly-loaded? (classname class-table env-class-table)
  (declare (xargs :guard (and (wff-instance-class-table-strong class-table)
                              (wff-static-class-table-strong env-class-table))
                  :guard-hints (("Goal" :in-theory (disable wff-class-rep 
                                                            wff-class-rep-static)))))
  (mv-let (found class-rep-static)
          (class-by-name-s classname env-class-table)
          (and found ;; should we move this into the guard??. We can. 
               (class-is-loaded? classname class-table)
               (class-is-loaded-from 
                                 (class-by-name classname class-table) 
                                 class-rep-static))))


(defun all-correctly-loaded? (supers class-table env-class-table)
  (declare (xargs :guard (and (wff-instance-class-table-strong class-table)
                              (wff-static-class-table-strong env-class-table))))
  (if (not (consp supers))
      t
    (and (correctly-loaded? (car supers) class-table env-class-table)
         (all-correctly-loaded? (cdr supers) class-table env-class-table))))



(defun loader-inv-helper1 (class-rep class-table env-class-table)
  (declare (xargs :guard (and (wff-class-rep class-rep)
                              (wff-instance-class-table-strong class-table)
                              (wff-static-class-table-strong env-class-table))))
  (let* ((classname (classname class-rep))
         (supers    (collect-assignableToName classname env-class-table)))
    (all-correctly-loaded? supers class-table env-class-table))) 


(defun loader-inv-helper (classes class-table env-class-table)
  (declare (xargs :guard (and (wff-instance-class-table-strong classes)
                              (wff-instance-class-table-strong class-table)
                              (wff-static-class-table-strong env-class-table))))
  (if (not (consp classes))
      t
    (and (loader-inv-helper1 (car classes) class-table env-class-table)
         (loader-inv-helper (cdr classes) class-table env-class-table))))


(defun loader-inv (s)
 (and (wff-state s)
      (wff-class-table (class-table s))
      (wff-env (env s))
      (wff-instance-class-table-strong (instance-class-table s))
      (wff-static-class-table-strong (external-class-table s))
      (or (not (no-fatal-error? s))
          (loader-inv-helper (instance-class-table s) (instance-class-table s)
                             (env-class-table (env s))))))
  







