(in-package "JVM")
(include-book "../M6-DJVM-shared/jvm-class-table")
(include-book "../M6-DJVM-shared/jvm-state")

(defun class-rep-verified? (class-rep)
  (< (class-status class-rep) *CLASS_VERIFIED*))

;; temp implementation, which every class is verified.

(defun verify-class1 (class-rep s)
  (let* ((new-class-rep 
          (class-rep-set-class-status *CLASS_VERIFIED* class-rep))
         (old-instance-class-table (instance-class-table s))
         (new-instance-class-table 
          (replace-class-table-entry class-rep new-class-rep
                                     old-instance-class-table)))
    (state-set-instance-class-table 
     new-instance-class-table s)))
         

;; we can proof, if it reach the stage of verifying class,
;; loading must succeeded, (super must exists? except for java.lang.Object)

(defun check-super-class-isnt-final (class-rep s)
  (let* ((supername (super class-rep))
         (super-rep   (class-by-name supername (instance-class-table s)))
         (accessflags (class-accessflags super-rep)))
    (mem '*final* accessflags)))

(defun check-interface-super-class-is-JavaLangObject (class-rep s)
  (declare (ignore s))
  (let* ((supername (super class-rep)))
    (equal supername "java.lang.Object")))


(defun verify-class (class-rep s) 
  (if (not (check-super-class-isnt-final class-rep s))
      (fatalError "class-extends-final-class" s)
    (if (isInterface class-rep) 
        (if (not (check-interface-super-class-is-JavaLangObject class-rep s))
            (fatalError "interfaces-does-not-extends-JavaLangObject" s)
          (verify-class1 class-rep s))
      (verify-class1 class-rep s))))

