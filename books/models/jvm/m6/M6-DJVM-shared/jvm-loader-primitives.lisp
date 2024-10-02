(in-package "JVM")
(include-book "../M6-DJVM-shared/jvm-object-manipulation-primitives")
(include-book "../M6-DJVM-shared/jvm-state")
(include-book "../M6-DJVM-shared/jvm-type-value")


(acl2::set-verify-guards-eagerness 2)

; ---- primitives for converting ACL2 string 
;      to m6 array object, futher to a m6 string.

(defun countdown-measure-guard (bound offset)
  (and (integerp bound)
       (integerp offset)
       (<= offset bound)))

(defun countdown-measure (bound offset)
  (declare (xargs :guard (countdown-measure-guard bound offset)))
  (if (zp (- bound offset))
             0
           (+ 1 (- bound offset))))

(defun str-to-array-char-data (str offset bound) 
  (declare (xargs :measure  (countdown-measure bound offset)
                  :guard (and (countdown-measure-guard bound offset)
                              (<= 0 offset)
                              (stringp str)
                              (<= bound (length str)))))
    (if (zp (- bound offset))
        nil
      (cons (char-code (char str offset))
            (str-to-array-char-data str (+ offset 1) bound))))

(defun str-to-array-obj (str s)
  (declare (xargs :guard (and (stringp str)
                              (build-a-java-visible-instance-guard
                               "java.lang.Object" s))))
  (let* ((array-data (str-to-array-char-data str 0 (length str)))
         (bound (len array-data)))
    (make-array (make-array-type 'char) 
                bound 
                array-data
                S)))


(defun make-immediate-string-part (array offset bound)
  (cons "java.lang.String" 
        (list (cons "value"  array)
              (cons "offset" offset)
              (cons "count"  bound))))


(defun make-java-lang-string-visible-part (str S)
  (declare (xargs :guard (and (stringp str)
                              (wff-state s)
                              (wff-heap (heap s))
                              (build-a-java-visible-instance-guard
                               "java.lang.Object" s))))
  (mv-let (Object-jvp new-s1)
          (build-a-java-visible-instance "java.lang.Object" s)
          ;; build-a-javaString assume the String's superclass is Object.
          (mv-let (array new-s2)
                  (str-to-array-obj str new-s1)
                  (let* ((heap1 (heap new-s2))
                         (new-array-addr (alloc heap1))
                         (heap2 (bind new-array-addr array heap1))
                         (bound (length str))
                         (offset 0)
                         (string-obj  
                          (cons (make-immediate-string-part 
                                 new-array-addr offset bound)
                                Object-jvp)))
                    (mv string-obj
                        (update-trace new-array-addr (state-set-heap heap2 new-s2)))))))

(defthm alistp-bind-alistp
  (implies (alistp l)
           (alistp (bind x any l))))


(defthm make-java-lang-string-visible-part-preserve-wff-state
  (implies (wff-state s)
           (wff-state (mv-nth 1 (make-java-lang-string-visible-part str S)))))

(defthm make-java-lang-string-visible-part-preserve-wff-heap
  (implies (wff-heap (heap s))
           (wff-heap (heap  (mv-nth 1 (make-java-lang-string-visible-part str S))))))

(defthm make-java-lang-string-visible-part-no-change-class-table
  (equal (class-table (mv-nth 1 (make-java-lang-string-visible-part str S)))
         (class-table s)))


;; this functions are used in building the string object when we load constant
;; pool

(defun ACL2-str-to-JavaString (str S)
  (declare (xargs :guard (and (stringp str)
                              (wff-state s)
                              (wff-heap (heap s))
                              (build-a-java-visible-instance-guard
                               "java.lang.Object" s))))
  (let ((common-info     (build-common-info "java.lang.String"))
        (specific-info   (build-STRING-specific-info)))
    (mv-let (java-visible-portion new-state)
            (make-java-lang-string-visible-part str S)
            (mv (make-object common-info specific-info java-visible-portion)
                new-state))))


;; (in-theory (disable ACL2-str-to-JavaString))

(defun create-string-guard (str s)
  (and (stringp str)
       (wff-state s)
       (wff-heap (heap s))
       (build-a-java-visible-instance-guard "java.lang.Object" s)))

(defun ACL2-str-to-JavaString-ref (str S)
  (declare (xargs :guard (create-string-guard str s)))
  (mv-let (the-String-obj new-S)
          (ACL2-str-to-JavaString str S)
          (let* ((heap   (heap new-S))
                 (new-addr (alloc heap))
                 (new-heap (bind new-addr the-String-obj heap)))
            (mv new-addr
                (update-trace new-addr (state-set-heap new-heap new-s))))))

;-----------------



