;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

;; ======================================================================

(in-package "X86ISA")
(include-book "row-wow-thms" :ttags :all :dir :proof-utils)

;; ======================================================================

(defthm nthcdr-true-listp
  (implies (true-listp xs)
           (true-listp (nthcdr n xs)))
  :rule-classes (:rewrite :type-prescription))

(encapsulate
 ()

 (local
  (include-book "std/lists/take" :dir :system))

 (defthm take-true-listp
   (implies (true-listp xs)
            (true-listp (take n xs)))
   :rule-classes (:rewrite :type-prescription))

 )

(defthm nthcdr-of-bytes-of-obj-non-empty
  (implies (and (< 0 (len bytes-of-obj))
                (< obj-offset bytes-of-obj))
           (and (nthcdr obj-offset bytes-of-obj)
                (< 0 (len (nthcdr obj-offset bytes-of-obj))))))

(in-theory (e/d () (take nthcdr)))

;; ======================================================================

;; File descriptor and contents fields:

(defthm file-descriptor-fieldp-implies-natp-offset
  (implies (file-descriptor-fieldp x)
           (natp (cdr (assoc-equal :offset x))))
  :rule-classes (:type-prescription :forward-chaining))

(defthm file-contents-fieldp-implies-stringp-contents
  (implies (file-contents-fieldp x)
           (stringp (cdr (assoc-equal :contents x))))
  :rule-classes (:type-prescription :forward-chaining))

(defthm file-descriptor-fieldp-preserved
  (implies (file-descriptor-fieldp ss)
           (file-descriptor-fieldp (put-assoc-equal
                                    :offset
                                    (+ 1 (cdr (assoc-equal :offset ss)))
                                    ss))))

(in-theory (e/d ()
                (file-descriptor-fieldp
                 file-contents-fieldp)))

;; ======================================================================
