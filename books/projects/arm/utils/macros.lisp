;; Cuong Chau <ckc8687@gmail.com>

;; June 2021

(in-package "RTL")

(local (include-book "rtl/rel11/lib/top-alt" :dir :system))

;; ======================================================================

(defmacro arith-5-for-rtl ()
  `(progn
     (include-book "arithmetic-5/top" :dir :system)

     (in-theory
      #!acl2(disable |(mod (+ x y) z) where (<= 0 z)|
                     |(mod (+ x (- (mod a b))) y)|
                     |(mod (mod x y) z)|
                     |(mod (+ x (mod a b)) y)|
                     mod-cancel-*-const
                     cancel-mod-+
                     reduce-additive-constant-<
                     ash-to-floor
                     |(floor x 2)|
                     |(equal x (if a b c))|
                     |(equal (if a b c) x)|
                     |(logior 1 x)|
                     mod-theorem-one-b
                     |(mod (- x) y)|))))

(defmacro bitthm (&rest thm)
  (declare (xargs :guard (and (true-listp thm)
                              (symbolp (car thm)))))
  (b* ((body (cadr thm))
       (term (cadr body)))
    `(defthm ,@thm
       :rule-classes ((:type-prescription :corollary (natp ,term))
                      (:linear :corollary (<= ,term 1))))))

(defmacro bvecthm (&rest thm)
  (declare (xargs :guard (and (true-listp thm)
                              (symbolp (car thm)))))
  (b* ((body (cadr thm))
       (implies-form? (equal (car body) 'implies))
       (term (if implies-form?
                 (cadr (caddr body))
               (cadr body)))
       (width (if implies-form?
                  (caddr (caddr body))
                (caddr body))))
    (if implies-form?
        `(defthm ,@thm
           :rule-classes ((:rewrite :corollary ,body)
                          (:type-prescription
                           :corollary
                           (implies ,(cadr body)
                                    (natp ,term)))
                          (:linear
                           :corollary
                           (implies ,(cadr body)
                                    (< ,term (expt 2 ,width))))))
      `(defthm ,@thm
         :rule-classes ((:rewrite :corollary ,body)
                        (:type-prescription :corollary (natp ,term))
                        (:linear :corollary (< ,term (expt 2 ,width))))))))

(defmacro bvecthm-nl (&rest thm)
  (declare (xargs :guard (and (true-listp thm)
                              (symbolp (car thm)))))
  (b* ((body (cadr thm))
       (implies-form? (equal (car body) 'implies))
       (term (if implies-form?
                 (cadr (caddr body))
               (cadr body)))
       (width (if implies-form?
                  (caddr (caddr body))
                (caddr body))))
    (if implies-form?
        `(defthm-nl ,@thm
           :rule-classes ((:rewrite :corollary ,body)
                          (:type-prescription
                           :corollary
                           (implies ,(cadr body)
                                    (natp ,term)))
                          (:linear
                           :corollary
                           (implies ,(cadr body)
                                    (< ,term (expt 2 ,width))))))
      `(defthm-nl ,@thm
         :rule-classes ((:rewrite :corollary ,body)
                        (:type-prescription :corollary (natp ,term))
                        (:linear :corollary (< ,term (expt 2 ,width))))))))

(defmacro bvecthm-nl++ (&rest thm)
  (declare (xargs :guard (and (true-listp thm)
                              (symbolp (car thm)))))
  (b* ((body (cadr thm))
       (implies-form? (equal (car body) 'implies))
       (term (if implies-form?
                 (cadr (caddr body))
               (cadr body)))
       (width (if implies-form?
                  (caddr (caddr body))
                (caddr body))))
    (if implies-form?
        `(defthm-nl++ ,@thm
           :rule-classes ((:rewrite :corollary ,body)
                          (:type-prescription
                           :corollary
                           (implies ,(cadr body)
                                    (natp ,term)))
                          (:linear
                           :corollary
                           (implies ,(cadr body)
                                    (< ,term (expt 2 ,width))))))
      `(defthm-nl++ ,@thm
         :rule-classes ((:rewrite :corollary ,body)
                        (:type-prescription :corollary (natp ,term))
                        (:linear :corollary (< ,term (expt 2 ,width))))))))

(defund strcat-for-expand-hints-nofree (l param newline)
  (declare (xargs :guard (and (symbol-listp l)
                              (stringp param)
                              (stringp newline))))
  (if (atom l)
      newline
    (concatenate 'string
                 newline "(" (symbol-name (car l)) " " param ")"
                 (strcat-for-expand-hints-nofree (cdr l) param newline))))

(defund strcat-for-expand-hints-free (l param free-str newline)
  (declare (xargs :guard (and (symbol-listp l)
                              (stringp param)
                              (stringp free-str)
                              (stringp newline))))
  (if (atom l)
      newline
    (concatenate
     'string
     newline "(:free " free-str
     " (" (symbol-name (car l)) " " param "))"
     (strcat-for-expand-hints-free (cdr l) param free-str newline))))

(defund strcat-for-expand-hints (l param free-str)
  (declare (xargs :guard (and (symbol-listp l)
                              (stringp param)
                              (stringp free-str))))
  (if (equal free-str "")
      (strcat-for-expand-hints-nofree l param (string '#\Newline))
    (strcat-for-expand-hints-free l param free-str (string '#\Newline))))
