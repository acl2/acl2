;; Functions used by both defsum and deftuple.

(in-package "ACL2")

(include-book "theory-tools")

(program)




;; A keyword alist is just an alist.
;; Look up the keyword in the alist; return default if it is not present.
(defun kwassoc (x default alist)
  (cond ((atom alist) default)
        ((eq x (caar alist)) (cdar alist))
        (t (kwassoc x default (cdr alist)))))




;; Keyword alists are constructed by separating each
;; keyword along with the argument following it from the rest of the input.
(defun strip-keywords (list)
  (if (atom list)
      ;; Return the input in case it is an atom; for situations where a single
      ;; symbol is acceptible instead of a list
      (mv list nil)
    (if (keywordp (car list))
        (mv-let (slist keyalist)
                (strip-keywords (cddr list))
                (mv slist (cons (cons (car list) (cadr list)) keyalist)))
      (mv-let (slist keyalist)
              (strip-keywords (cdr list))
              (mv (cons (car list) slist) keyalist)))))




(defun munge-components (components)
  (if (atom components)
      nil
    (cons ;; first component
     (mv-let (compo kwalist)
             (strip-keywords (car components))
             (if (consp compo)
                 (if (consp (cdr compo))
                     ;; type recognizer first, name second
                     (list* (cadr compo) (car compo) kwalist)
                   ;; no type recognizer
                   (list* (car compo) nil kwalist))
               ;; just an atom, presumably no keywords either
               (list* compo nil kwalist)))
     (munge-components (cdr components)))))

;; Utility functions for manipulating symbols.

;; Append symbols with dashes in between
(defun appsyms1 (symbols)
  (if (atom symbols)
      nil
    (if (atom (cdr symbols))
        symbols
      (list* (car symbols) '- (appsyms1 (cdr symbols))))))

(defun packsyms1 (lst)
  (cond ((null lst) "")
        (t (concatenate 'string (symbol-name (car lst))
                        (packsyms1 (cdr lst))))))

(defun packsyms (lst)
  (intern (packsyms1 lst) "ACL2"))

(defun appsyms (symbols)
  (packsyms (appsyms1 symbols)))





;; Each component within a product has a name as well as possibly a type; it
;; may have keywords as well.

(defun component-name (component)
  (car component))

(defun component-type (component)
  (cadr component))

(defun component-kwalist (component)
  (cddr component))




;; Each product has a name, a keyword list, and a list of components.
(defun product-name (product)
  (caar product))

(defun product-components (product)
  (cdar product))

(defun product-kwalist (product)
  (cdr product))



;; just the argument names, given the components of a product

(defun components-names (components)
  (if (atom components)
      nil
    (cons (component-name (car components))
          (components-names (cdr components)))))




(defun accessor-name (product component)
  (appsyms (list (product-name product) (component-name component))))

;; List of accessor names for a product
(defun accessor-list (product components)
  (if (consp components)
      (cons (accessor-name product (car components))
            (accessor-list product (cdr components)))
    nil))




(defun tm-split-list (half rest first)
  (if (zp half)
      (mv (reverse first) rest)
    (tm-split-list (1- half) (cdr rest) (cons (car rest) first))))


(defun argtree (cons args)
  (cond ((endp args)
         nil)
        ((endp (cdr args))
         (car args))
        (t (mv-let (first second)
             (tm-split-list (floor (len args) 2) args nil)
             `(,cons ,(argtree cons first)
                     ,(argtree cons second))))))



(defun recog-consp-list (nargs obj)
  (if (zp nargs)
      `((eq ,obj nil))
    (if  (= nargs 1)
        '(t)
      (let ((flo (floor nargs 2)))
        (cons `(consp ,obj)
              (append (recog-consp-list flo `(car ,obj))
                      (recog-consp-list (- nargs flo)
                                        `(cdr ,obj))))))))




(defun tree-accessor (n total nest opt)
  (if (zp total)
      nil
    (if (= 1 total)
        nest
      (let ((flo (floor total 2)))
        (if (<= n flo)
            (tree-accessor n flo `(,(if (eq opt :safe)
                                        'safe-car
                                      'car)
                                   ,nest)
                           opt)
          (tree-accessor (- n flo) (- total flo)
                         `(,(if (eq opt :safe)
                                'safe-cdr
                              'cdr)
                           ,nest)
                         opt))))))



(logic)

;; Theorems needed for proving theorems about defsum and deftuple
;; structures:
(defthmd nth-open
  (implies (not (zp n))
           (equal (nth n x)
                  (nth (1- n) (cdr x)))))

;; (defthmd safe-nth-open
;;   (implies (and (not (zp n))
;;                 (true-listp x))
;;            (equal (safe-nth n x)
;;                   (safe-nth (1- n) (cdr x))))
;;   :hints (("Goal" :in-theory (enable safe-nth))))

;; (defthmd cancel-+1
;;   (implies (and (syntaxp (quotep y))
;;                 (acl2-numberp y)
;;                 (acl2-numberp x))
;;            (equal (equal (+ 1 x) y)
;;                   (equal x (+ -1 y)))))

;; (defthmd cancel-+k
;;   (implies (and (syntaxp (quotep y))
;;                 (syntaxp (quotep k))
;;                 (acl2-numberp k)
;;                 (acl2-numberp y)
;;                 (acl2-numberp x))
;;            (equal (equal (+ k x) y)
;;                   (equal x (+ (- k) y)))))

(defthmd true-listp-len-0
  (implies (true-listp x)
           (equal (equal (len x) 0)
                  (not x))))

(defthmd acl2-count-car-cdr-of-cons-linear
  (implies (consp x)
           (and (< (acl2-count (car x)) (acl2-count x))
                (< (acl2-count (cdr x)) (acl2-count x))))
  :rule-classes :linear)

(defthmd acl2-count-nth-of-cons-linear
  (implies (consp x)
           (< (acl2-count (nth n x))
              (acl2-count x)))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :induct (nth n x))))

(defthmd acl2-count-0-len-0
  (implies (equal (acl2-count x) 0)
           (< (len x) 1))
  :rule-classes :linear)

(defthmd acl2-count-nth-of-len-2-or-greater-linear
  (and (implies (consp x)
                (<= (+ 1 (acl2-count (nth n x)))
                    (acl2-count x)))
       (implies (<= 2 (len x))
                (< (+ 1 (acl2-count (nth n x)))
                   (acl2-count x))))
  :hints (("Goal" :induct (nth n x)
           :in-theory (enable acl2-count-0-len-0)))
  :rule-classes (:rewrite :linear))

(defthmd len-0-true-listp-not-x
  (implies (and x (true-listp x))
           (not (equal (len x) 0))))
