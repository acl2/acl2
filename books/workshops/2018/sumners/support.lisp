(in-package "ACL2")
(include-book "std/util/define" :dir :system)
(include-book "std/util/defconsts" :dir :system)
(include-book "std/util/defval" :dir :system)
(include-book "std/util/bstar" :dir :system)
(include-book "centaur/sv/svex/svex" :dir :system)
(include-book "misc/total-order" :dir :system)
(include-book "std/strings/strprefixp" :dir :system)

(define append$! (x y)
  (if (atom x) y (cons (first x) (append$! (rest x) y))))

(defmacro append! (&rest x)
  (cond ((atom x) ()) ((atom (rest x)) (first x))
        (t `(append$! ,(first x) (append! ,@(rest x))))))

;(define in! (e x)
;  (and (consp x)
;       (or (equal e (first x))
;           (in! e (rest x)))))

(define look! (e x)
  (and (consp x)
       (consp (car x))
       (if (equal e (caar x)) (cdar x)
         (look! e (cdr x)))))

(define rev$! (x r)
  (if (atom x) r (rev$! (rest x) (cons (first x) r))))

(defmacro rev! (x) `(rev$! ,x ()))

(define first-last! (x)
  (cond ((atom x) ())
        ((atom (rest x)) (first x))
        (t (first-last! (rest x)))))

(define allbut-last! (x)
  (cond ((atom x) ())
        ((atom (rest x)) ())
        (t (cons (first x) (allbut-last! (rest x))))))

(define assoc! (e x)
  (and (consp x)
       (consp (car x))
       (or (and (hons-equal-lite e (caar x))
                (car x))
           (assoc! e (cdr x)))))

(define in! (e x)
  (and (consp x)
       (or (hons-equal-lite e (first x))
           (in! e (rest x)))))

(define add! (e x)
  (if (in! e x) x (cons e x)))

(define unite!* (x y)
  (if (atom x) y (unite!* (rest x) (add! (first x) y))))

(define unite! (x y)
  (if (atom y) x (unite!* x y)))

(define sdiff! (x y)
  (if (atom x) () (if (in! (first x) y) (sdiff! (rest x) y)
                    (cons (first x) (sdiff! (rest x) y)))))

(define isect! (x y)
  (if (atom x) () (if (not (in! (first x) y)) (isect! (rest x) y)
                    (cons (first x) (isect! (rest x) y)))))

(define g^ (k x)
  ;; a version of g where we expect to match (throw an error if not)
  ;; and use hons-equal-lite for equality checking:
  (cond ((atom x)
         (raise "Did not find entry to match in g^:~x0~%" (list k x)))
        ((not (consp (car x)))
         (raise "Ill-formed non-alist given to g^:~x0~%" (list k x)))
        ((hons-equal-lite k (caar x))
         (cdar x))
        (t (g^ k (cdr x)))))

(define s^ (k v x)
  ;; a version of s where we do normalize the order of the keys in 
  ;; building the alist to get "equal" structures, but do not normalize
  ;; on default values -- since we want them to work better for symbolic
  ;; simulation generating AIGs.. also use hons-equal-lite for slight 
  ;; speedup but unlikely to matter (<< check will dominate):
  (cond ((atom x) (cons (cons k v) x))
        ((not (consp (car x)))
         (raise "Ill-formed non-alist given to s^:~x0~%" (list k v x)))
        ((hons-equal-lite k (caar x))
         (cons (cons k v) (cdr x)))
        ((<< k (caar x))
         (cons (cons k v) x))
        (t (cons (car x) (s^ k v (cdr x))))))

(define rip (flds x)
  (if (atom flds) ()
    (b* ((f (first flds)))
      (s^ f (g^ f x) (rip (rest flds) x)))))

;;;; BACK to normal stuff.. defining snap macro..

(define dig-to-str (n)
  (case n (0 "0") (1 "1") (2 "2") (3 "3") (4 "4")
          (5 "5") (6 "6") (7 "7") (8 "8") (t "9")))

(local (include-book "arithmetic-5/top" :dir :system))

(defthm nat-floor-strictly-less
  (implies (and (natp x) (natp y) (> y 1) (>= x y))
           (< (floor x y) x)))

(in-theory (disable floor))

(define my-standard-string-p ((x stringp))
  (standard-char-listp (coerce x 'list)))

(define num-to-str (n)
  :measure (nfix n)
  (cond ((not (natp n))
         (prog2$ (raise "illegal value:~x0~%" n)
                 ""))
        ((< n 10) (dig-to-str n))
        (t (string-append (num-to-str (floor n 10))
                          (dig-to-str (mod n 10))))))

(define char-to-dig ((c characterp))
  (let ((n (char-code c)))
    (if (and (>= n (char-code #\0))
             (<= n (char-code #\9)))
        (- n (char-code #\0))
      0)))

(define stap (x flg)
  :guard-hints (("Goal" :in-theory (enable my-standard-string-p str-fix)))
  (cond ((null x)       "") ;; we treat nil specially as empty string since it ends lists..
        ((stringp x)    (if flg x
                          (if (my-standard-string-p x) (string-upcase x)
                            (prog2$ (raise "encountered non-standard string:~x0~%" x)
                                    ""))))
        ((symbolp x)    (symbol-name x)) ;; we just drop package..
        ((integerp x)   (if (< x 0) (string-append "-" (num-to-str (- x))) (num-to-str x)))
        ((characterp x) (coerce (list x) 'string))
        ((consp x)      (string-append (str-fix (stap (car x) flg))
                                       (str-fix (stap (cdr x) flg))))
        (t "")))

(defmacro strap  (&rest lst) `(stap (list ,@lst) nil))
(defmacro strap! (&rest lst) `(stap (list ,@lst) t))
(defmacro snap   (&rest lst) `(intern (strap  ,@lst) "ACL2"))
(defmacro snap!  (&rest lst) `(intern (strap! ,@lst) "ACL2"))

(define my-app (x y) (if (atom x) y (cons (first x) (my-app (rest x) y))))

(define mk-dfc-consts (vars)
  (cond ((null vars) ())
        ((symbolp vars) (list (snap '* vars '*)))
        ((atom vars) (raise "illegal obj:~x0~%" vars))
        (t (cons (snap '* (first vars) '*) (mk-dfc-consts (rest vars))))))

(define mk-dfc-form1 (var typ-p)
  `((define ,var () ,(snap '* var '*))
    (defthm ,(snap var '-is- typ-p) (,typ-p (,var)))
    (in-theory (disable (,var)))))

(define mk-dfc-forms (vars typs-p)
  (cond ((null vars) ())
        ((symbolp vars) (mk-dfc-form1 vars typs-p))
        ((or (atom vars) (atom typs-p))
         (raise "illegal objs:~x0~%" (list vars typs-p)))
        (t (my-app (mk-dfc-form1 (first vars) (first typs-p))
                   (mk-dfc-forms (rest vars) (rest typs-p))))))

(defmacro dfc (vars typs-p form) 
  `(progn (defconsts ,(mk-dfc-consts vars) (cwtime ,form :mintime 0))
          ,@(mk-dfc-forms vars typs-p)))

(defmacro mfal (&rest x) `(make-fast-alist (list ,@x)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;
;;;; some simple hons= based set operations
;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defabbrev acons! (a b x) (cons (cons a b) x))
(defabbrev hons=  (x y)   (hons-equal-lite x y))

(define in-hons= (e x)
  (and (consp x) (or (hons= e (first x)) (in-hons= e (rest x)))))

(define set-diff-hons= (x y &key (r 'nil))
  (if (atom x) r
    (b* ((e (first x)))
      (set-diff-hons= (rest x) y
                      :r (if (in-hons= e y) r (cons e r))))))

(define set-union-hons= (x y) (set-diff-hons= x y :r y))
(in-theory (enable set-union-hons=))

(defthm svarlist-set-diff-hons=
  (implies (and (sv::svarlist-p x) (sv::svarlist-p r))
           (sv::svarlist-p (set-diff-hons= x y :r r)))
  :hints (("Goal" :in-theory (enable set-diff-hons=))))

;;;;;;;;;;;;;;;;;
;; and finally.. junk theorems that we wish we didn't need..
;; and would like to remove..
;;;;;;;;;;;;;;;;;

(defthm junk1 (implies (natp x) (rationalp x)))
(defthm junk2 (implies (natp x) (acl2-numberp x)))

