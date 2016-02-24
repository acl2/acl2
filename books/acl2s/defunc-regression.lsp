; ****************** BEGIN INITIALIZATION FOR ACL2s MODE ****************** ;
; (Nothing to see here!  Your actual file is after this initialization code);

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading the CCG book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "ccg/ccg" :uncertified-okp nil :dir :acl2s-modes :ttags ((:ccg)) :load-compiled-file nil);v4.0 change

;Common base theory for all modes.
#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s base theory book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "base-theory" :dir :acl2s-modes)


#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s customizations book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "custom" :dir :acl2s-modes :uncertified-okp nil :ttags :all)

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem setting up ACL2s mode.") (value :invisible))

;Settings common to all ACL2s modes
(acl2s-common-settings)
;(acl2::xdoc acl2s::defunc) ;; 3 seconds is too much time to spare -- commenting out [2015-02-01 Sun]

; Non-events:
;(set-guard-checking :none)

(acl2::in-package "ACL2S")

; ******************* END INITIALIZATION FOR ACL2s MODE ******************* ;
;$ACL2s-SMode$;ACL2s

(acl2::include-book "misc/eval" :dir :system)#|ACL2s-ToDo-Line|#


(defunc llen (l)
  :input-contract (consp l)
  :output-contract (natp (llen l))
  (+ 1 (llen (rest l)))
  :debug t)


;does not go through in beginner mode.

(defunc f (x y)
  :input-contract (and (integerp x) (posp y))
  :output-contract t
  (if (> x y)
      y
      (f (+ x y) y))
  :debug t)

(defunc seq (i)
  :input-contract (natp i)
  :output-contract (and (natp (seq i))
                              (>= (seq i) 1003))
  (if (equal i 0)
    1003
    (- (* (seq (- i 1)) 10) 17)))


; in beg mode change true-listp to listp
(defunc how-many-t (e l acc)
  :input-contract (and (true-listp l) (natp acc))
  :output-contract (natp (how-many-t e l acc))
  (cond ((endp l) acc)
        ((equal e (first l)) (how-many-t e (rest l) (+ 1 acc)))
        (t (how-many-t e (rest l) acc))))

:program

(acl2::must-fail
 ;todo -- improve error message
(defunc how-many-t (e l acc)
  :input-contract (and (true-listp l) (natp acc))
  :output-contract (natp (how-many-t e l acc))
  (cond ((endp l) acc)
        ((equal e (first l)) (how-many-t e (rest l) (+ 1 acc)))
        (t (how-many-t e (rest l) acc)))
  :skip-tests t)
)



(defunc g-c (n count limit)
  :input-contract (and (integerp n) (natp count) (natp limit))
  :output-contract (or (natp (g-c n count limit))
                       (equal '! (g-c n count limit)))
  (cond
   ((or (not (natp n)) (equal count limit)) '!)
   ((equal n 0) count)
   (t (g-c (- n 1) (+ 1 count) limit))))

:logic

(defdata rationallist (listof rational))

:program
(defunc swap (i l)
  :input-contract (and (natp i)
                       (rationallistp l)
                       (>= (len l) 2))
  :output-contract (rationallistp (swap i l))
  (if (equal i 0) (rest l) l))

:logic

(defdata probability (range rational (0 <= _ <= 1)))

; ev is a constructor that creates a record with three fields:
(defdata event (oneof (ev (prob . probability) (event1 . event) (event2 . event))
                      rational))

(defun ev-count (e)
  (if (not (evp e))
    0
    (+ 1 (ev-count (ev-event1 e)) (ev-count (ev-event2 e)))))
  
(in-theory (disable ev ev-prob ev-event1 ev-event2))
(defthm ev-count-decreases 
 (implies (and (evp e)
               (evp (EV-EVENT1 E)))
          (< (EV-COUNT (EV (EV-PROB E) (EV-EVENT2 (EV-EVENT1 E)) (EV-EVENT2 E)))
             (EV-COUNT E)))
 :rule-classes :linear)

;TODO fix this failure
#|
(defunc flatten-event (e)
  :input-contract (eventp e)
  :output-contract (eventp (flatten-event e))
  :function-contract-hints (("Goal" :in-theory (enable ev ev-prob ev-event1 ev-event2)))
  (declare (xargs :consider-only-ccms ((ev-count e))))
                  ;:hints (("Goal" :in-theory (disable ev ev-prob ev-event1 ev-event2)))))
  
  (if (not (evp e))
    e
    (if (not (evp (ev-event1 e)))
      (ev (ev-prob e) (ev-event1 e) (flatten-event (ev-event2 e)))
      (ev (* (ev-prob e) (ev-prob (ev-event1 e)))
          (ev-event1 (ev-event1 e))
          (flatten-event (ev (ev-prob e)
                             (ev-event2 (ev-event1 e))
                             (ev-event2 e)))))))
|#


;from acl2s-issues.lisp
(defunc append-before-each-member (k l)
  :input-contract t
  :output-contract (alistp (append-before-each-member k l))
  (if (not (consp l))
    (if l
      (list (list k l))
      nil)
    (append (list (list k (car l))) (append-before-each-member k (cdr l)))))

(defunc append-after-each-member (l k)
  :input-contract t
  :output-contract (alistp (append-after-each-member l k))
  (if (not (consp l))
    (if l
      (list (list l k))
      nil)
    (append (list (list (car l) k)) (append-after-each-member (cdr l) k))))

(defunc cartesian-product (la lb)
  :input-contract t
  :output-contract (alistp (cartesian-product la lb))
  (if (not (consp la))
    (if la
      (append-before-each-member la lb)
      nil)
    (if (not (consp lb))
      (append-after-each-member la lb)
      (append (append-before-each-member (car la) lb)
              (cartesian-product (cdr la) lb)))))




(defunc app (x y)
  :input-contract (and (true-listp x) (true-listp y))
  :output-contract (true-listp (app x y))
  (append x y))

(defunc head (x)
  :input-contract (and (true-listp x) (consp x))
  :output-contract t
  (car x))

(defunc tail (x)
  :input-contract (and (true-listp x) (consp x))
  :output-contract (true-listp (tail x))
  (cdr x))


(acl2s-defaults :set num-trials 125)


(acl2s-defaults :get cgen-timeout)
(acl2s-defaults :set cgen-timeout 60)

(set-ignore-ok t)
(set-irrelevant-formals-ok t)


(acl2::must-fail
(defunc Rotate-buffer-left (l n)
  :input-contract (and (true-listp l) (natp n))
  :output-contract t
  (cond ((equal n 0) l)
        (t (Rotate-buffer-left (app (tail l) (head l))
                               (- n 1)))))
)

(acl2::must-fail
(defunc Rotate-buffer-left (l n)
  :input-contract (and (true-listp l) (natp n))
  :output-contract (and (true-listp (Rotate-buffer-left l n))
                        (equal (len (Rotate-buffer-left l n)) (len l)))
  (cond ((equal n 0) l)
        (t (Rotate-buffer-left (app (tail l) (head l))
                               (- n 1)))))
)

(acl2::must-fail
(defunc Rotate-buffer-left (l n)
  :input-contract (and (true-listp l) (natp n))
  :output-contract (and (true-listp (Rotate-buffer-left l n))
                        (equal (len (Rotate-buffer-left l n)) (len l)))
  (cond ((equal n 0) l)
        (t (Rotate-buffer-left (app (tail l) (list (head l)))
                               (- n 1)))))
)

(defunc Rotate-buffer-left (l n)
  :input-contract (and (true-listp l) (natp n))
  :output-contract (and (true-listp (Rotate-buffer-left l n))
                        (equal (len (Rotate-buffer-left l n)) (len l)))
  (cond ((equal n 0) l)
        ((endp l) nil)
        (t (Rotate-buffer-left (app (tail l) (list (head l)))
                               (- n 1)))))

