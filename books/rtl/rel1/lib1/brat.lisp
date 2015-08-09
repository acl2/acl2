; This file was created by J Moore and Matt Kaufmann in 1995 in support of
; their proof of the AMD-K5 division code.

(in-package "ACL2")

; In 1995 the following include-book was not local, but now it is so that
; we can safely include brat in top.
(local (include-book "../support/fp"))

; Since the above include-book is local, we need the following here.
(defun fl (x) (floor x 1))

; We say a rational p/q is a "binary rational" if q is a power of 2.
; A pair (n . i) consisting of two integers is called a "binary pair"
; and represents the binary rational n/2**i.

; We implement rather elaborate notational conventions to use in the
; output of test routines.

; We can represent a binary rational as a rational, a string, or a
; symbol, as illustrated below.  The fn listed on the right has the
; property that when given a legal object of any one of these three
; types it produces the equivalent object of the type indicated by the
; function's name.

; 209/16          rationalp   BRAT
; "B1101.0001"    stringp     BSTR
; "b1101.0001"    stringp
; B1101.0001      symbolp     BSYM

; In addition, negatives may be written in the more or less obvious ways:
;-209/16          rationalp   BRAT
;"-B1101.0001"    stringp     BSTR
;"-b1101.0001"    stringp
;-B1101.0001      symbolp     BSYM

; For example, given a rational, string or symbol, x, representing a
; binary rational, (BRAT x) will produce the equivalent rational,
; (BSTR x) will produce the equivalent string, and (BSYM x) will
; produce the equivalent symbol.

(defun log2 (x)
  (if (< (nfix x) 2) 0 (1+ (log2 (fl (/ x 2))))))

(defun binary-stringp (i str max pointp)
  (declare (xargs :mode :program))
  (cond ((>= i max) (> max 0))
        ((eq (char str i) #\.)
         (if pointp nil (binary-stringp (1+ i) str max t)))
        ((or (eq (char str i) #\1)
             (eq (char str i) #\0))
         (binary-stringp (1+ i) str max pointp))
        (t nil)))

(defun chk-binary (x)
  (declare (xargs :mode :program))
  (cond ((or (symbolp x)
             (stringp x))
         (let* ((str (if (stringp x) x (symbol-name x)))
                (max (length str)))
           (cond ((and (> max 2)
                       (or (eql (char str 0) #\B)
                           (eql (char str 0) #\b)
                           (and (or (eql (char str 0) #\-)
                                    (eql (char str 0) #\+))
                                (or (eql (char str 1) #\B)
                                    (eql (char str 1) #\b)))
                           (binary-stringp
                            (if (or (eql (char str 0) #\-)
                                    (eql (char str 0) #\+))
                                2 1)
                            str max nil)))
                  t)
                 (t (illegal 'binary-conversion
                             "Illegal or unrecognized binary syntax, ~p0."
                             (list (cons #\0 x)))))))
        ((and (rationalp x)
              (= (denominator x) (expt 2 (log2 (denominator x)))))
         t)
        (t (illegal 'binary-conversion
                    "Illegal or unrecognized binary syntax, ~p0."
                    (list (cons #\0 x))))))

(defun binary-string-to-rat (i str max p ans)
  (declare (xargs :mode :program))
  (cond ((>= i max) ans)
        ((eq (char str i) #\0)
         (if (null p)
             (binary-string-to-rat (1+ i) str max nil (* 2 ans))
           (binary-string-to-rat (1+ i) str max (/ p 2) ans)))
        ((eq (char str i) #\1)
         (if (null p)
             (binary-string-to-rat (1+ i) str max nil (1+ (* 2 ans)))
           (binary-string-to-rat (1+ i) str max (/ p 2) (+ ans p))))
        (t ;;; (eq (char str i) #\.) and (null p)
         (binary-string-to-rat (1+ i) str max 1/2 ans))))

(defun string-or-symbol-to-rat (x)
; We assume (chk-binary x) = t and x is a stringp or symbolp
  (declare (xargs :mode :program))
  (let* ((str (if (stringp x) x (symbol-name x)))
         (max (length str)))
    (cond ((eql (char str 0) #\-)
           (- (binary-string-to-rat 2 str max nil 0)))
          ((eql (char str 0) #\+)
           (binary-string-to-rat 2 str max nil 0))
          (t (binary-string-to-rat 1 str max nil 0)))))

(defun brat (x)
  (declare (xargs :mode :program))
  (cond ((and (chk-binary x)
              (or (symbolp x)
                  (stringp x)))
         (string-or-symbol-to-rat x))
        (t x)))

(defun nat-to-binary-charlist (x lst)
  (declare (xargs :mode :program))
  (cond ((= x 0) lst)
        (t (nat-to-binary-charlist (floor x 2)
                                   (cons (if (= (mod x 2) 1) #\1 #\0) lst)))))

(defun rat-to-str2 (lst place e)
  (declare (xargs :mode :program))
  (cond ((= place e) (cons #\. lst))
        ((null lst)
         (cons #\0 (rat-to-str2 nil (1+ place) e)))
        (t (cons (car lst) (rat-to-str2 (cdr lst) (1+ place) e)))))

(defun rat-to-str1 (m e)
  (declare (xargs :mode :program))
  (let* ((lst (nat-to-binary-charlist m nil))
         (place (- (length lst))))
    (cond ((< e place)
           (cons #\. (make-list-ac (- place e) #\0 lst)))
          (t (rat-to-str2 lst place e)))))

(defun bstr (x)
  (declare (xargs :mode :program))
  (let* ((rat (brat x))
         (abs-rat (abs rat))
         (sgn-rat (if (< rat 0) -1 +1)))
    (coerce
     (append (if (= sgn-rat -1) '(#\-) '(#\Space))
             (cons #\B
                   (let ((lst (rat-to-str1 (numerator abs-rat)
                                           (- (log2 (denominator abs-rat))))))
                     (if (eql (car lst) #\.) (cons #\0 lst) lst))))
     'string)))

(defun bsym (x)
  (declare (xargs :mode :program))
  (intern (bstr x) "ACL2"))

