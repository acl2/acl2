#|$ACL2s-Preamble$;
(acl2::begin-book t);$ACL2s-Preamble$|#

(in-package "ACL2")
(include-book "tools/bstar" :dir :system)

;;; For use by testing hints
;;; Get the type information from the ACL2 type alist
(mutual-recursion
 (defun get-type-from-type-set-decoded (ts-decoded)
   ;(declare (xargs :guard (symbolp ts-decoded)))
   (cond   ;primitve types
    ((eq ts-decoded '*TS-ZERO*)                  '(0) )
    ((eq ts-decoded '*TS-POSITIVE-INTEGER*)      '(pos) )     ;;; positive integers
    ((eq ts-decoded '*TS-POSITIVE-RATIO*)        '(positive-ratio) )     ;;; positive non-integer rationals
    ((eq ts-decoded '*TS-NEGATIVE-INTEGER*)      '(neg) ) ;;; negative integers
    ((eq ts-decoded '*TS-NEGATIVE-RATIO*)        '(negative-ratio) ) ;;; negative non-integer rationals
    ((eq ts-decoded '*TS-COMPLEX-RATIONAL*)      '(complex-rational) );;; complex rationals
    ((eq ts-decoded '*TS-NIL*)                   '('nil) );;; {nil}
    ((eq ts-decoded '*TS-T*)                     '('t) );;; {t}
    ((eq ts-decoded '*TS-NON-T-NON-NIL-SYMBOL*)  '(symbol) );;; symbols other than nil, t
    ((eq ts-decoded '*TS-PROPER-CONS*)           '(proper-cons) );;; null-terminated non-empty lists
    ((eq ts-decoded '*TS-IMPROPER-CONS*)         '(improper-cons) );;; conses that are not proper
    ((eq ts-decoded '*TS-STRING*)                '(string) );;; strings
    ((eq ts-decoded '*TS-CHARACTER*)             '(character) );;; characters
    
;non-primitive types but defined in ground acl2 theory and base.lisp
    ((eq ts-decoded '*TS-UNKNOWN*)               '(all) );should give out error?
    ((eq ts-decoded '*TS-NON-NIL* )              '(all) )
    ((eq ts-decoded '*TS-ACL2-NUMBER*)           '(acl2-number) )
    ((eq ts-decoded '*TS-RATIONAL-ACL2-NUMBER*)  '(acl2-number) )
    ((eq ts-decoded '*TS-RATIONAL* )             '(rational) )
    ((eq ts-decoded '*TS-TRUE-LIST-OR-STRING*)   '(true-list string)) 
    ((eq ts-decoded '*TS-SYMBOL*   )             '(symbol) )
    ((eq ts-decoded '*TS-INTEGER*   )            '(integer) )
    ((eq ts-decoded '*TS-NON-POSITIVE-RATIONAL*) '(negative-rational 0))
    ((eq ts-decoded '*TS-NON-NEGATIVE-RATIONAL*) '(positive-rational 0))
    ((eq ts-decoded '*TS-NEGATIVE-RATIONAL* )    '(negative-rational) )
    ((eq ts-decoded '*TS-POSITIVE-RATIONAL* )    '(positive-rational) )
    ((eq ts-decoded '*TS-NON-NEGATIVE-INTEGER*)  '(nat));(0 pos)) 
    ((eq ts-decoded '*TS-NON-POSITIVE-INTEGER*)  '(neg 0)) 
    ((eq ts-decoded '*TS-RATIO*)                 '(ratio) )
    ((eq ts-decoded '*TS-CONS*  )                '(cons) )
    ((eq ts-decoded '*TS-BOOLEAN*)               '(boolean) )
    ((eq ts-decoded '*TS-TRUE-LIST*)             '(true-list) )
    
    ((eq ts-decoded '*TS-EMPTY*)                 '(empty));is it possible?
    (t  (if (consp ts-decoded)
            (cond 
             ((equal 'TS-UNION (car ts-decoded))
              (get-types-from-type-set-decoded-lst (cdr ts-decoded) nil))
             ((and (equal 'TS-COMPLEMENT (car ts-decoded))
                   (equal (cadr ts-decoded) '*TS-CONS*))
              '(atom))
             (t '(all)))
          '(all)))))
 
(defun get-types-from-type-set-decoded-lst (ts-lst ans)
   (if (endp ts-lst)
     ans
     (get-types-from-type-set-decoded-lst 
      (cdr ts-lst) 
      (append (get-type-from-type-set-decoded (car ts-lst))
              ans))))
 )

(defun get-type-list-from-type-set (ts)
  (declare (xargs :mode :program
                  :guard (integerp ts)))
  (let ((typ (get-type-from-type-set-decoded 
              (acl2::decode-type-set ts))))
    (if (proper-consp typ)
      typ
      (list typ))))

(defun get-types-from-type-set-lst (ts-lst)
  (declare (xargs :mode :program 
                  :guard (integer-listp ts-lst)))
  (if (endp ts-lst)
    nil
    (append (get-type-list-from-type-set (car ts-lst))
            (get-types-from-type-set-lst (cdr ts-lst)))))



; for each var in freevars, look into the type-alist
; and build a no-dup vt-al(var-types-alist)
; Note: we can get a list of types which means TS-UNION
(defun get-var-types-from-type-alist (acl2-type-alist freevars ans)
  (declare (xargs :mode :program
                  :guard (and (alistp acl2-type-alist)
                              (symbol-listp freevars))))
  (if (endp freevars)
      ans
    (b* ((var (car freevars))
; CHECK: Can acl2-type-alist have duplicate keys?
         (ts-info (assoc-eq var acl2-type-alist))
         (ts (if (consp ts-info) (cadr ts-info) nil)))
     (if ts
         (let ((types (get-type-list-from-type-set ts)))
          (get-var-types-from-type-alist acl2-type-alist 
                                          (cdr freevars) 
                                          (acons var types ans)))
       (get-var-types-from-type-alist acl2-type-alist 
                                       (cdr freevars) ans)))))

(defun decode-acl2-type-alist (acl2-type-alist freevars)
  (declare (xargs :mode :program
                  :guard (and (alistp acl2-type-alist)
                              (symbol-listp freevars))))
  (if (endp acl2-type-alist)
      '()
    (get-var-types-from-type-alist acl2-type-alist freevars '())))



(set-verify-guards-eagerness 0)

(verify-termination acl2::quote-listp)
(verify-termination acl2::cons-term1)
(verify-termination acl2::cons-term); ASK MATT to make these logic mode
(set-verify-guards-eagerness 1)
