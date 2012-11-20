#|$ACL2s-Preamble$;
(ld ;; Newline to fool ACL2/cert.pl dependency scanner
 "portcullis.lsp")
(acl2::begin-book t);$ACL2s-Preamble$|#

(in-package "ACL2")
(include-book "graph")

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
    ((eq ts-decoded '*TS-NON-POSITIVE-RATIONAL*) '(0 negative-rational))
    ((eq ts-decoded '*TS-NON-NEGATIVE-RATIONAL*) '(0 positive-rational))
    ((eq ts-decoded '*TS-NEGATIVE-RATIONAL* )    '(negative-rational) )
    ((eq ts-decoded '*TS-POSITIVE-RATIONAL* )    '(positive-rational) )
    ((eq ts-decoded '*TS-NON-NEGATIVE-INTEGER*)  '(0 pos)) 
    ((eq ts-decoded '*TS-NON-POSITIVE-INTEGER*)  '(0 neg)) 
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
(defun get-var-types-from-type-alist1 (acl2-type-alist freevars ans)
  (declare (xargs :mode :program
                  :guard (and (alistp acl2-type-alist)
                              (symbol-listp freevars))))
  (if (endp freevars)
      ans
    (b* ((var (car freevars))
         (ts-info (assoc-eq var acl2-type-alist))
         (ts (if (consp ts-info) (cadr ts-info) nil)))
     (if ts
         (let ((types (get-type-list-from-type-set ts)))
          (get-var-types-from-type-alist1 acl2-type-alist 
                                          (cdr freevars) 
                                          (acons var types ans)))
       (get-var-types-from-type-alist1 acl2-type-alist 
                                       (cdr freevars) ans)))))

(defun get-var-types-from-type-alist (acl2-type-alist freevars)
  (declare (xargs :mode :program
                  :guard (and (alistp acl2-type-alist)
                              (symbol-listp freevars))))
  (if (endp acl2-type-alist)
      '()
    (get-var-types-from-type-alist1 acl2-type-alist freevars '())))




;;; Foll fun lifted from intersection-of-types in type.lisp
;; NOTE: In the following the type 'empty' has
;; special status and treated seperately
(defun meet (typ1 typ2 wrld)
  (declare (xargs :verify-guards nil
                  :guard (and (symbolp typ1)
                              (symbolp typ2)
                              (plist-worldp wrld))))
  ;; (decl :sig ((possible-defdata-type-p possible-defdata-type-p
;;                                        plist-world)
;;               -> possible-defdata-type-p)
;;         :doc "naive implementation of meet operation of the lattice of
;; defdata types")
  (b* (((when (or (eq 'acl2::empty typ1)
                  (eq 'acl2::empty typ2))) 'acl2::empty)
       ((unless (and (defdata::is-a-typeName typ1 wrld)
                     (defdata::is-a-typeName typ2 wrld)))
        (er hard 'meet "~x0 or ~x1 is not a defdata type.~|" typ1 typ2))
       ((when (eq 'acl2::all typ1)) typ2)
       ((when (eq 'acl2::all typ2)) typ1)
       ((when (defdata::is-subtype typ1 typ2 wrld))   typ1)
       ((when (defdata::is-subtype typ2 typ1 wrld))   typ2)
       ((when (defdata::is-disjoint typ2 typ1 wrld))  'acl2::empty) ;Should we instead define the NULL type??? Modified: so Ans is YES instead of Ans: NO, the way its used now, this is right!
;give preference to custom type
       ((when (defdata::is-a-custom-type typ1 wrld)) typ1)
       ((when (defdata::is-a-custom-type typ2 wrld)) typ2)

; choose the one that was defined later (earlier in 
; reverse chronological order)
       (types-in-wrld (strip-cars (table-alist 
                                   'defdata::types-info-table wrld)))
       (pos1 (position typ1 types-in-wrld))
       (pos2 (position typ2 types-in-wrld)))
   (if (< (nfix pos1) (nfix pos2)) 
       typ1 
     typ2)));type table is already in reverse chrono order

(set-verify-guards-eagerness 0)

(verify-termination quote-listp)
(verify-termination cons-term1)
(verify-termination cons-term); ASK MATT to make these logic mode
(set-verify-guards-eagerness 1)
