; A double-rewrite example based on events from Dave Greve.

(in-package "ACL2")

(encapsulate
 ((keys (res) t)
  (key-equal (x y) t)
  (pointers (x y) t)
  (foo (list args res st) t))

 (set-ignore-ok t)
 (set-irrelevant-formals-ok t)
 (local (defun keys (res) nil))
 (local (defun pointers (x y) nil))
 (local (defun key-equal (x y)
          (equal (keys x) (keys y))))
 (local (defun foo (list args res st) t))

 (defequiv key-equal)
 (defthm pointers-trace-key-equiv
   (key-equal (pointers mlist res) res)) ; Double-rewrite warning for res on rhs
 (defthm foo_res_equiv-original
   (implies (and (foo list args res1 st)
                 (syntaxp (not (cw "Hi ~x0 ~x1" res1 res2))) ; optional
                 (key-equal res1 res2)) ; Double-rewrite warnings for res1, res2
            (foo list args res2 st))))

; The following fails.  However, note that we get a Double-rewrite warning when
; foo_res_equiv-original is submitted.  The warning actually warns about both
; res1 and res2 in the third hypothesis of foo_res_equiv-original, but it will
; suffice to fix res1.  By the way, note that there is no binding occurrence of
; res1 as defined in the paper and the code: the binding of free variable res1
; in the first hypothesis is not considered a binding occurrence, because we
; have no idea which equivalence relations were being maintained when this
; value of res1 was rewritten earlier.

; (defthm foo_over_record_keeper-pointers_2
;   (implies (foo list args (pointers mlist res) st)
;            (foo list args res st)))

(defthm foo_res_equiv
  (implies (and (foo list args res1 st)
                (syntaxp (not (cw "Hi ~x0 ~x1" res1 res2))) ; optional
; Double-rewrite warning for third hyp is now for res2 only.
                (key-equal (double-rewrite res1) res2))
           (foo list args res2 st)))

(in-theory (disable foo_res_equiv-original))

(defthm foo_over_record_keeper-pointers_2
  (implies (foo list args (pointers mlist res) st)
           (foo list args res st)))
