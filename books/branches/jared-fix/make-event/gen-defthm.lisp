; This file shows how the expansion phase can modify state to generate events.
; The macro defthm! below is similar to the macro defthm? from the distributed
; book misc/expander.  But defthm? modifies state in a way that cannot be done
; in a certifiable book, because it relies on other than embedded event forms.
; Defthm!, on the other hand, calls defthm? during expansion to generate an
; event as the expansion result, which is then evaluated.  This is a bit
; inefficient since the same theorems are in essence proved twice, but it is
; sound: we revert the world and most of the state after expansion, record the
; expansion, and then treat the defthm! call as though it were the expansion --
; which is a legal embedded event form.

(in-package "ACL2")

(include-book "misc/expander" :dir :system)

(defmacro defthm! (&whole ev
                          &rest args)
  `(make-event (defthm? ,@args)
               :on-behalf-of ,ev))

(defthm! app-simplify
  (implies (true-listp x)
           (equal (append x y)
                  ?))
  :hints (("Goal" :expand ((true-listp x)
                           (true-listp (cdr x))
                           (append x y))))
; show some output
  :print-flg t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; The rest of this file just checks that the defthm! above generated the ;
; expected events.                                                       ;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(set-enforce-redundancy t)

(DEFTHM
  APP-SIMPLIFY$0
  (IMPLIES (AND (CONSP X) (NOT (CDR X)))
           (EQUAL (APPEND X Y) (CONS (CAR X) Y)))
#|
  :HINTS
  (("Goal"
    :EXPAND ((TRUE-LISTP X)
             (TRUE-LISTP (CDR X))
             (APPEND X Y))
    :IN-THEORY
    (UNION-THEORIES
     (DEFINITION-RUNES
       (UNION-EQ '(IFF)
                 *EXPANDABLE-BOOT-STRAP-NON-REC-FNS*)
       T WORLD)
     '((:DEFINITION TRUE-LISTP)
       (:DEFINITION BINARY-APPEND)
       (:EXECUTABLE-COUNTERPART CONSP)))))
|# ; |
  )

(DEFTHM
  APP-SIMPLIFY$1
  (IMPLIES (AND (CONSP X)
                (CONSP (CDR X))
                (TRUE-LISTP (CDDR X)))
           (EQUAL (APPEND X Y)
                  (CONS (CAR X) (APPEND (CDR X) Y))))
#|
  :HINTS
  (("Goal"
    :EXPAND ((TRUE-LISTP X)
             (TRUE-LISTP (CDR X))
             (APPEND X Y))
    :IN-THEORY
    (UNION-THEORIES
     (DEFINITION-RUNES
       (UNION-EQ '(IFF)
                 *EXPANDABLE-BOOT-STRAP-NON-REC-FNS*)
       T WORLD)
     '((:DEFINITION TRUE-LISTP)
       (:EXECUTABLE-COUNTERPART CONSP)
       (:DEFINITION BINARY-APPEND)))))
|# ; |
  )

(DEFTHM
  APP-SIMPLIFY$2
  (IMPLIES (NOT X) (EQUAL (APPEND X Y) Y))
#|
  :HINTS
  (("Goal"
    :EXPAND ((TRUE-LISTP X)
             (TRUE-LISTP (CDR X))
             (APPEND X Y))
    :IN-THEORY
    (UNION-THEORIES
     (DEFINITION-RUNES
       (UNION-EQ '(IFF)
                 *EXPANDABLE-BOOT-STRAP-NON-REC-FNS*)
       T WORLD)
     '((:DEFINITION TRUE-LISTP)
       (:EXECUTABLE-COUNTERPART CONSP)
       (:DEFINITION BINARY-APPEND)))))
|# ; |
  )
