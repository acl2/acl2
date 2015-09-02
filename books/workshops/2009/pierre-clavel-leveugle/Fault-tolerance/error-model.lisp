
; Error model (section 4.1)
; -------------------------

(IN-PACKAGE "ACL2")
(include-book "arithmetic-3/top" :dir :system)
(include-book "make-event/defspec" :dir :system)

; additional lemma
(defthm thm-natp-add-type
  (implies (and (natp n) (natp m))
           (natp (+ n m))))

; definition of an error in a register of type natp
; -------------------------------------------------

(encapsulate
;  - Signature
  (((STD-natp-error *) => *))
;  - Witness
  (local (defun STD-natp-error (x)
           (if (natp x)
               (1+ x)
               "error")))
; - Properties
  (defthm STD-natp-type1    ; returns a natp
    (implies (natp x)
             (natp (STD-natp-error x))))

  (defthm STD-natp-type2    ; takes a natp
    (implies (not (natp x))
             (equal (STD-natp-error x)
                    "error")))

  (defthm STD-natp-def      ; fault-injection is actual
    (implies (natp x)
             (not (equal (STD-natp-error x)
                         x))))

  ; the third property (only one memorizing element differs)
  ; is explicitly expressed in each component
)

; Note: similar definitions can be given for other types of
; memorizing elements (boolean, integer,...)
