(in-package "ACL2")

(defstobj a$c
          fld$c)

(defun a$ap (x)
  (declare (ignore x) (xargs :verify-guards t))
  t)

(defun create-a$a ()
  (declare (xargs :verify-guards t))
  nil)

(defun fld$a (x)
  (declare (xargs :verify-guards t))
  x)

(defun update-fld$a (x y)
  (declare (ignore y) (xargs :verify-guards t))
  x)

(defun a$corr (a$c a$a)
  (declare (xargs :verify-guards t
                  :stobjs (a$c)))
  (equal (fld$c a$c) a$a))

(DEFTHM CREATE-A{CORRESPONDENCE}
  (A$CORR (CREATE-A$C) (CREATE-A$A))
  :RULE-CLASSES NIL)

(DEFTHM CREATE-A{PRESERVED}
  (A$AP (CREATE-A$A))
  :RULE-CLASSES NIL)

(DEFTHM FLD{CORRESPONDENCE}
  (IMPLIES (A$CORR A$C A)
           (EQUAL (FLD$C A$C) (FLD$A A)))
  :RULE-CLASSES NIL)

(DEFTHM UPDATE-FLD{CORRESPONDENCE}
  (IMPLIES (A$CORR A$C A)
           (A$CORR (UPDATE-FLD$C V A$C)
                   (UPDATE-FLD$A V A)))
  :RULE-CLASSES NIL)

(DEFTHM UPDATE-FLD{PRESERVED}
  (IMPLIES (A$AP A)
           (A$AP (UPDATE-FLD$A V A)))
  :RULE-CLASSES NIL)

(defabsstobj a
             :exports (fld update-fld))

(defstobj b$c
          (afld$c :type a))

(defun b$ap (x)
  (declare (xargs :verify-guards t))
  (a$ap x))

(defun create-b$a ()
  (declare (xargs :verify-guards t))
  (create-a$a))

(defun afld$a (x)
  (declare (xargs :verify-guards t))
  x)

(defun update-afld$a (x y)
  (declare (ignore y) (xargs :verify-guards t))
  x)

(defun b$corr (b$c b$a)
  (declare (xargs :verify-guards t
                  :stobjs (b$c)))
  (equal (stobj-let ((a (afld$c b$c)))
                    (val)
                    (fld a)
                    val)
         b$a))

(DEFTHM CREATE-B{CORRESPONDENCE}
  (B$CORR (CREATE-B$C) (CREATE-B$A))
  :RULE-CLASSES NIL)

(DEFTHM CREATE-B{PRESERVED}
  (B$AP (CREATE-B$A))
  :RULE-CLASSES NIL)

(DEFTHM AFLD{CORRESPONDENCE}
  (IMPLIES (B$CORR B$C B)
           (EQUAL (AFLD$C B$C) (AFLD$A B)))
  :RULE-CLASSES NIL)

(DEFTHM UPDATE-AFLD{CORRESPONDENCE}
  (IMPLIES (B$CORR B$C B)
           (B$CORR (UPDATE-AFLD$C A B$C)
                   (UPDATE-AFLD$A A B)))
  :RULE-CLASSES NIL)

(DEFTHM UPDATE-AFLD{PRESERVED}
  (IMPLIES (B$AP B)
           (B$AP (UPDATE-AFLD$A A B)))
  :RULE-CLASSES NIL)

(defabsstobj b
          :exports (afld update-afld))

(ld "translate-hack-for-yahya-1.lisp")
(defun indirect-setter (val a$c)
  (declare (xargs :stobjs (a$c)))
  (update-fld$c val a$c))

(defun set-fld (b$c)
  (declare (xargs :stobjs (b$c)))
  (stobj-let ((a (afld$c b$c)))
             (a)
             (indirect-setter 'test a)
             b$c))
