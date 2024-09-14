; Copyright (C) 2024, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(defstobj sub-stobj sub-stobj-fld)

(defstobj gen$c
  (sub$c :type sub-stobj))

(defun-nx gen$ap (x)
  (declare (xargs :guard t))
  (gen$cp x))

(defun-nx create-gen$a ()
  (declare (xargs :guard t))
  (create-gen$c))

(defun-nx sub$a (x)
  (declare (xargs :guard (gen$ap x)))
  (sub$c x))

(defun-nx update-sub$a (sub-stobj x)
  (declare (xargs :stobjs sub-stobj :guard (gen$ap x)))
  (update-sub$c sub-stobj x))
  
(defun-nx gen$corr (x y)
  (equal x y))

(progn
(DEFTHM CREATE-IMPL{CORRESPONDENCE}
  (GEN$CORR (CREATE-GEN$C) (CREATE-GEN$A))
  :RULE-CLASSES NIL)

(DEFTHM CREATE-IMPL{PRESERVED}
  (GEN$AP (CREATE-GEN$A))
  :RULE-CLASSES NIL)

(DEFTHM SUB-IMPL{CORRESPONDENCE}
  (IMPLIES (AND (GEN$CORR GEN$C IMPL)
                (GEN$AP IMPL))
           (EQUAL (SUB$C GEN$C) (SUB$A IMPL)))
  :RULE-CLASSES NIL)

(DEFTHM UPDATE-SUB-IMPL{CORRESPONDENCE}
  (IMPLIES (AND (GEN$CORR GEN$C IMPL)
                (SUB-STOBJP SUB-STOBJ)
                (GEN$AP IMPL))
           (GEN$CORR (UPDATE-SUB$C SUB-STOBJ GEN$C)
                     (UPDATE-SUB$A SUB-STOBJ IMPL)))
  :RULE-CLASSES NIL)

(DEFTHM UPDATE-SUB-IMPL{PRESERVED}
  (IMPLIES (AND (SUB-STOBJP SUB-STOBJ)
                (GEN$AP IMPL))
           (GEN$AP (UPDATE-SUB$A SUB-STOBJ IMPL)))
  :RULE-CLASSES NIL)
)

(defabsstobj impl
  :foundation gen$c
  :creator (create-impl :logic create-gen$a :exec create-gen$c)
  :recognizer (implp :logic gen$ap :exec gen$cp)
  :corr-fn gen$corr
  :exports ((sub-impl :logic sub$a :exec sub$c :updater update-sub-impl)
            (update-sub-impl :logic update-sub$a :exec update-sub$c)))

(attach-stobj gen impl)

(progn
(DEFTHM CREATE-GEN{CORRESPONDENCE}
  (GEN$CORR (CREATE-GEN$C) (CREATE-GEN$A))
  :RULE-CLASSES NIL)

(DEFTHM CREATE-GEN{PRESERVED}
  (GEN$AP (CREATE-GEN$A))
  :RULE-CLASSES NIL)

(DEFTHM SUB{CORRESPONDENCE}
  (IMPLIES (AND (GEN$CORR GEN$C GEN) (GEN$AP GEN))
           (EQUAL (SUB$C GEN$C) (SUB$A GEN)))
  :RULE-CLASSES NIL)

(DEFTHM UPDATE-SUB{CORRESPONDENCE}
  (IMPLIES (AND (GEN$CORR GEN$C GEN)
                (SUB-STOBJP SUB-STOBJ)
                (GEN$AP GEN))
           (GEN$CORR (UPDATE-SUB$C SUB-STOBJ GEN$C)
                     (UPDATE-SUB$A SUB-STOBJ GEN)))
  :RULE-CLASSES NIL)

(DEFTHM UPDATE-SUB{PRESERVED}
  (IMPLIES (AND (SUB-STOBJP SUB-STOBJ)
                (GEN$AP GEN))
           (GEN$AP (UPDATE-SUB$A SUB-STOBJ GEN)))
  :RULE-CLASSES NIL)
)

(defabsstobj gen
  :exports ((sub :updater update-sub)
            update-sub)
  :attachable t)
