(IN-PACKAGE "RTL")

(INCLUDE-BOOK "rtl/rel11/lib/rac" :DIR :SYSTEM)

(SET-IGNORE-OK T)

(SET-IRRELEVANT-FORMALS-OK T)

(DEFUN STK_INIT (SOBJ)
       (AS 'NODETOP
           (BITS (+ 16382 1) 13 0)
           SOBJ))

(DEFUN STK_INITALL-LOOP-0 (I SOBJ)
       (DECLARE (XARGS :MEASURE (NFIX (- (+ 16382 1) I))))
       (IF (AND (INTEGERP I)
                (INTEGERP (+ 16382 1))
                (< I (+ 16382 1)))
           (LET ((SOBJ (AS 'NODEARR
                           (AS I (BITS 0 63 0) (AG 'NODEARR SOBJ))
                           SOBJ)))
                (STK_INITALL-LOOP-0 (+ I 1) SOBJ))
           SOBJ))

(DEFUN STK_INITALL (SOBJ)
       (LET ((SOBJ (AS 'NODETOP
                       (BITS (+ 16382 1) 13 0)
                       SOBJ)))
            (STK_INITALL-LOOP-0 0 SOBJ)))

(DEFUN STK_TOP (SOBJ)
       (IF1 (LOG= (AG 'NODETOP SOBJ) (+ 16382 1))
            (MV (BITS 255 7 0) (BITS 0 63 0))
            (MV (BITS 0 7 0)
                (AG (AG 'NODETOP SOBJ)
                    (AG 'NODEARR SOBJ)))))

(DEFUN STK_NEXT (SOBJ)
       (IF1 (LOG< (- (+ 16382 1) (AG 'NODETOP SOBJ))
                  2)
            (MV (BITS 255 7 0) (BITS 0 63 0))
            (MV (BITS 0 7 0)
                (AG (+ (AG 'NODETOP SOBJ) 1)
                    (AG 'NODEARR SOBJ)))))

(DEFUN STK_SZ (SOBJ)
       (BITS (- (+ 16382 1) (AG 'NODETOP SOBJ))
             13 0))

(DEFUN STK_SPACE (SOBJ)
       (AG 'NODETOP SOBJ))

(DEFUN STK_POP (SOBJ)
       (IF1 (LOG= (AG 'NODETOP SOBJ) (+ 16382 1))
            SOBJ
            (AS 'NODETOP
                (BITS (+ (AG 'NODETOP SOBJ) 1) 13 0)
                SOBJ)))

(DEFUN STK_POPTO-LOOP-0 (I SOBJ DATUM D)
       (DECLARE (XARGS :MEASURE (NFIX (- (- (+ 16382 1) (AG 'NODETOP SOBJ))
                                         I))))
       (IF (AND (INTEGERP I)
                (INTEGERP (- (+ 16382 1) (AG 'NODETOP SOBJ)))
                (AND (< I (- (+ 16382 1) (AG 'NODETOP SOBJ)))
                     (NOT (EQL (SI (AG (+ I (AG 'NODETOP SOBJ))
                                       (AG 'NODEARR SOBJ))
                                   64)
                               (SI DATUM 64)))))
           (LET ((D (BITS (+ D 1) 13 0)))
                (STK_POPTO-LOOP-0 (+ I 1) SOBJ DATUM D))
           (MV I D)))

(DEFUN STK_POPTO (DATUM SOBJ)
       (IF1 (LOG= (- (+ 16382 1) (AG 'NODETOP SOBJ))
                  0)
            SOBJ
            (LET ((D (BITS 0 13 0)) (I 0))
                 (MV-LET (I D)
                         (STK_POPTO-LOOP-0 0 SOBJ DATUM D)
                         (AS 'NODETOP
                             (BITS (+ (AG 'NODETOP SOBJ) D) 13 0)
                             SOBJ)))))

(DEFUN STK_PUSH (V SOBJ)
       (IF1 (LOG= (AG 'NODETOP SOBJ) 0)
            SOBJ
            (LET ((SOBJ (AS 'NODETOP
                            (BITS (- (AG 'NODETOP SOBJ) 1) 13 0)
                            SOBJ)))
                 (AS 'NODEARR
                     (AS (AG 'NODETOP SOBJ)
                         V (AG 'NODEARR SOBJ))
                     SOBJ))))

