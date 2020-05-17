; Copyright (C) 2020 David S. Hardin
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.


(IN-PACKAGE "RTL")

(INCLUDE-BOOK "rtl/rel11/lib/rac" :DIR :SYSTEM)

(SET-IGNORE-OK T)

(SET-IRRELEVANT-FORMALS-OK T)

(DEFUND STK_INIT (SOBJ)
        (AS 'NODETOP (BITS 16383 13 0) SOBJ))

(DEFUND STK_INITALL-LOOP-0 (I SOBJ)
        (DECLARE (XARGS :MEASURE (NFIX (- 16383 I))))
        (IF (AND (INTEGERP I) (< I 16383))
            (LET ((SOBJ (AS 'NODEARR
                            (AS I (BITS 0 63 0) (AG 'NODEARR SOBJ))
                            SOBJ)))
                 (STK_INITALL-LOOP-0 (+ I 1) SOBJ))
            SOBJ))

(DEFUND STK_INITALL (SOBJ)
        (LET ((SOBJ (AS 'NODETOP (BITS 16383 13 0) SOBJ)))
             (STK_INITALL-LOOP-0 0 SOBJ)))

(DEFUND STK_CAPACITY (SOBJ)
        (BITS 16383 13 0))

(DEFUND STK_ISEMPTY (SOBJ)
        (LOG= 16383 (AG 'NODETOP SOBJ)))

(DEFUND STK_SZ (SOBJ)
        (BITS (- 16383 (AG 'NODETOP SOBJ))
              13 0))

(DEFUND STK_SPACE (SOBJ)
        (AG 'NODETOP SOBJ))

(DEFUND STK_POP (SOBJ)
        (IF1 (LOG< (AG 'NODETOP SOBJ) 16383)
             (AS 'NODETOP
                 (BITS (+ (AG 'NODETOP SOBJ) 1) 13 0)
                 SOBJ)
             SOBJ))

(DEFUND STK_POPTO-LOOP-0 (I SOBJ DATUM D)
        (DECLARE (XARGS :MEASURE (NFIX (- (- 16383 (AG 'NODETOP SOBJ)) I))))
        (IF (AND (INTEGERP I)
                 (INTEGERP (- 16383 (AG 'NODETOP SOBJ)))
                 (AND (< I (- 16383 (AG 'NODETOP SOBJ)))
                      (NOT (EQL (SI (AG (+ I (AG 'NODETOP SOBJ))
                                        (AG 'NODEARR SOBJ))
                                    64)
                                (SI DATUM 64)))))
            (LET ((D (BITS (+ D 1) 13 0)))
                 (STK_POPTO-LOOP-0 (+ I 1) SOBJ DATUM D))
            (MV I D)))

(DEFUND STK_POPTO (DATUM SOBJ)
        (IF1 (LOG= (- 16383 (AG 'NODETOP SOBJ)) 0)
             SOBJ
             (LET ((D (BITS 0 13 0)) (I 0))
                  (MV-LET (I D)
                          (STK_POPTO-LOOP-0 0 SOBJ DATUM D)
                          (AS 'NODETOP
                              (BITS (+ (AG 'NODETOP SOBJ) D) 13 0)
                              SOBJ)))))

(DEFUND STK_TOP (SOBJ)
        (IF1 (LOG< (AG 'NODETOP SOBJ) 16383)
             (MV (BITS 0 7 0)
                 (AG (AG 'NODETOP SOBJ)
                     (AG 'NODEARR SOBJ)))
             (MV (BITS 255 7 0) (BITS 0 63 0))))

(DEFUND STK_TOPTHENPOP (SOBJ)
        (IF1 (LOG< (AG 'NODETOP SOBJ) 16383)
             (LET ((TOS (AG (AG 'NODETOP SOBJ)
                            (AG 'NODEARR SOBJ)))
                   (SOBJ (AS 'NODETOP
                             (BITS (+ (AG 'NODETOP SOBJ) 1) 13 0)
                             SOBJ)))
                  (MV (BITS 0 7 0) TOS))
             (MV (BITS 255 7 0) (BITS 0 63 0))))

(DEFUND STK_NEXT (SOBJ)
        (IF1 (LOG< (- 16383 (AG 'NODETOP SOBJ)) 2)
             (MV (BITS 255 7 0) (BITS 0 63 0))
             (MV (BITS 0 7 0)
                 (AG (+ (AG 'NODETOP SOBJ) 1)
                     (AG 'NODEARR SOBJ)))))

(DEFUND STK_PUSH (V SOBJ)
        (IF1 (LOG<> (AG 'NODETOP SOBJ) 0)
             (LET ((SOBJ (AS 'NODETOP
                             (BITS (- (AG 'NODETOP SOBJ) 1) 13 0)
                             SOBJ)))
                  (AS 'NODEARR
                      (AS (AG 'NODETOP SOBJ)
                          V (AG 'NODEARR SOBJ))
                      SOBJ))
             SOBJ))

