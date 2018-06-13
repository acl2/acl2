; Copyright (C) 2018, Regents of the University of Texas
; Written by Ebelechukwu Esimai
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; An example of a Hexnet network represented in ACL2


; The graphp is represented as an associated list of junctions. Each junction
; is paired with a list of its neighboring junctions and corresponding links
; between the junctions.

; A junction is either connected to one other junction or three.

; Each member of the list below is of the form

; (junction (target1 link01 link10)
;           (target2 link02 link20)
;           (target3 link03 link30)
; Each link0n is the link from junction to targetn, and
; linkn0 goes in the opposite direction.


(defconst *network*

;;               Target
;; Junction      Junction
;; (jx . jy)    ((dx . dy) in   out)
  '(((0 . 2)    ((2 . 2)   S1   S2))
    ((2 . 2)    ((0 . 2)   S2   S1)
                ((4 . 2)   S3   S4)
                ((2 . 4)   T1   T2))
    ((4 . 2)    ((2 . 2)   S4   S3)
                ((6 . 2)   S5   S6)
                ((4 . 3)   T3   T4))
    ((6 . 2)    ((4 . 2)   S6   S5)
                ((8 . 2)   S7   S8)
                ((6 . 0)   T5   T6))
    ((8 . 2)    ((6 . 2)   S8   S7)
                ((10 . 2)  S9   S10)
                ((8 . 3)   T7   T8))
    ((10 . 2)   ((8 . 2)   S10  S9)
                ((12 . 2)  S11  S12)
                ((10 . 4)  T9   T10))
    ((12 . 2)   ((10 . 2)  S12  S11))
    ((6 . 0)    ((6 . 2)   T6   T5))
    ((4 . 3)    ((4 . 2)   T4   T3))
    ((8 . 3)    ((8 . 2)   T8   T7))
    ((2 . 4)    ((2 . 2)   T2   T1)
                ((3 . 4)   S15  S16)
                ((2 . 6)   T13  T14))
    ((3 . 4)    ((2 . 4)   S16  S15))
    ((10 . 4)   ((10 . 2)  T10  T9)
                ((11 . 4)  S17  S18)
                ((10 . 6)  T15  T16))
    ((11 . 4)   ((10 . 4)  S18  S17))
    ((0 . 6)    ((2 . 6)   S19  S20))
    ((2 . 6)    ((0 . 6)   S20  S19)
                ((4 . 6)   S21  S22)
                ((2 . 4)   T14  T13))
    ((4 . 6)    ((2 . 6)   S22  S21)
                ((6 . 6)   S23  S24)
                ((4 . 7)   T17  T18))
    ((6 . 6)    ((4 . 6)   S24  S23)
                ((8 . 6)   S25  S26)
                ((6 . 8)   T19  T20))
    ((8 . 6)    ((6 . 6)   S26  S25)
                ((10 . 6)  S27  S28)
                ((8 . 7)   T21  T22))
    ((10 . 6)   ((8 . 6)   S28  S27)
                ((12 . 6)  S29  S30)
                ((10 . 4)  T16  T15))
    ((12 . 6)   ((10 . 6)  S30  S29))
    ((4 . 7)    ((4 . 6)   T18  T17))
    ((8 . 7)    ((8 . 6)   T22  T21))
    ((6 . 8)    ((6 . 6)   T20  T19))))



;; Linktable
(create-linktable *linktable* *network*)


;; Inverse-graph
(create-inverse-graph *inverse-graph* *network*)


;; To sumilate packet movement through the network
;; Run multistep function
(multi-step (list (list '(pkt1 (11 . 4) (0 . 2) data)  
                        '(pkt2 (12 . 2) (6 . 8) data))
                  (list '(pkt3 (8 . 7) (3 . 4) data)  
                        '(pkt4 (6 . 8) (11 . 4) data)
                        '(pkt5 (3 . 4) (12 . 6) data))
                  nil
                  nil
                  nil nil nil)
            nil
            *linktable*
            *inverse-graph*
            nil
            *network*
            nil)

;; To trace packet movement through the network
;; Run trace function
(trace-pkts (list (list '(pkt1 (11 . 4) (0 . 2) data)  
                        '(pkt2 (12 . 2) (6 . 8) data))
                  (list '(pkt3 (8 . 7) (3 . 4) data)  
                        '(pkt4 (6 . 8) (11 . 4) data)
                        '(pkt5 (3 . 4) (12 . 6) data))
                  nil
                  nil
                  nil nil nil)
            nil
            *linktable*
            *inverse-graph*
            nil
            *network*
            nil)
