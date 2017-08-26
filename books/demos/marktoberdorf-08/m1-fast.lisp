#|
(include-book "m1")
(certify-book "m1-fast" 1)
|#
(in-package "M1")

(include-book "fast")

(defconst *m1-boyer-moore-program*

; Allocation of locals

; pat   0 
; j     1
; txt   2
; i     3
; pmax  4 = (length pat)
; tmax  5 = (length txt)
; array 6 = (preprocess pat)
; c     7 = temp - last char read from txt

  '(

    (load 0)        ;  0    (load pat)
    (push "")       ;  1    (push "")
    (ifane 5)       ;  2    (ifane loop)        ; if pat/="", goto loop
    (load 2)        ;  3    (load txt)
    (push "")       ;  4    (push "")
    (ifane 40)      ;  5    (ifane win)         ; if txt/="", goto win
    (goto 43)       ;  6    (goto lose)         
; loop:             
    (load 1)        ;  7    (load j)     
    (iflt 37)       ;  8    (iflt win))         ; if j<0, goto win
    (load 5)        ;  9    (load tmax)  
    (load 3)        ; 10    (load i)     
    (sub)           ; 11    (sub)        
    (ifle 37)       ; 12    (ifle lose)         ; if (length txt)-i <= 0, goto lose
    (load 0)        ; 13    (load pat)   
    (load 1)        ; 14    (load j)     
    (aload)         ; 15    (aload)             ; pat[j]
    (load 2)        ; 16    (load txt)   
    (load 3)        ; 17    (load i)     
    (aload)         ; 18    (aload)             ; txt[i]
    (store 7)       ; 19    (store v)           ; (store into v)
    (load 7)        ; 20    (load v)     
    (sub)           ; 21    (sub)        
    (ifne 10)       ; 22    (ifne skip)         ; if pat[j] /= txt[i], goto skip
    (load 1)        ; 23    (load j)     
    (push 1)        ; 24    (push 1)    
    (sub)           ; 25    (sub)        
    (store 1)       ; 26    (store j)           ; j=j-1
    (load 3)        ; 27    (load i)     
    (push 1)        ; 28    (push 1)    
    (sub)           ; 29    (sub)        
    (store 3)       ; 30    (store i)           ; i=i-1
    (goto -24)      ; 31    (goto loop)         ; goto loop
; skip:
    (load 3)        ; 32    (load i)     
    (load 6)        ; 33    (load array)       
    (load 7)        ; 34    (load v)     
    (aload)         ; 35    (aload)      
    (load 1)        ; 36    (load j)     
    (aload)         ; 37    (aload)      
    (add)           ; 38    (add)
    (store 3)       ; 39    (store i)           ; i := i+array[c][j]
    (load 4)        ; 40    (load pmax)  
    (push 1)        ; 41    (push 1)    
    (sub)           ; 42    (sub)
    (store 1)       ; 43    (store j)           ; j := (length pat)-1
    (goto -37)      ; 44    (goto loop)   
; win:
    (load 3)        ; 45    (load i)     
    (push 1)        ; 46    (push 1)    
    (add)           ; 47    (add)        
    (return)        ; 48    (return)     
; lose:
    (push nil)      ; 49    (push nil) 
    (return) )      ; 50    (return))
  )

; We use the recurrence scheme in fast-loop repeatedly.  But when it was
; justified, char and length were enabled so we re-enable them so the
; termination proofs below are just like those for fast-loop.  We could have
; (should have) packaged the measure lemma differently.

(in-theory (enable char length))

(defun m1-boyer-moore-loop-sched (pat j txt i)
  (declare (xargs :measure (measure pat j txt i)
                  :well-founded-relation l<))
  (cond
   ((not (and (stringp pat) (integerp j)
              (stringp txt) (integerp i)
              (<= -1 j) (< j (length pat))
              (<= j i)))
    nil)
   ((< j 0)
    (repeat 0 6))
   ((<= (length txt) i)
    (repeat 0 8))
   ((equal (char-code (char pat j)) (char-code (char txt i)))
    (append (repeat 0 25)
            (m1-boyer-moore-loop-sched pat (- j 1) txt (- i 1))))
   (t (append (repeat 0 29)
              (m1-boyer-moore-loop-sched pat
                                         (- (length pat) 1)
                                         txt
                                         (+ i (delta (char txt i)
                                                     j
                                                     pat)))))))

(defun m1-boyer-moore-sched (pat txt)
  (if (equal pat "")
      (if (equal txt "")
          (repeat 0 9)
        (repeat 0 10))
    (append (repeat 0 3)
            (m1-boyer-moore-loop-sched pat 
                                       (- (length pat) 1)
                                       txt
                                       (- (length pat) 1)))))
(defun m1-boyer-moore-loop-vars (pat j txt i v)
  (declare (xargs :measure (measure pat j txt i)
                  :well-founded-relation l<))
  (cond
   ((not (and (stringp pat) (integerp j)
              (stringp txt) (integerp i)
              (<= -1 j) (< j (length pat))
              (<= j i)))
    (list j i v))
   ((< j 0)
    (list j i v))
   ((<= (length txt) i)
    (list j i v))
   ((equal (char-code (char pat j)) (char-code (char txt i)))
    (m1-boyer-moore-loop-vars
     pat
     (- j 1)
     txt
     (- i 1)
     (char-code (char txt i))))
   (t (m1-boyer-moore-loop-vars
       pat
       (- (length pat) 1)
       txt
       (+ i (delta (char txt i)
                   j
                   pat))
       (char-code (char txt i))))))

(defthm m1-boyer-moore-loop-is-fast-loop
  (implies (and (stringp pat)
                (stringp txt)
                (integerp j)
                (<= -1 j)
                (< j (length pat))
                (integerp i)
                (<= j i))
           (equal (run (m1-boyer-moore-loop-sched pat j txt i)
                       (make-state 7
                                   (list pat
                                         j
                                         txt
                                         i
                                         (length pat)
                                         (length txt)
                                         (preprocess pat)
                                         v)
                                   nil
                                   *m1-boyer-moore-program*))
                  (if (fast-loop pat j txt i)
                      (make-state 48
                                  (list pat
                                        (nth 0 (m1-boyer-moore-loop-vars pat j txt i v))
                                        txt
                                        (nth 1 (m1-boyer-moore-loop-vars pat j txt i v))
                                        (length pat)
                                        (length txt)
                                        (preprocess pat)
                                        (nth 2 (m1-boyer-moore-loop-vars pat j txt i v)))
                                  (push (fast-loop pat j txt i) nil)
                                  *m1-boyer-moore-program*)
                    (make-state 50
                                (list pat
                                      (nth 0 (m1-boyer-moore-loop-vars pat j txt i v))
                                      txt
                                      (nth 1 (m1-boyer-moore-loop-vars pat j txt i v))
                                      (length pat)
                                      (length txt)
                                      (preprocess pat)
                                      (nth 2 (m1-boyer-moore-loop-vars pat j txt i v)))
                                (push nil nil)
                                *m1-boyer-moore-program*))))
  :hints (("Goal" :in-theory (enable preprocess))))

(in-theory (disable length))

(defthm m1-boyer-moore-is-fast
  (implies (and (stringp pat)
                (stringp txt))
           (equal (top
                   (stack
                    (run (m1-boyer-moore-sched pat txt)
                         (make-state 0
                                     (list pat
                                           (- (length pat) 1)
                                           txt
                                           (- (length pat) 1)
                                           (length pat)
                                           (length txt)
                                           (preprocess pat)
                                           0)
                                     nil
                                     *m1-boyer-moore-program*))))
                  (fast pat txt))))

(defthm m1-boyer-moore-halts
  (implies (and (stringp pat)
                (stringp txt))
           (haltedp
            (run (m1-boyer-moore-sched pat txt)
                 (make-state 0
                             (list pat
                                   (- (length pat) 1)
                                   txt
                                   (- (length pat) 1)
                                   (length pat)
                                   (length txt)
                                   (preprocess pat)
                                   0)
                             nil
                             *m1-boyer-moore-program*)))))

(defthm m1-boyer-moore-is-correct
  (implies (and (stringp pat)
                (stringp txt))
           (equal (top
                   (stack
                    (run (m1-boyer-moore-sched pat txt)
                         (make-state 0
                                     (list pat
                                           (- (length pat) 1)
                                           txt
                                           (- (length pat) 1)
                                           (length pat)
                                           (length txt)
                                           (preprocess pat)
                                           0)
                                     nil
                                     *m1-boyer-moore-program*))))
                  (correct pat txt))))






