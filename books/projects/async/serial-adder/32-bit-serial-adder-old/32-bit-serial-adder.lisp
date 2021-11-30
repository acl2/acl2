;; Copyright (C) 2017, Regents of the University of Texas
;; Written by Cuong Chau
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; May 2019

(in-package "ADE")

(include-book "32-bit-serial-adder-control")
(include-book "adder")
(include-book "link-joint")
(include-book "vector-module")

(local (include-book "arithmetic/top" :dir :system))
(local (include-book "centaur/gl/gl" :dir :system))

;; ======================================================================

;; One-Bit Full-Adder

(defconst *1-bit-adder$go-num* 2)

(module-generator
 1-bit-adder* ()
 '1-bit-adder
 (list* 'a-act 'a-in 'b-act 'b-in 'dr-lci 's-act
        (sis 'go 0 *1-bit-adder$go-num*))
 '(empty-a- empty-b- ready-out s-out ci-out)
 '(la a lb b lci ci ls s lco co)
 (list
  ;; LINKS
  ;; A
  '(la (a-status) link-cntl (a-act add-act))
  '(a (a-out a-out~) latch (a-act a-in))

  ;; B
  '(lb (b-status) link-cntl (b-act add-act))
  '(b (b-out b-out~) latch (b-act b-in))

  ;; CI
  '(lci (ci-status) link-cntl (carry-act comb-dr-lci))
  '(ci (ci-out ci-out~) latch (carry-act ci-in))

  ;; S
  '(ls (s-status) link-cntl (add-act s-act))
  '(s (s-out s-out~) latch (add-act s-in))

  ;; CO
  '(lco (co-status) link-cntl (add-act carry-act))
  '(co (co-out co-out~) latch (add-act co-in))

  ;; JOINTS
  ;; Full-adder
  '(g0 (add-full-in) b-and3 (a-status b-status ci-status))
  '(g1 (add-empty-out) b-or (s-status co-status))
  (list 'j-add
        '(add-act)
        'joint-cntl
        (list 'add-full-in 'add-empty-out (si 'go 0)))

  '(h0 (s-in co-in) full-adder (ci-out a-out b-out))

  ;; CO to CI
  (list 'j-carry
        '(carry-act)
        'joint-cntl
        (list 'co-status 'ci-status (si 'go 1)))

  '(h1 (ci-in) b-buf (co-out))

  '(c0 (comb-dr-lci) b-or (add-act dr-lci))

  ;; STATUS
  ;; '(s0 (l-a+b-status~) b-nand (a-status b-status))
  ;; '(empty--s (empty-) b-nand (ci-status l-a+b-status~))

  '(s0 (a-status~) b-not (a-status))
  '(in-status-a (empty-a-) b-nand (ci-status a-status~))

  '(s1 (b-status~) b-not (b-status))
  '(in-status-b (empty-b-) b-nand (ci-status b-status~))

  '(out-status (ready-out) b-and (ci-status s-status))
  )

 (declare (xargs :guard t)))

(make-event
 `(progn
    ,@(state-accessors-gen '1-bit-adder
                           '(la a lb b lci ci ls s lco co)
                           0)))

(defund 1-bit-adder$netlist ()
  (declare (xargs :guard t))
  (cons (1-bit-adder*)
        (union$ *joint-cntl* *full-adder*
                :test 'equal)))

(defund 1-bit-adder& (netlist)
  (declare (xargs :guard (alistp netlist)))
  (b* ((subnetlist (delete-to-eq '1-bit-adder netlist)))
    (and (equal (assoc '1-bit-adder netlist)
                (1-bit-adder*))
         (joint-cntl& subnetlist)
         (full-adder& subnetlist))))

(local
 (defthmd check-1-bit-adder$netlist
   (and (net-syntax-okp (1-bit-adder$netlist))
        (net-arity-okp (1-bit-adder$netlist))
        (1-bit-adder& (1-bit-adder$netlist)))))

(defund 1-bit-adder$empty-a- (st)
  (b* ((la  (nth *1-bit-adder$la* st))
       (lci (nth *1-bit-adder$lci* st)))
    (f-nand (car lci)
            (f-not (car la)))))

(defund 1-bit-adder$empty-b- (st)
  (b* ((lb  (nth *1-bit-adder$lb* st))
       (lci (nth *1-bit-adder$lci* st)))
    (f-nand (car lci)
            (f-not (car lb)))))

(defund 1-bit-adder$ready-out (st)
  (b* ((lci (nth *1-bit-adder$lci* st))
       (ls  (nth *1-bit-adder$ls* st)))
    (f-and (car lci)
           (car ls))))

(defthm 1-bit-adder$value
  (b* ((ci  (nth *1-bit-adder$ci* st))
       (s   (nth *1-bit-adder$s* st)))
    (implies (1-bit-adder& netlist)
             (equal (se '1-bit-adder inputs st netlist)
                    (list (1-bit-adder$empty-a- st)
                          (1-bit-adder$empty-b- st)
                          (1-bit-adder$ready-out st)
                          (f-buf (car s))
                          (f-buf (car ci))))))
  :hints (("Goal"
           :expand (se '1-bit-adder inputs st netlist)
           :in-theory (e/d (de-rules
                            1-bit-adder&
                            1-bit-adder*$destructure
                            1-bit-adder$ready-out
                            1-bit-adder$empty-a-
                            1-bit-adder$empty-b-)
                           ((1-bit-adder*)
                            de-module-disabled-rules)))))

(defun 1-bit-adder$step (inputs st)
  (b* ((a-act    (nth 0 inputs))
       (a-in     (nth 1 inputs))
       (b-act    (nth 2 inputs))
       (b-in     (nth 3 inputs))
       (dr-lci   (nth 4 inputs))
       (s-act    (nth 5 inputs))
       (go-signals (nthcdr 6 inputs))

       (go-add   (nth 0 go-signals))
       (go-carry (nth 1 go-signals))

       (la  (nth *1-bit-adder$la* st))
       (a   (nth *1-bit-adder$a* st))
       (lb  (nth *1-bit-adder$lb* st))
       (b   (nth *1-bit-adder$b* st))
       (lci (nth *1-bit-adder$lci* st))
       (ci  (nth *1-bit-adder$ci* st))
       (ls  (nth *1-bit-adder$ls* st))
       (s   (nth *1-bit-adder$s* st))
       (lco (nth *1-bit-adder$lco* st))
       (co  (nth *1-bit-adder$co* st))

       (add-act (joint-act (f-and3 (car la) (car lb) (car lci))
                           (f-or (car ls) (car lco))
                           go-add))
       (carry-act (joint-act (car lco) (car lci) go-carry)))

    (list (list (f-sr a-act add-act (car la)))
          (list (f-if a-act a-in (car a)))

          (list (f-sr b-act add-act (car lb)))
          (list (f-if b-act b-in (car b)))

          (list (f-sr carry-act (f-or add-act dr-lci) (car lci)))
          (list (f-if carry-act (car co) (car ci)))

          (list (f-sr add-act s-act (car ls)))
          (list (f-if add-act
                      (f-xor3 (car ci)
                              (f-if a-act a-in (car a))
                              (f-if b-act b-in (car b)))
                      (car s)))

          (list (f-sr add-act carry-act (car lco)))
          (list (f-if add-act
                      (f-or (f-and (f-if a-act a-in (car a))
                                   (f-if b-act b-in (car b)))
                            (f-and (f-xor (f-if a-act a-in (car a))
                                          (f-if b-act b-in (car b)))
                                   (car ci)))
                      (car co))))))

(local
 (defthmd car-and-cdr-of-atom
   (implies (atom x)
            (and (not (car x))
                 (not (cdr x))))))

(defthm 1-bit-adder$state
  (b* ((inputs (list* a-act a-in b-act b-in dr-lci s-act go-signals)))
    (implies (and (1-bit-adder& netlist)
                  (equal (len go-signals) *1-bit-adder$go-num*))
             (equal (de '1-bit-adder inputs st netlist)
                    (1-bit-adder$step inputs st))))
  :hints (("Goal"
           :expand (:free (inputs)
                          (de '1-bit-adder inputs st netlist))
           :in-theory (e/d (de-rules
                            1-bit-adder&
                            1-bit-adder*$destructure
                            car-and-cdr-of-atom)
                           ((1-bit-adder*)
                            acl2::hons-duplicity-alist-p-of-cons
                            acl2::alistp-when-hons-duplicity-alist-p
                            de-module-disabled-rules)))))

(in-theory (disable 1-bit-adder$step))

;; ======================================================================

;; 32-Bit Serial Adder

;; Two operands and the sum are stored in shift registers.

(defconst *serial-adder$prim-go-num* 3)
(defconst *serial-adder$go-num* (+ *serial-adder$prim-go-num*
                                   *1-bit-adder$go-num*))

(module-generator
 serial-adder* ()
 'serial-adder
 (list* 'cntl-act 'bit-in 'result-act
        (sis 'go 0 *serial-adder$go-num*))
 (list* 'ready-in- 'ready-out
        (append (sis 'reg2-out 0 *data-size*) (list 'c-out)))
 '(lreg0 reg0 lreg1 reg1 lreg2 reg2 bit-add)
 (list
  ;; LINKS
  ;; REG0
  '(lreg0 (reg0-status) link-cntl (cntl-act a-act))
  (list 'reg0
        (sis 'reg0-out 0 *data-size*)
        'shift-reg32
        '(cntl-act bit-in))

  ;; REG1
  '(lreg1 (reg1-status) link-cntl (cntl-act b-act))
  (list 'reg1
        (sis 'reg1-out 0 *data-size*)
        'shift-reg32
        '(cntl-act bit-in))

  ;; REG2
  '(g (dr-lreg2) b-or (cntl-act result-act))
  '(lreg2 (reg2-status) link-cntl (s-act dr-lreg2))
  (list 'reg2
        (sis 'reg2-out 0 *data-size*)
        'shift-reg32
        '(s-act s-out))

  ;; BIT-ADD
  (list 'bit-add
        '(bit-add-empty-a- bit-add-empty-b- bit-add-ready-out
                           s-out ci-out)
        '1-bit-adder
        (list* 'a-act 'a-in 'b-act 'b-in 'result-act 's-act
               (sis 'go
                    *serial-adder$prim-go-num*
                    *1-bit-adder$go-num*)))
  '(carry-out (c-out) b-buf (ci-out))

  ;; JOINTS
  ;; Fetch operand A
  (list 'j-a
        '(a-act)
        'joint-cntl
        (list 'reg0-status 'bit-add-empty-a- (si 'go 0)))

  (list 'h0 '(a-in) 'b-buf (list (si 'reg0-out 0)))

  ;; Fetch operand B
  (list 'j-b
        '(b-act)
        'joint-cntl
        (list 'reg1-status 'bit-add-empty-b- (si 'go 1)))

  (list 'h1 '(b-in) 'b-buf (list (si 'reg1-out 0)))

  ;; Write sum
  (list 'j-s
        '(s-act)
        'joint-cntl
        (list 'bit-add-ready-out 'reg2-status (si 'go 2)))

  ;;'(h2 (bit2-in) b-buf (s-out))

  ;; STATUS
  '(s0 (reg2-status~) b-not (reg2-status))
  '(in-status (ready-in-) b-or3 (reg0-status reg1-status reg2-status~))
  '(out-status (ready-out) b-buf (reg2-status))
  )

 (declare (xargs :guard t)))

(make-event
 `(progn
    ,@(state-accessors-gen 'serial-adder
                           '(lreg0 reg0 lreg1 reg1 lreg2 reg2 bit-add)
                           0)))

(defund serial-adder$netlist ()
  (declare (xargs :guard t))
  (cons (serial-adder*)
        (1-bit-adder$netlist)))

(defund serial-adder& (netlist)
  (declare (xargs :guard (alistp netlist)))
  (b* ((subnetlist (delete-to-eq 'serial-adder netlist)))
    (and (equal (assoc 'serial-adder netlist)
                (serial-adder*))
         (joint-cntl& subnetlist)
         (1-bit-adder& subnetlist))))

(local
 (defthmd check-serial-adder$netlist
   (and (net-syntax-okp (serial-adder$netlist))
        (net-arity-okp (serial-adder$netlist))
        (serial-adder& (serial-adder$netlist)))))

(defund serial-adder$ready-in- (st)
  (b* ((lreg0 (nth *serial-adder$lreg0* st))
       (lreg1 (nth *serial-adder$lreg1* st))
       (lreg2 (nth *serial-adder$lreg2* st)))
    (f-or3 (car lreg0)
           (car lreg1)
           (f-not (car lreg2)))))

(defund serial-adder$ready-out (st)
  (b* ((lreg2 (nth *serial-adder$lreg2* st)))
    (f-buf (car lreg2))))

(defthm serial-adder$value
  (b* ((reg2    (nth *serial-adder$reg2* st))
       (bit-add (nth *serial-adder$bit-add* st))
       (ci      (nth *1-bit-adder$ci* bit-add)))
    (implies (and (serial-adder& netlist)
                  (true-listp (car reg2))
                  (equal (len (car reg2)) *data-size*))
             (equal (se 'serial-adder inputs st netlist)
                    (list* (serial-adder$ready-in- st)
                           (serial-adder$ready-out st)
                           (append (car reg2)
                                   (list (f-buf (car ci))))))))
  :hints (("Goal"
           :expand (se 'serial-adder inputs st netlist)
           :in-theory (e/d (de-rules
                            serial-adder&
                            serial-adder*$destructure
                            serial-adder$ready-out
                            serial-adder$ready-in-)
                           ((serial-adder*)
                            de-module-disabled-rules)))))

(defun serial-adder$step (inputs st)
  (b* ((cntl-act   (nth 0 inputs))
       (bit-in     (nth 1 inputs))
       (result-act (nth 2 inputs))
       (go-signals (nthcdr 3 inputs))

       (go-a       (nth 0 go-signals))
       (go-b       (nth 1 go-signals))
       (go-s       (nth 2 go-signals))
       (1-bit-adder$go-signals (nthcdr *serial-adder$prim-go-num*
                                       go-signals))

       (lreg0   (nth *serial-adder$lreg0* st))
       (reg0    (nth *serial-adder$reg0*  st))
       (lreg1   (nth *serial-adder$lreg1* st))
       (reg1    (nth *serial-adder$reg1*  st))
       (lreg2   (nth *serial-adder$lreg2* st))
       (reg2    (nth *serial-adder$reg2*  st))
       (bit-add (nth *serial-adder$bit-add* st))

       (s (nth *1-bit-adder$s* bit-add))

       (a-act (joint-act (car lreg0)
                         (1-bit-adder$empty-a- bit-add)
                         go-a))
       (a-in (f-buf (caar reg0)))
       (b-act (joint-act (car lreg1)
                         (1-bit-adder$empty-b- bit-add)
                         go-b))
       (b-in (f-buf (caar reg1)))
       (s-act (joint-act (1-bit-adder$ready-out bit-add)
                         (car lreg2)
                         go-s))
       (1-bit-adder$inputs (list* a-act a-in b-act b-in result-act s-act
                                  1-bit-adder$go-signals)))

    (list (list (f-sr cntl-act a-act (car lreg0)))
          (list (write-shift-reg cntl-act bit-in (car reg0)))

          (list (f-sr cntl-act b-act (car lreg1)))
          (list (write-shift-reg cntl-act bit-in (car reg1)))

          (list (f-sr s-act
                      (f-or cntl-act result-act)
                      (car lreg2)))
          (list (write-shift-reg s-act (car s) (car reg2)))

          (1-bit-adder$step 1-bit-adder$inputs bit-add))))

(defthm serial-adder$state
  (b* ((inputs (list* cntl-act bit-in result-act go-signals))
       (reg0   (nth *serial-adder$reg0* st))
       (reg1   (nth *serial-adder$reg1* st)))
    (implies (and (serial-adder& netlist)

                  (true-listp go-signals)
                  (equal (len go-signals) *serial-adder$go-num*)

                  (equal (len (car reg0)) *data-size*)
                  (equal (len (car reg1)) *data-size*))
             (equal (de 'serial-adder inputs st netlist)
                    (serial-adder$step inputs st))))
  :hints (("Goal"
           :expand (:free (inputs)
                          (de 'serial-adder inputs st netlist))
           :in-theory (e/d (de-rules
                            serial-adder&
                            serial-adder*$destructure
                            car-and-cdr-of-atom)
                           ((serial-adder*)
                            acl2::hons-duplicity-alist-p-of-cons
                            acl2::alistp-when-hons-duplicity-alist-p
                            de-module-disabled-rules)))))

(in-theory (disable serial-adder$step))

;; ======================================================================

;; 32-Bit Asynchronous Serial Adder with Control

(defconst *async-adder$prim-go-num* 3)
(defconst *async-adder$go-num* (+ *async-adder$prim-go-num*
                                  *serial-adder$go-num*))
(defconst *async-adder$st-len* 9)
(defconst *async-adder$cntl-st-len* 5)

(module-generator
 async-adder* ()
 'async-adder
 (list* 'dr-lresult (sis 'go 0 *async-adder$go-num*))
 (list* 'ready-in- 'ready-out (sis 'result-out 0 (1+ *data-size*)))
 '(lcntl cntl lnext-cntl next-cntl ldone- done- lresult result
         serial-add)

 (list
  ;; LINKS
  ;; CNTL
  '(lcntl (cntl-status) link-cntl (cntl-buf-act cntl-act))
  (list 'cntl
        (sis 'cntl-out 0 *async-adder$cntl-st-len*)
        (si 'latch-n *async-adder$cntl-st-len*)
        (list* 'cntl-buf-act (sis 'cntl-in 0 *async-adder$cntl-st-len*)))

  ;; NEXT-CNTL
  '(lnext-cntl (next-cntl-status) link-cntl (cntl-act cntl-buf-act))
  (list 'next-cntl
        (sis 'next-cntl-out 0 *async-adder$cntl-st-len*)
        (si 'latch-n 5)
        (list* 'cntl-act (sis 'next-cntl-in 0 *async-adder$cntl-st-len*)))

  ;; DONE-
  '(ldone- (done-status) link-cntl (cntl-act dr-ldone-))
  '(done- (done-out- done-out) latch (cntl-act done-in-))

  ;; RESULT
  '(lresult (result-status) link-cntl (result-act dr-lresult))
  (list 'result
        (sis 'result-out 0 (1+ *data-size*))
        (si 'latch-n (1+ *data-size*))
        (list* 'result-act (append (sis 'sum 0 *data-size*) (list 'carry))))

  ;; SERIAL-ADD
  (list 'serial-add
        (list* 'serial-add-ready-in- 'serial-add-ready-out
               (append (sis 'sum 0 *data-size*) (list 'carry)))
        'serial-adder
        (list* 'cntl-act 'low 'result-act (sis 'go
                                               *async-adder$prim-go-num*
                                               *serial-adder$go-num*)))

  ;; JOINTS
  ;; Next control state
  '(g0 (cntl-ready) b-or3 (next-cntl-status done-status
                                            serial-add-ready-in-))
  (list 'j-next-state
        '(cntl-act)
        'joint-cntl
        (list 'cntl-status 'cntl-ready (si 'go 0)))

  (list 'h0
        (list* 'low 'done-in-
               (sis 'next-cntl-in 0 *async-adder$cntl-st-len*))
        'next-cntl-state
        (sis 'cntl-out 0 *async-adder$cntl-st-len*))

  ;; Buffer control state
  '(g1 (next-cntl-ready) b-and3 (next-cntl-status done-status done-out-))
  (list 'j-buf-state
        '(cntl-buf-act)
        'joint-cntl
        (list 'next-cntl-ready 'cntl-status (si 'go 1)))

  (list 'buf-state
        (sis 'cntl-in 0 *async-adder$cntl-st-len*)
        (si 'v-buf *async-adder$cntl-st-len*)
        (sis 'next-cntl-out 0 *async-adder$cntl-st-len*))

  ;; Store the result to RESULT register
  '(g2 (result-ready) b-and3 (serial-add-ready-out done-status done-out))
  (list 'j-result
        '(result-act)
        'joint-cntl
        (list 'result-ready 'result-status (si 'go 2)))

  '(j-done- (dr-ldone-) b-or (cntl-buf-act result-act))

  ;; STATUS
  '(s0 (next-cntl-status~) b-not (next-cntl-status))
  '(in-status (ready-in-) b-or3 (next-cntl-status~
                                 done-status
                                 result-status))
  '(out-status (ready-out) b-buf (result-status))
  )

 (declare (xargs :guard t)))

(make-event
 `(progn
    ,@(state-accessors-gen
       'async-adder
       '(lcntl cntl lnext-cntl next-cntl ldone- done- lresult result
               serial-add)
       0)))

(defund async-adder$netlist ()
  (declare (xargs :guard t))
  (cons (async-adder*)
        (union$ (latch-n$netlist *async-adder$cntl-st-len*)
                (latch-n$netlist (1+ *data-size*))
                (v-buf$netlist *async-adder$cntl-st-len*)
                (serial-adder$netlist)
                (next-cntl-state$netlist)
                :test 'equal)))

(defund async-adder& (netlist)
  (declare (xargs :guard (alistp netlist)))
  (b* ((subnetlist (delete-to-eq 'async-adder netlist)))
    (and (equal (assoc 'async-adder netlist)
                (async-adder*))
         (joint-cntl& subnetlist)
         (latch-n& subnetlist *async-adder$cntl-st-len*)
         (latch-n& subnetlist (1+ *data-size*))
         (v-buf& subnetlist *async-adder$cntl-st-len*)
         (serial-adder& subnetlist)
         (next-cntl-state& subnetlist))))

(local
 (defthmd check-async-adder$netlist
   (and (net-syntax-okp (async-adder$netlist))
        (net-arity-okp (async-adder$netlist))
        (async-adder& (async-adder$netlist)))))

(defund async-adder$ready-in- (st)
  (b* ((lnext-cntl (nth *async-adder$lnext-cntl* st))
       (ldone-     (nth *async-adder$ldone-* st))
       (lresult    (nth *async-adder$lresult* st)))
    (f-or3 (f-not (car lnext-cntl))
           (car ldone-)
           (car lresult))))

(defund async-adder$ready-out (st)
  (b* ((lresult (nth *async-adder$lresult* st)))
    (f-buf (car lresult))))

(defthm async-adder$value
  (b* ((result     (nth *async-adder$result* st))
       (serial-add (nth *async-adder$serial-add* st))
       (reg2       (nth *serial-adder$reg2* serial-add)))
    (implies (and (async-adder& netlist)
                  (true-listp result)
                  (equal (len result) (1+ *data-size*))
                  (true-listp (car reg2))
                  (equal (len (car reg2)) *data-size*))
             (equal (se 'async-adder inputs st netlist)
                    (list* (async-adder$ready-in- st)
                           (async-adder$ready-out st)
                           (v-threefix (strip-cars result))))))
  :hints (("Goal"
           :expand (se 'async-adder inputs st netlist)
           :in-theory (e/d (de-rules
                            async-adder&
                            async-adder*$destructure
                            async-adder$ready-out
                            async-adder$ready-in-)
                           ((async-adder*)
                            open-v-threefix
                            de-module-disabled-rules)))))

(defun async-adder$step (inputs st)
  (b* ((dr-lresult (nth 0 inputs))
       (go-signals (nthcdr 1 inputs))

       (go-cntl     (nth 0 go-signals))
       (go-buf-cntl (nth 1 go-signals))
       (go-result   (nth 2 go-signals))
       (serial-adder$go-signals (nthcdr *async-adder$prim-go-num*
                                        go-signals))

       (lcntl (nth *async-adder$lcntl* st))
       (cntl (nth *async-adder$cntl* st))
       (lnext-cntl (nth *async-adder$lnext-cntl* st))
       (next-cntl (nth *async-adder$next-cntl* st))
       (ldone- (nth *async-adder$ldone-* st))
       (done- (nth *async-adder$done-* st))
       (lresult (nth *async-adder$lresult* st))
       (result (nth *async-adder$result* st))
       (serial-add (nth *async-adder$serial-add* st))

       (reg2 (nth *serial-adder$reg2* serial-add))
       (bit-add (nth *serial-adder$bit-add* serial-add))

       (ci (nth *1-bit-adder$ci* bit-add))

       (cntl-act (joint-act (car lcntl)
                            (f-or3 (car lnext-cntl)
                                   (car ldone-)
                                   (serial-adder$ready-in- serial-add))
                            go-cntl))
       (cntl-buf-act (joint-act (f-and3 (car lnext-cntl)
                                        (car ldone-)
                                        (car done-))
                                (car lcntl)
                                go-buf-cntl))
       (result-act (joint-act (f-and3 (serial-adder$ready-out serial-add)
                                      (car ldone-)
                                      (f-not (car done-)))
                              (car lresult)
                              go-result))
       (serial-adder$inputs
        (list* cntl-act nil result-act serial-adder$go-signals)))

    (list
     (list (f-sr cntl-buf-act cntl-act (car lcntl)))
     (pairlis$ (fv-if cntl-buf-act
                      (strip-cars next-cntl)
                      (strip-cars cntl))
               nil)

     (list (f-sr cntl-act cntl-buf-act (car lnext-cntl)))
     (pairlis$
      (fv-if cntl-act
             (f$next-cntl-state (v-threefix (strip-cars cntl)))
             (strip-cars next-cntl))
      nil)

     (list (f-sr cntl-act
                 (f-or cntl-buf-act result-act)
                 (car ldone-)))
     (list (f-if cntl-act
                 (compute-done- (v-threefix (strip-cars cntl)))
                 (car done-)))

     (list (f-sr result-act dr-lresult (car lresult)))
     (pairlis$ (fv-if result-act
                      (append (car reg2)
                              (list (f-buf (car ci))))
                      (strip-cars result))
               nil)

     (serial-adder$step serial-adder$inputs serial-add))))

(defthm async-adder$state
  (b* ((inputs (list* dr-lresult go-signals))

       (cntl       (nth *async-adder$cntl* st))
       (next-cntl  (nth *async-adder$next-cntl* st))
       (result     (nth *async-adder$result* st))
       (serial-add (nth *async-adder$serial-add* st))

       (reg0 (nth *serial-adder$reg0* serial-add))
       (reg1 (nth *serial-adder$reg1* serial-add))
       (reg2 (nth *serial-adder$reg2* serial-add)))
    (implies (and (async-adder& netlist)

                  (true-listp go-signals)
                  (equal (len go-signals) *async-adder$go-num*)

                  (len-1-true-listp cntl)
                  (equal (len cntl) *async-adder$cntl-st-len*)
                  (len-1-true-listp next-cntl)
                  (equal (len next-cntl) *async-adder$cntl-st-len*)
                  (true-listp result)
                  (equal (len result) (1+ *data-size*))
                  (equal (len (car reg0)) *data-size*)
                  (equal (len (car reg1)) *data-size*)
                  (true-listp (car reg2))
                  (equal (len (car reg2)) *data-size*))
             (equal (de 'async-adder inputs st netlist)
                    (async-adder$step inputs st))))
  :hints (("Goal"
           :expand (:free (inputs)
                          (de 'async-adder inputs st netlist))
           :in-theory (e/d (de-rules
                            async-adder&
                            async-adder*$destructure
                            open-nthcdr
                            list-rewrite-5
                            len-1-true-listp)
                           ((async-adder*)
                            acl2::hons-duplicity-alist-p-of-cons
                            acl2::alistp-when-hons-duplicity-alist-p
                            open-v-threefix
                            de-module-disabled-rules)))))

(in-theory (disable async-adder$step))

;; ======================================================================

;; Prove the state invariant of the async serial adder for one iteration.

(defund async-adder$go-cntl (inputs)
  (declare (xargs :guard (true-listp inputs)))
  (b* ((go-signals (nthcdr 1 inputs)))
    (nth 0 go-signals)))

(defund async-adder$go-buf-cntl (inputs)
  (declare (xargs :guard (true-listp inputs)))
  (b* ((go-signals (nthcdr 1 inputs)))
    (nth 1 go-signals)))

(defund async-adder$go-result (inputs)
  (declare (xargs :guard (true-listp inputs)))
  (b* ((go-signals (nthcdr 1 inputs)))
    (nth 2 go-signals)))

(defund async-adder$go-a (inputs)
  (declare (xargs :guard (true-listp inputs)))
  (b* ((go-signals (nthcdr 1 inputs))
       (serial-adder$go-signals (nthcdr *async-adder$prim-go-num*
                                        go-signals)))
    (nth 0 serial-adder$go-signals)))

(defund async-adder$go-b (inputs)
  (declare (xargs :guard (true-listp inputs)))
  (b* ((go-signals (nthcdr 1 inputs))
       (serial-adder$go-signals (nthcdr *async-adder$prim-go-num*
                                        go-signals)))
    (nth 1 serial-adder$go-signals)))

(defund async-adder$go-s (inputs)
  (declare (xargs :guard (true-listp inputs)))
  (b* ((go-signals (nthcdr 1 inputs))
       (serial-adder$go-signals (nthcdr *async-adder$prim-go-num*
                                        go-signals)))
    (nth 2 serial-adder$go-signals)))

(defund async-adder$go-add (inputs)
  (declare (xargs :guard (true-listp inputs)))
  (b* ((go-signals (nthcdr 1 inputs))
       (serial-adder$go-signals (nthcdr *async-adder$prim-go-num*
                                        go-signals))
       (1-bit-adder$go-signals (nthcdr *serial-adder$prim-go-num*
                                       serial-adder$go-signals)))
    (nth 0 1-bit-adder$go-signals)))

(defund async-adder$go-carry (inputs)
  (declare (xargs :guard (true-listp inputs)))
  (b* ((go-signals (nthcdr 1 inputs))
       (serial-adder$go-signals (nthcdr *async-adder$prim-go-num*
                                        go-signals))
       (1-bit-adder$go-signals (nthcdr *serial-adder$prim-go-num*
                                       serial-adder$go-signals)))
    (nth 1 1-bit-adder$go-signals)))

(deftheory async-adder$go-signals
  '(async-adder$go-cntl
    async-adder$go-buf-cntl
    async-adder$go-result
    async-adder$go-a
    async-adder$go-b
    async-adder$go-s
    async-adder$go-add
    async-adder$go-carry))

(defund async-adder$input-format (inputs)
  (declare (xargs :guard (true-listp inputs)))
  (b* ((dr-lresult (nth 0 inputs))
       (go-signals (nthcdr 1 inputs)))
    (and
     (equal dr-lresult nil)
     (true-listp go-signals)
     (equal (len go-signals) *async-adder$go-num*)
     (equal inputs
            (list* dr-lresult go-signals)))))

(defthmd async-adder$state-alt
  (b* ((cntl (nth *async-adder$cntl* st))
       (next-cntl (nth *async-adder$next-cntl* st))
       (result (nth *async-adder$result* st))
       (serial-add (nth *async-adder$serial-add* st))

       (reg0 (nth *serial-adder$reg0* serial-add))
       (reg1 (nth *serial-adder$reg1* serial-add))
       (reg2 (nth *serial-adder$reg2* serial-add)))
    (implies
     (and (async-adder& netlist)
          (async-adder$input-format inputs)

          (len-1-true-listp cntl)
          (equal (len cntl) *async-adder$cntl-st-len*)
          (len-1-true-listp next-cntl)
          (equal (len next-cntl) *async-adder$cntl-st-len*)
          (true-listp result)
          (equal (len result) (1+ *data-size*))
          (equal (len (car reg0)) *data-size*)
          (equal (len (car reg1)) *data-size*)
          (true-listp (car reg2))
          (equal (len (car reg2)) *data-size*))
     (equal (de 'async-adder inputs st netlist)
            (async-adder$step inputs st))))
  :hints (("Goal"
           :in-theory (enable async-adder$input-format)
           :use (:instance async-adder$state
                           (dr-lresult (nth 0 inputs))
                           (go-signals (nthcdr 1 inputs))))))

(run-gen async-adder)

(input-format-n-gen async-adder)

(defthmd de-n$async-adder
  (b* ((cntl (nth *async-adder$cntl* st))
       (next-cntl (nth *async-adder$next-cntl* st))
       (result (nth *async-adder$result* st))
       (serial-add (nth *async-adder$serial-add* st))

       (reg0 (nth *serial-adder$reg0* serial-add))
       (reg1 (nth *serial-adder$reg1* serial-add))
       (reg2 (nth *serial-adder$reg2* serial-add)))
    (implies (and (async-adder& netlist)
                  (async-adder$input-format-n inputs-seq n)

                  (len-1-true-listp cntl)
                  (equal (len cntl) *async-adder$cntl-st-len*)
                  (len-1-true-listp next-cntl)
                  (equal (len next-cntl) *async-adder$cntl-st-len*)
                  (true-listp result)
                  (equal (len result) (1+ *data-size*))
                  (equal (len (car reg0)) *data-size*)
                  (equal (len (car reg1)) *data-size*)
                  (true-listp (car reg2))
                  (equal (len (car reg2)) *data-size*))
             (equal (de-n 'async-adder inputs-seq st netlist n)
                    (async-adder$run inputs-seq st n))))
  :hints (("Goal"
           :induct (de-n 'async-adder inputs-seq st netlist n)
           :in-theory (e/d (de-n
                            async-adder$state-alt
                            async-adder$step
                            serial-adder$step
                            list-rewrite-10)
                           (nth
                            nthcdr
                            pairlis$
                            strip-cars
                            true-listp)))))

(defund async-adder$inv-st (st)
  (b* ((lcntl      (nth *async-adder$lcntl* st))
       (cntl       (nth *async-adder$cntl* st))
       (lnext-cntl (nth *async-adder$lnext-cntl* st))
       (next-cntl  (nth *async-adder$next-cntl* st))
       (ldone-     (nth *async-adder$ldone-* st))
       (done-      (nth *async-adder$done-* st))
       (lresult    (nth *async-adder$lresult* st))
       (result     (nth *async-adder$result* st))
       (serial-add (nth *async-adder$serial-add* st))

       (lreg0   (nth *serial-adder$lreg0* serial-add))
       (reg0    (nth *serial-adder$reg0*  serial-add))
       (lreg1   (nth *serial-adder$lreg1* serial-add))
       (reg1    (nth *serial-adder$reg1*  serial-add))
       (lreg2   (nth *serial-adder$lreg2* serial-add))
       (reg2    (nth *serial-adder$reg2*  serial-add))
       (bit-add (nth *serial-adder$bit-add* serial-add))

       (la  (nth *1-bit-adder$la* bit-add))
       (?a  (nth *1-bit-adder$a* bit-add))
       (lb  (nth *1-bit-adder$lb* bit-add))
       (?b  (nth *1-bit-adder$b* bit-add))
       (lci (nth *1-bit-adder$lci* bit-add))
       (?ci (nth *1-bit-adder$ci* bit-add))
       (ls  (nth *1-bit-adder$ls* bit-add))
       (?s  (nth *1-bit-adder$s* bit-add))
       (lco (nth *1-bit-adder$lco* bit-add))
       (?co (nth *1-bit-adder$co* bit-add)))

    (and (emptyp lcntl)
         (len-1-true-listp cntl)
         (equal (len cntl) *async-adder$cntl-st-len*)

         (fullp lnext-cntl)
         (len-1-true-listp next-cntl)
         (equal (len next-cntl) *async-adder$cntl-st-len*)
         (bvp (strip-cars next-cntl))

         (fullp ldone-)
         (equal (car done-) t)

         (emptyp lresult)
         (true-listp result)
         (equal (len result) (1+ *data-size*))

         (fullp lreg0)
         (equal (len (car reg0)) *data-size*)
         (fullp lreg1)
         (equal (len (car reg1)) *data-size*)
         (emptyp lreg2)
         (true-listp (car reg2))
         (equal (len (car reg2)) *data-size*)

         (emptyp la)
         (emptyp lb)
         (fullp lci)
         (emptyp ls)
         (emptyp lco))))

(defconst *async-adder-interleavings*
  (prepend-rec
   (shuffle-rec2 '(async-adder$go-buf-cntl)
                 (prepend-rec (shuffle '(async-adder$go-a)
                                       '(async-adder$go-b))
                              '(async-adder$go-add
                                async-adder$go-carry
                                async-adder$go-s)))
   '(async-adder$go-cntl)))

(defconst *async-adder-independ-lst*
  '((async-adder$go-buf-cntl async-adder$go-a async-adder$go-b)
    (async-adder$go-buf-cntl async-adder$go-add)
    (async-adder$go-buf-cntl async-adder$go-carry)
    (async-adder$go-buf-cntl async-adder$go-s)))

(make-event `,(st-trans-fn 'async-adder
                           *async-adder-interleavings*
                           *async-adder-independ-lst*))

(defund extract-async-adder-result-status (st)
  (nth 6 st))

(defund extract-async-adder-result-value (st)
  (strip-cars (nth 7 st)))

(defun async-adder$result-empty-n (inputs-seq st n)
  (declare (xargs :measure (acl2-count n)))
  (if (zp n)
      t
    (and (emptyp (extract-async-adder-result-status st))
         (async-adder$result-empty-n
          (cdr inputs-seq)
          (async-adder$step (car inputs-seq) st)
          (1- n)))))

(defthm open-async-adder$result-empty-n-zp
  (implies (zp n)
           (equal (async-adder$result-empty-n inputs-seq st n)
                  t)))

(defthm open-async-adder$result-empty-n
  (implies (not (zp n))
           (equal (async-adder$result-empty-n inputs-seq st n)
                  (and (emptyp (extract-async-adder-result-status st))
                       (async-adder$result-empty-n
                        (cdr inputs-seq)
                        (async-adder$step (car inputs-seq) st)
                        (1- n))))))

(defthm async-adder$result-emptyp-plus
  (implies (and (natp m)
                (natp n))
           (equal (async-adder$result-empty-n inputs-seq st (+ m n))
                  (and (async-adder$result-empty-n inputs-seq st m)
                       (async-adder$result-empty-n
                        (nthcdr m inputs-seq)
                        (async-adder$run inputs-seq st m)
                        n))))
  :hints (("Goal"
           :induct (async-adder$result-empty-n inputs-seq st m))))

(defthm async-adder$result-empty-n-lemma
  (implies (and (async-adder$result-empty-n inputs-seq st n)
                (natp m)
                (natp n)
                (< m n))
           (emptyp (extract-async-adder-result-status
                    (async-adder$run inputs-seq st m))))
  :hints (("Goal"
           :in-theory (enable async-adder$run))))

(in-theory (disable async-adder$result-empty-n))

(defthm consp-fv-shift-right
  (implies (consp a)
           (consp (fv-shift-right a si)))
  :hints (("Goal" :in-theory (enable fv-shift-right)))
  :rule-classes :type-prescription)

;; This function produces two lemmas:

;; (1) The emptyness property of the result register's status.

;; (2) The state of the async serial adder is preserved after running it a
;; certain number of DE steps (Note that the number of DE steps to be executed
;; is varied due to different interleavings of GO signals). We prove that this
;; property holds for all possible interleavings of GO signals specified in
;; *ASYNC-ADDER-INTERLEAVINGS*.

(defun async-adder-invariant-gen (n)
  (declare (xargs :guard (natp n)))
  (b* ((hyps
        '((async-adder$inv-st st)))
       (concl1
        '(async-adder$result-empty-n inputs-seq st n))
       (concl2
        '(equal
          (async-adder$run inputs-seq st n)
          (list '(nil)
                next-cntl
                '(t)
                (pairlis$ (next-cntl-state (strip-cars next-cntl))
                          nil)
                '(t)
                (list (compute-done- (strip-cars next-cntl)))
                '(nil)
                (pairlis$ (v-threefix (strip-cars result))
                          nil)
                (list '(t)
                      (list (fv-shift-right (car reg0) nil))
                      '(t)
                      (list (fv-shift-right (car reg1) nil))
                      '(nil)
                      (list (fv-shift-right (car reg2)
                                            (f-xor3 (car ci)
                                                    (car (car reg0))
                                                    (car (car reg1)))))
                      (list '(nil)
                            (list (f-buf (car (car reg0))))
                            '(nil)
                            (list (f-buf (car (car reg1))))
                            '(t)
                            (list (f-or (f-and (car (car reg0))
                                               (car (car reg1)))
                                        (f-and (f-xor (car (car reg0))
                                                      (car (car reg1)))
                                               (car ci))))
                            '(nil)
                            (list (f-xor3 (car ci)
                                          (car (car reg0))
                                          (car (car reg1))))
                            '(nil)
                            (list (f-or (f-and (car (car reg0))
                                               (car (car reg1)))
                                        (f-and (f-xor (car (car reg0))
                                                      (car (car reg1)))
                                               (car ci)))))))
          )))
    (if (zp n)
        `((defthmd async-adder$invalid-result
            (implies
             (and ,@hyps
                  (async-adder$st-trans inputs-seq)
                  (equal n (async-adder$st-trans->numsteps inputs-seq))
                  (async-adder$input-format-n inputs-seq n))
             ,concl1)
            :hints (("Goal"
                     :in-theory (e/d* (async-adder$st-trans
                                       async-adder$st-trans->numsteps)
                                      (open-async-adder$result-empty-n
                                       fullp emptyp posp
                                       open-async-adder$input-format-n)))))

          (defthmd async-adder$state-invariant
            (b* ((?lcntl      (nth *async-adder$lcntl* st))
                 (?cntl       (nth *async-adder$cntl* st))
                 (?lnext-cntl (nth *async-adder$lnext-cntl* st))
                 (?next-cntl  (nth *async-adder$next-cntl* st))
                 (?ldone-     (nth *async-adder$ldone-* st))
                 (?done-      (nth *async-adder$done-* st))
                 (?lresult    (nth *async-adder$lresult* st))
                 (?result     (nth *async-adder$result* st))
                 (serial-add  (nth *async-adder$serial-add* st))

                 (?lreg0  (nth *serial-adder$lreg0* serial-add))
                 (?reg0   (nth *serial-adder$reg0*  serial-add))
                 (?lreg1  (nth *serial-adder$lreg1* serial-add))
                 (?reg1   (nth *serial-adder$reg1*  serial-add))
                 (?lreg2  (nth *serial-adder$lreg2* serial-add))
                 (?reg2   (nth *serial-adder$reg2*  serial-add))
                 (bit-add (nth *serial-adder$bit-add* serial-add))

                 (?la  (nth *1-bit-adder$la* bit-add))
                 (?a   (nth *1-bit-adder$a* bit-add))
                 (?lb  (nth *1-bit-adder$lb* bit-add))
                 (?b   (nth *1-bit-adder$b* bit-add))
                 (?lci (nth *1-bit-adder$lci* bit-add))
                 (?ci  (nth *1-bit-adder$ci* bit-add))
                 (?ls  (nth *1-bit-adder$ls* bit-add))
                 (?s   (nth *1-bit-adder$s* bit-add))
                 (?lco (nth *1-bit-adder$lco* bit-add))
                 (?co  (nth *1-bit-adder$co* bit-add)))
              (implies
               (and ,@hyps
                    (async-adder$st-trans inputs-seq)
                    (equal n (async-adder$st-trans->numsteps inputs-seq))
                    (async-adder$input-format-n inputs-seq n))
               ,concl2))
            :hints (("Goal"
                     :in-theory (e/d* (async-adder$st-trans
                                       async-adder$st-trans->numsteps)
                                      (open-async-adder$run
                                       fullp emptyp
                                       open-async-adder$input-format-n)))))
          )

      (b* ((lemma-name-1 (intern$ (concatenate
                                   'string
                                   "ASYNC-ADDER$INVALID-RESULT-"
                                   (str::nat-to-dec-string (1- n)))
                                  "ADE"))
           (lemma-name-2 (intern$ (concatenate
                                   'string
                                   "ASYNC-ADDER$STATE-INVARIANT-"
                                   (str::nat-to-dec-string (1- n)))
                                  "ADE"))
           (st-trans (intern$ (concatenate
                               'string
                               "ASYNC-ADDER$ST-TRANS-"
                               (str::nat-to-dec-string (1- n)))
                              "ADE"))
           (st-trans->numsteps (intern$ (concatenate
                                         'string
                                         "*ASYNC-ADDER$ST-TRANS-"
                                         (str::nat-to-dec-string (1- n))
                                         "->NUMSTEPS*")
                                        "ADE")))

        (append
         `((local
            (defthm ,lemma-name-1
              (implies
               (and ,@hyps
                    (,st-trans inputs-seq)
                    (equal n ,st-trans->numsteps)
                    (async-adder$input-format-n inputs-seq n))
               ,concl1)
              :hints (("Goal"
                       :do-not-induct t
                       :in-theory (e/d* (extract-async-adder-result-status
                                         async-adder$st-trans-rules
                                         async-adder$input-format
                                         async-adder$go-signals
                                         async-adder$step
                                         serial-adder$step
                                         serial-adder$ready-out
                                         serial-adder$ready-in-
                                         1-bit-adder$step
                                         1-bit-adder$ready-out
                                         1-bit-adder$empty-a-
                                         1-bit-adder$empty-b-
                                         async-adder$inv-st)
                                        (nth
                                         nthcdr
                                         take
                                         open-v-threefix
                                         car-cdr-elim))))))

           (local
            (defthm ,lemma-name-2
              (b* ((?lcntl      (nth *async-adder$lcntl* st))
                   (?cntl       (nth *async-adder$cntl* st))
                   (?lnext-cntl (nth *async-adder$lnext-cntl* st))
                   (?next-cntl  (nth *async-adder$next-cntl* st))
                   (?ldone-     (nth *async-adder$ldone-* st))
                   (?done-      (nth *async-adder$done-* st))
                   (?lresult    (nth *async-adder$lresult* st))
                   (?result     (nth *async-adder$result* st))
                   (serial-add  (nth *async-adder$serial-add* st))

                   (?lreg0  (nth *serial-adder$lreg0* serial-add))
                   (?reg0   (nth *serial-adder$reg0*  serial-add))
                   (?lreg1  (nth *serial-adder$lreg1* serial-add))
                   (?reg1   (nth *serial-adder$reg1*  serial-add))
                   (?lreg2  (nth *serial-adder$lreg2* serial-add))
                   (?reg2   (nth *serial-adder$reg2*  serial-add))
                   (bit-add (nth *serial-adder$bit-add* serial-add))

                   (?la  (nth *1-bit-adder$la* bit-add))
                   (?a   (nth *1-bit-adder$a* bit-add))
                   (?lb  (nth *1-bit-adder$lb* bit-add))
                   (?b   (nth *1-bit-adder$b* bit-add))
                   (?lci (nth *1-bit-adder$lci* bit-add))
                   (?ci  (nth *1-bit-adder$ci* bit-add))
                   (?ls  (nth *1-bit-adder$ls* bit-add))
                   (?s   (nth *1-bit-adder$s* bit-add))
                   (?lco (nth *1-bit-adder$lco* bit-add))
                   (?co  (nth *1-bit-adder$co* bit-add)))
                (implies
                 (and ,@hyps
                      (,st-trans inputs-seq)
                      (equal n ,st-trans->numsteps)
                      (async-adder$input-format-n inputs-seq n))
                 ,concl2))
              :hints (("Goal"
                       :do-not-induct t
                       :in-theory (e/d* (async-adder$st-trans-rules
                                         async-adder$input-format
                                         async-adder$go-signals
                                         async-adder$step
                                         serial-adder$step
                                         serial-adder$ready-out
                                         serial-adder$ready-in-
                                         1-bit-adder$step
                                         1-bit-adder$ready-out
                                         1-bit-adder$empty-a-
                                         1-bit-adder$empty-b-
                                         write-shift-reg
                                         async-adder$inv-st)
                                        (nth
                                         nthcdr
                                         take
                                         open-v-threefix
                                         car-cdr-elim)))))))

         (async-adder-invariant-gen (1- n)))))))

(make-event
 `(encapsulate
    ()
    ,@(async-adder-invariant-gen
       (len *async-adder-interleavings*))))

(defund last-round-st (st)
  (b* ((lcntl      (nth *async-adder$lcntl* st))
       (cntl       (nth *async-adder$cntl* st))
       (lnext-cntl (nth *async-adder$lnext-cntl* st))
       (next-cntl  (nth *async-adder$next-cntl* st))
       (ldone-     (nth *async-adder$ldone-* st))
       (done-      (nth *async-adder$done-* st))
       (lresult    (nth *async-adder$lresult* st))
       (result     (nth *async-adder$result* st))
       (serial-add (nth *async-adder$serial-add* st))

       (lreg0   (nth *serial-adder$lreg0* serial-add))
       (reg0    (nth *serial-adder$reg0*  serial-add))
       (lreg1   (nth *serial-adder$lreg1* serial-add))
       (reg1    (nth *serial-adder$reg1*  serial-add))
       (lreg2   (nth *serial-adder$lreg2* serial-add))
       (reg2    (nth *serial-adder$reg2*  serial-add))
       (bit-add (nth *serial-adder$bit-add* serial-add))

       (la  (nth *1-bit-adder$la* bit-add))
       (?a  (nth *1-bit-adder$a* bit-add))
       (lb  (nth *1-bit-adder$lb* bit-add))
       (?b  (nth *1-bit-adder$b* bit-add))
       (lci (nth *1-bit-adder$lci* bit-add))
       (?ci (nth *1-bit-adder$ci* bit-add))
       (ls  (nth *1-bit-adder$ls* bit-add))
       (?s  (nth *1-bit-adder$s* bit-add))
       (lco (nth *1-bit-adder$lco* bit-add))
       (?co (nth *1-bit-adder$co* bit-add)))

    (and (emptyp lcntl)
         (len-1-true-listp cntl)
         (equal (len cntl) *async-adder$cntl-st-len*)
         (bvp (strip-cars cntl))

         (fullp lnext-cntl)
         (len-1-true-listp next-cntl)
         (equal (len next-cntl) *async-adder$cntl-st-len*)
         (bvp (strip-cars next-cntl))

         (fullp ldone-)
         (equal (car done-) nil) ;; Done

         (emptyp lresult)
         (true-listp result)
         (equal (len result) (1+ *data-size*))

         (fullp lreg0)
         (equal (len (car reg0)) *data-size*)
         (fullp lreg1)
         (equal (len (car reg1)) *data-size*)
         (emptyp lreg2)
         (true-listp (car reg2))
         (equal (len (car reg2)) *data-size*)

         (emptyp la)
         (emptyp lb)
         (fullp lci)
         (emptyp ls)
         (emptyp lco))))

(defconst *async-adder-last-round-interleavings*
  (prepend-rec (shuffle '(async-adder$go-a) '(async-adder$go-b))
               '(async-adder$go-add
                 async-adder$go-carry
                 async-adder$go-s
                 async-adder$go-result)))

(defconst *async-adder-last-round-independ-lst*
  '((async-adder$go-a async-adder$go-b)))

(make-event `,(st-trans-fn 'async-adder-last-round
                           *async-adder-last-round-interleavings*
                           *async-adder-last-round-independ-lst*))

;; This function produces two lemmas:

;; (1) The emptyness property of the result register's status in the last
;; iteration.

;; (2) The state of the async serial adder after running it the last iteration,
;; i.e., DONE- signal is NIL (enabled). This lemma holds for all possible
;; interleavings of GO signals specified in
;; *ASYNC-ADDER-LAST-ROUND-INTERLEAVINGS*.

(defun async-adder-last-round-gen (n)
  (declare (xargs :guard (natp n)))
  (b* ((hyps
        '((last-round-st st)))
       (concl1
        '(async-adder$result-empty-n inputs-seq st n))
       (concl2
        '(equal
          (async-adder$run inputs-seq st n)
          (list '(nil)
                cntl
                '(t)
                next-cntl
                '(nil)
                '(nil) ;; Done
                '(t)
                (pairlis$
                 (append (fv-shift-right (car reg2)
                                         (f-xor3 (car ci)
                                                 (car (car reg0))
                                                 (car (car reg1))))
                         (list (f-or (f-and (car (car reg0))
                                            (car (car reg1)))
                                     (f-and (f-xor (car (car reg0))
                                                   (car (car reg1)))
                                            (car ci)))))
                 nil)
                (list '(nil)
                      (list (car reg0))
                      '(nil)
                      (list (car reg1))
                      '(nil)
                      (list (fv-shift-right (car reg2)
                                            (f-xor3 (car ci)
                                                    (car (car reg0))
                                                    (car (car reg1)))))
                      (list '(nil)
                            (list (f-buf (car (car reg0))))
                            '(nil)
                            (list (f-buf (car (car reg1))))
                            '(nil)
                            (list (f-or (f-and (car (car reg0))
                                               (car (car reg1)))
                                        (f-and (f-xor (car (car reg0))
                                                      (car (car reg1)))
                                               (car ci))))
                            '(nil)
                            (list (f-xor3 (car ci)
                                          (car (car reg0))
                                          (car (car reg1))))
                            '(nil)
                            (list (f-or (f-and (car (car reg0))
                                               (car (car reg1)))
                                        (f-and (f-xor (car (car reg0))
                                                      (car (car reg1)))
                                               (car ci)))))))
          )))
    (if (zp n)
        `((defthmd async-adder-last-round$invalid-result
            (implies
             (and ,@hyps
                  (async-adder-last-round$st-trans inputs-seq)
                  (equal n (async-adder-last-round$st-trans->numsteps
                            inputs-seq))
                  (async-adder$input-format-n inputs-seq n))
             ,concl1)
            :hints (("Goal"
                     :in-theory (e/d* (async-adder-last-round$st-trans
                                       async-adder-last-round$st-trans->numsteps)
                                      (open-async-adder$result-empty-n
                                       fullp emptyp posp
                                       open-async-adder$input-format-n)))))

          (defthmd async-adder-last-round$sim
            (b* ((?lcntl      (nth *async-adder$lcntl* st))
                 (?cntl       (nth *async-adder$cntl* st))
                 (?lnext-cntl (nth *async-adder$lnext-cntl* st))
                 (?next-cntl  (nth *async-adder$next-cntl* st))
                 (?ldone-     (nth *async-adder$ldone-* st))
                 (?done-      (nth *async-adder$done-* st))
                 (?lresult    (nth *async-adder$lresult* st))
                 (?result     (nth *async-adder$result* st))
                 (serial-add  (nth *async-adder$serial-add* st))

                 (?lreg0  (nth *serial-adder$lreg0* serial-add))
                 (?reg0   (nth *serial-adder$reg0*  serial-add))
                 (?lreg1  (nth *serial-adder$lreg1* serial-add))
                 (?reg1   (nth *serial-adder$reg1*  serial-add))
                 (?lreg2  (nth *serial-adder$lreg2* serial-add))
                 (?reg2   (nth *serial-adder$reg2*  serial-add))
                 (bit-add (nth *serial-adder$bit-add* serial-add))

                 (?la  (nth *1-bit-adder$la* bit-add))
                 (?a   (nth *1-bit-adder$a* bit-add))
                 (?lb  (nth *1-bit-adder$lb* bit-add))
                 (?b   (nth *1-bit-adder$b* bit-add))
                 (?lci (nth *1-bit-adder$lci* bit-add))
                 (?ci  (nth *1-bit-adder$ci* bit-add))
                 (?ls  (nth *1-bit-adder$ls* bit-add))
                 (?s   (nth *1-bit-adder$s* bit-add))
                 (?lco (nth *1-bit-adder$lco* bit-add))
                 (?co  (nth *1-bit-adder$co* bit-add)))
              (implies
               (and ,@hyps
                    (async-adder-last-round$st-trans inputs-seq)
                    (equal n (async-adder-last-round$st-trans->numsteps
                              inputs-seq))
                    (async-adder$input-format-n inputs-seq n))
               ,concl2))
            :hints (("Goal"
                     :in-theory (e/d* (async-adder-last-round$st-trans
                                       async-adder-last-round$st-trans->numsteps)
                                      (open-async-adder$run
                                       fullp emptyp
                                       open-async-adder$input-format-n)))))
          )

      (b* ((lemma-name-1
            (intern$ (concatenate
                      'string
                      "ASYNC-ADDER-LAST-ROUND$INVALID-RESULT-"
                      (str::nat-to-dec-string (1- n)))
                     "ADE"))
           (lemma-name-2 (intern$ (concatenate
                                   'string
                                   "ASYNC-ADDER-LAST-ROUND$SIM-"
                                   (str::nat-to-dec-string (1- n)))
                                  "ADE"))
           (st-trans (intern$ (concatenate
                               'string
                               "ASYNC-ADDER-LAST-ROUND$ST-TRANS-"
                               (str::nat-to-dec-string (1- n)))
                              "ADE"))
           (st-trans->numsteps (intern$ (concatenate
                                         'string
                                         "*ASYNC-ADDER-LAST-ROUND$ST-TRANS-"
                                         (str::nat-to-dec-string (1- n))
                                         "->NUMSTEPS*")
                                        "ADE")))

        (append
         `((local
            (defthm ,lemma-name-1
              (implies
               (and ,@hyps
                    (,st-trans inputs-seq)
                    (equal n ,st-trans->numsteps)
                    (async-adder$input-format-n inputs-seq n))
               ,concl1)
              :hints (("Goal"
                       :do-not-induct t
                       :in-theory (e/d* (extract-async-adder-result-status
                                         async-adder-last-round$st-trans-rules
                                         async-adder$input-format
                                         async-adder$go-signals
                                         async-adder$step
                                         serial-adder$step
                                         serial-adder$ready-out
                                         serial-adder$ready-in-
                                         1-bit-adder$step
                                         1-bit-adder$ready-out
                                         1-bit-adder$empty-a-
                                         1-bit-adder$empty-b-
                                         last-round-st
                                         v-threefix-append)
                                        (nth
                                         nthcdr
                                         take
                                         append-v-threefix
                                         car-cdr-elim))))))

           (local
            (defthm ,lemma-name-2
              (b* ((?lcntl      (nth *async-adder$lcntl* st))
                   (?cntl       (nth *async-adder$cntl* st))
                   (?lnext-cntl (nth *async-adder$lnext-cntl* st))
                   (?next-cntl  (nth *async-adder$next-cntl* st))
                   (?ldone-     (nth *async-adder$ldone-* st))
                   (?done-      (nth *async-adder$done-* st))
                   (?lresult    (nth *async-adder$lresult* st))
                   (?result     (nth *async-adder$result* st))
                   (serial-add  (nth *async-adder$serial-add* st))

                   (?lreg0  (nth *serial-adder$lreg0* serial-add))
                   (?reg0   (nth *serial-adder$reg0*  serial-add))
                   (?lreg1  (nth *serial-adder$lreg1* serial-add))
                   (?reg1   (nth *serial-adder$reg1*  serial-add))
                   (?lreg2  (nth *serial-adder$lreg2* serial-add))
                   (?reg2   (nth *serial-adder$reg2*  serial-add))
                   (bit-add (nth *serial-adder$bit-add* serial-add))

                   (?la  (nth *1-bit-adder$la* bit-add))
                   (?a   (nth *1-bit-adder$a* bit-add))
                   (?lb  (nth *1-bit-adder$lb* bit-add))
                   (?b   (nth *1-bit-adder$b* bit-add))
                   (?lci (nth *1-bit-adder$lci* bit-add))
                   (?ci  (nth *1-bit-adder$ci* bit-add))
                   (?ls  (nth *1-bit-adder$ls* bit-add))
                   (?s   (nth *1-bit-adder$s* bit-add))
                   (?lco (nth *1-bit-adder$lco* bit-add))
                   (?co  (nth *1-bit-adder$co* bit-add)))
                (implies
                 (and ,@hyps
                      (,st-trans inputs-seq)
                      (equal n ,st-trans->numsteps)
                      (async-adder$input-format-n inputs-seq n))
                 ,concl2))
              :hints (("Goal"
                       :do-not-induct t
                       :in-theory (e/d* (async-adder-last-round$st-trans-rules
                                         async-adder$input-format
                                         async-adder$go-signals
                                         async-adder$step
                                         serial-adder$step
                                         serial-adder$ready-out
                                         serial-adder$ready-in-
                                         1-bit-adder$step
                                         1-bit-adder$ready-out
                                         1-bit-adder$empty-a-
                                         1-bit-adder$empty-b-
                                         write-shift-reg
                                         last-round-st
                                         v-threefix-append)
                                        (nth
                                         nthcdr
                                         take
                                         append-v-threefix
                                         car-cdr-elim)))))))

         (async-adder-last-round-gen (1- n)))))))

(make-event
 `(encapsulate
    ()
    ,@(async-adder-last-round-gen
       (len *async-adder-last-round-interleavings*))))

(local
 (defthmd async-adder$state-fixpoint-instance
   (b* ((st (list '(nil)
                  cntl
                  '(t)
                  next-cntl
                  '(nil)
                  '(nil) ;; Done
                  '(t)
                  (pairlis$
                   (append (fv-shift-right (car reg2)
                                           (f-xor3 (car ci)
                                                   (car (car reg0))
                                                   (car (car reg1))))
                           (list (f-or (f-and (car (car reg0))
                                              (car (car reg1)))
                                       (f-and (f-xor (car (car reg0))
                                                     (car (car reg1)))
                                              (car ci)))))
                   nil)
                  (list '(nil)
                        (list (car reg0))
                        '(nil)
                        (list (car reg1))
                        '(nil)
                        (list (fv-shift-right (car reg2)
                                              (f-xor3 (car ci)
                                                      (car (car reg0))
                                                      (car (car reg1)))))
                        (list '(nil)
                              (list (f-buf (car (car reg0))))
                              '(nil)
                              (list (f-buf (car (car reg1))))
                              '(nil)
                              (list (f-or (f-and (car (car reg0))
                                                 (car (car reg1)))
                                          (f-and (f-xor (car (car reg0))
                                                        (car (car reg1)))
                                                 (car ci))))
                              '(nil)
                              (list (f-xor3 (car ci)
                                            (car (car reg0))
                                            (car (car reg1))))
                              '(nil)
                              (list (f-or (f-and (car (car reg0))
                                                 (car (car reg1)))
                                          (f-and (f-xor (car (car reg0))
                                                        (car (car reg1)))
                                                 (car ci)))))))))
     (implies
      (and (async-adder$input-format inputs)

           (len-1-true-listp cntl)
           (equal (len cntl) *async-adder$cntl-st-len*)
           (bvp (strip-cars cntl))

           (len-1-true-listp next-cntl)
           (equal (len next-cntl) *async-adder$cntl-st-len*)
           (bvp (strip-cars next-cntl))

           (equal (len (car reg0)) *data-size*)
           (equal (len (car reg1)) *data-size*)
           (true-listp (car reg2))
           (equal (len (car reg2)) *data-size*))
      (equal (async-adder$step inputs st)
             st)))
   :hints (("Goal" :in-theory (e/d* (async-adder$input-format
                                     async-adder$step
                                     serial-adder$step
                                     1-bit-adder$step
                                     1-bit-adder$ready-out
                                     write-shift-reg
                                     v-threefix-append)
                                    (append-v-threefix))))))

(defthmd async-adder$state-fixpoint
  (b* ((st (list '(nil)
                 cntl
                 '(t)
                 next-cntl
                 '(nil)
                 '(nil) ;; Done
                 '(t)
                 (pairlis$
                  (append (fv-shift-right (car reg2)
                                          (f-xor3 (car ci)
                                                  (car (car reg0))
                                                  (car (car reg1))))
                          (list (f-or (f-and (car (car reg0))
                                             (car (car reg1)))
                                      (f-and (f-xor (car (car reg0))
                                                    (car (car reg1)))
                                             (car ci)))))
                  nil)
                 (list '(nil)
                       (list (car reg0))
                       '(nil)
                       (list (car reg1))
                       '(nil)
                       (list (fv-shift-right (car reg2)
                                             (f-xor3 (car ci)
                                                     (car (car reg0))
                                                     (car (car reg1)))))
                       (list '(nil)
                             (list (f-buf (car (car reg0))))
                             '(nil)
                             (list (f-buf (car (car reg1))))
                             '(nil)
                             (list (f-or (f-and (car (car reg0))
                                                (car (car reg1)))
                                         (f-and (f-xor (car (car reg0))
                                                       (car (car reg1)))
                                                (car ci))))
                             '(nil)
                             (list (f-xor3 (car ci)
                                           (car (car reg0))
                                           (car (car reg1))))
                             '(nil)
                             (list (f-or (f-and (car (car reg0))
                                                (car (car reg1)))
                                         (f-and (f-xor (car (car reg0))
                                                       (car (car reg1)))
                                                (car ci)))))))))
    (implies
     (and (async-adder$input-format-n inputs-seq n)

          (len-1-true-listp cntl)
          (equal (len cntl) *async-adder$cntl-st-len*)
          (bvp (strip-cars cntl))

          (len-1-true-listp next-cntl)
          (equal (len next-cntl) *async-adder$cntl-st-len*)
          (bvp (strip-cars next-cntl))

          (equal (len (car reg0)) *data-size*)
          (equal (len (car reg1)) *data-size*)
          (true-listp (car reg2))
          (equal (len (car reg2)) *data-size*))
     (equal (async-adder$run inputs-seq st n)
            st)))
  :hints (("Goal"
           :in-theory (e/d (async-adder$run
                            async-adder$input-format-n
                            async-adder$state-fixpoint-instance)
                           (car-cdr-elim)))))

(defthmd async-adder$sim-last-round-to-fixpoint
  (b* ((?lcntl      (nth *async-adder$lcntl* st))
       (?cntl       (nth *async-adder$cntl* st))
       (?lnext-cntl (nth *async-adder$lnext-cntl* st))
       (?next-cntl  (nth *async-adder$next-cntl* st))
       (?ldone-     (nth *async-adder$ldone-* st))
       (?done-      (nth *async-adder$done-* st))
       (?lresult    (nth *async-adder$lresult* st))
       (?result     (nth *async-adder$result* st))
       (serial-add  (nth *async-adder$serial-add* st))

       (?lreg0  (nth *serial-adder$lreg0* serial-add))
       (?reg0   (nth *serial-adder$reg0*  serial-add))
       (?lreg1  (nth *serial-adder$lreg1* serial-add))
       (?reg1   (nth *serial-adder$reg1*  serial-add))
       (?lreg2  (nth *serial-adder$lreg2* serial-add))
       (?reg2   (nth *serial-adder$reg2*  serial-add))
       (bit-add (nth *serial-adder$bit-add* serial-add))

       (?la  (nth *1-bit-adder$la* bit-add))
       (?a   (nth *1-bit-adder$a* bit-add))
       (?lb  (nth *1-bit-adder$lb* bit-add))
       (?b   (nth *1-bit-adder$b* bit-add))
       (?lci (nth *1-bit-adder$lci* bit-add))
       (?ci  (nth *1-bit-adder$ci* bit-add))
       (?ls  (nth *1-bit-adder$ls* bit-add))
       (?s   (nth *1-bit-adder$s* bit-add))
       (?lco (nth *1-bit-adder$lco* bit-add))
       (?co  (nth *1-bit-adder$co* bit-add)))
    (implies
     (and (async-adder-last-round$st-trans inputs-seq)
          (natp n)
          (<= (async-adder-last-round$st-trans->numsteps inputs-seq)
              n)
          (async-adder$input-format-n inputs-seq n)
          (last-round-st st))
     (equal (async-adder$run inputs-seq st n)
            (list '(nil)
                  cntl
                  '(t)
                  next-cntl
                  '(nil)
                  '(nil) ;; Done
                  '(t)
                  (pairlis$
                   (append (fv-shift-right (car reg2)
                                           (f-xor3 (car ci)
                                                   (car (car reg0))
                                                   (car (car reg1))))
                           (list (f-or (f-and (car (car reg0))
                                              (car (car reg1)))
                                       (f-and (f-xor (car (car reg0))
                                                     (car (car reg1)))
                                              (car ci)))))
                   nil)
                  (list '(nil)
                        (list (car reg0))
                        '(nil)
                        (list (car reg1))
                        '(nil)
                        (list (fv-shift-right (car reg2)
                                              (f-xor3 (car ci)
                                                      (car (car reg0))
                                                      (car (car reg1)))))
                        (list '(nil)
                              (list (f-buf (car (car reg0))))
                              '(nil)
                              (list (f-buf (car (car reg1))))
                              '(nil)
                              (list (f-or (f-and (car (car reg0))
                                                 (car (car reg1)))
                                          (f-and (f-xor (car (car reg0))
                                                        (car (car reg1)))
                                                 (car ci))))
                              '(nil)
                              (list (f-xor3 (car ci)
                                            (car (car reg0))
                                            (car (car reg1))))
                              '(nil)
                              (list (f-or (f-and (car (car reg0))
                                                 (car (car reg1)))
                                          (f-and (f-xor (car (car reg0))
                                                        (car (car reg1)))
                                                 (car ci)))))))
            )))
  :hints (("Goal"
           :use ((:instance
                  async-adder$input-format-plus
                  (m (async-adder-last-round$st-trans->numsteps inputs-seq))
                  (n (- n
                        (async-adder-last-round$st-trans->numsteps
                         inputs-seq))))
                 (:instance
                  async-adder$run-plus
                  (m (async-adder-last-round$st-trans->numsteps inputs-seq))
                  (n (- n
                        (async-adder-last-round$st-trans->numsteps
                         inputs-seq)))))
           :in-theory (e/d (async-adder-last-round$sim
                            async-adder$state-fixpoint
                            last-round-st)
                           (open-async-adder$run
                            async-adder$input-format-plus
                            async-adder$run-plus
                            car-cdr-elim)))))

;; ======================================================================

;; Prove the loop state-invariant of the async serial adder.

(defun fv-shift-right-nil-n (a n)
  (declare (xargs :guard (natp n)))
  (if (zp n)
      a
    (fv-shift-right-nil-n (fv-shift-right a nil)
                          (1- n))))

(defthm len-fv-shift-right-nil-n
  (equal (len (fv-shift-right-nil-n a n))
         (len a)))

(defthm open-fv-shift-right-nil-n-zp
  (implies (zp n)
           (equal (fv-shift-right-nil-n a n)
                  a)))

(defthm open-fv-shift-right-nil-n
  (implies (not (zp n))
           (equal (fv-shift-right-nil-n a n)
                  (fv-shift-right-nil-n (fv-shift-right a nil)
                                        (1- n)))))

(in-theory (disable fv-shift-right-nil-n))

(defun fv-serial-sum (c a b n acc)
  (declare (xargs :measure (acl2-count n)
                  :guard (and (true-listp b)
                              (natp n))))
  (if (or (zp n) (atom a))
      acc
    (b* ((acc (fv-shift-right acc (f-xor3 c (car a) (car b)))))
      (fv-serial-sum (f-or (f-and (car a) (car b))
                           (f-and (f-xor (car a) (car b)) c))
                     (fv-shift-right a nil)
                     (fv-shift-right b nil)
                     (1- n)
                     acc))))

(defthm open-fv-serial-sum-zp
  (implies (or (zp n) (atom a))
           (equal (fv-serial-sum c a b n acc)
                  acc)))

(defthm open-fv-serial-sum
  (implies (not (or (zp n) (atom a)))
           (equal (fv-serial-sum c a b n acc)
                  (b* ((acc (fv-shift-right acc
                                            (f-xor3 c (car a) (car b)))))
                    (fv-serial-sum (f-or (f-and (car a) (car b))
                                         (f-and (f-xor (car a) (car b))
                                                c))
                                   (fv-shift-right a nil)
                                   (fv-shift-right b nil)
                                   (1- n)
                                   acc)))))

(in-theory (disable fv-serial-sum))

(defun fv-serial-carry (c a b n)
  (declare (xargs :measure (acl2-count n)
                  :guard (and (true-listp b)
                              (natp n))))
  (if (or (zp n) (atom a))
      c
    (fv-serial-carry (f-or (f-and (car a) (car b))
                           (f-and (f-xor (car a) (car b)) c))
                     (fv-shift-right a nil)
                     (fv-shift-right b nil)
                     (1- n))))

(defthm open-fv-serial-carry-zp
  (implies (or (zp n) (atom a))
           (equal (fv-serial-carry c a b n)
                  c)))

(defthm open-fv-serial-carry
  (implies (not (or (zp n) (atom a)))
           (equal (fv-serial-carry c a b n)
                  (fv-serial-carry (f-or (f-and (car a) (car b))
                                         (f-and (f-xor (car a) (car b))
                                                c))
                                   (fv-shift-right a nil)
                                   (fv-shift-right b nil)
                                   (1- n)))))

(in-theory (disable fv-serial-carry))

(defund fv-serial-adder (c a b n acc)
  (declare (xargs :guard (and (true-listp acc)
                              (true-listp b)
                              (natp n))))
  (append (fv-serial-sum c a b n acc)
          (list (fv-serial-carry c a b n))))

(defun next-cntl-state-n (st n)
  (declare (xargs :guard (and (true-listp st)
                              (natp n))))
  (if (zp n)
      st
    (next-cntl-state-n (next-cntl-state st)
                       (1- n))))

(defthm open-next-cntl-state-n-zp
  (implies (zp n)
           (equal (next-cntl-state-n st n) st)))

(defthm open-next-cntl-state-n
  (implies (not (zp n))
           (equal (next-cntl-state-n st n)
                  (next-cntl-state-n (next-cntl-state st)
                                     (1- n)))))

(in-theory (disable next-cntl-state-n))

(defun simulate-async-adder-loop-induct (inputs-seq st n count)
  (if (zp count)
      (list st n)
    (simulate-async-adder-loop-induct
     (nthcdr (async-adder$st-trans->numsteps inputs-seq)
             inputs-seq)
     (async-adder$run inputs-seq
                             st
                             (async-adder$st-trans->numsteps inputs-seq))
     (- n (async-adder$st-trans->numsteps inputs-seq))
     (1- count))))

(local
 (defthmd pos-len=>consp
   (implies (< 0 (len x))
            (consp x))))

(encapsulate
  ()

  (local
   (defthm simulate-async-adder-loop-aux-1
     (implies (and (natp x)
                   (<= 30 x)
                   (posp y)
                   (< (+ x y) 32))
              (equal y 1))
     :rule-classes nil))

  (local
   (defthm simulate-async-adder-loop-aux-2
     (implies
      (and (posp count)
           (not
            (equal
             (async-adder$st-trans-n->numsteps
              (nthcdr (async-adder$st-trans->numsteps inputs-seq)
                      inputs-seq)
              (+ -1 count))
             (+ (async-adder$st-trans->numsteps
                 (nthcdr (async-adder$st-trans->numsteps inputs-seq)
                         inputs-seq))
                (async-adder$st-trans-n->numsteps
                 (nthcdr (+ (async-adder$st-trans->numsteps inputs-seq)
                            (async-adder$st-trans->numsteps
                             (nthcdr (async-adder$st-trans->numsteps
                                      inputs-seq)
                                     inputs-seq)))
                         inputs-seq)
                 (+ -2 count))))))
      (equal count 1))
     :rule-classes nil))

  ;; The emptyness property of the result register's status. Prove by
  ;; induction.

  (defthmd simulate-async-adder-loop-invalid-result
    (b* ((next-cntl (nth *async-adder$next-cntl* st)))
      (implies
       (and (posp count)
            (< (+ (v-to-nat (strip-cars next-cntl))
                  count)
               *data-size*)
            (async-adder$st-trans-n inputs-seq count)
            (equal n (async-adder$st-trans-n->numsteps inputs-seq count))
            (async-adder$input-format-n inputs-seq n)
            (async-adder$inv-st st))
       (async-adder$result-empty-n inputs-seq st n)))
    :hints (("Goal"
             :induct
             (simulate-async-adder-loop-induct inputs-seq st n count)
             :in-theory (e/d (async-adder$invalid-result
                              async-adder$state-invariant
                              async-adder$inv-st
                              async-adder$st-trans-n)
                             (open-async-adder$input-format-n
                              open-async-adder$result-empty-n
                              open-async-adder$run
                              open-v-threefix
                              fullp
                              emptyp
                              nth
                              nthcdr
                              car-cdr-elim
                              (:type-prescription bvp-cvzbv)
                              true-listp
                              bv-is-true-list
                              fv-shift-right=v-shift-right
                              f-gates=b-gates
                              strip-cars)))
            ("Subgoal *1/2"
             :use (simulate-async-adder-loop-aux-2
                   (:instance simulate-async-adder-loop-aux-1
                              (x (v-to-nat (strip-cars
                                            (nth *async-adder$next-cntl*
                                                 st))))
                              (y count)))
             )))

  ;; The loop state-invariant of the async serial adder. Prove by induction.

  (defthmd simulate-async-adder-loop
    (b* ((?lcntl      (nth *async-adder$lcntl* st))
         (?cntl       (nth *async-adder$cntl* st))
         (?lnext-cntl (nth *async-adder$lnext-cntl* st))
         (?next-cntl  (nth *async-adder$next-cntl* st))
         (?ldone-     (nth *async-adder$ldone-* st))
         (?done-      (nth *async-adder$done-* st))
         (?lresult    (nth *async-adder$lresult* st))
         (?result     (nth *async-adder$result* st))
         (serial-add  (nth *async-adder$serial-add* st))

         (?lreg0  (nth *serial-adder$lreg0* serial-add))
         (?reg0   (nth *serial-adder$reg0*  serial-add))
         (?lreg1  (nth *serial-adder$lreg1* serial-add))
         (?reg1   (nth *serial-adder$reg1*  serial-add))
         (?lreg2  (nth *serial-adder$lreg2* serial-add))
         (?reg2   (nth *serial-adder$reg2*  serial-add))
         (bit-add (nth *serial-adder$bit-add* serial-add))

         (?la  (nth *1-bit-adder$la* bit-add))
         (?a   (nth *1-bit-adder$a* bit-add))
         (?lb  (nth *1-bit-adder$lb* bit-add))
         (?b   (nth *1-bit-adder$b* bit-add))
         (?lci (nth *1-bit-adder$lci* bit-add))
         (?ci  (nth *1-bit-adder$ci* bit-add))
         (?ls  (nth *1-bit-adder$ls* bit-add))
         (?s   (nth *1-bit-adder$s* bit-add))
         (?lco (nth *1-bit-adder$lco* bit-add))
         (?co  (nth *1-bit-adder$co* bit-add)))
      (implies
       (and (posp count)
            (< (+ (v-to-nat (strip-cars next-cntl))
                  count)
               *data-size*)
            (async-adder$st-trans-n inputs-seq count)
            (equal n (async-adder$st-trans-n->numsteps inputs-seq count))
            (async-adder$input-format-n inputs-seq n)
            (async-adder$inv-st st))
       (equal
        (async-adder$run inputs-seq st n)
        (list
         '(nil)
         (pairlis$ (next-cntl-state-n (strip-cars next-cntl)
                                      (1- count))
                   nil)
         '(t)
         (pairlis$ (next-cntl-state-n (strip-cars next-cntl)
                                      count)
                   nil)
         '(t)
         (list (compute-done- (next-cntl-state-n (strip-cars next-cntl)
                                                 (1- count))))
         '(nil)
         (pairlis$ (v-threefix (strip-cars result))
                   nil)
         (list '(t)
               (list (fv-shift-right-nil-n (car reg0) count))
               '(t)
               (list (fv-shift-right-nil-n (car reg1) count))
               '(nil)
               (list
                (fv-serial-sum (car ci) (car reg0) (car reg1)
                               count
                               (car reg2)))
               (list '(nil)
                     (list (f-buf (car (fv-shift-right-nil-n
                                        (car reg0)
                                        (1- count)))))
                     '(nil)
                     (list (f-buf (car (fv-shift-right-nil-n
                                        (car reg1)
                                        (1- count)))))
                     '(t)
                     (list (fv-serial-carry (car ci)
                                            (car reg0)
                                            (car reg1)
                                            count))
                     '(nil)
                     (list (f-xor3 (fv-serial-carry (car ci)
                                                    (car reg0)
                                                    (car reg1)
                                                    (1- count))
                                   (car (fv-shift-right-nil-n
                                         (car reg0)
                                         (1- count)))
                                   (car (fv-shift-right-nil-n
                                         (car reg1)
                                         (1- count)))))
                     '(nil)
                     (list (fv-serial-carry (car ci)
                                            (car reg0)
                                            (car reg1)
                                            count))))))))
    :hints (("Goal"
             :induct
             (simulate-async-adder-loop-induct inputs-seq st n count)
             :in-theory (e/d (async-adder$state-invariant
                              async-adder$inv-st
                              pos-len=>consp
                              async-adder$st-trans-n
                              next-cntl-state-n)
                             (open-async-adder$input-format-n
                              open-v-threefix
                              fullp
                              emptyp
                              nth
                              nthcdr
                              car-cdr-elim
                              (:type-prescription bvp-cvzbv)
                              true-listp
                              bv-is-true-list
                              fv-shift-right=v-shift-right
                              f-gates=b-gates
                              strip-cars)))
            ("Subgoal *1/2"
             :use (:instance simulate-async-adder-loop-aux-1
                             (x (v-to-nat
                                 (strip-cars (nth *async-adder$next-cntl*
                                                  st))))
                             (y count)))))
  )

(encapsulate
  ()

  (local
   (defthm 3vp-of-car-v-threefix
     (3vp (car (v-threefix x)))
     :hints (("Goal" :in-theory (enable 3vp v-threefix)))))

  (defthm f-buf-of-car-fv-shift-right-canceled
    (equal (f-buf (car (fv-shift-right a si)))
           (car (fv-shift-right a si)))
    :hints (("Goal" :in-theory (enable fv-shift-right))))

  (defthm f-buf-of-car-fv-shift-right-nil-n-canceled
    (implies (posp n)
             (equal (f-buf (car (fv-shift-right-nil-n a n)))
                    (car (fv-shift-right-nil-n a n))))
    :hints (("Goal" :in-theory (enable fv-shift-right-nil-n
                                       fv-shift-right)))))

(defun async-adder$init-st (st)
  (b* ((lcntl      (nth *async-adder$lcntl* st))
       (cntl       (nth *async-adder$cntl* st))
       (lnext-cntl (nth *async-adder$lnext-cntl* st))
       (next-cntl  (nth *async-adder$next-cntl* st))
       (ldone-     (nth *async-adder$ldone-* st))
       (done-      (nth *async-adder$done-* st))
       (lresult    (nth *async-adder$lresult* st))
       (result     (nth *async-adder$result* st))
       (serial-add (nth *async-adder$serial-add* st))

       (lreg0   (nth *serial-adder$lreg0* serial-add))
       (reg0    (nth *serial-adder$reg0*  serial-add))
       (lreg1   (nth *serial-adder$lreg1* serial-add))
       (reg1    (nth *serial-adder$reg1*  serial-add))
       (lreg2   (nth *serial-adder$lreg2* serial-add))
       (reg2    (nth *serial-adder$reg2*  serial-add))
       (bit-add (nth *serial-adder$bit-add* serial-add))

       (la  (nth *1-bit-adder$la* bit-add))
       (?a  (nth *1-bit-adder$a* bit-add))
       (lb  (nth *1-bit-adder$lb* bit-add))
       (?b  (nth *1-bit-adder$b* bit-add))
       (lci (nth *1-bit-adder$lci* bit-add))
       (?ci (nth *1-bit-adder$ci* bit-add))
       (ls  (nth *1-bit-adder$ls* bit-add))
       (?s  (nth *1-bit-adder$s* bit-add))
       (lco (nth *1-bit-adder$lco* bit-add))
       (?co (nth *1-bit-adder$co* bit-add)))

    (and (emptyp lcntl)
         (len-1-true-listp cntl)
         (equal (len cntl) *async-adder$cntl-st-len*)

         (fullp lnext-cntl)
         (equal next-cntl '((nil) (nil) (nil) (nil) (nil)))

         (fullp ldone-)
         (equal (car done-) t)

         (emptyp lresult)
         (true-listp result)
         (equal (len result) (1+ *data-size*))

         (fullp lreg0)
         (equal (len (car reg0)) *data-size*)
         (fullp lreg1)
         (equal (len (car reg1)) *data-size*)
         (emptyp lreg2)
         (true-listp (car reg2))
         (equal (len (car reg2)) *data-size*)

         (emptyp la)
         (emptyp lb)
         (fullp lci)
         (emptyp ls)
         (emptyp lco))))

(defthmd async-adder$init-st=>inv-st
  (implies (async-adder$init-st st)
           (async-adder$inv-st st))
  :hints (("Goal" :in-theory (enable async-adder$inv-st))))

(in-theory (disable async-adder$init-st))

(defthmd simulate-async-adder-loop-invalid-result-instance
  (implies
   (and (equal count (1- *data-size*))
        (async-adder$st-trans-n inputs-seq count)
        (equal n (async-adder$st-trans-n->numsteps inputs-seq count))
        (async-adder$input-format-n inputs-seq n)
        (async-adder$init-st st))
   (async-adder$result-empty-n inputs-seq st n))
  :hints (("Goal"
           :do-not-induct t
           :use simulate-async-adder-loop-invalid-result
           :in-theory (union-theories
                       '(async-adder$init-st
                         async-adder$init-st=>inv-st
                         posp
                         v-to-nat
                         len-1-true-listp
                         len
                         bvp
                         true-list-listp
                         booleanp
                         strip-cars)
                       (theory 'minimal-theory)))))

(defthmd simulate-async-adder-loop-instance
  (b* ((?lcntl      (nth *async-adder$lcntl* st))
       (?cntl       (nth *async-adder$cntl* st))
       (?lnext-cntl (nth *async-adder$lnext-cntl* st))
       (?next-cntl  (nth *async-adder$next-cntl* st))
       (?ldone-     (nth *async-adder$ldone-* st))
       (?done-      (nth *async-adder$done-* st))
       (?lresult    (nth *async-adder$lresult* st))
       (?result     (nth *async-adder$result* st))
       (serial-add  (nth *async-adder$serial-add* st))

       (?lreg0  (nth *serial-adder$lreg0* serial-add))
       (?reg0   (nth *serial-adder$reg0*  serial-add))
       (?lreg1  (nth *serial-adder$lreg1* serial-add))
       (?reg1   (nth *serial-adder$reg1*  serial-add))
       (?lreg2  (nth *serial-adder$lreg2* serial-add))
       (?reg2   (nth *serial-adder$reg2*  serial-add))
       (bit-add (nth *serial-adder$bit-add* serial-add))

       (?la  (nth *1-bit-adder$la* bit-add))
       (?a   (nth *1-bit-adder$a* bit-add))
       (?lb  (nth *1-bit-adder$lb* bit-add))
       (?b   (nth *1-bit-adder$b* bit-add))
       (?lci (nth *1-bit-adder$lci* bit-add))
       (?ci  (nth *1-bit-adder$ci* bit-add))
       (?ls  (nth *1-bit-adder$ls* bit-add))
       (?s   (nth *1-bit-adder$s* bit-add))
       (?lco (nth *1-bit-adder$lco* bit-add))
       (?co  (nth *1-bit-adder$co* bit-add)))
    (implies
     (and (equal count (1- *data-size*))
          (async-adder$st-trans-n inputs-seq count)
          (equal n (async-adder$st-trans-n->numsteps inputs-seq count))
          (async-adder$input-format-n inputs-seq n)
          (async-adder$init-st st))
     (equal (async-adder$run inputs-seq st n)
            (list
             '(nil)
             '((nil) (t) (t) (t) (t))
             '(t)
             '((nil) (nil) (nil) (nil) (nil))
             '(t)
             '(nil) ;; Done
             '(nil)
             (pairlis$ (v-threefix (strip-cars result))
                       nil)
             (list '(t)
                   (list (fv-shift-right-nil-n (car reg0) count))
                   '(t)
                   (list (fv-shift-right-nil-n (car reg1) count))
                   '(nil)
                   (list
                    (fv-serial-sum (car ci) (car reg0) (car reg1)
                                   count
                                   (car reg2)))
                   (list '(nil)
                         (list (car (fv-shift-right-nil-n
                                     (car reg0)
                                     (1- count))))
                         '(nil)
                         (list (car (fv-shift-right-nil-n
                                     (car reg1)
                                     (1- count))))
                         '(t)
                         (list (fv-serial-carry (car ci)
                                                (car reg0)
                                                (car reg1)
                                                count))
                         '(nil)
                         (list (f-xor3 (fv-serial-carry (car ci)
                                                        (car reg0)
                                                        (car reg1)
                                                        (1- count))
                                       (car (fv-shift-right-nil-n
                                             (car reg0)
                                             (1- count)))
                                       (car (fv-shift-right-nil-n
                                             (car reg1)
                                             (1- count)))))
                         '(nil)
                         (list (fv-serial-carry (car ci)
                                                (car reg0)
                                                (car reg1)
                                                count))))))))
  :hints (("Goal"
           :do-not-induct t
           :use simulate-async-adder-loop
           :in-theory (union-theories
                       '(async-adder$init-st
                         async-adder$init-st=>inv-st
                         v-to-nat
                         compute-done-
                         len-1-true-listp
                         len
                         bvp
                         posp
                         true-list-listp
                         booleanp
                         pairlis$
                         strip-cars
                         (f-nand4)
                         (next-cntl-state-n)
                         f-buf-of-car-fv-shift-right-nil-n-canceled)
                       (theory 'minimal-theory)))))

;; ======================================================================

;; Prove that the state of the async serial adder will eventually reach a fixed
;; point. We show that the result register stays empty until the fixed point is
;; reached. At that fixed point, the result register becomes full and its value
;; complies with the serial adder spec.

(defthm consp-fv-serial-sum
  (implies (consp acc)
           (consp (fv-serial-sum c a b n acc)))
  :hints (("Goal" :in-theory (enable fv-serial-sum)))
  :rule-classes :type-prescription)

(defthm true-listp-fv-serial-sum
  (implies (true-listp acc)
           (true-listp (fv-serial-sum c a b n acc)))
  :hints (("Goal" :in-theory (enable fv-serial-sum)))
  :rule-classes :type-prescription)

(defthm len-fv-serial-sum
  (equal (len (fv-serial-sum c a b n acc))
         (len acc))
  :hints (("Goal" :in-theory (enable fv-serial-sum))))

(defthm fv-serial-sum-simplified
  (implies (and (natp n)
                (consp a))
           (equal (fv-shift-right (fv-serial-sum c a b n acc)
                                  (f-xor3 (fv-serial-carry c a b n)
                                          (car (fv-shift-right-nil-n a n))
                                          (car (fv-shift-right-nil-n b n))))
                  (fv-serial-sum c a b (1+ n) acc)))
  :hints (("Goal"
           :in-theory (enable fv-serial-sum
                              fv-serial-carry
                              fv-shift-right-nil-n))))

(defthm f-buf-of-fv-serial-carry-canceled
  (implies (and (posp n)
                (consp a))
           (equal (f-buf (fv-serial-carry c a b n))
                  (fv-serial-carry c a b n)))
  :hints (("Goal" :in-theory (enable f-buf fv-serial-carry))))

(defthm fv-serial-carry-simplified
  (implies (and (natp n)
                (consp a))
           (equal (f-or (f-and (car (fv-shift-right-nil-n a n))
                               (car (fv-shift-right-nil-n b n)))
                        (f-and (f-xor (car (fv-shift-right-nil-n a n))
                                      (car (fv-shift-right-nil-n b n)))
                               (fv-serial-carry c a b n)))
                  (fv-serial-carry c a b (1+ n))))
  :hints (("Goal"
           :in-theory (enable fv-serial-carry
                              fv-shift-right-nil-n))))

(defund async-adder-interleavings (inputs-seq operand-size)
  (declare (xargs :guard (and (true-list-listp inputs-seq)
                              (posp operand-size))))
  (b* ((inv-steps (async-adder$st-trans-n->numsteps inputs-seq
                                                    (1- operand-size)))
       (remained-inputs-seq (nthcdr inv-steps inputs-seq)))
    (and (async-adder$st-trans-n inputs-seq (1- operand-size))
         (async-adder-last-round$st-trans remained-inputs-seq))))

(defund async-adder-numsteps (inputs-seq operand-size)
  (declare (xargs :guard (and (true-list-listp inputs-seq)
                              (posp operand-size))))
  (b* ((inv-steps (async-adder$st-trans-n->numsteps inputs-seq
                                                    (1- operand-size)))
       (remained-inputs-seq (nthcdr inv-steps inputs-seq)))
    (+ inv-steps
       (async-adder-last-round$st-trans->numsteps remained-inputs-seq))))

(defthmd simulate-async-adder-invalid-result
  (implies
   (and (equal operand-size *data-size*)
        (async-adder-interleavings inputs-seq operand-size)
        (equal n (async-adder-numsteps inputs-seq operand-size))
        (async-adder$input-format-n inputs-seq n)
        (async-adder$init-st st))
   (async-adder$result-empty-n inputs-seq st n))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (simulate-async-adder-loop-invalid-result-instance
                            simulate-async-adder-loop-instance
                            async-adder-last-round$invalid-result
                            async-adder-interleavings
                            async-adder-numsteps
                            async-adder$init-st
                            last-round-st)
                           (open-async-adder$result-empty-n
                            open-async-adder$input-format-n
                            open-async-adder$st-trans-n
                            open-async-adder$st-trans-n->numsteps
                            open-fv-shift-right-nil-n
                            open-fv-serial-sum
                            open-fv-serial-carry
                            open-v-threefix
                            fullp
                            emptyp
                            car-cdr-elim)))))

(defthmd simulate-async-adder-to-fixpoint
  (b* ((?lcntl      (nth *async-adder$lcntl* st))
       (?cntl       (nth *async-adder$cntl* st))
       (?lnext-cntl (nth *async-adder$lnext-cntl* st))
       (?next-cntl  (nth *async-adder$next-cntl* st))
       (?ldone-     (nth *async-adder$ldone-* st))
       (?done-      (nth *async-adder$done-* st))
       (?lresult    (nth *async-adder$lresult* st))
       (?result     (nth *async-adder$result* st))
       (serial-add  (nth *async-adder$serial-add* st))

       (?lreg0  (nth *serial-adder$lreg0* serial-add))
       (?reg0   (nth *serial-adder$reg0*  serial-add))
       (?lreg1  (nth *serial-adder$lreg1* serial-add))
       (?reg1   (nth *serial-adder$reg1*  serial-add))
       (?lreg2  (nth *serial-adder$lreg2* serial-add))
       (?reg2   (nth *serial-adder$reg2*  serial-add))
       (bit-add (nth *serial-adder$bit-add* serial-add))

       (?la  (nth *1-bit-adder$la* bit-add))
       (?a   (nth *1-bit-adder$a* bit-add))
       (?lb  (nth *1-bit-adder$lb* bit-add))
       (?b   (nth *1-bit-adder$b* bit-add))
       (?lci (nth *1-bit-adder$lci* bit-add))
       (?ci  (nth *1-bit-adder$ci* bit-add))
       (?ls  (nth *1-bit-adder$ls* bit-add))
       (?s   (nth *1-bit-adder$s* bit-add))
       (?lco (nth *1-bit-adder$lco* bit-add))
       (?co  (nth *1-bit-adder$co* bit-add)))
    (implies
     (and (equal operand-size *data-size*)
          (async-adder-interleavings inputs-seq operand-size)
          (natp n)
          (>= n (async-adder-numsteps inputs-seq operand-size))
          (async-adder$input-format-n inputs-seq n)
          (async-adder$init-st st))
     (equal (async-adder$run inputs-seq st n)
            (list
             '(nil)
             '((nil) (t) (t) (t) (t))
             '(t)
             '((nil) (nil) (nil) (nil) (nil))
             '(nil)
             '(nil) ;; Done
             '(t)
             ;; Final result
             (pairlis$
              (fv-serial-adder (car ci) (car reg0) (car reg1)
                               operand-size
                               (car reg2))
              nil)
             (list '(nil)
                   (list (fv-shift-right-nil-n (car reg0)
                                               (1- operand-size)))
                   '(nil)
                   (list (fv-shift-right-nil-n (car reg1)
                                               (1- operand-size)))
                   '(nil)
                   (list
                    (fv-serial-sum (car ci) (car reg0) (car reg1)
                                   operand-size
                                   (car reg2)))
                   (list '(nil)
                         (list (car (fv-shift-right-nil-n
                                     (car reg0)
                                     (1- operand-size))))
                         '(nil)
                         (list (car (fv-shift-right-nil-n
                                     (car reg1)
                                     (1- operand-size))))
                         '(nil)
                         ;; Carry
                         (list (fv-serial-carry (car ci)
                                                (car reg0)
                                                (car reg1)
                                                operand-size))
                         '(nil)
                         (list (f-xor3 (fv-serial-carry (car ci)
                                                        (car reg0)
                                                        (car reg1)
                                                        (1- operand-size))
                                       (car (fv-shift-right-nil-n
                                             (car reg0)
                                             (1- operand-size)))
                                       (car (fv-shift-right-nil-n
                                             (car reg1)
                                             (1- operand-size)))))
                         '(nil)
                         (list (fv-serial-carry (car ci)
                                                (car reg0)
                                                (car reg1)
                                                operand-size))))))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance
                  async-adder$run-plus
                  (m (async-adder$st-trans-n->numsteps
                      inputs-seq
                      (1- operand-size)))
                  (n (- n (async-adder$st-trans-n->numsteps
                           inputs-seq
                           (1- operand-size)))))
                 (:instance
                  async-adder$input-format-plus
                  (m (async-adder$st-trans-n->numsteps
                      inputs-seq
                      (1- operand-size)))
                  (n (- n (async-adder$st-trans-n->numsteps
                           inputs-seq
                           (1- operand-size))))))
           :in-theory (e/d (simulate-async-adder-loop-instance
                            async-adder$sim-last-round-to-fixpoint
                            async-adder$init-st
                            last-round-st
                            async-adder-interleavings
                            async-adder-numsteps
                            fv-serial-adder
                            pos-len=>consp)
                           (async-adder$run-plus
                            async-adder$input-format-plus
                            open-async-adder$run
                            open-async-adder$input-format-n
                            open-async-adder$st-trans-n
                            open-async-adder$st-trans-n->numsteps
                            open-fv-shift-right-nil-n
                            open-fv-serial-sum
                            open-fv-serial-carry
                            open-v-threefix
                            fullp
                            emptyp
                            car-cdr-elim)))))

;; ======================================================================

;; Prove (using GL) that the serial adder produces the same result with the
;; ripple-carry adder

(defthm v-to-nat-upper-bound
  (< (v-to-nat x)
     (expt 2 (len x)))
  :hints (("Goal" :in-theory (enable v-to-nat)))
  :rule-classes :linear)

(encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthm nat-to-v-of-v-to-nat
    (implies (and (bvp x)
                  (equal (len x) n))
             (equal (nat-to-v (v-to-nat x) n)
                    x))
    :hints (("Goal" :in-theory (enable bvp
                                       nat-to-v
                                       v-to-nat)))))

(encapsulate
  ()

  (local
   (def-gl-thm fv-serial-adder=fv-adder-32-aux
     :hyp (and (booleanp c)
               (natp a)
               (natp b)
               (natp acc)
               (< a (expt 2 32))
               (< b (expt 2 32))
               (< acc (expt 2 32)))
     :concl (equal (fv-serial-adder c (nat-to-v a 32) (nat-to-v b 32)
                                   32
                                   (nat-to-v acc 32))
                   (fv-adder c (nat-to-v a 32) (nat-to-v b 32)))
     :g-bindings `((c (:g-boolean . 0))
                   (a ,(gl::g-int 1 2 33))
                   (b ,(gl::g-int 2 2 33))
                   (acc ,(gl::g-int 67 1 33)))))

  (local
   (defthm v-to-nat-upper-bound-instance
     (implies (equal (len x) 32)
              (< (v-to-nat x) 4294967296))
     :hints (("Goal" :use v-to-nat-upper-bound))
     :rule-classes :linear))

  (defthm fv-serial-adder=fv-adder-32
    (implies (and (equal n 32)
                  (booleanp c)
                  (bvp a)
                  (equal (len a) n)
                  (bvp b)
                  (equal (len b) n)
                  (bvp acc)
                  (equal (len acc) n))
             (equal (fv-serial-adder c a b n acc)
                    (fv-adder c a b)))
    :hints (("Goal"
             :use (:instance fv-serial-adder=fv-adder-32-aux
                             (a (v-to-nat a))
                             (b (v-to-nat b))
                             (acc (v-to-nat acc))))))
  )

;; Prove that the async serial adder indeed performs the addition.

(defthmd async-adder$input-format-n-lemma
 (implies (and (async-adder$input-format-n inputs-seq n)
               (natp n)
               (<= m n))
          (async-adder$input-format-n inputs-seq m))
 :hints (("Goal" :in-theory (enable async-adder$input-format-n))))

(defthmd async-adder$empty-result
  (implies
   (and (async-adder& netlist)
        (equal operand-size *data-size*)
        (async-adder-interleavings inputs-seq operand-size)
        (natp m)
        (< m n)
        (equal n (async-adder-numsteps inputs-seq operand-size))
        (async-adder$input-format-n inputs-seq n)
        (async-adder$init-st st))
   (b* ((final-st (de-n 'async-adder inputs-seq st netlist m)))
     (emptyp (extract-async-adder-result-status final-st))))
  :hints (("Goal"
           :use async-adder$result-empty-n-lemma
           :in-theory (e/d (de-n$async-adder
                            async-adder$input-format-n-lemma
                            async-adder$init-st
                            simulate-async-adder-invalid-result)
                           (async-adder$result-empty-n-lemma
                            open-async-adder$result-empty-n
                            fullp
                            emptyp
                            open-de-n
                            open-async-adder$run
                            open-async-adder$input-format-n
                            car-cdr-elim)))))

;; Termination theorem

(defthmd async-adder$termination
  (b* ((serial-add (nth *async-adder$serial-add* st))

       (reg0 (nth *serial-adder$reg0* serial-add))
       (reg1 (nth *serial-adder$reg1* serial-add))
       (reg2 (nth *serial-adder$reg2* serial-add))
       (bit-add (nth *serial-adder$bit-add* serial-add))

       (ci (nth *1-bit-adder$ci* bit-add)))
    (implies
     (and (async-adder& netlist)
          (equal operand-size *data-size*)
          (async-adder-interleavings inputs-seq operand-size)
          (natp n)
          (>= n (async-adder-numsteps inputs-seq operand-size))
          (async-adder$input-format-n inputs-seq n)
          (async-adder$init-st st))
     (b* ((final-st (de-n 'async-adder inputs-seq st netlist n)))
       (and
        (fullp (extract-async-adder-result-status final-st)) ;; Terminate
        (implies (and (bvp (car reg0))
                      (bvp (car reg1))
                      (bvp (car reg2))
                      (booleanp (car ci)))
                 (equal (v-to-nat
                         (extract-async-adder-result-value final-st))
                        (+ (bool->bit (car ci))
                           (v-to-nat (car reg0))
                           (v-to-nat (car reg1)))))))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (de-n$async-adder
                            simulate-async-adder-to-fixpoint
                            extract-async-adder-result-status
                            extract-async-adder-result-value
                            async-adder$init-st)
                           (fullp
                            emptyp
                            open-de-n
                            open-async-adder$run
                            open-async-adder$input-format-n
                            open-fv-shift-right-nil-n
                            open-fv-serial-sum
                            open-fv-serial-carry
                            car-cdr-elim)))))

(encapsulate
  ()

  (local
   (defthm empty=>not-full
     (implies (emptyp x)
              (not (fullp x)))))

  ;; Partial correctness theorem

  (defthmd async-adder$partial-correct
    (b* ((serial-add (nth *async-adder$serial-add* st))

         (reg0 (nth *serial-adder$reg0* serial-add))
         (reg1 (nth *serial-adder$reg1* serial-add))
         (reg2 (nth *serial-adder$reg2* serial-add))
         (bit-add (nth *serial-adder$bit-add* serial-add))

         (ci (nth *1-bit-adder$ci* bit-add)))
      (implies
       (and (async-adder& netlist)
            (equal operand-size *data-size*)
            (async-adder-interleavings inputs-seq operand-size)
            (natp m)
            (equal n (async-adder-numsteps inputs-seq operand-size))
            (async-adder$input-format-n inputs-seq (max m n))
            (async-adder$init-st st))
       (b* ((final-st (de-n 'async-adder inputs-seq st netlist m)))
         (implies (and (fullp (extract-async-adder-result-status final-st))
                       (bvp (car reg0))
                       (bvp (car reg1))
                       (bvp (car reg2))
                       (booleanp (car ci)))
                  (equal (v-to-nat
                          (extract-async-adder-result-value final-st))
                         (+ (bool->bit (car ci))
                            (v-to-nat (car reg0))
                            (v-to-nat (car reg1))))))))
    :hints (("Goal"
             :cases ((< m n))
             :in-theory (e/d (async-adder$empty-result
                              async-adder$termination)
                             (fullp
                              emptyp
                              open-de-n
                              open-async-adder$run
                              open-async-adder$input-format-n
                              open-fv-shift-right-nil-n
                              open-fv-serial-sum
                              open-fv-serial-carry
                              car-cdr-elim))))))
