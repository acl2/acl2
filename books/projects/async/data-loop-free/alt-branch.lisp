;; Copyright (C) 2017, Regents of the University of Texas
;; Written by Cuong Chau
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; December 2017

(in-package "ADE")

(include-book "constants")
(include-book "link-joint")
(include-book "vector-module")

(local (in-theory (e/d (f-buf-delete-lemmas-1
                        f-buf-delete-lemmas-2)
                       (nth-of-bvp-is-booleanp
                        take-of-len-free))))

;; ======================================================================

;; Alternate branch

(defconst *alt-branch$data-ins-len* (+ 3 *data-width*))
(defconst *alt-branch$go-num* 2)
(defconst *alt-branch$ins-len* (+ *alt-branch$data-ins-len*
                              *alt-branch$go-num*))
(defconst *alt-branch$st-len* 4)

(module-generator
 alt-branch* ()
 'alt-branch
 (list* 'full-in 'full-out0- 'full-out1-
        (append (sis 'data-in 0 *data-width*)
                (sis 'go 0 *alt-branch$go-num*)))
 (list* 'act 'act0 'act1
        (sis 'data-out 0 *data-width*))
 '(ldemux demux ldemux-buf demux-buf)
 (list
  ;; LINKS
  ;; Demux
  '(ldemux (demux-status) link-cntl (buf-act act))
  '(demux (demux-out demux-out~) latch (buf-act demux-in))
  
  ;; Demux-buf
  '(ldemux-buf (demux-buf-status) link-cntl (act buf-act))
  '(demux-buf (demux-buf-out demux-buf-out~) latch (act demux-buf-in))

  ;; JOINTS
  ;; Alt-Branch
  '(g0 (ready-in) b-and (full-in demux-status))
  '(g1 (ready-out0-) b-or3 (full-out0- demux-buf-status demux-out))
  '(g2 (ready-out1-) b-or3 (full-out1- demux-buf-status demux-out~))
  (list 'alt-branch-cntl0
        '(act0)
        'joint-cntl
        (list 'ready-in 'ready-out0- (si 'go 0)))
  (list 'alt-branch-cntl1
        '(act1)
        'joint-cntl
        (list 'ready-in 'ready-out1- (si 'go 0)))
  '(alt-branch-cntl (act) b-or (act0 act1))
  
  (list 'alt-branch-op0
        (sis 'data-out 0 *data-width*)
        (si 'v-buf *data-width*)
        (sis 'data-in 0 *data-width*))
  '(alt-branch-op1 (demux-buf-in) b-not (demux-out))

  ;; Buffer
  (list 'buf-cntl
        '(buf-act)
        'joint-cntl
        (list 'demux-buf-status 'demux-status (si 'go 1)))
  '(buf-op (demux-in) b-buf (demux-buf-out)))

 :guard t)

(defun alt-branch$netlist ()
  (declare (xargs :guard t))
  (cons (alt-branch*)
        (union$ (v-buf$netlist *data-width*)
                *joint-cntl*
                :test 'equal)))

(defthmd alt-branch$netlist-okp
  (and (net-syntax-okp (alt-branch$netlist))
       (net-arity-okp (alt-branch$netlist))))

(defund alt-branch& (netlist)
  (declare (xargs :guard (alistp netlist)))
  (and (equal (assoc 'alt-branch netlist)
              (alt-branch*))
       (b* ((netlist (delete-to-eq 'alt-branch netlist)))
         (and (joint-cntl& netlist)
              (v-buf& netlist *data-width*)))))

(defthm check-alt-branch$netlist
  (alt-branch& (alt-branch$netlist)))

(defconst *alt-branch$ldemux*     0)
(defconst *alt-branch$demux*      1)
(defconst *alt-branch$ldemux-buf* 2)
(defconst *alt-branch$demux-buf*  3)

(defund alt-branch$valid-st (st)
  (b* ((ldemux     (get-field *alt-branch$ldemux* st))
       (demux      (get-field *alt-branch$demux* st))
       (ldemux-buf (get-field *alt-branch$ldemux-buf* st))
       (demux-buf  (get-field *alt-branch$demux-buf* st)))
    (and (validp ldemux)
         (booleanp (car demux))

         (validp ldemux-buf)
         (booleanp (car demux-buf)))))

(defun alt-branch$map-to-links (st)
  (b* ((ldemux (get-field *alt-branch$ldemux* st))
       (demux  (get-field *alt-branch$demux* st))
       (ldemux-buf (get-field *alt-branch$ldemux-buf* st))
       (demux-buf  (get-field *alt-branch$demux-buf* st)))
    (map-to-links (list (list 'demux ldemux (list demux))
                        (list 'demux-buf ldemux-buf (list demux-buf))))))

(defun alt-branch$map-to-links-list (x)
  (if (atom x)
      nil
    (cons (alt-branch$map-to-links (car x))
          (alt-branch$map-to-links-list (cdr x)))))

(defund alt-branch$sim (n state)
  (declare (xargs :guard (natp n)
                  :verify-guards nil
                  :stobjs state))
  (b* ((num-signals *alt-branch$ins-len*)
       ((mv inputs-lst state) (go-vals-gen num-signals n state nil))
       ;;(- (cw "~x0~%" inputs-lst))
       (full '(t))
       (empty '(nil))
       (st (list full '(nil)
                 empty '(x))))
    (mv (pretty-list
         (remove-dup-neighbors
          (alt-branch$map-to-links-list
           (de-sim-list 'alt-branch inputs-lst st (alt-branch$netlist))))
         0)
        state)))

(defun alt-branch$get-data-in (inputs)
  (declare (xargs :guard (true-listp inputs)))
  (subseq-list inputs 3 (+ 3 *data-width*)))

(defthm len-alt-branch$get-data-in
  (equal (len (alt-branch$get-data-in inputs))
         *data-width*))

(in-theory (disable alt-branch$get-data-in))

(defund alt-branch$act0 (inputs st)
  (b* ((full-in    (nth 0 inputs))
       (full-out0- (nth 1 inputs))
       (go-signals (nthcdr *alt-branch$data-ins-len* inputs))
       
       (go-alt-branch (nth 0 go-signals))
       
       (ldemux (get-field *alt-branch$ldemux* st))
       (demux  (get-field *alt-branch$demux* st))
       (ldemux-buf (get-field *alt-branch$ldemux-buf* st))
       
       (ready-in (f-and full-in (car ldemux)))
       (ready-out0- (f-or3 full-out0- (car ldemux-buf) (car demux))))
    
    (joint-act ready-in ready-out0- go-alt-branch)))

(defund alt-branch$act1 (inputs st)
  (b* ((full-in    (nth 0 inputs))
       (full-out1- (nth 2 inputs))
       (go-signals (nthcdr *alt-branch$data-ins-len* inputs))
       
       (go-alt-branch (nth 0 go-signals))
       
       (ldemux (get-field *alt-branch$ldemux* st))
       (demux  (get-field *alt-branch$demux* st))
       (ldemux-buf (get-field *alt-branch$ldemux-buf* st))
       
       (ready-in (f-and full-in (car ldemux)))
       (ready-out1- (f-or3 full-out1-
                           (car ldemux-buf)
                           (f-not (car demux)))))
    
    (joint-act ready-in ready-out1- go-alt-branch)))

(defund alt-branch$act (inputs st)
  (f-or (alt-branch$act0 inputs st)
        (alt-branch$act1 inputs st)))

(defthmd alt-branch$value
  (b* ((inputs (list* full-in full-out0- full-out1-
                      (append data-in go-signals))))
    (implies (and (alt-branch& netlist)
                  (true-listp data-in)
                  (equal (len data-in) *data-width*)
                  (true-listp go-signals)
                  (equal (len go-signals) *alt-branch$go-num*)
                  (alt-branch$valid-st st))
             (equal (se 'alt-branch inputs st netlist)
                    (list* (alt-branch$act inputs st)
                           (alt-branch$act0 inputs st)
                           (alt-branch$act1 inputs st)
                           (v-threefix data-in)))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (se-rules
                            get-field
                            alt-branch&
                            alt-branch*$destructure
                            joint-cntl$value
                            v-buf$value
                            open-nth
                            alt-branch$valid-st
                            alt-branch$act
                            alt-branch$act0
                            alt-branch$act1)
                           ((alt-branch*)
                            (si)
                            (sis)
                            validp
                            open-v-threefix
                            tv-disabled-rules)))))

(defun alt-branch$state-fn (inputs st)
  (b* ((go-signals (nthcdr *alt-branch$data-ins-len* inputs))

       (go-buf (nth 1 go-signals))
       
       (ldemux (get-field *alt-branch$ldemux* st))
       (demux  (get-field *alt-branch$demux* st))
       (ldemux-buf (get-field *alt-branch$ldemux-buf* st))
       (demux-buf  (get-field *alt-branch$demux-buf* st))

       (act (alt-branch$act inputs st))
       (buf-act (joint-act (car ldemux-buf) (car ldemux) go-buf)))
    (list
     (list (f-sr buf-act act (car ldemux)))
     (list (f-if buf-act (car demux-buf) (car demux)))

     (list (f-sr act buf-act (car ldemux-buf)))
     (list (f-if act (f-not (car demux)) (car demux-buf))))))

(defthm len-of-alt-branch$state-fn
  (equal (len (alt-branch$state-fn inputs st))
         *alt-branch$st-len*))

(defthmd alt-branch$state
  (b* ((inputs (list* full-in full-out0- full-out1-
                      (append data-in go-signals))))
    (implies (and (alt-branch& netlist)
                  (equal (len data-in) *data-width*)
                  (true-listp go-signals)
                  (equal (len go-signals) *alt-branch$go-num*)
                  (alt-branch$valid-st st))
             (equal (de 'alt-branch inputs st netlist)
                    (alt-branch$state-fn inputs st))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (de-rules
                            get-field
                            alt-branch&
                            alt-branch*$destructure
                            alt-branch$valid-st
                            alt-branch$act
                            alt-branch$act0
                            alt-branch$act1
                            open-nth
                            joint-cntl$value
                            v-buf$value)
                           ((alt-branch*)
                            (si)
                            (sis)
                            validp
                            open-v-threefix
                            tv-disabled-rules)))))

(in-theory (disable alt-branch$state-fn))

;; ======================================================================

(defund alt-branch$input-format (inputs)
  (declare (xargs :guard (true-listp inputs)))
  (b* ((full-in    (nth 0 inputs))
       (full-out0- (nth 1 inputs))
       (full-out1- (nth 2 inputs))
       (data-in    (alt-branch$get-data-in inputs))
       (go-signals (nthcdr *alt-branch$data-ins-len* inputs)))
    (and
     (booleanp full-in)
     (booleanp full-out0-)
     (booleanp full-out1-)
     (bvp data-in)
     (true-listp go-signals)
     (= (len go-signals) *alt-branch$go-num*)
     (equal inputs
            (list* full-in full-out0- full-out1-
                   (append data-in go-signals))))))

(defthm alt-branch$valid-st-preserved
  (implies (and (alt-branch$input-format inputs)
                (alt-branch$valid-st st))
           (alt-branch$valid-st (alt-branch$state-fn inputs st)))
  :hints (("Goal"
           :in-theory (e/d (get-field
                            alt-branch$input-format
                            alt-branch$valid-st
                            alt-branch$state-fn
                            alt-branch$act
                            alt-branch$act0
                            alt-branch$act1
                            f-sr)
                           (if*
                            nth
                            nthcdr
                            acl2::true-listp-append)))))

(defund alt-branch$inv (st)
  (b* ((ldemux     (get-field *alt-branch$ldemux* st))
       (ldemux-buf (get-field *alt-branch$ldemux-buf* st)))
    (not (equal ldemux ldemux-buf))))

(defthm alt-branch$inv-preserved
  (implies (and (alt-branch$input-format inputs)
                (alt-branch$valid-st st)
                (alt-branch$inv st))
           (alt-branch$inv (alt-branch$state-fn inputs st)))
  :hints (("Goal"
           :in-theory (e/d (get-field
                            alt-branch$input-format
                            alt-branch$valid-st
                            alt-branch$inv
                            alt-branch$state-fn
                            alt-branch$act
                            alt-branch$act0
                            alt-branch$act1
                            f-sr)
                           (if*
                            nth
                            nthcdr
                            acl2::true-listp-append)))))

