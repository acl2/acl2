

(in-package "GL")

(include-book "glmc")
(include-book "bfr-mcheck-abc")
(include-book "centaur/gl/bfr-satlink" :dir :system)

; cert_param: (hons-only)
; cert_param: (uses-glucose)
; cert_param: (uses-abc)

(bfr-mcheck-use-abc-simple)
(gl-satlink-mode)
(value-triple (acl2::tshell-start))

(local
 (progn
   (defun my-glucose-config ()
     (declare (xargs :guard t))
     (satlink::make-config :cmdline "glucose"
                           :verbose t
                           :mintime 1/2
                           :remove-temps t))

   (defattach gl::gl-satlink-config my-glucose-config)))

(defun my-nextst (st incr reset)
  (b* (((when reset) 0)
       (st (lnfix st))
       ((unless incr) st)
       (next (1+ st))
       ((when (eql next 10)) 0))
    next))

(defund my-run-prop (st ins)
  (declare (xargs :measure (len ins)))
  (if (atom ins)
      t
    (and (not (equal st 14))
         (my-run-prop (my-nextst st (caar ins) (cdar ins)) (cdr ins)))))


(define my-gl-abc-mcheck-script ((input-fname stringp) (ctrex-fname stringp))
  :returns (script stringp :rule-classes :type-prescription)
  (concatenate 'string
               "&r " input-fname "
                &put
                dprove -v -j -V 1
                print_status
                write_cex " ctrex-fname))

(defattach gl-abc-mcheck-script my-gl-abc-mcheck-script)

(defthm my-run-prop-correct
  (implies (and (natp st)
                (< st 5))
           (my-run-prop st ins))
  :hints ((glmc-hint
           ;; :side-goals t
           :shape-spec-bindings `((incr ,(g-var 'incr))
                                  (reset ,(g-var 'reset))
                                  (st ,(g-int 0 1 5)))
           :state-var st
           :initstatep (< st 5)
           :nextstate (my-nextst st incr reset)
           :frame-input-bindings ((incr (caar ins))
                                  (reset (cdar ins)))
           :rest-of-input-bindings ((ins (cdr ins)))
           :end-of-inputsp (atom ins)
           :measure (len ins)
           :run (my-run-prop st ins)
           :state-hyp (and (natp st) (< st 16))
           :prop (not (equal st 14))
           :run-check-hints ('(:expand ((my-run-prop st ins)))))))

(defun bool-pair-listp (x)
  (if (atom x)
      t
    (and (consp (car x))
         (booleanp (caar x))
         (booleanp (cdar x))
         (bool-pair-listp (cdr x)))))

(defthm my-run-prop-correct-bool-pairs
  (implies (and (natp st)
                (< st 5)
                (bool-pair-listp ins))
           (my-run-prop st ins))
  :hints ((glmc-hint
           ;; :side-goals t
           :shape-spec-bindings `((incr ,(g-boolean 0))
                                  (reset ,(g-boolean 1))
                                  (st ,(g-int 2 1 5)))
           :state-var st
           :initstatep (< st 5)
           :nextstate (my-nextst st incr reset)
           :frame-input-bindings ((incr (caar ins))
                                  (reset (cdar ins)))
           :rest-of-input-bindings ((ins (cdr ins)))
           :end-of-inputsp (atom ins)
           :measure (len ins)
           :run (implies (bool-pair-listp ins)
                         (my-run-prop st ins))
           :state-hyp (and (natp st) (< st 16))
           :input-hyp (and (booleanp incr) (booleanp reset))
           :prop (not (equal st 14))
           :run-check-hints ('(:expand ((my-run-prop st ins)))))))

(defthm my-run-prop-correct-raw
  (implies (and (natp st)
                (< st 5))
           (my-run-prop st ins))
  :hints (("goal" :clause-processor
           (test-glmc
            ; glmc-side-goals
            clause
            (make-glmc-config
             :glcp-config (make-glcp-config
                           :shape-spec-alist
                           `((incr ,(g-var 'incr))
                             (reset ,(g-var 'reset))
                             (st ,(g-int 0 1 5))))
                             
             :st-var 'st
             :in-vars '(ins)
             :frame-in-vars '(incr reset)
             :frame-ins '((car (car ins))
                          (cdr (car ins)))
             :rest-ins '((cdr ins))
             :end-ins '(not (consp ins))
             :in-measure '(len ins)
             :run '(my-run-prop st ins)
             :st-hyp '(if (natp st) (< st '16) 'nil)
             :in-hyp ''t
             :initstp '(< st '10)
             :nextst '(my-nextst st incr reset)
             :constr ''t
             :prop '(not (equal st '14))
             :st-hyp-method :mcheck)
            state)
           :do-not-induct t)
          (and stable-under-simplificationp
               '(:expand ((my-run-prop st ins))))))



(defund my-run-prop-nths (st frame nframes ins)
  (declare (xargs :measure (nfix (- (nfix nframes) (nfix frame)))))
  (if (zp (- (nfix nframes) (nfix frame)))
      t
    (and (not (equal st 14))
         (let ((in (nth frame ins)))
           (my-run-prop-nths (my-nextst st (car in) (cdr in))
                             (+ 1 (nfix frame)) nframes ins)))))

(defthm my-run-prop-correct-nths
  (implies (and (natp st)
                (< st 5))
           (my-run-prop-nths st frame nframes ins))
  :hints ((glmc-hint
           ;; :side-goals t
           :shape-spec-bindings `((incr ,(g-var 'incr))
                                  (reset ,(g-var 'reset))
                                  (st ,(g-int 0 1 5)))
           :state-var st
           :initstatep (< st 5)
           :nextstate (my-nextst st incr reset)
           :frame-input-bindings ((incr (car (nth frame ins)))
                                  (reset (cdr (nth frame ins))))
           :rest-of-input-bindings ((frame (+ 1 (nfix frame)))
                                    (nframes nframes)
                                    (ins ins))
           :end-of-inputsp (zp (- (nfix nframes) (nfix frame)))
           :measure (nfix (- (nfix nframes) (nfix frame)))
           :run (my-run-prop-nths st frame nframes ins)
           :state-hyp (and (natp st) (< st 16))
           :prop (not (equal st 14))
           :run-check-hints ('(:expand ((my-run-prop-nths st frame nframes ins)))))))
