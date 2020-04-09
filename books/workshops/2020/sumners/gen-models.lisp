; Copyright (C) 2020, Rob Sumners
; Written by Rob Sumners
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

;; In this book, we include the finite set GL and build the graphs we use to
;; check for cycles..

(include-book "gl-fin-set")
(include-book "cycle-check")

(defconst *src-var*  'src$)
(defconst *dst-var*  'dst$)
(defconst *top-var*  'top$)

(fty::defalist ord-tagging
  :key-type ord-p
  :val-type ord-tag-p
  :short "a mapping from ord-p values to symbols-- either :<<, t, or nil"
  :true-listp t)

(fty::defalist arc-label
  :key-type node-p
  :val-type ord-tagging-p
  :short "a mapping of dest nodes to ord-tagging for this arc"
  :true-listp t)
  
(fty::defalist ord-graph
  :key-type node-p
  :val-type arc-label-p
  :short "a mapping of source nodes to a list of dest node to ord sets"
  :true-listp t)

(fty::defalist node-bind
  :key-type symbolp
  :val-type node-p
  :short "a binding of variable symbols to nodes used in term substitutions"
  :true-listp t)

(fty::defalist ord-term-map
  :key-type ord-p
  :val-type pseudo-termp
  :short "a mapping from ords to terms defining what to compute for the ordering"
  :true-listp t)

(make-alist-thms ord-tagging-p ord-tag-p)
(make-alist-thms arc-label-p   ord-tagging-p)
(make-alist-thms ord-graph-p   arc-label-p)
(make-alist-thms node-bind-p   node-p)

;;;;;;;

(define check-arc-ord-tagging ((src node-p) (dst node-p) (ord ord-p) 
                               (o-g ord-graph-p))
  :returns (r ord-tag-p)
  (b* ((look1 (hons-get src o-g))
       ((unless look1)
        (raise "did not find source node in arc lookup:~x0" src))
       (look2 (assoc-hons-equal dst (cdr look1)))
       ((unless look2)
        (raise "did not find dest node in arc lookup:~x0" dst))
       (look3 (assoc-hons-equal ord (cdr look2))))
    (ord-tag-fix (and look3 (cdr look3)))))

;;;;;;;

(encapsulate
  (((get-var-shp *) => *))
  (local (defun get-var-shp (x)
           (declare (ignore x))
           nil))
  (defthm get-var-shp-returns-shape-spec
    (gl::shape-specp (get-var-shp x))))

(define get-var-shps (vars)
  :returns (r gl::shape-spec-bindingsp)
  (cond ((atom vars) ())
        ((not (gl::variablep (first vars)))
         (raise "unexpected illegal variable for GL:~x0" (first vars)))
        (t
         (cons (list (first vars)
                     (get-var-shp (first vars)))
               (get-var-shps (rest vars))))))

(local (defthm shape-spec-bindings-are-alists
         (implies (gl::shape-spec-bindingsp x)
                  (alistp x))
         :hints (("Goal" :in-theory (enable alistp gl::shape-spec-bindingsp)))))

(define replace-node-vars ((vars symbol-listp) (n-b node-bind-p))
  (if (endp vars) ()
    (b* ((var (first vars))
         (look (assoc-eq var n-b)))
      (cons (if look `(quote ,(cdr look)) var)
            (replace-node-vars (rest vars) n-b)))))

(define node-bind-isect ((n-b node-bind-p) (vars symbol-listp))
  (and (consp n-b)
       (or (member-eq (caar n-b) vars)
           (node-bind-isect (cdr n-b) vars))))

(define remove-node-bind ((n-b node-bind-p) (vars symbol-listp))
  :returns (r symbol-listp :hyp (symbol-listp vars))
  :verify-guards nil
  (if (endp n-b) vars
    (remove-node-bind (cdr n-b) (remove-eq (caar n-b) vars))))

(verify-guards remove-node-bind)

(define nodes-from-graph ((g graph-p) &key ((r arcs-p) '()))
  :returns (r arcs-p)
  (if (endp g) (arcs-fix r)
    (nodes-from-graph (rest g) :r (cons (caar g) r))))

(define comp-map-call ((hyp pseudo-termp)
                       (trm pseudo-termp)
                       (n-b node-bind-p)
                       (max-count natp)
                       &key
                       (state 'state))
  (b* ((hyp-vars (all-vars hyp))
       (trm-vars (all-vars trm))
       ((when (not (and (symbol-listp hyp-vars)
                        (symbol-listp trm-vars))))
        (mv (raise "internal error.. should get symbol-lists!!") state))
       ((mv hyp hyp-vars)
        (if (node-bind-isect n-b hyp-vars)
            (mv `((lambda ,hyp-vars ,hyp) ,@(replace-node-vars hyp-vars n-b))
                (remove-node-bind n-b hyp-vars))
          (mv hyp hyp-vars)))
       ((mv trm trm-vars)
        (if (node-bind-isect n-b trm-vars)
            (mv `((lambda ,trm-vars ,trm) ,@(replace-node-vars trm-vars n-b))
                (remove-node-bind n-b trm-vars))
          (mv trm trm-vars)))
       ((when (not (and (pseudo-termp hyp)
                        (pseudo-termp trm))))
        (mv (raise "internal error.. should get pseudo-terms!!") state))
       (g-b (get-var-shps (union-eq hyp-vars trm-vars)))
       ((when (assoc-eq *top-var* g-b))
        (mv (raise "cannot bind top-var name ~x0 in terms" *top-var*) state))
       ((mv is-total rslt state)
        (gl::compute-finite-values trm hyp g-b max-count
                                   :top-var *top-var*))
       ((unless is-total)
        (mv (raise "exceeded maximum width of abstract graph!") state)))
    (mv rslt state)))

;;;;;;

(define make-into-nodes (l &key ((r arcs-p) '()))
  :returns (r arcs-p)
  (cond ((atom l) (arcs-fix r))
        ((atom (car l))
         (raise "expected rslt-bindings format from compute-finite-set!"))
        (t
         (make-into-nodes (rest l)
                          :r (cons (node-fix (hons-copy (caar l))) r)))))

(define make-into-ord-tag (l &key ((r natp) '0))
  :returns (r ord-tag-p :hyp :guard)
  (cond ((atom l)
         (cond ((eql r 0) nil)
               ((eql r 1) :<<)
               ((eql r 2) t)
               (t nil)))
        ((or (atom (car l))
             (not (natp (caar l))))
         (raise "expected ord-tag result from compute-finite-set: ~x0"
                (car l)))
        (t
         (make-into-ord-tag (cdr l)
                            :r (if (< r (caar l)) (caar l) r)))))

(define comp-map-step ((hyp pseudo-termp)
                       (trm pseudo-termp)
                       (node node-p)
                       &key
                       ((max-width natp) 'max-width)
                       (state 'state))
  :returns (mv (r arcs-p) state)
  (b* (((mv rslt state)
        (comp-map-call hyp trm
                       (list (cons *src-var* node))
                       max-width)))
    (mv (make-into-nodes rslt) state)))

(define comp-map-arc ((hyp pseudo-termp)
                      (trm pseudo-termp)
                      (src node-p) (dst node-p)
                      &key
                      ((max-width natp) 'max-width)
                      (state 'state))
  :returns (mv (r arcs-p) state)
  (b* (((mv rslt state)
        (comp-map-call hyp trm
                       (list (cons *src-var* src)
                             (cons *dst-var* dst))
                       max-width)))
    (mv (make-into-nodes rslt) state)))

(define comp-map-arc-ord ((src node-p) (dst node-p)
                          (hyp pseudo-termp)
                          (trm pseudo-termp)
                          &key
                          ((max-ords natp)  'max-ords)
                          (state            'state))
  :returns (mv (r ord-tag-p) state)
  (b* (((mv rslt state)
        (comp-map-call hyp trm
                       (list (cons *src-var* src)
                             (cons *dst-var* dst))
                       max-ords)))
    (mv (make-into-ord-tag rslt) state)))

;;;;;;

(define add-new-to-visit ((x arcs-p) (g graph-p) (r arcs-p))
  :returns (r arcs-p)
  (if (endp x) (arcs-fix r)
    (add-new-to-visit (rest x) g
                      (if (graph-get (first x) g) r (cons (first x) r)))))

(define comp-map-reach* ((step-hyp pseudo-termp)
                         (step-trm pseudo-termp)
                         &key
                         ((visit arcs-p)   'visit)
                         ((g graph-p)      '())
                         ((max-width natp) 'max-width)
                         ((max-nodes natp) 'max-nodes)
                         (state            'state))
  :measure (nfix max-nodes)
  :returns (mv (r graph-p) state)
  (cond 
   ((endp visit) 
    (mv (graph-fix g) state))
   ((zp max-nodes)
    (mv (raise "exceeded maximum depth in abstract graph!") state))
   (t
    (b* ((node (first visit))
         ((mv arcs state)
          (comp-map-step step-hyp step-trm node))
         (visit (add-new-to-visit arcs g (rest visit)))
         (g (graph-set node arcs g)))
      (comp-map-reach* step-hyp step-trm
                       :g g 
                       :max-nodes (1- max-nodes))))))

(define comp-map-arcs ((dsts arcs-p)
                       (src node-p)
                       (blok-hyp pseudo-termp)
                       (blok-trm pseudo-termp)
                       &key
                       ((r arcs-p)       '())
                       ((max-width natp) 'max-width)
                       (state            'state))
  :returns (mv (r arcs-p) state)
  :verify-guards nil
  (if (endp dsts) (mv (arcs-fix r) state)
    (b* ((dst (first dsts))
         ((mv arcs state)
          (comp-map-arc blok-hyp blok-trm src dst))
         (r (append arcs r)))
        (comp-map-arcs (rest dsts) src blok-hyp blok-trm :r r))))

(local (defthm arcs-p-is-true-listp
         (implies (arcs-p x) (true-listp x))
         :hints (("Goal" :in-theory (enable arcs-p)))))

(verify-guards comp-map-arcs-fn)

(define comp-map-blok* ((nodes arcs-p)
                        (blok-hyp pseudo-termp)
                        (blok-trm pseudo-termp)
                        (top arcs-p)
                        &key
                        ((r graph-p)      '())
                        ((max-width natp) 'max-width)
                        (state            'state))
  :measure (len nodes)
  :returns (mv (r graph-p) state)
  (if (endp nodes) (mv (graph-fix r) state)
    (b* ((src  (first nodes))
         ((mv arcs state)
          (comp-map-arcs top src blok-hyp blok-trm))
         (r (graph-set src arcs r)))
      (comp-map-blok* (rest nodes) blok-hyp blok-trm top :r r))))

(define comp-map-arc-ords ((src node-p) (dst node-p) 
                           (ordr-hyp pseudo-termp)
                           (ordr-trms ord-term-map-p)
                           &key
                           ((r ord-tagging-p) '())
                           ((max-ords natp)   'max-ords)
                           (state             'state))
  :measure (len ordr-trms)
  :returns (mv (r ord-tagging-p) state)
  (if (endp ordr-trms) (mv (ord-tagging-fix r) state)
    (b* ((ord (caar ordr-trms))
         (ordr-trm (cdar ordr-trms))
         ((mv o-t state)
          (comp-map-arc-ord src dst ordr-hyp ordr-trm))
         (r (cons (cons ord o-t) r)))
      (comp-map-arc-ords src dst ordr-hyp (rest ordr-trms) :r r))))

(define comp-map-arcs-ords ((dsts arcs-p) (src node-p)
                            (ordr-hyp pseudo-termp)
                            (ordr-trms ord-term-map-p)
                            &key
                            ((r arc-label-p)  '())
                            ((max-ords natp)  'max-ords)
                            (state            'state))
  :measure (len dsts)
  :returns (mv (r arc-label-p) state)
  (if (endp dsts) (mv (arc-label-fix r) state)
    (b* ((dst (first dsts))
         ((mv o-s state)
          (comp-map-arc-ords src dst ordr-hyp ordr-trms))
         (r (cons (cons dst o-s) r)))
      (comp-map-arcs-ords (rest dsts) src ordr-hyp ordr-trms :r r))))

(define comp-map-order* ((g graph-p)
                         (ordr-hyp pseudo-termp)
                         (ordr-trms ord-term-map-p)
                         &key
                         ((r ord-graph-p)  '())
                         ((max-ords natp)  'max-ords)
                         (state            'state))
  :measure (len g)
  :returns (mv (r ord-graph-p) state)
  (if (endp g) (mv (ord-graph-fix r) state)
    (b* ((src  (caar g))
         (dsts (cdar g))
         ((mv a-l state)
          (comp-map-arcs-ords dsts src ordr-hyp ordr-trms))
         (r (hons-acons src a-l r)))
      (comp-map-order* (cdr g) ordr-hyp ordr-trms :r r))))

;;;;;;

;; I don't like going into program mode.. but necessary to get macroexpansion and translation:
(defun acl2-expand-trans (x state)
  (declare (xargs :mode :program
                  :stobjs state))
  (mv-let (erp x+)
      (acl2::macroexpand1*-cmp x 'acl2-expand-trans (w state) (default-state-vars nil))
    (if erp (mv erp x+)
      (acl2::translate-cmp x+ t t t 'acl2-expand-trans (w state) (default-state-vars nil)))))

(defun acl2-expand-trans-alst (x state)
  (declare (xargs :mode :program
                  :stobjs state))
  (cond ((atom x) (mv nil ()))
        ((atom (car x)) (mv "ill-formed ord-map incoming!" (car x)))
        (t (mv-let (erp fst) (acl2-expand-trans (cdar x) state)
             (if erp (mv erp fst)
               (mv-let (erp rst) (acl2-expand-trans-alst (cdr x) state)
                 (if erp (mv erp rst)
                   (mv nil (cons (cons (caar x) fst) rst)))))))))

(defun ord-term-map-termsp (x state)
  (declare (xargs :mode :program
                  :stobjs state))
  (or (null x)
      (and (consp x)
           (consp (car x))
           (ord-p (caar x))
           (termp (cdar x) (w state))
           (ord-term-map-termsp (cdr x) state))))

(defun comp-map-reach-fn (init-hyp init-trm step-hyp step-trm max-width max-nodes state)
  (declare (xargs :mode :program
                  :stobjs state))
  (b* ((__function__ 'comp-map-reach-fn) ;; needed for 'raise below:
       ((mv erp init-hyp+) (acl2-expand-trans init-hyp state))
       ((when erp)
        (mv (raise "error occured in macroexpansion/translation:~x0:~x1" erp init-hyp) state))
       ((mv erp init-trm+) (acl2-expand-trans init-trm state))
       ((when erp)
        (mv (raise "error occured in macroexpansion/translation:~x0:~x1" erp init-trm) state))
       ((mv erp step-hyp+) (acl2-expand-trans step-hyp state))
       ((when erp)
        (mv (raise "error occured in macroexpansion/translation:~x0:~x1" erp step-hyp) state))
       ((mv erp step-trm+) (acl2-expand-trans step-trm state))
       ((when erp)
        (mv (raise "error occured in macroexpansion/translation:~x0:~x1" erp step-trm) state))
       ((unless (plist-worldp-with-formals (w state)))
        (mv (raise "world does not satisfy pre-req for termp") state))
       ((unless (termp init-hyp+ (w state)))
        (mv (raise "init-hyp does not expand to termp:~x0" init-hyp+) state))
       ((unless (termp init-trm+ (w state)))
        (mv (raise "init-trm does not expand to termp:~x0" init-trm+) state))
       ((unless (termp step-hyp+ (w state)))
        (mv (raise "step-hyp does not expand to termp:~x0" step-hyp+) state))
       ((unless (termp step-trm+ (w state)))
        (mv (raise "step-trm does not expand to termp:~x0" step-trm+) state))
       ((mv visit state)
        (comp-map-step init-hyp+ init-trm+ nil)))
    (comp-map-reach* step-hyp+ step-trm+)))

(defmacro comp-map-reach (&key init-hyp init-trm step-hyp step-trm max-width max-nodes)
  `(comp-map-reach-fn ,init-hyp ,init-trm ,step-hyp ,step-trm
                      ,(nfix (or max-width 1000))
                      ,(nfix (or max-nodes 10000))
                      state))

(defun comp-map-blok-fn (reach blok-hyp blok-trm max-width state)
  (declare (xargs :mode :program
                  :stobjs state))
  (b* ((__function__ 'comp-map-blok-fn) ;; needed for 'raise below:
       ((unless (graph-p reach))
        (mv (raise "incoming reach set is not graph-p") state))
       (nodes (nodes-from-graph reach))
       ((mv erp blok-hyp+) (acl2-expand-trans blok-hyp state))
       ((when erp)
        (mv (raise "error occured in macroexpansion/translation:~x0:~x1" erp blok-hyp) state))
       ((mv erp blok-trm+) (acl2-expand-trans blok-trm state))
       ((when erp)
        (mv (raise "error occured in macroexpansion/translation:~x0:~x1" erp blok-trm) state))
       ((unless (plist-worldp-with-formals (w state)))
        (mv (raise "world does not satisfy pre-req for termp") state))
       ((unless (termp blok-hyp+ (w state)))
        (mv (raise "blok-hyp does not expand to termp:~x0" blok-hyp+) state))
       ((unless (termp blok-trm+ (w state)))
        (mv (raise "blok-trm does not expand to termp:~x0" blok-trm+) state)))
    (comp-map-blok* nodes blok-hyp+ blok-trm+ nodes)))

(defmacro comp-map-blok (&key reach blok-hyp blok-trm max-width)
  `(comp-map-blok-fn ,reach ,blok-hyp ,blok-trm 
                     ,(nfix (or max-width 100)) ;; BOZO -- probably just 1 or 2 here given
                                                ;; how we have set this up...
                     state))

(defun comp-map-order-fn (reach ordr-hyp ordr-trms max-ords state)
  (declare (xargs :mode :program
                  :stobjs state))
  (b* ((__function__ 'comp-map-order-fn) ;; needed for 'raise below:
       ((unless (graph-p reach))
        (mv (raise "incoming reach set is not graph-p") state))
       ((mv erp ordr-hyp+) (acl2-expand-trans ordr-hyp state))
       ((when erp)
        (mv (raise "error occured in macroexpansion/translation:~x0:~x1" erp ordr-hyp) state))
       ((mv erp ordr-trms+) (acl2-expand-trans-alst ordr-trms state))
       ((when erp)
        (mv (raise "error occured in macroexpansion/translation:~x0:~x1" erp ordr-trms) state))
       ((unless (plist-worldp-with-formals (w state)))
        (mv (raise "world does not satisfy pre-req for termp") state))
       ((unless (termp ordr-hyp+ (w state)))
        (mv (raise "ordr-hyp does not expand to termp:~x0" ordr-hyp+) state))
       ((unless (ord-term-map-termsp ordr-trms+ state))
        (mv (raise "ordr-trms does not expand to all termp:~x0" ordr-trms+) state)))
    (comp-map-order* reach ordr-hyp+ ordr-trms+)))

(defmacro comp-map-order (&key reach ordr-hyp ordr-trms max-ords)
  `(comp-map-order-fn ,reach ,ordr-hyp ,ordr-trms 
                      ,(nfix (or max-ords 1000))
                      state))




