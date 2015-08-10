
(in-package "ACL2")


(defthm nth-out-of-range
  (implies (<= (len lst) (nfix n))
           (not (nth n lst))))

(defthm len-resize-list
  (equal (len (resize-list lst n default))
         (nfix n)))

(defun nth-rsz-induction (n len lst)
  (if (or (zp n) (zp len))
      lst
    (nth-rsz-induction (1- n) (1- len)
                       (if (consp lst) (cdr lst) lst))))


(defthm nth-resize-list-nil
  (implies (<= (nfix len) (nfix n))
           (equal (nth n (resize-list lst len default)) nil))
  :hints (("goal" :induct (nth-rsz-induction n len lst))))

(defthm nth-resize-list
  (equal (nth n (resize-list lst len default))
         (and (< (nfix n) (nfix len))
              (if (< (nfix n) (len lst))
                  (nth n lst)
                default)))
  :hints (("goal" :induct (nth-rsz-induction n len lst)
           :in-theory (enable zp len))
          ("Subgoal *1/1"
           :expand ((resize-list lst len default)
                    (len lst)))))

(defun nth-make-list-ac-ind (m n)
  (if (or (zp m) (zp n))
      nil
    (nth-make-list-ac-ind (1- m) (1- n))))

(defthmd make-list-ac-open
  (implies (not (zp n))
           (equal (make-list-ac n elt tail)
                  (cons elt (make-list-ac (1- n) elt tail)))))

(encapsulate
 nil
 (local (include-book "arithmetic-5/top" :dir :system))
 (defthm nth-make-list-ac
   ;; JCD changed names to match data-structures/list-defthms
   (equal (nth i (make-list-ac j val ac))
          (if (< (nfix i) (nfix j))
              val (nth (- i (nfix j)) ac)))
   :hints (("goal" :induct (nth-make-list-ac-ind i j)
            :in-theory (enable make-list-ac-open)))))

(include-book "misc/simplify-thm" :dir :system)

(program) (set-state-ok t)

(defun array-specp (spec)
  (let ((type (cadr (assoc-keyword :type (cdr spec)))))
    (and (consp type)
         (eq (car type) 'array))))

(defun ht-specp (spec)
  (let ((type (cadr (assoc-keyword :type (cdr spec)))))
    (and (consp type)
         (eq (car type) 'hash-table))))



(defun mutator-calls (spec stobj renaming)
  (let ((field (car spec)))
    (cond
     ((ht-specp spec)
      `((,(defstobj-fnname field :updater :hash-table renaming) mk v ,stobj)
        (,(defstobj-fnname field :remove :hash-table renaming) mk ,stobj)
        (,(defstobj-fnname field :clear :hash-table renaming) ,stobj)))
     ((array-specp spec)
      `((,(defstobj-fnname field :updater :array renaming) mi v ,stobj)
        (,(defstobj-fnname field :resize :array renaming) len ,stobj)))
     (t
      `((,(defstobj-fnname field :updater nil renaming) v ,stobj))))))

(defun accessor-calls (spec stobj renaming)
  (let ((field (car spec)))
    (cond
     ((ht-specp spec)
      `((,(defstobj-fnname field :accessor :hash-table renaming) ak ,stobj)
        (,(defstobj-fnname field :boundp :hash-table renaming) ak ,stobj)
;; Leave out the get? function because we prefer to just expand its definition.
;;        (,(defstobj-fnname field :accessor? :hash-table renaming) ak ,stobj)
        (,(defstobj-fnname field :count :hash-table renaming) ,stobj)))
     ((array-specp spec)
      `((,(defstobj-fnname field :accessor :array renaming) ai ,stobj)
        (,(defstobj-fnname field :length :array renaming) ,stobj)))
     (t
      `((,(defstobj-fnname field :accessor nil renaming) ,stobj))))))

(defun def-stobj-self-mod-thms (spec stobj renaming)
  (let ((field (car spec))
        (create (defstobj-fnname stobj :creator nil renaming))
        (init (cadr (assoc-keyword :initially (cdr spec)))))
    (cond
     ((ht-specp spec)
      (let* ((upd (defstobj-fnname field :updater :hash-table renaming))
             (rem (defstobj-fnname field :remove :hash-table renaming))
             (clr (defstobj-fnname field :clear :hash-table renaming))
             (acc (defstobj-fnname field :accessor :hash-table renaming))
             (bdp (defstobj-fnname field :boundp :hash-table renaming))
             (cnt (defstobj-fnname field :count :hash-table renaming)))
        ;; Hoo boy.
        `((defthm ,(incat stobj (symbol-name stobj) "-"
                          (symbol-name acc) "-"
                          (symbol-name create))
            (equal (,acc ak (,create)) nil))
          (defthm ,(incat stobj (symbol-name stobj) "-"
                          (symbol-name acc) "-"
                          (symbol-name upd))
            (equal (,acc ak (,upd mk v ,stobj))
                   (if (equal ak mk)
                       v
                     (,acc ak ,stobj))))
          (defthm ,(incat stobj  (symbol-name stobj) "-"
                          (symbol-name acc) "-"
                          (symbol-name rem))
            (equal (,acc ak (,rem mk ,stobj))
                   (if (equal ak mk)
                       nil
                     (,acc ak ,stobj))))
          (defthm ,(incat stobj  (symbol-name stobj) "-"
                          (symbol-name acc) "-"
                          (symbol-name clr))
            (equal (,acc ak (,clr ,stobj))
                   nil))
          (defthm ,(incat stobj (symbol-name stobj) "-"
                          (symbol-name bdp) "-"
                          (symbol-name create))
            (equal (,bdp ak (,create)) nil))
          (defthm ,(incat stobj  (symbol-name stobj) "-"
                          (symbol-name bdp) "-"
                          (symbol-name upd))
            (equal (,bdp ak (,upd mk v ,stobj))
                   (if (equal ak mk)
                       t
                     (,bdp ak ,stobj))))
          (defthm ,(incat stobj  (symbol-name stobj) "-"
                          (symbol-name bdp) "-"
                          (symbol-name rem))
            (equal (,bdp ak (,rem mk ,stobj))
                   (if (equal ak mk)
                       nil
                     (,bdp ak ,stobj))))
          (defthm ,(incat stobj  (symbol-name stobj) "-"
                          (symbol-name bdp) "-"
                          (symbol-name clr))
            (equal (,bdp ak (,clr ,stobj))
                   nil))
          (defthm ,(incat stobj (symbol-name stobj) "-"
                          (symbol-name cnt) "-"
                          (symbol-name create))
            (equal (,cnt (,create)) 0))
          (defthm ,(incat stobj  (symbol-name stobj) "-"
                          (symbol-name cnt) "-"
                          (symbol-name upd))
            (equal (,cnt (,upd mk v ,stobj))
                   (if (,bdp mk ,stobj)
                       (,cnt ,stobj)
                     (+ 1 (,cnt ,stobj)))))
          (defthm ,(incat stobj  (symbol-name stobj) "-"
                          (symbol-name cnt) "-"
                          (symbol-name rem))
            (equal (,cnt (,rem mk ,stobj))
                   (if (,bdp mk ,stobj)
                       (- (,cnt ,stobj) 1)
                     (,cnt ,stobj))))
          (defthm ,(incat stobj  (symbol-name stobj) "-"
                          (symbol-name cnt) "-"
                          (symbol-name clr))
            (equal (,cnt (,clr ,stobj)) 0)))))
     ((array-specp spec)
      (let* ((upd (defstobj-fnname field :updater :array renaming))
             (rsz (defstobj-fnname field :resize :array renaming))
             (acc (defstobj-fnname field :accessor :array renaming))
             (len (defstobj-fnname field :length :array renaming))
             (size (car (caddr (cadr (assoc-keyword :type (cdr spec)))))))
        `((defthm ,(incat stobj (symbol-name stobj) "-"
                          (symbol-name acc) "-"
                          (symbol-name create))
            (equal (,acc ai (,create))
                   (and (< (nfix ai) ,size) ,init))
            :hints (("Goal" :in-theory (disable make-list-ac
                                                (make-list-ac)))))
          (defthmd ,(incat stobj (symbol-name stobj) "-"
                          (symbol-name acc) "-OUT-OF-RANGE")
            (implies (<= (,len ,stobj) (nfix n))
                     (not (,acc n ,stobj))))
          (defthm ,(incat stobj (symbol-name stobj) "-"
                          (symbol-name acc) "-NON-NATP")
            (implies (not (natp n))
                     (equal (,acc n ,stobj)
                            (,acc 0 ,stobj))))
          (defthm ,(incat stobj (symbol-name stobj) "-"
                          (symbol-name acc) "-"
                          (symbol-name upd))
            (equal (,acc ai (,upd mi v ,stobj))
                   (if (equal (nfix ai) (nfix mi))
                       v
                     (,acc ai ,stobj))))
          (defthm ,(incat stobj (symbol-name stobj) "-"
                          (symbol-name upd) "-NON-NATP")
            (implies (not (natp n))
                     (equal (,upd n v ,stobj)
                            (,upd 0 v ,stobj))))
          (defthm ,(incat stobj (symbol-name stobj) "-"
                          (symbol-name acc)
                          (symbol-name rsz))
            (equal (,acc ai (,rsz len ,stobj))
                   (and (< (nfix ai) (nfix len))
                        (if (< (nfix ai) (,len ,stobj))
                            (,acc ai ,stobj)
                          ,init))))
          (defthm ,(incat stobj (symbol-name stobj) "-"
                          (symbol-name len) "-"
                          (symbol-name create))
            (equal (,len (,create)) ,size))
          (defthm ,(incat stobj (symbol-name stobj) "-"
                          (symbol-name len) "-"
                          (symbol-name upd))
            (equal (,len (,upd mi v ,stobj))
                   (max (+ 1 (nfix mi)) (,len ,stobj))))
          (defthm ,(incat stobj (symbol-name stobj) "-"
                          (symbol-name len) "-"
                          (symbol-name rsz))
            (equal (,len (,rsz len ,stobj))
                   (nfix len))))))
     (t (let* ((upd (defstobj-fnname field :updater nil renaming))
               (acc (defstobj-fnname field :accessor nil renaming)))
          `((defthm ,(incat stobj (symbol-name stobj) "-"
                            (symbol-name acc) "-"
                            (symbol-name create))
              (equal (,acc (,create)) ,init))
            (defthm ,(incat stobj (symbol-name stobj) "-"
                            (symbol-name acc) "-"
                            (symbol-name upd))
              (equal (,acc (,upd v ,stobj)) v))))))))

(defun def-stobj-acc-of-upd-thms1111 (stobj acc upds)
  (if (atom upds)
      nil
    (cons `(defthm ,(incat stobj (symbol-name stobj) "-"
                           (symbol-name (car acc)) "-"
                           (symbol-name (caar upds)))
             (equal ,(subst (car upds) stobj acc)
                    ,acc))
          (def-stobj-acc-of-upd-thms1111 stobj acc (cdr upds)))))

(defun def-stobj-acc-of-upd-thms111 (stobj accs upds)
  (if (atom accs)
      nil
    (append (def-stobj-acc-of-upd-thms1111 stobj (car accs) upds)
            (def-stobj-acc-of-upd-thms111 stobj (cdr accs) upds))))

(defun def-stobj-acc-of-upd-thms11 (stobj spec specs renaming)
  (if (atom specs)
      nil
    (append (if (equal spec (car specs))
                (def-stobj-self-mod-thms spec stobj renaming)
              (def-stobj-acc-of-upd-thms111
                stobj
                (accessor-calls spec stobj renaming)
                (mutator-calls (car specs) stobj renaming)))
            (def-stobj-acc-of-upd-thms11 stobj spec (cdr specs) renaming))))

(defun def-stobj-acc-of-upd-thms1 (stobj specs all-specs renaming)
  (if (atom specs)
      nil
    (append (def-stobj-acc-of-upd-thms11 stobj (car specs) all-specs renaming)
            (def-stobj-acc-of-upd-thms1 stobj (cdr specs) all-specs
              renaming))))

(defun def-stobj-acc-of-upd-thms-mkevent (stobj state)
  (let* ((rb (getprop stobj 'redundancy-bundle nil 'current-acl2-world
                      (w state)))
         (specs (car rb))
         (renaming (cdr rb)))
    (def-stobj-acc-of-upd-thms1 stobj specs specs renaming)))

(defmacro def-stobj-acc-of-upd-thms (stobj)
  `(make-event
    `(progn . ,(def-stobj-acc-of-upd-thms-mkevent ',stobj state))))







(defun def-stobj-type-theory-fn (stobj specs renaming state)
  (declare (xargs :mode :program))
  (if (atom specs)
      (value nil)
    (er-let*
     ((thms
       (let* ((spec (car specs))
              (field (car spec)))
         (cond
          ((ht-specp spec)
           (let* ((upd (defstobj-fnname field :updater :hash-table renaming))
                  (rem (defstobj-fnname field :remove :hash-table renaming))
                  (clr (defstobj-fnname field :clear :hash-table renaming))
                  (bdp (defstobj-fnname field :boundp :hash-table renaming))
                  (cnt (defstobj-fnname field :count :hash-table renaming))
                  (stobj-rec
                   (defstobj-fnname stobj :recognizer :top renaming)))
             (value
              `((defthm ,(incat stobj (symbol-name stobj) "-BOOLEANP-"
                                (symbol-name bdp))
                  (booleanp (,bdp ak ,stobj))
                  :rule-classes :type-prescription)
                (defthm ,(incat stobj (symbol-name stobj) "-NATP-"
                                (symbol-name cnt))
                  (natp (,cnt ,stobj))
                  :rule-classes :type-prescription)
                (defthm ,(incat stobj (symbol-name stobj-rec) "-"
                                (symbol-name upd))
                  (implies (,stobj-rec ,stobj)
                           (,stobj-rec (,upd mk v ,stobj))))
                (defthm ,(incat stobj (symbol-name stobj-rec) "-"
                                (symbol-name rem))
                  (implies (,stobj-rec ,stobj)
                           (,stobj-rec (,rem mk ,stobj))))
                (defthm ,(incat stobj (symbol-name stobj-rec) "-"
                                (symbol-name clr))
                  (implies (,stobj-rec ,stobj)
                           (,stobj-rec (,clr ,stobj))))))))
          ((array-specp spec)
           (let* ((upd (defstobj-fnname field :updater :array renaming))
                  (rsz (defstobj-fnname field :resize :array renaming))
                  (acc (defstobj-fnname field :accessor :array renaming))
                  (len (defstobj-fnname field :length :array renaming))
                  (field-rec
                   (defstobj-fnname field :recognizer :hash-table renaming))
                  (stobj-rec
                   (defstobj-fnname stobj :recognizer :top renaming))
                  (init (cadr (assoc-keyword :initially (cdr spec))))
                  (type (cadr (cadr (assoc-keyword :type (cdr spec)))))
                  (pred (translate-declaration-to-guard type 'x (w state)))
                  (stobj-rec-upd-form
                   `(implies (and (,stobj-rec ,stobj)
                                  ,pred
                                  (< (nfix i) (,len ,stobj)))
                             (,stobj-rec (,upd i x ,stobj)))))
             (er-let*
              ((stobj-rec-upd-thms
                (simplify-thm-fn
                 (incat field (symbol-name stobj-rec) "-" (symbol-name upd))
                 stobj-rec-upd-form `(("Goal" :in-theory (theory 'minimal-theory)))
                 nil state)))
              (value
               `((defthmd ,(incat field (symbol-name stobj) "-"
                                  (symbol-name field-rec) "-NTH-TYPE")
                   (implies (and (,field-rec x)
                                 (< (nfix n) (len x)))
                            ,(subst '(nth n x) 'x pred))
                   :rule-classes :type-prescription)
                 (defthm ,(incat field (symbol-name stobj) "-"
                                 (symbol-name acc) "-TYPE")
                   (implies (and (,stobj-rec ,stobj)
                                 (< (nfix i) (,len ,stobj)))
                            ,(subst `(,acc i ,stobj) 'x pred))
                   :hints (("goal" :in-theory
                            (enable ,(incat field (symbol-name stobj) "-"
                                            (symbol-name field-rec)
                                            "-NTH-TYPE"))))
                   :rule-classes :type-prescription)
                 (defthm ,(incat field (symbol-name stobj) "-"
                                 (symbol-name field-rec) "-UPDATE-NTH")
                   (implies (and (,field-rec fld)
                                 (< (nfix n) (len fld))
                                 ,pred)
                            (,field-rec (update-nth n x fld))))
                 ,@stobj-rec-upd-thms
                 (defthm ,(incat field (symbol-name stobj) "-"
                                 (symbol-name len) "-TYPE")
                   (natp (,len ,stobj))
                   :rule-classes :type-prescription)
                 (defthm ,(incat field (symbol-name stobj) "-"
                                 (symbol-name field-rec) "-RESIZE-LIST")
                   (implies (,field-rec x)
                            (,field-rec (resize-list x n ,init))))
                 (defthm ,(incat field (symbol-name stobj) "-"
                                 (symbol-name rsz) "-" (symbol-name stobj-rec))
                   (implies (,stobj-rec ,stobj)
                            (,stobj-rec (,rsz n ,stobj)))))))))
          (t (let* ((upd (defstobj-fnname field :updater nil renaming))
                    (acc (defstobj-fnname field :accessor nil renaming))
                    (type (cadr (assoc-keyword :type (cdr spec))))
                    (pred (translate-declaration-to-guard type 'x (w state)))
                    (stobj-rec
                     (defstobj-fnname stobj :recognizer :top renaming))
                    (stobj-rec-upd-form
                     `(implies (and (,stobj-rec ,stobj)
                                    ,@(if (equal pred ''nil) nil (list pred)))
                               (,stobj-rec (,upd x ,stobj)))))
               (er-let*
                ((stobj-rec-upd-thms
                  (simplify-thm-fn
                   (incat field (symbol-name stobj-rec) "-" (symbol-name upd))
                   stobj-rec-upd-form '(("Goal" :in-theory (theory
                                                            'minimal-theory)))
                   nil state)))
                (if (equal pred ''nil)
                    (value stobj-rec-upd-thms)
                  (value
                   `((defthm ,(incat field (symbol-name stobj) "-" (symbol-name acc) "-TYPE")
                       (implies (,stobj-rec ,stobj)
                                ,(subst `(,acc ,stobj) 'x pred))
                       :rule-classes :type-prescription)
                     . ,stobj-rec-upd-thms)))))))))
      (rest (def-stobj-type-theory-fn stobj (cdr specs) renaming state)))
     (value (append thms rest)))))


(defun def-stobj-simple-field-equivs11 (stobj equiv calls)
  (if (atom calls)
      nil
    (cons `(defthm ,(incat equiv (symbol-name equiv) "-"
                           (symbol-name (caar calls)))
             (,equiv ,(car calls) ,stobj))
          (def-stobj-simple-field-equivs11 stobj equiv (cdr calls)))))

(defun def-stobj-simple-field-equivs1 (stobj cspec equiv specs renaming)
  (if (atom specs)
      nil
    (if (equal cspec (car specs))
        (def-stobj-simple-field-equivs1 stobj cspec equiv (cdr specs) renaming)
      (let* ((spec (car specs))
             (calls (mutator-calls spec stobj renaming)))
        (append (def-stobj-simple-field-equivs11 stobj equiv calls)
                (def-stobj-simple-field-equivs1 stobj cspec equiv (cdr specs)
                  renaming))))))

(defun def-stobj-simple-field-equivs (stobj specs all-specs renaming)
  (if (atom specs)
      nil
    (if (or (ht-specp (car specs))
            (array-specp (car specs)))
        (def-stobj-simple-field-equivs stobj (cdr specs) all-specs renaming)
      (let* ((spec (car specs))
             (field (car spec))
             (equiv (incat stobj (symbol-name stobj) "-"
                           (symbol-name field) "-EQ"))
             (acc (defstobj-fnname field :accessor nil renaming))
             (upd (defstobj-fnname field :updater nil renaming)))
        `((defun-nx ,equiv (a b)
            (equal (,acc a) (,acc b)))
          (defequiv ,equiv)
          (defcong ,equiv equal (,acc ,stobj) 1)
          (defthm ,(incat stobj (symbol-name equiv) "-"
                          (symbol-name upd) "-NORM")
            (implies (syntaxp (not (equal ,stobj ''t)))
                     (,equiv (,upd x ,stobj)
                             (,upd x t))))
          ,@(def-stobj-simple-field-equivs1 stobj spec equiv all-specs renaming)
          ,@(def-stobj-simple-field-equivs stobj (cdr specs) all-specs
              renaming)
          (in-theory (disable ,equiv)))))))



(defun def-stobj-theory-fn-names1 (specs stobj renaming)
  (if (atom specs)
      nil
    (append
     (strip-cars (mutator-calls (car specs) stobj renaming))
     (strip-cars (accessor-calls (car specs) stobj renaming))
     (def-stobj-theory-fn-names1 (cdr specs) stobj renaming))))

(defun def-stobj-theory-fn-names (specs stobj renaming)
  (list* (defstobj-fnname stobj :recognizer :top renaming)
         (def-stobj-theory-fn-names1 specs stobj renaming)))


(defun def-stobj-theory-mkevent (stobj state)
  (declare (xargs :mode :program
                  :stobjs state))
  (let* ((rb (getprop stobj 'redundancy-bundle nil 'current-acl2-world
                      (w state)))
         (specs (car rb))
         (renaming (cdr rb))
         (fn-names (def-stobj-theory-fn-names specs stobj renaming)))
    (er-let*
     ((type-thms (def-stobj-type-theory-fn stobj specs renaming state)))
     (value
      `(encapsulate
        nil
        ,@(def-stobj-acc-of-upd-thms1 stobj specs specs renaming)
        ,@type-thms
        (in-theory (disable . ,fn-names))
        . ,(def-stobj-simple-field-equivs stobj specs specs renaming))))))

(defmacro def-stobj-theory (stobj)
  `(make-event
    (def-stobj-theory-mkevent ',stobj state)))

