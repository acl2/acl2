;; vcd.lisp
;;
;; Book defining functions which can read and write VCD files. The VCD read
;; function reads a VCD file and populates a vcd$ stobj with the results. The
;; VCD write operation takes a populated vcd$ stobj and writes it out to a VCD
;; file. The main "exported" functions from this book are read-vcd-file-to-vcd$
;; and write-vcd$-to-vcd-file.

(in-package "ACL2")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; BOZOs
;; 1. ???
;;
;; TODOs
;; 1. ??? 
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(include-book "std/util/define" :dir :system)
(include-book "std/util/defconsts" :dir :system)
(include-book "std/util/defval" :dir :system)
(include-book "std/util/bstar" :dir :system)
;(include-book "std/io/read-file-lines-no-newlines" :dir :system)
(include-book "std/strings/strtok" :dir :system)
(include-book "std/strings/substrp" :dir :system)
(include-book "centaur/sv/svex/svex" :dir :system)
(include-book "centaur/fty/top" :dir :system)
(include-book "misc/file-io" :dir :system)
(include-book "std/io/base" :dir :system)
(include-book "support")
(include-book "vcdtypes")

(defsection exsim-vcd-reading-and-writing
  :parents (exsim)
  :short "Functions defining reading from and writing to VCD files"
  :autodoc nil
  :long " <p> The function @({ (read-vcd-file-to-vcd$) }) reads in an input VCD
  file and stores the results in the vcd$ stobj with the other direction
  defined by @({ (write-vcd$-to-vcd-file) }) which takes a populated vcd$ stobj
  and writes out a VCD file </p> ")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 0. parsing VCD files (defining function read-vcd-file-to-vcd$)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-theory (disable princ$ open-output-channel-p1))

(define vcd-write-lines! ((lines string-listp) (chan symbolp) &key (state 'state))
  :guard (non-exec (open-output-channel-p1 chan :character state))
  :returns (new-state (and (state-p1 new-state)
                           (open-output-channel-p1 chan :character new-state))
                      :hyp :guard)
  (if (endp lines) state
    (b* ((state (princ$ (strap! (first lines) #\Newline) chan state)))
      (vcd-write-lines! (rest lines) chan))))

(defttag :need-file-writing-for-vcd-io)

(define vcd-write-lines-file ((fname stringp) (lines string-listp)
                              &key (state 'state))
  (b* (((mv chan state) (acl2::open-output-channel! fname :character state))
       ((when (not chan))
        (prog2$ (raise "could not open file:~x0~%" fname) state))
       (state (vcd-write-lines! lines chan))
       (state (acl2::close-output-channel chan state)))
    state))

(defttag nil)

(defconst *vcd-tags*
  '(;; misc
    ("$comment"   . :comment)
    ("$date"      . :date)
    ("$version"   . :version)
    ("$timescale" . :timescale)
    ("$enddefinitions" . :enddefs)
    ;; vars
    ("$scope"     . :scope)
    ("$upscope"   . :upscope)
    ("$var"       . :var)))

(define pickup-vcd-data ((lines string-listp))
  (if (endp lines)
      (mv (raise "Did not find expected tag:~x0~%" lines) ())
    (b* ((fst (str::strtok (first lines) (list #\Space)))
         ((when (equal (first-last! fst) "$end"))
          (mv (allbut-last! fst) (rest lines)))
         ((mv more rst)
          (pickup-vcd-data (rest lines))))
      (mv (append! fst more) rst))))

(defthm pickup-vcd-data-string-listp
  (implies (string-listp x) (string-listp (mv-nth 1 (pickup-vcd-data x))))
  :hints (("Goal" :in-theory (enable pickup-vcd-data))))
   
(defthm pickup-vcd-data-smaller1
  (implies (consp x) (< (len (mv-nth 1 (pickup-vcd-data x))) (len x)))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable pickup-vcd-data))))

(defthm pickup-vcd-data-smaller2
  (implies (atom x) (equal (mv-nth 1 (pickup-vcd-data x)) nil))
  :hints (("Goal" :in-theory (enable pickup-vcd-data))))

(defthm pickup-vcd-data-smaller3
  (<= (len (mv-nth 1 (pickup-vcd-data x))) (len x))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable pickup-vcd-data))))

(define next-vcd-lines ((lines string-listp))
  (if (atom lines)
      (mv (raise "Did not find expected tag:~x0~%" lines) () ())
    (b* ((fst (str::strtok (first lines) (list #\Space)))
         ((when (atom fst))
          (next-vcd-lines (rest lines)))
         (tag (look! (first fst) *vcd-tags*))
         (dat (rest fst))
         ((when (not tag))
          (mv (raise "Did not have proper tag:~x0~%" fst) () ()))
         ((when (equal (first-last! dat) "$end"))
          (mv tag (allbut-last! dat) (rest lines)))
         ((mv more rst)
          (pickup-vcd-data (rest lines))))
      (mv tag (append! dat more) rst))))

(defthm next-vcd-lines-string-listp
  (implies (string-listp x) (string-listp (mv-nth 2 (next-vcd-lines x))))
  :hints (("Goal" :in-theory (enable next-vcd-lines))))

(defthm next-vcd-lines-smaller
  (implies (consp x) (< (len (mv-nth 2 (next-vcd-lines x))) (len x)))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable next-vcd-lines))))

(define split-vcd-lines ((lines string-listp) defs)
  :measure (len lines)
  (if (atom lines)
      (mv (raise "Failed to find updates:~x0~%" lines) defs)
    (b* (((mv tag dat rst) (next-vcd-lines lines)))
      (if (eq tag :enddefs)
          (mv rst (rev! defs))
        (split-vcd-lines rst (cons (cons tag dat) defs))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; vcd$ stobj definition
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defstobj vcd$
  ;;;; header info. returned and used in vcd input and output:
  (vcd$-comments       :type (satisfies string-listp)     :initially nil)
  (vcd$-date           :type (satisfies string-listp)     :initially nil)
  (vcd$-version        :type (satisfies string-listp)     :initially nil)
  (vcd$-timescale      :type (satisfies string-listp)     :initially nil)
  ;;;; tables/stacks generated during vcd input:
  (vcd$-curr-scope     :type (satisfies vcd-scope-lst-p)  :initially nil)
  (vcd$-scopes-stk     :type (satisfies vcd-scopes-lst-p) :initially nil)
  (vcd$-id-map         :type (satisfies vcd-id-map-p)     :initially nil)
  ;;;; tables generated during vcd output:
  (vcd$-str-tbl        :type (satisfies vcd-str-map-p)    :initially nll)
  (vcd$-scope-tbl      :type (satisfies vcd-scope-tbl-p)  :initially nll)
  ;;;; returned as part of vcd input:
  (vcd$-inst-map       :type (satisfies vcd-inst-map-p)   :initially nil)
  (vcd$-child-map      :type (satisfies vcd-child-map-p)  :initially nil)
  (vcd$-parent-map     :type (satisfies vcd-parent-map-p) :initially nil)
  (vcd$-var-tbl        :type (satisfies vcd-var-map-p)    :initially nil)
  ;;;; used in both vcd input and output:
  (vcd$-val-chg-lst    :type (satisfies vcd-val-chgs-p)   :initially nil)
  ;;;; tbl parameter used in vcd output only:
  (vcd$-out-tbl        :type (satisfies vcd-out-map-p)    :initially nil)
  (vcd$-top-mod        :type string                       :initially ""))

(define parse-init-vcd$ (vcd$)
  (b* ((vcd$ (update-vcd$-comments        nil vcd$))
       (vcd$ (update-vcd$-date            nil vcd$))
       (vcd$ (update-vcd$-version         nil vcd$))
       (vcd$ (update-vcd$-timescale       nil vcd$))
       ;;;;
       (vcd$ (update-vcd$-curr-scope      nil vcd$))
       (vcd$ (update-vcd$-scopes-stk      nil vcd$))
       (vcd$ (update-vcd$-id-map          :vcd-id-map vcd$))
       ;;;;
       (vcd$ (update-vcd$-str-tbl         :vcd-str-tbl   vcd$))
       (vcd$ (update-vcd$-scope-tbl       :vcd-scope-tbl vcd$))
       ;;;;
       (vcd$ (update-vcd$-inst-map        :vcd-inst-map   vcd$))
       (vcd$ (update-vcd$-child-map       :vcd-child-map  vcd$))
       (vcd$ (update-vcd$-parent-map      :vcd-parent-map vcd$))
       (vcd$ (update-vcd$-var-tbl         :vcd-var-tbl   vcd$))
       ;;;;
       (vcd$ (update-vcd$-val-chg-lst     nil vcd$))
       ;;;;
       (vcd$ (update-vcd$-out-tbl         :vcd-out-tbl   vcd$)))
    vcd$))

;;;;;;;;;;;;;;;;;;;;;;;;


;; 
;; NOTES on special handling for struct-type and array-type "scoping".. 
;;
;; VCD does not have specific handling for structures and arrays, but some
;; "standards" are in use which we support here.. In particular, a variable
;; which is built from arrays and/or structs will have special scoping which
;; extends the normal scope handling as follows:
;;
;;  1. a special "array" scope typeis introduced whenever a variable with a [N]
;;     suffix is encountered in either a scope name or variable name. We push
;;     [N] onto the scope stack and then process the variable/scope as we would
;;     normally and then add an unscope when either the variable is completed
;;     or we hit an upscope for the scope with [N] suffix (a double upscope in
;;     that case).
;;
;;  2. one (or more) of the existing VCD scope types (currently "fork" is the
;;     one we have seen) will be repurposed as a "struct" scope. This scope is
;;     still pushed/popped like other scope types.. but we track this scope
;;     (and subscopes) relative to a parent variable/scope
;;
;;  3. array and struct scopes are both tracked relative to a parent 
;;     variable/scope and are used to build mappings to and from the parent
;;     (i.e. a mapping from the parent to the "fields" of that parent and
;;     their location in the parent.. and mappings from the "fields" back
;;     to their location in the parent).. These are used when translating
;;     the VCD wave input to correlate with values for variables that may
;;     have been collapsed -- this is common in processing compiled SVEX
;;     for example.
;;


(define vcd-svar-name1 ((scope vcd-scope-lst-p) rslt)
  (if (endp scope) rslt
    (vcd-svar-name1 (rest scope) (hons (caar scope) rslt))))

(define vcd-svar-name ((scope vcd-scope-lst-p))
  (if (endp scope) nil ;; (raise "should not build var on empty scope!")
    (vcd-svar-name1 (rest scope) (caar scope))))

(define vcd-make-svar ((scope vcd-scope-lst-p))
  :returns (rslt sv::svar-p)
  (hons-copy (sv::make-svar :name (vcd-svar-name scope)
                            :delay 0 :nonblocking nil)))

(define vcd$-make-svar (vcd$)
  :returns (rslt sv::svar-p)
  (vcd-make-svar (vcd$-curr-scope vcd$)))

(define revapp! (x y)
  (if (atom x) y (revapp! (rest x) (cons (first x) y))))

(define len! (x &key ((rslt natp) '0))
  :returns (rslt natp :hyp :guard)
  (if (atom x) rslt (len! (rest x) :rslt (1+ rslt))))

(define nthcdr! (x (n natp))
  (cond ((zp n) x)
        ((atom x) (raise "unexpected cdring:~x0~%" (list x n)))
        (t (nthcdr! (rest x) (1- n)))))

(define upd-parent-map ((new-scopes vcd-scope-lst-p)
                        (curr-scope vcd-scope-lst-p)
                        (p-map vcd-parent-map-p))
  :returns (rslt vcd-parent-map-p)
  (if (endp new-scopes) (vcd-parent-map-fix p-map)
    (b* ((p-var (vcd-make-svar curr-scope))
         (next-scope (cons (first new-scopes) curr-scope))
         (c-var (vcd-make-svar next-scope))
         (look (hons-get p-var p-map)))
      (upd-parent-map (rest new-scopes) next-scope
                      (hons-acons p-var (cons c-var (cdr look)) p-map)))))

(define upd-child-map ((new-scopes vcd-scope-lst-p)
                       (curr-scope vcd-scope-lst-p)
                       (c-map vcd-child-map-p))
  :returns (rslt vcd-child-map-p)
  (if (endp new-scopes) (vcd-child-map-fix c-map)
    (b* ((p-var (vcd-make-svar curr-scope))
         (next-scope (cons (first new-scopes) curr-scope))
         (c-var (vcd-make-svar next-scope))
         (look (hons-get c-var c-map))
         ((when look) (raise "should not see child-var again:~x0~%" c-var)))
      (upd-child-map (rest new-scopes) next-scope
                     (hons-acons c-var p-var c-map)))))

(define upd-inst-map ((new-scopes vcd-scope-lst-p)
                      (curr-scope vcd-scope-lst-p)
                      (i-map vcd-inst-map-p))
  :returns (rslt vcd-inst-map-p)
  (cond ((endp new-scopes) (vcd-inst-map-fix i-map))
        ((or (not (stringp (caar new-scopes)))
             (not (eq (cdar new-scopes) :module)))
         (upd-inst-map (rest new-scopes)
                       (cons (first new-scopes) curr-scope)
                       i-map))
        (t
         (b* ((i-name (hons-copy (caar new-scopes)))
              (next-scope (cons (first new-scopes) curr-scope))
              (i-var (vcd-make-svar next-scope))
              (look (hons-get i-name i-map)))
           (upd-inst-map (rest new-scopes) next-scope
                         (hons-acons i-name (cons i-var (cdr look)) i-map))))))

(defthm revapp!-vcd-scope-lst
  (implies (and (vcd-scope-lst-p x) (vcd-scope-lst-p y))
           (vcd-scope-lst-p (revapp! x y)))
  :hints (("Goal" :in-theory (enable revapp! vcd-scope-lst-p))))

(defthm nthcdr!-vcd-scope-lst
  (implies (vcd-scope-lst-p x)
           (vcd-scope-lst-p (nthcdr! x n)))
  :hints (("Goal" :in-theory (enable nthcdr! vcd-scope-lst-p))))

(define push-current-scope ((new-scopes vcd-scope-lst-p) vcd$)
  (b* ((curr-scope (vcd$-curr-scope vcd$))
       (vcd$ (update-vcd$-parent-map
              (upd-parent-map new-scopes curr-scope (vcd$-parent-map vcd$))
              vcd$))
       (vcd$ (update-vcd$-child-map
              (upd-child-map new-scopes curr-scope (vcd$-child-map vcd$))
              vcd$))
       (vcd$ (update-vcd$-inst-map
              (upd-inst-map new-scopes curr-scope (vcd$-inst-map vcd$))
              vcd$))
       (vcd$ (update-vcd$-scopes-stk 
              (cons new-scopes (vcd$-scopes-stk vcd$)) vcd$))
       (vcd$ (update-vcd$-curr-scope
              (revapp! new-scopes (vcd$-curr-scope vcd$)) vcd$)))
    vcd$))

(define pop-current-scope (vcd$)
  (b* ((vcd$ (update-vcd$-curr-scope
              (nthcdr! (vcd$-curr-scope vcd$)
                       (len! (car (vcd$-scopes-stk vcd$))))
              vcd$))
       (vcd$ (update-vcd$-scopes-stk
              (cdr (vcd$-scopes-stk vcd$))
              vcd$)))
    vcd$))

(define var-current-scope ((v-type symbolp)
                           (v-size natp)
                           (v-id stringp)
                           (v-vec stringp)
                           vcd$)
  ;; only update var-tbl and id-maps
  (b* ((svar (vcd$-make-svar vcd$))
       (new-id-map  (hons-acons (hons-copy v-id) svar
                                (vcd$-id-map vcd$)))
       (new-var-tbl (hons-acons svar (make-vcd-var-elem :v-size v-size
                                                        :v-type v-type
                                                        :v-id   v-id
                                                        :v-vec  v-vec)
                                (vcd$-var-tbl vcd$)))
       (vcd$ (update-vcd$-id-map new-id-map vcd$))
       (vcd$ (update-vcd$-var-tbl new-var-tbl vcd$)))
    vcd$))

;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *map-scope-type*
  '(("begin" . :begin)
    ("function" . :function)
    ("fork" . :fork)
    ("module" . :module)
    ("task" . :task)))

(defconst *map-var-types*
  '(("event" . :event)
    ("integer" . :integer)
    ("parameter" . :parameter)
    ("real" . :real)
    ("reg" . :reg)
    ("supply0" . :supply0)
    ("supply1" . :supply1)
    ("time" . :time)
    ("tri" . :tri)
    ("triand" . :triand)
    ("trior" . :trior)
    ("trireg" . :trireg)
    ("tri0" . :tri0)
    ("tri1" . :tri1)
    ("wand" . :wand)
    ("wire" . :wire)
    ("wor" . :wor)))

;;
;; NOTE -- the "fork" scope type is often reused in generated VCD as a
;;         way of defining struct data types, but if something else is
;;         used, please adjust this function accordingly:
;;
(defabbrev is-struct-type (x) (eq x :fork))
(defabbrev get-struct-type () :fork)
;;
;; NOTE -- we introduce array scope types as a way to account for indexes
;;         in scopes and variable declarations in a normalized way
;;         relative to how they are handled in SVARs and handling of struct
;;         types:
;;
(defabbrev is-array-type (x) (eq x :array))

(defmacro strings-p (vals n)
  (if (zp n) `(null ,vals)
    `(and (consp ,vals) (stringp (first ,vals))
          (strings-p (rest ,vals) ,(1- n)))))

(define symbol-look-p (x)
  (or (atom x)
      (and (consp (car x))
           (symbolp (cdar x))
           (symbol-look-p (cdr x)))))
            
(defthm look!-symbol-look-p
  (implies (and (symbol-look-p x) (look! e x))
           (symbolp (look! e x)))
  :hints (("Goal" :in-theory (enable look! symbol-look-p))))

(define ch-to-dig ((ch characterp))
  (let ((n (- (char-code ch) (char-code #\0))))
    (if (and (natp n) (< n 10)) n
      (prog2$ (raise "illegal ch-to-dig:~x0~%" ch) 0))))

(define str-to-num* ((str stringp) (i natp) (n natp) (r natp))
  (if (zp n) r
    (str-to-num* str (1+ i) (1- n)
                 (if (< i (length str))
                     (+ (* r 10) (ch-to-dig (char str i)))
                   (prog2$ (raise "illegal str-to-num* index:~x0~%" i) r)))))

(define str-to-num ((str stringp))
  (str-to-num* str 0 (length str) 0))

(define laststr! ((x string-listp))
  :returns (r stringp :hyp :guard)
  (if (endp x) (prog2$ (raise "unexpected empty lst!") "")
    (b* ((a (first x)) (r (rest x)))
      (if (endp r) a (laststr! r)))))

(define butlaststrs! ((x string-listp))
  :returns (r string-listp :hyp :guard)
  (if (endp x) ()
    (b* ((a (first x)) (r (rest x)))
      (if (endp r) () (cons a (butlaststrs! r))))))

(defthm string-list-consp-car
  (implies (and (string-listp x) (consp x))
           (stringp (car x))))

(defthm string-list-consp-cdr
  (implies (and (string-listp x) (consp x))
           (string-listp (cdr x))))

(define parse-vcd-ref ((ref stringp))
  :returns (mv (name stringp)
               (ndxs string-listp)
               (vec  stringp))
  (b* ((lst (str::strtok ref (list #\[ #\])))
       ((when (atom lst))
        (prog2$ (raise "ref parsing failed:~x0~%" ref)
                (mv "" () "")))
       (v-name (first lst))
       (lst (rest lst))
       ((when (atom lst))
        (mv v-name () ""))
       (v-vec (laststr! lst))
       ((when (str::substrp v-vec ":"))
        (mv v-name
            (butlaststrs! lst)
            (strap! "[" v-vec "]"))))
    (mv v-name lst "")))

(define mk-array-types (ndxs)
  :returns (rslt vcd-scope-lst-p)
  (if (atom ndxs) ()
    (cons (cons (first ndxs) :array) (mk-array-types (rest ndxs)))))

(define parse-vcd-var (vals vcd$)
  ;;
  ;; NOTE -- in the standard, it appears that we should only have 4
  ;;         tokens on a variable declaration line as follows:
  ;;
  ;;    $var type size identifier reference $end
  ;;
  ;; where the reference may have a suffix denoting array and vector
  ;; references, e.g. [3][4:2].. but we have seen some VCD output with
  ;; this suffix seperated from the "name" part of the reference with
  ;; a space, and as such, we try to normalize this by pre-processing the
  ;; vals to attach the name and suffix back into a reference -- which we
  ;; will later parse back out but that is a seperate standard process
  ;; we use for other scope names as well.
  ;;
  (b* ((vals (if (strings-p vals 5)
                 (list (first vals) (second vals) (third vals)
                       (strap! (fourth vals) (fifth vals)))
               vals))
       ((when (not (strings-p vals 4)))
        (prog2$ (raise "illegal var param.s:~x0~%" vals) vcd$))
       (v-type (look! (first vals) *map-var-types*))
       (v-size (str-to-num (second vals)))
       (v-id   (third vals))
       (v-ref  (fourth vals))
       ((when (not v-type))
        (prog2$ (raise "illegal var type:~x0~%" v-type) vcd$))
       ((when (not (natp v-size)))
        (prog2$ (raise "illegal var size:~x0~%" v-size) vcd$))
       ((mv v-name v-ndxs v-vec) (parse-vcd-ref v-ref))
       (new-scopes (cons (cons v-name (get-struct-type)) 
                         (mk-array-types v-ndxs)))
       (vcd$ (push-current-scope new-scopes vcd$))
       (vcd$ (var-current-scope v-type v-size v-id v-vec vcd$))
       (vcd$ (pop-current-scope vcd$)))
    vcd$))

(define parse-vcd-scope (vals vcd$)
  (b* (((when (not (strings-p vals 2)))
        (prog2$ (raise "illegal scope param.s:~x0~%" vals) vcd$))
       (s-type (look! (first vals) *map-scope-type*))
       (s-ref (second vals))
       ((when (not s-type))
        (prog2$ (raise "illegal scope type:~x0~%" s-type) vcd$))
       ((mv s-name s-ndxs s-vec) (parse-vcd-ref s-ref))
       ((when (not (equal s-vec "")))
        (prog2$ (raise "illegal non-array index for scope:~x0~%" s-vec) vcd$))
       (new-scopes (cons (cons s-name s-type) 
                         (mk-array-types s-ndxs)))
       (vcd$ (push-current-scope new-scopes vcd$)))
    vcd$))

(define parse-vcd-upscope (vals vcd$)
  (b* (((when (not (strings-p vals 0)))
        (prog2$ (raise "illegal scope param.s:~x0~%" vals) vcd$))
       (vcd$ (pop-current-scope vcd$)))
    vcd$))

;;;;;;;;;;;;;;;;;;;;;;;;

(define vcd-bval ((lst true-listp) (up natp) (lo natp))
  :returns (rslt sv::4vec-p)
  (if (endp lst) (sv::make-4vec :upper up :lower lo)
    (b* ((ch (first lst)))
      (cond ((eql ch #\b)
             (vcd-bval (rest lst) up lo))
            ((eql ch #\0)
             (vcd-bval (rest lst) (+ (* up 2) 0) (+ (* lo 2) 0)))
            ((eql ch #\1)
             (vcd-bval (rest lst) (+ (* up 2) 1) (+ (* lo 2) 1)))
            ((eql ch #\x)
             (vcd-bval (rest lst) (+ (* up 2) 1) (+ (* lo 2) 0)))
            ((eql ch #\z)
             (vcd-bval (rest lst) (+ (* up 2) 0) (+ (* lo 2) 1)))
            (t
             (prog2$ (raise "illegal character:~x0~%" lst)
                     (sv::make-4vec :upper 0 :lower 0)))))))

(define vcd-parse-chgs (chgs (rslt val-chgs-p) vcd$)
  :returns (rslt val-chgs-p)
  (if (atom chgs) (val-chgs-fix rslt)
    (b* ((chg (first chgs))
         ((when (not (stringp chg)))
          (raise "illegal non string:~x0~%" chg))
         (l (length chg))
         ((when (eql l 0))
          (raise "illegal empty string:~x0~%" chg))
         (ch (char chg 0))
         ((when (eql ch #\r))
          (raise "unsupported real value type:~x0~%" chg))
         ((when (not (member ch '(#\b #\0 #\1 #\x #\z))))
          (raise "unsupported value type:~x0~%" chg))
         (lst (and (eql ch #\b) (str::strtok chg (list #\Space))))
         ((when (and (eql ch #\b) (not (strings-p lst 2))))
          (raise "unsupported vector value:~x0~%" chg))
         (val (cond ((eql ch #\0) 0)
                    ((eql ch #\1) 1)
                    ((eql ch #\x) (sv::make-4vec :upper 1 :lower 0))
                    ((eql ch #\z) (sv::make-4vec :upper 0 :lower 1))
                    (t (vcd-bval (coerce (first lst) 'list) 0 0))))
         (id  (hons-copy (if (eql ch #\b) (second lst) (subseq chg 1 l))))
         (look (hons-get id (vcd$-id-map vcd$)))
         ((when (not look))
          (raise "did not find var for sequence:~x0~%" look)))
      (vcd-parse-chgs (rest chgs) (cons (cons (cdr look) val) rslt) vcd$))))

(define add-vcd-chgs ((time stringp) chgs vcd$)
  (update-vcd$-val-chg-lst
   (cons (make-vcd-val-chg :timestamp time
                           :val-chgs (vcd-parse-chgs chgs () vcd$))
         (vcd$-val-chg-lst vcd$))
   vcd$))

;;;;;;;;;;;;;;;;;;;;;;;;

(defthm append!$-string-listp
  (implies (and (string-listp x) (string-listp y))
           (string-listp (append$! x y)))
  :hints (("Goal" :in-theory (enable append$!))))

(define parse-vcd-def (tag (vals string-listp) vcd$)
  (case tag
    (:comment   (update-vcd$-comments  (append! (vcd$-comments  vcd$) vals) vcd$))
    (:date      (update-vcd$-date      (append! (vcd$-date      vcd$) vals) vcd$))
    (:version   (update-vcd$-version   (append! (vcd$-version   vcd$) vals) vcd$))
    (:timescale (update-vcd$-timescale (append! (vcd$-timescale vcd$) vals) vcd$))
    (:scope     (parse-vcd-scope vals vcd$))
    (:upscope   (parse-vcd-upscope vals vcd$))
    (:var       (parse-vcd-var vals vcd$))
    (t          (prog2$ (raise "Unsupported tag in parse-vcd-def:~x0~%" tag) vcd$))))

(define parse-vcd-defs (defs vcd$)
  (if (atom defs) vcd$
    (b* ((def (first defs))
         ((when (not (and (consp def)
                          (string-listp (cdr def)))))
          (prog2$ (raise "Ill-formed def:~x0~%" def) vcd$))
         (vcd$ (parse-vcd-def (car def) (cdr def) vcd$)))
      (parse-vcd-defs (rest defs) vcd$))))


(define vcd-time-str ((val stringp))
  (if (or (in! val '("$dumpvars" "$dumpoff" "$dumpon" "$dumpall"))
          (and (> (length val) 0) (eql (char val 0) #\#)))
      val
    nil))

(define pull-first-chgs (vals time chgs)
  (if (atom vals) (mv time (rev! chgs) ())
    (b* ((val (first vals))
         ((when (not (stringp val)))
          (mv (raise "illegal. val should be string:~x0~%" val) () ()))
         ((when (equal val ""))
          (pull-first-chgs (rest vals) time chgs))
         ((when (and (not time) (not (vcd-time-str val))))
          (mv (raise "illegal. val not timely:~x0~%" val) () ()))
         ((when (not time))
          (pull-first-chgs (rest vals) (vcd-time-str val) chgs))
         ((when (equal val "$end"))
          (mv time (rev! chgs) (rest vals)))
         ((when (vcd-time-str val))
          (mv time (rev! chgs) vals)))
      (pull-first-chgs (rest vals) time (cons val chgs)))))

(defthm pull-first-chgs-smaller1
  (<= (len (mv-nth 2 (pull-first-chgs x y z))) (len x))
  :rule-classes (:linear :rewrite)
  :hints (("Goal" :in-theory (enable pull-first-chgs))))

(defthm pull-first-chgs-smaller2
  (implies (and (consp x) (not y)) (< (len (mv-nth 2 (pull-first-chgs x y z))) (len x)))
  :rule-classes (:linear :rewrite)
  :hints (("Goal" :in-theory (enable pull-first-chgs))))

(defthm true-listp-rev$!
  (implies (true-listp y) (true-listp (rev$! x y)))
  :hints (("Goal" :in-theory (enable rev$!))))

(defthm vcd-val-chgsp-rev$!
  (implies (and (vcd-val-chgs-p y) (vcd-val-chgs-p x))
           (vcd-val-chgs-p (rev$! x y)))
  :hints (("Goal" :in-theory (enable rev$! vcd-val-chgs-p))))

(define parse-vcd-vals (vals vcd$)
  :measure (len vals)
  (if (atom vals)
      (update-vcd$-val-chg-lst (rev! (vcd$-val-chg-lst vcd$)) vcd$)
    (b* (((mv time chgs rst) (pull-first-chgs vals nil ()))
         ((when (not (stringp time)))
          (prog2$ (raise "timestamp should be string:~x0~%" time)
                  vcd$))
         (vcd$ (add-vcd-chgs time chgs vcd$)))
      (parse-vcd-vals rst vcd$))))

;; BOZO -- abstract the following file reading to being another stobj passed in
;; which has all of the lines from the source file -- either directly read.. or
;; from the output of a decompressor..

(define read-vcd-file-to-vcd$ ((fname stringp) state vcd$)
  (b* ((contents (acl2::read-file-into-string fname))
       ((when (not (stringp contents)))
        (prog2$ (raise "Failed to read file:~x0~%" fname) vcd$))
       (contents (str::strtok contents (list #\Newline)))
       ((mv vals defs) (split-vcd-lines contents ()))
       (vcd$ (parse-init-vcd$ vcd$))
       (vcd$ (parse-vcd-defs defs vcd$))
       (vcd$ (parse-vcd-vals vals vcd$)))
    vcd$))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define strs-fix ((x string-listp))
  :returns (r string-listp)
  (mbe :logic (if (string-listp x) x ()) :exec x))

(defthm append-string-list
  (implies (and (string-listp x) (string-listp y))
           (string-listp (append x y))))

(defthm rev-string-listp
  (implies (string-listp x) (string-listp (rev x))))

(defthm string-list-true-list
  (implies (string-listp x) (true-listp x)))

(define vcd-header-out ((pre stringp) (strs string-listp))
  :returns (r string-listp)
  (strs-fix (append (list pre) strs (list "$end"))))

(defmacro vcd$->header-date      () `(vcd-header-out "$date"      (vcd$-date      vcd$)))
(defmacro vcd$->header-version   () `(vcd-header-out "$version"   (vcd$-version   vcd$)))
(defmacro vcd$->header-timescale () `(vcd-header-out "$timescale" (vcd$-timescale vcd$)))
(defmacro vcd$->header-comments  () `(vcd-header-out "$comment"   (vcd$-comments  vcd$)))

(define vcd$->vcd-header (vcd$)
  :returns (r string-listp)
  (append (vcd$->header-date)
          (vcd$->header-version)
          (vcd$->header-timescale)
          (vcd$->header-comments)))

(define mk-svar (x &key ((d natp) '0))
  :returns (x sv::svar-p)
  (sv::make-svar :name x :delay d :nonblocking nil))

(defconst *svar-top* (mk-svar "top"))

(define drop-last (x)
  (cond ((atom x) x)
        ((atom (rest x)) (rest x))
        (t (cons (first x) (drop-last (rest x))))))

(define drop-var (x)
  (cond ((atom x) x)
        ((atom (rest x)) (first x))
        (t (cons (first x) (drop-var (rest x))))))

(defthm len-drop-last
  (implies (consp x)
           (< (len (drop-last x)) (len x)))
  :hints (("Goal" :in-theory (enable drop-last)))
  :rule-classes (:linear :rewrite))

(defthm svar-name-mk-svar
  (equal (sv::svar->name (mk-svar name :d d)) name)
  :hints (("Goal" :in-theory (enable mk-svar))))

(defthm svar-delay-mk-svar
  (implies (natp d)
           (equal (sv::svar->delay (mk-svar name :d d)) d))
  :hints (("Goal" :in-theory (enable mk-svar))))

(define vcd-scope-path! ((var sv::svar-p) (path sv::svarlist-p))
  :measure (len (sv::svar->name var))
  :returns (path sv::svarlist-p)
  (b* ((vn (sv::svar->name var)))
    (if (atom vn) (sv::svarlist-fix (cons *svar-top* path))
      (vcd-scope-path! (mk-svar (drop-last vn)) 
                       (cons (mk-svar (drop-var vn)) path)))))

(define vcd-scope-path ((var sv::svar-p))
  :returns (path sv::svarlist-p)
  (vcd-scope-path! var (list var)))

(define vcd-upd-scope ((prev sv::svar-p) (next sv::svar-p)
                       (rslt vcd-scope-tbl-p))
  :returns (rslt vcd-scope-tbl-p)
  (b* ((look (cdr (hons-get prev rslt))))
    (vcd-scope-tbl-fix
     (if (in-hons= next look) rslt 
       (hons-acons prev (cons next look) rslt)))))

(define vcd-add-scope ((path sv::svarlist-p) (rslt vcd-scope-tbl-p))
  :returns (rslt vcd-scope-tbl-p)
  (if (or (endp path) (endp (rest path))) (vcd-scope-tbl-fix rslt)
    (vcd-add-scope (rest path) (vcd-upd-scope (first path) (second path) rslt))))

(define vcd-collect-scopes ((vars vcd-out-map-p) 
                            &key ((rslt vcd-scope-tbl-p) ':vcd-collect-scopes))
  :returns (r vcd-scope-tbl-p)
  (if (atom vars) (vcd-scope-tbl-fix rslt)
    (vcd-collect-scopes (rest vars)
                        :rslt (vcd-add-scope (vcd-scope-path (caar vars)) rslt))))

(local (include-book "arithmetic-5/top" :dir :system))

(define vcd-var-seq! ((ndx natp))
  :measure (nfix ndx)
  :returns (r character-listp)
  ;; we can use ascii printable code chars 126 down to 33 (94 characters)
  (if (zp ndx) () (cons (code-char (+ (mod ndx 94) 33))
                        (vcd-var-seq! (floor ndx 94)))))

(define vcd-var-seq ((ndx natp))
  :returns (r character-listp)
  (if (zp ndx) (list #\!) (vcd-var-seq! ndx)))

(define vcd-make-strs-tbl ((vars vcd-out-map-p)
                           &key ((ndx natp) '0) ((rslt vcd-str-map-p) ':vcd-make-strs-tbl))
  :returns (r vcd-str-map-p)
  (if (atom vars) (vcd-str-map-fix (make-fast-alist rslt))
    (vcd-make-strs-tbl (rest vars) :ndx (1+ ndx)
                       :rslt (acons! (caar vars) (coerce (vcd-var-seq ndx) 'string) rslt))))

(progn
(defthm vcd-scope-tbl-fast-alist-fork
  (implies (and (vcd-scope-tbl-p x) (vcd-scope-tbl-p y))
           (vcd-scope-tbl-p (fast-alist-fork x y))))
(defthm vcd-scope-tbl-last
  (implies (vcd-scope-tbl-p x) (vcd-scope-tbl-p (last x))))
)

(define vcd-fill-in-for-output (vcd$)
  (b* ((sc-tbl (vcd-collect-scopes (vcd$-out-tbl vcd$)))
       (sc-tbl (fast-alist-clean sc-tbl))
       (vcd$ (update-vcd$-scope-tbl sc-tbl vcd$))
       (st-tbl (vcd-make-strs-tbl (vcd$-out-tbl vcd$)))
       (vcd$ (update-vcd$-str-tbl st-tbl vcd$)))
    vcd$))

(define last-car (x)
  (cond ((atom x) x)
        ((atom (cdr x)) (car x))
        (t (last-car (cdr x)))))

(define last-cdr (x)
  (cond ((atom x) x)
        ((atom (cdr x)) (cdr x))
        (t (last-cdr (cdr x)))))

(define vcd-output-scope ((vars sv::svarlist-p)
                          &key ((depth natp) '10000) (vcd$ 'vcd$))
  :measure (make-ord (1+ (nfix depth)) (1+ (len vars)) 0)
  :returns (r string-listp)
  (cond ((zp depth)
         (raise "exceeded depth in vcd-output-scope:~x0~%" vars))
        ((endp vars) ())
        (t (b* ((var    (first vars))
                (name   (sv::svar->name var))
                (sz-tbl (vcd$-out-tbl vcd$))
                (look   (hons-get var sz-tbl)))
             (append (if (not look)
                         (b* ((sc-tbl (vcd$-scope-tbl vcd$))
                              (look   (hons-get var sc-tbl))
                              ((when (not look))
                               (raise "no entry in scope-tbl:~x0~%" var)))
                           (append (list (strap! "$scope module " (last-car name) " $end"))
                                   (vcd-output-scope (cdr (hons-get var sc-tbl)) :depth (1- depth))
                                   (list (strap! "$upscope $end"))))
                       (b* ((v-size (cdr look))
                            (st-tbl (vcd$-str-tbl vcd$))
                            (look   (hons-get var st-tbl))
                            ((when (not look))
                             (raise "no entry in strs-tbl:~x0~%" var)))
                         (list (strap! "$var wire " v-size " " (cdr look) " " (last-cdr name) " $end"))))
                     (vcd-output-scope (rest vars) :depth depth))))))

(define vcd$->vars-scope (vcd$)
  :returns (r string-listp)
  (vcd-output-scope (list *svar-top*))) ;; BOZO: need to change to this.. (vcd$-top-mod vcd$))))

(define vcd-bit (up lo)
  :returns (r characterp)
  (if (eql up 0) (if (eql lo 0) #\0 #\z) (if (eql lo 0) #\x #\1)))

(define vcd-bit-seq ((v-size natp) (up integerp) (lo integerp)
                     &key ((rslt character-listp) 'nil))
  :returns (r character-listp :hyp :guard)
  (if (zp v-size) rslt
    (vcd-bit-seq (1- v-size) (logcdr up) (logcdr lo)
                 :rslt (cons (vcd-bit (logcar up) (logcar lo)) rslt))))

(define vcd-slice-line ((v-str stringp) (v-size natp) (val sv::4vec-p))
  :returns (r stringp)
  (b* ((up (sv::4vec->upper val))
       (lo (sv::4vec->lower val)))
    (cond ((eql v-size 0)
           (prog2$ (raise "should not have zero-width variable!") ""))
          ((eql v-size 1)
           (strap! (vcd-bit (logcar up) (logcar lo)) v-str))
          (t
           (strap! "b" (coerce (vcd-bit-seq v-size up lo) 'string) " " v-str)))))

(define vcd-output-slice! ((slice val-chgs-p) &key ((rslt string-listp) 'nil) (vcd$ 'vcd$))
  :returns (r string-listp)
  (if (atom slice) (strs-fix rslt)
    (b* ((var (hons-copy (caar slice)))
         (val (cdar slice))
         (st-tbl (vcd$-str-tbl vcd$))
         (sz-tbl (vcd$-out-tbl vcd$))
         (look (hons-get var st-tbl))
         ((when (not look)) (raise "did not find var in st-tbl:~x0~%" var))
         (v-str (cdr look))
         (look (hons-get var sz-tbl))
         ((when (not look)) (raise "did not find var in sz-tbl:~x0~%" var))
         (v-size (cdr look)))
      (vcd-output-slice! (rest slice)
                         :rslt
                         (cons (vcd-slice-line v-str v-size val) rslt)))))

(define vcd-output-slice ((slice vcd-val-chg-p) &key (vcd$ 'vcd$))
  :returns (r string-listp)
  (b* (((vcd-val-chg slice)))
    (cons slice.timestamp (vcd-output-slice! slice.val-chgs))))

(define vcd-output-vals ((vals vcd-val-chgs-p)
                         &key ((rslt string-listp) 'nil) (vcd$ 'vcd$))
  :returns (r string-listp)
  (if (endp vals) (strs-fix (reverse rslt))
    (vcd-output-vals (rest vals)
                     :rslt (append (vcd-output-slice (first vals)) rslt))))

(define vcd$->vars-vals (vcd$)
  :returns (r string-listp)
  (vcd-output-vals (vcd$-val-chg-lst vcd$)))

(define vcd$->vcd-end-header ()
  :returns (r string-listp)
  (list "$enddefinitions" "$end"))

(in-theory (disable (vcd$->vcd-end-header)))

(define vcd$->out-lines (vcd$)
  :returns (rslt string-listp)
  (append (vcd$->vcd-header vcd$)
          (vcd$->vars-scope vcd$)
          (vcd$->vcd-end-header)
          (vcd$->vars-vals vcd$)))

(define write-vcd$-to-vcd-file ((fname stringp) state vcd$)
  (b* ((vcd$ (vcd-fill-in-for-output vcd$)) 
       (lines (vcd$->out-lines vcd$))
       (state (vcd-write-lines-file fname lines)))
    (mv vcd$ state)))
