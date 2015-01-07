#|$ACL2s-Preamble$;
(include-book ;; Newline to fool ACL2/cert.pl dependency scanner
 "../portcullis")
(acl2::begin-book t);$ACL2s-Preamble$|#

#|
API to register a type
author: harshrc
file name: register-type.lisp
date created: [2014-08-06 Sun]
data last modified: [2014-08-06]
|#

(in-package "DEFDATA")

(include-book "defdata-util")


(defun make-enum-uniform-defun-ev (name enum)
  (declare (xargs :guard (symbolp enum)))
  `((defund ,name (m seed)
     (declare (ignorable m))
     (declare (type (unsigned-byte 31) seed))
     (declare (xargs :verify-guards nil ;todo
                     :mode :program ;todo
                     :guard (and (natp m)
                                 (unsigned-byte-p 31 seed))))
; 12 July 2013 - adding uniform random seed distribution to cgen enum
; we will take advantage of the recent addition for an uniform
; interface to both infinite and finite enum (defconsts)
     (mv-let (n seed)
             (random-natural-seed seed)
             (mv (,enum n) (the (unsigned-byte 31) seed))))))






(defun well-formed-metadata-entry-p (key val wrld)
  (case key
    (:predicate  (allows-arity val 1 wrld))
    (:enumerator (allows-arity val 1 wrld)) 
    (:enum/acc   (allows-arity val 2 wrld))
    (:enum/test  (allows-arity val 1 wrld))
    (:enum/test/acc (allows-arity val 2 wrld))
    (:equiv (allows-arity val 2 wrld))
    (:equiv-fixer (allows-arity val 1 wrld))
    (:lub (predicate-name val))
    (:glb (predicate-name val)) 
    (:sampling (possible-constant-values-p val))
    (:size (or (eq 't val) (natp val)))
    (:verbose (booleanp val))
    (:theory-name (proper-symbolp val))
    (otherwise t) ;dont be strict.
    ))

(defun ill-formed-metadata-entry-msg1 (key val)
  (declare (ignorable val))
  (case key
    (:predicate        "~x0 should be a 1-arity fn")
    (:enumerator       "~x0 should be a 1-arity fn") 
    (:enum/acc         "~x0 should be a 2-arity fn")
    (:enum/test        "~x0 should be a 1-arity fn")
    (:enum/test/acc    "~x0 should be a 2-arity fn")
    (:equiv            "~x0 should be a 2-arity fn")
    (:equiv-fixer      "~x0 should be a 1-arity fn")
    (:lub              "~x0 should be a type name")
    (:glb              "~x0 should be a type name") 
    (:sampling         "~x0 should be a list of constants" )
    (:size             "~x0 should be either 't or a natural")
    (:verbose         "~x0 should be a boolean")
    (:theory-name      "~x0 should be a symbol")
    (otherwise         "Unhandled case!")
    ))


(defloop well-formed-type-metadata-p (al wrld)
  (for ((p in al)) (always (well-formed-metadata-entry-p (car p) (cdr p) wrld))))

; TYPE METADATA TABLE

(table type-metadata-table nil nil :clear)


(program)
(defun ill-formed-metadata-entry-msg (key val wrld)
  (and (not (well-formed-metadata-entry-p key val wrld))
       (b* ((x0-str (ill-formed-metadata-entry-msg1 key val))
            ((mv & msg) (acl2::fmt1!-to-string x0-str (acons #\0 val '()) 0)))
         msg)))


(defloop ill-formed-type-metadata-msg (al wrld)
  (for ((p in al)) (thereis (ill-formed-metadata-entry-msg (car p) (cdr p) wrld))))

;TODO
; Q: howto to generate an enumerator or fixer from a predicate def
; 11 June 2014 - 2am

; A: We will take the inverse of P defined in defdata paper i.e. we
; will map each predicate expression to a core defdata
; expression. Once we have it, we will use E defined in defdata paper
; to generate the enumerator expression. To furthur generate a fixer,
; we can take the acl2-count or size of the argument (a value in the
; domain of the fixer) and pass it through the enumerator definition
; to obtain the result of the fixer function. But we will probably use
; a separate F interpretation to directly generate a fixer from the
; core defdata expressopn. Like P, we will store P^-1 in the builtin
; combinator table.


(defconst *register-type-keywords*
  '(:predicate :enumerator ;mandatory names
               :enum/acc :enum/test :enum/test/acc :equiv :equiv-fixer ;names
               :lub :glb
               :sampling
               :size
               :verbose :hints
               :theory-name
               :clique :def :normalized-def :prettyified-def ;defdata
               ))

(defun register-type-fn (name args ctx wrld)
  (b* (((mv kwd-alist rest) (extract-keywords ctx *register-type-keywords* args nil))
       ((when rest) (er hard? ctx "~| Extra args: ~x0~%" rest))
       ((unless (proper-symbolp name)) (er hard? ctx "~| ~x0 should be a proper symbol.~%" name))
       
       ((when (assoc-eq name (table-alist 'type-metadata-table wrld)))
        (er hard? ctx "~| ~x0 is already a registered defdata type.~%" name))

       ((unless (well-formed-type-metadata-p kwd-alist wrld))
        (er hard? ctx "~| ~s0~%" (ill-formed-type-metadata-msg kwd-alist wrld)))
        
       (enum (get1 :enumerator  kwd-alist))
       (enum/acc (get1 :enum/acc  kwd-alist))
       (enum/test (get1 :enum/test  kwd-alist))
       (enum/test/acc (get1 :enum/test/acc  kwd-alist))
       (enum/acc-default (s+ enum '|/ACC|))
       (enum/test/acc-default (s+ enum/test '|/ACC|))
       (kwd-alist (if enum/test
                      (put-assoc-eq :enum/test/acc (or enum/test/acc enum/test/acc-default) kwd-alist)
                  kwd-alist))
       (kwd-alist (put-assoc-eq :enum/acc (or enum/acc enum/acc-default) kwd-alist))
       (kwd-alist (put-assoc-eq :size (or (get1 :size kwd-alist) 't) kwd-alist))
       (kwd-alist (put-assoc-eq :theory-name (or (get1 :theory-name kwd-alist) (s+ name 'theory)) kwd-alist))
       )
    
       
  `( ;(IN-THEORY (DISABLE ,enum))
    ,@(and (not enum/acc) (make-enum-uniform-defun-ev enum/acc-default enum))
    ,@(and enum/test (not enum/test/acc) (make-enum-uniform-defun-ev enum/test/acc-default enum/test))
    (TABLE TYPE-METADATA-TABLE ',name ',kwd-alist))))

(defmacro register-type (name &rest keys) 
  (b* ((verbosep (let ((lst (member :verbose keys)))
                   (and lst (cadr lst))))
       (ctx 'register-type)
       ((unless (and (member :predicate keys) (member :enumerator keys)))
        (er hard ctx "~| Keyword args predicate, enumerator are mandatory.~%")))
    `(with-output ,@(and (not verbosep) '(:off :all)) :stack :push
       (make-event
        (cons 'progn
              (register-type-fn ',name ',keys ',ctx (w state)))))))





(defconst *defdata-attach-overridable-keywords* 
  '(:predicate :enumerator :size :clique :def :normalized-def :prettyified-def)) ;add more later

(defconst *defdata-attach-keywords* (append '(:test-enumerator ;alias afor :enum/test
                                              :enum/test 
                                              :equiv :equiv-fixer :sampling)
                                            *defdata-attach-overridable-keywords*))


;TODO: The following form is currently quite limited. Extend it later to be more general.
(defmacro defdata-attach  (name &rest keys)
  (b* ((verbosep (let ((lst (member :verbose keys)))
                   (and lst (cadr lst))))
       (override-ok-p (let ((lst (member :override-ok keys)))
                        (and lst (cadr lst))))
       (keys (remove-keywords-from-args '(:verbose :override-ok) keys)))
   
  `(with-output 
    ,@(and (not verbosep) '(:off :all)) :stack :push
    (make-event
        (cons 'progn
              (defdata-attach-fn ',name ',keys ',verbosep ',override-ok-p (w state)))))))

         
(defun defdata-attach-fn (name keys verbosep override-ok-p wrld)
  (b* ((ctx 'defdata-attach)
       ((unless (assoc-eq name (table-alist 'type-metadata-table wrld)))
        (er hard? ctx "~x0 is not a recognized type. Use register-type to register it.~%" name))
       
       ((mv kwd-alist rest) (extract-keywords ctx *defdata-attach-keywords* keys nil))
       ((when rest) (er hard? ctx "~| Extra args: ~x0~%" rest))
       ((unless (= 1 (len kwd-alist)))
        (er hard? ctx "~| Exactly one keyword argument is allowed at a time. You have provided multiple: ~x0~%" keys))
       
       ;;support the alias to enum/test -- legacy issue
       (test-enumerator (get1 :test-enumerator kwd-alist))
       (kwd-alist (if test-enumerator
                      (put-assoc-eq :enum/test test-enumerator (delete-assoc-eq :test-enumerator kwd-alist))
                    kwd-alist))
       (- (cw? verbosep "~|Got kwd-alist: ~x0~%" kwd-alist))
       ((unless (well-formed-type-metadata-p kwd-alist wrld))
        (er hard? ctx "~| ~s0~%" (ill-formed-type-metadata-msg kwd-alist wrld)))

       ;;check if key is overridable
       ((when (and (subsetp (strip-cars kwd-alist) *defdata-attach-overridable-keywords*)
                   (not override-ok-p)))
        (er hard? ctx "~| ~x0 can only be overrriden if :override-ok t is provided.~%" keys))
       
       (existing-kwd-alist (cdr (assoc-eq name (table-alist 'type-metadata-table wrld))))
       (kwd-alist (union-alist2 kwd-alist existing-kwd-alist))
       ;(- (cw? verbosep "~|After union: kwd-alist: ~x0~%" kwd-alist))
       (enum/test (get1 :enum/test  kwd-alist))
       (enum/test/acc (get1 :enum/test/acc  kwd-alist))
       (enum/test/acc-default (s+ enum/test '|/ACC|))
       (kwd-alist (put-assoc-eq :enum/test/acc (or enum/test/acc enum/test/acc-default) kwd-alist))
       )
    
       
    `(,@(and enum/test (not enum/test/acc) (make-enum-uniform-defun-ev enum/test/acc-default enum/test))
      (TABLE TYPE-METADATA-TABLE ',name ',kwd-alist :put))))