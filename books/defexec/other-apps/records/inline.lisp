(in-package "ACL2")

;; We define some macros which can be used for performing function inlining in
;; a very basic sense (in particular the function exec-trm would need to be
;; extended to support cond, case, let, and any other macros the user might
;; utilize.) The goal here is not to define a one-size-fits-all solution for
;; supporting inlining, but to instead demonstrate how inlining can be
;; performed through macros and the use of mbe, while still allowing nice
;; functional decomposition and control in the logic. Note that one potential
;; difficulty that a full-fledged :inline support would need to handle is
;; control over the mbe guard proofs which should be equal but may require some
;; guidance to ACL2 to avoid unnecessary effort (i.e. preprocessing,
;; normalization, case-splitting, etc.). Another glaring omission is support
;; for stobjs which is hindered by the still awkward handling of stobj-named
;; parameters for defmacro :(

(defun symbol-binary-append (x y)
  (declare (xargs :guard (and (symbolp x) (symbolp y))))
  (intern (string-append (symbol-name x) (symbol-name y)) "ACL2"))

(defmacro symbol-append (symb &rest symbs)
  (if (endp symbs) symb
    `(symbol-binary-append ,symb (symbol-append ,@symbs))))

(defmacro bind (v a r)
  `(let ((,v ,a)) ,r))

;; obviously, the following would need to be extended (or replaced with a
;; different mechanism altogether -- i.e. packages or function prefixes) in
;; order to be of any practical use.
(defconst *exec-trm-built-ins*
  '(the signed-byte or not integerp consp
    and if car cdr + - * < > <= >= 1+ 1- zp
    bind eq eql g s true-listp nfix
    first second third fourth))

(defun prefix-match (x y)
  (declare (xargs :guard (and (stringp x) (stringp y))))
  (and (> (length x) (length y))
       (equal (subseq x 0 (length y)) y)))

(defun stobj-access-fn (fn)
  (declare (xargs :guard (symbolp fn)))
  (let* ((str (symbol-name fn)))
    (or (prefix-match str "GET-")
        (prefix-match str "UPDATE-"))))

(defun exec-call (fn in-fn)
  (declare (xargs :guard t))
  (not (or (not (symbolp fn))
           (eq fn in-fn)
           (member-eq fn *exec-trm-built-ins*)
           (stobj-access-fn fn))))

(defun exec-fnname (fn)
  (declare (xargs :guard (symbolp fn)))
  (symbol-append fn '$exec))

;; I need to drop-stobjs in the exec portion of the inlined function because
;; of the unfortunate (and silly) restriction on not using stobj names as
;; parameter names for macros (yuck!).

(defun is-stobj-name (arg)
  (declare (xargs :guard t))
  (and (symbolp arg)
       (prefix-match (symbol-name arg) "STOBJ$")))

(defun drop-stobjs (args)
  (declare (xargs :guard t))
  (cond ((atom args) ())
        ((is-stobj-name (first args))
         (drop-stobjs (rest args)))
        (t (cons (first args)
                 (drop-stobjs (rest args))))))

(mutual-recursion
(defun exec-trm (trm in-fn)
  (declare (xargs :guard t))
  (cond
   ((or (atom trm) (quotep trm)) trm)
   ((exec-call (first trm) in-fn)
    (cons (exec-fnname (first trm))
          (drop-stobjs (exec-args (rest trm) in-fn))))
   (t
    (cons (first trm)
          (exec-args (rest trm) in-fn)))))

(defun exec-args (args in-fn)
  (declare (xargs :guard t))
  (if (atom args) ()
    (cons (exec-trm (first args) in-fn)
          (exec-args (rest args) in-fn))))
)

(defun is-exec-decl (decl)
  (declare (xargs :guard t))
  (and (consp decl)
       (symbolp (first decl))
       (member-eq (first decl) '(type ignore))))

(defun parse-exec-decls (decls)
  (declare (xargs :guard (true-listp decls)))
  (cond ((endp decls) ())
        ((is-exec-decl (first decls))
         (cons (list 'declare (first decls))
               (parse-exec-decls (rest decls))))
        (t (parse-exec-decls (rest decls)))))

(defun collect-exec-decls (aux)
  (declare (xargs :guard (true-listp aux)))
  (cond ((endp aux) ())
        ((stringp (first aux))
         (cons (first aux)
               (collect-exec-decls (rest aux))))
        ((and (consp (first aux))
              (true-listp (first aux))
              (eq (first (first aux)) 'declare))
         (append (parse-exec-decls (rest (first aux)))
                 (collect-exec-decls (rest aux))))
        (t (collect-exec-decls (rest aux)))))

(defmacro defun* (fn args &rest aux)
  (declare (xargs :guard (and (symbolp fn)
                              (symbol-listp args)
                              (consp aux)
                              (true-listp aux))))
  (let* ((inline (eq (first aux) :inline))
         (aux (if inline (rest aux) aux))
         (body (car (last aux)))
         (aux (butlast aux 1))
         (exec-decls (collect-exec-decls aux))
         (exec-fn (exec-fnname fn))
         (exec-args (drop-stobjs args)))
    `(progn (defun ,fn ,args ,@aux
              (mbe :logic ,body :exec ,(exec-trm body fn)))
            (defabbrev ,exec-fn ,exec-args ,@exec-decls
              ,(if inline body (cons fn args))))))

;; Ok, a simple contrived test. We define a simple countdown loop using defun*
;; with certain functions inlined versus a version written with defun.

(defun* decr-fast (n) :inline
  (declare (xargs :guard (natp n))
           (type (signed-byte 29) n))
  (the (signed-byte 29) (1- n)))

(defun* zp-fast (n) :inline
  (declare (xargs :guard (natp n))
           (type (signed-byte 29) n))
  (or (not (integerp n)) (<= n 0)))

(defun* loop-fast (n)
  (declare (xargs :guard (natp n))
           (type (signed-byte 29) n))
  (if (zp-fast n) n (loop-fast (decr-fast n))))

(defun decr-slow (n)
  (declare (xargs :guard (natp n))
           (type (signed-byte 29) n))
  (the (signed-byte 29) (1- n)))

(defun zp-slow (n)
  (declare (xargs :guard (natp n))
           (type (signed-byte 29) n))
  (or (not (integerp n)) (<= n 0)))

(defun loop-slow (n)
  (declare (xargs :guard (natp n))
           (type (signed-byte 29) n))
  (if (zp-slow n) n (loop-slow (decr-slow n))))

;; We end up with the following execution times under Franz Lisp on Linux/x86:
;;    (time (loop-fast 200000000)) = 0.7 seconds
;;    (time (loop-slow 200000000)) = 6.0 seconds

;; macros from the paper defined using defun*:

; Changed August 2012 by Matt K.: Defun-inline is now the name of an ACL2
; system macro, so we rename the book version below to defun/inline.

(defmacro defun/inline (name args &rest x)
  `(defun* ,name ,args :inline ,@x))

(defmacro defun-exec (name args &rest x)
  `(defun* ,name ,args ,@x))





