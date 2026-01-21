; Leo Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "LEO-EARLY")

(include-book "../definition/flattening")
(include-book "../definition/parser-interface")
(include-book "../definition/syntax-abstraction")
(include-book "../definition/pretty-printer")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *prog*
  "
program irgendetwas.net {
function f (x: u8, const c: u8) -> u8 {
    const d: u8 = c + 1u8;
    return d * x;
}
}
")

(defconst *cst*
  (parse-from-string *prog*))

(defconst *ast*
  (abs-file *cst*))

(defconst *fun*
  (topdecl-function->get (car (programdecl->items (file->program *ast*)))))

(defconst *fenv*
  (make-fenv :constants (omap::update (identifier "c")
                                      (value-u8 4)
                                      nil)
             :curve :edwards-bls12))

(defconst *fun1*
  (flatten-fundecl *fun* *fenv*))

(define pprint-to-string ((lines msg-listp))
  :mode :program
  (b* (((when (endp lines)) "")
       ((mv & str) (fmt1-to-string "~@0" (list (cons #\0 (car lines))) 0)))
    (concatenate 'string str (pprint-to-string (cdr lines)))))

(defconst *prog1*
  (pprint-to-string (pprint-fundecl *fun1* 0)))

(assert-event
 (equal *prog1*
        "function f(x: u8, const c: u8) -> u8 {
    return 5u8 * x;
}
"))
