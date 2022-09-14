#|$ACL2s-Preamble$;
(ld "acl2s-pkg.lsp")

(acl2::begin-book t :ttags ((:acl2s-graphics)));$ACL2s-Preamble$|#


(in-package "ACL2")

(include-book "canonical-print")

(defconst *graphics-defuns*
  '((defun GRAPHICS-EVENT-INPUT-STREAMP (X)
      (DECLARE (XARGS :GUARD T :VERIFY-GUARDS T)
               (IGNORE X))
      T)
    (defun GRAPHICS-OP-RESPONSE-STREAMP (X)
      (DECLARE (XARGS :GUARD T :VERIFY-GUARDS T)
               (IGNORE X))
      T)
    (defun GRAPHICSP (GRAPHICS)
      (COND ((THE-LIVE-STOBJP GRAPHICS) T)
            (T (AND (TRUE-LISTP GRAPHICS)
                    (= (LENGTH GRAPHICS) 2)
                    (GRAPHICS-EVENT-INPUT-STREAMP (NTH 0 GRAPHICS))
                    (GRAPHICS-OP-RESPONSE-STREAMP (NTH 1 GRAPHICS))))))
    (defun CREATE-GRAPHICS NIL
      (er hard 'create-graphics
          "Execution of this function has been disabled."))
    (defun GRAPHICS-EVENT-INPUT-STREAM (GRAPHICS)
      (declare (ignore graphics))
      (er hard 'graphics-event-input-stream
          "Execution of this function has been disabled."))
    (defun UPDATE-GRAPHICS-EVENT-INPUT-STREAM (V GRAPHICS)
      (declare (ignore v graphics))
      (er hard 'update-graphics-event-input-stream
          "Execution of this function has been disabled."))
    (defun GRAPHICS-OP-RESPONSE-STREAM (GRAPHICS)
      (declare (ignore graphics))
      (er hard 'graphics-op-response-stream
          "Execution of this function has been disabled."))
    (defun UPDATE-GRAPHICS-OP-RESPONSE-STREAM (V GRAPHICS)
      (declare (ignore v graphics))
      (er hard 'update-graphics-op-response-stream
          "Execution of this function has been disabled."))))



(defconst *graphics-replacement-cltl-command*
  `(DEFSTOBJ
     GRAPHICS
     *THE-LIVE-GRAPHICS* (VECTOR 'NIL 'NIL)

     ,(strip-cdrs *graphics-defuns*)
     
     (DEFSTOBJ-TEMPLATE
      (NIL)
      (GRAPHICSP . CREATE-GRAPHICS)
      ((DEFSTOBJ-FIELD-TEMPLATE
           ((GRAPHICS-EVENT-INPUT-STREAMP . T) NIL)
           (GRAPHICS-EVENT-INPUT-STREAM . UPDATE-GRAPHICS-EVENT-INPUT-STREAM)
           NIL NIL)
       (DEFSTOBJ-FIELD-TEMPLATE
           ((GRAPHICS-OP-RESPONSE-STREAMP . T) NIL)
           (GRAPHICS-OP-RESPONSE-STREAM . UPDATE-GRAPHICS-OP-RESPONSE-STREAM)
           NIL NIL))
      NIL NIL)

     ;; (GRAPHICSP CREATE-GRAPHICS
     ;;            ((GRAPHICS-EVENT-INPUT-STREAMP T NIL GRAPHICS-EVENT-INPUT-STREAM
     ;;                                           UPDATE-GRAPHICS-EVENT-INPUT-STREAM
     ;;                                           NIL NIL NIL)
     ;;             (GRAPHICS-OP-RESPONSE-STREAMP T NIL GRAPHICS-OP-RESPONSE-STREAM
     ;;                                           UPDATE-GRAPHICS-OP-RESPONSE-STREAM
     ;;                                           NIL NIL NIL))
     ;;            NIL NIL)
     
     ((GRAPHICS-EVENT-INPUT-STREAMP (X)
                                    (DECLARE (XARGS :GUARD T :VERIFY-GUARDS T)
                                             (IGNORE X))
                                    T)
      (GRAPHICS-OP-RESPONSE-STREAMP (X)
                                    (DECLARE (XARGS :GUARD T :VERIFY-GUARDS T)
                                             (IGNORE X))
                                    T)
      (GRAPHICSP (GRAPHICS)
                 (DECLARE (XARGS :GUARD T :VERIFY-GUARDS T))
                 (AND (TRUE-LISTP GRAPHICS)
                      (= (LENGTH GRAPHICS) 2)
                      (GRAPHICS-EVENT-INPUT-STREAMP (NTH 0 GRAPHICS))
                      (GRAPHICS-OP-RESPONSE-STREAMP (NTH 1 GRAPHICS))
                      T))
      (CREATE-GRAPHICS NIL
                       (DECLARE (XARGS :GUARD T :VERIFY-GUARDS T))
                       (LIST 'NIL 'NIL))
      (GRAPHICS-EVENT-INPUT-STREAM (GRAPHICS)
                                   (DECLARE (XARGS :GUARD (GRAPHICSP GRAPHICS)
                                                   :VERIFY-GUARDS T))
                                   (NTH 0 GRAPHICS))
      (UPDATE-GRAPHICS-EVENT-INPUT-STREAM
       (V GRAPHICS)
       (DECLARE (XARGS :GUARD (GRAPHICSP GRAPHICS)
                       :VERIFY-GUARDS T))
       (UPDATE-NTH 0 V GRAPHICS))
      (GRAPHICS-OP-RESPONSE-STREAM (GRAPHICS)
                                   (DECLARE (XARGS :GUARD (GRAPHICSP GRAPHICS)
                                                   :VERIFY-GUARDS T))
                                   (NTH 1 GRAPHICS))
      (UPDATE-GRAPHICS-OP-RESPONSE-STREAM
       (V GRAPHICS)
       (DECLARE (XARGS :GUARD (GRAPHICSP GRAPHICS)
                       :VERIFY-GUARDS T))
       (UPDATE-NTH 1 V GRAPHICS)))))


(defttag :acl2s-graphics)

(include-book "hacking/hacker" :dir :system)
(progn+all-ttags-allowed
 (include-book "hacking/all" :dir :system :ttags :all))
(subsume-ttags-since-defttag)


; modified defstobj
(defcode
  :loop
  (defstobj graphics
    (graphics-event-input-stream :type t :initially nil)
    (graphics-op-response-stream :type t :initially nil)))

(replace-last-cltl-command *graphics-replacement-cltl-command*)

(make-event
 `(defcode
    :compile
    ,*graphics-defuns*))


; pop-graphics-event
(defun-bridge pop-graphics-event (graphics)
  :logic-declare (xargs :stobjs graphics)
  :logic
  (let ((ev-lst (graphics-event-input-stream graphics)))
    (if (consp ev-lst)
      (let ((graphics (update-graphics-event-input-stream (cdr ev-lst) graphics)))
        (mv (car ev-lst) graphics))
      (mv nil graphics)))
  :raw
  (if (the-live-stobjp graphics)
    (prog2$ (cw "$GrApHiCs-EvEnT{$~%")
            (mv-let (erp v st)
                    (read-object *standard-oi* *the-live-state*)
                    (declare (ignore st))
                    (prog2$ (cw "$GrApHiCs-EvEnT}$~%")
                            (if erp
                              (mv nil graphics)
                              (mv v graphics)))))
    (let ((ev-lst (graphics-event-input-stream graphics)))
      (if (consp ev-lst)
        (let ((graphics (update-graphics-event-input-stream (cdr ev-lst) graphics)))
          (mv (car ev-lst) graphics))
        (mv nil graphics)))))

; push-graphics-op
(defun-bridge push-graphics-op (op graphics) 
  :logic-declare (xargs :stobjs graphics)
  :logic
  (update-graphics-op-response-stream
   (cons (cons op ;the operation
               ;; and what's left of the event stream
               ;; (so that the "timing" is recorded/implied)
               (graphics-event-input-stream graphics))
         (graphics-op-response-stream graphics))
   graphics)
  :raw
  (let ((state *the-live-state*))
    (if (the-live-stobjp graphics)
      (prog2$ (mv-nth 1 ; cheating
                      (acl2s-hooks::fmx-canonical
                       "$GrApHiCs-Op{$~%~x0~%$GrApHiCs-Op}$~%" op))
              graphics)
      (update-graphics-op-response-stream
       (cons (cons op ;the operation
                   ;; and what's left of the event stream
                   ;; (so that the "timing" is recorded/implied)
                   (graphics-event-input-stream graphics))
             (graphics-op-response-stream graphics))
       graphics))))
