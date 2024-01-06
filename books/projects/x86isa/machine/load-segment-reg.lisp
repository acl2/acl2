(in-package "X86ISA")

(include-book "state")
(include-book "linear-memory")
(include-book "segmentation")

;; ----------------------------------------------------------------------
;; The model state has two seperate sets of fields for system segment registers
;; and regular segment registers. The code to load these is basically identical
;; except for using different updaters. We use the following function to generate
;; load-segment-reg and load-system-segment-reg.

;; TODO make this throw the proper exceptions when you go past the limit on the GDT
;; TODO make it behave properly when the selector is 0
;; TODO add support for the other bits in the selector
;; TODO handle failure reading descriptor
;; TODO check limits on the gdtr/ldtr
(define define-segment-register-loader ((typ :type (member seg ssr)))
  (b* ((regular-segment? (equal typ 'seg))
       (!reg-visiblei (acl2::packn (list '! typ '-visiblei)))
       (!reg-hidden-basei (acl2::packn (list '! typ '-hidden-basei)))
       (!reg-hidden-limiti (acl2::packn (list '! typ '-hidden-limiti)))
       (!reg-hidden-attri (acl2::packn (list '! typ '-hidden-attri))))
      `(define ,(acl2::packn (list 'load- (if regular-segment? 'segment 'system-segment) '-reg))
         ((seg-reg :type (integer 0 ,(1- (if regular-segment? *segment-register-names-len* *ldtr-tr-names-len*))))
          (selector :type (unsigned-byte 16))
          x86)
         :returns (x86 x86p :hyp (x86p x86))
         ;; We set the CS here to perform a privileged memory read even if we're not in privilege level 0
         (b* ((cs (seg-visiblei *cs* x86))
              (x86 (!seg-visiblei *cs* (!segment-selectorBits->rpl 0 cs) x86))
              (descriptor-addr (+ (i64 (gdtr/idtrBits->base-addr
                                         (stri (if (logtest selector #x4)
                                                 *ldtr*
                                                 *gdtr*)
                                               x86)))
                                  (logand selector #xFFF8)))
              ((unless (canonical-address-p descriptor-addr)) x86)
              ((mv & descriptor x86) (rml128 descriptor-addr :r x86))
              (x86 (,!reg-visiblei *cs* cs x86))
              (x86 (,!reg-visiblei seg-reg selector x86))
              (limit (logior (logand descriptor #xFFFF)
                             (logand (ash descriptor (- 16 48)) #xF0000)))
              (x86 (,!reg-hidden-limiti seg-reg limit x86))
              (base (logior (logand (ash descriptor -16) #xFFFFFF)
                            (logand (ash descriptor (- 24 56)) #xFFFFFFFFFF000000)))
              (x86 (,!reg-hidden-basei seg-reg base x86))
              (attr (make-code-segment-attr-field (logand #xFFFFFFFFFFFFFFFF descriptor)))
              (x86 (,!reg-hidden-attri seg-reg attr x86)))
             x86))))

(make-event (define-segment-register-loader 'seg))
(make-event (define-segment-register-loader 'ssr))
