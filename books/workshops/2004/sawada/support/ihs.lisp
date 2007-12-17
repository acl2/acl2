(in-package "ACL2")
(deflabel before-loading-ihs)
(include-book "../../../../ihs/ihs-definitions")
(include-book "../../../../ihs/logops-lemmas")
;(include-book "/usr/local/src/acl2-v2.7/books/ihs/ihs-lemmas")

(defthm bsp-position-cons
    (equal (bsp-position (cons s p)) p)
  :hints (("goal" :in-theory (enable bsp-position))))

(defthm bsp-size-cons
    (equal (bsp-size (cons s p)) s)
  :hints (("goal" :in-theory (enable bsp-size))))

(defthm bspp-cons
    (implies (and (integerp s) (<= 0 s) (integerp p) (<= 0 p))
	     (bspp (cons s p)))
  :hints (("goal" :in-theory (enable bspp))))

(deflabel after-loading-ihs)

(deftheory default-IHS-incompatibles
    '(oddp evenp floor mod rem truncate expt
      loghead logtail logior lognot logand logand
      logeqv logorc1 logorc2 logandc1 logandc2 logcount
      lognand lognor logxor))

(in-theory
 (set-difference-theories (current-theory :here)
	  (set-difference-theories  (universal-theory 'after-loading-IHS)
				    (universal-theory 'before-loading-IHS))))

(in-theory (disable default-ihs-incompatibles))
(in-theory
 (enable
;  ihs-math				; From "math-lemmas"
;  quotient-remainder-rules		; From "quotient-remainder-lemmas"
  logops-lemmas-theory))		; From "logops-lemmas"

(in-theory (disable (force)))

;(in-theory (disable
;	    (:generalize MOD-X-Y-=-X+Y)
;	    (:generalize MOD-X-Y-=-X)
;	    (:generalize MOD-=-0)
;	    (:generalize FLOOR-TYPE-4)
;	    (:generalize FLOOR-TYPE-3)
;	    (:generalize FLOOR-TYPE-2)
;	    (:generalize FLOOR-TYPE-1)
;	    (:generalize FLOOR-BOUNDS)
;	    (:generalize FLOOR-=-X/Y)
;))
