;; vcdtypes.lisp
;;
;; Book defining FTY types used in the vcd.lisp book which reads
;; in and writes out VCD files through the vcd$ stobj defined in
;; that book (which has many fields of types defined here)

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
(include-book "centaur/sv/svex/svex" :dir :system)
(include-book "centaur/fty/top" :dir :system)
(include-book "support")

(fty::defprod vcd-var-elem
              ((v-size natp)
               (v-type symbolp)
               (v-vec  stringp)
               (v-id   stringp)))

(fty::defalist vcd-var-map
               :key-type sv::svar-p
               :val-type vcd-var-elem)

(fty::defalist vcd-id-map
               :key-type stringp
               :val-type sv::svar-p)

(fty::defalist vcd-inst-map ;; maps inst name to svars which are insts
               :key-type stringp
               :val-type sv::svarlist-p)

(fty::defalist vcd-out-map
               :key-type sv::svar-p
               :val-type natp)

(fty::defalist vcd-str-map
               :key-type sv::svar-p
               :val-type stringp)

(fty::defalist vcd-scope-tbl
               :key-type sv::svar-p
               :val-type sv::svarlist-p)

(fty::defalist vcd-scope-lst
               :key-type any-p
               :val-type symbolp
               :true-listp t)

(fty::deflist vcd-scopes-lst
              :elt-type vcd-scope-lst-p
              :true-listp t)

(fty::defalist val-chgs
               :key-type sv::svar-p
               :val-type sv::4vec-p)

(fty::defprod vcd-val-chg
              ((timestamp stringp)
               (val-chgs  val-chgs-p)))

(fty::deflist vcd-val-chgs
              :elt-type vcd-val-chg-p
              :true-listp t)

(fty::defalist vcd-child-map
               :key-type sv::svar-p
               :val-type sv::svar-p)

(fty::defalist vcd-parent-map
               :key-type sv::svar-p
               :val-type sv::svarlist-p)


