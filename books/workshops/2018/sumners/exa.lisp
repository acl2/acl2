(in-package "ACL2")

;; local
(include-book "std/io/top" :dir :system)
(include-book "arithmetic-5/top" :dir :system)

;; support
(include-book "std/util/define" :dir :system)
(include-book "std/util/defconsts" :dir :system)
(include-book "std/util/defval" :dir :system)
(include-book "std/util/bstar" :dir :system)
(include-book "centaur/sv/svex/svex" :dir :system)
(include-book "misc/total-order" :dir :system)
(include-book "std/strings/strprefixp" :dir :system)

;; nxtypes
(include-book "std/util/define" :dir :system)
(include-book "std/util/defconsts" :dir :system)
(include-book "std/util/defval" :dir :system)
(include-book "std/util/bstar" :dir :system)
(include-book "misc/random" :dir :system)
(include-book "centaur/sv/mods/compile" :dir :system)
(include-book "centaur/fty/top" :dir :system)

;; extypes
(include-book "centaur/satlink/litp" :dir :system)

;; nxtbl
(include-book "std/util/define" :dir :system)
(include-book "std/util/defconsts" :dir :system)
(include-book "std/util/defval" :dir :system)
(include-book "std/util/bstar" :dir :system)
(include-book "misc/random" :dir :system)
(include-book "centaur/sv/mods/compile" :dir :system)
(include-book "std/io/read-file-lines" :dir :system)
(include-book "centaur/fty/top" :dir :system)
(include-book "std/strings/strprefixp" :dir :system)

;; svcnf
(include-book "std/io/read-file-lines-no-newlines" :dir :system)
(include-book "std/strings/strtok" :dir :system)
(include-book "centaur/satlink/top" :dir :system)
(include-book "centaur/aignet/top" :dir :system)
(include-book "centaur/aignet/transforms" :dir :system)
(include-book "centaur/aignet/ipasir" :dir :system)
(include-book "centaur/sv/svex/top" :dir :system)

;; vcd
(include-book "std/util/define" :dir :system)
(include-book "std/util/defconsts" :dir :system)
(include-book "std/util/defval" :dir :system)
(include-book "std/util/bstar" :dir :system)
(include-book "std/strings/strtok" :dir :system)
(include-book "std/strings/substrp" :dir :system)
(include-book "centaur/sv/svex/svex" :dir :system)
(include-book "centaur/fty/top" :dir :system)
(include-book "misc/file-io" :dir :system)
(include-book "std/io/base" :dir :system)

;; exbase
(include-book "centaur/ipasir/ipasir-logic" :dir :system)
(include-book "centaur/ipasir/ipasir-tools" :dir :system)
(include-book "centaur/misc/seed-random" :dir :system)
(include-book "misc/file-io" :dir :system)
(include-book "misc/random" :dir :system)

;; exloop
(include-book "centaur/ipasir/ipasir-logic" :dir :system)
(include-book "centaur/ipasir/ipasir-tools" :dir :system)
(include-book "centaur/misc/seed-random" :dir :system)
(include-book "misc/file-io" :dir :system)
(include-book "misc/random" :dir :system)

;; exsim
(include-book "std/util/defconsts" :dir :system)
(include-book "std/util/defval" :dir :system)
(include-book "centaur/sv/vl/top" :dir :system)
(include-book "centaur/sv/mods/compile" :dir :system)
(include-book "std/io/read-file-lines" :dir :system)
(include-book "centaur/vl/loader/top" :dir :system)
(include-book "centaur/ipasir/ipasir-logic" :dir :system)
(include-book "centaur/ipasir/ipasir-tools" :dir :system)
(include-book "centaur/misc/seed-random" :dir :system)
(include-book "misc/file-io" :dir :system)
(include-book "misc/random" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; functions for building SV design from Verilog files:
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(encapsulate 
 (((compute-vl-conf *) => * 
   :formals (mod) 
   :guard (stringp mod)))

 (local (defun compute-vl-conf (mod)
          (declare (xargs :guard (stringp mod))
                   (ignore mod))
          (vl::make-vl-loadconfig :start-files (list "") :search-path '())))
 
 (defthm compute-vl-conf-returns-vl-loadconfig
   (vl::vl-loadconfig-p (compute-vl-conf mod))))

;; The following function is the default name for a function
;; which we use to map mod-name to a vl-config object which is
;; used to read in the design:
;;
(define compute-vl-conf-inst ((mod stringp))
  :returns (rslt vl::vl-loadconfig-p)
  (b* ((v-file (string-append mod ".v")))
    (vl::make-vl-loadconfig :start-files (list v-file) :search-path '())))

(defattach compute-vl-conf compute-vl-conf-inst)

(define load-processor-vl-design ((vl-config vl::vl-loadconfig-p) state)
  :returns (mv (design vl::vl-design-p) state)
  (b* (((mv loadresult state) (vl::vl-load vl-config))
       (design (vl::vl-loadresult->design loadresult))
       (reportcard (vl::vl-design-reportcard design))
       (- (acl2::cw-unformatted (vl::vl-reportcard-to-string reportcard))))
   (mv design state)))

(define trans-vl-design-to-sv-design ((top-mod stringp) (vl-design vl::vl-design-p))
  :returns (sv-des sv::design-p)
  (b* ((config (vl::make-vl-simpconfig))
       ((mv err sv-des ?good ?bad)
        (vl::vl-design->svex-design top-mod vl-design config))
       ((when err)
        ;;(vl::vl-design->mods bad)
        ;;(vl::vl-design->warnings bad)
        ;;(vl::vl-design->warnings good)))
        (prog2$ (raise "Error/warning returned by vl-design->svex-design: ~x0~%" err)
                (sv::make-design :modalist () :top t))))
    sv-des))

(define vl->sv-design ((mod-name stringp)
                       &key
                       ((top-mod stringp) '"top")
                       (state 'state))
  :returns (mv (rslt sv::design-p) state)
  (b* ((vl-config            (compute-vl-conf mod-name))
       ((mv vl-design state) (load-processor-vl-design vl-config state))
       (sv-design            (trans-vl-design-to-sv-design top-mod vl-design)))
    (mv sv-design state)))

; acl2 < exa.lsp > exa.out
;
;; now quit and save image:
;; :q
;; (save-exec "exa" "Adds supporting libraries for building exsim")
;
;; NOTE:: This can never be included in an image.. it must be dynamically
;; included at runtime to ensure that the corresponding library is loaded and
;; linked correctly.. the library is not saved as part of the image and it
;; fails if you try to include it in the image:
;;
;; (include-book "centaur/ipasir/ipasir-backend" :dir :system)
