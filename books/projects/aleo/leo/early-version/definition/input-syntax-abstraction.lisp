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

(include-book "input-files")
(include-book "syntax-abstraction")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ input-syntax-abstraction
  :parents (abstract-syntax)
  :short "Mapping from concrete to abstract syntax, for Leo input files."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is analogous to @(see syntax-abstraction),
     and partly based on it,
     but for Leo input files instead of Leo code files."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-input-type ((tree abnf::treep))
  :returns (intype input-type-resultp)
  :short "Abstract an @('input-type') to an input type."
  (b* (((okf tree) (abnf::check-tree-nonleaf-1-1 tree "input-type"))
       ((okf type) (abs-type tree)))
    (input-type type))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-input-expression ((tree abnf::treep))
  :returns (inexpr input-expression-resultp)
  :short "Abstract an @('input-expression') to an input expression."
  (b* (((okf tree) (abnf::check-tree-nonleaf-1-1 tree "input-expression"))
       ((okf expr) (abs-expression tree)))
    (input-expression expr))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-input-item ((tree abnf::treep))
  :returns (initem input-item-resultp)
  :short "Abstract an @('input-item') to an input item."
  (b* (((okf (abnf::tree-list-tuple6 sub))
        (abnf::check-tree-nonleaf-6 tree "input-item"))
       ((okf tree) (abnf::check-tree-list-1 sub.1st))
       ((okf ident) (abs-identifier tree))
       ((okf tree) (abnf::check-tree-list-1 sub.2nd))
       ((okf &) (abnf::check-tree-ichars tree ":"))
       ((okf tree) (abnf::check-tree-list-1 sub.3rd))
       ((okf intype) (abs-input-type tree))
       ((okf tree) (abnf::check-tree-list-1 sub.4th))
       ((okf &) (abnf::check-tree-ichars tree "="))
       ((okf tree) (abnf::check-tree-list-1 sub.5th))
       ((okf inexpr) (abs-input-expression tree))
       ((okf tree) (abnf::check-tree-list-1 sub.6th))
       ((okf &) (abnf::check-tree-ichars tree ";")))
    (make-input-item :name ident :type intype :value inexpr))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-*-input-item ((trees abnf::tree-listp))
  :returns
  (initems
   input-item-list-resultp
   :hints
   (("Goal"
     :in-theory
     (enable
      input-itemp-when-input-item-resultp-and-not-reserrp
      input-item-listp-when-input-item-list-resultp-and-not-reserrp))))
  :short "Abstract a @('*input-item') to a list of input items."
  (b* (((when (endp trees)) nil)
       ((okf initem) (abs-input-item (car trees)))
       ((okf initems) (abs-*-input-item (cdr trees))))
    (cons initem initems))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Temporarily not used.  See abs-public/private/constants/constant/const/main/registers

(define abs-public/private/constants/constant/const ((tree abnf::treep))
  :returns (intitle input-title-resultp)
  :short "Abstract a
          @('( %s\"public\" / %s\"private\" / %s\"constants\" / %s\"constant\" / %s\"const\" )')
          to an input title."
  (b* (((okf tree) (abnf::check-tree-nonleaf-1-1 tree nil))
       ((when (abnf-tree-with-root-p tree "identifier"))
        (if (equal (abnf::tree->string tree)
                   (string=>nats "private"))
            (input-title (var/const-sort-private))
          (reserrf (list :found (abnf::tree-fix tree)))))
       ((unless (abnf::tree-case tree :leafterm))
        (reserrf (list :found (abnf::tree-fix tree))))
       ((when (equal (abnf::tree->string tree)
                     (string=>nats "public")))
        (input-title (var/const-sort-public)))
       ((when (equal (abnf::tree->string tree)
                     (string=>nats "constants")))
        (input-title (var/const-sort-constant)))
       ((when (equal (abnf::tree->string tree)
                     (string=>nats "constant")))
        (input-title (var/const-sort-constant)))
       ((when (equal (abnf::tree->string tree)
                     (string=>nats "const")))
        (input-title (var/const-sort-const))))
    (reserrf (list :found (abnf::tree-fix tree))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; This definition is temporary.  [main] and [registers] are currently
;; the section titles in the .in files, but they should be eliminated soon.
;; For now, main becomes private and registers are discarded.

(define abs-public/private/constants/constant/const/main/registers ((tree abnf::treep))
  :returns (intitle input-title-option-resultp)
  :short "Abstract a
          @('( %s\"public\" / %s\"private\" / %s\"constants\" / %s\"constant\" / %s\"const\" / %s\"main\" / %s\"registers\" )')
          to an input title."
  (b* (((okf tree) (abnf::check-tree-nonleaf-1-1 tree nil))
       ((when (abnf-tree-with-root-p tree "identifier"))
        (cond ((equal (abnf::tree->string tree)
                   (string=>nats "private"))
               (input-title (var/const-sort-private)))
              ((equal (abnf::tree->string tree)
                   (string=>nats "main"))
               (input-title (var/const-sort-private)))
              ((equal (abnf::tree->string tree)
                      (string=>nats "constants"))
               (input-title (var/const-sort-const)))
              ((equal (abnf::tree->string tree)
                   (string=>nats "registers"))
               ;; This is a hack, just to get registers out of the way.
               ;; It doesn't work to make them private
               ;; since then the sections collide.
               ;; It doesn't work to even get the vars under [registers]
               ;; because then the input file vars don't match the main params.
              nil)
              (t
               (reserrf (list :found (abnf::tree-fix tree))))))
       ((unless (abnf::tree-case tree :leafterm))
        (reserrf (list :found (abnf::tree-fix tree))))
       ((when (equal (abnf::tree->string tree)
                     (string=>nats "public")))
        (input-title (var/const-sort-public)))
       ((when (equal (abnf::tree->string tree)
                     (string=>nats "main")))
        (input-title (var/const-sort-public)))
       ((when (equal (abnf::tree->string tree)
                     (string=>nats "registers")))
        (input-title (var/const-sort-public)))
       ((when (equal (abnf::tree->string tree)
                     (string=>nats "constant")))
        (input-title (var/const-sort-constant)))
       ((when (equal (abnf::tree->string tree)
                     (string=>nats "const")))
        (input-title (var/const-sort-const))))
    (reserrf (list :found (abnf::tree-fix tree))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-input-title ((tree abnf::treep))
  :returns (intitle input-title-option-resultp)
  :short "Abstract an @('input-title') to an input title."
  (b* (((okf (abnf::tree-list-tuple3 sub))
        (abnf::check-tree-nonleaf-3 tree "input-title"))
       ((okf tree) (abnf::check-tree-list-1 sub.1st))
       ((okf &) (abnf::check-tree-ichars tree "["))
       ((okf tree) (abnf::check-tree-list-1 sub.2nd))
       ((okf intitle) (abs-public/private/constants/constant/const/main/registers tree))
       ((okf tree) (abnf::check-tree-list-1 sub.3rd))
       ((okf &) (abnf::check-tree-ichars tree "]")))
    intitle)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-input-section ((tree abnf::treep))
  :returns
  (insec
   input-section-option-resultp
   :hints
   (("Goal"
     :in-theory
     (enable
      input-title-optionp-when-input-title-option-resultp-and-not-reserrp))))
  :short "Abstract an @('input-section') to an input section."
  (b* (((okf (abnf::tree-list-tuple2 sub))
        (abnf::check-tree-nonleaf-2 tree "input-section"))
       ((okf tree) (abnf::check-tree-list-1 sub.1st))
       ((okf intitle) (abs-input-title tree))
       ((okf initems) (abs-*-input-item sub.2nd))
       ((unless (mbt (input-title-optionp intitle)))
        (reserrf :cannot-happen))
       ;; If the intitle is null, it means to discard the whole section.
       ((when (null intitle)) nil))
    (make-input-section :title intitle :items initems))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-*-input-section ((trees abnf::tree-listp))
  :returns
  (initems
   input-section-list-resultp
   :hints
   (("Goal"
     :in-theory
     (enable
      input-section-optionp-when-input-section-option-resultp-and-not-reserrp
      input-section-listp-when-input-section-list-resultp-and-not-reserrp))))
  :short "Abstract a @('*input-item') to a list of input items."
  (b* (((when (endp trees)) nil)
       ((okf insec) (abs-input-section (car trees)))
       ((okf insecs) (abs-*-input-section (cdr trees))))
    ;; Allow a null insec to be discarded.
    (if (null insec)
        insecs
      (cons insec insecs)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-input-file ((tree abnf::treep))
  :returns (infile input-file-resultp)
  :short "Abstract an @('input-file') to an input file."
  (b* (((okf trees) (abnf::check-tree-nonleaf-1 tree "input-file"))
       ((okf insecs) (abs-*-input-section trees)))
    (make-input-file :sections insecs))
  :hooks (:fix))
