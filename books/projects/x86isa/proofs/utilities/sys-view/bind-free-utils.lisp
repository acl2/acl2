;; Shilpi Goel <shilpi@centtech.com>

(in-package "X86ISA")
(include-book "clause-processors/find-subterms" :dir :system)
(include-book "clause-processors/find-matching" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/lists/list-fix" :dir :system)

;; ----------------------------------------------------------------------

;; Some misc. utils for bind-free and syntaxp:

(defun l-addrs-candidates (n-var addr-var calls)
  (if (endp calls)
      nil
    (cons
     (list
      (cons n-var    (nth 1 (car calls)))
      (cons addr-var (nth 2 (car calls))))
     (l-addrs-candidates n-var addr-var (cdr calls)))))

(defun find-l-addrs-from-fn (fn n-var addr-var mfc state)
  (declare (xargs :stobjs (state) :mode :program)
           (ignorable state))
  (b* ((calls (acl2::find-calls-lst fn (acl2::mfc-clause mfc)))
       ((when (not calls))
        ;; fn term not encountered.
        nil))
    (l-addrs-candidates n-var addr-var calls)))

(defun find-program-at-info (addr-var bytes-var mfc state)
  (declare (xargs :stobjs (state) :mode :program)
           (ignorable state))
  (b* ((call (acl2::find-call-lst 'program-at-alt (acl2::mfc-clause mfc)))
       (call (or call (acl2::find-call-lst 'program-at (acl2::mfc-clause mfc))))
       ((when (not call))
        ;; No program-at-alt or program-at terms encountered.
        nil))
    `((,addr-var . ,(nth 1 call))
      (,bytes-var . ,(nth 2 call)))))

(define find-l-addrs-from-las-to-pas-candidates (n-var addr-var calls)
  (if (atom calls)
      nil
    (b* ((one-call (car calls))
         ((unless (and (true-listp one-call) (< 3 (len one-call)))) nil))
      (cons (list (cons n-var    (nth 1 one-call))
                  (cons addr-var (nth 2 one-call)))
            (find-l-addrs-from-las-to-pas-candidates n-var addr-var (cdr calls))))))

(defun find-l-addrs-from-las-to-pas (vars r-w-x mfc state)
  (declare (xargs :stobjs (state) :mode :program)
           (ignorable state))
  ;; Narrows the matches by looking at only those calls of las-to-pas
  ;; which have "r-w-x" in the permission field.
  (b* (((list n-var addr-var) vars)
       (calls (acl2::find-matches-list
               `(las-to-pas n addr ,r-w-x x86)
               (acl2::mfc-clause mfc) nil))
       ((when (not calls))
        ;; las-to-pas term not encountered.
        nil))
    (find-l-addrs-from-las-to-pas-candidates n-var addr-var calls)))

(defun find-almost-matching-ia32e-la-to-pas-candidates (r-w-x-var calls)
  (if (endp calls)
      nil
    (cons (list (cons r-w-x-var (nth 2 (car calls)))) ;; r-w-x
          (find-almost-matching-ia32e-la-to-pas-candidates r-w-x-var (cdr calls)))))

(defun find-almost-matching-ia32e-la-to-pas (free-r-w-x-var lin-addr mfc state)
  (declare (xargs :stobjs (state) :mode :program)
           (ignorable state))
  (b* ((calls
        (acl2::find-matches-list
         `(ia32e-la-to-pa ,lin-addr r-w-x x86)
         (acl2::mfc-clause mfc) nil))
       ((when (not calls))
        ;; ia32e-la-to-pa term for lin-addr not encountered.
        nil))
    (find-almost-matching-ia32e-la-to-pas-candidates free-r-w-x-var calls)))

(defun find-almost-matching-las-to-pas-candidates (r-w-x-var calls)
  (if (endp calls)
      nil
    (cons (list (cons r-w-x-var (nth 3 (car calls)))) ;; r-w-x
          (find-almost-matching-las-to-pas-candidates r-w-x-var (cdr calls)))))

(defun find-almost-matching-las-to-pas (free-r-w-x-var n lin-addr mfc state)
  (declare (xargs :stobjs (state) :mode :program)
           (ignorable state))
  (b* ((calls
        (acl2::find-matches-list
         `(las-to-pas ,n ,lin-addr r-w-x x86)
         (acl2::mfc-clause mfc) nil))
       ((when (not calls))
        ;; las-to-pas term for lin-addr not encountered.
        nil))
    (find-almost-matching-las-to-pas-candidates free-r-w-x-var calls)))

;; ----------------------------------------------------------------------

(defun get-subterm-from-list-of-terms (n x)
  (declare (xargs :guard (and (natp n) (pseudo-term-listp x))))
  ;; E.g.:
  ;; (get-subterm-from-list-of-terms 1 '((las-to-pas l-addrs-1 r-w-x cpl x86)
  ;;                                     (las-to-pas l-addrs-2 r-w-x cpl x86)
  ;;                                     (las-to-pas l-addrs-2 r-w-x cpl x86)
  ;;                                     (foo x)))
  (if (atom x)
      nil
    (cons (nth n (acl2::list-fix (car x)))
          (get-subterm-from-list-of-terms n (cdr x)))))

(define make-bind-free-alist-lists (var values)
  (if (atom values)
      nil
    (cons (acons var (car values) nil)
          (make-bind-free-alist-lists var (cdr values)))))

(defun find-arg-of-fn (fn arg-number free-var mfc state)
  (declare (xargs :stobjs (state) :mode :program)
           (ignorable state))
  (b* ((calls (acl2::find-calls-lst fn (acl2::mfc-clause mfc)))
       ((when (not calls)) nil)
       (bind-candidates (get-subterm-from-list-of-terms arg-number calls))
       (alst-lst
        (make-bind-free-alist-lists free-var bind-candidates)))
    alst-lst))

;; ----------------------------------------------------------------------
