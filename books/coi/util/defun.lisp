; Computational Object Inference
; Copyright (C) 2005-2014 Kookamara LLC
;
; Contact:
;
;   Kookamara LLC
;   11410 Windermere Meadows
;   Austin, TX 78759, USA
;   http://www.kookamara.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.

(in-package "DEFUN")

(include-book "recursion-support")
(include-book "pseudo-translate")
(include-book "mv-nth")
(include-book "centaur/fty/deftypes" :dir :system)

(local
 (defthm true-listp-append-rewrite
   (implies
    (true-listp y)
    (true-listp (append x y)))))

(defun local-suffix (name string)
  (declare (type symbol name)
           (type string string))
  (intern-in-package-of-symbol (concatenate 'string (symbol-name name) string) name))

(defthm symbolp-suffix
  (implies
   (and
    (stringp string)
    (symbolp symbol))
   (symbolp (local-suffix symbol string))))

(in-theory (disable local-suffix))

(defun contains-nil-alistp (alist)
  (declare (type (satisfies alistp) alist))
  (if (consp alist)
      (or (null (cdar alist))
          (contains-nil-alistp (cdr alist)))
    nil))

(defun contains-nil (list)
  (declare (type t list))
  (if (consp list)
      (or (null (car list))
          (contains-nil (cdr list)))
    nil))

(in-theory (disable function-declaration-p))
(in-theory (disable decompose-defun-body))

;; The :fty keyword can replace the :signature keyword.  In an :fty signature
;; fty type names are provided insead of type predicates.  An fty signature
;; will a) add type guards b) add fixing functions and c) generate conruence
;; relations.
;;
(defun fty::get-key (key entry)
  (declare (xargs :guard (and (consp entry) (alistp (cdr entry)))))
  (let ((alist (cdr entry)))
    (let ((hit (assoc-equal key alist)))
      (if (not (consp hit)) (coi-debug::fail :message "FTY entry for ~x0 missing key ~x1~%" :parameters ((car entry) key))
        (cdr hit)))))

(in-theory (disable fty::get-key))

(defun fty::get-entry (type alist)
  (declare (type (satisfies alistp) alist))
  (let ((hit (assoc-equal type alist)))
    (if (not (consp hit))
        (cons nil (coi-debug::fail :message "Unrecognized :fty type name: ~x0~%"
                                   :parameters (type)))
      (if (not (alistp (cdr hit)))
          (cons nil (coi-debug::fail :message "Non-alist :fty entry~%"))
        hit))))

(defthm alistp-get-entry
  (and (consp (fty::get-entry type alist))
       (alistp (cdr (fty::get-entry type alist)))))

(in-theory (disable fty::get-entry))

(defun make-all-true (list)
  (declare (type t list))
  (if (not (consp list)) nil
    (cons t (make-all-true (cdr list)))))

(defthm true-listp-make-all-true
  (true-listp (make-all-true x)))

(defthm iff-true-listp-append
  (iff (true-listp (append x y))
       (true-listp y)))

(defun fty-arg-specs (fty-args fty-alist)
  (declare (type (satisfies alistp) fty-alist))
  (if (not (consp fty-args)) (mv nil nil nil)
    (let ((entry (fty::get-entry (car fty-args) fty-alist)))
      (met ((arg-types arg-congs arg-fixes) (fty-arg-specs (cdr fty-args) fty-alist))
        (let ((typep (fty::get-key 'fty::pred  entry))
              (equiv (fty::get-key 'fty::equiv entry))
              (fixer (fty::get-key 'fty::fix   entry)))
          (mv (cons typep arg-types)
              (cons equiv arg-congs)
              (cons fixer arg-fixes)))))))

(defthm true-listp-fty-arg-specs
  (and (true-listp (val 0 (fty-arg-specs fty-args fty-alist)))
       (true-listp (val 1 (fty-arg-specs fty-args fty-alist)))
       (true-listp (val 2 (fty-arg-specs fty-args fty-alist)))))

(defun fty-val-specs (val-specs fty-alist)
  (declare (type (satisfies alistp) fty-alist))
  (if (not (consp val-specs)) (mv nil nil)
    (met ((val-types val-congs) (fty-val-specs (cdr val-specs) fty-alist))
      (let ((entry (fty::get-entry (car val-specs) fty-alist)))
        (let ((typep (fty::get-key 'fty::pred  entry)))
          (mv (cons typep  val-types)
              (cons 'equal val-congs)))))))

(defthm true-listp-fty-val-specs
  (true-listp (val 0 (fty-val-specs x y))))

(defthm consp-fty-val-specs
  (iff (consp (val 0 (fty-val-specs x y)))
       (consp x)))

(defun use-fty-specs (name cong-specs fty-sig signature fty-alist)
  (declare (type (satisfies alistp) fty-alist)
           (xargs :guard (and (or (null signature) (function-declaration-p signature))
                              (or (null fty-sig) (function-declaration-p fty-sig)))))
  (if (not fty-sig) (mv cong-specs signature signature nil)
    (if signature
        (let ((zed (coi-debug::fail :message "The :fty and :signature keywords are mutually exclusive")))
          (declare (ignore zed))
          (mv cong-specs signature signature nil))
      (let ((fty-args (function-declaration-args fty-sig))
            (fty-vals (function-declaration-vals fty-sig)))
        (met ((arg-types arg-congs arg-fixes) (fty-arg-specs fty-args fty-alist))
          (met ((val-types val-congs) (fty-val-specs fty-vals fty-alist))
            (let ((cong-specs (cons (cons arg-congs val-congs) cong-specs)))
              (mv cong-specs
                  (function-declaration name (make-all-true arg-types) val-types)
                  (function-declaration name arg-types val-types)
                  arg-fixes))))))))

(in-theory (disable function-declaration-args
                    function-declaration-vals))

(defthm use-fty-specs-signature
  (implies
   (and
    (implies
     signature
     (FUNCTION-DECLARATION-P SIGNATURE))
    (implies
     fty-sig
     (FUNCTION-DECLARATION-P fty-sig)))
   (and
    (implies
     (val 1 (use-fty-specs name cong-specs fty-sig signature fty-alist))
     (function-declaration-p (val 1 (use-fty-specs name cong-specs fty-sig signature fty-alist))))
    (implies
     (val 2 (use-fty-specs name cong-specs fty-sig signature fty-alist))
     (function-declaration-p (val 2 (use-fty-specs name cong-specs fty-sig signature fty-alist)))))))

(in-theory (disable use-fty-specs))

(defun fix-inputs (args fty-fixes)
  (declare (type t args fty-fixes))
  (if (not (and (consp args) (consp fty-fixes))) nil
    (let ((arg (car args))
          (fix (car fty-fixes)))
      (if fix (cons `(,arg (,fix ,arg))
                    (fix-inputs (cdr args) (cdr fty-fixes)))
        (fix-inputs (cdr args) (cdr fty-fixes))))))

(defun defun-fn (disable name args body induction-defun fty-alist)
  (declare (type symbol name)
           (type (satisfies symbol-listp) args)
           (type (satisfies wf-defun-body) body)
           (type (satisfies alistp) fty-alist)
           (type (satisfies true-listp) induction-defun)
           (type t args body)
           (xargs :guard-hints (("Goal" :do-not-induct t))))
  (met ((doc decls body) (decompose-defun-body body))
    (met ((typespec signature fty-sig sig-hints decls) (extract-function-declaration decls))
      (let ((induction-defun (and (not fty-sig) induction-defun)))
        (met ((cong-hints decls) (extract-xarg-key-from-decls :congruence-hints decls))
          (met ((cong-specs decls) (extract-xarg-key-from-decls :congruence decls))
            (if (not (or (null signature) (function-declaration-p signature)))
                (coi-debug::fail :message "malformed :signature")
              (if (not (or (null fty-sig) (function-declaration-p fty-sig)))
                  (coi-debug::fail :message "malformed :fty signature")
                (met ((cong-specs thm-signature guard-signature fty-fixes) (use-fty-specs name cong-specs fty-sig signature fty-alist))
                  (let ((body `(let (,@(fix-inputs args fty-fixes)) ,body)))
                    (cond
                     ((not (wf-congruence-hint-listp cong-hints))
                      (coi-debug::fail :message "malformed :congruence-hints"))
                     ((not (wf-congruence-spec-listp cong-specs))
                      (coi-debug::fail :message "malformed :congruence specification"))
                     ((and signature (not (equal (len args) (len (function-declaration-args signature)))))
                      (coi-debug::fail :message "incorrect :signature specification length"))
                     (t
                      (let* ((verify-guards   (get-xarg-keys-from-decls :verify-guards decls))
                             (xarg-guards     (get-xarg-keys-from-decls :guard decls))
                             (xarg-mode       (get-xarg-keys-from-decls :mode  decls))
                             (guard-hints     (get-xarg-keys-from-decls :guard-hints decls))
                             (type-decls      (get-type-declarations-from-decls decls))
                             (not-inhibited   (not (contains-nil verify-guards)))
                             (verify-guards   (and not-inhibited (or thm-signature verify-guards xarg-guards type-decls)))
                             (decls           (if guard-signature
                                                  (cons `(declare
                                                          (xargs :guard
                                                                 ,(function-declaration-to-guard args guard-signature))) decls)
                                                decls))
                             (typespec        (or typespec thm-signature))
                             (inhibited-decls (cons `(declare (xargs :verify-guards nil)) decls))
                             (name-induction  (symbol-fns::suffix name '-induction)))

                        `(progn

                           (defun ,name ,args
                             ,@(and doc (list doc))
                             ,@(if (or verify-guards (member-equal :program xarg-mode)) inhibited-decls decls)
                             ,body)

                           ,@(and (member-equal :program xarg-mode)
                                  `((skip-proofs (verify-termination ,name))))

                           ,@(and typespec
                                  (function-declaration-to-type-thm name args typespec sig-hints))

                           ,@(and verify-guards `((verify-guards ,name
                                                                 ,@(and guard-hints `(:hints ,@guard-hints)))))

                           ,@(and induction-defun cong-specs
                                  `((encapsulate
                                        ()
                                      (set-ignore-ok :warn)
                                      (set-irrelevant-formals-ok :warn)

                                      ,@induction-defun

                                      ,(congruence-induction-reduction-proof name-induction name args)

                                      )))

                           ;; And here we can add congruence proofs ..
                           ,@(process-congruence-arguments name args cong-hints cong-specs induction-defun)

                           ,@(and disable `((in-theory (disable ,name ,@(and (null args) `((,name)))))))

                           ))))))))))))))

(set-state-ok t)

(defun defun-fn-wrapper (disable name args body state)
  (declare (xargs :mode :program))
  (met ((doc decls xbody) (decompose-defun-body body))
    (let ((wrld (w state)))
      (let ((fty-alist (fty::get-fixtypes-alist wrld)))
        (met ((err tbody) (acl2::pseudo-translate xbody (list (cons name args)) wrld))
          (met ((case base) (lift-base (list name) tbody args))
            (declare (ignore base))
            (let ((event (if (not (equal case acl2::*nil*))
                             (let ((induction-defun (make-defun 'defun name args (make-defun-body doc decls tbody))))
                               (let ((induction-defun `(,(congruence-induction-function induction-defun))))
                                 (defun-fn disable name args body induction-defun fty-alist)))
                           (defun-fn disable name args body nil fty-alist))))
              (mv err event state))))))))

(defmacro def::un (name args &rest body)
  `(make-event (defun-fn-wrapper nil ',name ',args ',body state)))

(defmacro def::und (name args &rest body)
  `(make-event (defun-fn-wrapper t ',name ',args ',body state)))

(defun signature-fn (fn argspec vals hints)
  (let ((args (symbol-fns::item-to-numbered-symbol-list 'acl2::x (len argspec))))
    (function-declaration-to-type-thm fn args `(function ,fn ,argspec ,@vals) hints)))

(defun extract-hints (args)
  (if (consp args)
      (let ((arg (car args)))
        (if (equal arg :hints) (mv (cadr args) nil)
          (met ((hints args) (extract-hints (cdr args)))
            (mv hints (cons arg args)))))
    (mv nil nil)))

(defmacro def::signature (fname args &rest vals)
  (met ((hints vals) (extract-hints vals))
    `(acl2::progn ,@(signature-fn fname args vals hints))))

(defmacro def::signatured (name &rest args)
  `(progn
     (def::signature ,name ,@args)
     (in-theory (disable ,name))
     ))

(defmacro def::congruence (fname argspec &rest vals)
  (let ((args (symbol-fns::item-to-numbered-symbol-list 'acl2::x (len argspec))))
    (met ((hints vals) (defun::extract-hints vals))
      (let ((spec (cons argspec vals)))
        (let ((pairs (defun::pair-hints-with-patterns-and-split hints (list spec))))
          `(acl2::progn ,@(defun::make-congruence-theorems 0 fname nil args pairs)))))))

(local
 (encapsulate
     ()

   (local
    (encapsulate
        ()

      (def::un zed (a b)
        (declare (type integer a)
                 (type string b)

                 ;; The following assertion is really at the heart of
                 ;; what we are doing (for now) with def::un.
                 ;; Assertions such as this provide a short-hand
                 ;; notation allowing us to auto-generate type
                 ;; theorems about functions.

                 (function zed (integer string) integer string))
        (mv (+ a 1) b))

      ))

   ))

(local
 (encapsulate
     ()

   (local
    (encapsulate
        ()

      (defund fred (x)
        (declare (type t x))
        (integerp x))

      (def::un zed (a b)
        (declare (xargs :signature ((fred string) fred string)
                        :signature-hints (("Goal" :in-theory (enable fred)))
                        :guard-hints (("Goal" :in-theory (enable fred)))))
        (mv (+ a 1) b))

      ))

   ))

(local
 (encapsulate
     ()

   (local
    (encapsulate
        ()

      (defun equiv1 (x y) (equal x y))
      (defun equiv2 (x y) (equal x y))

      (defequiv equiv1)
      (defequiv equiv2)

      (def::un foo (x)
        (declare (xargs :measure (len x)
                        :congruence ((equiv1) equiv2)
                        :congruence ((equiv2) equiv1)
                        :congruence-hints (("Goal" :in-theory (current-theory :here)))))
        (if (consp x) (foo (cdr x)) (endp x)))



      ))
   (local
    (encapsulate
        ()

      (defun nfixequiv (x y) (equal (nfix x) (nfix y)))
      (defun ifixequiv (x y) (equal (ifix x) (ifix y)))

      (defequiv nfixequiv)
      (defequiv ifixequiv)

      ;; Multiple return values ..

      (def::un goo (x y)
        (declare (xargs :congruence ((ifixequiv nfixequiv) ifixequiv nfixequiv)))
        (mv x (nfix y)))

      ;; The def::congruence macro allows congruence relations to be
      ;; specified after function admission.

      (def::congruence goo (ifixequiv nfixequiv) ifixequiv nfixequiv)

      ;; Note that any field in the congruence spec (in either
      ;; def::congruence or def::un) can be 'nil' which indicates that
      ;; no congruence should be asserted for that location
      (def::congruence goo (nil nfixequiv) ifixequiv nil)

      ;; The def::signature macro allows type signatures to be
      ;; specified after function admission.  This is particularly
      ;; useful when you want weak guards but strong type theorems.
      ;; For signatures, use 't' to indicate that the associated value
      ;; has no type restriction.
      (def::signature goo (integerp t) t natp)

      ))
   ))
