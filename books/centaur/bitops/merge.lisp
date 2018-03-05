; Centaur Bitops Library
; Copyright (C) 2010-2013 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
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
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "BITOPS")
(include-book "std/util/define" :dir :system)
(include-book "std/basic/arith-equivs" :dir :system)
(include-book "ihs/logops-definitions" :dir :system)
(include-book "tools/templates" :dir :system)
(local (include-book "ihsext-basics"))
(local (include-book "signed-byte-p"))
(local (include-book "equal-by-logbitp"))

(local (defthm ash-of-logior-of-ash
         (implies (natp amt)
                  (equal (ash (logior a b) amt)
                         (logior (ash a amt)
                                 (ash b amt))))
         :hints((acl2::equal-by-logbitp-hammer))))

;; Speed hint
(local (in-theory (disable LOGIOR-<-0-LINEAR-2
                           LOGIOR-<-0-LINEAR-1
                           logior-fold-consts
                           logior-natp-type
                           ash-natp-type
                           )))

(defxdoc bitops/merge
  :parents (bitops)
  :short "Efficient operations for concatenating fixed-sized bit vectors."

  :long "<p>We now introduce many operations that concatenate together bit
vectors of some fixed size to create a new, merged bit vector.  For example,
@(see merge-4-u8s) joins together four 8-bit vectors into a 32-bit result.</p>

<p>In general, the function @(see logapp) is a more flexible alternative to the
operations below&mdash;it can be used to merge bit vectors of different sizes.
However, since it can only merge two bit-vectors at a time, using @('logapp')
directly can become quite tedious when you have a lot of vectors to merge.  For
instance, these merging operations may be especially useful for describing SIMD
style operations, byte swapping operations, and so forth.</p>

<p>Each of our merging operations is logically simple.  However, we go to some
lengths to make them execute more efficiently.  This is accomplished by
providing ample @(see acl2::type-spec) declarations and arranging the order of
operations to use fixnums for as long as possible.  This provides significant
speedups, for instance:</p>

@({
    ;; logic mode version: 11.112 seconds
    ;; exec mode version:   1.404 seconds
    (let ((a7 1)
          (a6 2)
          (a5 3)
          (a4 4)
          (a3 5)
          (a2 6)
          (a1 7)
          (a0 8))
      (time (loop for i fixnum from 1 to 100000000 do
                  (merge-8-u8s a7 a6 a5 a4 a3 a2 a1 a0))))
})

<p>Note that when designing these functions, we typically assume that fixnums
are large enough to hold 56-bit results.  Our definitions should therefore
perform well on 64-bit Lisps including at least CCL and SBCL.</p>

<p>We prove that each merge produces a result of the correct size (expressed as
a theorem about @(see unsigned-byte-p)), and that it has a @(see nat-equiv)
@(see acl2::congruence) for each of its arguments.</p>")

(local (xdoc::set-default-parents bitops/merge))

(defun congruences-for-merge-fn (form n equiv)
  (declare (xargs :mode :program))
  (if (zp n)
      nil
    (cons
     `(defcong ,equiv equal ,form ,n)
     (congruences-for-merge-fn form (- n 1) equiv))))

(defmacro congruences-for-merge (form n &key (equiv 'nat-equiv))
  `(progn . ,(congruences-for-merge-fn form n equiv)))

;; Template tools ----
(define indexed-subst-templates ((name symbolp)
                                 (from integerp)
                                 (by integerp)
                                 (how-many natp)
                                 &key
                                 ((base-subst acl2::tmplsubst-p) '(acl2::make-tmplsubst)))
  
  :mode :program
  (if (zp how-many)
      nil
    (cons (b* (((acl2::tmplsubst base-subst)))
            (acl2::change-tmplsubst
             base-subst
             :atoms (append `((,name . ,from)) base-subst.atoms)
             :strs (append `((,(symbol-name name) . ,(coerce (explode-atom from 10) 'string)))
                           base-subst.strs)))
          (indexed-subst-templates name (+ from by) by (1- how-many) :base-subst base-subst))))
      

(defun logapp*-fn (width args)
  (if (atom args)
      0
    (if (atom (cdr args))
        (car args)
      `(logapp ,width ,(car args)
               ,(logapp*-fn width (cdr args))))))

(defmacro logapp* (width &rest args)
  (logapp*-fn width args))

;; Theory for merges -- want to prove logiors of ash equivalent to logapps.

(local (in-theory (disable acl2::commutativity-of-logior
                           commutativity-2-of-logior)))

(local (defthm logior-of-ash-to-logapp
         (implies (unsigned-byte-p width y)
                  (equal (logior (ash x width) y)
                         (logapp width y x)))
         :hints(("Goal" :in-theory (e/d* (ihsext-inductions
                                          ihsext-recursive-redefs)
                                         (unsigned-byte-p))))))


(local
 (encapsulate nil
   
   (in-theory (enable bitops::logapp-right-assoc))

   (defthm logapp-of-loghead-same
     (equal (logapp w (loghead w x) y)
            (logapp w x y))
     :hints(("Goal" :in-theory (e/d* (ihsext-inductions
                                      ihsext-recursive-redefs)))))))




(define merge-unsigneds-aux ((width natp)
                             (elts integer-listp)
                             (acc natp))
  ;; BOZO Optimize this for execution efficiency somehow?
  :returns (packed natp :rule-classes :type-prescription)
  (if (atom elts)
      (lnfix acc)
    (merge-unsigneds-aux
     width (cdr elts)
     (logapp width (car elts) (lnfix acc))))
  ///
  (local (in-theory (disable unsigned-byte-p)))
  (local (defthm unsigned-byte-p-of-integer-length
           (implies (natp x)
                    (unsigned-byte-p (integer-length x) x))
           :hints(("Goal" :in-theory (enable* ihsext-inductions
                                              ihsext-recursive-redefs)))))
  (local (defthm integer-length-of-logapp
           (implies (natp b)
                    (equal (integer-length (logapp width a b))
                           (if (posp b)
                               (+ (nfix width) (integer-length b))
                             (integer-length (loghead width a)))))
           :hints(("Goal" :in-theory (enable* ihsext-inductions
                                              ihsext-recursive-redefs)))))
                  
  (defret width-of-merge-unsigneds-aux
    (unsigned-byte-p (+ (integer-length (nfix acc))
                        (* (nfix width) (len elts)))
                     packed))

  (defthm merge-unsigneds-aux-of-nil
    (equal (merge-unsigneds-aux width nil acc) (nfix acc)))

  (defthmd merge-unsigneds-aux-of-cons
    (equal (merge-unsigneds-aux width (cons a b) acc)
           (merge-unsigneds-aux width b (logapp width a (nfix acc))))))

(define merge-unsigneds ((width natp)
                         (elts integer-listp))
  :returns (packed natp :rule-classes :type-prescription)
  :short "Concatenate the given list of integers together at the given width, most-significant
          first, to form a single natural number."
  (merge-unsigneds-aux width elts 0)
  ///
  (local (in-theory (disable unsigned-byte-p)))

  (defret width-of-merge-unsigneds
    (implies (and (<= (* (nfix width) (len elts)) n)
                  (natp n))
             (unsigned-byte-p n packed))
    :hints(("Goal" :in-theory (disable width-of-merge-unsigneds-aux)
            :use (:instance width-of-merge-unsigneds-aux
                  (acc 0)))))

  (local (defun merge-unsigneds-aux-elim-ind (width lst acc)
           (if (atom lst)
               (list width acc)
             (list (merge-unsigneds-aux-elim-ind width (cdr lst) (logapp width (car lst) (nfix acc)))
                   (merge-unsigneds-aux-elim-ind width (cdr lst) (loghead width (car lst)))))))

  (local (defthm logapp-of-equal-logapp-right-assoc
           (implies (and (equal x (logapp w2 a b))
                         (natp w1) (natp w2))
                    (EQUAL (LOGAPP W1 x C)
                           (LOGAPP (MIN W1 W2)
                                   A
                                   (IF (<= W1 W2)
                                       C (LOGAPP (- W1 W2) B C)))))))

  (local (defthmd merge-unsigneds-aux-elim
           (equal (merge-unsigneds-aux width lst acc)
                  (logapp (* (nfix width) (len lst))
                          (merge-unsigneds width lst)
                          (nfix acc)))
           :hints(("Goal" 
                   :induct (merge-unsigneds-aux-elim-ind width lst acc)
                   :expand ((:free (acc) (merge-unsigneds-aux width lst acc)))))))

  (defthmd merge-unsigneds-alt-def
    (equal (merge-unsigneds width elts)
           (if (atom elts)
               0
             (logapp (* (nfix width) (len (cdr elts)))
                     (merge-unsigneds width (cdr elts))
                     (loghead width (car elts)))))
    :hints (("goal" :expand ((merge-unsigneds-aux width elts 0)
                             (merge-unsigneds width elts))
             :in-theory (disable merge-unsigneds))
            (and stable-under-simplificationp
                 '(:in-theory (e/d (merge-unsigneds-aux-elim)
                                   (merge-unsigneds)))))
    :rule-classes ((:definition :controller-alist ((merge-unsigneds nil t))))))

;; Merging Bits ---------------------------------------------------------------

(def-ruleset merges-are-merge-unsigneds nil)
(def-ruleset merge-definitions '(merge-unsigneds-aux-of-cons
                                 merge-unsigneds-aux-of-nil
                                 merge-unsigneds))

(defun def-merge-n-bits-fn (n)
  (declare (xargs :mode :program))
  (b* ((ns (coerce (explode-atom n 10) 'string))
       (n-1s (coerce (explode-atom (1- n) 10) 'string))
       ;; bozo I was trying to use fmt1-to-string with ~n0 to produce
       ;; e.g. "eight" for 8 but ran into weird safe-mode problems
       (str-alist `(("<N>" . ,ns)
                    ("<N-1>" . ,n-1s)
                    ("<NSTR>" . ,ns)))
       ((mv shortstr &) (acl2::tmpl-str-sublis
                         str-alist "Concatenate <NSTR> bits together to form an <N>-bit natural.")))
    (acl2::template-subst
     '(define merge-<n>-bits ((:@proj countdown (a<i> bitp)))
        (declare (type bit (:@proj countdown a<i>)))
        :returns (result natp :rule-classes :type-prescription)
        :short <shortstr>
        :split-types t
        :inline t
        (mbe :logic (logapp* 1 (:@proj countup (bfix a<i>)) 0)
             :exec
             (b* ((ans a0)
                  (:@proj countup1-1 ;; missing both 0 and last
                   (ans (the (unsigned-byte <n>)
                              (logior (the (unsigned-byte <n>) (ash a<i> <i>))
                                      (the (unsigned-byte <n>) ans))))))
               (the (unsigned-byte <n>)
                    (logior (the (unsigned-byte <n>) (ash a<n-1> <n-1>))
                            (the (unsigned-byte <n>) ans)))))
        ///
        (acl2::add-to-ruleset merge-definitions '((:d merge-<n>-bits)))

        (defthm unsigned-byte-p-<n>-of-merge-<n>-bits
          (unsigned-byte-p <n> (merge-<n>-bits (:@proj countdown a<i>))))

        (defthmd merge-<n>-bits-is-merge-unsigneds
          (equal (merge-<n>-bits (:@proj countdown a<i>))
                 (merge-unsigneds 1 (list (:@proj countdown (bfix a<i>)))))
          :hints(("Goal" :in-theory (enable merge-unsigneds
                                            merge-unsigneds-aux-of-cons))))

        (acl2::add-to-ruleset merges-are-merge-unsigneds merge-<n>-bits-is-merge-unsigneds)

        "<h5>Basic @(see bit-equiv) congruences.</h5>"
        (congruences-for-merge (merge-<n>-bits (:@proj countdown a<i>)) <n>
                               :equiv bit-equiv))
     :atom-alist `((<n> . ,n)
                   (<n-1> . ,(1- n))
                   (<shortstr> . ,shortstr))
     :str-alist str-alist
     :subsubsts `((countdown . ,(indexed-subst-templates '<i> (1- n) -1 n))
                  (countdown1 . ,(indexed-subst-templates '<i> (1- n) -1 (1- n)))
                  (countup1 . ,(indexed-subst-templates '<i> 1 1 (1- n)))
                  (countup1-1 . ,(indexed-subst-templates '<i> 1 1 (- n 2)))
                  (countup . ,(indexed-subst-templates '<i> 0 1 n)))
     :pkg-sym nil)))

(defmacro def-merge-n-bits (n)
  (def-merge-n-bits-fn n))


(def-merge-n-bits 2)
(def-merge-n-bits 4)
(def-merge-n-bits 8)
(def-merge-n-bits 16)





;; Merging U2s ----------------------------------------------------------------

(defun def-merge-n-unsigneds-fn (n width)
  (declare (xargs :mode :program))
  (b* ((ns (coerce (explode-atom n 10) 'string))
       (n-1s (coerce (explode-atom (1- n) 10) 'string))
       (widthstr (coerce (explode-atom width 10) 'string))
       (prod (* n width))
       (prodstr (coerce (explode-atom prod 10) 'string))
       (numtypes (case width
                   (4 "nibbles")
                   (8 "bytes")
                   (otherwise (b* (((mv str &) (acl2::tmpl-str-sublis
                                                `(("<WIDTH>" . ,widthstr))
                                                "<WIDTH>-bit numbers")))
                                str))))
       ;; bozo I was trying to use fmt1-to-string with ~n0 to produce
       ;; e.g. "eight" for 8 but ran into weird safe-mode problems       
       (str-alist `(("<N>" . ,ns)
                    ("<N-1>" . ,n-1s)
                    ("<N/2>" . ,(coerce (explode-atom (/ n 2) 10) 'string))
                    ("<NSTR>" . ,ns)
                    ("<WIDTH>" . ,widthstr)
                    ("<PROD>" . ,prodstr)
                    ("<PROD/2>" . ,(coerce (explode-atom (/ prod 2) 10) 'string))
                    ("<NUMTYPES>" . ,numtypes)))
       ((mv shortstr &) (acl2::tmpl-str-sublis
                         str-alist "Concatenate <NSTR> <NUMTYPES> together to form an <PROD>-bit result.")))
    (acl2::template-subst
     '(define merge-<n>-u<width>s ((:@proj countdown a<i>))
        (declare (type (unsigned-byte <width>) (:@proj countdown a<i>)))
        :returns (result natp :rule-classes :type-prescription)
        :short <shortstr>
        (:@ :inline :inline t)
        (:@ (not :linear)
         :guard-hints (("goal" :in-theory (enable merge-2-u<prod/2>s
                                                  merge-<n/2>-u<width>s))))
        (mbe :logic (logapp* <width> (:@proj countup (nfix a<i>)) 0)
             :exec
             (:@ :linear
              (b* ((ans a0)
                   (:@proj countup1-1 ;; missing both 0 and last
                    (ans (the (unsigned-byte <prod>)
                              (logior (the (unsigned-byte <prod>) (ash a<i> (* <i> <width>)))
                                      (the (unsigned-byte <prod>) ans))))))
                (the (unsigned-byte <prod>)
                     (logior (the (unsigned-byte <prod>) (ash a<n-1> (* <n-1> <width>)))
                             (the (unsigned-byte <prod>) ans)))))
             (:@ (not :linear)
              (merge-2-u<prod/2>s
               (the (unsigned-byte <prod/2>)
                    (merge-<n/2>-u<width>s
                     (:@proj countdown-half2 a<i>)))
               (the (unsigned-byte <prod/2>)
                    (merge-<n/2>-u<width>s
                     (:@proj countdown-half1 a<i>))))))
        ///
        (acl2::add-to-ruleset merge-definitions '((:d merge-<n>-u<width>s)))

        (defthm unsigned-byte-p-<prod>-of-merge-<n>-u<width>s
          (unsigned-byte-p <prod> (merge-<n>-u<width>s (:@proj countdown a<i>))))

        (defthmd merge-<n>-u<width>s-is-merge-unsigneds
          (equal (merge-<n>-u<width>s (:@proj countdown a<i>))
                 (merge-unsigneds <width> (list (:@proj countdown (nfix a<i>)))))
          :hints(("Goal" :in-theory (enable merge-unsigneds
                                            merge-unsigneds-aux-of-cons))))

        (acl2::add-to-ruleset merges-are-merge-unsigneds merge-<n>-u<width>s-is-merge-unsigneds)

        "<h5>Basic @(see nat-equiv) congruences.</h5>"
        (congruences-for-merge (merge-<n>-u<width>s (:@proj countdown a<i>)) <n>))
     :atom-alist `((<n> . ,n)
                   (<n-1> . ,(1- n))
                   (<n/2> . ,(/ n 2))
                   (<width> . ,width)
                   (<prod> . ,prod)
                   (<prod/2> . ,(/ prod 2))
                   (<shortstr> . ,shortstr))
     :str-alist str-alist
     :subsubsts `((countdown . ,(indexed-subst-templates '<i> (1- n) -1 n))
                  (countdown1 . ,(indexed-subst-templates '<i> (1- n) -1 (1- n)))
                  (countdown-half1 . ,(indexed-subst-templates '<i> (1- (/ n 2)) -1 (/ n 2)))
                  (countdown-half2 . ,(indexed-subst-templates '<i> (1- n) -1 (/ n 2)))
                  (countup1 . ,(indexed-subst-templates '<i> 1 1 (1- n)))
                  (countup1-1 . ,(indexed-subst-templates '<i> 1 1 (- n 2)))
                  (countup . ,(indexed-subst-templates '<i> 0 1 n)))
     :features (append (and (<= prod 60) '(:inline))
                       (and (or (and (<= prod 64)
                                     (<= n 4))
                                (<= n 2))
                            '(:linear)))
     :pkg-sym nil)))

(defmacro def-merge-n-unsigneds (n width)
  (def-merge-n-unsigneds-fn n width))

(def-merge-n-unsigneds 2 2)
(def-merge-n-unsigneds 2 4)
(def-merge-n-unsigneds 2 8)
(def-merge-n-unsigneds 2 16)
(def-merge-n-unsigneds 2 32)
(def-merge-n-unsigneds 2 64)
(def-merge-n-unsigneds 2 128)
(def-merge-n-unsigneds 2 256)

(def-merge-n-unsigneds 4 2)
(def-merge-n-unsigneds 4 4)
(def-merge-n-unsigneds 4 8)
(def-merge-n-unsigneds 4 16)
(def-merge-n-unsigneds 4 32)
(def-merge-n-unsigneds 4 64)
(def-merge-n-unsigneds 4 128)

(def-merge-n-unsigneds 8 2)
(def-merge-n-unsigneds 8 4)
(def-merge-n-unsigneds 8 8)
(def-merge-n-unsigneds 8 16)
(def-merge-n-unsigneds 8 32)
(def-merge-n-unsigneds 8 64)

(def-merge-n-unsigneds 16 8)
(def-merge-n-unsigneds 16 16)
(def-merge-n-unsigneds 16 32)

(def-merge-n-unsigneds 32 8)
(def-merge-n-unsigneds 32 16)

(def-merge-n-unsigneds 64 8)
