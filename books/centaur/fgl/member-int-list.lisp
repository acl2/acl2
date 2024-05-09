; FGL - A Symbolic Simulation Framework for ACL2
; Copyright (C) 2018 Centaur Technology
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
; Original author: Sol Swords <sswords@centtech.com>

(in-package "FGL")

(include-book "member-equal")
(include-book "fgl-object")
(include-book "std/typed-lists/unsigned-byte-listp" :dir :system)
(include-book "std/typed-lists/signed-byte-listp" :dir :system)
(include-book "centaur/aig/aig-base" :dir :system)

(local (include-book "centaur/bitops/ihsext-basics" :dir :System))

(local (in-theory (disable signed-byte-p
                           unsigned-byte-p)))

;; This book gives a method of compiling a membership check of a symbolic
;; integer in a list of concrete integers.  To do this, we derive an AIG from
;; the list of concrete integers.  Then, the (symbolic) integer is a member of
;; the list if it is in the size bounds and the evaluation of the AIG with
;; variables 0, 1, ... N bound to bit values 0, 1, ... N of the symbolic
;; integer returns T.

;; Produces an AIG env binding variables 0...N-1 to bits 0...N-1 of the input integer.
(define integer-to-aig-env-aux ((i natp) (n natp) (input integerp) (acc))
  :measure (nfix (- (nfix n) (nfix i)))
  :guard (<= i n)
  (let ((i (lnfix i)))
    (if (mbe :logic (zp (- (nfix n) i))
             :exec (eql n i))
        acc
      (integer-to-aig-env-aux (1+ i) n (logcdr input)
                              (hons-acons i (intcar input) acc)))))
                            

(define integer-to-aig-env ((n natp) (input integerp))
  :returns (env)
  :verify-guards nil
  (mbe :logic (b* (((when (zp n)) nil)
                   (n (1- n)))
                (cons (cons n (logbitp n input))
                      (integer-to-aig-env n input)))
       :exec (integer-to-aig-env-aux 0 n input nil))
  ///
  (local (defun integer-to-aig-env-intermed-1 (i n input acc)
           (declare (xargs :measure (nfix (- (nfix n) (nfix i)))))
           (if (zp (- (nfix n) (nfix i)))
               acc
             (integer-to-aig-env-intermed-1 (1+ (nfix i))
                                            n input (cons (cons (nfix i) (logbitp i input)) acc)))))

  (local (defthm integer-to-aig-env-aux-is-intermed-1
           (equal (integer-to-aig-env-aux i n (logtail i input) acc)
                  (integer-to-aig-env-intermed-1 i n input acc))
           :hints(("Goal" 
                   :induct (integer-to-aig-env-intermed-1 i n input acc)
                   :in-theory (enable bool->bit)
                   :expand ((integer-to-aig-env-aux i n (logtail i input) acc)
                            (integer-to-aig-env-intermed-1 i n input acc))))))
  
  (local (defun integer-to-aig-env-intermed-2 (i n input)
           (declare (xargs :measure (nfix (- (nfix n) (nfix i)))))
           (if (zp (- (nfix n) (nfix i)))
               nil
             (b* ((n (1- (nfix n))))
               (cons (cons n (logbitp n input))
                     (integer-to-aig-env-intermed-2 i n input))))))

  (local (defthmd integer-to-aig-env-intermed-2-open-rev
           (implies (< (nfix i) (nfix n))
                    (equal (integer-to-aig-env-intermed-2 i n input)
                           (append (integer-to-aig-env-intermed-2 (+ 1 (nfix i)) n input)
                                   (list (cons (nfix i) (logbitp i input))))))
           :hints(("Goal" :in-theory (enable integer-to-aig-env-intermed-2)))))

  (local (defthm integer-to-aig-env-intermed-2-is-1
             (equal (integer-to-aig-env-intermed-1 i n input acc)
                    (append (integer-to-aig-env-intermed-2 i n input) acc))
             :hints (("goal" :induct (integer-to-aig-env-intermed-1 i n input acc)
                      :in-theory (enable integer-to-aig-env-intermed-2-open-rev)))))

  (local (defthm integer-to-aig-env-intermed-2-of-0
           (equal (integer-to-aig-env-intermed-2 0 n input)
                  (integer-to-aig-env n input))))

  (local (defthm integer-to-aig-env-aux-of-ifix
           (equal (integer-to-aig-env-aux i n (ifix input) acc)
                  (integer-to-aig-env-aux i n input acc))
           :hints(("Goal" 
                   :expand ((:free (input) (integer-to-aig-env-aux i n input acc)))))))
  
  (local (defthm integer-to-aig-env-aux-elim
           (equal (integer-to-aig-env-aux 0 n input nil)
                  (integer-to-aig-env n input))
           :hints (("goal" :use ((:instance integer-to-aig-env-aux-is-intermed-1 (i 0) (acc nil)))
                    :in-theory (disable integer-to-aig-env-aux-is-intermed-1)))))

  (verify-guards integer-to-aig-env)
  
  ;; (local
  ;;  (defthm integer-to-aig-env-aux-elim-1
  ;;    (equal (integer-to-aig-env-intermed i n input acc)
  ;;           (integer-to-aig-env-aux i n (logtail i input) acc))
  ;;    :hints(("Goal" :in-theory (enable integer-to-aig-env-aux)
  ;;            :induct (integer-to-aig-env-intermed i n input acc)))))
  
  (fgl::def-fgl-rewrite integer-to-aig-env-fgl
    (equal (integer-to-aig-env n input)
           (integer-to-aig-env-aux 0 n input nil)))

  
  (defret hons-assoc-equal-of-<fn>
    (equal (hons-assoc-equal k env)
           (and (natp k)
                (< k (nfix n))
                (cons k (logbitp k input)))))
  (defret aig-env-lookup-of-<fn>
    (equal (acl2::aig-env-lookup k env)
           (or (not (natp k))
               (>= k (nfix n))
               (logbitp k input)))
    :hints(("Goal" :in-theory (enable acl2::aig-env-lookup)))))


;; Produces an AIG that is true if variables 0...N-1 match the values of bits 0...N-1 of the target number.
(define integer-to-aig ((n natp) (target integerp))
  :returns (aig)
  (b* (((when (zp n)) t)
       (n (1- n)))
    (acl2::aig-and (if (logbitp n target)
                       n
                     (acl2::aig-not n))
                   (integer-to-aig n target)))
  ///
  
  (local (defthm equal-loghead-by-logbitp
           (implies (and (equal (loghead (+ -1 n) x)
                                (loghead (+ -1 n) y))
                         (posp n))
                    (equal (equal (loghead n x)
                                  (loghead n y))
                           (equal (logbitp (+ -1 n) x)
                                  (logbitp (+ -1 n) y))))
           :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions
                                              bitops::ihsext-recursive-redefs)))))

  (local (defthm equal-loghead-n-minus-1
           (implies (equal (loghead n x)
                           (loghead n y))
                    (equal (equal (loghead (+ -1 n) x)
                                  (loghead (+ -1 n) y))
                           t))
           :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions
                                              bitops::ihsext-recursive-redefs)))))
  
  (defret <fn>-correct
    (implies (<= (nfix n) (nfix k))
             (iff (acl2::aig-eval aig (integer-to-aig-env k input))
                  (equal (loghead n input) (loghead n target))))
    :hints (("goal" :induct <call>
             :expand (<call>)))))


(define integer-list-to-aig ((width natp) (targets integer-listp))
  :returns (aig)
  (if (atom targets)
      nil
    (acl2::aig-or (integer-to-aig width (car targets))
                  (integer-list-to-aig width (cdr targets))))
  ///
  (defret <fn>-correct-for-unsigned
    (implies (and (acl2::unsigned-byte-listp width targets)
                  (unsigned-byte-p width input))
             (iff (acl2::aig-eval aig (integer-to-aig-env width input))
                  (member-equal input targets)))
    :hints(("Goal" :in-theory (e/d (acl2::unsigned-byte-listp)
                                   (unsigned-byte-p)))))

  (local (defthm loghead-equal-when-signed-byte-p
           (implies (and (signed-byte-p n x)
                         (signed-byte-p n y))
                    (equal (equal (loghead n x) (loghead n y))
                           (equal x y)))
           :hints(("Goal" :in-theory (e/d* (bitops::ihsext-inductions
                                            bitops::ihsext-recursive-redefs)
                                           (signed-byte-p))))))
  
  (defret <fn>-correct-for-signed
    (implies (and (acl2::signed-byte-listp width targets)
                  (signed-byte-p width input))
             (iff (acl2::aig-eval aig (integer-to-aig-env width input))
                  (member-equal input targets)))
    :hints(("Goal" :in-theory (e/d (acl2::signed-byte-listp)
                                   (signed-byte-p))))))



(define integer-list-signedp ((x integer-listp))
  (if (atom x)
      nil
    (or (< (lifix (car x)) 0)
        (integer-list-signedp (cdr x)))))


(define max-integer-length ((x integer-listp))
  :returns (max-len natp :rule-classes :type-prescription)
  (if (atom x)
      0
    (max (integer-length (car x))
         (max-integer-length (cdr x))))
  ///
  (local (defthm unsigned-byte-p-by-integer-length
           (implies (and (natp x)
                         (natp n)
                         (<= (integer-length x) n))
                    (unsigned-byte-p n x))
           :hints(("Goal" :in-theory (e/d* (bitops::ihsext-inductions
                                            bitops::ihsext-recursive-redefs)
                                           (unsigned-byte-p))))))
  
  (defthm unsigned-byte-listp-by-max-integer-length
    (implies (and (integer-listp x)
                  (not (integer-list-signedp x))
                  (<= (max-integer-length x) n)
                  (natp n))
             (acl2::unsigned-byte-listp n x))
    :hints(("Goal" :in-theory (e/d (integer-list-signedp acl2::unsigned-byte-listp)
                                   (unsigned-byte-p)))))

  (local (defthm signed-byte-p-by-integer-length
           (implies (and (integerp x)
                         (posp n)
                         (< (integer-length x) n))
                    (signed-byte-p n x))
           :hints(("Goal" :in-theory (e/d* (bitops::ihsext-inductions
                                            bitops::ihsext-recursive-redefs)
                                           (signed-byte-p))))))
  
  (defthm signed-byte-listp-by-max-integer-length
    (implies (and (integer-listp x)
                  (< (max-integer-length x) n)
                  (natp n))
             (acl2::signed-byte-listp n x))
    :hints(("Goal" :in-theory (e/d (acl2::unsigned-byte-listp)
                                   (unsigned-byte-p))))))


(define integer-list-to-aig-top ((x integer-listp))
  :returns (mv signedp width aig)
  (b* ((signedp (integer-list-signedp x))
       (len (max-integer-length x))
       (width (if signedp (+ 1 len) len))
       (aig (integer-list-to-aig width x)))
    (mv signedp width aig))
  ///
  (memoize 'integer-list-to-aig-top)


  (local (defthm signed-byte-p-when-member-signed-byte-listp
           (implies (and (member-equal x lst)
                         (acl2::signed-byte-listp n lst))
                    (signed-byte-p n x))
           :hints(("Goal" :in-theory (enable acl2::signed-byte-listp)))))

  (local (defthm unsigned-byte-p-when-member-unsigned-byte-listp
           (implies (and (member-equal x lst)
                         (acl2::unsigned-byte-listp n lst))
                    (unsigned-byte-p n x))
           :hints(("Goal" :in-theory (enable acl2::unsigned-byte-listp)))))
  
  (defthmd member-equal-of-integer-list
    (implies (and (syntaxp (fgl-object-case lst :g-concrete))
                  (integer-listp lst))
             (iff (member-equal x lst)
                  (b* (((mv signedp width aig) (integer-list-to-aig-top lst)))
                    (and (if signedp
                             (signed-byte-p width x)
                           (unsigned-byte-p width x))
                         (acl2::aig-eval aig (integer-to-aig-env width x))))))))

(fgl::def-fgl-rewrite memberp-equal-of-integer-list
  (implies (and (syntaxp (fgl-object-case lst :g-concrete))
                (integer-listp lst))
           (equal (memberp-equal x lst)
                  (b* (((mv signedp width aig) (integer-list-to-aig-top lst)))
                    (and (if signedp
                             (signed-byte-p width x)
                           (unsigned-byte-p width x))
                         (car (acl2::aig-eval-list (list aig)
                                                   (make-fast-alist (integer-to-aig-env width x))))))))
  :hints(("Goal" :use member-equal-of-integer-list
          :in-theory (enable acl2::aig-eval-list))))
                        

