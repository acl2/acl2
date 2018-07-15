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


(in-package "ACL2")

(include-book "../symbol-fns/symbol-fns")

(defun deffix-fixed-p-fn (prefix fix fixed-p equiv)
  (let* ((equiv-reduction           (symbol-fns::suffix prefix equiv '_ fix '_reduction))
         (fixed-p                   (or fixed-p (symbol-fns::suffix fix 'ed-p)))
         (fixed-p-fix               (symbol-fns::suffix prefix fixed-p '_ fix))
         (equal-fix-to-equiv        (symbol-fns::suffix prefix 'equal_ fix '_to_ equiv))
         (fixed-p-fix-reduction     (symbol-fns::suffix prefix fixed-p '_ fix '_reduction))
         )
    `(encapsulate
         ()

       ;; Fixed predicates ..
       (defund ,fixed-p (x)
	 (equal x (,fix x)))
       
       (in-theory (disable (,fixed-p)))
       
       (defthm ,fixed-p-fix
	 (,fixed-p (,fix x))
	 :rule-classes (:rewrite
			(:forward-chaining :trigger-terms ((,fix x))))
	 :hints (("Goal" :in-theory (enable ,fixed-p))))
       
       (defthm ,fixed-p-fix-reduction
	 (implies
	  (,fixed-p x)
	  (equal (,fix x) x))
	 :hints (("Goal" :in-theory (enable ,fixed-p))))
       
       (defthmd ,equal-fix-to-equiv
	 (equal (equal (,fix x) y)
		(and (,fixed-p y)
		     (,equiv x y)))
	 :hints (("Goal" :in-theory (enable ,fixed-p ,equiv-reduction))))
       
       (theory-invariant (incompatible (:rewrite ,equal-fix-to-equiv)
				       (:rewrite ,equiv-reduction)))

       )))
       

(defun deffix-raw-fn (prefix fix fixed-p equiv in-theory)
  (let ((fix-fixes                 (symbol-fns::suffix prefix fix '_fixes))
	(equal-fix-implies-equiv   (symbol-fns::suffix prefix 'equal_ fix '_implies_ equiv))
	(equiv-reduction           (symbol-fns::suffix prefix equiv '_ fix '_reduction))
        (any-fix-is-equiv          (symbol-fns::suffix prefix 'any_ fix '_is_ equiv))
        )

  `(encapsulate
       ()

     ,@(and in-theory `((local (in-theory ,in-theory))))

     (defchoose ,fix x (y)
       (,equiv x y)
       :strengthen t)

     (encapsulate
	 ()

       (defcong ,equiv equal (,fix y) 1
	 :hints (("Goal" :use (:instance ,fix (y1 y-equiv)))))

       (defthm ,fix-fixes
	 (,equiv (,fix x) x)
	 :hints (("Goal" :use ((:instance ,fix (y x))))))

       ;; anything that fixes to this point is equiv

       (local
	(defthm ,any-fix-is-equiv
	  (implies (equal y (,fix x))
		   (,equiv y x))
	  :rule-classes nil)
	)

       (local
	(defthmd ,equal-fix-implies-equiv
	  (implies (equal (,fix y) (,fix x))
		   (equal (,equiv y x) t))
	  :hints (("Goal" :use (:instance ,any-fix-is-equiv (y (,fix y))))))
	)

       (defthmd ,equiv-reduction
	 (equal (,equiv x y)
		(equal (,fix x) (,fix y)))
	 :hints (("Goal" :in-theory (enable ,equal-fix-implies-equiv))))

       ,(deffix-fixed-p-fn prefix fix fixed-p equiv)
       
       ))))

(defun deffix-type-fn (prefix fix fixed-p equiv type type-fix in-theory)
  (let* ((type-equiv         (symbol-fns::suffix prefix type '_equiv))
         (fix-preserves-type (symbol-fns::suffix prefix fix '_preserves_ type))
         (define-refinement  type-fix)
         (refined-equiv      (if define-refinement (symbol-fns::suffix prefix 'refined_ equiv) equiv))
         )
    `(encapsulate
         ()

       ,@(and in-theory `((local (in-theory ,in-theory))))
       
       ;; ------------------------------------------------

       ;; ------------------------------------------------

       ,@(and define-refinement
              `(
                (defun ,type-equiv (x y)
                  (equal (,type x) 
                         (,type y)))
                
                (defequiv ,type-equiv)
                
                (defcong ,type-equiv equal (,type x) 1)
                
                (defun ,refined-equiv (x y)
                  (and (,type-equiv x y)
                       (,equiv x y)))
                
                (defequiv ,refined-equiv)
                (defrefinement ,refined-equiv ,type-equiv)       
                (defrefinement ,refined-equiv ,equiv)
                
                ))
                
       ;; If there is no fixing function, this will need to follow
       ;; from the original equivalence relation.
       (defcong ,refined-equiv equal (,type x) 1)
       
       ,@(and define-refinement `((in-theory (disable ,type-equiv ,refined-equiv))))

       ;; ------------------------------------------------

       ;; The workhorse
       ,(deffix-raw-fn prefix fix fixed-p refined-equiv nil)
       
       (local
        ;; We get this for free via the refined-equiv congruence theorem .. so we don't export it.
        (defthm ,fix-preserves-type
          (equal (,type (,fix x))
                 (,type x))))
       
       )))

(defun deffix-fix-fn (prefix fix fixed-p equiv type type-fix in-theory)
  (let* ((type-fix-equiv               (symbol-fns::suffix prefix type-fix '_equiv))
         (type-fix-equiv-type-fix      (symbol-fns::suffix prefix type-fix '_equiv_of_ type-fix))
         (equiv-type-fix               (symbol-fns::suffix prefix equiv '_ type-fix))
         (type-fix-equiv-refines-equiv (symbol-fns::suffix prefix type-fix '_equiv_refines_ equiv))
         (refined-fix                  (symbol-fns::suffix prefix 'refined_ fix))
         (refined-fixed-p              (if fixed-p (symbol-fns::suffix prefix 'refined_ fixed-p)
                                         (symbol-fns::suffix prefix 'refined_ fix 'ed-p)))
         (type-equiv                   (symbol-fns::suffix prefix type '_equiv))
         (refined-equiv                (symbol-fns::suffix prefix 'refined_ equiv))
         (fix-is-type                  (symbol-fns::suffix prefix fix '_is_ type))
         (equiv-fix                    (symbol-fns::suffix prefix equiv '_of_ fix))
         (equiv_reduction              (symbol-fns::suffix prefix equiv '_ fix '_reduction))
         (refined-equiv-reduction      (symbol-fns::suffix prefix refined-equiv '_ refined-fix '_reduction))
         )

    `(encapsulate
         ()

       ,@(and in-theory `((local (in-theory ,in-theory))))
       
       (defun ,type-fix-equiv (x y)
         (equal (,type-fix x) (,type-fix y)))
       
       (defequiv ,type-fix-equiv)
       
       (defcong ,type-fix-equiv equal (,type-fix x) 1)
       
       (defthm ,type-fix-equiv-type-fix
         (,type-fix-equiv (,type-fix x) x))
       
       (encapsulate
           ()
         
         ;; We need to prove this in the user-provided theory ..
         (local
          (defthm ,equiv-type-fix
            (iff (,equiv (,type-fix x) (,type-fix y))
                 (,equiv x y))))
         
         (defthm ,type-fix-equiv-refines-equiv
           (implies
            (,type-fix-equiv x y)
            (,equiv x y))
           :hints (("Goal" :in-theory '(,type-fix-equiv)
                    :use ,equiv-type-fix))
           :rule-classes (:refinement))
         
         )
       
       (in-theory (disable ,type-fix-equiv))
       
       ,(deffix-type-fn prefix refined-fix refined-fixed-p equiv type type-fix in-theory)

       (defun ,fix (x)
         (declare (type t x))
         (,refined-fix (ec-call (,type-fix x))))
       
       (in-theory (disable (,fix)))

       (defthm ,fix-is-type
         (,type (,fix x))
         :rule-classes (:type-prescription 
                        :rewrite
                        (:forward-chaining :trigger-terms ((,fix x)))))
       
       (defthm ,equiv-fix
         (,equiv (,fix x) x))
       
       (defthmd ,equiv_reduction
         (iff (,equiv x y)
              (equal (,fix x) (,fix y)))
         :hints (("Goal" :in-theory (enable ,refined-equiv ,type-equiv)
                  :use (:instance ,refined-equiv-reduction (x (,type-fix x)) (y (,type-fix y))))))
       
       (defcong ,equiv equal (,fix x) 1
         :hints (("goal" :in-theory (enable ,equiv_reduction))))
       
       (in-theory (disable ,fix))
       
       ,(deffix-fixed-p-fn prefix fix fixed-p equiv)

       )))

(defun deffix-fn (fix fixed-p equiv type type-fix in-theory)
  (let ((prefix (symbol-fns::suffix (symbol-fns::prefix 'deffix_ equiv) '_)))
    (if (not type) (deffix-raw-fn prefix fix fixed-p equiv in-theory)
      ;; If you provide a type but no fixing function, equiv
      ;; must satisfy (defcong equiv equal (type x) 1)
      (if (not type-fix) (deffix-type-fn prefix fix fixed-p equiv type type-fix in-theory)
        ;; If you provide a type-fix function, equiv must be
        ;; a refinement of (equal (fix x) (fix y))
        (deffix-fix-fn prefix fix fixed-p equiv type type-fix in-theory)))))

(defmacro def::fix (fix equiv &key (fixed-p 'nil) (type 'nil) (type-fix 'nil) (in-theory 'nil))
  (deffix-fn fix fixed-p equiv type type-fix in-theory))

(local
 (encapsulate
     ()

   (defun my-eq (x y)
     (equal x y))

   (defequiv my-eq)

   (encapsulate
       ()

     (local (in-theory (disable my-eq)))
     
     (def::fix my-fix my-eq :in-theory '(my-eq-is-an-equivalence))
     
     )

   ))

(local
 (encapsulate
     ()

   (defun my-type (x)
     (integerp x))

   (defun my-type-eq (x y)
     (equal x y))

   (defequiv my-type-eq)

   ;; ==============================================================

   ;; We need to know this about the equivalence relation and the
   ;; type if we don't provide a fixing function ..

   (defcong my-type-eq equal (my-type x) 1)

   ;; ==============================================================

   (encapsulate
       ()

     (local (in-theory (disable my-type my-type-eq)))
     
     (def::fix fix-my-type-eq my-type-eq 
       :type my-type
       )
     
     )

   ))

(local
 (encapsulate
     ()

   (defun typex (x)
     (integerp x))

   (defun fixx (x)
     (if (typex x) x 0))

   (defun equivx (x y)
     (equal (fixx x)
            (fixx y)))

   (defequiv equivx)

   ;; ==============================================================

   ;; Here are the things we need to know about the functions typex,
   ;; fixx and equivx :

   (defthm typex-fixx
     (typex (fixx x)))

   (defthm fixx-fixx
     (equal (fixx (fixx x))
            (fixx x)))

   ;; Which is to say: equiv fixes it's arguments.
   (defthm equivx-fixx
     (and (equal (equivx (fixx x) y)
                 (equivx x y))
          (equal (equivx x (fixx y))
                 (equivx x y))))

   ;; ==============================================================

   (encapsulate
       ()

     (local (in-theory (disable typex fixx equivx)))

     (def::fix fix-equivx equivx 
       :type typex
       :type-fix fixx
       )

     )

   ))
