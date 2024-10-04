(in-package "DJVM")

(include-book "base")
(include-book "base-consistent-state")


;; the following proof is slow. make it a separate book! 

(defthm isAssignable-car-opstack-sig-to-class-implies-car-opstack-reduce-to-value-sig
  (implies (bcv::isAssignable (car (opstack-sig stk cl hp hp-init method-ptr))
                              (bcv::prefix-class any) 
                              env)
           (not (canPopCategory2 stk))))

