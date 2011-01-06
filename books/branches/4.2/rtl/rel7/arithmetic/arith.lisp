(in-package "ACL2")

;This book contains basic arith stuff which i'm pretty sure won't hurt anything.

(local (include-book "arith2"))
(include-book "meta/meta-plus-equal" :dir :system)
(include-book "meta/meta-plus-lessp" :dir :system)
(include-book "meta/meta-times-equal" :dir :system)

;Note!  There is not meta-times-lessp, which would be really nice to have.  I now have a bind-free rule to do that...

(defthm collect-constants-in-equal-of-sums
  (implies (and (syntaxp (and (quotep c1) (quotep c2)))
                (case-split (acl2-numberp c1))
                )
           (and (equal (equal (+ c2 x) c1)
                       (equal (fix x) (- c1 c2)))
                (equal (equal c1 (+ c2 x))
                       (equal (fix x) (- c1 c2))))))

(defthm collect-constants-in-equal-of-sums-2
  (implies (syntaxp (and (quotep c1) (quotep c2)))
           (and (equal (equal (+ c2 x) (+ c1 y))
                       (equal (fix x) (+ (- c1 c2) y))))))

(defthm collect-constants-in-<-of-sums
  (implies (syntaxp (and (quotep c1) (quotep c2)))
           (and (equal (< (+ c2 x) c1)
                       (< x (- c1 c2)))
                (equal (< c1 (+ c2 x))
                       (< (- c1 c2) x)))))

(defthm collect-constants-in-<-of-sums-2
  (implies (syntaxp (and (quotep c1) (quotep c2)))
           (equal (< (+ c2 x) (+ c1 y))
                  (< x (+ (- c1 c2) y)))))

;I put this in because it seems to help rewrite stupid hyps quickly.
(defthm dumb
  (equal (< x x)
         nil))