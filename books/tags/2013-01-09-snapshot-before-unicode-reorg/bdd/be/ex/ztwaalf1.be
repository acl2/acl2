@BE1
@invar 
 (a1 a2 a3 a4 a5 a6 b1 b2 b3 b4 b5 b6)


@out
out =
   (or (and a1 a2 (not a6))   (and (not a3) (not a4) (not a5) (not a6))
    (and (not a3) a4 a5 (not a6))   (and (not a1) (not b1))    
    (and (not a1) (not b2) (not b3))  (and (not a1) (not b2) b4 (not b5)) 
    (and (not a1) (not b2) (not b4) b5)  (and a1 a2 (not b6))
    (and (not a3) (not a4) (not a5) (not b6)) (and (not a3) a4 a5 (not b6)) 
    (and (not b1) (not b6))  (and (not b2) (not b3) (not b6)) 
    (and (not b2) b4 (not b5) (not b6))  (and (not b2) (not b4) b5 (not b6))
    (and (not a1) a3 a6 b6)   (and (not a2) a3 a6 b6) 
    (and (not a1) a4 (not a5) a6 b6)   (and (not a2) a4 (not a5) a6 b6)
    (and (not a1) (not a4) a5 a6 b6)   (and (not a2) (not a4) a5 a6 b6)
    (and a1 b1 b2 b6)  (and a1 b1 b3 (not b4) (not b5) b6)
    (and a1 b1 b3 b4 b5 b6))

@end


@BE2
@invar 
(a1 a2 a3 a4 a5 a6 b1 b2 b3 b4 b5 b6)

@sub
s1 =
 (exor (or (and a1 a2) (and (not a3) (not (exor a4 a5)))) (and a6 b6))
s2 =
 (exor (and b1 (or b2 (and b3 (not (exor b4 b5))))) (and b6 a1))

@out
out =
   (or s1 (not s2))

@end
