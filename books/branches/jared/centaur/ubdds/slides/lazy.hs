
ints i = i : ints (i+1)

member a x = if x == []
               then False
             else if (a == head x)
               then True
             else
               member a (tail x)

intersect x y = if x == []
                  then []
                else if (member (head x) y)
                  then (head x) : (intersect (tail x) y)
                else
                  intersect (tail x) y

opp_intersect x y = if y == []
                      then []
                    else 
                      intersect x y
    