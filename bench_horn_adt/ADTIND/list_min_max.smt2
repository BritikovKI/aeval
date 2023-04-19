(set-logic HORN)
(declare-datatypes () ((Lst (cons (head Int) (tail Lst)) (nil))))
(declare-fun min (Lst Int) Bool)
(assert (min nil 0))
(assert (forall ((x Int) (xs Lst) (ys Lst) (l Int) (r Int)) 
           (=> (and (= xs (cons x ys)) (min ys l) (= r (ite (< l x) l x))) (min xs r))))

(declare-fun max (Lst Int) Bool)
(assert (max nil 0))
(assert (forall ((x Int) (xs Lst) (ys Lst) (l Int) (r Int)) 
           (=> (and (= xs (cons x ys)) (max ys l) (= r (ite (> l x) l x))) (max xs r))))

(assert (forall ((x Int) (y Int) (xs Lst))
       (=> (and (min xs x) (max xs y) (not (>= y x))) false)))
(check-sat)