(set-logic HORN)
(declare-datatypes () ((Lst (cons (head Int) (tail Lst)) (nil))))
(declare-fun length (Lst Int) Bool)
(declare-fun append (Lst Lst Lst) Bool)
(declare-fun butlast (Lst Lst) Bool)

(assert (length nil 0))
(assert (forall ((x Int) (xs Lst) (ys Lst) (l Int)) 
           (=> (and (= xs (cons x ys)) (length ys l)) (length xs (+ l 1)))))

(assert (butlast nil nil))
(assert (forall ((n Int) (xs Lst) (rs Lst) (ys Lst)) (=> (and (= ys (cons n xs)) (= xs nil)) (butlast ys nil))))
(assert (forall ((n Int) (xs Lst) (rs Lst) (ys Lst) (x Int) (zs Lst))
	(=> (and (butlast xs rs) (= ys (cons n xs)) (= xs (cons x zs))) (butlast ys (cons n rs)))))

(assert (forall ((xs Lst) (ys Lst) (zs Lst) (n Int) (l1 Int) (l2 Int)) 
	(=> (and (= ys (cons n xs)) (butlast ys zs) (length ys l1) (length zs l2) (not (= (+ l2 1) l1))) false)))
(check-sat)