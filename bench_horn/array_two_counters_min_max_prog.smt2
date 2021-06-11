(declare-var a (Array Int Int))
(declare-var b (Array Int Int))
(declare-var b1 (Array Int Int))
(declare-var c (Array Int Int))
(declare-var c1 (Array Int Int))
(declare-var i Int)
(declare-var i1 Int)
(declare-var j Int)
(declare-var j1 Int)
(declare-var m Int)
(declare-var m1 Int)
(declare-var n Int)
(declare-var n1 Int)
(declare-var N Int)

(declare-rel inv ((Array Int Int) (Array Int Int) (Array Int Int) Int Int Int Int Int))
(declare-rel fail ())

(rule (=> (> N 0) (inv a b c 0 (- N 1) m n N)))

(rule (=> (and (inv a b c i j m n N)
    (< i N) (>= j 0)
    (= m1 (ite (= i 0) (select a i) (ite (> (select a i) m) (select a i) m)))
    (= n1 (ite (= j (- N 1)) (select a j) (ite (< (select a j) n) (select a j) n)))
    (= b1 (store b i m1))
    (= c1 (store c j n1))
    (= i1 (+ i 1))
    (= j1 (- j 1))) (inv a b1 c1 i1 j1 m1 n1 N)))

(rule (=> (and (inv a b c i j m n N) (not (and (< i N) (>= j 0))) (< 0 i1) (< i1 N)
  (not (>= (select b i1) (select c i1)))) fail))

(query fail)
