(declare-datatypes ((|bytes_tuple| 0)) (((|bytes_tuple| (|bytes_tuple_accessor_array| (Array Int Int)) (|bytes_tuple_accessor_length| Int)))))

(declare-fun uf ((|bytes_tuple|)) Int)
(declare-fun ufa ((|bytes_tuple|)) (Array Int Int))

(declare-fun bytes_tuple_1 () |bytes_tuple|)

(declare-fun arr () (Array Int Int))

(assert (= bytes_tuple_1 (|bytes_tuple| arr 1)))
(assert (= 1 (uf bytes_tuple_1)))
(assert (= arr (ufa bytes_tuple_1)))

(assert (not (= 1 (uf bytes_tuple_1))))

(check-sat)
; now, unsat
