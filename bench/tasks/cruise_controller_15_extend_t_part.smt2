; K = 0
; Transition relation
(define-fun T ((%init Bool) ($mode$0 Int) ($desiredSpeed$0 Real) ($OK$0 Bool) ($mode$1 Int) ($desiredSpeed$1 Real) ($OK$1 Bool)) Bool (= $OK$1 (or (not (or (= $mode$1 1) (= $mode$1 3))) (= $desiredSpeed$1 (/ 0 10)))))
; Universally quantified variables
(declare-fun %init () Bool)
(declare-fun $mode$~1 () Int)
(declare-fun $desiredSpeed$~1 () Real)
(declare-fun $OK$~1 () Bool)
(declare-fun $mode$2 () Int)
(declare-fun $desiredSpeed$2 () Real)
(declare-fun $OK$2 () Bool)
(assert (and (T %init $mode$~1 $desiredSpeed$~1 $OK$~1 $mode$2 $desiredSpeed$2 $OK$2) $OK$2))
