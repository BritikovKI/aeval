;; Original file: adr_114.smt2
(set-logic HORN)
(declare-fun |f$unknown:3| (Int Int Int) Bool)
(declare-fun |f$unknown:1| (Int) Bool)
(declare-fun |f$unknown:4| (Int Int) Bool)
(declare-fun |f$unknown:2| (Int Int) Bool)
(declare-fun |h$unknown:5| (Int) Bool)
(declare-fun |h$unknown:6| (Int Int) Bool)


(assert (forall ((|$knormal:1| Int)
         (|$alpha-1:x| Int)
         (|$V-reftype:15| Int)
         (|$knormal:2| Int))
  (=> (and (= |$knormal:1| (+ |$alpha-1:x| 1))
           (= |$V-reftype:15| |$knormal:2|)
           (|f$unknown:3| |$knormal:2| |$knormal:1| |$alpha-1:x|)
           (|f$unknown:1| |$alpha-1:x|))
      (|f$unknown:4| |$V-reftype:15| |$alpha-1:x|))))
(assert (forall ((|$knormal:1| Int) (|$alpha-1:x| Int))
  (=> (and (= |$knormal:1| (+ |$alpha-1:x| 1))
           (|f$unknown:1| |$alpha-1:x|))
      (|f$unknown:2| |$knormal:1| |$alpha-1:x|))))
(assert (forall ((|$knormal:4| Int) (|$alpha-4:n| Int) (|$V-reftype:3| Int))
  (let ((a!1 (and (= (not (= 0 |$knormal:4|)) (> |$alpha-4:n| 0))
                  (not (= 0 |$knormal:4|))
                  (|f$unknown:2| |$V-reftype:3| |$alpha-4:n|))))
    (=> a!1 (|h$unknown:5| |$V-reftype:3|)))))
(assert (forall ((|$knormal:4| Int)
         (|$alpha-4:n| Int)
         (|$V-reftype:10| Int)
         (h Int))
  (let ((a!1 (and (= (not (= 0 |$knormal:4|)) (> |$alpha-4:n| 0))
                  (not (= 0 |$knormal:4|))
                  (|h$unknown:6| |$V-reftype:10| h)
                  (|f$unknown:2| h |$alpha-4:n|))))
    (=> a!1 (|f$unknown:3| |$V-reftype:10| h |$alpha-4:n|)))))
(assert (forall ((|$knormal:3| Int)
         (|$alpha-3:y| Int)
         (|$V-reftype:17| Int))
  (let ((a!1 (and (= (not (= 0 |$knormal:3|)) (> |$alpha-3:y| 0))
                  (= |$V-reftype:17| 1)
                  (not (= 0 |$knormal:3|))
                  (|h$unknown:5| |$alpha-3:y|))))
    (=> a!1 (|h$unknown:6| |$V-reftype:17| |$alpha-3:y|)))))
(assert (forall ((|$knormal:3| Int) (|$alpha-3:y| Int))
  (let ((a!1 (and (= (not (= 0 |$knormal:3|)) (> |$alpha-3:y| 0))
                  (not (not (= 0 |$knormal:3|)))
                  (|h$unknown:5| |$alpha-3:y|))))
    (=> a!1 false))))
(assert (forall ((|$knormal:4| Int) (|$alpha-4:n| Int))
  (let ((a!1 (and (= (not (= 0 |$knormal:4|)) (> |$alpha-4:n| 0))
                  (not (= 0 |$knormal:4|)))))
    (=> a!1 (|f$unknown:1| |$alpha-4:n|)))))
(check-sat)