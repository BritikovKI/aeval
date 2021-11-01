(set-logic HORN)

(declare-datatypes ((listOfInt 0) )
(((cons-listOfInt (head-listOfInt Int) (tail-listOfInt listOfInt)) (nil-listOfInt))))
(declare-datatypes ((queueOfInt 0) )
(((queue-queueOfInt (front-queueOfInt listOfInt) (back-queueOfInt listOfInt)) )))

(declare-fun len (listOfInt Int) Bool)
(declare-fun append (listOfInt listOfInt listOfInt) Bool)
(declare-fun queuetolst (queueOfInt listOfInt) Bool)
(declare-fun qrev (listOfInt listOfInt) Bool)
(declare-fun qreva (listOfInt listOfInt listOfInt) Bool)
(declare-fun amortizequeue (listOfInt listOfInt queueOfInt) Bool)
(declare-fun butlast (listOfInt listOfInt) Bool)
(declare-fun qpop (queueOfInt queueOfInt) Bool)

(declare-fun ff () Bool)

(assert
  (forall ( (A Int) )
    (=>
      (= A 0)
      (len nil-listOfInt A)
    )
  )
)
(assert
  (forall ( (A Int) (B listOfInt) (C Int) (D Int) )
    (=>
      (and
        (= C (+ 1 D))
        (len B D)
      )
      (len (cons-listOfInt A B) C)
    )
  )
)
(assert
  (forall ( (A listOfInt) )
    (append nil-listOfInt A A)
  )
)
(assert
  (forall ( (A Int) (B listOfInt) (C listOfInt) (D listOfInt) )
    (=>
      (append B C D)
      (append (cons-listOfInt A B) C (cons-listOfInt A D))
    )
  )
)
(assert
  (forall ( (A listOfInt) )
    (qreva nil-listOfInt A A)
  )
)
(assert
  (forall ( (A Int) (B listOfInt) (C listOfInt) (D listOfInt) )
    (=>
      (qreva B (cons-listOfInt A C) D)
      (qreva (cons-listOfInt A B) C D)
    )
  )
)
(assert
  (forall ( (A listOfInt) (B listOfInt) )
    (=>
      (qreva A nil-listOfInt B)
      (qrev A B)
    )
  )
)
(assert
  (forall ( (A listOfInt) (B listOfInt) (C listOfInt) (D listOfInt) )
    (=>
      (and
        (qrev B D)
        (append A D C)
      )
      (queuetolst (queue-queueOfInt A B)  C)
    )
  )
)
(assert
  (forall ( (A listOfInt) (B listOfInt) (C Bool) (D Int) (E Int) )
    (=>
      (and
        (<= D E)
        (len A E)
        (len B D)
      )
      (amortizequeue A B (queue-queueOfInt A B) )
    )
  )
)
(assert
  (forall ( (A listOfInt) (B listOfInt) (C listOfInt) (D Bool) (E Int) (F Int) (G listOfInt) )
    (=>
      (and
        (> E F)
        (len A F)
        (len B E)
        (append A G C)
        (qrev B G)
      )
      (amortizequeue A B (queue-queueOfInt C nil-listOfInt) )
    )
  )
)
(assert
    (butlast nil-listOfInt nil-listOfInt)
)
(assert
  (forall ( (A Int) )
    (butlast (cons-listOfInt A nil-listOfInt) nil-listOfInt)
  )
)
(assert
  (forall ( (A Int) (B Int) (C listOfInt) (D listOfInt) )
    (=>
      (butlast (cons-listOfInt B C) D)
      (butlast (cons-listOfInt A (cons-listOfInt B C)) (cons-listOfInt A D))
    )
  )
)
(assert
  (forall ( (A listOfInt) (B Int) (C listOfInt) )
    (qpop (queue-queueOfInt A (cons-listOfInt B C))  (queue-queueOfInt A C) )
  )
)
(assert
  (forall ( (A listOfInt) (B listOfInt) )
    (=>
      (butlast A B)
      (qpop (queue-queueOfInt A nil-listOfInt)  (queue-queueOfInt B nil-listOfInt) )
    )
  )
)

(assert
  (forall ( (A Bool) (B listOfInt) (C listOfInt) (D listOfInt) (E listOfInt) (F queueOfInt) (G listOfInt) )
    (=>
      (and
        (queuetolst (queue-queueOfInt B C)  D)
        (butlast D E)
        (qpop (queue-queueOfInt B C)  F)
        (queuetolst F G)
        (not (= E G))
      )
      ff
    )
  )
)


(assert (not ff))
(check-sat)