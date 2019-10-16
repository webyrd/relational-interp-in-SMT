(declare-datatypes ((Ssym 0) (Sexpr 0)  )
                   (((sa)
                     (sb))
                    ((mynil)
                     (mycons (hd Sexpr) (tl Sexpr))
                     (ssym (ssym-val Ssym)))
                    ))

(define-fun-rec eval2
  ((fuel Int)
    (exp Sexpr)) Sexpr
  (ite (> fuel 0)
       (ite ((_ is mycons) exp)
            (ite (= (hd exp) (ssym sa))
                 (ite ((_ is mycons) (tl exp))
                      (eval2 (- fuel 1) (tl exp))
                      mynil)
                 (eval2 (- fuel 1) (tl exp)))
            mynil)
       mynil))

(declare-const ma8 Sexpr)
(assert (= ma8 (eval2 10 (mycons (ssym sb) mynil))))
(assert (not (= ma8 mynil)))
(check-sat)
(get-model)


(define-fun-rec eval3
  ((fuel Int)
    (exp Sexpr)) Sexpr
  (ite (> fuel 0)
       (ite ((_ is mycons) exp)
            (ite (= (hd exp) (ssym sa))
                 (eval3 (- fuel 1) (tl exp))
                 (eval3 (- fuel 1) (tl exp)))
            mynil)
       mynil))

(declare-const ma9 Sexpr)
(assert (= ma9 (eval3 10 (mycons (ssym sb) mynil))))
(assert (not (= ma9 mynil)))
(check-sat)
(get-model)
