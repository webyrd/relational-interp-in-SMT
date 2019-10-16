(declare-datatypes ((Ssym 0) (Sexpr 0)  )
                   (((sa)
                     (sb))
                    ((nil)
                     (cons (hd Sexpr) (tl Sexpr))
                     (ssym (ssym-val Ssym)))
                    ))

(define-fun-rec eval2
  ((fuel Int)
    (exp Sexpr)) Sexpr
  (ite (>= fuel 0)
       (ite ((_ is cons) exp)
            (ite (= (hd exp) (ssym sa))
                 (ite ((_ is cons) (tl exp))
                      (eval2 (- fuel 1) (tl exp))
                      nil)
                 (eval2 (- fuel 1) (tl exp)))
            nil)
       nil))

(declare-const ma8 Sexpr)
(assert (= ma8 (eval2 10 (cons (ssym sb) nil))))
(assert (not (= ma8 nil)))
(check-sat)
(get-model)


(define-fun-rec eval3
  ((fuel Int)
    (exp Sexpr)) Sexpr
  (ite (>= fuel 0)
       (ite ((_ is cons) exp)
            (ite (= (hd exp) (ssym sa))
                 (eval3 (- fuel 1) (tl exp))
                 (eval3 (- fuel 1) (tl exp)))
            nil)
       nil))

(declare-const ma9 Sexpr)
(assert (= ma9 (eval3 10 (cons (ssym sb) nil))))
(assert (not (= ma9 nil)))
(check-sat)
(get-model)
