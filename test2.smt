(declare-datatypes ((Maybe 1))
                   ((par (T)
                     ((just (just-v T))
                      (nothing)))))

(declare-datatypes ((Ssym 0) (Sexpr 0) (Senv 0) (Sval 0))
                   (((sa)
                     (sb)
                     (sc)
                     (sd)
                     (se)
                     (sf)
                     (sg)
                     (slambda)
                     (skons)
                     (slist)
                     (squote)
                     )
                    ((nil)
                     (kons (hd Sexpr) (tl Sexpr))
                     (ssym (ssym-val Ssym)))
                    ((empty-env)
                     (ext-env (senv-id Ssym) (senv-val Sval) (senv-rest Senv)))
                    ((sexpr (sexpr-val Sexpr))
                     (sclo (sclo-id Ssym) (sclo-body Sexpr) (sclo-env Senv)))))

(define-fun is-kons-expression
  ((exp Sexpr)) Bool
  (and ((_ is kons) exp)
       (= (hd exp) (ssym skons))
       ((_ is kons) (tl exp))
       ((_ is kons) (tl (tl exp)))
       ((_ is nil) (tl (tl (tl exp))))))

(define-fun interp-kons
  ((exp Sexpr)) (Maybe Sexpr)
  (ite (is-kons-expression exp)
       (just (kons (hd (tl exp))
                   (hd (tl (tl exp)))))
       (as nothing (Maybe Sexpr))))


(declare-const a Sexpr)
(declare-const b (Maybe Sexpr))
(declare-const e1 Sexpr)
(declare-const e2 Sexpr)


(assert (= a (kons (ssym skons) (kons e1 (kons e2 nil)))))
(assert (= b (interp-kons a)))
(check-sat)
(get-model)


(assert (not (= b (just (kons e1 e2)))))
(check-sat)
(get-model)



;; (assert (= a (kons (ssym skons) (kons e1 (kons e2 nil)))))
;; (check-sat)
;; (get-model)
