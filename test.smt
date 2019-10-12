(declare-datatypes ((Maybe 1))
                   ((par (T)
                     ((just (just-v T))
                      (nothing)))))

(declare-const a Int)
(declare-const b (Maybe Int))

;; (assert (= a (just-v (just 1))))
;; (check-sat)
;; (get-model)

;; (assert (not (= a 1)))
;; (check-sat)
;; (get-model)

(assert (= b (as nothing (Maybe Int))))
(assert (and ((_ is just) b)
             (= a (just-v b))))
(check-sat)
(get-model)

(assert (not (= a 0)))
(check-sat)
(get-model)
