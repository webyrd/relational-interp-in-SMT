;;; biggest problem:  can only do well-founded relations

(declare-datatypes ((Ssym 0) (Sexpr 0) (Senv 0) (Sval 0))
                   (((sa)
                     (sb)
                     (sc)
                     (sd)
                     (se)
                     (sf)
                     (sg)
                     (slambda)
                     (scons)
                     (squote)
                     )
                    ((nil)
                     (cons (hd Sexpr) (tl Sexpr))
                     (ssym (ssym-val Ssym)))
                    ((empty-env)
                     (ext-env (senv-id Ssym) (senv-val Sval) (senv-rest Senv)))
                    ((sexpr (sexpr-val Sexpr))
                     (sclo (sclo-id Ssym) (sclo-body Sexpr) (sclo-env Senv)))))

(declare-datatypes ((Maybe 1))
                   ((par (T)
                     ((just (just-v T))
                      (nothing)))))

(define-fun-rec env-lookup
  ((env Senv) (x Ssym)) (Maybe Sval)
  (ite ((_ is empty-env) env)
       (as nothing (Maybe Sval))
       (ite ((_ is ext-env) env)
            (ite (= (senv-id env) x)
                 (just (senv-val env))
                 (env-lookup (senv-rest env) x))
            (as nothing (Maybe Sval)))))

(define-fun is-quote
  ((exp Sexpr)) Bool
  (and ((_ is cons) exp)
       (= (hd exp) (ssym squote))
       ((_ is cons) (tl exp))
       ((_ is nil) (tl (tl exp)))))

(define-fun is-lambda
  ((exp Sexpr)) Bool
  (and ((_ is cons) exp)
       (= (hd exp) (ssym slambda))
       ((_ is cons) (tl exp))
       ((_ is cons) (hd (tl exp)))
       ((_ is nil) (tl (hd (tl exp))))
       ((_ is ssym) (hd (hd (tl exp))))
       ((_ is cons) (tl (tl exp)))
       ((_ is nil) (tl (tl (tl exp))))))

(define-fun is-kons
  ((exp Sexpr)) Bool
  (and ((_ is cons) exp)
       (= (hd exp) (ssym scons))
       ((_ is cons) (tl exp))
       ((_ is cons) (tl (tl exp)))
       ((_ is nil) (tl (tl (tl exp))))))

(define-fun is-app
  ((exp Sexpr)) Bool
  (and ((_ is cons) exp)
       ((_ is cons) (tl exp))
       ((_ is nil) (tl (tl exp)))))

;; (define-fun-rec even
;;   ((n Int)) Bool
;;   (or (= n 0)
;;        (not (odd (- n 1)))))

;; (define-fun-rec odd
;;   ((n Int)) Bool
;;   (or (= n 1)
;;       (not (even (- n 1)))))

(define-fun-rec eval
  ((fuel Int)
   (env Senv) (exp Sexpr)) (Maybe Sval)
  (ite (> fuel 0)
  (ite ((_ is ssym) exp)
       (env-lookup env (ssym-val exp))
  (ite (is-quote exp)
       (just (sexpr (hd (tl exp))))
  (ite (is-lambda exp)
       (just (sclo (ssym-val (hd (hd (tl exp)))) (hd (tl (tl exp))) env))
  (ite (is-kons exp)
       (let ((a (eval (- fuel 1) env (hd (tl exp))))
             (d (eval (- fuel 1) env (hd (tl (tl exp))))))
         (ite (and ((_ is just) a) ((_ is just) d)
                   ((_ is sexpr) (just-v a))
                   ((_ is sexpr) (just-v d))
                   )
              (just (sexpr (cons (sexpr-val (just-v a))
                                 (sexpr-val (just-v d)))))
              (as nothing (Maybe Sval))))
  (ite (is-app exp)
       (let ((f (eval (- fuel 1) env (hd exp)))
             (a (eval (- fuel 1) env (hd (tl exp)))))
         (ite (and ((_ is just) f)
                   ((_ is just) a)
                   ((_ is sclo) (just-v f)))
             (eval
              (- fuel 1)
              (ext-env (sclo-id (just-v f))
                       (just-v a)
                       (sclo-env (just-v f)))
              (sclo-body (just-v f)))
             (as nothing (Maybe Sval))))
       (as nothing (Maybe Sval))
       )))))
  (as nothing (Maybe Sval))))

(declare-const ma (Maybe Sval))
(declare-const a Sval)
(declare-const e Senv)
(declare-const t Sexpr)
(declare-const id Sexpr)

;; (assert (= ma (eval 50 empty-env
;;                       (cons (ssym squote) (cons nil nil))
;;                     )))
(assert (= id

           
                                           (cons
                      (ssym slambda) ; A
                      (cons
                       (cons (ssym sb) nil) ; B
                       (cons
                        ;;(cons (ssym squote) (cons (ssym sc) nil))
                        (ssym sb) ; C
                        nil))) ; OP
           ))


(assert (= (just (sexpr t)) (eval 7 empty-env t)))

;;(assert (= ma (eval 500 empty-env (cons (cons id (cons id nil)) (cons id nil)))))

;;(assert (= ma (eval 500 empty-env (cons (cons id (cons id nil)) (cons id nil)))))

;; (assert (= t (cons 
;;               (cons
;;                (ssym slambda) ; A
;;                (cons
;;                 (cons (ssym sa) nil) ; B
;;                 (cons
;;                  (ssym sa) ; C
;;                  nil))) ; OP
;;               (cons
;;                nil ; OP
;;                nil)
;;               )))

;;(assert (= ma (eval 50 empty-env t)))

;; (assert
;;  (= ma
;;     (eval 100 empty-env
;;           (cons (ssym scons)
;;                 (cons
;;                  (cons (ssym squote) (cons (ssym sa) nil))
;;                  (cons
;;                   (cons (ssym squote) (cons nil nil))
;;                   nil))))))


(check-sat)
(get-model)

;;((lambda (sa) sa) (cons nil nil))

;; (assert (= a (env-lookup empty-env sa)))
;; (check-sat)
;; (get-model)

;; (assert (not (= a (as nothing (Maybe Sval)))))
;; (check-sat)
;; (get-model)


;; (declare-const b (Maybe Sval))

;; (assert (= b (env-lookup (ext-env sa (sexpr nil) empty-env) sa)))
;; (check-sat)
;; (get-model)

;; (assert (not (= b (just (sexpr nil)))))
;; (check-sat)
;; (get-model)


;; (declare-const c Senv)
;; (declare-const d Ssym)

;; (assert (= (just (sexpr nil)) (env-lookup c d)))
;; (check-sat)
;; (get-model)


;; (assert (and ((_ is ext-env) c) (not (= (senv-id c) slambda))))
;; (check-sat)
;; (get-model)

;; (assert (= d slambda))
;; (check-sat)
;; (get-model)
