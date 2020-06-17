; First frame rule set we cannot change order so have to edit P to match Γ
; Everything else we can do any order aslong as the Q' we create is a subset of Q
; So what we want to do is calculate Q and use weakening and frame to add everything that is not in the
; current action into Q'. Where Q' is the preconditions of the action composed + every item in Q that is not in Q'.
;consider the weakening case

;Minor hiccup sometimes the function lambda z -> z is not needed and refl is asked for instead
;Need to check why this is. It is probably because weakening is weird. Weakening should be adjusted to give refl instead

;{- first construction
;
;                       (((frame + (onTable a) (λ z → z) (λ z → z)
;                       (frame + (clear a) (λ z → z) (λ z → z)
;                       (frame +  (onTable c) (λ z → z) (λ z → z)
;                       (frame + (clear c) (λ z → z) (λ z → z) applyAction))))))
;
;-}

;{- we get given p -}
;{- we need to re-oreder p so that its preconditions are at the end for the given action -}
;{- then we need to frame all p that is not a precondition and follow that with applyAction-}

;{- second construction
;          ((frame + (onTable a) (λ z → z) (λ z → z)
;          (frame + (clear a) (λ z → z) (λ z → z)
;          (frame + (onTable c) (λ z → z) (λ z → z)
;          (weakening - handEmpty (λ z → z) refl
;          (frame - (onTable b) (λ z → z) (λ z → z)
;          (frame + (clear b) (λ z → z) (λ z → z) applyAction))))))))
;-}
;we get our new P by applying the effects from the previous action.

;We then check the P' of our new action and then frame all items in P
;that are not in P' whilst checking that the action we are framing is
;not already in Q. If it is in Q then we use weakening instead.

;Then we  just keep repeating the above

;Lisp code we need
;1. The ability to create a world list
;2. The pre and post conditions of actions returnable as functions
;3. The ability to apply post conditions to a world
;4. A function to generate the frame additions
;(optional: before framing a function to compare the p' of an action
;to the P we are trying to prove so that any polarity differences can be seen
;and an error message thrown.)


;We have to check that for every item we frame in it is not in the right hand side of the action used in Q'
;if it is in the right hand side of the action used in Q' then we have to use weakening

; Γ₁ (pickup_from_table x) = (+ , handEmpty) ∷ (+ , onTable x) ∷ (+ , clear x) ∷ [] , (+ , clear x) ∷ (- , handEmpty) ∷ (- , onTable x) ∷ (+ , holding x) ∷ []
;Γ₁ (putdown_on_table x) = (+ , holding x) ∷ [] , (- , holding x) ∷ (+ , onTable x) ∷ (+ , handEmpty) ∷ []



;(print plan)

;(setq domainfile "logistics-domain.pddl")
;(setq problemfile "logistics-problem.pddl")

(load "domain_lisp")
(load "problem_lisp")


;(print predicates)
;(print actionList)
;(print context)

(with-open-file ( my-stream "context.lisp" :direction :output)
  (loop for c in context
    do (write-line c my-stream)))

(load "context")

;Generates the list used fos subtypes
(defun effectToQ (world preconditions postcon)
  (let ((effect postcon)
       (inEffect nil)
       (w world)
       (q nil))

    (loop for p in preconditions
       do (progn (setq inEffect nil)
        (loop for e in effect
          do (when (eq 'not (car e))
             (when (equal p (cadr e))
               (setq inEffect t))))
              (when (eq nil inEffect)
                (progn
                 (setq w (remove p w :test #'equal))
                 (setq effect (cons p effect))))))



     (loop for p in effect
       do (if (eq 'not (car p))
           (progn
               (setq w (remove (cadr p) w :test #'equal))
               (setq q (cons p q)))
           (progn (setq w (remove (cons 'not (list p)) w  :test #'equal))
              (setq q (cons p q)))))

  (setq q (reverse q))

  (append w q)
))

;Returns list of world with preconditions removed
(defun removePreconditions (world precon)
  (let ((w world)
        (l 0))

    (loop for p in precon
      do (progn
            (setq l (length w))
            (setq w (remove p w :test #'equal))
            (when (not (< (length w) l))
              (error (concatenate 'string "precondition: " (string (car p)) " " (paramToString (cdr p)) " not satisfied.")))
            )
          )
    w
))

(defun removeNot (lst)
  (let ((ls nil))

  (loop for l in lst
    do (if (eq 'not (car l))
        (setq ls (cons (cadr l) ls))
        (setq ls (cons l ls))))

  (reverse ls)
))

(defun getPreSub (world postcon)
  (let ((st ())
        (post (removeNot postcon)))
  ;(print post)

  (loop for w in world

    do (progn

          (if (eq 'not (car w))
            (when (eq nil (find (cadr w) post :test #'equal))
                (setq st (cons w st)))


            (when (eq nil (find w post :test #'equal))
              (setq st (cons w st)))
    )))

    (reverse st)
))

(defun generateProofRules (world postcon)
  (let ((st "(")
        (end ")")
        (post (removeNot postcon)))
  ;(print post)

  (loop for w in world

    do (progn

          (if (eq 'not (car w))
            (when (eq nil (find (cadr w) post :test #'equal))
                ;(if (eq nil (cdadr w))
                ;  (setq st (concatenate 'string st "(weakening - (" (stringconvert (string (caadr w))) ") (λ z → z) refl "))
                ;  (setq st (concatenate 'string st "(weakening - (" (stringconvert (string (caadr w))) (paramToString (cdadr w)) ") (λ z → z) refl ")))
                (progn
                  (setq end (concatenate 'string end ")"))
                (if (eq nil (cdadr w))
                  (setq st (concatenate 'string st "(frame - (" (stringconvert (string (caadr w))) ") (λ z → z) (λ z → z) "))
                  (setq st (concatenate 'string st "(frame - (" (stringconvert (string (caadr w))) (paramToString (cdadr w)) ") (λ z → z) (λ z → z) ")))))

            (when (eq nil (find w post :test #'equal))
              ;(if (eq nil (cdr w))
              ;  (setq st (concatenate 'string st "(weakening + (" (stringconvert (string (car w))) ") (λ z → z) refl "))
              ;  (setq st (concatenate 'string st "(weakening + (" (stringconvert (string (car w))) (paramToString (cdr w)) ") (λ z → z) refl ")))
              (progn
                (setq end (concatenate 'string end ")"))
              (if (eq nil (cdr w))
                (setq st (concatenate 'string st "(frame + (" (stringconvert (string (car w))) ") (λ z → z) (λ z → z) "))
                (setq st (concatenate 'string st "(frame + (" (stringconvert (string (car w))) (paramToString (cdr w)) ") (λ z → z) (λ z → z) "))))))

    ))

    (concatenate 'string st "(applyAction tt tt)" end)
))

(defun applyPostConditions (world postcon)
  (let ((w world))

  (loop for p in postcon
    do (if (eq 'not (car p))
          (progn
            (setq w (remove (cadr p) w :test #'equal))
            (setq w (cons p w)))
          (progn (setq w (remove (cons 'not (list p)) w  :test #'equal))
                 (setq w (cons p w)))))
  w
))


(defun planToString (plan)
  (let ((st "")
         (name "")
         (arg ""))



  (setq name (stringconvert (string (caar plan))))
  (loop for c in (cdar plan)
    do (setq arg (concatenate 'string arg " " (stringconvert (string (cadr c))))))

  (setq st (concatenate 'string "(join " "(act (" name " " arg "))"))

  (loop for p in (cdr plan)
    do (progn (setq name (stringconvert (string (car p))))
              (setq arg "")
              (loop for c in (cdr p)
                do (setq arg (concatenate 'string arg " " (stringconvert (string (cadr c))))))
              (setq st (concatenate 'string "(join " st " (act (" name " " arg")))"))
  ))

  (concatenate 'string "plan = " st " halt)")
))

;(defun paramToString(param)
;  (let ((st ""))
;
;  (loop for p in param
;    do (setq st (concatenate 'string st " " (stringconvert (string p))))
;  )
;  st
;))

(defun solve ()
  (let ((res nil)
        (w init))

  (setq preSub nil)
  ;(setq preSub2 nil)
  (setq postSub nil)


  (loop for p in plan
    do (progn

      (princ "action ")
      (print p)
      (print w)
      ;(print (car (eval p)))
      ;(print (removePreconditions w (car (eval p))))

      ;(setq preSub (cons (conditionConvert (append (removePreconditions w (car (eval p))) (car (eval p)))) preSub))
      (setq postSub (cons (conditionConvert (effectToQ w (car (eval p)) (cdr (eval p)))) postSub))

      (setq preSub (cons (conditionConvert
          (append (getPreSub (removePreconditions w (car (eval p))) (cdr (eval p))) (car (eval p)))) preSub))


      ;(print "precondition")
      ;(print (conditionConvert (append (removePreconditions w (car (eval p))) (car (eval p)))))
      ;(print "postcondition")
      ;(print (conditionConvert (effectToQ w (car (eval p)) (cdr (eval p)))) )


      ;(setq preSub (cons (getPreSub
      ;        (append (removePreconditions w (car (eval p))) (car (eval p)))
      ;        (cdr (eval p))) preSub))

      (setq res
        (cons (generateProofRules
                (removePreconditions w (car (eval p)))
                (cdr (eval p)))
              res))

      (setq w (applyPostConditions w (cdr (eval p))))


  ))

  ;(print preSub)
  ;(print preSub2)

  res
))

;(with-open-file ( my-stream "res.txt" :direction :output)
(with-open-file ( my-stream (concatenate 'string outputfile ".agda") :direction :output :if-exists :append )
  (setq frameAxioms (reverse (solve)))
  (setq sp8 "        ")

  (setq p (nth (- (length preSub) 1) preSub))
  ;(print p)

  (write-line "P' : State" my-stream)
  (write-line (concatenate 'string "P' = " p) my-stream)
  (write-line "" my-stream)

  (write-line "plan : f" my-stream)
  (write-line (planToString plan) my-stream)
  (write-line "" my-stream)

  (write-line "Derivation : Γ₁ , P ↝ Q ¦ plan" my-stream)
  (write-line "Derivation = weakening P (from-yes (decSub P' P)) tt (halt Q tt" my-stream)

  (write-line (concatenate 'string sp8 "(from-yes (decSub Q (" (car postSub) ")))") my-stream)

  (setq i 0)
  (loop for p in (cdr postSub)
      do (progn
          (write-line (concatenate 'string sp8 "(composition (from-yes (decSub (" (nth i preSub) ")") my-stream)
          (write-line (concatenate 'string sp8 "(" p ")))") my-stream)
          (incf i)
        )
  )

  (write-line (concatenate 'string sp8 (car frameAxioms)) my-stream)

  (loop for f in (cdr frameAxioms)
    do (write-line (concatenate 'string sp8 f ")") my-stream))

  (write-line (concatenate 'string sp8 ")") my-stream)


)



  ;(loop for f in (reverse (solve))
  ;  do (write-line s my-stream)))


; For subting x <: y
; y is generated by the P (remove preconditions) appended by the postconditions (not effects)
; x is generated by the frame axiom + the preconditions of the next action
;


;(print (removePreconditions init (car (eval (car plan)))))
;(print (removePreconditions init '((onTable a z))))

;(print (generateProofRules
;        (removePreconditions init (car (eval (car plan))))
;        (cdr (eval (car plan)))))

;(print (applyPostConditions init (cdr (eval (car plan)))))
