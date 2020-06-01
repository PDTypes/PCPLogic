;;Domain Parsing

;(setf (readtable-case *readtable*) :invert)

(with-open-file (my-stream domainfile :direction :input)
	(setq input (read my-stream)))

;watch out for ordering
(setq context ())
(setq actions ())

(defun parseDom (in)
  (cond
   ((eq nil (car in)) (print "done"))
   ((eq 'define (car in)) (progn (print "define") (parseDom (cdr in))))
   ((eq :predicates (caar in)) (progn (print "predicates") (setq predicates (predicateHandler (cdr (car in)) "R")) (parseDom (cdr in))))
   ((eq :action (caar in)) (progn (print "action")
                                  (actionParser (cadar in) (cddar in))
                                  (parseDom (cdr in))))
   (t (parseDom (cdr in)))
  ))

(defun predicateConverHelper (varNum letter)
	(let ((st ""))

		(loop repeat varNum
			do (setq st (concatenate 'string st "C → "))
			)

		(concatenate 'string st letter)
))

(defun predicateConvert (preds letter)
	(let ((st ()))

	(loop for p in preds
		do (setq st (cons (concatenate 'string "  " (stringconvert (string (car p))) " : " (predicateConverHelper (cdr p) letter)) st))
	)

	(reverse st)
))


(defun predicateHandler (pred letter)
  (let ((preds ()))

  (loop for p in pred
	     do (setq preds (cons (cons (car p) (length (cdr p))) preds)))

	(predicateConvert preds letter)
))

;Γ₁ : Γ
;Γ₁ (pickupFromTable x) = (+ , onTable x) ∷ (+ , clear x) ∷ (+ , handEmpty) ∷ [] ,
;                                (- , handEmpty) ∷ (- , onTable x) ∷ (+ , holding x) ∷ (+ , clear x) ∷ []
;Γ₁ (putdownOnStack x y) = (+ , clear y) ∷ (+ , holding x) ∷ [] ,
;                                     (- , holding x) ∷ (- , clear y) ∷ (+ , on x y) ∷ (+ , handEmpty) ∷ []

(defun actionParser(actName act)
  (let ((parameters ())
        (preconditions ())
        (effect ())
        (inEffect nil))

  (labels ((aP (in)
        (cond
          ((eq nil (car in)) (print "done"))
          ((eq :parameters (car in)) (progn (print "parameters") (setq parameters (cadr in)) (aP (cdr in))))
          ((eq :precondition (car in)) (progn (print "preconditions")
							(if (eq 'and (caadr in))
								(setq preconditions (cdadr in))
								(setq effect (cdr in)))
								(aP (cdr in))))
          ((eq :effect (car in)) (progn (print "effect")
							(if (eq 'and (caadr in))
								(setq effect (cdadr in))
								(setq effect (cdr in)))
							(aP (cdr in))))
          (t (aP (cdr in))))))
  (aP act)

	(print preconditions)
	(print effect)

  (print "start")

  ; We don't actually use effects but post state
  ; therefore we need to add all preconditions in p to effect that are not
  ; already mentioned in effect

	;this is super naive and does not take into account parameters
	;also this is a problem because it assumes that all preconditions
	;cannot contain a not which is a problem for sure

  (loop for p in preconditions
     do (progn (setq inEffect nil)
			 (loop for e in effect
         do (when (eq' not (car e))
				 		;(progn
						;	(print p)
						;	(print (cadr e))
						;	(print (equal p (cadr e)))
            (when (equal p (cadr e)) ;naive fix
              (setq inEffect t)))) ;)
              (when (eq nil inEffect)
                (setq effect (cons p effect)))))

	(print effect)

  (actionHandler actName parameters preconditions effect)
)))


(defun paramToString(param)
  (let ((st ""))

  (loop for p in param
    do (setq st (concatenate 'string st " " (stringconvert (string p))))
  )
  st
))

(defun conditionConvert (conditions)
  (let ((st ""))

  (loop for c in conditions
    do (if (eq 'not (car c))
          ;(progn (print "not") (print (caadr c)) (print (cdadr c)))
          (if (eq nil (cdadr c))
            (setq st (concatenate 'string st "(- , " (stringconvert (string (caadr c))) ") ∷ "))
            (setq st (concatenate 'string st "(- , " (stringconvert (string (caadr c))) (paramToString (cdadr c)) ") ∷ ")))
          (if (eq nil (cdr c))
            (setq st (concatenate 'string st "(+ , " (stringconvert (string (car c))) ") ∷ "))
            (setq st (concatenate 'string st "(+ , " (stringconvert (string (car c))) (paramToString (cdr c)) ") ∷ "))))
  )

  (concatenate 'string st "[]")
))

(defun actionHandler(actName param precon effect)
  (let ((start (concatenate 'string "Γ₁ (" (stringconvert (string actName)) (paramToString param) ") = "))
        (pre (conditionConvert precon))
        (eff (conditionConvert effect)))

  (setq actions (cons (cons actName param) actions))
  (setq context (cons (concatenate 'string start pre " , " eff) context))

))

(parseDom input)

;(print predicates)
(setq actionList (predicateHandler actions "Action"))
(setq context (reverse context)) ;to match lisp file
