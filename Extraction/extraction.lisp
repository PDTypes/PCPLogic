;;Warning. I am using case sensitive lisp for more pretty parsing.

(setq domainfile "satellite-domain.pddl")
(setq problemfile "satellite-problem.pddl")
(setq outputfile "run")


(defun stringconvert (st)
  (let ((s st))

  (when (eq #\? (char s 0))
    (setq s (subseq s 1)))

  (if (upper-case-p (char s 0))
      (string-downcase s)
      s)
))

(load "domain_extraction")
(load "problem_extraction")

(print objList)
(print init)
(print goal)
(print predicates)
(print actionList)
(print context)

;(setf (readtable-case *readtable*) :preserve)
;(SETQ help (READ))
;(SETF (READTABLE-CASE *READTABLE*) :INVERT)
;(print HELP)
;(exit)


;Potential problem with and on the goal still needs fixed

(with-open-file ( my-stream (concatenate 'string outputfile ".agda") :direction :output)
  ;module
  (write-line (concatenate 'string "module " outputfile " where") my-stream)

  ;imports
  (write-line "" my-stream)
  (write-line "open import satellite" my-stream)
  (write-line "open import Agda.Builtin.IO" my-stream)
  (write-line "open import Agda.Builtin.Unit" my-stream)
  (write-line "open import Agda.Builtin.String" my-stream)
  (write-line "open import Data.List hiding (_++_)" my-stream)
  (write-line "open import Data.String" my-stream)
  (write-line "" my-stream)

  (write-line "postulate" my-stream)
  (write-line "  putStrLn : String → IO ⊤" my-stream)
  (write-line "" my-stream)

  (write-line "{-# FOREIGN GHC import qualified Data.Text.IO as Text #-}" my-stream)
  (write-line "{-# COMPILE GHC putStrLn = Text.putStrLn #-}" my-stream)


  ;constants
  (write-line "" my-stream)
  (write-line "showC : C -> String" my-stream)
  (print objList)
  (loop for c in objList
    do (write-line (concatenate 'string "showC " c " = \"" c " \"") my-stream))

  (print predicates)
  (write-line "" my-stream)
  (write-line "showR : R -> String" my-stream)
  (loop for p in predicates
    do (progn
        (setq tstring "")
        (if (eq nil (cdr p))
          (write-line (concatenate 'string
                        "showR "
                        (stringconvert (string (car p)))
                        " = \""
                        (stringconvert (string (car p)))
                        " \"") my-stream)
          (progn
            (setq tstring (concatenate 'string
                            "showR ("
                             (stringconvert (string (car p)))))

            (loop for c in (cdr p)
               do (setq tstring (concatenate 'string tstring (convert c))))
            (setq tstring (concatenate 'string tstring
                             ") = \""
                             (stringconvert (string (car p)))
                             " \""))
            (loop for c in (cdr p)
              do (setq tstring (concatenate 'string tstring
                              " ++ showC"
                              (convert c))))
              (write-line tstring my-stream)))))

  (write-line "" my-stream)
  (write-line "showEval : List R -> String" my-stream)
  (write-line "showEval [] = \"emp\"" my-stream)
  (write-line "showEval (x ∷ xs) = showR x ++ \" * \" ++ (showEval xs)" my-stream)

  (write-line "" my-stream)
  (write-line "main : IO ⊤" my-stream)
  (write-line "main = putStrLn (showEval world-eval)" my-stream)










  )
