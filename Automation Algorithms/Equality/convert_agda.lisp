;;Warning. I am using case sensitive lisp for more pretty parsing.

;(setq domainfile "logistics-domain.pddl")
;(setq problemfile "logistics-problem.pddl")
;(setq outputfile "test")


(defun stringconvert (st)
  (let ((s st))

  (when (eq #\? (char s 0))
    (setq s (subseq s 1)))

  (if (upper-case-p (char s 0))
      (string-downcase s)
      s)
))

;(setq domainfile "mprime-domain.pddl")
;(setq problemfile "mprime-problem.pddl")
;(setq outputfile "mprime")


(load "domain_agda")
(load "problem_agda")

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
  (write-line "open import Relation.Binary.PropositionalEquality" my-stream)
  (write-line "open import Relation.Binary" my-stream)
  (write-line "open import Data.List" my-stream)
  (write-line "open import Data.List.Relation.Unary.Any" my-stream)
  (write-line "open import Relation.Nullary using (yes; no; Dec)" my-stream)
  (write-line "open import Level" my-stream)
  (write-line "open import Tactic.Deriving.Eq" my-stream)

  ;constants
  (write-line "" my-stream)
  (write-line "data C : Set where" my-stream)
  (write-line objList my-stream)
  (write-line "-- EqC : Eq C" my-stream)
  (write-line "unquoteDecl EqC = deriveEq EqC (quote C)" my-stream)

  ;predicates
  (write-line "" my-stream)
  (write-line "data R : Set where" my-stream)
  (loop for p in predicates
    do (write-line p my-stream))
  (write-line "-- EqR : Eq R" my-stream)
  (write-line "unquoteDecl EqR = deriveEq EqR (quote R)" my-stream)

  ;actions
  (write-line "" my-stream)
  (write-line "data Action : Set where" my-stream)
  (loop for a in actionList
    do (write-line a my-stream))
  (write-line "-- EqAction : Eq Action" my-stream)
  (write-line "unquoteDecl EqAction = deriveEq EqAction (quote Action)" my-stream)

  ;import
  (write-line "" my-stream)
  (write-line "open import Mangle using (mangle)" my-stream)

  ;decidablity proofs
  (write-line "" my-stream)
  (write-line "isDecidable : IsDecEquivalence {zero} {zero} (_≡_ {A = R})" my-stream)
  (write-line "isDecidable = record { isEquivalence = record {" my-stream)
  (write-line "  refl = λ {x} → refl ;" my-stream)
  (write-line "  sym = λ x → sym x ;" my-stream)
  (write-line "  trans = trans } ;" my-stream)
  (write-line " _≟_ = mangle  }" my-stream)


  (write-line "" my-stream)
  (write-line "isDEC : IsDecEquivalence {zero} {zero} (_≡_ {A = C})" my-stream)
  (write-line "isDEC = record { isEquivalence = record {" my-stream)
  (write-line "  refl = λ {x} → refl ;" my-stream)
  (write-line "  sym = λ x → sym x ;" my-stream)
  (write-line "  trans = trans } ;" my-stream)
  (write-line "  _≟_ = mangle  }" my-stream)

  (write-line "" my-stream)
  (write-line "isDECA : IsDecEquivalence {zero} {zero} (_≡_ {A = Action})" my-stream)
  (write-line "isDECA = record { isEquivalence = record {" my-stream)
  (write-line "  refl = λ {x} → refl ;" my-stream)
  (write-line "  sym = λ x → sym x ;" my-stream)
  (write-line "  trans = trans } ;" my-stream)
  (write-line "  _≟_ = mangle  }" my-stream)

  ;instantiate proof system
  (write-line "" my-stream)
  (write-line "open import sep_equality {Action} {R} {C} {isDecidable} {isDEC} {isDECA}" my-stream)

  (write-line "" my-stream)
  (write-line "open import Data.Product" my-stream)

  ;context
  (write-line "" my-stream)
  (write-line "Γ₁ : Γ" my-stream)
  (loop for g in context
    do  (write-line g my-stream))

  (write-line "" my-stream)
  (write-line "open Data.Product renaming (_,_ to _↝_)" my-stream)
  (write-line "" my-stream)

  ;Initial State
  (write-line "" my-stream)
  (write-line "P : State" my-stream)
  (write-line init my-stream)

  ;Goal State
  (write-line "" my-stream)
  (write-line "Q : State" my-stream)
  (write-line goal my-stream)

  ;more imports
  (write-line "" my-stream)
  (write-line "open import Relation.Nullary.Decidable" my-stream)
  (write-line "open import Data.Unit" my-stream)








  )
