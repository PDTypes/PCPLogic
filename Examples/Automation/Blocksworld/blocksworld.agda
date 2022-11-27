module blocksworld where

open import Relation.Binary.PropositionalEquality
open import Relation.Binary
open import Data.List
open import Data.List.Relation.Unary.Any
open import Relation.Nullary using (yes; no; Dec)
open import Level
open import Tactic.Deriving.Eq

data C : Set where
 a b c d e f1 : C
-- EqC : Eq C
unquoteDecl EqC = deriveEq EqC (quote C)

data R : Set where
  clear : C → R
  on : C → C → R
  ontable : C → R
  holding : C → R
  handempty : R
-- EqR : Eq R
unquoteDecl EqR = deriveEq EqR (quote R)

data Action : Set where
  pickup_from_table : C → Action
  putdown_on_table : C → Action
  pickup_from_stack : C → C → Action
  putdown_on_stack : C → C → Action
-- EqAction : Eq Action
unquoteDecl EqAction = deriveEq EqAction (quote Action)

open import Mangle using (mangle)

isDecidable : IsDecEquivalence {zero} {zero} (_≡_ {A = R})
isDecidable = record { isEquivalence = record {
  refl = λ {x} → refl ;
  sym = λ x → sym x ;
  trans = trans } ;
 _≟_ = mangle  }

isDEC : IsDecEquivalence {zero} {zero} (_≡_ {A = C})
isDEC = record { isEquivalence = record {
  refl = λ {x} → refl ;
  sym = λ x → sym x ;
  trans = trans } ;
  _≟_ = mangle  }

isDECA : IsDecEquivalence {zero} {zero} (_≡_ {A = Action})
isDECA = record { isEquivalence = record {
  refl = λ {x} → refl ;
  sym = λ x → sym x ;
  trans = trans } ;
  _≟_ = mangle  }

open import PCPLogic_no_equality {Action} {R} {C} {isDecidable} {isDEC} {isDECA}

open import Data.Product

Γ₁ : Γ
Γ₁ (pickup_from_table x) = (+ , handempty) ∷ (+ , ontable x) ∷ (+ , clear x) ∷ [] , (+ , clear x) ∷ (- , handempty) ∷ (- , ontable x) ∷ (+ , holding x) ∷ []
Γ₁ (putdown_on_table x) = (+ , holding x) ∷ [] , (- , holding x) ∷ (+ , ontable x) ∷ (+ , handempty) ∷ []
Γ₁ (pickup_from_stack x y) = (+ , on x y) ∷ (+ , clear x) ∷ (+ , handempty) ∷ [] , (+ , clear x) ∷ (- , on x y) ∷ (- , handempty) ∷ (+ , holding x) ∷ (+ , clear y) ∷ []
Γ₁ (putdown_on_stack x y) = (+ , holding x) ∷ (+ , clear y) ∷ [] , (- , holding x) ∷ (- , clear y) ∷ (+ , on x y) ∷ (+ , handempty) ∷ []

open Data.Product renaming (_,_ to _↝_)


P : State
P = (+ ↝ (ontable a)) ∷ (+ ↝ (ontable b)) ∷ (+ ↝ (ontable c)) ∷ (+ ↝ (ontable d)) ∷ (+ ↝ (ontable e)) ∷ (+ ↝ (ontable f1)) ∷ (+ ↝ (clear a)) ∷ (+ ↝ (clear b)) ∷ (+ ↝ (clear c)) ∷ (+ ↝ (clear d)) ∷ (+ ↝ (clear e)) ∷ (+ ↝ (clear f1)) ∷ (+ ↝ (handempty)) ∷ []

Q : State
Q = (+ ↝ (on a b)) ∷ (+ ↝ (on b c)) ∷ (+ ↝ (on c d)) ∷ (+ ↝ (on d e)) ∷ (+ ↝ (on e f1)) ∷ []

open import Relation.Nullary.Decidable
open import Data.Unit
P' : State
P' = (+ , ontable a) ∷ (+ , ontable b) ∷ (+ , ontable c) ∷ (+ , ontable d) ∷ (+ , ontable f1) ∷ (+ , clear a) ∷ (+ , clear b) ∷ (+ , clear c) ∷ (+ , clear d) ∷ (+ , clear f1) ∷ (+ , handempty) ∷ (+ , ontable e) ∷ (+ , clear e) ∷ []

plan : f
plan = (join (join (join (join (join (join (join (join (join (join (act (pickup_from_table  e)) (act (putdown_on_stack  e f1))) (act (pickup_from_table  d))) (act (putdown_on_stack  d e))) (act (pickup_from_table  c))) (act (putdown_on_stack  c d))) (act (pickup_from_table  b))) (act (putdown_on_stack  b c))) (act (pickup_from_table  a))) (act (putdown_on_stack  a b))) halt)

Derivation : Γ₁ , P ↝ Q ¦ plan
Derivation = weakening P (from-yes (decSub P' P)) tt (halt Q tt
        (from-yes (decSub Q ((- , ontable a) ∷ (+ , on b c) ∷ (- , clear c) ∷ (- , holding b) ∷ (- , ontable b) ∷ (+ , on c d) ∷ (- , clear d) ∷ (- , holding c) ∷ (- , ontable c) ∷ (+ , on d e) ∷ (- , clear e) ∷ (- , holding d) ∷ (- , ontable d) ∷ (+ , on e f1) ∷ (- , clear f1) ∷ (- , holding e) ∷ (- , ontable e) ∷ (+ , ontable f1) ∷ (+ , clear a) ∷ (- , holding a) ∷ (- , clear b) ∷ (+ , on a b) ∷ (+ , handempty) ∷ [])))
        (composition (from-yes (decSub ((- , ontable a) ∷ (+ , on b c) ∷ (- , clear c) ∷ (- , holding b) ∷ (- , ontable b) ∷ (+ , on c d) ∷ (- , clear d) ∷ (- , holding c) ∷ (- , ontable c) ∷ (+ , on d e) ∷ (- , clear e) ∷ (- , holding d) ∷ (- , ontable d) ∷ (+ , on e f1) ∷ (- , clear f1) ∷ (- , holding e) ∷ (- , ontable e) ∷ (+ , ontable f1) ∷ (+ , clear a) ∷ (+ , holding a) ∷ (+ , clear b) ∷ [])
        ((+ , on b c) ∷ (- , clear c) ∷ (- , holding b) ∷ (- , ontable b) ∷ (+ , on c d) ∷ (- , clear d) ∷ (- , holding c) ∷ (- , ontable c) ∷ (+ , on d e) ∷ (- , clear e) ∷ (- , holding d) ∷ (- , ontable d) ∷ (+ , on e f1) ∷ (- , clear f1) ∷ (- , holding e) ∷ (- , ontable e) ∷ (+ , ontable f1) ∷ (+ , clear b) ∷ (+ , clear a) ∷ (- , handempty) ∷ (- , ontable a) ∷ (+ , holding a) ∷ [])))
        (composition (from-yes (decSub ((+ , on b c) ∷ (- , clear c) ∷ (- , holding b) ∷ (- , ontable b) ∷ (+ , on c d) ∷ (- , clear d) ∷ (- , holding c) ∷ (- , ontable c) ∷ (+ , on d e) ∷ (- , clear e) ∷ (- , holding d) ∷ (- , ontable d) ∷ (+ , on e f1) ∷ (- , clear f1) ∷ (- , holding e) ∷ (- , ontable e) ∷ (+ , ontable f1) ∷ (+ , clear b) ∷ (+ , handempty) ∷ (+ , ontable a) ∷ (+ , clear a) ∷ [])
        ((- , ontable b) ∷ (+ , on c d) ∷ (- , clear d) ∷ (- , holding c) ∷ (- , ontable c) ∷ (+ , on d e) ∷ (- , clear e) ∷ (- , holding d) ∷ (- , ontable d) ∷ (+ , on e f1) ∷ (- , clear f1) ∷ (- , holding e) ∷ (- , ontable e) ∷ (+ , ontable a) ∷ (+ , ontable f1) ∷ (+ , clear a) ∷ (+ , clear b) ∷ (- , holding b) ∷ (- , clear c) ∷ (+ , on b c) ∷ (+ , handempty) ∷ [])))
        (composition (from-yes (decSub ((- , ontable b) ∷ (+ , on c d) ∷ (- , clear d) ∷ (- , holding c) ∷ (- , ontable c) ∷ (+ , on d e) ∷ (- , clear e) ∷ (- , holding d) ∷ (- , ontable d) ∷ (+ , on e f1) ∷ (- , clear f1) ∷ (- , holding e) ∷ (- , ontable e) ∷ (+ , ontable a) ∷ (+ , ontable f1) ∷ (+ , clear a) ∷ (+ , clear b) ∷ (+ , holding b) ∷ (+ , clear c) ∷ [])
        ((+ , on c d) ∷ (- , clear d) ∷ (- , holding c) ∷ (- , ontable c) ∷ (+ , on d e) ∷ (- , clear e) ∷ (- , holding d) ∷ (- , ontable d) ∷ (+ , on e f1) ∷ (- , clear f1) ∷ (- , holding e) ∷ (- , ontable e) ∷ (+ , ontable a) ∷ (+ , ontable f1) ∷ (+ , clear a) ∷ (+ , clear c) ∷ (+ , clear b) ∷ (- , handempty) ∷ (- , ontable b) ∷ (+ , holding b) ∷ [])))
        (composition (from-yes (decSub ((+ , on c d) ∷ (- , clear d) ∷ (- , holding c) ∷ (- , ontable c) ∷ (+ , on d e) ∷ (- , clear e) ∷ (- , holding d) ∷ (- , ontable d) ∷ (+ , on e f1) ∷ (- , clear f1) ∷ (- , holding e) ∷ (- , ontable e) ∷ (+ , ontable a) ∷ (+ , ontable f1) ∷ (+ , clear a) ∷ (+ , clear c) ∷ (+ , handempty) ∷ (+ , ontable b) ∷ (+ , clear b) ∷ [])
        ((- , ontable c) ∷ (+ , on d e) ∷ (- , clear e) ∷ (- , holding d) ∷ (- , ontable d) ∷ (+ , on e f1) ∷ (- , clear f1) ∷ (- , holding e) ∷ (- , ontable e) ∷ (+ , ontable a) ∷ (+ , ontable b) ∷ (+ , ontable f1) ∷ (+ , clear a) ∷ (+ , clear b) ∷ (+ , clear c) ∷ (- , holding c) ∷ (- , clear d) ∷ (+ , on c d) ∷ (+ , handempty) ∷ [])))
        (composition (from-yes (decSub ((- , ontable c) ∷ (+ , on d e) ∷ (- , clear e) ∷ (- , holding d) ∷ (- , ontable d) ∷ (+ , on e f1) ∷ (- , clear f1) ∷ (- , holding e) ∷ (- , ontable e) ∷ (+ , ontable a) ∷ (+ , ontable b) ∷ (+ , ontable f1) ∷ (+ , clear a) ∷ (+ , clear b) ∷ (+ , clear c) ∷ (+ , holding c) ∷ (+ , clear d) ∷ [])
        ((+ , on d e) ∷ (- , clear e) ∷ (- , holding d) ∷ (- , ontable d) ∷ (+ , on e f1) ∷ (- , clear f1) ∷ (- , holding e) ∷ (- , ontable e) ∷ (+ , ontable a) ∷ (+ , ontable b) ∷ (+ , ontable f1) ∷ (+ , clear a) ∷ (+ , clear b) ∷ (+ , clear d) ∷ (+ , clear c) ∷ (- , handempty) ∷ (- , ontable c) ∷ (+ , holding c) ∷ [])))
        (composition (from-yes (decSub ((+ , on d e) ∷ (- , clear e) ∷ (- , holding d) ∷ (- , ontable d) ∷ (+ , on e f1) ∷ (- , clear f1) ∷ (- , holding e) ∷ (- , ontable e) ∷ (+ , ontable a) ∷ (+ , ontable b) ∷ (+ , ontable f1) ∷ (+ , clear a) ∷ (+ , clear b) ∷ (+ , clear d) ∷ (+ , handempty) ∷ (+ , ontable c) ∷ (+ , clear c) ∷ [])
        ((- , ontable d) ∷ (+ , on e f1) ∷ (- , clear f1) ∷ (- , holding e) ∷ (- , ontable e) ∷ (+ , ontable a) ∷ (+ , ontable b) ∷ (+ , ontable c) ∷ (+ , ontable f1) ∷ (+ , clear a) ∷ (+ , clear b) ∷ (+ , clear c) ∷ (+ , clear d) ∷ (- , holding d) ∷ (- , clear e) ∷ (+ , on d e) ∷ (+ , handempty) ∷ [])))
        (composition (from-yes (decSub ((- , ontable d) ∷ (+ , on e f1) ∷ (- , clear f1) ∷ (- , holding e) ∷ (- , ontable e) ∷ (+ , ontable a) ∷ (+ , ontable b) ∷ (+ , ontable c) ∷ (+ , ontable f1) ∷ (+ , clear a) ∷ (+ , clear b) ∷ (+ , clear c) ∷ (+ , clear d) ∷ (+ , holding d) ∷ (+ , clear e) ∷ [])
        ((+ , on e f1) ∷ (- , clear f1) ∷ (- , holding e) ∷ (- , ontable e) ∷ (+ , ontable a) ∷ (+ , ontable b) ∷ (+ , ontable c) ∷ (+ , ontable f1) ∷ (+ , clear a) ∷ (+ , clear b) ∷ (+ , clear c) ∷ (+ , clear e) ∷ (+ , clear d) ∷ (- , handempty) ∷ (- , ontable d) ∷ (+ , holding d) ∷ [])))
        (composition (from-yes (decSub ((+ , on e f1) ∷ (- , clear f1) ∷ (- , holding e) ∷ (- , ontable e) ∷ (+ , ontable a) ∷ (+ , ontable b) ∷ (+ , ontable c) ∷ (+ , ontable f1) ∷ (+ , clear a) ∷ (+ , clear b) ∷ (+ , clear c) ∷ (+ , clear e) ∷ (+ , handempty) ∷ (+ , ontable d) ∷ (+ , clear d) ∷ [])
        ((- , ontable e) ∷ (+ , ontable a) ∷ (+ , ontable b) ∷ (+ , ontable c) ∷ (+ , ontable d) ∷ (+ , ontable f1) ∷ (+ , clear a) ∷ (+ , clear b) ∷ (+ , clear c) ∷ (+ , clear d) ∷ (+ , clear e) ∷ (- , holding e) ∷ (- , clear f1) ∷ (+ , on e f1) ∷ (+ , handempty) ∷ [])))
        (composition (from-yes (decSub ((- , ontable e) ∷ (+ , ontable a) ∷ (+ , ontable b) ∷ (+ , ontable c) ∷ (+ , ontable d) ∷ (+ , ontable f1) ∷ (+ , clear a) ∷ (+ , clear b) ∷ (+ , clear c) ∷ (+ , clear d) ∷ (+ , clear e) ∷ (+ , holding e) ∷ (+ , clear f1) ∷ [])
        ((+ , ontable a) ∷ (+ , ontable b) ∷ (+ , ontable c) ∷ (+ , ontable d) ∷ (+ , ontable f1) ∷ (+ , clear a) ∷ (+ , clear b) ∷ (+ , clear c) ∷ (+ , clear d) ∷ (+ , clear f1) ∷ (+ , clear e) ∷ (- , handempty) ∷ (- , ontable e) ∷ (+ , holding e) ∷ [])))
        ((frame + (ontable a) (λ z → z) (λ z → z) (frame + (ontable b) (λ z → z) (λ z → z) (frame + (ontable c) (λ z → z) (λ z → z) (frame + (ontable d) (λ z → z) (λ z → z) (frame + (ontable f1) (λ z → z) (λ z → z) (frame + (clear a) (λ z → z) (λ z → z) (frame + (clear b) (λ z → z) (λ z → z) (frame + (clear c) (λ z → z) (λ z → z) (frame + (clear d) (λ z → z) (λ z → z) (frame + (clear f1) (λ z → z) (λ z → z) (applyAction tt tt))))))))))))
        ((frame - (ontable e) (λ z → z) (λ z → z) (frame + (ontable a) (λ z → z) (λ z → z) (frame + (ontable b) (λ z → z) (λ z → z) (frame + (ontable c) (λ z → z) (λ z → z) (frame + (ontable d) (λ z → z) (λ z → z) (frame + (ontable f1) (λ z → z) (λ z → z) (frame + (clear a) (λ z → z) (λ z → z) (frame + (clear b) (λ z → z) (λ z → z) (frame + (clear c) (λ z → z) (λ z → z) (frame + (clear d) (λ z → z) (λ z → z) (frame + (clear e) (λ z → z) (λ z → z) (applyAction tt tt))))))))))))))
        ((frame + (on e f1) (λ z → z) (λ z → z) (frame - (clear f1) (λ z → z) (λ z → z) (frame - (holding e) (λ z → z) (λ z → z) (frame - (ontable e) (λ z → z) (λ z → z) (frame + (ontable a) (λ z → z) (λ z → z) (frame + (ontable b) (λ z → z) (λ z → z) (frame + (ontable c) (λ z → z) (λ z → z) (frame + (ontable f1) (λ z → z) (λ z → z) (frame + (clear a) (λ z → z) (λ z → z) (frame + (clear b) (λ z → z) (λ z → z) (frame + (clear c) (λ z → z) (λ z → z) (frame + (clear e) (λ z → z) (λ z → z) (applyAction tt tt)))))))))))))))
        ((frame - (ontable d) (λ z → z) (λ z → z) (frame + (on e f1) (λ z → z) (λ z → z) (frame - (clear f1) (λ z → z) (λ z → z) (frame - (holding e) (λ z → z) (λ z → z) (frame - (ontable e) (λ z → z) (λ z → z) (frame + (ontable a) (λ z → z) (λ z → z) (frame + (ontable b) (λ z → z) (λ z → z) (frame + (ontable c) (λ z → z) (λ z → z) (frame + (ontable f1) (λ z → z) (λ z → z) (frame + (clear a) (λ z → z) (λ z → z) (frame + (clear b) (λ z → z) (λ z → z) (frame + (clear c) (λ z → z) (λ z → z) (frame + (clear d) (λ z → z) (λ z → z) (applyAction tt tt))))))))))))))))
        ((frame + (on d e) (λ z → z) (λ z → z) (frame - (clear e) (λ z → z) (λ z → z) (frame - (holding d) (λ z → z) (λ z → z) (frame - (ontable d) (λ z → z) (λ z → z) (frame + (on e f1) (λ z → z) (λ z → z) (frame - (clear f1) (λ z → z) (λ z → z) (frame - (holding e) (λ z → z) (λ z → z) (frame - (ontable e) (λ z → z) (λ z → z) (frame + (ontable a) (λ z → z) (λ z → z) (frame + (ontable b) (λ z → z) (λ z → z) (frame + (ontable f1) (λ z → z) (λ z → z) (frame + (clear a) (λ z → z) (λ z → z) (frame + (clear b) (λ z → z) (λ z → z) (frame + (clear d) (λ z → z) (λ z → z) (applyAction tt tt)))))))))))))))))
        ((frame - (ontable c) (λ z → z) (λ z → z) (frame + (on d e) (λ z → z) (λ z → z) (frame - (clear e) (λ z → z) (λ z → z) (frame - (holding d) (λ z → z) (λ z → z) (frame - (ontable d) (λ z → z) (λ z → z) (frame + (on e f1) (λ z → z) (λ z → z) (frame - (clear f1) (λ z → z) (λ z → z) (frame - (holding e) (λ z → z) (λ z → z) (frame - (ontable e) (λ z → z) (λ z → z) (frame + (ontable a) (λ z → z) (λ z → z) (frame + (ontable b) (λ z → z) (λ z → z) (frame + (ontable f1) (λ z → z) (λ z → z) (frame + (clear a) (λ z → z) (λ z → z) (frame + (clear b) (λ z → z) (λ z → z) (frame + (clear c) (λ z → z) (λ z → z) (applyAction tt tt))))))))))))))))))
        ((frame + (on c d) (λ z → z) (λ z → z) (frame - (clear d) (λ z → z) (λ z → z) (frame - (holding c) (λ z → z) (λ z → z) (frame - (ontable c) (λ z → z) (λ z → z) (frame + (on d e) (λ z → z) (λ z → z) (frame - (clear e) (λ z → z) (λ z → z) (frame - (holding d) (λ z → z) (λ z → z) (frame - (ontable d) (λ z → z) (λ z → z) (frame + (on e f1) (λ z → z) (λ z → z) (frame - (clear f1) (λ z → z) (λ z → z) (frame - (holding e) (λ z → z) (λ z → z) (frame - (ontable e) (λ z → z) (λ z → z) (frame + (ontable a) (λ z → z) (λ z → z) (frame + (ontable f1) (λ z → z) (λ z → z) (frame + (clear a) (λ z → z) (λ z → z) (frame + (clear c) (λ z → z) (λ z → z) (applyAction tt tt)))))))))))))))))))
        ((frame - (ontable b) (λ z → z) (λ z → z) (frame + (on c d) (λ z → z) (λ z → z) (frame - (clear d) (λ z → z) (λ z → z) (frame - (holding c) (λ z → z) (λ z → z) (frame - (ontable c) (λ z → z) (λ z → z) (frame + (on d e) (λ z → z) (λ z → z) (frame - (clear e) (λ z → z) (λ z → z) (frame - (holding d) (λ z → z) (λ z → z) (frame - (ontable d) (λ z → z) (λ z → z) (frame + (on e f1) (λ z → z) (λ z → z) (frame - (clear f1) (λ z → z) (λ z → z) (frame - (holding e) (λ z → z) (λ z → z) (frame - (ontable e) (λ z → z) (λ z → z) (frame + (ontable a) (λ z → z) (λ z → z) (frame + (ontable f1) (λ z → z) (λ z → z) (frame + (clear a) (λ z → z) (λ z → z) (frame + (clear b) (λ z → z) (λ z → z) (applyAction tt tt))))))))))))))))))))
        ((frame + (on b c) (λ z → z) (λ z → z) (frame - (clear c) (λ z → z) (λ z → z) (frame - (holding b) (λ z → z) (λ z → z) (frame - (ontable b) (λ z → z) (λ z → z) (frame + (on c d) (λ z → z) (λ z → z) (frame - (clear d) (λ z → z) (λ z → z) (frame - (holding c) (λ z → z) (λ z → z) (frame - (ontable c) (λ z → z) (λ z → z) (frame + (on d e) (λ z → z) (λ z → z) (frame - (clear e) (λ z → z) (λ z → z) (frame - (holding d) (λ z → z) (λ z → z) (frame - (ontable d) (λ z → z) (λ z → z) (frame + (on e f1) (λ z → z) (λ z → z) (frame - (clear f1) (λ z → z) (λ z → z) (frame - (holding e) (λ z → z) (λ z → z) (frame - (ontable e) (λ z → z) (λ z → z) (frame + (ontable f1) (λ z → z) (λ z → z) (frame + (clear b) (λ z → z) (λ z → z) (applyAction tt tt)))))))))))))))))))))
        ((frame - (ontable a) (λ z → z) (λ z → z) (frame + (on b c) (λ z → z) (λ z → z) (frame - (clear c) (λ z → z) (λ z → z) (frame - (holding b) (λ z → z) (λ z → z) (frame - (ontable b) (λ z → z) (λ z → z) (frame + (on c d) (λ z → z) (λ z → z) (frame - (clear d) (λ z → z) (λ z → z) (frame - (holding c) (λ z → z) (λ z → z) (frame - (ontable c) (λ z → z) (λ z → z) (frame + (on d e) (λ z → z) (λ z → z) (frame - (clear e) (λ z → z) (λ z → z) (frame - (holding d) (λ z → z) (λ z → z) (frame - (ontable d) (λ z → z) (λ z → z) (frame + (on e f1) (λ z → z) (λ z → z) (frame - (clear f1) (λ z → z) (λ z → z) (frame - (holding e) (λ z → z) (λ z → z) (frame - (ontable e) (λ z → z) (λ z → z) (frame + (ontable f1) (λ z → z) (λ z → z) (frame + (clear a) (λ z → z) (λ z → z) (applyAction tt tt))))))))))))))))))))))
        )
