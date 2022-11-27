-- Alasdair Hill
-- This file defines Planning languages as types, plans as prrof terms approach to PDDL

open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Level

--------------------------------------------------------
--  Definition of formulae, possible world semantics, actions, plans

--
-- The following module declarartion allows to develop the file parametrised on an abstract set R of predicates
-- an an abstract set A of declared actions. The former must have decidable equivalence.

module PCPLogic_no_equality {Action : Set} {R : Set} {C : Set} {isDE : IsDecEquivalence {A = R} (_≡_) }
                                              {isDEC : IsDecEquivalence {A = C} (_≡_) }
                                              {isDECA : IsDecEquivalence {A = Action} (_≡_) }where

-- R is a predicate

open import Agda.Builtin.Nat hiding (_*_ ; _+_ ; _-_; zero)
open import Data.Vec hiding (_++_; remove)
open import Data.List hiding (any)
open import Data.Product


--This data type describes a plan which is a non-empty sequence of Actions
data f : Set where
  halt : f
  act  : Action -> f
  join : f -> f -> f
--  _||_ : Action -> f -> f -- this is for concurrent actions which we currently do not use
--infixl 4 _||_


----------------------------------------------------------------------------------------------

-- Old Implementation

data Form : Set where
  _∧_ : Form → Form → Form
  ¬_ : R  → Form
  atom : R → Form
infixl 4 _∧_
infixl 5 ¬_

---------------------------------------------------------
-- Figure 4. Possible worlds
--


World : Set
World = List R

-- Polarity
data Polarity : Set where
  + - : Polarity

-- Negation of polarities
neg : Polarity → Polarity
neg + = -
neg - = +

--------------------------------------------------------
-- Declarative (possible world) semantics
--

open import Data.List.Membership.Propositional
--open import Data.List.Any.Membership.Propositional

-- Entailment Relation
infix 3 _⊨[_]_
data _⊨[_]_ : World → Polarity → Form → Set where
  flip : ∀{w t A} → w ⊨[ neg t ] (atom A) → w ⊨[ t ] ¬ A
  both : ∀{w t P Q} → w ⊨[ t ] P → w ⊨[ t ] Q → w ⊨[ t ] P ∧ Q
  somewhere : ∀{w a} → a ∈ w → w ⊨[ + ] atom a
  nowhere : ∀{w a} → a ∉ w → w ⊨[ - ] atom a

-- A pair containing a predicate and polarity
PredMap : Set
PredMap = (Polarity × R)

-- A list containing pairs of polarities and predicates
State : Set
State = List PredMap

open import Data.List.Membership.Propositional

-- Operational Semantics: normalisation function
infixr 3 _↓[_]_
_↓[_]_ : Form → Polarity → State → State
P ∧ Q ↓[ t ] N = Q ↓[ t ] P ↓[ t ] N
¬ x ↓[ t ] N = (neg t , x) ∷ N
atom x ↓[ t ] N = (t , x) ∷ N

--------------------------------------------------------

-- Is a given state satisfied in a world.
-- A state is satisfied if for all positive polarities
-- of a predicate the predicate exists in the world and
-- for all negative polatities the predicate does not exist
-- in the world.

_∈⟨_⟩ : World → State → Set
w ∈⟨ S ⟩ = (∀ a → (+ , a) ∈ S → a ∈ w) × (∀ a → (- , a) ∈ S → a ∉ w)

open import Data.List.Relation.Unary.Any

--------------------------------------------------------
-- Code for the Soundness and Completeness proofs
--
-- We first prove some auxiliary lemmas:

weakeningH : ∀ t₁ t₂ P Q N a -> (t₁ , a) ∈ (P ↓[ t₂ ] N) -> (t₁ , a) ∈ (Q ↓[ t₂ ] P ↓[ t₂ ] N)
weakeningH t₁ t₂ P (Q ∧ Q₁) N a x = weakeningH t₁ t₂ Q Q₁ (P ↓[ t₂ ] N) a (weakeningH t₁ t₂ P Q N a x)
weakeningH t₁ t₂ P (¬ x₁) N a x = there x
weakeningH t₁ t₂ P (atom x₁) N a x = there x

--
-- ∈⟨⟩-weakeningH
--
∈⟨⟩-weakeningH : ∀ w t P Q N -> w ∈⟨ Q ↓[ t ] P ↓[ t ] N ⟩ -> (w ∈⟨ P ↓[ t ] N ⟩)
∈⟨⟩-weakeningH w t P Q N (pos , neg)
  = (λ a1 x → pos a1 (weakeningH + t P Q N a1 x))
  , (λ a1 x x2 → neg a1 (weakeningH - t P Q N a1 x) x2)

lemma-transport-r : ∀ t P M N →
  ((P ↓[ t ] M) ++ N) ≡ (P ↓[ t ] (M ++ N))
lemma-transport-r t (P ∧ Q) M N = trans
  (lemma-transport-r t Q (P ↓[ t ] M) N)
  (cong (λ x → Q ↓[ t ] x) (lemma-transport-r t P M N))
lemma-transport-r t (¬ A) M N = refl
lemma-transport-r t (atom x) M N = refl


-- older stdlib
{-
open import Algebra
++-assoc :  (x x₁ x₂ : List ( Polarity × R)) →  (x ++ x₁) ++ x₂ ≡ x ++ x₁ ++ x₂
++-assoc = Monoid.assoc (monoid (Polarity × R))-}

--newer stdlib
open import Data.List.Properties


lemma-transport-l : ∀ t P M N →
  (M ++ (P ↓[ t ] N)) ≡ ((M ++ (P ↓[ t ] [])) ++ N)
lemma-transport-l t (P ∧ P₁) M N
  = sym (trans (++-assoc M (P₁ ↓[ t ] P ↓[ t ] []) N)
               (cong (λ x → M ++ x)
                     (trans (lemma-transport-r t P₁ (P ↓[ t ] []) N)
                            (cong (λ x → P₁ ↓[ t ] x) (lemma-transport-r t P [] N)))))
lemma-transport-l t (¬ x) M N = sym (++-assoc M (((neg t) , x) ∷ []) N)
lemma-transport-l t (atom x) M N = sym (++-assoc M ((t , x) ∷ []) N)

open import AnyLemma


∈-transport-l : ∀ a {t1} t P M N -> (t1 , a) ∈ ( M ++ (P ↓[ t ] N))
  -> (t1 , a) ∈ ((M ++ (P ↓[ t ] [])) ++ N)
∈-transport-l a₁ {t₁} t P M N x
  = any-cong {zero} {zero} {Polarity × R} {λ _ → R} x (lemma-transport-l t P M N)



∈-transport-r : ∀ a {t1} t P M N -> (t1 , a) ∈ ((M ++ (P ↓[ t ] [])) ++ N)
  -> (t1 , a) ∈ ( M ++ (P ↓[ t ] N))
∈-transport-r a₁ t P M N x
  = any-cong {zero} {zero} {Polarity × R} {λ _ → R}  x (sym (lemma-transport-l t P M N))

--
-- exchange for the underlying representation (was cAny)
--
∈-exchange : ∀ a {t} t1 t2 P Q N1 N2 -> (t , a) ∈ ( N1 ++ (P ↓[ t1 ] Q ↓[ t2 ] N2))
  -> (t , a) ∈ (N1 ++ (Q ↓[ t2 ] P ↓[ t1 ] N2))
∈-exchange a₁ t1 t2 P (Q ∧ R) N1 N2 x
  = ∈-transport-r a₁ t2 R N1 (Q ↓[ t2 ] P ↓[ t1 ] N2)
      (∈-exchange a₁ t1 t2 P Q (N1 ++ (R ↓[ t2 ] [])) N2
            (∈-transport-l a₁ t2 R N1 (P ↓[ t1 ] Q ↓[ t2 ] N2)
                             (∈-exchange a₁ t1 t2 P R N1 (Q ↓[ t2 ] N2) x)))
∈-exchange a₁ t1 t2 (P ∧ Q) (¬ A) N1 N2 x
  = ∈-exchange a₁ t1 t2 Q (¬ A) N1 (P ↓[ t1 ] N2)
    (∈-transport-r a₁ t1 Q N1 ((¬ A) ↓[ t2 ] P ↓[ t1 ] N2)
      (∈-exchange a₁ t1 t2 P (¬ A) (N1 ++ (Q ↓[ t1 ] [])) N2
        (∈-transport-l a₁ t1 Q N1 (P ↓[ t1 ] (¬ A) ↓[ t2 ] N2) x)))
∈-exchange a₁ t1 t2 (¬ x₁) (¬ A) [] N2 (here px) = there (here px)
∈-exchange a₁ t1 t2 (¬ x₁) (¬ A) [] N2 (there (here px)) = here px
∈-exchange a₁ t1 t2 (¬ x₁) (¬ A) [] N2 (there (there x)) = there (there x)
∈-exchange a₁ t1 t2 (¬ x₁) (¬ A) (x₂ ∷ N1) N2 (here px) = here px
∈-exchange a₁ t1 t2 (¬ x₁) (¬ A) (x₂ ∷ N1) N2 (there x)
  = there (∈-exchange a₁ t1 t2 (¬ x₁) (¬ A) N1 N2 x)
∈-exchange a₁ t1 t2 (atom x₁) (¬ A) [] N2 (here px) = there (here px)
∈-exchange a₁ t1 t2 (atom x₁) (¬ A) [] N2 (there (here px)) = here px
∈-exchange a₁ t1 t2 (atom x₁) (¬ A) [] N2 (there (there x)) = there (there x)
∈-exchange a₁ t1 t2 (atom x₁) (¬ A) (x₂ ∷ N1) N2 (here px) = here px
∈-exchange a₁ t1 t2 (atom x₁) (¬ A) (x₂ ∷ N1) N2 (there x)
  = there (∈-exchange a₁ t1 t2 (atom x₁) (¬ A) N1 N2 x)
∈-exchange a₁ t1 t2 (P ∧ Q) (atom x₁) N1 N2 x
  = ∈-exchange a₁ t1 t2 Q (atom x₁) N1 (P ↓[ t1 ] N2)
    (∈-transport-r a₁ t1 Q N1 ((atom x₁) ↓[ t2 ] P ↓[ t1 ] N2)
      (∈-exchange a₁ t1 t2 P (atom x₁) (N1 ++ (Q ↓[ t1 ] [])) N2
        (∈-transport-l a₁ t1 Q N1 (P ↓[ t1 ] (atom x₁) ↓[ t2 ] N2) x)))
∈-exchange a₁ t1 t2 (¬ A) (atom x₁) [] N2 (here px) = there (here px)
∈-exchange a₁ t1 t2 (¬ A) (atom x₁) [] N2 (there (here px)) = here px
∈-exchange a₁ t1 t2 (¬ A) (atom x₁) [] N2 (there (there x)) = there (there x)
∈-exchange a₁ t1 t2 (¬ A) (atom x₁) (x₂ ∷ N1) N2 (here px) = here px
∈-exchange a₁ t1 t2 (¬ A) (atom x₁) (x₂ ∷ N1) N2 (there x)
  = there (∈-exchange a₁ t1 t2 (¬ A) (atom x₁) N1 N2 x)
∈-exchange a₁ t1 t2 (atom x₂) (atom x₁) [] N2 (here refl) = there (here refl)
∈-exchange a₁ t1 t2 (atom x₂) (atom x₁) [] N2 (there (here px)) = here px
∈-exchange a₁ t1 t2 (atom x₂) (atom x₁) [] N2 (there (there x)) = there (there x)
∈-exchange a₁ t1 t2 (atom x₂) (atom x₁) ((t3 , x₃) ∷ N1) N2 (here px) = here px
∈-exchange a₁ t1 t2 (atom x₂) (atom x₁) ((t3 , x₃) ∷ N1) N2 (there x)
  = there (∈-exchange a₁ t1 t2 (atom x₂) (atom x₁) N1 N2 x)

--
-- ∈⟨⟩-exchange lemma
--
-- a wrapper around ∈-exchange
--
∈⟨⟩-exchange : ∀ w t1 t2 P Q N1 N2 -> w ∈⟨ N1 ++ (P ↓[ t1 ] Q ↓[ t2 ] N2) ⟩
  -> w ∈⟨ N1 ++ (Q ↓[ t2 ] P ↓[ t1 ] N2) ⟩
∈⟨⟩-exchange w t1 t2 P (Q ∧ R) N1 N2 (fst , snd)
  = (λ { a₁ x₁ → fst a₁ (∈-exchange a₁ t2 t1 R P N1 (Q ↓[ t2 ] N2)
       (∈-transport-r a₁ t2 R N1 (P ↓[ t1 ] Q ↓[ t2 ] N2)
         (∈-exchange a₁ t2 t1  Q P  (N1 ++ (R ↓[ t2 ] [])) N2
           (∈-transport-l a₁ t2 R N1 (Q ↓[ t2 ] P ↓[ t1 ] N2) x₁))))})
  , (λ { a₁ x x₁ → snd a₁
       ( ∈-exchange a₁ t2 t1 R P N1 (Q ↓[ t2 ] N2)
         (∈-transport-r a₁ t2 R N1 (P ↓[ t1 ] Q ↓[ t2 ] N2)
           (∈-exchange a₁ t2 t1 Q P  (N1 ++ (R ↓[ t2 ] [])) N2
             (∈-transport-l a₁ t2 R N1 (Q ↓[ t2 ] P ↓[ t1 ] N2) x)))  )
      x₁})
∈⟨⟩-exchange w t1 t2 P (¬ A) N1 N2 (fst , snd)
  = (λ {a₁ x₁ → fst a₁ (∈-exchange a₁ (neg t2) t1 (atom A) P N1 N2 x₁)})
  , (λ {a₁ x x₁ → snd a₁ (∈-exchange a₁ (neg t2) t1 (atom A) P N1 N2 x) x₁})
∈⟨⟩-exchange w t1 t2 P (atom x₁) N1 N2 (fst , snd)
  = (λ {a₁ x → fst a₁ (∈-exchange a₁ t2 t1 (atom x₁) P N1 N2 x)})
  , (λ {a₁ x x₂ → snd a₁ (∈-exchange a₁ t2 t1 (atom x₁) P N1 N2 x) x₂})


--
-- soundness of operational semantics 
--
↓-sound : ∀{w t P} → w ∈⟨ P ↓[ t ] [] ⟩ → w ⊨[ t ] P
↓-sound {w} {t} {P ∧ Q} x
  = both (↓-sound (∈⟨⟩-weakeningH w t P Q [] x))
         (↓-sound (∈⟨⟩-weakeningH w t Q P [] (∈⟨⟩-exchange w t t Q P [] [] x )))
↓-sound {w} {+} {¬ A} (proj1 , proj2) = flip (nowhere (proj2 A (here refl)))
↓-sound {w} { - } {¬ A} (proj1 , proj2) = flip (somewhere (proj1 A (here (refl))))
↓-sound {w} {+} {atom p} (proj1 , proj2) = somewhere (proj1 p (here refl))
↓-sound {w} { - } {atom p} (proj1 , proj2) = nowhere (proj2 p (here refl))


open import Data.Sum

strengthening : ∀ t₁ t₂ P Q N a -> (t₁ , a) ∈ (Q ↓[ t₂ ] P ↓[ t₂ ] N)
  -> ((t₁ , a) ∈ (Q ↓[ t₂ ] N)) ⊎  ((t₁ , a) ∈ (P ↓[ t₂ ] N))
strengthening t₁ t₂ (P ∧ P₁) (Q₁ ∧ Q₂) N a x
  with strengthening t₁ t₂ Q₁ Q₂ (P₁ ↓[  t₂ ] P ↓[ t₂ ] N) a x
strengthening t₁ t₂ (P ∧ P₁) (Q₁ ∧ Q₂) N a x | inj₁ x₁
  with strengthening t₁ t₂ Q₂ P₁ (P ↓[ t₂ ] N) a (∈-exchange a t₂ t₂ Q₂ P₁ [] (P ↓[ t₂ ] N) x₁)
strengthening t₁ t₂ (P ∧ P₁) (Q₁ ∧ Q₂) N a x | inj₁ x₁ | inj₁ x₂ = inj₂ x₂
strengthening t₁ t₂ (P ∧ P₁) (Q₁ ∧ Q₂) N a x | inj₁ x₁ | inj₂ y
  with strengthening t₁ t₂ P Q₂ N a y
strengthening t₁ t₂ (P ∧ P₁) (Q₁ ∧ Q₂) N a x | inj₁ x₁ | inj₂ y | inj₁ x₂
  = inj₁ (∈-exchange a t₂ t₂ Q₁ Q₂ [] N (weakeningH t₁ t₂ Q₂ Q₁ N a x₂))
strengthening t₁ t₂ (P ∧ P₁) (Q₁ ∧ Q₂) N a x | inj₁ x₁ | inj₂ y | inj₂ y₁
  = inj₂ (weakeningH t₁ t₂ P P₁ N a y₁)
strengthening t₁ t₂ (P ∧ P₁) (Q₁ ∧ Q₂) N a x | inj₂ y
  with strengthening t₁ t₂ Q₁ P₁ (P ↓[ t₂ ] N) a (∈-exchange a t₂ t₂ Q₁ P₁ [] (P ↓[ t₂ ] N) y)
strengthening t₁ t₂ (P ∧ P₁) (Q₁ ∧ Q₂) N a x | inj₂ y | inj₁ x₂ = inj₂ x₂
strengthening t₁ t₂ (P ∧ P₁) (Q₁ ∧ Q₂) N a x | inj₂ y | inj₂ y₂
  with strengthening t₁ t₂ P Q₁ N a y₂
strengthening t₁ t₂ (P ∧ P₁) (Q₁ ∧ Q₂) N a x | inj₂ y | inj₂ y₂ | inj₁ x₁ = inj₁ (weakeningH t₁ t₂ Q₁ Q₂ N a x₁)
strengthening t₁ t₂ (P ∧ P₁) (Q₁ ∧ Q₂) N a x | inj₂ y | inj₂ y₂ | inj₂ y₁ = inj₂ (weakeningH t₁ t₂ P P₁ N a y₁)
strengthening t₁ t₂ (¬ x₁) (Q₁ ∧ Q₂) N a x with ∈-exchange a t₂ t₂ (Q₁ ∧ Q₂) (¬ x₁) [] N x
strengthening t₁ t₂ (¬ x₁) (Q₁ ∧ Q₂) N a x | here px = inj₂ (here px)
strengthening t₁ t₂ (¬ x₁) (Q₁ ∧ Q₂) N a x | there res = inj₁ res
strengthening t₁ t₂ (atom x₁) (Q₁ ∧ Q₂) N a x with ∈-exchange a t₂ t₂ (Q₁ ∧ Q₂) (atom x₁) [] N x
strengthening t₁ t₂ (atom x₁) (Q₁ ∧ Q₂) N a x | here px = inj₂ (here px)
strengthening t₁ t₂ (atom x₁) (Q₁ ∧ Q₂) N a x | there res = inj₁ res
strengthening t₁ t₂ P (¬ x₁) N a (here px) = inj₁ (here px)
strengthening t₁ t₂ (P ∧ P₁) (¬ x₁) N a (there x) = inj₂ x
strengthening t₁ t₂ (¬ x₂) (¬ x₁) N a (there (here px)) = inj₂ (here px)
strengthening t₁ t₂ (¬ x₂) (¬ x₁) N a (there (there x)) = inj₁ (there x)
strengthening t₁ t₂ (atom x₂) (¬ x₁) N a (there (here px)) = inj₂ (here px)
strengthening t₁ t₂ (atom x₂) (¬ x₁) N a (there (there x)) = inj₁ (there x)
strengthening t₁ t₂ P (atom x₁) N a (here px) = inj₁ (here px)
strengthening t₁ t₂ P (atom x₁) N a (there x) = inj₂ x

helperPos :  ∀ w t P Q N a → (w ∈⟨ P ↓[ t ] N ⟩) -> (w ∈⟨ Q ↓[ t ] N ⟩)
           -> (+ , a) ∈ (Q ↓[ t ] P ↓[ t ] N)
           -> a ∈ w
helperPos w t P Q N a x x1 x2 with (strengthening + t P Q N) a x2
helperPos w t P Q N a x x1 x2 | inj₁ y = proj₁ x1 a y
helperPos w t P Q N a x x1  x2 | inj₂ y = proj₁ x a y

open import Data.Empty

helperNeg : ∀ w t P Q N a → (w ∈⟨ P ↓[ t ] N ⟩) -> (w ∈⟨ Q ↓[ t ] N ⟩)
            -> (- , a) ∈ (Q ↓[ t ] P ↓[ t ] N)
            -> a ∉ w
helperNeg w t P Q N a x x1 x2 x3 with (strengthening - t P Q N) a x2
helperNeg w t P Q N a x x1 x2 x3 | inj₁ y = proj₂ x1 a y x3
helperNeg w t P Q N a x x1 x2 x3 | inj₂ y = proj₂ x a y x3


∈⟨⟩-strengthening : ∀ w t P Q N -> (w ∈⟨ P ↓[ t ] N ⟩) -> (w ∈⟨ Q ↓[ t ] N ⟩)
  -> w ∈⟨ Q ↓[ t ] P ↓[ t ] N ⟩
∈⟨⟩-strengthening w t P Q N p n
  = (λ { a x → helperPos w t P Q N a p n x })
    , (λ {a x x2 → helperNeg w t P Q N a p n x x2})


--
-- Completeness of operational semantics 
--
↓-complete : ∀{w t P} → w ⊨[ t ] P → w ∈⟨ P ↓[ t ] [] ⟩
↓-complete {w} {t} {P ∧ Q} (both x y)
  = ∈⟨⟩-strengthening w t P Q [] (↓-complete x) (↓-complete y)
↓-complete {w} {+} {¬ x₁} (flip (nowhere x))
  = (λ { a (here ())
       ; a (there ())})
  , (λ { a (here refl) x₃ → x x₃
       ; a (there ()) x₃})
↓-complete {w} { - } {¬ x₁} (flip (somewhere x))
  = (λ { a (here refl) → x
       ; a (there ())})
  , (λ { a (here ()) x₃
       ; a (there ()) x₃})
↓-complete {w} { .+ } {atom x₁} (somewhere x)
  = (λ { a (here refl) → x
       ; a (there ()) })
  , (λ { a (here ()) x₃
       ; a (there ()) x₃ })
↓-complete {w} { .- } {atom x₁} (nowhere x)
  = (λ { a (here ())
       ; a (there ())})
  , (λ { a (here refl) x₃ → x x₃
       ; a (there ()) x₃})

open import Data.Product
open import Agda.Builtin.Bool
open import Relation.Nullary
open import Data.Nat hiding (_*_ ; _+_) renaming (_≟_ to _=N?_)
open IsDecEquivalence isDEC renaming (_≟_ to _=C?_) hiding (refl)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; cong)
open import Data.Empty
open import Data.Unit hiding (_≟_)
open Relation.Nullary
open IsDecEquivalence isDE hiding (refl)

-- Is an atom in a State
_∈S_ : (a : R) (s : State) -> Set
At ∈S [] = ⊥
At ∈S ((t , At') ∷ s) with At' ≟ At
(At ∈S ((t , At') ∷ s)) | yes p = At ≡ At'
(At ∈S ((t , At') ∷ s)) | no ¬p = At ∈S s

-- Is an atom not in a State
_∉S_ : (a : R) (s : State) -> Set
a ∉S s = Relation.Nullary.¬ (a ∈S s)

-- Decidability of an Atom's membership in a State
isInState : (a : R) -> (s : State) -> Dec (a ∈S s)
isInState At [] = no (λ z → z)
isInState At ((t , At') ∷ s) with At' ≟  At
isInState At ((t , .At) ∷ s) | yes refl = yes refl
isInState At ((t , At') ∷ s) | no ¬p = isInState At s


--Decidability of uniqueness of atoms in a given State
uniqueAtom : (a : R) -> (s : State) -> Dec (a ∉S s)
uniqueAtom At [] = yes λ ()
uniqueAtom At ((t , At') ∷ s) with At' ≟ At
uniqueAtom At ((t , At') ∷ s) | yes refl = no (λ prf → prf refl)
uniqueAtom At ((t , At') ∷ s) | no ¬p = uniqueAtom At s

-- A State is valid if there is no duplicate predicates in the State.
validState : State -> Set
validState [] = ⊤
validState ((t , At') ∷ s) with isInState At' s
validState ((t , At') ∷ s) | yes p = ⊥
validState ((t , At') ∷ s) | no ¬p = validState s

--Decidability of State validity
decValidState : (s : State) -> Dec (validState s)
decValidState [] = yes tt
decValidState ((t , At') ∷ s) with isInState At' s
decValidState ((t , At') ∷ s) | yes p =  no λ ()
decValidState ((t , At') ∷ s) | no ¬p = decValidState s

-- Context
Γ : Set
Γ = Action → State × State

-- Decidablity of polarities
decZ : (z : Polarity) -> (z' : Polarity) -> Dec (z ≡ z')
decZ + + = yes refl
decZ + - = no (λ ())
decZ - + = no (λ ())
decZ - - = yes refl

open Data.Product renaming (_,_ to _↝_)
open import Relation.Nullary

-- Subtyping
infix 3 _<:_
data _<:_ : State → State → Set where
  []<:_ : ∀ Q → [] <: Q
  atom<: : ∀{t x P Q} → (t , x) ∈ Q → P <: Q → (t , x) ∷ P <: Q

-- Extension of subtyping
<:atom : (P : State) -> (Q : State) -> (s : PredMap) -> P <: Q -> P <: s ∷ Q
<:atom .[] Q s ([]<: .Q) = []<: (s ∷ Q)
<:atom ((z ↝ a) ∷ P) Q s (atom<: x₂ x₁) = atom<: (there x₂) (<:atom P Q s x₁)

-- Reflexivity of subtyping
reflSub : (S : State) -> S <: S
reflSub [] = []<: []
reflSub (s ∷ S) = atom<: (here refl) (<:atom S S s (reflSub S))

helpTrans : ∀ x -> (P : State) -> (Q : State ) -> x ∈ P -> P <: Q -> x ∈ Q
helpTrans .(_ ↝ _) .((_ ↝ _) ∷ _) Q (here refl) (atom<: x x₂) = x
helpTrans x .((_ ↝ _) ∷ _) Q (there x₁) (atom<: x₂ x₃) = helpTrans x _ Q x₁ x₃

-- Transitivity of subtyping
transSub : (L : State) -> (M : State) -> (N : State) -> L <: M -> M <: N -> L <: N
transSub [] M N x x₁ = []<: N
transSub (.(_ ↝ _) ∷ L) M N (atom<: x x₂) x₁ = atom<: (helpTrans _ M N x x₁) (transSub L M N x₂ x₁)

-- Weakening of subtyping
weakSub : (s : PredMap) -> (P : State) -> (Q : State) ->  (s ∷ P) <: Q -> P <: Q
weakSub .(_ ↝ _) P Q (atom<: x₁ x₂) = x₂


-- Decidablity of subtyping

isSame : (s : PredMap) -> (s' : PredMap) -> Dec (s ≡ s')
isSame (z , a) (z' , a') with decZ z z' | a ≟ a'
isSame (z ↝ a) (.z ↝ .a) | yes refl | yes refl = yes refl
isSame (z ↝ a) (.z ↝ a') | yes refl | no ¬p = no λ { refl → ¬p refl}
isSame (z ↝ a) (z' ↝ a') | no ¬p | yes p = no λ { refl → ¬p refl}
isSame (z ↝ a) (z' ↝ a') | no ¬p | no ¬p₁ = no λ { refl → ¬p refl}

isSameInState : (s : PredMap) -> (S : State) -> Dec (s ∈ S)
isSameInState s [] = no (λ ())
isSameInState s (s' ∷ S) with isSame s s'
isSameInState s (.s ∷ S) | yes refl = yes (here refl)
isSameInState s (s' ∷ S) | no ¬p with isSameInState s S
isSameInState s (s' ∷ S) | no ¬p | yes p = yes (there p)
isSameInState s (s' ∷ S) | no ¬p | no ¬p₁ = no (λ { (here px) → ¬p px ; (there x) → ¬p₁ x})

decSub : (P : State) -> (Q : State) -> Dec (P <: Q)
decSub [] Q = yes ([]<: Q)
decSub (p ∷ P) Q with isSameInState p Q
decSub (p ∷ P) Q | no ¬p = no (λ { (atom<: x₁ x) → ¬p x₁})
decSub (p ∷ P) Q | yes p₁ with decSub P Q
decSub (p ∷ P) Q | yes p₁ | no ¬p = no (λ { (atom<: x₁ x) → ¬p x})
decSub (p ∷ P) Q | yes p₁ | yes p₂ = yes (atom<: p₁ p₂)

-----------------------------------------------------------------------

open Data.List renaming (_∷_ to _*_)

data  _,_¦_ :  Γ -> (State × State) -> f -> Set where
    weakening : ∀{Γ P Q fs} ->  (P' : State) -> P <: P' -> validState P' -> Γ , P ↝ Q ¦ fs -> Γ , P' ↝ Q ¦ fs
    applyAction : ∀ {Γ f} -> validState (proj₁ (Γ f)) -> validState (proj₂ (Γ f)) -> Γ , Γ f ¦ act f
    composition : ∀ {Γ P Q Q' R fs f'} -> Q' <: Q -> Γ , P ↝ Q ¦ fs -> Γ , Q' ↝ R ¦ f' -> Γ , P ↝ R ¦ join fs f'
    frame : ∀ {Γ P Q f } -> (z : Polarity) -> (a : R) -> a ∉S P -> a ∉S Q -> Γ , P ↝  Q  ¦ act f
                                                                              -> Γ , ((z , a) * P) ↝  ((z , a) * Q)  ¦ act f --this is a restriction on the normal frame rule
    halt :  ∀ {Γ P Q fs} -> (Q' : State) -> (validState Q') -> Q' <: Q -> Γ , P ↝ Q ¦ fs ->  Γ , P ↝ Q' ¦ join fs (halt)


-- Transitivity of subtyping
--transSub : (L : State) -> (M : State) -> (N : State) -> L <: M -> M <: N -> L <: N
--transSub [] M N x x₁ = []<: N
--transSub (.(_ ↝ _) ∷ L) M N (atom<: x x₂) x₁ = atom<: (helpTrans _ M N x x₁) (transSub L M N x₂ x₁)

--Proof that an actions preconditions are always a subtype of pre-state, p , in a given contstruction of our semantics
preSatP : ∀ Γ p q f -> Γ , p ↝ q ¦ act f -> proj₁ (Γ f) <: p
preSatP Γ p q f₁ (weakening .p x₁ x₂ x) with preSatP Γ _ q f₁ x
... | ans = transSub (proj₁ (Γ f₁)) _ p ans x₁
preSatP Γ p q f₁ (applyAction x x₁) = reflSub p
preSatP Γ ((z ↝ a) ∷ p) ((z ↝ a) ∷ q) f₁ (frame z a x x₁ x₂) with preSatP Γ p q f₁ x₂
... | ans = <:atom _ p (z , a) ans

--Proof that an actions postconditions are always a subtype of post-state, q , in a given contstruction of our semantics
postSatQ : ∀ Γ p q f -> Γ , p ↝ q ¦ act f -> proj₂ (Γ f) <: q
postSatQ Γ₁ p q f₁ (weakening .p x₁ x₂ x) with postSatQ Γ₁ _ q f₁ x
... | ans = ans
postSatQ Γ p q f₁ (applyAction x x₁) = reflSub q
postSatQ Γ ((z ↝ a) ∷ p) ((z ↝ a) ∷ q) f₁ (frame z a x x₁ x₂) with postSatQ Γ p q f₁ x₂
... | ans = <:atom _ q (z , a) ans

------------------------------------------------------------

-- Alternate declaration of validity of States. Showing that all states do not contain any duplicate predicates.
validS : State -> Set
validS [] = ⊤
validS ((z ↝ r) ∷ S) = r ∉S S × validS S

-- Proof that validS is equivalent to validState
validProof : (S : State) -> validS S -> validState S
validProof [] x = tt
validProof ((z , a)  ∷ S) x with isInState a S
validProof ((z ↝ a) ∷ S) (fst ↝ snd) | yes p = fst p
validProof ((z ↝ a) ∷ S) (fst ↝ snd) | no ¬p = validProof S snd

validStateToS :  (S : State) -> validState S -> validS S
validStateToS [] x = tt
validStateToS ((z ↝ r) ∷ S) x with isInState r S
validStateToS ((z ↝ r) ∷ S) x | yes p = ⊥-elim x
validStateToS ((z ↝ r) ∷ S) x | no ¬p = ¬p ↝ validStateToS S x

-- A proof showing that our rules will never introduce inconsistency as long as we were given
-- valid actions.
consistency : ∀ Γ p q fs -> Γ , p ↝ q ¦ fs -> validS p × validS q
consistency Γ₁ p q fs (weakening .p x x₁ x₂) with consistency Γ₁ _ q fs x₂
... | fst ↝ snd = validStateToS p x₁ ↝ snd
consistency Γ₁ p q .(act _) (applyAction vp vq) = validStateToS p vp ↝ validStateToS q vq
consistency Γ₁ p q .(join _ _) (composition x x₁ x₂) with consistency Γ₁ _ q _ x₂ | consistency Γ₁ p _ _ x₁
... | fst ↝ snd | fst₁ ↝ snd₁ = fst₁ ↝ snd
consistency Γ₁ ((z ↝ a) ∷ p) ((z ↝ a) ∷ q) f (frame z a x x₁ x₂) with consistency Γ₁ p _ f x₂
... | fst ↝ snd = (x ↝ fst) ↝ x₁ ↝ snd
consistency Γ₁ p q .(join _ halt) (halt .q x x₁ x₂) with consistency Γ₁ p _ _ x₂
... | fst ↝ snd = fst ↝ (validStateToS q x)


open import Data.Sum

-------------------------------------------------------------------

del : R → State → State
del x [] = []
del x ((z , a) ∷ S) with x ≟ a
del x ((z , a) ∷ S) | yes p =  del x S
del x ((z , a) ∷ S) | no ¬p = (z , a) ∷ del x S

-- Override operator
_⊔N_ : State → State → State
P ⊔N [] = P
P ⊔N ((z , a) ∷ Q) = (z , a) ∷ del a P ⊔N Q

del-spec : ∀ t x N → (t , x) ∉ del x N
del-spec t x [] ()
del-spec t x ((t' , y) ∷ N) tx∈N' with x ≟ y
del-spec t x ((t' , y) ∷ N) tx∈N' | yes p = del-spec t x N tx∈N'
del-spec .t' .y ((t' , y) ∷ N) (here refl) | no ¬p = ¬p _≡_.refl
del-spec t x ((t' , y) ∷ N) (there tx∈N') | no ¬p =  del-spec t x N tx∈N'

del-∈ : ∀{M y x} → x ∈ del y M → x ∈ M
del-∈ {[]}             ()
del-∈ {(t , z) ∷ M}{y} x∈ with y ≟ z
del-∈ {(t , z) ∷ M} {y} x∈ | yes p = there (del-∈ x∈)
del-∈ {(t , z) ∷ M} {y} (here refl) | no ¬p = here _≡_.refl
del-∈ {(t , z) ∷ M} {y} (there x∈) | no ¬p = there (del-∈ x∈)

⊔-right-bias : ∀{N x M} → x ∈ N → x ∈ M ⊔N N
⊔-right-bias {[]}    ()
⊔-right-bias {y ∷ N} (here refl) = here _≡_.refl
⊔-right-bias {y ∷ N}{x}{M} (there x∈N) = there (⊔-right-bias x∈N)

----------------------------------------------------------

-- Figure 12
--

-- Action Handler
ActionHandler : Set
ActionHandler = Action → World → World


-- Evaluation function
⟦_⟧ : f → ActionHandler → World → World
⟦ halt ⟧ σ w = w
⟦ act x ⟧ σ w = σ x w
⟦ join x x₁ ⟧ σ w = ⟦ x₁ ⟧ σ (⟦ x ⟧ σ w) --first actions in x

-- Well formed handler

{-
  If we have an action α in gamma
  And has preconditions proj₁ (Γ α) and postconditions proj₂ (Γ α)
  proj₁ (Γ α) is a subtype of M
  and M is true in the world w
  then the application of the action handler σ of action α
  results in M being overriden by proj₂ (Γ α) in w
-}


WfHandler : Γ → ActionHandler → Set
WfHandler Γ σ =
  ∀{α P} → proj₁ (Γ α) <: P → ∀{w} → w ∈⟨ P ⟩ → σ α w ∈⟨ P ⊔N proj₂ (Γ α) ⟩

-- If some state M is satisfied in the world w and we have another state N
-- that is a subtype of M then N is also satisfied in the world
<:-resp-∈ : ∀{N M} → N <: M → ∀{w} → w ∈⟨ M ⟩ → w ∈⟨ N ⟩
<:-resp-∈ ([]<: N) w∈⟨M⟩ = (λ _ ()) , λ _ ()
<:-resp-∈ (atom<: {t}{x}{N}{M} tx∈M N<:M) {w} w∈⟨M⟩ = lt , rt where
  ih : w ∈⟨ N ⟩
  ih = <:-resp-∈ N<:M w∈⟨M⟩
  lt : ∀ a' → (+ , a') ∈ (t , x) ∷ N → a' ∈ w
  lt a' (here px) =  proj₁ w∈⟨M⟩ a' (subst (λ tx → tx ∈ M) (Relation.Binary.PropositionalEquality.sym px) tx∈M)
  lt a' (there +a'∈N) = proj₁ ih a' +a'∈N
  rt : ∀ a' → (- , a') ∈ (t , x) ∷ N → a' ∉ w
  rt a' (here px) a'∈w =
    proj₂ w∈⟨M⟩ a' (subst (λ tx → tx ∈ M) (Relation.Binary.PropositionalEquality.sym px) tx∈M) a'∈w
  rt a' (there -a'∈N) a'∈w = proj₂ ih a' -a'∈N a'∈w

-- When P is overrided with Q all elements of Q remain in the result
PostPreservationO : (Q : State) -> (s : PredMap) -> (P : State) -> s ∈ Q → s ∈ P ⊔N Q
PostPreservationO (q ∷ Q) .q P (here refl) = here _≡_.refl
PostPreservationO (q ∷ Q) s P (there s∈Q) = there (PostPreservationO Q s _ s∈Q)

-- Q is a subtype of P override Q
PostSubO : (P : State) -> (Q : State) -> Q <: (P ⊔N Q)
PostSubO P [] = []<: P
PostSubO P (q ∷ Q) with PostPreservationO (q ∷ Q) q P (here refl)
... | ans = atom<: ans (<:atom Q (del (proj₂ q) P ⊔N Q) q (PostSubO (del (proj₂ q) P) Q))

-- If P override Q is satisfied in a world then Q is also satsfied in that world
PostSatO : (σ : ActionHandler) -> (f : Action) -> (w : World) -> (P : State) -> (Q : State) ->  (Γ₁ : Γ) -> σ f w ∈⟨ P ⊔N Q ⟩ ->  σ f w ∈⟨ Q ⟩
PostSatO σ f₁ w P Q Γ₁ x = <:-resp-∈ (PostSubO P Q) x

-- If we have a well formed handler and an action and the pre-conditions of an action are satsfied in a given world then we can apply
-- the ActionHandler to produce a world where the post-conditions are satisfied.
wellFormedApplication : (σ : ActionHandler) -> (w : World) -> (Γ₁ : Γ) -> (f : Action) -> WfHandler Γ₁ σ
                                               -> validState (proj₁ (Γ₁ f))
                                               ->  validState (proj₂ (Γ₁ f))
                                               -> w ∈⟨ proj₁ (Γ₁ f) ⟩ ->  σ f w ∈⟨ proj₂ (Γ₁ f) ⟩
wellFormedApplication σ w Γ₁ f₁ WfH vp vq w∈⟨P⟩ with WfH (preSatP Γ₁ (proj₁ (Γ₁ f₁)) (proj₂ (Γ₁ f₁)) f₁ (applyAction vp vq)) w∈⟨P⟩
wellFormedApplication σ w Γ₁ f₁ x vp vq x₁ | ans = PostSatO σ f₁ w (proj₁ (Γ₁ f₁)) (proj₂ (Γ₁ f₁)) Γ₁ ans

-- If a State, (s :: S), is satisfied in a world then we can Weaken the result to show that S will also be satisfied
weakHelp : (w : World) -> (s : PredMap) -> (S : State) -> w ∈⟨ s ∷ S ⟩ -> w ∈⟨ S ⟩
weakHelp w s S w∈⟨s∷S⟩ = <:-resp-∈ (<:atom S S s (reflSub S)) w∈⟨s∷S⟩

-- Helper lemma
subProofHelp : (a : R) -> (z : Polarity) -> (P : State) -> a ∈S ((z , a) ∷ P)
subProofHelp a z P with a ≟ a
subProofHelp a z P | yes p₁ = refl
subProofHelp a z P | no ¬p = ⊥-elim (¬p refl)

-- Weakening for state membership
stateMemWeak : (a : R) -> (P : State) -> (s : PredMap) ->  a ∈S P -> a ∈S (s ∷ P)
stateMemWeak a [] s x₁ = ⊥-elim x₁
stateMemWeak a (p ∷ P) s x₁ with proj₂ s ≟ a
stateMemWeak .(proj₂ s) (p ∷ P) s x₁ | yes refl = refl
stateMemWeak a (p ∷ P) s x₁ | no ¬p = x₁

{- Doesn't work with older versions of Agda
test28 : (a : R) -> (p : NPred) -> (x : (Polarity × R)) ->  a ∈S p -> a ∈S (x ∷ p)
test28 a (x₂ ∷ p) x x₁ with proj₂ x ≟ a
test28 .(proj₂ x) (x₂ ∷ p) x x₁ | yes refl = refl
test28 a (x₂ ∷ p) x x₁ | no ¬p = x₁ -}

-- Helper proof for ProofSubIn
membershipHelper : (a : R) -> (z : Polarity) -> (S : State) -> (z , a) ∈ S -> a ∈S S
membershipHelper a z .((z ↝ a) ∷ _) (here refl) = subProofHelp a z _
membershipHelper a z (s ∷ S) (there x) = stateMemWeak a S s (membershipHelper a z S x)

-- Is P is a subtype of Q and some predicate, a, is in P then it will also be in Q
ProofSubIn :  (a : R) -> (P : State) -> (Q : State) -> P <: Q -> a ∈S P -> a ∈S Q
ProofSubIn a [] Q x ()
ProofSubIn a ((z1 ↝ a1) ∷ P) Q (atom<: x₂ x) x₁ with a1 ≟ a
ProofSubIn .a1 ((z1 ↝ a1) ∷ P) Q (atom<: x₂ x) refl | yes p₁ = membershipHelper a1 z1 Q x₂
ProofSubIn a ((z1 ↝ a1) ∷ P) Q (atom<: x₂ x) x₁ | no ¬p = ProofSubIn a P Q x x₁

-- If P is a subtype of Q and some predicate, a, is not in Q then it will also not be in P
proofSub : (a : R) -> (P : State) -> (Q : State) -> P <: Q -> a ∉S Q -> a ∉S P
proofSub a [] Q x x₁ ()
proofSub a (p ∷ P) Q x x₁ x₂ with proj₂ p ≟ a
proofSub .(proj₂ p) (p ∷ P) Q x x₁ refl | yes p₁ = x₁ (ProofSubIn (proj₂ p) ((p ∷ P)) Q x (subProofHelp ((proj₂ p)) (proj₁ p) P))
proofSub a (p ∷ P) Q x x₁ x₂ | no ¬p = proofSub a P Q (weakSub p P Q x) x₁ x₂

-- If a predicate, a, is not in Q and a predMap containing a is in P then that predMap will still exist after P is overriden by Q
predMapMembership : (Γ₁ : Γ) ->  (f₁ : Action) -> (z : Polarity) -> (a : R) -> (P : State) -> (Q : State) -> a ∉S Q -> (z , a) ∈ (((z , a) ∷ P) ⊔N Q)
predMapMembership Γ₁ f₁ z a P [] x = here refl
predMapMembership Γ₁ f₁ z a P (q ∷ Q) x with proj₂ q ≟ a
predMapMembership Γ₁ f₁ z .(proj₂ q) P (q ∷ Q) x | yes refl = ⊥-elim (x refl)
predMapMembership Γ₁ f₁ z a P (q ∷ Q) x | no ¬p = there (predMapMembership Γ₁ f₁ z a ((del (proj₂ q) P)) Q x) --recursive case came through by changing ∈S to match del

-- If a predicate, a, is not in Q and a predMap containing a is in P then that predMap will be a subtype of P overriden by Q
predMapPreservation : (Γ₁ : Γ) ->  (f₁ : Action) -> (P : State) -> (Q : State) -> (s : PredMap) -> proj₂ s ∉S Q -> s ∷ [] <: ((s ∷ P) ⊔N Q)
predMapPreservation Γ₁ f₁ P Q s x₁ = atom<: (predMapMembership Γ₁ f₁ (proj₁ s) (proj₂ s) P Q x₁) ([]<: ((s ∷ P) ⊔N Q))

-- If a predicate is not in Q and a PredMap, s, containing that predicate in P and we have a world which satisfies P overriden by Q then the PredMap s is satisfied in that world
framePreservation : ∀{f₁ w P s} -> (Γ₁ : Γ) -> (σ : ActionHandler) -> (Q : State) -> proj₂ s ∉S Q -> σ f₁ w ∈⟨ (s ∷ P) ⊔N Q ⟩ -> σ f₁ w ∈⟨ (s ∷ []) ⟩
framePreservation {f₁} {w} {P} {s} Γ₁ σ Q s∉Sq res = <:-resp-∈ (predMapPreservation Γ₁ f₁ P Q s s∉Sq) res

-- If we have derived two results from the same action then we can combine them since they both represents smaller portions of the world
strength : ∀{f₁ w Q } -> (s : PredMap) -> (σ : ActionHandler) -> σ f₁ w ∈⟨ Q ⟩ ->  σ f₁ w ∈⟨ (s ∷ []) ⟩ -> σ f₁ w ∈⟨ s ∷ Q ⟩
strength {f₁} {w} {Q} x σ x₁ x₂ = (λ { a (here px) → proj₁ x₂ a (here px) ; a (there x₃) → proj₁ x₁ a x₃})
                             ↝ λ { a (here px) x₄ → proj₂ x₂ a (here px) x₄ ; a (there x₃) x₄ → proj₂ x₁ a x₃ x₄}


---------------------------------------------------------------
--  Soundness of evaluation of normalised formula
--


sound : ∀{w σ p Γ fs q}
      → WfHandler Γ σ
      → Γ , p ↝ q ¦ fs
      → w ∈⟨ p ⟩
      → ⟦ fs ⟧ σ w ∈⟨ q ⟩
sound  {w} {σ} {p} {Γ} {fs} {q} WfH  (weakening p1 x₁ x₂ x) w∈⟨P⟩ with sound WfH x (<:-resp-∈ x₁ w∈⟨P⟩) 
... | ans = ans
sound {w} {σ} {p} {Γ} {fs} {q} WfH (applyAction vp vq) w∈⟨P⟩ = wellFormedApplication σ w Γ _ WfH vp vq w∈⟨P⟩
sound WfH (composition Q'<:Q Γ₁,P↝Q¦fs Γ₁,Q'↝R¦actf') w∈⟨P⟩ = sound WfH Γ₁,Q'↝R¦actf' (<:-resp-∈ Q'<:Q (sound WfH Γ₁,P↝Q¦fs w∈⟨P⟩))
--with sound WfH Γ₁,P↝Q¦fs w∈⟨P⟩
--... | ans = sound WfH Γ₁,Q'↝R¦actf' (<:-resp-∈ Q'<:Q ans)
sound {w} {σ} {p} {Γ} {fs} {q} WfH (frame {Γ₁} {p₁} {q₁} {f₁} z a x₁ x₃ x₄) x₂ =  strength (z ↝ a) σ
                                                                                  (sound WfH x₄ (<:-resp-∈ (<:atom p₁ p₁ (z ↝ a) (reflSub p₁)) x₂)) --(weakHelp w (z , a) p₁ x₂))
                                                                                  (framePreservation Γ σ (proj₂ (Γ f₁))
                                                                                    (proofSub a (proj₂ (Γ f₁)) q₁ (postSatQ Γ₁ p₁ q₁ f₁ x₄) x₃)
                                                                                    (WfH (preSatP Γ p q f₁ (frame z a x₁ x₃ x₄)) x₂)) 
sound {w} {σ} {p} {Γ} {fs} {.Q'} WfH (halt Q' x x₁ x₂) x₃ = <:-resp-∈ x₁ (sound WfH x₂ x₃)



---------------------------------------------------------------
--  Soundness of evaluation
--

_↓₊ : Form → State
P ↓₊ = P ↓[ + ] []


sound' : ∀{Γ fs P Q σ}
       → WfHandler Γ σ
       → Γ , (P ↓₊) ↝ (Q ↓₊) ¦ fs
       → ∀{w} → w ⊨[ + ] P
       → ⟦ fs ⟧ σ w ⊨[ + ] Q
sound' {Γ}{f}{P}{Q}{σ} wfσ Γ⊢f∶P↓₊↝Q↓₊ {w} w⊨₊P = ↓-sound h
  where h : ⟦ f ⟧ σ w ∈⟨ Q ↓₊ ⟩
        h = sound wfσ Γ⊢f∶P↓₊↝Q↓₊ (↓-complete w⊨₊P)

-----------------------------------------------------------------------
-- Introduces Well-Formed Canonical Handler

remove : R → World → World
remove x [] = []
remove x (y ∷ w) with x ≟ y
remove x (y ∷ w) | yes p = remove x w
remove x (y ∷ w) | no ¬p = y ∷ remove x w

remove-other : ∀{w x} → x ∈ w → ∀{y} → x ≢ y → x ∈ remove y w
remove-other {[]}    x∈w x≢y = x∈w
remove-other {z ∷ w} x∈w {y} x≢z with y ≟ z
remove-other {z ∷ w} (here _≡_.refl) {y} x≢z | yes p = ⊥-elim (x≢z (IsEquivalence.sym (IsDecEquivalence.isEquivalence isDE) p))
remove-other {z ∷ w} (there x∈w) {y} x≢z | yes p = remove-other x∈w x≢z
remove-other {z ∷ w} (here px) {y} x≢z | no ¬p = here px
remove-other {z ∷ w} (there x∈w) {y} x≢z | no ¬p = there (remove-other x∈w x≢z)

remove-spec : (x : R) (w : World) → x ∉ remove x w
remove-spec x [] = λ ()
remove-spec x (y ∷ w) with  x ≟ y
remove-spec x (y ∷ w) | yes p = remove-spec x w
remove-spec x (y ∷ w) | no ¬p = contr
  where
    contr : x ∉ y ∷ remove x w
    contr (here x≡y) = ¬p x≡y
    contr (there x∈) = remove-spec x w x∈

-- World constructor from state
σα : State → World → World
σα [] w = w
σα ((+ , x) ∷ N) w = x ∷ σα N w
σα ((- , x) ∷ N) w = remove x (σα N w)

-- Canonical Handler
canonical-σ : Γ → ActionHandler
canonical-σ Γ α = σα (proj₂ (Γ α))

---------------------------------------------------------------

∉-tail : {A : Set} {xs : List A} {x y : A} → x ∉ y ∷ xs → x ∉ xs
∉-tail x∉y∷ys x∈ys = x∉y∷ys (there x∈ys)

remove-resp-∈ : ∀{N x y} → x ∈ remove y N → x ∈ N
remove-resp-∈ {[]}    x∈ = x∈
remove-resp-∈ {z ∷ N}{x}{y} x∈ with y ≟ z
remove-resp-∈ {z ∷ N}{x}{y} x∈ | yes refl = there (remove-resp-∈ {N} x∈)
remove-resp-∈ {z ∷ N} {x} {y} (here refl) | no y≢x = here _≡_.refl
remove-resp-∈ {z ∷ N} {x} {y} (there x∈)  | no y≢x = there (remove-resp-∈ x∈)

remove-resp-∉ : ∀{N x} → x ∉ N → ∀{y} → x ∉ remove y N
remove-resp-∉ {[]}    x∉N x∈N' = x∉N x∈N'
remove-resp-∉ {x ∷ N} x∉N {y} x∈N' with y ≟ x
remove-resp-∉ {x ∷ N} x∉N {.x} x∈N' | yes refl = remove-resp-∉ (∉-tail x∉N) x∈N'
remove-resp-∉ {x ∷ N} x∉N {y} (here refl)  | no x≢y = x∉N (here _≡_.refl)
remove-resp-∉ {x ∷ N} x∉N {y} (there x∈N') | no x≢y = remove-resp-∉ (∉-tail x∉N) x∈N'

sym≢ : {A : Set} → {x y : A} → x ≢ y → y ≢ x
sym≢ x≢y refl = x≢y _≡_.refl

postulate
  implicit-consistency-assumption : (t : Polarity) (x : R) → ∀ N → (t , x) ∈ N → (neg t , x) ∉ N

σα-insert : ∀{N x} → (+ , x) ∈ N → ∀ w → x ∈ σα N w
σα-insert {.(_ ∷ _)} (here refl) w = here _≡_.refl
σα-insert {(- , y) ∷ N}{x} (there +x∈N) w with y ≟ x
σα-insert {(- , y) ∷ N}{.y} (there +y∈N) w | yes refl = ⊥-elim (implicit-consistency-assumption - y ((- , y) ∷ N) (here _≡_.refl) (there +y∈N))
σα-insert {(- , y) ∷ N}{x} (there +x∈N)  w | no y≢x = remove-other (σα-insert +x∈N w) (sym≢ y≢x)
σα-insert {(+ , y) ∷ N}{x} (there +x∈N) w with y ≟ x
σα-insert {(+ , y) ∷ N}{.y} (there +x∈N) w | yes refl = here _≡_.refl
σα-insert {(+ , y) ∷ N}{x} (there +x∈N)  w | no y≢x = there (σα-insert +x∈N w)

σα-keep : ∀{x w} → x ∈ w → ∀{N} → (- , x) ∉ N → x ∈ σα N w
σα-keep     x∈w {[]}          -x∉N  = x∈w
σα-keep {x} x∈w {(+ , y) ∷ N} -ty∉N = there (σα-keep x∈w (∉-tail -ty∉N))
σα-keep {x} x∈w {(- , y) ∷ N} -ty∉N with x ≟ y
σα-keep {x} x∈w {(- , .x) ∷ N} -ty∉N | yes refl = ⊥-elim (-ty∉N (here _≡_.refl))
σα-keep {x} x∈w {(- , y) ∷ N} -ty∉N  | no x≢y = remove-other (σα-keep x∈w (∉-tail -ty∉N)) x≢y

σα-delete : ∀{x N} → (- , x) ∈ N → ∀ w → x ∉ σα N w
σα-delete {x}{[]}    () w
σα-delete {x}{y ∷ N} (here refl) w = remove-spec x (σα N w)
σα-delete {x} {(+ , y) ∷ N} (there -x∈N) w with y ≟ x
σα-delete {x} {(+ , y) ∷ N} (there -x∈N) w | yes refl = ⊥-elim (implicit-consistency-assumption + y ((+ , y) ∷ N) (here _≡_.refl) (there -x∈N))
σα-delete {x} {(+ , y) ∷ N} (there -x∈N) w | no y≢x = contr where
  contr : x ∉ y ∷ σα N w
  contr (here x≡y) = y≢x (Relation.Binary.PropositionalEquality.sym x≡y)
  contr (there x∈) = σα-delete -x∈N w x∈
σα-delete {x} {(- , y) ∷ N} (there -x∈N) w = remove-resp-∉ (σα-delete -x∈N w) {y}

σα-source : ∀{N x w} → x ∈ σα N w → (+ , x) ∈ N ⊎ x ∈ w
σα-source {[]}          {x} x∈ = inj₂ x∈
σα-source {(+ , y) ∷ N} {x} x∈ with x ≟ y
σα-source {(+ , .x) ∷ N} {x}{w} x∈ | yes refl = inj₁ (here  _≡_.refl)
σα-source {(+ , y) ∷ N}  {x}{w} (here refl) | no y≢y = ⊥-elim (y≢y _≡_.refl)
σα-source {(+ , y) ∷ N}  {x}{w} (there x∈)  | no x≢y = h (σα-source x∈) where
  h : (+ , x) ∈ N ⊎ x ∈ w → (+ , x) ∈ (+ , y) ∷ N ⊎ x ∈ w
  h (inj₁ +x∈N) = inj₁ (there +x∈N)
  h (inj₂ x∈w) = inj₂ x∈w
σα-source {(- ,  y) ∷ N} {x} x∈ with x ≟ y
σα-source {(- , .x) ∷ N} {x}{w} x∈ | yes refl = ⊥-elim (remove-spec x (σα N w) x∈)
σα-source {(- ,  y) ∷ N} {x}{w} x∈ | no x≢y = h (σα-source (remove-resp-∈ x∈)) where
  h : (+ , x) ∈ N ⊎ x ∈ w → (+ , x) ∈ (- , y) ∷ N ⊎ x ∈ w
  h (inj₁ +x∈N) = inj₁ (there +x∈N)
  h (inj₂ x∈w)  = inj₂ x∈w

σα-keep-∉ : ∀{x w} → x ∉ w → ∀{N} → (+ , x) ∉ N → x ∉ σα N w
σα-keep-∉        x∉w {[]}          +x∉N x∈w = x∉w x∈w
σα-keep-∉ {x}{w} x∉w {(+ , y) ∷ N} +x∉N (here refl) = +x∉N (here _≡_.refl)
σα-keep-∉ {x}{w} x∉w {(+ , y) ∷ N} +x∉N (there x∈) = σα-keep-∉ x∉w (∉-tail +x∉N) x∈
σα-keep-∉ {x}{w} x∉w {(- , y) ∷ N} +x∉N x∈ with x ≟ y
σα-keep-∉ {x}{w} x∉w {(- , .x) ∷ N} +x∉N x∈ | yes refl = remove-spec x (σα N w) x∈
σα-keep-∉ {x}{w} x∉w {(- , y) ∷ N}  +x∉N x∈ | no x≢y = h (σα-source (remove-resp-∈ x∈)) where
  h : (+ , x) ∈ N ⊎ x ∈ w → ⊥
  h (inj₁ +x∈N) = +x∉N (there +x∈N)
  h (inj₂ x∈w)  = x∉w x∈w


⊔-union : ∀{N t x M} → (t , x) ∈ M ⊔N N → (t , x) ∈ M × (neg t , x) ∉ N ⊎ (t , x) ∈ N
⊔-union {[]} x∈M = inj₁ (x∈M , λ ())
⊔-union {x ∷ N} (here refl)   = inj₂ (here _≡_.refl)
⊔-union {x ∷ N}{t}{y}{M} (there x∈M⊔N) = h (⊔-union {N}{t}{y} x∈M⊔N)
  where h : (t , y) ∈ del (proj₂ x) M × (neg t , y) ∉ N ⊎ (t , y) ∈ N → (t , y) ∈ M × (neg t , y) ∉ x ∷ N ⊎ (t , y) ∈ x ∷ N
        h (inj₁ (ty∈ , -ty∉N)) = inj₁ (del-∈ ty∈ , h') where
          h' : (neg t , y) ∉ x ∷ N
          h' (here refl) = del-spec t y M ty∈
          h' (there -ty∈N) = -ty∉N -ty∈N
        h (inj₂ pf) = inj₂ (there pf)


wf-canonical-σ : ∀ Γ → WfHandler Γ (canonical-σ Γ)
wf-canonical-σ Γ {α} {M} M'<:M {w} w∈⟨M⟩ =
  (λ a +a∈M → lt a (⊔-union +a∈M)) ,
  λ a -a∈M a∈w → rt a (⊔-union -a∈M) a∈w
  where lt : ∀ x → (+x∈M⊎N : (+ , x) ∈ M × (- , x) ∉ proj₂ (Γ α) ⊎ (+ , x) ∈ proj₂ (Γ α)) → x ∈ canonical-σ Γ α w
        lt x (inj₁ (+x∈M , -x∉N)) = σα-keep (proj₁ w∈⟨M⟩ x +x∈M) -x∉N
        lt x (inj₂ +x∈N) = σα-insert +x∈N w
        rt : ∀ x → (+x∈M⊎N : (- , x) ∈ M × (+ , x) ∉ proj₂ (Γ α) ⊎ (- , x) ∈ proj₂ (Γ α)) → x ∉ canonical-σ Γ α w
        rt x (inj₁ (-x∈M , +x∉N)) = σα-keep-∉ (proj₂ w∈⟨M⟩ x -x∈M) +x∉N
        rt x (inj₂ -x∈N) = σα-delete -x∈N w 

--------------------------------------------------------------------------------------------------------------





