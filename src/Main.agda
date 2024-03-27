module Main where

open import ARM using (arm_[_]_) renaming (Execution to Executionᵃʳᵐ; Event to Eventᵃʳᵐ; Relation to Relationᵃʳᵐ)
open import RA using (ra_[_]_) renaming (Execution to Executionʳᵃ)
open import Data.Fin using (Fin; _≟_)
open import Data.List using (List; foldr; zip; allFin; length; lookup; findᵇ; tabulate; [_])
open import Data.List.NonEmpty using (List⁺; toList; _∷_) renaming (length to length⁺)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; suc; _<′_)
open import Data.Nat.Induction using (<′-wellFounded)
open import Data.Product using (_×_; _,_; uncurry)
open import Data.Sum using (inj₁; inj₂)
open import Function using (case_of_; _∘_; id)
open import Level using (Level; 0ℓ)
open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality using (_≡_; subst; sym; inspect)
open import Relation.Nullary using (no; yes)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Induction.WellFounded using (WellFounded; Acc)

open Relationᵃʳᵐ
open Fin
open ℕ
open List
open Executionᵃʳᵐ
open _≡_
open Acc

record IR (xs : List⁺ Eventᵃʳᵐ) : Set where
  constructor ir_[_]_
  field
    events : List (Fin (length⁺ xs))
    initial : List (Fin (length⁺ xs))
    relations : List (Relationᵃʳᵐ xs)

index : (xs : List Eventᵃʳᵐ) → List (Fin (length xs) × Eventᵃʳᵐ)
index xs = zip (allFin (length xs)) xs

index⁺ : (xs : List⁺ Eventᵃʳᵐ) → List (Fin (length⁺ xs) × Eventᵃʳᵐ)
index⁺ xs = index (toList xs)

hlength : (xs : List Eventᵃʳᵐ) → length (index xs) ≡ length xs
hlength xs = helper xs id
  where
  helper : {ℓ₁ ℓ₂ : Level} → {α : Set ℓ₁} → {β : Set ℓ₂} → (xs : List α) → (f : Fin (length xs) → β) → length (zip (tabulate f) xs) ≡ length xs
  helper [] f = refl
  helper (_ ∷ xs) f with helper xs (f ∘ suc)
  ... | h = subst (λ test → suc test ≡ suc (length xs)) (sym h) refl

-- diff : {n : ℕ} → List (Fin n) → List (Fin n) → ℕ
-- diff [] ys = zero
-- diff (x ∷ xs) ys with findᵇ (λ current → ⌊ current ≟ x ⌋) ys
-- ... | just _ = diff xs ys
-- ... | nothing = suc (diff xs ys)

-- _<_ : {n : ℕ} → Rel (List (Fin n) × List (Fin n)) 0ℓ
-- (xs₁ , ys₁) < (xs₂ , ys₂) = diff xs₁ ys₁ <′ diff xs₂ ys₂

-- <-wf : {n : ℕ} → WellFounded (_<_ {n = n})
-- <-wf (xs , ys) = acc<′⇒acc< (<′-wellFounded (diff xs ys))
--   where
--     acc<′⇒acc< : {n : ℕ} → {xs : (List (Fin n) × List (Fin n))} → Acc _<′_ ((uncurry diff) xs) → Acc _<_ xs
--     acc<′⇒acc< (acc h) = acc λ hlt → acc<′⇒acc< (h hlt)

{-# TERMINATING #-}
compute-initial : {eventsᵃʳᵐ : List⁺ Eventᵃʳᵐ} → {relationsᵃʳᵐ : List (Relationᵃʳᵐ eventsᵃʳᵐ)} → {eventsʳᵃ : List (Fin (length⁺ eventsᵃʳᵐ))} → Fin (length⁺ eventsᵃʳᵐ) → List (Fin (length⁺ eventsᵃʳᵐ)) → List (Fin (length⁺ eventsᵃʳᵐ))
compute-initial {eventsᵃʳᵐ} {relationsᵃʳᵐ} {eventsʳᵃ} i visited with findᵇ (λ x → ⌊ x ≟ i ⌋) visited
... | just _ = []
... | nothing with lookup (index⁺ eventsᵃʳᵐ) (subst Fin (sym (hlength ((toList eventsᵃʳᵐ)))) i)
...   | i , inj₁ _ = [ i ]
...   | i , inj₂ _ = helper i (i ∷ visited) relationsᵃʳᵐ
  where
  helper : Fin (length⁺ eventsᵃʳᵐ) → List (Fin (length⁺ eventsᵃʳᵐ)) → List (Relationᵃʳᵐ eventsᵃʳᵐ) → List (Fin (length⁺ eventsᵃʳᵐ))
  helper i visited [] = []
  helper i visited (po from to ∷ es) with from ≟ i
  ... | no _ = helper i visited es
  ... | yes _ with findᵇ (λ x → ⌊ x ≟ to ⌋) eventsʳᵃ
  ...   | just _ = to ∷ helper i visited es
  ...   | nothing = compute-initial {eventsᵃʳᵐ} {relationsᵃʳᵐ} {eventsʳᵃ} to visited
  helper i visited (rf from to _ ∷ es) with from ≟ i
  ... | no _ = helper i visited es
  ... | yes _ with findᵇ (λ x → ⌊ x ≟ to ⌋) eventsʳᵃ
  ...   | just _ = to ∷ helper i visited es
  ...   | nothing = compute-initial {eventsᵃʳᵐ} {relationsᵃʳᵐ} {eventsʳᵃ} to visited
  helper i visited (mo from to _ ∷ es) with from ≟ i
  ... | no _ = helper i visited es
  ... | yes _ with findᵇ (λ x → ⌊ x ≟ to ⌋) eventsʳᵃ
  ...   | just _ = to ∷ helper i visited es
  ...   | nothing = compute-initial {eventsᵃʳᵐ} {relationsᵃʳᵐ} {eventsʳᵃ} to visited
  helper i visited (fr from to _ ∷ es) with from ≟ i
  ... | no _ = helper i visited es
  ... | yes _ with findᵇ (λ x → ⌊ x ≟ to ⌋) eventsʳᵃ
  ...   | just _ = to ∷ helper i visited es
  ...   | nothing = compute-initial {eventsᵃʳᵐ} {relationsᵃʳᵐ} {eventsʳᵃ} to visited
  helper i visited (rmw from to _ ∷ es) with from ≟ i
  ... | no _ = helper i visited es
  ... | yes _ with findᵇ (λ x → ⌊ x ≟ to ⌋) eventsʳᵃ
  ...   | just _ = to ∷ helper i visited es
  ...   | nothing = compute-initial {eventsᵃʳᵐ} {relationsᵃʳᵐ} {eventsʳᵃ} to visited

translate : (arm : Executionᵃʳᵐ) → IR (events arm)
translate (arm eventsᵃʳᵐ [ initialᵃʳᵐ ] relationsᵃʳᵐ) = ir eventsʳᵃ [ compute-initial {eventsᵃʳᵐ} {relationsᵃʳᵐ} {eventsʳᵃ} initialᵃʳᵐ [] ] {!   !}
  where
  mapEvents : (xs : List (Fin (length⁺ eventsᵃʳᵐ) × Eventᵃʳᵐ)) → List (Fin (length⁺ eventsᵃʳᵐ))
  mapEvents [] = []
  mapEvents ((i , inj₁ _) ∷ xs) = i ∷ mapEvents xs
  mapEvents (_ ∷ xs) = mapEvents xs

  eventsʳᵃ : List (Fin (length⁺ eventsᵃʳᵐ))
  eventsʳᵃ = mapEvents (index⁺ eventsᵃʳᵐ)
