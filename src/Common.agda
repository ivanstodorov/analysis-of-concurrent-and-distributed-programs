{-# OPTIONS --without-K --safe #-}
module Common where

open import Data.Bool using (Bool)
open import Data.Fin using (Fin)
open import Data.List using (List; length; allFin)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_)
open import Data.String using (String)
open import Data.Vec using (Vec; fromList; zip) renaming (allFin to allFinᵛ; length to lengthᵛ)
open import Function using (case_of_)
open import Level using (0ℓ)
open import Relation.Binary using (Rel)
open import Relation.Binary.Definitions using (Decidable)
open import Relation.Nullary using (no; yes)

open Bool
open List
open Vec

data MemoryAccess : Set where
  read : MemoryAccess
  write : MemoryAccess

record Event : Set where
  constructor _▷_＝_
  field
    type : MemoryAccess
    location : String
    value : ℕ

behavior : (es : List Event) → (r : Rel (Fin (length es)) 0ℓ) → ⦃ Decidable r ⦄ → List (String × ℕ)
behavior es _ ⦃ r-dec ⦄ = behavior' (zip (allFinᵛ (lengthᵛ esᵛ)) esᵛ)
  where
  esᵛ : Vec Event (length es)
  esᵛ = fromList es

  helper : Fin (length es) → List (Fin (length es)) → Bool
  helper _ [] = true
  helper i (j ∷ js) with r-dec i j
  ... | no _ = helper i js
  ... | yes _ = false

  behavior' : {n : ℕ} → Vec (Fin (length es) × Event) n → List (String × ℕ)
  behavior' [] = []
  behavior' ((_ , (read ▷ _ ＝ _)) ∷ es₁) = behavior' es₁
  behavior' ((i , (write ▷ l ＝ v)) ∷ es₁) with helper i (allFin (length es))
  ... | false = behavior' es₁
  ... | true = (l , v) ∷ behavior' es₁
