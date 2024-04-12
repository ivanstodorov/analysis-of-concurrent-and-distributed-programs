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

behavior : (es : List Event) → (Fin (length es) → Fin (length es) → Bool) → List (String × ℕ)
behavior es r = behavior' (zip (allFinᵛ (lengthᵛ esᵛ)) esᵛ) r
  where
  esᵛ : Vec Event (length es)
  esᵛ = fromList es

  helper : Fin (length es) → List (Fin (length es)) → Bool
  helper _ [] = true
  helper i (j ∷ js) with r i j
  ... | false = helper i js
  ... | true = false

  behavior' : {n : ℕ} → Vec (Fin (length es) × Event) n → (Fin (length es) → Fin (length es) → Bool) → List (String × ℕ)
  behavior' [] r = []
  behavior' ((_ , (read ▷ _ ＝ _)) ∷ es₁) r = behavior' es₁ r
  behavior' ((i , (write ▷ l ＝ v)) ∷ es₁) r with helper i (allFin (length es))
  ... | false = behavior' es₁ r
  ... | true = (l , v) ∷ behavior' es₁ r
