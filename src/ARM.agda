module ARM where

open import Data.Bool using (Bool; T)
open import Data.Fin using (Fin)
open import Data.List using (List; lookup)
open import Data.List.NonEmpty using (List⁺; length; toList)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_; Σ-syntax)
open import Data.String using (String)
open import Data.Sum using (_⊎_; inj₁)
open import Relation.Binary.PropositionalEquality using (_≡_)

data MemoryAccessType : Set where
  read : MemoryAccessType
  write : MemoryAccessType

record MemoryAccess : Set where
  constructor _▷_＝_
  field
    type : MemoryAccessType
    location : String
    value : ℕ

open MemoryAccess

data Fence : Set where
  load : Fence
  store : Fence
  full : Fence

Event : Set
Event = MemoryAccess ⊎ Fence

data Relation (events : List⁺ Event) : Set where
  po  : Fin (length events) → Fin (length events) → Relation events
  rf  : (from : Fin (length events)) → (to : Fin (length events)) → (Σ[ (location , value) ∈ String × ℕ ] (lookup (toList events) from ≡ inj₁ (write ▷ location ＝ value)) × (lookup (toList events) from ≡ inj₁ (read ▷ location ＝ value))) → Relation events
  mo  : (from : Fin (length events)) → (to : Fin (length events)) → (Σ[ location ∈ String ] (Σ[ value ∈ ℕ ] lookup (toList events) from ≡ inj₁ (write ▷ location ＝ value)) × (Σ[ value ∈ ℕ ] lookup (toList events) to ≡ inj₁ (write ▷ location ＝ value))) → Relation events
  fr  : (from : Fin (length events)) → (to : Fin (length events)) → (Σ[ location ∈ String ] (Σ[ value ∈ ℕ ] lookup (toList events) from ≡ inj₁ (read ▷ location ＝ value)) × (Σ[ value ∈ ℕ ] lookup (toList events) to ≡ inj₁ (write ▷ location ＝ value))) → Relation events
  rmw : (from : Fin (length events)) → (to : Fin (length events)) → (Σ[ (location , value) ∈ String × ℕ ] (lookup (toList events) from ≡ inj₁ (read ▷ location ＝ value)) × (lookup (toList events) to ≡ inj₁ (write ▷ location ＝ value))) → Relation events

record Execution : Set where
  constructor arm_[_]_
  field
    events : List⁺ Event
    initial : Fin (length events)
    relations : List (Relation events)

-- isConsistent : Execution → Set
-- isConsistent e = Coh e × sc-per-loc e × atomicity e
--   where
--   Coh : Execution → Set
--   Coh e = {!   !}

--   sc-per-loc : Execution → Set
--   sc-per-loc e = {!   !}

--   atomicity : Execution → Set
--   atomicity e = {!   !}
