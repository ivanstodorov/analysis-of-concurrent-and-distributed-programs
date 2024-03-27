module RA where

open import Data.Fin using (Fin)
open import Data.List using (List; lookup)
open import Data.List.NonEmpty using (List⁺; toList; length)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_; Σ-syntax)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_)

data MemoryAccessType : Set where
  read : MemoryAccessType
  write : MemoryAccessType
  update : MemoryAccessType

record MemoryAccess : Set where
  constructor _▷_＝_
  field
    type : MemoryAccessType
    location : String
    value : ℕ

open MemoryAccess

Event : Set
Event = MemoryAccess

data Relation (events : List⁺ Event) : Set where
  po : Fin (length events) → Fin (length events) → Relation events
  rf : (from : Fin (length events)) → (to : Fin (length events)) → (Σ[ (location , value) ∈ String × ℕ ] (lookup (toList events) from ≡ write ▷ location ＝ value) × (lookup (toList events) to ≡ read ▷ location ＝ value)) → Relation events
  mo : (from : Fin (length events)) → (to : Fin (length events)) → (Σ[ location ∈ String ] (Σ[ value ∈ ℕ ] lookup (toList events) from ≡ write ▷ location ＝ value) × (Σ[ value ∈ ℕ ] lookup (toList events) to ≡ write ▷ location ＝ value)) → Relation events
  fr  : (from : Fin (length events)) → (to : Fin (length events)) → (Σ[ location ∈ String ] (Σ[ value ∈ ℕ ] lookup (toList events) from ≡ read ▷ location ＝ value) × (Σ[ value ∈ ℕ ] lookup (toList events) to ≡ write ▷ location ＝ value)) → Relation events
  rmw : (from : Fin (length events)) → (to : Fin (length events)) → (Σ[ (location , value) ∈ String × ℕ ] (lookup (toList events) from ≡ read ▷ location ＝ value) × (lookup (toList events) to ≡ write ▷ location ＝ value)) → Relation events

record Execution : Set where
  constructor ra_[_]_
  field
    events : List⁺ Event
    initial : List (Fin (length events))
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
