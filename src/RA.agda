module RA where

open import Data.Bool using (Bool; _∧_)
open import Data.Fin using (Fin)
open import Data.List using (List; lookup; length)
open import Data.List.NonEmpty using (List⁺; toList) renaming (length to length⁺)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_; Σ-syntax)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_)

open Bool
open List

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

data Relation (events : List Event) : Set where
  po : Fin (length events) → Fin (length events) → Relation events
  rf : (from : Fin (length events)) → (to : Fin (length events)) → (Σ[ (location , value) ∈ String × ℕ ] (lookup events from ≡ write ▷ location ＝ value) × (lookup events from ≡ read ▷ location ＝ value)) → Relation events
  mo : (from : Fin (length events)) → (to : Fin (length events)) → (Σ[ location ∈ String ] (Σ[ value ∈ ℕ ] lookup events from ≡ write ▷ location ＝ value) × (Σ[ value ∈ ℕ ] lookup events to ≡ write ▷ location ＝ value)) → Relation events

record Execution : Set where
  field
    events : List⁺ Event
    relations : List (Relation (toList events))
    initial : Fin (length⁺ events)

isCorrect : Execution → Set
isCorrect e = {!    !}

isConsistent : Execution → Set
isConsistent e = isCorrect e × {!   !} -- Coh (complete e) × sc-per-loc (complete e) × atomicity (complete e)
  -- where

  -- record Execution'

  -- complete : Execution → Execution'

  -- Coh : Execution' → Set
  -- Coh e = ?

  -- sc-per-loc : Execution' → Set
  -- sc-per-loc e = ?

  -- atomicity : Execution' → Set
  -- atomicity e = ?
