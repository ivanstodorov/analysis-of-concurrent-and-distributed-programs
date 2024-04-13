{-# OPTIONS --without-K --safe #-}
module ARM where

open import Common using (write; read; Event) renaming (behavior to behaviorᶜ)
open import Data.Bool using (Bool; T)
open import Data.Fin using (Fin)
open import Data.List using (List; length; lookup)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_; Σ-syntax)
open import Data.String using (String)
open import Data.Sum using (_⊎_)
open import Function using (_∘₂_; flip; id)
open import Level using (0ℓ)
open import RA using () renaming (Program to Programʳᵃ)
open import Relation.Binary using (Rel)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star)
open import Relation.Binary.Construct.Closure.Transitive using (TransClosure)
open import Relation.Binary.Construct.Intersection using (_∩_)
open import Relation.Binary.Construct.Union using (_∪_)
open import Relation.Binary.Construct.Composition using (_;_)
open import Relation.Binary.Definitions using (Irreflexive)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)
open import Relation.Nullary using (¬_)
open import Relation.Unary using (Pred)

open Event

Program : Set
Program = List Event

fromRA : Programʳᵃ → Program
fromRA = id

record Execution (p : Program) : Set₁ where
  constructor arm[_．_．_．_]+[_．_]+[_．_]+[_．_．_．_]+[_]
  field
    poᵇ : Fin (length p) → Fin (length p) → Bool
    rfᵇ : Fin (length p) → Fin (length p) → Bool
    moᵇ : Fin (length p) → Fin (length p) → Bool
    rmwᵇ : Fin (length p) → Fin (length p) → Bool

    po-irreflexive : {i j : Fin (length p)} → T (poᵇ i j) → i ≢ j
    po-transitive : {i j k : Fin (length p)} → T (poᵇ i j) → T (poᵇ j k) → T (poᵇ i k)

    rf-consistent : {i j : Fin (length p)} → T (rfᵇ i j) → type (lookup p i) ≡ write × type (lookup p j) ≡ read × location (lookup p i) ≡ location (lookup p j) × value (lookup p i) ≡ value (lookup p j)
    rf-exists-unique : {j : Fin (length p)} → type (lookup p j) ≡ read → Σ[ i ∈ Fin (length p) ] (type (lookup p i) ≡ write × T (rfᵇ i j) × ({x : Fin (length p)} → T (rfᵇ x j) → x ≡ i))

    mo-consistent : {i j : Fin (length p)} →  T (moᵇ i j) → type (lookup p i) ≡ write × type (lookup p j) ≡ write × location (lookup p i) ≡ location (lookup p j)
    mo-irreflexive : {i j : Fin (length p)} → T (moᵇ i j) → i ≢ j
    mo-transitive : {i j k : Fin (length p)} → T (moᵇ i j) → T (moᵇ j k) → T (moᵇ i k)
    mo-total : {i j : Fin (length p)} → type (lookup p i) ≡ write → type (lookup p j) ≡ write → location (lookup p i) ≡ location (lookup p j) → T (moᵇ i j) ⊎ T (moᵇ j i) ⊎ i ≡ j

    rmw-consistent : {i j : Fin (length p)} → T (rmwᵇ i j) → type (lookup p i) ≡ read × type (lookup p j) ≡ write × ¬ (Σ[ x ∈ Fin (length p) ] (T (poᵇ i x) × T (poᵇ x j)))

  po : Rel (Fin (length p)) 0ℓ
  po = T ∘₂ poᵇ

  poloc : Rel (Fin (length p)) 0ℓ
  poloc i j = po i j × location (lookup p i) ≡ location (lookup p j)

  rf : Rel (Fin (length p)) 0ℓ
  rf = T ∘₂ rfᵇ

  rfe : Rel (Fin (length p)) 0ℓ
  rfe i j = rf i j × ¬ po i j

  mo : Rel (Fin (length p)) 0ℓ
  mo = T ∘₂ moᵇ

  moe : Rel (Fin (length p)) 0ℓ
  moe i j = mo i j × ¬ po i j

  rmw : Rel (Fin (length p)) 0ℓ
  rmw = T ∘₂ rmwᵇ

  fr : Rel (Fin (length p)) 0ℓ
  fr = rf⁻¹ ; mo
    where
    rf⁻¹ : Rel (Fin (length p)) 0ℓ
    rf⁻¹ = flip rf

  fre : Rel (Fin (length p)) 0ℓ
  fre i j = fr i j × ¬ po i j

  fʷʷ : Rel (Fin (length p)) 0ℓ
  fʷʷ i j = po i j × type (lookup p i) ≡ write × type (lookup p j) ≡ write

  fʳᵐ : Rel (Fin (length p)) 0ℓ
  fʳᵐ i j = po i j × type (lookup p i) ≡ read

  bob : Rel (Fin (length p)) 0ℓ
  bob = fʷʷ ∪ fʳᵐ

open Execution

behavior : {p : Program} → (ex : Execution p) → List (String × ℕ)
behavior {p} ex = behaviorᶜ p (moᵇ ex)

Coh : {p : Program} → Pred (Execution p) 0ℓ
Coh ex = Irreflexive _≡_ (TransClosure (bob ex ∪ rfe ex ∪ moe ex ∪ fre ex))

sc-per-loc : {p : Program} → Pred (Execution p) 0ℓ
sc-per-loc ex = Irreflexive _≡_ (TransClosure (poloc ex ∪ rf ex ∪ mo ex ∪ fr ex))

atomicity : {p : Program} → Pred (Execution p) 0ℓ
atomicity {p} ex = ¬ (Σ[ (i , j) ∈ Fin (length p) × Fin (length p) ] (rmw ex ∩ fr ex ; mo ex) i j)

isConsistent : {p : Program} → Pred (Execution p) 0ℓ
isConsistent ex = Coh ex × sc-per-loc ex × atomicity ex
