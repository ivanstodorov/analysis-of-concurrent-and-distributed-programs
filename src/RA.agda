{-# OPTIONS --without-K --safe #-}
module RA where

open import Common using (write; read; Event) renaming (behavior to behaviorᶜ)
open import Data.Fin using (Fin)
open import Data.List using (List; length; lookup)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_; Σ-syntax)
open import Data.String using (String)
open import Data.Sum using (_⊎_)
open import Function using (_∘₂_; flip)
open import Level using (0ℓ)
open import Relation.Binary using (Rel)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star)
open import Relation.Binary.Construct.Closure.Transitive using (TransClosure)
open import Relation.Binary.Construct.Intersection using (_∩_)
open import Relation.Binary.Construct.Union using (_∪_)
open import Relation.Binary.Construct.Composition using (_;_)
open import Relation.Binary.Definitions using (Decidable; Irreflexive)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)
open import Relation.Nullary using (¬_)
open import Relation.Unary using (Pred)

open Event

Program : Set
Program = List Event

record Execution (p : Program) : Set₁ where
  constructor ra_+_⟪_·_·_⟫_+_⟪_·_⟫_+_⟪_·_·_·_⟫_+_⟪_⟫
  field
    po : Rel (Fin (length p)) 0ℓ
    po-dec : Decidable po

    po-irreflexive : {i j : Fin (length p)} → po i j → i ≢ j
    po-transitive : {i j k : Fin (length p)} → po i j → po j k → po i k
    po-exists-unique : Σ[ j ∈ Fin (length p) ] (∀ {i : Fin (length p)} → ¬ po i j) × ∀ {x : Fin (length p)} → x ≢ j → Σ[ i ∈ Fin (length p) ] po i j

    rf : Rel (Fin (length p)) 0ℓ
    rf-dec : Decidable rf

    rf-consistent : {i j : Fin (length p)} → rf i j → type (lookup p i) ≡ write × type (lookup p j) ≡ read × location (lookup p i) ≡ location (lookup p j) × value (lookup p i) ≡ value (lookup p j)
    rf-exists-unique : {j : Fin (length p)} → type (lookup p j) ≡ read → Σ[ i ∈ Fin (length p) ] rf i j × (∀ {x : Fin (length p)} → rf x j → x ≡ i)

    mo : Rel (Fin (length p)) 0ℓ
    mo-dec : Decidable mo

    mo-consistent : {i j : Fin (length p)} →  mo i j → type (lookup p i) ≡ write × type (lookup p j) ≡ write × location (lookup p i) ≡ location (lookup p j)
    mo-irreflexive : {i j : Fin (length p)} → mo i j → i ≢ j
    mo-transitive : {i j k : Fin (length p)} → mo i j → mo j k → mo i k
    mo-total : {i j : Fin (length p)} → type (lookup p i) ≡ write → type (lookup p j) ≡ write → location (lookup p i) ≡ location (lookup p j) → mo i j ⊎ mo j i ⊎ i ≡ j

    rmw : Rel (Fin (length p)) 0ℓ
    rmw-dec : Decidable rmw

    rmw-consistent : {i j : Fin (length p)} → rmw i j → type (lookup p i) ≡ read × type (lookup p j) ≡ write × po i j × ¬ (Σ[ x ∈ Fin (length p) ] (po i x × po x j))

  poloc : Rel (Fin (length p)) 0ℓ
  poloc i j = po i j × location (lookup p i) ≡ location (lookup p j)

  fr : Rel (Fin (length p)) 0ℓ
  fr = rf⁻¹ ; mo
    where
    rf⁻¹ : Rel (Fin (length p)) 0ℓ
    rf⁻¹ = flip rf

  hb : Rel (Fin (length p)) 0ℓ
  hb = TransClosure (po ∪ rf)

open Execution

behavior : {p : Program} → (ex : Execution p) → List (String × ℕ)
behavior {p} ex = behaviorᶜ p (mo ex) ⦃ mo-dec ex ⦄

Coh : {p : Program} → Pred (Execution p) 0ℓ
Coh ex = Irreflexive _≡_ (hb ex ; Star (rf ex ∪ mo ex ∪ fr ex))

sc-per-loc : {p : Program} → Pred (Execution p) 0ℓ
sc-per-loc ex = Irreflexive _≡_ (TransClosure (poloc ex ∪ rf ex ∪ mo ex ∪ fr ex))

atomicity : {p : Program} → Pred (Execution p) 0ℓ
atomicity {p} ex = ¬ (Σ[ (i , j) ∈ Fin (length p) × Fin (length p) ] (rmw ex ∩ fr ex ; mo ex) i j)

isConsistent : {p : Program} → Pred (Execution p) 0ℓ
isConsistent ex = Coh ex × sc-per-loc ex × atomicity ex
