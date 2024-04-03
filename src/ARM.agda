module ARM where

open import Data.Bool using (Bool; T)
open import Data.Empty using (⊥)
open import Data.Fin using (Fin)
open import Data.List using (List; length; lookup; allFin)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_; Σ-syntax)
open import Data.String using (String; _==_)
open import Data.Vec using (Vec; fromList; zip) renaming (allFin to allFinᵛ; length to lengthᵛ)
open import Function using (flip; _∘₂_; case_of_)
open import Level using (0ℓ)
open import Relation.Binary.Construct.Closure.Transitive using (TransClosure)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star)
open import Relation.Binary.Construct.Composition using (_;_)
open import Relation.Binary.Construct.Never using (Never)
open import Relation.Binary.Construct.Intersection using (_∩_)
open import Relation.Binary.Construct.Union using (_∪_)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Definitions using (Irreflexive)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (¬_)

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

open Event

record Execution : Set where
  constructor arm_[_．_．_．_]
  field
    es : List Event
    poᵇ : Fin (length es) → Fin (length es) → Bool
    rfᵇ : Fin (length es) → Fin (length es) → Bool
    moᵇ : Fin (length es) → Fin (length es) → Bool
    rmwᵇ : Fin (length es) → Fin (length es) → Bool

behavior : Execution → List (String × ℕ)
behavior arm es [ poᵇ ． rfᵇ ． moᵇ ． rmwᵇ ] = let esᵛ = fromList es in check (zip (allFinᵛ (lengthᵛ esᵛ)) esᵛ)
  where
  check : {n : ℕ} → Vec (Fin (length es) × Event) n → List (String × ℕ)
  check [] = []
  check ((_ , (read ▷ _ ＝ _)) ∷ es₁) = check es₁
  check ((i , (write ▷ l ＝ v)) ∷ es₁) = case check' i (allFin (length es)) of λ { false → check es₁ ; true → (l , v) ∷ check es₁ }
    where
    check' : Fin (length es) → List (Fin (length es)) → Bool
    check' i [] = true
    check' i (j ∷ js) with moᵇ i j
    ... | false = check' i js
    ... | true = false

isConsistent : Execution → Set
isConsistent arm es [ poᵇ ． rfᵇ ． moᵇ ． rmwᵇ ] = Coh × sc-per-loc × atomicity
  where
  po : Rel (Fin (length es)) 0ℓ
  po = T ∘₂ poᵇ

  poloc : Rel (Fin (length es)) 0ℓ
  poloc i j with location (lookup es i) == location (lookup es i)
  ... | false = ⊥
  ... | true = po i j

  rf : Rel (Fin (length es)) 0ℓ
  rf = T ∘₂ rfᵇ

  rfe : Rel (Fin (length es)) 0ℓ
  rfe i j with poᵇ i j
  ... | false = rf i j
  ... | true = ⊥

  mo : Rel (Fin (length es)) 0ℓ
  mo = T ∘₂ moᵇ

  moe : Rel (Fin (length es)) 0ℓ
  moe i j with poᵇ i j
  ... | false = mo i j
  ... | true = ⊥

  fr : Rel (Fin (length es)) 0ℓ
  fr = rf⁻¹ ; mo
    where
    rf⁻¹ : Rel (Fin (length es)) 0ℓ
    rf⁻¹ = flip rf

  fre : Rel (Fin (length es)) 0ℓ
  fre i j with poᵇ i j
  ... | false = fr i j
  ... | true = ⊥

  rmw : Rel (Fin (length es)) 0ℓ
  rmw = T ∘₂ rmwᵇ

  bob : Rel (Fin (length es)) 0ℓ
  bob i j with type (lookup es i) | type (lookup es j)
  ... | write | read = ⊥
  ... | _ | _ = po i j

  Coh : Set
  Coh = Irreflexive _≡_ (TransClosure (bob ∪ rfe ∪ moe ∪ fre))

  sc-per-loc : Set
  sc-per-loc = Irreflexive _≡_ (poloc ∪ rf ∪ mo ∪ fr)

  atomicity : Set
  atomicity = ¬ (Σ[ (i , j) ∈ Fin (length es) × Fin (length es) ] (rmw ∩ fr ; mo) i j)
