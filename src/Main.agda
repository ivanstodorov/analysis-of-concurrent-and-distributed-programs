module Main where

open import ARM using (arm_[_．_．_．_]) renaming (MemoryAccess to MemoryAccessᵃʳᵐ; Execution to Executionᵃʳᵐ; isConsistent to isConsistentᵃʳᵐ; behavior to behaviorᵃʳᵐ; Event to Eventᵃʳᵐ; _▷_＝_ to _▷ᵃʳᵐ_＝_)
open import RA using (ra_[_．_．_．_]) renaming (MemoryAccess to MemoryAccessʳᵃ; Execution to Executionʳᵃ; isConsistent to isConsistentʳᵃ; behavior to behaviorʳᵃ; Event to Eventʳᵃ; _▷_＝_ to _▷ʳᵃ_＝_)
open import Data.Bool using (Bool; _∧_; T)
open import Data.Fin using (Fin; cast)
open import Data.List using (List; findᵇ; map; length)
open import Data.List.Properties using (length-map)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; _≡ᵇ_)
open import Data.Product using (_×_; _,_; uncurry)
open import Data.String using (String; _==_)
open import Data.Unit using (tt)
open import Function using (_∘₂_)
open import Level using (Level)

open MemoryAccessᵃʳᵐ
open MemoryAccessʳᵃ
open Bool
open List

mapᵉˣ : Executionʳᵃ → Executionᵃʳᵐ
mapᵉˣ ra es [ poᵇ ． rfᵇ ． moᵇ ． rmwᵇ ] = arm map mapᵉ es [ mapʳ es poᵇ ． mapʳ es rfᵇ ． mapʳ es moᵇ ． mapʳ es rmwᵇ ]
  where
  mapᵉ : Eventʳᵃ → Eventᵃʳᵐ
  mapᵉ (read ▷ʳᵃ l ＝ v) = read ▷ᵃʳᵐ l ＝ v
  mapᵉ (write ▷ʳᵃ l ＝ v) = write ▷ᵃʳᵐ l ＝ v

  mapʳ : (es : List Eventʳᵃ) → (Fin (length es) → Fin (length es) → Bool) → Fin (length (map mapᵉ es)) → Fin (length (map mapᵉ es)) → Bool
  mapʳ es r = uncurry r ∘₂ mapⁱ es
    where
    mapⁱ : (es : List Eventʳᵃ) → Fin (length (map mapᵉ es)) → Fin (length (map mapᵉ es)) → Fin (length es) × Fin (length es)
    mapⁱ es i j = cast (length-map mapᵉ es) i , cast (length-map mapᵉ es) j

isSameBehaviour : Executionʳᵃ → Executionᵃʳᵐ → Bool
isSameBehaviour raᵉ armᵉ with behaviorʳᵃ raᵉ | behaviorᵃʳᵐ armᵉ
... | raᵇ | armᵇ = checkMembership raᵇ armᵇ ∧ checkMembership armᵇ raᵇ
  where
  checkMembership : List (String × ℕ) → List (String × ℕ) → Bool
  checkMembership [] ys = true
  checkMembership ((lx , vx) ∷ xs) ys with findᵇ (λ (ly , vy) → (lx == ly) ∧ (vx ≡ᵇ vy)) ys
  ... | just _ = checkMembership xs ys
  ... | nothing = false

theorem : (ra : Executionʳᵃ) → isConsistentᵃʳᵐ (mapᵉˣ ra) → isConsistentʳᵃ ra × T (isSameBehaviour ra (mapᵉˣ ra))
theorem ra es [ poᵇ ． rfᵇ ． moᵇ ． rmwᵇ ] h = {!   !} , {!   !}
