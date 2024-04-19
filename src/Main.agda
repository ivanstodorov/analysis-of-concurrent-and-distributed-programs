{-# OPTIONS --without-K --safe #-}
module Main where

open import ARM using (Execution'; arm_+_⟪_·_·_⟫_+_⟪_·_⟫_+_⟪_·_·_·_⟫_+_⟪_⟫_⟪_⟫_⟪_⟫_⟪_⟫; ex'→ex; fromRA) renaming (Execution to Executionᵃʳᵐ; behavior to behaviorᵃʳᵐ; Coh to Cohᵃʳᵐ; sc-per-loc to sc-per-locᵃʳᵐ; atomicity to atomicityᵃʳᵐ; isConsistent to isConsistentᵃʳᵐ)
open import Common using (read; write; Event)
open import Data.Bool using (true; false; T)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin)
open import Data.List using (length; lookup)
open import Data.Product using (_×_; _,_; Σ-syntax)
open import Data.String using (_≟_)
open import Data.Sum using (_⊎_)
open import Data.Unit using (tt)
open import Function using (id; case_of_)
open import Level using (0ℓ)
open import RA using (ra_+_⟪_·_·_⟫_+_⟪_·_⟫_+_⟪_·_·_·_⟫_+_⟪_⟫) renaming (Program to Programʳᵃ; Execution to Executionʳᵃ; behavior to behaviorʳᵃ; Coh to Cohʳᵃ; sc-per-loc to sc-per-locʳᵃ; atomicity to atomicityʳᵃ; isConsistent to isConsistentʳᵃ)
open import Relation.Binary using (Rel)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star; _◅◅_)
open import Relation.Binary.Construct.Closure.Transitive using (TransClosure; _∷ʳ_; _++_)
open import Relation.Binary.Construct.Composition using (_;_)
open import Relation.Binary.Construct.Union using (_∪_)
open import Relation.Binary.PropositionalEquality using (_≡_; inspect; [_]; subst; sym; trans)
open import Relation.Nullary using (¬_; no; yes)

open Execution'
open Executionᵃʳᵐ renaming (poloc to polocᵃʳᵐ; rf to rfᵃʳᵐ; rfe to rfeᵃʳᵐ; mo to moᵃʳᵐ; fr to frᵃʳᵐ)
open Event
open _⊎_
open Executionʳᵃ renaming (po to poʳᵃ; poloc to polocʳᵃ; rf to rfʳᵃ; mo to moʳᵃ; fr to frʳᵃ; po-irreflexive to po-irreflexiveʳᵃ)
open Star
open TransClosure
open _≡_

theorem : {p : Programʳᵃ} → (ex : Execution' p) → isConsistentᵃʳᵐ (ex'→ex ex) → Σ[ exʳᵃ ∈ Executionʳᵃ p ] (isConsistentʳᵃ exʳᵃ × behaviorʳᵃ exʳᵃ ≡ behaviorᵃʳᵐ (ex'→ex ex))
theorem ex hᵃʳᵐ = toRA (ex'→ex ex) , (hᶜ ex hᵃʳᵐ , hˢ ex hᵃʳᵐ , hᵃ ex hᵃʳᵐ) , refl
  where
  toRA : {p : Programʳᵃ} → Executionᵃʳᵐ (fromRA p) → Executionʳᵃ p
  toRA arm po + po-dec ⟪ po-irreflexive · po-transitive · po-exists-unique ⟫ rf + rf-dec ⟪ rf-consistent · rf-exists-unique ⟫ mo + mo-dec ⟪ mo-consistent · mo-irreflexive · mo-transitive · mo-total ⟫ rmw + rmw-dec ⟪ rmw-consistent ⟫ _ ⟪ _ ⟫ _ ⟪ _ ⟫ _ ⟪ _ ⟫ = ra po + po-dec ⟪ po-irreflexive · po-transitive · po-exists-unique ⟫ rf + rf-dec ⟪ rf-consistent · rf-exists-unique ⟫ mo + mo-dec ⟪ mo-consistent · mo-irreflexive · mo-transitive · mo-total ⟫ rmw + rmw-dec ⟪ rmw-consistent ⟫

  hᶜ : {p : Programʳᵃ} → (ex : Execution' (fromRA p)) → isConsistentᵃʳᵐ (ex'→ex ex) → Cohʳᵃ (toRA (ex'→ex ex))
  hᶜ ex (cᵃʳᵐ , sᵃʳᵐ , _) heq@refl (k , fst , snd) = case translateʳᵉˢᵗ (toRA (ex'→ex ex)) fst snd of λ { (inj₁ x) → cᵃʳᵐ refl (convertʰᵇ₁ ex x)
                                                                                                        ; (inj₂ (_ , w , x@(_ , y , z))) → cᵃʳᵐ refl (convertʰᵇ₂ ex w x sᵃʳᵐ ++ convertʳᵉˢᵗ ex y z) }
    where
    rfeʳᵃ : {p : Programʳᵃ} → (ex : Executionʳᵃ p) → Rel (Fin (length p)) 0ℓ
    rfeʳᵃ ex i j = rfʳᵃ ex i j × ¬ poʳᵃ ex i j

    translateʳᵉˢᵗ' : {p : Programʳᵃ} → (ex : Executionʳᵃ p) → {w x y z : Fin (length p)} → hb ex w x → Star (rfʳᵃ ex ∪ moʳᵃ ex ∪ frʳᵃ ex) x y → (moʳᵃ ex ∪ frʳᵃ ex) y z → Star (rfʳᵃ ex ∪ moʳᵃ ex ∪ frʳᵃ ex) z w → Σ[ (i , j) ∈ Fin (length p) × Fin (length p) ] (hb ex i j × (Star (rfʳᵃ ex ∪ moʳᵃ ex ∪ frʳᵃ ex) ; (moʳᵃ ex ∪ frʳᵃ ex)) j i)
    translateʳᵉˢᵗ' ex {w = w} {x = x} {y = y} h h' h'' ε = (w , x) , h , y , h' , h''
    translateʳᵉˢᵗ' ex {x = x} {y = y} {z = z} h h' h'' (inj₁ rf ◅ ε) = (z , x) , inj₂ rf ∷ h , y , h' , h''
    translateʳᵉˢᵗ' ex h h' h'' (inj₁ rf₁ ◅ inj₁ rf₂ ◅ h''') with rf-consistent ex rf₁ | rf-consistent ex rf₂
    ... | _ , hr , _ | hw , _ , _ = let h = subst (λ x → x ≡ write) hr hw in case h of λ ()
    translateʳᵉˢᵗ' ex h h' h'' (inj₁ rf ◅ inj₂ x ◅ h''') = translateʳᵉˢᵗ' ex h (h' ◅◅ inj₂ h'' ◅ inj₁ rf ◅ ε) x h'''
    translateʳᵉˢᵗ' ex h h' h'' (inj₂ x ◅ h''') = translateʳᵉˢᵗ' ex h (h' ◅◅ inj₂ h'' ◅ ε) x h'''

    translateʳᵉˢᵗ : {p : Programʳᵃ} → (ex : Executionʳᵃ p) → {i j : Fin (length p)} → hb ex i j → Star (rfʳᵃ ex ∪ moʳᵃ ex ∪ frʳᵃ ex) j i → hb ex i i ⊎ Σ[ (i , j) ∈ Fin (length p) × Fin (length p) ] (hb ex i j × (Star (rfʳᵃ ex ∪ moʳᵃ ex ∪ frʳᵃ ex) ; (moʳᵃ ex ∪ frʳᵃ ex)) j i)
    translateʳᵉˢᵗ _ h ε = inj₁ h
    translateʳᵉˢᵗ _ h (inj₁ rf ◅ ε) = inj₁ (h ∷ʳ inj₂ rf)
    translateʳᵉˢᵗ ex h (inj₁ rf₁ ◅ inj₁ rf₂ ◅ rest) with rf-consistent ex rf₁ | rf-consistent ex rf₂
    ... | _ , hr , _ | hw , _ , _ = let h = subst (λ x → x ≡ write) hr hw in case h of λ ()
    translateʳᵉˢᵗ ex h (inj₁ rf ◅ inj₂ x ◅ rest) = inj₂ (translateʳᵉˢᵗ' ex (h ∷ʳ inj₂ rf) ε x rest)
    translateʳᵉˢᵗ ex h (inj₂ x ◅ rest) = inj₂ (translateʳᵉˢᵗ' ex h ε x rest)

    helper-po : {p : Programʳᵃ} → (ex : Executionʳᵃ p) → {i j : Fin (length p)} → TransClosure (poʳᵃ ex ; rfeʳᵃ ex) i j → type (lookup p j) ≡ read
    helper-po ex [ _ , _ , rf , _ ] with rf-consistent ex rf
    ... | _ , hⱼ , _ , _ = hⱼ
    helper-po ex (_ ∷ h) = helper-po ex h

    translateʰᵇ-po₁ : {p : Programʳᵃ} → (ex : Executionʳᵃ p) → {i j k : Fin (length p)} → TransClosure (poʳᵃ ex ; rfeʳᵃ ex) i j → hb ex j k → (TransClosure (poʳᵃ ex ; rfeʳᵃ ex) ∪ TransClosure (poʳᵃ ex ; rfeʳᵃ ex) ; poʳᵃ ex) i k
    translateʰᵇ-po₂ : {p : Programʳᵃ} → (ex : Executionʳᵃ p) → {w x y z : Fin (length p)} → TransClosure (poʳᵃ ex ; rfeʳᵃ ex) w x → poʳᵃ ex x y → hb ex y z → (TransClosure (poʳᵃ ex ; rfeʳᵃ ex) ∪ TransClosure (poʳᵃ ex ; rfeʳᵃ ex) ; poʳᵃ ex) w z

    translateʰᵇ-po₁ ex {j = j} h [ inj₁ po ] = inj₂ (j , h , po)
    translateʰᵇ-po₁ ex h [ inj₂ rf ] with helper-po ex h | rf-consistent ex rf
    ... | hr | hw , _ , _ , _ = let h = subst (λ x → x ≡ write) hr hw in case h of λ ()
    translateʰᵇ-po₁ ex h (inj₁ po ∷ h') = translateʰᵇ-po₂ ex h po h'
    translateʰᵇ-po₁ ex h (inj₂ rf ∷ _) with helper-po ex h | rf-consistent ex rf
    ... | hr | hw , _ , _ , _ = let h = subst (λ x → x ≡ write) hr hw in case h of λ ()

    translateʰᵇ-po₂ ex {x = x} h h' [ inj₁ po ] = inj₂ (x , h , po-transitive ex h' po)
    translateʰᵇ-po₂ ex {x = x} {y = y} {z = z} h h' [ inj₂ rf ] with po-dec ex y z
    ... | no hⁿ = inj₁ (h ∷ʳ (y , h' , rf , hⁿ))
    ... | yes hʸ = inj₂ (x , h , po-transitive ex h' hʸ)
    translateʰᵇ-po₂ ex h h' (inj₁ po ∷ h'') = translateʰᵇ-po₂ ex h (po-transitive ex h' po) h''
    translateʰᵇ-po₂ ex {x = x} h h' (_∷_ {x = y} {y = z} (inj₂ rf) h'') with po-dec ex y z
    ... | no hⁿ = translateʰᵇ-po₁ ex (h ∷ʳ (y , h' , rf , hⁿ)) h''
    ... | yes hʸ = translateʰᵇ-po₂ ex h (po-transitive ex h' hʸ) h''

    translateʰᵇ-po : {p : Programʳᵃ} → (ex : Executionʳᵃ p) → {i j k : Fin (length p)} → poʳᵃ ex i j → hb ex j k → (poʳᵃ ex ∪ TransClosure (poʳᵃ ex ; rfeʳᵃ ex) ∪ TransClosure (poʳᵃ ex ; rfeʳᵃ ex) ; poʳᵃ ex) i k
    translateʰᵇ-po ex h [ inj₁ po ] = inj₁ (po-transitive ex h po)
    translateʰᵇ-po ex {j = j} {k = k} h [ inj₂ rf ] with po-dec ex j k
    ... | no hⁿ = inj₂ (inj₁ [ j , h , rf , hⁿ ])
    ... | yes hʸ = inj₁ (po-transitive ex h hʸ)
    translateʰᵇ-po ex h (inj₁ po ∷ h') = translateʰᵇ-po ex (po-transitive ex h po) h'
    translateʰᵇ-po ex h (_∷_ {x = x} {y = y} (inj₂ rf ) h') with po-dec ex x y
    ... | yes hʸ = translateʰᵇ-po ex (po-transitive ex h hʸ) h'
    ... | no hⁿ with translateʰᵇ-po₁ ex [ x , h , rf , hⁿ ] h'
    ...   | inj₁ x = inj₂ (inj₁ x)
    ...   | inj₂ y = inj₂ (inj₂ y)

    helper-rfe : {p : Programʳᵃ} → (ex : Executionʳᵃ p) → {i j k : Fin (length p)} → TransClosure (rfeʳᵃ ex ; poʳᵃ ex) i j → poʳᵃ ex j k → TransClosure (rfeʳᵃ ex ; poʳᵃ ex) i k
    helper-rfe ex [ i , fst , snd ] po = [ i , fst , po-transitive ex snd po ]
    helper-rfe ex (x∼y ∷ h) po = x∼y ∷ helper-rfe ex h po

    translateʰᵇ-rfe₁ : {p : Programʳᵃ} → (ex : Executionʳᵃ p) → {i j k : Fin (length p)} → TransClosure (rfeʳᵃ ex ; poʳᵃ ex) i j → hb ex j k → (TransClosure (rfeʳᵃ ex ; poʳᵃ ex) ∪ TransClosure (rfeʳᵃ ex ; poʳᵃ ex) ; rfeʳᵃ ex) i k
    translateʰᵇ-rfe₂ : {p : Programʳᵃ} → (ex : Executionʳᵃ p) → {w x y z : Fin (length p)} → TransClosure (rfeʳᵃ ex ; poʳᵃ ex) w x → rfeʳᵃ ex x y → hb ex y z → (TransClosure (rfeʳᵃ ex ; poʳᵃ ex) ∪ TransClosure (rfeʳᵃ ex ; poʳᵃ ex) ; rfeʳᵃ ex) w z

    translateʰᵇ-rfe₁ ex h [ inj₁ po ] = inj₁ (helper-rfe ex h po)
    translateʰᵇ-rfe₁ ex {j = j} {k = k} h [ inj₂ rf ] with po-dec ex j k
    ... | no hⁿ = inj₂ (j , h , rf , hⁿ)
    ... | yes hʸ = inj₁ (helper-rfe ex h hʸ)
    translateʰᵇ-rfe₁ ex h (inj₁ po ∷ h') = translateʰᵇ-rfe₁ ex (helper-rfe ex h po) h'
    translateʰᵇ-rfe₁ ex h (_∷_ {x = i} {y = j} (inj₂ rf) h') with po-dec ex i j
    ... | no hⁿ = translateʰᵇ-rfe₂ ex h (rf , hⁿ) h'
    ... | yes hʸ = translateʰᵇ-rfe₁ ex (helper-rfe ex h hʸ) h'

    translateʰᵇ-rfe₂ ex {y = y} h h' [ inj₁ po ] = inj₁ (h ∷ʳ (y , h' , po))
    translateʰᵇ-rfe₂ ex h (h' , _) [ inj₂ rf ] with rf-consistent ex h' | rf-consistent ex rf
    ... | _ , hr , _ | hw , _ = let h = subst (λ x → x ≡ write) hr hw in case h of λ ()
    translateʰᵇ-rfe₂ ex {y = y} h h' (inj₁ po ∷ h'') = translateʰᵇ-rfe₁ ex (h ∷ʳ (y , h' , po)) h''
    translateʰᵇ-rfe₂ ex h (h' , _) (inj₂ rf ∷ _) with rf-consistent ex h' | rf-consistent ex rf
    ... | _ , hr , _ | hw , _ = let h = subst (λ x → x ≡ write) hr hw in case h of λ ()

    translateʰᵇ-rfe : {p : Programʳᵃ} → (ex : Executionʳᵃ p) → {i j k : Fin (length p)} → rfeʳᵃ ex i j → hb ex j k → (TransClosure (rfeʳᵃ ex ; poʳᵃ ex) ∪ TransClosure (rfeʳᵃ ex ; poʳᵃ ex) ; rfeʳᵃ ex) i k
    translateʰᵇ-rfe ex {j = j} h [ inj₁ po ] = inj₁ [ j , h , po ]
    translateʰᵇ-rfe ex (h , _) [ inj₂ rf ] with rf-consistent ex h | rf-consistent ex rf
    ... | _ , hr , _ | hw , _ = let h = subst (λ x → x ≡ write) hr hw in case h of λ ()
    translateʰᵇ-rfe ex {j = j} h (inj₁ po ∷ h') = translateʰᵇ-rfe₁ ex [ j , h , po ] h'
    translateʰᵇ-rfe ex (h , _) (inj₂ rf ∷ h') with rf-consistent ex h | rf-consistent ex rf
    ... | _ , hr , _ | hw , _ = let h = subst (λ x → x ≡ write) hr hw in case h of λ ()

    translateʰᵇ : {p : Programʳᵃ} → (ex : Executionʳᵃ p) → {i j : Fin (length p)} → hb ex i j → (poʳᵃ ex ∪ rfeʳᵃ ex ∪ TransClosure (poʳᵃ ex ; rfeʳᵃ ex) ∪ TransClosure (poʳᵃ ex ; rfeʳᵃ ex) ; poʳᵃ ex ∪ TransClosure (rfeʳᵃ ex ; poʳᵃ ex) ∪ TransClosure (rfeʳᵃ ex ; poʳᵃ ex) ; rfeʳᵃ ex) i j
    translateʰᵇ ex [ inj₁ po ] = inj₁ po
    translateʰᵇ ex {i = i} {j = j} [ inj₂ rf ] with po-dec ex i j
    ... | no hⁿ = inj₂ (inj₁ (rf , hⁿ))
    ... | yes hʸ = inj₁ hʸ
    translateʰᵇ ex (inj₁ po ∷ h) = case translateʰᵇ-po ex po h of λ { (inj₁ x) → inj₁ x
                                                                    ; (inj₂ (inj₁ y)) → inj₂ (inj₂ (inj₁ y))
                                                                    ; (inj₂ (inj₂ z)) → inj₂ (inj₂ (inj₂ (inj₁ z))) }
    translateʰᵇ ex (_∷_ {x = i} {y = j} (inj₂ rf) h) with po-dec ex i j
    ... | no hⁿ = case translateʰᵇ-rfe ex (rf , hⁿ) h of λ x → inj₂ (inj₂ (inj₂ (inj₂ x)))
    ... | yes hʸ = case translateʰᵇ-po ex hʸ h of λ { (inj₁ x) → inj₁ x
                                                    ; (inj₂ (inj₁ y)) → inj₂ (inj₂ (inj₁ y))
                                                    ; (inj₂ (inj₂ z)) → inj₂ (inj₂ (inj₂ (inj₁ z))) }

    convertʳᵉˢᵗ : {p : Programʳᵃ} → (ex : Execution' p) → {i j k : Fin (length p)} → Star (rfʳᵃ (toRA (ex'→ex ex)) ∪ moʳᵃ (toRA (ex'→ex ex)) ∪ frʳᵃ (toRA (ex'→ex ex))) i j → (moʳᵃ (toRA (ex'→ex ex)) ∪ frʳᵃ (toRA (ex'→ex ex))) j k → ob (ex'→ex ex) i k
    convertʳᵉˢᵗ ex {j = j} {k = k} ε (inj₁ mo) with po-dec (toRA (ex'→ex ex)) j k
    ... | no hⁿ = [ inj₂ (inj₂ (inj₁ (mo , hⁿ))) ]
    ... | yes hʸ with mo'-consistent ex mo
    ...   | hⱼ , hₖ , _ = [ inj₁ (inj₂ (inj₂ (hⱼ , hₖ , hʸ))) ]
    convertʳᵉˢᵗ ex {j = j} {k = k} ε (inj₂ fr@(_ , rf⁻¹ , _)) with po-dec (toRA (ex'→ex ex)) j k
    ... | no hⁿ = [ inj₂ (inj₂ (inj₂ (fr , hⁿ))) ]
    ... | yes hʸ with rf'-consistent ex rf⁻¹
    ...   | _ , hⱼ , _ = [ inj₁ (inj₂ (inj₁ (hⱼ , hʸ))) ]
    convertʳᵉˢᵗ ex (inj₁ rf ◅ ε) (inj₁ mo) with rf'-consistent ex rf | mo'-consistent ex mo
    ... | _ , hr , _ | hw , _ = let h = subst (λ x → x ≡ write) hr hw in case h of λ ()
    convertʳᵉˢᵗ {p} ex {i = i} {k = k} (inj₁ rf ◅ ε) (inj₂ (_ , rf⁻¹ , mo)) with rf'-consistent ex rf
    ... | _ , hr , _ with rf'-exists-unique ex hr
    ...   | _ , _ , heq with heq rf | heq rf⁻¹
    ...     | heq₁ | heq₂ with po-dec (toRA (ex'→ex ex)) i k
    ...       | no hⁿ = [ inj₂ (inj₂ (inj₁ (subst (λ x → moᵃʳᵐ (ex'→ex ex) x k) (subst (λ x → x ≡ i) (sym heq₂) (sym heq₁)) mo , hⁿ))) ]
    ...       | yes hʸ with mo'-consistent ex mo
    ...         | hᵢ , hₖ , _ = [ inj₁ (inj₂ (inj₂ (subst (λ x → type (lookup p x) ≡ write) (subst (λ x → x ≡ i) (sym heq₂) (sym heq₁)) hᵢ , hₖ , hʸ))) ]
    convertʳᵉˢᵗ ex (inj₁ rf₁ ◅ inj₁ rf₂ ◅ _) _ with rf'-consistent ex rf₁ | rf'-consistent ex rf₂
    ... | _ , hr , _ | hw , _ = let h = subst (λ x → x ≡ write) hr hw in case h of λ ()
    convertʳᵉˢᵗ ex (inj₁ rf ◅ inj₂ (inj₁ mo) ◅ _) _ with rf'-consistent ex rf | mo'-consistent ex mo
    ... | _ , hr , _ | hw , _ = let h = subst (λ x → x ≡ write) hr hw in case h of λ ()
    convertʳᵉˢᵗ {p} ex (_◅_ {i = i} (inj₁ rf) (_◅_ {j = j} (inj₂ (inj₂ fr@(_ , rf⁻¹ , mo))) h)) h'  with rf'-consistent ex rf
    ... | _ , hr , _ with rf'-exists-unique ex hr
    ...   | _ , _ , heq with heq rf | heq rf⁻¹
    ...     | heq₁ | heq₂ with po-dec (toRA (ex'→ex ex)) i j
    ...       | no hⁿ = inj₂ (inj₂ (inj₁ (subst (λ x → moᵃʳᵐ (ex'→ex ex) x j) (subst (λ x → x ≡ i) (sym heq₂) (sym heq₁)) mo , hⁿ))) ∷ convertʳᵉˢᵗ ex h h'
    ...       | yes hʸ with mo'-consistent ex mo
    ...         | hᵢ , hⱼ , _ = inj₁ (inj₂ (inj₂ (subst (λ x → type (lookup p x) ≡ write) (subst (λ x → x ≡ i) (sym heq₂) (sym heq₁)) hᵢ , hⱼ , hʸ))) ∷ convertʳᵉˢᵗ ex h h'
    convertʳᵉˢᵗ ex (_◅_ {i = i} {j = j} (inj₂ (inj₁ mo)) h) h' with po-dec (toRA (ex'→ex ex)) i j
    ... | no hⁿ = inj₂ (inj₂ (inj₁ (mo , hⁿ))) ∷ convertʳᵉˢᵗ ex h h'
    ... | yes hʸ with mo'-consistent ex mo
    ...   | hᵢ , hⱼ , _ = inj₁ (inj₂ (inj₂ (hᵢ , hⱼ , hʸ))) ∷ convertʳᵉˢᵗ ex h h'
    convertʳᵉˢᵗ ex (_◅_ {i = i} {j = j} (inj₂ (inj₂ fr@(_ , rf⁻¹ , _))) h) h' with po-dec (toRA (ex'→ex ex)) i j
    ... | no hⁿ = inj₂ (inj₂ (inj₂ (fr , hⁿ))) ∷ convertʳᵉˢᵗ ex h h'
    ... | yes hʸ with rf'-consistent ex rf⁻¹
    ...   | _ , hᵢ , _ = inj₁ (inj₂ (inj₁ (hᵢ , hʸ))) ∷ convertʳᵉˢᵗ ex h h'

    helper-[po+rfe]⁺ : {p : Programʳᵃ} → (ex : Execution' (fromRA p)) → {i j : Fin (length p)} → TransClosure (poʳᵃ (toRA (ex'→ex ex)) ; rfeʳᵃ (toRA (ex'→ex ex))) i j → ob (ex'→ex ex) i j
    helper-[po+rfe]⁺ {p} ex {i = i} [ _ , po , rfe@(rf , _) ] with type (lookup p i) | inspect type (lookup p i)
    ... | read | [ heq ] = inj₁ (inj₂ (inj₁ (heq , po))) ∷ [ inj₂ (inj₁ rfe) ]
    ... | write | [ heqᵢ ] with rf'-consistent ex rf
    ...   | heqⱼ , _ = inj₁ (inj₂ (inj₂ (heqᵢ , heqⱼ , po))) ∷ [ inj₂ (inj₁ rfe) ]
    helper-[po+rfe]⁺ {p} ex {i} ((_ , po , rfe@(rf , _)) ∷ h) with type (lookup p i) | inspect type (lookup p i)
    ... | read | [ heq ] = inj₁ (inj₂ (inj₁ (heq , po))) ∷ inj₂ (inj₁ rfe) ∷ helper-[po+rfe]⁺ ex h
    ... | write | [ heqᵢ ] with rf'-consistent ex rf
    ...   | heqⱼ , _ = inj₁ (inj₂ (inj₂ (heqᵢ , heqⱼ , po))) ∷ inj₂ (inj₁ rfe) ∷ helper-[po+rfe]⁺ ex h

    helper-[rfe+po]⁺ : {p : Programʳᵃ} → (ex : Execution' (fromRA p)) → {i j : Fin (length p)} → TransClosure (rfeʳᵃ (toRA (ex'→ex ex)) ; poʳᵃ (toRA (ex'→ex ex))) i j → ob (ex'→ex ex) i j
    helper-[rfe+po]⁺ ex [ _ , rfe@(rf , _) , po ] with rf'-consistent ex rf
    ... | _ , heq , _ = inj₂ (inj₁ rfe) ∷ [ inj₁ (inj₂ (inj₁ (heq , po))) ]
    helper-[rfe+po]⁺ ex ((_ , rfe@(rf , _) , po) ∷ h) with rf'-consistent ex rf
    ... | _ , heq , _ = inj₂ (inj₁ rfe) ∷ inj₁ (inj₂ (inj₁ (heq , po))) ∷ helper-[rfe+po]⁺ ex h

    convertʰᵇ : {p : Programʳᵃ} → (ex : Execution' (fromRA p)) → {i j : Fin (length p)} → (rfeʳᵃ (toRA (ex'→ex ex)) ∪ TransClosure (poʳᵃ (toRA (ex'→ex ex)) ; rfeʳᵃ (toRA (ex'→ex ex))) ∪ TransClosure (poʳᵃ (toRA (ex'→ex ex)) ; rfeʳᵃ (toRA (ex'→ex ex))) ; poʳᵃ (toRA (ex'→ex ex)) ∪ TransClosure (rfeʳᵃ (toRA (ex'→ex ex)) ; poʳᵃ (toRA (ex'→ex ex))) ∪ TransClosure (rfeʳᵃ (toRA (ex'→ex ex)) ; poʳᵃ (toRA (ex'→ex ex))) ; rfeʳᵃ (toRA (ex'→ex ex))) i j → ob (ex'→ex ex) i j
    convertʰᵇ _ (inj₁ rfe) = [ inj₂ (inj₁ rfe) ]
    convertʰᵇ ex (inj₂ (inj₁ [po+rfe]⁺)) = helper-[po+rfe]⁺ ex [po+rfe]⁺
    convertʰᵇ ex (inj₂ (inj₂ (inj₁ (_ , [po+rfe]⁺ , po)))) = case helper ex [po+rfe]⁺ of λ heq → helper-[po+rfe]⁺ ex [po+rfe]⁺ ∷ʳ inj₁ (inj₂ (inj₁ (heq , po)))
      where
      helper : {p : Programʳᵃ} → (ex : Execution' (fromRA p)) → {i j : Fin (length p)} → TransClosure (poʳᵃ (toRA (ex'→ex ex)) ; rfeʳᵃ (toRA (ex'→ex ex))) i j → type (lookup p j) ≡ read
      helper ex [ _ , _ , rf , _ ] with rf'-consistent ex rf
      ... | _ , heq , _ = heq
      helper ex (_ ∷ h) = helper ex h
    convertʰᵇ ex (inj₂ (inj₂ (inj₂ (inj₁ [rfe+po]⁺)))) = helper-[rfe+po]⁺ ex [rfe+po]⁺
    convertʰᵇ ex (inj₂ (inj₂ (inj₂ (inj₂ (_ , [rfe+po]⁺ , rfe))))) = helper-[rfe+po]⁺ ex [rfe+po]⁺ ∷ʳ inj₂ (inj₁ rfe)

    convertʰᵇ₁ : {p : Programʳᵃ} → (ex : Execution' (fromRA p)) → {i : Fin (length p)} → hb (toRA (ex'→ex ex)) i i → ob (ex'→ex ex) i i
    convertʰᵇ₁ ex h with translateʰᵇ (toRA (ex'→ex ex)) h
    ... | inj₂ x = convertʰᵇ ex x
    ... | inj₁ po = ⊥-elim (po-irreflexiveʳᵃ (toRA (ex'→ex ex)) po refl)

    convertʰᵇ₂ : {p : Programʳᵃ} → (ex : Execution' (fromRA p)) → {i j : Fin (length p)} → hb (toRA (ex'→ex ex)) i j → (Star (rfʳᵃ (toRA (ex'→ex ex)) ∪ moʳᵃ (toRA (ex'→ex ex)) ∪ frʳᵃ (toRA (ex'→ex ex))) ; (moʳᵃ (toRA (ex'→ex ex)) ∪ frʳᵃ (toRA (ex'→ex ex)))) j i → sc-per-locᵃʳᵐ (ex'→ex ex) → ob (ex'→ex ex) i j
    convertʰᵇ₂ {p} ex {i = i} {j = j} h (_ , h' , h'') sᵃʳᵐ with translateʰᵇ (toRA (ex'→ex ex)) h
    ... | inj₂ x = convertʰᵇ ex x
    ... | inj₁ po with type (lookup p i) | inspect type (lookup p i) | type (lookup p j) | inspect type (lookup p j)
    ...   | read | [ eqᵢ ] | _ | _ = [ inj₁ (inj₂ (inj₁ (eqᵢ , po))) ]
    ...   | write | [ eqᵢ ] | write | [ eqⱼ ] = [ inj₁ (inj₂ (inj₂ (eqᵢ , eqⱼ , po))) ]
    ...   | write | [ eqᵢ ] | read | [ eqⱼ ] with location (lookup p i) ≟ location (lookup p j)
    ...     | no hneq = ⊥-elim (hneq (sym (helper ex h' h'')))
      where
      helper : {p : Programʳᵃ} → (ex : Execution' (fromRA p)) → {i j k : Fin (length p)} → Star (rfʳᵃ (toRA (ex'→ex ex)) ∪ moʳᵃ (toRA (ex'→ex ex)) ∪ frʳᵃ (toRA (ex'→ex ex))) i j → (moʳᵃ (toRA (ex'→ex ex)) ∪ frʳᵃ (toRA (ex'→ex ex))) j k → location (lookup p i) ≡ location (lookup p k)
      helper ex ε (inj₁ mo) with mo'-consistent ex mo
      ... | _ , _ , heq = heq
      helper ex ε (inj₂ (_ , rf⁻¹ , mo)) with rf'-consistent ex rf⁻¹ | mo'-consistent ex mo
      ... | _ , _ , heq₁ , _ | _ , _ , heq₂ = trans (sym heq₁) heq₂
      helper ex (inj₁ rf ◅ h) h' with rf'-consistent ex rf
      ... | _ , _ , heq , _ = trans heq (helper ex h h')
      helper ex (inj₂ (inj₁ mo) ◅ h) h' with mo'-consistent ex mo
      ... | _ , _ , heq = trans heq (helper ex h h')
      helper ex (inj₂ (inj₂ (_ , rf⁻¹ , mo)) ◅ h) h' with rf'-consistent ex rf⁻¹ | mo'-consistent ex mo
      ... | _ , _ , heq₁ , _ | _ , _ , heq₂ = trans (trans (sym heq₁) heq₂) (helper ex h h')
    ...     | yes heq = ⊥-elim (sᵃʳᵐ refl ([ inj₁ (po , heq) ] ++ helper ex h' h''))
      where
      helper : {p : Programʳᵃ} → (ex : Execution' (fromRA p)) → {i j k : Fin (length p)} → Star (rfʳᵃ (toRA (ex'→ex ex)) ∪ moʳᵃ (toRA (ex'→ex ex)) ∪ frʳᵃ (toRA (ex'→ex ex))) i j → (moʳᵃ (toRA (ex'→ex ex)) ∪ frʳᵃ (toRA (ex'→ex ex))) j k → TransClosure (polocᵃʳᵐ (ex'→ex ex) ∪ rfᵃʳᵐ (ex'→ex ex) ∪ moᵃʳᵐ (ex'→ex ex) ∪ frᵃʳᵐ (ex'→ex ex)) i k
      helper _ ε x = [ inj₂ (inj₂ x) ]
      helper ex (x ◅ h) h' = inj₂ x ∷ helper ex h h'

  hˢ : {p : Programʳᵃ} → (ex : Execution' (fromRA p)) → isConsistentᵃʳᵐ (ex'→ex ex) → sc-per-locʳᵃ (toRA (ex'→ex ex))
  hˢ ex (_ , sᵃʳᵐ , _) heq@refl h = sᵃʳᵐ heq (convert ex h)
    where
    convert : {p : Programʳᵃ} → (ex : Execution' (fromRA p)) → {i j : Fin (length p)} → TransClosure (polocʳᵃ (toRA (ex'→ex ex)) ∪ rfʳᵃ (toRA (ex'→ex ex)) ∪ moʳᵃ (toRA (ex'→ex ex)) ∪ frʳᵃ (toRA (ex'→ex ex))) i j → TransClosure (polocᵃʳᵐ (ex'→ex ex) ∪ rfᵃʳᵐ (ex'→ex ex) ∪ moᵃʳᵐ (ex'→ex ex) ∪ frᵃʳᵐ (ex'→ex ex)) i j
    convert ex [ inj₁ poloc ] = [ inj₁ poloc ]
    convert _ [ inj₂ (inj₁ rf) ] = [ inj₂ (inj₁ rf) ]
    convert _ [ inj₂ (inj₂ (inj₁ mo)) ] = [ inj₂ (inj₂ (inj₁ mo)) ]
    convert _ [ inj₂ (inj₂ (inj₂ fr)) ] = [ inj₂ (inj₂ (inj₂ fr)) ]
    convert ex (inj₁ poloc ∷ h) = inj₁ poloc ∷ convert ex h
    convert ex (inj₂ (inj₁ rf) ∷ h) = inj₂ (inj₁ rf) ∷ convert ex h
    convert ex (inj₂ (inj₂ (inj₁ mo)) ∷ h) = inj₂ (inj₂ (inj₁ mo)) ∷ convert ex h
    convert ex (inj₂ (inj₂ (inj₂ fr)) ∷ h) = inj₂ (inj₂ (inj₂ fr)) ∷ convert ex h

  hᵃ : {p : Programʳᵃ} → (ex : Execution' (fromRA p)) → isConsistentᵃʳᵐ (ex'→ex ex) → atomicityʳᵃ (toRA (ex'→ex ex))
  hᵃ _ (_ , _ , aᵃʳᵐ) h = aᵃʳᵐ h
