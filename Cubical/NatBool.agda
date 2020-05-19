{-# OPTIONS --cubical --safe #-}

module NatBool where

open import Cubical.Core.Everything using (_≡_; Level; Type; Σ; _,_; fst; snd; _≃_; ~_)

open import Cubical.Foundations.Prelude using (refl; sym; _∙_; cong; transport; subst; funExt; transp; I; i0; i1)
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Univalence using (ua)
open import Cubical.Foundations.Isomorphism using (iso; Iso; isoToPath; section; retract)

open import Data.Bool.Base using (Bool; true; false; _∧_)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product using (_×_; proj₁; proj₂)

open import Lemmas

Input Output : Set

Input  = Bool × (ℕ × Bool)

firstB : Input → Bool
firstB = proj₁

secondB : Input → Bool
secondB = proj₂ ∘ proj₂

Output = ℕ × Bool

andB : Output → Bool
andB = proj₂

record Input' : Set where
  constructor input'
  field
    firstBool  : Bool
    numberI    : ℕ
    secondBool : Bool
open Input'

record Output' : Set where
  constructor output'
  field
    numberO  : ℕ
    andBools : Bool
open Output'

--------------

Input→Input' : Input → Input'
Input→Input' (b , (n , b')) = input' b n b'

Input'→Input : Input' → Input
Input'→Input (input' b n b') = (b , (n , b'))

Input→Input'→Input : (i : Input) → Input'→Input (Input→Input' i) ≡ i
Input→Input'→Input i = refl

Input'→Input→Input' : (i : Input') → Input→Input' (Input'→Input i) ≡ i
Input'→Input→Input' i = refl

isoInput : Iso Input Input'
isoInput = iso Input→Input' Input'→Input Input'→Input→Input' Input→Input'→Input 

Input≡Input' : Input ≡ Input'
Input≡Input' = isoToPath isoInput

Output→Output' : Output → Output'
Output→Output' (n , b) = output' n b

Output'→Output : Output' → Output
Output'→Output (output' n b) = n , b

Output→Output'→Output : (o : Output) → Output'→Output (Output→Output' o) ≡ o
Output→Output'→Output o = refl

Output'→Output→Output' : (o : Output') → Output→Output' (Output'→Output o) ≡ o
Output'→Output→Output' o = refl

isoOutput : Iso Output Output'
isoOutput = iso Output→Output' Output'→Output Output'→Output→Output' Output→Output'→Output 

Output≡Output' : Output ≡ Output'
Output≡Output' = isoToPath isoOutput

--------------


op : Input → Output
op (b , (n , b')) = n , b ∧ b'

op' : Input' → Output'
op' = transport Output≡Output' ∘ op ∘ transport (sym Input≡Input')

--------------

-- Computations

b1 = true
b2 = false
n = 3

out = op (b1 , (n , b2))

outv : out ≡ (3 , false)
outv = refl

out' = op' (input' b1 n b2)

outv' : out' ≡ (output' 3 false)
outv' = refl

--------------

-- Another isomorphism

Input2  = Bool × Output'

Input→Input2 : Input → Input2
Input→Input2 (b , (n , b')) = b , output' n b'

Input2→Input : Input2 → Input
Input2→Input (b , (output' n b')) = b , (n , b')

Input→Input2→Input : (i : Input) → Input2→Input (Input→Input2 i) ≡ i
Input→Input2→Input i = refl

Input2→Input→Input2 : (i : Input2) → Input→Input2 (Input2→Input i) ≡ i
Input2→Input→Input2 i = refl

isoInput2 : Iso Input Input2
isoInput2 = iso Input→Input2 Input2→Input Input2→Input→Input2 Input→Input2→Input 

Input≡Input2 : Input ≡ Input2
Input≡Input2 = isoToPath isoInput2

--------------

-- Proofs

andSpecTrueTrue : (r : Input) → (F : firstB r ≡ true) → (S : secondB r ≡ true) → andB (op r) ≡ true
andSpecTrueTrue r F S = subst (λ x → x ∧ secondB r ≡ true) (sym F) (subst (λ x → x ≡ true) (sym S) refl)

andSpecTrueTrue' : (r : Input') → (F : firstBool r ≡ true) → (S : secondBool r ≡ true) → andBools (op' r) ≡ true
andSpecTrueTrue' r F S = subst (λ x → x ∧ secondBool r ≡ true) (sym F) (subst (λ x → x ≡ true) (sym S) refl)

-- Lift the first proof
andSpecTrueTrueLift : (r' : Input') → (F' : firstBool r' ≡ true) → (S' : secondBool r' ≡ true) → andBools (op' r') ≡ true
andSpecTrueTrueLift r' F' S' =
  let r : Input              ; r = transport (sym Input≡Input') r'
      F : firstB r ≡ true    ; F = F'
      S : secondB r ≡ true   ; S = S'
      B : andB (op r) ≡ true ; B = andSpecTrueTrue r F S
  in B
