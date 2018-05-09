{-# OPTIONS --cubical #-}
module Cubical.Examples.Sets where

open import Agda.Builtin.Sigma
open import Agda.Builtin.Unit
open import Agda.Builtin.Nat
open import Cubical.PathPrelude hiding (_≃_)
open import Cubical.GradLemma
open import Cubical.Univalence

data ⊥ : Set where

lem : isContr ⊤
lem = tt , λ y → refl

prop⊤ : isProp ⊤
prop⊤ = λ{ tt tt → refl}

prop⊥ : isProp ⊥
prop⊥ = λ{ () ()}

code : Nat → Nat → Set
code zero zero = ⊤
code zero (suc n) = ⊥
code (suc m) zero = ⊥
code (suc m) (suc n) = code m n

-- code-ind : {m n : Nat} → code m n → {A : Set} → A → (A → A) → A
-- code-ind {zero} {zero} tt b _ = b
-- code-ind {zero} {suc n} ()
-- code-ind {suc m} {zero} ()
-- code-ind {suc m} {suc n} c b i = i $ code-ind {m} {n} c b i

r : (n : Nat) → code n n
r zero = tt
r (suc n) = r n

encode : {m n : Nat} → m ≡ n → code m n
encode {m} {n} p = transp (λ i → code m (p i)) (r m)

decode : {m n : Nat} → code m n → m ≡ n
decode {zero} {zero} tt = refl
decode {zero} {suc n} ()
decode {suc m} {zero} ()
decode {suc m} {suc n} c = cong suc (decode c)

base : {m : Nat} → decode (encode (λ i → m)) ≡ (λ i → m)
base {zero}  = refl
base {suc m} = cong (cong suc) (base {m})

help0 : {m n : Nat} → (p : m ≡ n) → decode (encode p) ≡ p
help0 {m} {n} = pathJ (λ _ p → decode (encode p) ≡ p) base n

help1 : {m n : Nat} → (c : code m n) → encode {m} {n} (decode c) ≡ c
help1 {zero} {zero} tt = refl
help1 {zero} {suc n} ()
help1 {suc m} {zero} ()
help1 {suc m} {suc n} c = help1 {m} {n} c

-- 2.13.1
lem3 : {m n : Nat} → (m ≡ n) ≃ (code m n)
lem3 {m} {n} = con encode (gradLemma encode decode (help1 {m} {n}) help0)

propCode : {m n : Nat} → isProp (code m n)
propCode {zero} {zero} = prop⊤
propCode {zero} {suc n} = prop⊥
propCode {suc m} {zero} = prop⊥
propCode {suc m} {suc n} = propCode {m} {n}

lem2 : isSet Nat
lem2 m n p q = begin p ≡⟨ {!!} ⟩ q ∎
  where
  p* : code m n
  p* = encode p
  q* : code m n
  q* = encode q
  p' : PathP (λ i → ua (lem3 {m} {n}) i) p p*
  p' = {!!}
  q' : PathP (λ i → ua (lem3 {m} {n}) i) q q*
  q' = {!!}
  -- Where did i flip the arguments?
  φ : p* ≡ q*
  φ = propCode {m} {n} p* q*
