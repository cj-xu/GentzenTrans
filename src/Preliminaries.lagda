
 ======================
 =                    =
 =  §0  Mini library  =
 =                    =
 ======================

    Chuangjie Xu

A small library for the Agda development of the paper

  A Gentzen-style monadic translation of Gödel's System T

by Chuangjie Xu.

\begin{code}

{-# OPTIONS --without-K --safe #-}

module Preliminaries where

\end{code}

■ Identity types

\begin{code}

infix 2 _≡_

data _≡_ {ℓ} {A : Set ℓ} (a : A) : A → Set ℓ where
 refl : a ≡ a

ap : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
ap f refl = refl

ap² : ∀ {ℓ ℓ' ℓ''} {A : Set ℓ} {B : Set ℓ'} {C : Set ℓ''}
    → (f : A → B → C) {x y : A} {u v : B} → x ≡ y → u ≡ v → f x u ≡ f y v
ap² f refl refl = refl

sym : ∀ {ℓ} {A : Set ℓ} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀ {ℓ} {A : Set ℓ} {x y z : A}
      → x ≡ y → y ≡ z → x ≡ z
trans refl p = p

transport : ∀ {ℓ ℓ'} {A : Set ℓ} (P : A → Set ℓ') {x y : A}
          → x ≡ y → P x → P y
transport P refl p = p

infix  1 begin_
infix  3 _∎
infixr 2 _≡⟨_⟩_

begin_ : ∀ {ℓ} {A : Set ℓ} {x y : A} → x ≡ y → x ≡ y
begin x≡y = x≡y

_≡⟨_⟩_ : ∀ {ℓ} {A : Set ℓ} (x {y z} : A) → x ≡ y → y ≡ z → x ≡ z
_ ≡⟨ x≡y ⟩ y≡z = trans x≡y y≡z

_∎ : ∀ {ℓ} {A : Set ℓ} (x : A) → x ≡ x
_∎ _ = refl

\end{code}

■ More operations and types

\begin{code}

--
-- function composition
--
_∘_ : {A : Set} {B : A → Set} {C : {a : A} → B a → Set}
    → ({a : A} (b : B a) → C b) → (f : (a : A) → B a) → (a : A) → C (f a)
f ∘ g = λ a → f (g a)

--
-- (dependent) pairs
--
record Σ {A : Set} (B : A → Set) : Set where
 constructor _,_
 field
  pr₁ : A
  pr₂ : B pr₁

open Σ public

infixr 1 _×_ _,_

_×_ : Set → Set → Set
A × B = Σ \(_ : A) → B

--
-- coproduct
--
data _+_ (A B : Set) : Set where
 inl : A → A + B
 inr : B → A + B

case : ∀{ℓ} {A B : Set} {C : Set ℓ}
     → (A → C) → (B → C) → A + B → C
case f g (inl a) = f a
case f g (inr b) = g b

--
-- the empty type
--
data 𝟘 : Set where

𝟘-elim : {A : Set} → 𝟘 → A
𝟘-elim ()

--
-- the unit type
--
data 𝟙 : Set where
 ⋆ : 𝟙

\end{code}

■ Natural numbers

\begin{code}

data ℕ : Set where
 zero : ℕ
 suc  : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

rec : {A : Set} → A → (ℕ → A → A) → ℕ → A
rec a f  0      = a
rec a f (suc n) = f n (rec a f n)

ind : ∀ {ℓ} {P : ℕ → Set ℓ} → P 0 → (∀ n → P n → P (suc n)) → ∀ n → P n
ind p f  0      = p
ind p f (suc n) = f n (ind p f n)

infix 5 _≤_ _<_ _≥_ _>_

data _≤_ : ℕ → ℕ → Set where
 ≤zero : {n : ℕ} → 0 ≤ n
 ≤suc  : {n m : ℕ} → n ≤ m → suc n ≤ suc m

_<_ _≥_ _>_ : ℕ → ℕ → Set
n < m = suc n ≤ m
n ≥ m = m ≤ n
n > m = m < n

≤refl : {n : ℕ} → n ≤ n
≤refl {0}     = ≤zero
≤refl {suc n} = ≤suc ≤refl

≤refl' : {n m : ℕ} → n ≡ m → n ≤ m
≤refl' refl = ≤refl

≤trans : {n m l : ℕ} → n ≤ m → m ≤ l → n ≤ l
≤trans  ≤zero    _       = ≤zero
≤trans (≤suc r) (≤suc s) = ≤suc (≤trans r s)

≤-cases : {n m : ℕ} → n ≤ suc m → (n ≡ suc m) + (n ≤ m)
≤-cases {0}     {m}      ≤zero   = inr ≤zero
≤-cases {1}     {0}     (≤suc r) = inl refl
≤-cases {suc n} {suc m} (≤suc r) with ≤-cases r
≤-cases {suc n} {suc m} (≤suc r) | inl e = inl (ap suc e)
≤-cases {suc n} {suc m} (≤suc r) | inr s = inr (≤suc s)

\end{code}

■ Infinite sequences

\begin{code}

_ᴺ : Set → Set
A ᴺ = ℕ → A

ℕᴺ : Set
ℕᴺ = ℕ ᴺ

0ʷ : ℕᴺ
0ʷ = λ i → 0

infixr 30 _✶_

_✶_ : {A : Set} → A → A ᴺ → A ᴺ
a ✶ u = rec a (λ i _ → u i)
-- (a ✶ u)  0      = a
-- (a ✶ u) (suc i) = u i

head : {A : Set} → A ᴺ → A
head α = α 0

tail : {A : Set} → A ᴺ → A ᴺ
tail α i = α (suc i)

data _≡[_]_ {A : Set} : A ᴺ → ℕ → A ᴺ → Set where
 ≡[zero] : {α β : A ᴺ} → α ≡[ 0 ] β
 ≡[suc]  : {α β : A ᴺ} {n : ℕ} → head α ≡ head β → tail α ≡[ n ] tail β → α ≡[ suc n ] β

≡[≤] : {A : Set} {α β : A ᴺ} {n m : ℕ}
     → α ≡[ n ] β → m ≤ n → α ≡[ m ] β
≡[≤]  en            ≤zero   = ≡[zero]
≡[≤] (≡[suc] e en) (≤suc r) = ≡[suc] e (≡[≤] en r)

≡[]-< : {A : Set} {α β : A ᴺ} {n i : ℕ}
      → α ≡[ n ] β → suc i ≤ n → α i ≡ β i
≡[]-< (≡[suc] e en) (≤suc ≤zero)    = e
≡[]-< (≡[suc] e en) (≤suc (≤suc r)) = ≡[]-< en (≤suc r)

≡[]-refl : {n : ℕ} {A : Set} {α : A ᴺ}
         → α ≡[ n ] α
≡[]-refl {0}     = ≡[zero]
≡[]-refl {suc n} = ≡[suc] refl ≡[]-refl

\end{code}
