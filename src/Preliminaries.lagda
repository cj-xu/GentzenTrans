
 ===================
 =                 =
 =  Preliminaries  =
 =                 =
 ===================

    Chuangjie Xu

This module collects the basic types and lemmas used throughout the
development of Gödel's System T, its translations and their applications.
We begin with identity types and equational reasoning, then define
dependent pairs, coproducts and the order on natural numbers.

We represent a finite sequence by an infinite sequence together with a
length. The sequence lemmas describe agreement on initial segments and
how extending a finite sequence affects that agreement.

\begin{code}

{-# OPTIONS --without-K --safe #-}

module Preliminaries where

open import Agda.Primitive using (_⊔_)


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

FunExt : Set₁
FunExt = {A B : Set} {f g : A → B} → (∀ x → f x ≡ g x) → f ≡ g

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
record Σ {ℓ ℓ'} {A : Set ℓ} (B : A → Set ℓ') : Set (ℓ ⊔ ℓ') where
 constructor _,_
 field
  pr₁ : A
  pr₂ : B pr₁

open Σ public

infixr 1 _×_ _,_

_×_ : ∀ {ℓ ℓ'} → Set ℓ → Set ℓ' → Set (ℓ ⊔ ℓ')
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

¬ : Set → Set
¬ A = A → 𝟘

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

not-zero-is-suc : {n : ℕ} → ¬ (n ≡ 0) → Σ \m → suc m ≡ n
not-zero-is-suc {0}     f = 𝟘-elim (f refl)
not-zero-is-suc {suc n} f = n , refl

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

≤-cases : {n m : ℕ} → n ≤ m → (n ≡ m) + (n < m)
≤-cases {0}     {0}      ≤zero   = inl refl
≤-cases {0}     {suc m}  ≤zero   = inr (≤suc ≤zero)
≤-cases {suc n} {suc m} (≤suc r) with ≤-cases r
... | inl refl = inl refl
... | inr s    = inr (≤suc s)

≤suc' : {n m : ℕ} → n ≤ m → n ≤ suc m
≤suc'  ≤zero   = ≤zero
≤suc' (≤suc r) = ≤suc (≤suc' r)

≤-pred : {n m : ℕ} → suc n ≤ suc m → n ≤ m
≤-pred (≤suc r) = r

suc≰zero : {n : ℕ} → ¬ (suc n ≤ 0)
suc≰zero ()

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

drop : {A : Set} → ℕ → A ᴺ → A ᴺ
drop 0       α = α
drop (suc n) α = drop n (tail α)

drop-head : {A : Set} (n : ℕ) (α : A ᴺ) → head (drop n α) ≡ α n
drop-head 0       α = refl
drop-head (suc n) α = drop-head n (tail α)

drop-agreement : {A : Set} (k : ℕ) {m : ℕ} {α β : A ᴺ}
               → tail (drop k α) ≡[ m ] tail (drop k β)
               → drop (suc k) α ≡[ m ] drop (suc k) β
drop-agreement 0       e = e
drop-agreement (suc k) e = drop-agreement k e

_≤¹_ : ℕᴺ → ℕᴺ → Set
α ≤¹ β = ∀ i → α i ≤ β i

≤¹refl : ∀{α} → α ≤¹ α
≤¹refl i = ≤refl

✶≤¹ : {α β : ℕᴺ} {n : ℕ} → α ≤¹ tail β → n ≤ β 0 → n ✶ α ≤¹ β
✶≤¹ u r  0      = r
✶≤¹ u r (suc i) = u i

\end{code}

■ Finite sequences

\begin{code}

_* : Set → Set
A * = A ᴺ × ℕ

ℕ* : Set
ℕ* = ℕ *

len : {A : Set} → A * → ℕ
len = pr₂

infixl 10 _✦_

_✦_ : {A : Set} → A * → A → A *
(α , l) ✦ a = rec (λ _ v → rec v (λ _ _ → a) , 1)
                  (λ n z f v → rec (f 0) (λ i g → pr₁ (z (f ∘ suc) v) i) , suc (suc n))
                  l α a

len✦-suc : {A : Set} (s : A *) {a : A} → suc (len s) ≡ len (s ✦ a)
len✦-suc (α , 0)     = refl
len✦-suc (α , suc l) = refl

_∋_ : {A : Set} → A * → A ᴺ → Set
(α , l) ∋ β = ∀ i → i < l → α i ≡ β i

✦-prefix : {A : Set} (s : A *) (α : A ᴺ) {a : A}
        → s ∋ α → a ≡ α (len s) → (s ✦ a) ∋ α
✦-prefix (γ , 0)     α p e 0       _         = e
✦-prefix (γ , 0)     α p e (suc i) (≤suc ())
✦-prefix (γ , suc l) α p e 0       _         = p 0 (≤suc ≤zero)
✦-prefix (γ , suc l) α p e (suc i) (≤suc r) =
  ✦-prefix (γ ∘ suc , l) (tail α)
    (λ j q → p (suc j) (≤suc q)) e i
    (transport (λ k → i < k) (len✦-suc ((γ ∘ suc) , l)) r)

pad : ℕ → ℕᴺ → ℕᴺ
pad = rec (λ α i → 0)
          (λ n h α → rec (α 0) (λ i r → h (α ∘ suc) i))

_^ : ℕ* → ℕᴺ
(α , l) ^ = pad l α

s∋s^ : (s : ℕ*) → s ∋ (s ^)
s∋s^ (α , suc l)  0      (≤suc r) = refl
s∋s^ (α , suc l) (suc i) (≤suc r) = s∋s^ ((α ∘ suc) , l) i r

s∋sn^ : (s : ℕ*) {n : ℕ} → s ∋ ((s ✦ n) ^)
s∋sn^ (α , suc l)        0      (≤suc r) = refl
s∋sn^ (α , suc (suc l)) (suc i) (≤suc r) = s∋sn^ (α ∘ suc , suc l) i r


infixl 10 _＠_

_＠_ : ℕ* → ℕᴺ → ℕᴺ
(α , l) ＠ β =
  rec (λ α β → β)
      (λ n h α β → rec (α 0) (λ i r → h (α ∘ suc) (β ∘ suc) i))
      l α β

s∋s＠α : (s : ℕ*) (α : ℕᴺ) → s ∋ (s ＠ α)
s∋s＠α (α , suc l) β  0       _       = refl
s∋s＠α (α , suc l) β (suc i) (≤suc p) = s∋s＠α (α ∘ suc , l) (β ∘ suc) i p

\end{code}

■ Inductively defined lists

\begin{code}

infixr 5 _∷_
data List {a} (A : Set a) : Set a where
  []  : List A
  _∷_ : (x : A) (xs : List A) → List A

{-# BUILTIN LIST List #-}

listrec : {A B : Set} → B → (A → List A → B → B) → List A → B
listrec b h []       = b
listrec b h (a ∷ xs) = h a xs (listrec b h xs)

\end{code}
