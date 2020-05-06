
 =========================
 =                       =
 =  §3.4  Bar recursion  =
 =                       =
 =========================

    Chuangjie Xu, February 2020

    updated in May 2020

Schwichtenberg [2] shows that the terms of Gödel's System T are closed
under the rule of Spector's bar recursion of types 0 and 1.  Oliva and
Steila [1] provide a more direct proof of Schwichtenberg's theorem via
their notion of general bar recursion whose termination condition is
given by decidable monotone predicates on finite sequences.  We present
their construction general-bar-recursion functionals [1, Def. 3.1&3.3]
as an instance of our translation, and then prove its correctness using
the fundamental theorem of logical relation.


References

[1] P. Oliva and S. Steila.  A direct proof of Schwichtenberg's bar
    recursion closure theorem.  Accepted by The Journal of Symbolic
    Logic, 2017.

[2] H. Schwichtenberg.  On bar recursion of types 0 and 1.  The
    Journal of Symbolic Logic, vol. 44, no. 3, pp. 325–329, 1979.

\begin{code}

{-# OPTIONS --without-K --safe #-}

open import Preliminaries
open import T
open import TAuxiliaries hiding (Φ ; Φ-spec)

module BarRecursion (σ : Ty) where

\end{code}

■ Function extensionality

We will need function extensionality in the proofs of

 1. Ψ k is a bar recursion functional of λα.k [1, Lemma 2.1], and

 2. κ preserves the logical relation.

\begin{code}

FunExt : Set₁
FunExt = {A B : Set} {f g : A → B} → (∀ x → f x ≡ g x) → f ≡ g

\end{code}

■ Preliminaries

\begin{code}

--
-- finite sequences of natural numbers
--
ℕ* : Set
ℕ* = ℕᴺ × ℕ

infixl 10 _✦_

--
-- s ✦ n -- append n to s
--
_✦_ : ℕ* → ℕ → ℕ*
(α , l) ✦ n = rec (λ _ v → rec v (λ _ _ → 0) , 1)
                  (λ n z f v → rec (f 0) (λ i g → pr₁ (z (f ∘ suc) v) i) , suc (suc n))
                  l α n

--
-- s ∋ β means s is an initial segment of β.
--
_∋_ : ℕ* → ℕᴺ → Set
(α , l) ∋ β = ∀ i → i < l → α i ≡ β i

--
-- extend finite sequences to infinite ones
--
_^ : ℕ* → ℕᴺ
_^ = pr₁

s∋sn^ : (s : ℕ*) {n : ℕ} → s ∋ ((s ✦ n) ^)
s∋sn^ (α , suc l)  0       _         = refl
s∋sn^ (α , suc l) (suc i) (≤suc i<l) = s∋sn^ (α ∘ suc , l) i i<l

--
-- length of finite sequences
--
len : ℕ* → ℕ
len = pr₂

len✦-suc : {s : ℕ*} {n : ℕ} → suc (len s) ≡ len (s ✦ n)
len✦-suc {α , 0}     {n} = refl
len✦-suc {α , suc l} {n} = refl


infix 2 _∈_ _∉_
--
-- decidable predicates as ℕ-valued functions
--
_∉_ _∈_ : {A : Set} → A → (A → ℕ) → Set
a ∈ Q = ¬ (Q a ≡ 0)
a ∉ Q = Q a ≡ 0

∈-dec : {A : Set} {a : A} (Q : A → ℕ) → (a ∈ Q) + (a ∉ Q)
∈-dec {_} {a} Q with Q a
... | 0     = inr refl
... | suc n = inl (λ ())

monotone : (ℕ* → ℕ) → Set
monotone S = ∀ s n → s ∈ S → (s ✦ n) ∈ S

_secures_ : (ℕ* → ℕ) → (ℕᴺ → ℕ) → Set
S secures Y = ∀ (s : ℕ*) → s ∈ S → ∀ (α : ℕᴺ) → s ∋ α → Y (s ^) ≡ Y α

\end{code}

■ General bar recursion

\begin{code}

gBR : {A : Set}
    → (ℕ* → ℕ)
    → ((ℕ* → A) → (ℕ* → (ℕ → A) → A) → ℕ* → A)
    → Set
gBR {A} S ξ = ∀ (G : ℕ* → A) (H : ℕ* → (ℕ → A) → A) (s : ℕ*) →
                  (s ∈ S → ξ G H s ≡ G s)
                × (s ∉ S → ξ G H s ≡ H s (λ n → ξ G H (s ✦ n)))

\end{code}

■ A nucleus for general bar recursion

\begin{code}

Jι : Ty
Jι = (ιᶥ ⇾ ι) ⊠ (ι* ⇾ ι) ⊠ ((ι* ⇾ σ) ⇾ (ι* ⇾ (ι ⇾ σ) ⇾ σ) ⇾ ι* ⇾ σ)

private

 ⟨_,_,_⟩ : {Γ : Cxt}
         → T Γ (ιᶥ ⇾ ι)
         → T Γ (ι* ⇾ ι)
         → T Γ ((ι* ⇾ σ) ⇾ (ι* ⇾ (ι ⇾ σ) ⇾ σ) ⇾ ι* ⇾ σ)
         → T Γ Jι
 ⟨ t₀ , t₁ , t₂ ⟩ = Pair · t₀ · (Pair · t₁ · t₂)

 V : {Γ : Cxt}
   → T Γ Jι
   → T Γ (ιᶥ ⇾ ι)
 V w = Pr1 · w

 𝑉 : ⟦ Jι ⟧ʸ → ℕᴺ → ℕ
 𝑉 = pr₁

 S : {Γ : Cxt}
   → T Γ Jι
   → T Γ (ι* ⇾ ι)
 S w = Pr1 · (Pr2 · w)

 𝑆 : ⟦ Jι ⟧ʸ → ℕ* → ℕ
 𝑆 = pr₁ ∘ pr₂

 B  : {Γ : Cxt}
   → T Γ Jι
   → T Γ ((ι* ⇾ σ) ⇾ (ι* ⇾ (ι ⇾ σ) ⇾ σ) ⇾ ι* ⇾ σ)
 B w = Pr2 · (Pr2 · w)

 𝐵 : ⟦ Jι ⟧ʸ → (ℕ* → ⟦ σ ⟧ʸ) → (ℕ* → (ℕ → ⟦ σ ⟧ʸ) → ⟦ σ ⟧ʸ) → ℕ* → ⟦ σ ⟧ʸ
 𝐵 = pr₂ ∘ pr₂

η : {Γ : Cxt} → T Γ (ι ⇾ Jι)
η = Lam ⟨ Lam ν₁ , Lam 𝟏 , Lam (Lam ν₁) ⟩
 -- λ n . ⟨ λα.n , λs.1 , λGH.G ⟩

κ : {Γ : Cxt} → T Γ ((ι ⇾ Jι) ⇾ Jι ⇾ Jι)
κ = Lam (Lam ⟨ Lam (V (ν₂ · (V ν₁ · ν₀)) · ν₀)
 -- λ g  w . ⟨ λ α . V (g    (V w    α))    α
             , Lam (Min · (S ν₁ · ν₀) · (S (ν₂ · (V ν₁ · ^ ν₀ ^)) · ν₀))
 --          , λ s . min  ( S w   s   ,  S ( g  (V  w     s^))      s)
             , Lam (Lam (B ν₂ · Lam (B (ν₄ · (V ν₃ · ^ ν₀ ^)) · ν₂ · ν₁ · ν₀) · ν₀)) ⟩)
 --          , λ G   H . B w   (λ s . B (g   (V  w     s^))    G    H   s)    H  ⟩

--
-- Instantiate the translation by importing the following module
-- with the nucleus (Jι, η, κ)
--
open import GentzenTranslation Jι η κ public

\end{code}

■ The generic element Ω

\begin{code}

--
-- Helper function for constructing the constant bar-recursion functional Ψ
--
φ : {Γ : Cxt}
  → T Γ (ι ⇾ (ι* ⇾ σ) ⇾ (ι* ⇾ (ι ⇾ σ) ⇾ σ) ⇾ ι* ⇾ σ)
φ = Rec · Lam (Lam ν₁)
--  rec  (λ G   H . G)
        · Lam (Lam (Lam (Lam (Lam (ν₁ · ν₀ · Lam (ν₄ · ν₃ · ν₂ · (ν₁ ★ ν₀)))))))
--       (λ n   z    G    H    s . H    s   (λ x . z   G   H    (s ★ x)))
-- φ(0,G,H)   = G
-- φ(n+1,G,H) = λs.H(s,λx.φ(n,G,H,s⋆x))

--
-- Bar-recursion functional for constant terminating functional λα.k
--
Ψ : {Γ : Cxt}
  → T Γ (ι ⇾ (ι* ⇾ σ) ⇾ (ι* ⇾ (ι ⇾ σ) ⇾ σ) ⇾ ι* ⇾ σ)
Ψ = Lam (Lam (Lam (Lam (If · (Lt · ν₃ · Len ν₀)
                           · (ν₂ · ν₀)
                           · (φ · (Minus · (Suc · ν₃) · Len ν₀) · ν₂ · ν₁ · ν₀)))))
-- Ψ(n,G,H,s) = G(s)              if |s|>n
-- Ψ(n,G,H,s) = φ(n+1-|s|,G,H,s)  otherwise

--
-- [1, Lemma 2.1] : Ψ k is a bar recursion functional for λα.k
--
Ψ-gBR : FunExt
      → (k : ℕ) → gBR (λ s → lt k (len s)) (⟦ Ψ ⟧ k)
-- i.e. for any G H s
--
--   k < |s|  →  Ψ k G H s ≡ G s
--   k ≮ |s|  →  Ψ k G H s ≡ H s (λ m → Ψ k G H (s ✦ m)
--
-- The proof is given in the appendix.

Α : {Γ : Cxt} → T Γ (ι ⇾ Jι)
Α = Lam ⟨ Lam (ν₀ · ν₁)
 -- λn. ⟨ λ α . α n
        , Lam (Lt · ν₁ · Len ν₀)
 --     , λ s . Lt   n    |s|
        , Ψ · ν₀ ⟩
 --     , Ψ n ⟩

--
-- the generic element
--
Ω : {Γ : Cxt} → T Γ (Jι ⇾ Jι)
Ω = κ · Α

\end{code}

■ A parametrized logical relation for general bar recursion

\begin{code}

--
-- Base case of the logical relation
--
Rι : ℕᴺ → ⟦ ι ⟧ʸ → ⟦ Jι ⟧ʸ → Set
Rι α n (Y , S , B) = n ≡ Y α × monotone S × S secures Y × gBR S B

--
-- η preserves the logical relation
--
Rη : (α : ℕᴺ)
   → {Γ : Cxt} (γ : ⟦ Γ ⟧ˣ) (n : ⟦ ι ⟧ʸ) → Rι α n (⟦ η ⟧ᵐ γ n)
Rη α γ n = refl , (λ _ _ z → z) , (λ _ _ _ _ → refl) , (λ _ _ _ → (λ _ → refl) , λ ())

--
-- κ preserves the logical relation
--
Rκ : FunExt
   → (α : ℕᴺ)
   → {Γ : Cxt} (γ : ⟦ Γ ⟧ˣ) {f : ⟦ ι ⇾ ι ⟧ʸ} {g : ⟦ ι ⇾ Jι ⟧ʸ}
   → (∀ i → Rι α (f i) (g i))
   → ∀ {n w} → Rι α n w → Rι α (f n) (⟦ κ ⟧ᵐ γ g w)
--
-- The proof is given in the appendix.
--

--
-- Ω preserves the logical relation
--
RΩ : FunExt
   → (α : ℕᴺ)
   → ∀{n w} → Rι α n w → Rι α (α n) (⟦ Ω ⟧ w)
RΩ funExt α {n} {w} = Rκ funExt α ⋆ claim {n} {w}
 where
  mSΑ : (k : ℕ) → monotone (𝑆 (⟦ Α ⟧ k))
  mSΑ k s m r = <→Lt k<|sm|
   where
   k<|s|  : k < len s
   k<|s|  = Lt→< r
   k<|sm| : k < len (s ✦ m)
   k<|sm| = ≤trans k<|s| (≤trans (≤suc' ≤refl) (≤refl' len✦-suc))
  SΑsVΑ : (k : ℕ) → 𝑆 (⟦ Α ⟧ k) secures 𝑉 (⟦ Α ⟧ k)
  SΑsVΑ k s k<|s| α sα = sα k (Lt→< k<|s|)
  claim : ∀ i → Rι α (α i) (⟦ Α ⟧ i)
  claim i = refl , mSΑ i , SΑsVΑ i , Ψ-gBR funExt i


\end{code}

■ Theorem 11. For any closed term Y : ℕᴺ → ℕ of T,

  1. S(YᴶΩ) is a monotone predicate securing Y, and

  2. B(YᴶΩ) is a functional of general bar recursion.

\begin{code}

Thm[gBR] : FunExt
         → (Y : T ε (ιᶥ ⇾ ι))
         →   monotone (𝑆 ⟦ Y ᴶ · Ω ⟧)
           × 𝑆 ⟦ Y ᴶ · Ω ⟧ secures ⟦ Y ⟧
           × gBR (𝑆 ⟦ Y ᴶ · Ω ⟧) (𝐵 ⟦ Y ᴶ · Ω ⟧)
Thm[gBR] funExt Y = mS , SsY , gbr
 where
  --
  -- Extend Rι to R for all types of T
  --
  R : ℕᴺ → {ρ : Ty} → ⟦ ρ ⟧ʸ → ⟦ ⟨ ρ ⟩ᴶ ⟧ʸ → Set
  R α = LR._R_
   where
    import LogicalRelation Jι η κ (Rι α) (Rη α) (Rκ funExt α) as LR
  --
  -- Use the fundamental theorem of logical relation
  --
  fact : ∀ α → Rι α (⟦ Y ⟧ α) ⟦ Y ᴶ · Ω ⟧
  fact α = LR.FTLR Y ⋆ (RΩ funExt α)
   where
    import LogicalRelation Jι η κ (Rι α) (Rη α) (Rκ funExt α) as LR
  mS : monotone (𝑆 ⟦ Y ᴶ · Ω ⟧)
  mS = pr₁ (pr₂ (fact 0ʷ))
  SsY : 𝑆 ⟦ Y ᴶ · Ω ⟧ secures ⟦ Y ⟧
  SsY s sS α sα = begin
     ⟦ Y ⟧ (s ^)
    ≡⟨ pr₁ (fact (s ^)) ⟩
     𝑉 ⟦ Y ᴶ · Ω ⟧ (s ^)
    ≡⟨ pr₁ (pr₂ (pr₂ (fact 0ʷ))) s sS α sα ⟩
     𝑉 ⟦ Y ᴶ · Ω ⟧ α
    ≡⟨ sym (pr₁ (fact α)) ⟩
     ⟦ Y ⟧ α
    ∎
  gbr : gBR (𝑆 ⟦ Y ᴶ · Ω ⟧) (𝐵 ⟦ Y ᴶ · Ω ⟧)
  gbr = pr₂ (pr₂ (pr₂ (fact 0ʷ)))

--
-- Functional of general bar recursion
--
GBF : T ε (ιᶥ ⇾ ι)
    → (ℕ* → ⟦ σ ⟧ʸ) → (ℕ* → (ℕ → ⟦ σ ⟧ʸ) → ⟦ σ ⟧ʸ) → ℕ* → ⟦ σ ⟧ʸ
GBF t = ⟦ B (t ᴶ · Ω) ⟧


\end{code}

■ Spector's Bar-recursion functionals

\begin{code}

private
 --
 -- Step functionals fro general bar recursion
 --
 H : {Γ : Cxt}
   → T Γ ((ιᶥ ⇾ ι)           -- termination functional
        ⇾ (ι* ⇾ σ)           -- base functional for Spector's bar recursion
        ⇾ (ι* ⇾ (ι ⇾ σ) ⇾ σ) -- step functional for Spector's bar recursion
        ⇾ ι* ⇾ (ι ⇾ σ) ⇾ σ)  -- step functional for general bar recursion
 H = Lam (Lam (Lam (Lam (Lam (If · (Minus · Len ν₁ · (ν₄ · ^ ν₁ ^))
                                 · (ν₃ · ν₁)
                                 · (ν₂ · ν₁ · ν₀))))))

 --
 -- Converting general-bar-recursion functional to Spector's one
 --
 Φ : {Γ : Cxt}
   → T Γ ((ιᶥ ⇾ ι)
        ⇾ ((ι* ⇾ σ) ⇾ (ι* ⇾ (ι ⇾ σ) ⇾ σ) ⇾ ι* ⇾ σ)  -- general bar recursion
        ⇾ ((ι* ⇾ σ) ⇾ (ι* ⇾ (ι ⇾ σ) ⇾ σ) ⇾ ι* ⇾ σ)) -- Spector's bar recursion
 Φ = Lam (Lam (Lam (Lam (ν₂ · Lam (Ψ · (ν₄ · ^ ν₀ ^) · ν₂ · ν₁ · ν₀) · (H · ν₃ · ν₁ · ν₀)))))

--
-- Functional of Spector's bar recursion
--
SBF : T ε (ιᶥ ⇾ ι)
    → (ℕ* → ⟦ σ ⟧ʸ) → (ℕ* → (ℕ → ⟦ σ ⟧ʸ) → ⟦ σ ⟧ʸ) → ℕ* → ⟦ σ ⟧ʸ
SBF t = ⟦ Φ · t · B (t ᴶ · Ω) ⟧


\end{code}

■ Appendix : Proofs of
             1. Ψ-gBR : Ψ k is a bar recursion functional for λα.k
             2. Rκ : κ preserves the logical relation

\begin{code}

--
-- [1, Lemma 2.1] : Ψ k is a bar recursion functional for λα.k
--
-- Ψ-gBR : FunExt
--       → (k : ℕ) → gBR (λ s → lt k (len s)) (⟦ Ψ ⟧ k)
--
-- i.e. for any G H s
--
--   k < |s|  →  Ψ k G H s ≡ G s
--   k ≮ |s|  →  Ψ k G H s ≡ H s (λ m → Ψ k G H (s ✦ m)
--
Ψ-gBR funExt k G H s = base , step
 where
  base : ¬ (lt k (len s) ≡ 0)
       → ⟦ Ψ ⟧ k G H s ≡ G s
  base = If-spec₁
  step : lt k (len s) ≡ 0
       → ⟦ Ψ ⟧ k G H s ≡ H s (λ m → ⟦ Ψ ⟧ k G H (s ✦ m))
  step k≮|s| = case claim₀ claim₁ (≤-cases (Lt→≤ k≮|s|))
   where
    E4 : ⟦ Ψ ⟧ k G H s ≡ ⟦ φ ⟧ (suc k - len s) G H s
    E4 = If-spec₀ k≮|s|
    claim₀ : len s ≡ k
           → ⟦ Ψ ⟧ k G H s ≡ H s (λ m → ⟦ Ψ ⟧ k G H (s ✦ m))
    claim₀ |s|≡n = begin
      ⟦ Ψ ⟧ k G H s ≡⟨ E4 ⟩  ⟦ φ ⟧ (suc k - len s) G H s
                    ≡⟨ † ⟩   ⟦ φ ⟧ 1 G H s
                    ≡⟨ E4' ⟩ H s (λ m → ⟦ Ψ ⟧ k G H (s ✦ m)) ∎
     where
      † : ⟦ φ ⟧ (suc k - len s) G H s ≡ ⟦ φ ⟧ 1 G H s
      † = ap (λ x → ⟦ φ ⟧ x G H s)
             (trans (ap (suc k -_) |s|≡n) (Lm[n+1-n≡1] k))
      k+1≡|sm| : {m : ℕ} → suc k ≡ len (s ✦ m)
      k+1≡|sm| = trans (sym (ap suc |s|≡n)) len✦-suc
      k<|sm| : {m : ℕ} → ¬ (lt k (len (s ✦ m)) ≡ 0)
      k<|sm| {m} = <→Lt (≤refl' k+1≡|sm|)
      fact : (m : ℕ) → ⟦ Ψ ⟧ k G H (s ✦ m) ≡ G (s ✦ m)
      fact _ = If-spec₁ k<|sm|
      E4' : H s (λ m → G (s ✦ m)) ≡ H s (λ m → ⟦ Ψ ⟧ k G H (s ✦ m))
      E4' = ap (H s) (sym (funExt fact))
    claim₁ : len s < k
           → ⟦ Ψ ⟧ k G H s ≡ H s (λ m → ⟦ Ψ ⟧ k G H (s ✦ m))
    claim₁ |s|<k = begin
      ⟦ Ψ ⟧ k G H s ≡⟨ E4 ⟩  ⟦ φ ⟧ (suc k - len s) G H s
                    ≡⟨ E3 ⟩  H s (λ m → ⟦ φ ⟧ (k+1-|s|-1) G H (s ✦ m))
                    ≡⟨ □ ⟩   H s (λ m → ⟦ φ ⟧ (suc k - len (s ✦ m)) G H (s ✦ m))
                    ≡⟨ E4' ⟩ H s (λ m → ⟦ Ψ ⟧ k G H (s ✦ m)) ∎
     where
      |s|<k+1 : len s < suc k
      |s|<k+1 = ≤suc' |s|<k
      k+1-|s|-1 : ℕ
      k+1-|s|-1 = pr₁ (Lm[n<m→k+1=m-n] |s|<k+1)
      k+1-|s|-1-spec : suc k+1-|s|-1 ≡ suc k - len s
      k+1-|s|-1-spec = pr₂ (Lm[n<m→k+1=m-n] |s|<k+1)
      E3 : ⟦ φ ⟧ (suc k - len s) G H s ≡ H s (λ m → ⟦ φ ⟧ (k+1-|s|-1) G H (s ✦ m))
      E3 = ap (λ x → ⟦ φ ⟧ x G H s) (sym k+1-|s|-1-spec)
      ex : (m : ℕ)
         → ⟦ φ ⟧ (k+1-|s|-1) G H (s ✦ m) ≡ ⟦ φ ⟧ (suc k - len (s ✦ m)) G H (s ✦ m)
      ex m = ap (λ x → ⟦ φ ⟧ x G H (s ✦ m))
                (trans (Lm[k+1=n+1-m→k=n-m] k k+1-|s|-1-spec)
                       (ap (suc k -_) (len✦-suc {s})))
      □ :  H s (λ m → ⟦ φ ⟧ (k+1-|s|-1) G H (s ✦ m))
         ≡ H s (λ m → ⟦ φ ⟧ (suc k - len (s ✦ m)) G H (s ✦ m))
      □ = ap (H s) (funExt ex)
      n≮|sm| : {m : ℕ} → lt k (len (s ✦ m)) ≡ 0
      n≮|sm| = transport (λ x → lt k x ≡ 0) len✦-suc (≤→Lt |s|<k)
      ex' : (m : ℕ)
          → ⟦ Ψ ⟧ k G H (s ✦ m) ≡ ⟦ φ ⟧ (suc k - len (s ✦ m)) G H (s ✦ m)
      ex' m = If-spec₀ n≮|sm|
      E4' :  H s (λ m → ⟦ φ ⟧ (suc k - len (s ✦ m)) G H (s ✦ m))
           ≡ H s (λ m → ⟦ Ψ ⟧ k G H (s ✦ m))
      E4' = sym (ap (H s) (funExt ex'))


--
-- κ preserves the logical relation
--
-- Rκ : (α : ℕᴺ)
--    → {Γ : Cxt} (γ : ⟦ Γ ⟧ˣ) {f : ⟦ ι ⇾ ι ⟧ʸ} {g : ⟦ ι ⇾ Jι ⟧ʸ}
--    → (∀ i → Rι α (f i) (g i))
--    → ∀ {n w} → Rι α n w → Rι α (f n) (⟦ κ ⟧ᵐ γ g w)
Rκ funExt α γ {f} {g} ζ {n} {Y , S , B} (n≡Yα , mS , SsY , gbr) = e , mSκ , SκsVκ , gbrκ
 where
  e₀ : f n ≡ pr₁ (g n) α
  e₀ = pr₁ (ζ n)
  e₁ : pr₁ (g n) α ≡ pr₁ (g (Y α)) α
  e₁ = ap (λ x → pr₁ (g x) α) n≡Yα
  e : f n ≡ pr₁ (g (Y α)) α
  e = trans e₀ e₁
  mSκ : monotone (𝑆 (⟦ κ ⟧ᵐ γ g (Y , S , B)))
  mSκ s n sSκ = Min-nonzero' _ _ snS snSg
   where
    sS : s ∈ S
    sS = pr₁ (Min-nonzero _ _ sSκ)
    snS : (s ✦ n) ∈ S
    snS = mS s n sS
    Ys≡Ysn : Y (s ^) ≡ Y ((s ✦ n) ^)
    Ys≡Ysn = SsY s sS ((s ✦ n) ^) (s∋sn^ s)
    sSg : s ∈ 𝑆 (g (Y (s ^)))
    sSg = pr₂ (Min-nonzero (S s) _ sSκ)
    snSgs : (s ✦ n) ∈ 𝑆 (g (Y (s ^)))
    snSgs = pr₁ (pr₂ (ζ (Y (s ^)))) s n sSg
    snSg : (s ✦ n) ∈ 𝑆 (g (Y ((s ✦ n) ^)))
    snSg = transport (λ x → (s ✦ n) ∈ 𝑆 (g x)) Ys≡Ysn snSgs
  SκsVκ : (𝑆 (⟦ κ ⟧ᵐ γ g (Y , S , B))) secures (𝑉 (⟦ κ ⟧ᵐ γ g (Y , S , B)))
  SκsVκ s sSκ α sα = begin
     𝑉 (g (Y (s ^))) (s ^)
    ≡⟨ ap (λ x → 𝑉 (g x) (s ^)) Ys≡Yα ⟩
     𝑉 (g (Y α)) (s ^)
    ≡⟨ pr₁ (pr₂ (pr₂ (ζ (Y α)))) s sSgα α sα ⟩
     𝑉 (g (Y α)) α
    ∎
   where
    sS : s ∈ S
    sS = pr₁ (Min-nonzero _ _ sSκ)
    Ys≡Yα : Y (s ^) ≡ Y α
    Ys≡Yα = SsY s sS α sα
    sSg : s ∈ 𝑆 (g (Y (s ^)))
    sSg = pr₂ (Min-nonzero (S s) _ sSκ)
    sSgα : s ∈ 𝑆 (g (Y α))
    sSgα = transport (λ x → s ∈ 𝑆 (g x)) Ys≡Yα sSg
  gbrκ : gBR (𝑆 (⟦ κ ⟧ᵐ γ g (Y , S , B))) (𝐵 (⟦ κ ⟧ᵐ γ g (Y , S , B)))
  gbrκ G H s = base , step
   where
    base : s ∈ 𝑆 (⟦ κ ⟧ᵐ γ g (Y , S , B))
         → 𝐵 (⟦ κ ⟧ᵐ γ g (Y , S , B)) G H s ≡ G s
    base sSκ = begin
       B (λ s' → 𝐵 (g (Y (s' ^))) G H s') H s
      ≡⟨ pr₁ (gbr _ H s) sS ⟩
       𝐵 (g (Y (s ^))) G H s
      ≡⟨ pr₁ (pr₂ (pr₂ (pr₂ (ζ (Y (s ^))))) G H s) sSg ⟩
       G s
      ∎
     where
      sS : s ∈ S
      sS = pr₁ (Min-nonzero _ _ sSκ)
      sSg : s ∈ 𝑆 (g (Y (s ^)))
      sSg = pr₂ (Min-nonzero (S s) _ sSκ)
    step : s ∉ 𝑆 (⟦ κ ⟧ᵐ γ g (Y , S , B))
         →  𝐵 (⟦ κ ⟧ᵐ γ g (Y , S , B)) G H s
          ≡ H s (λ m → 𝐵 (⟦ κ ⟧ᵐ γ g (Y , S , B)) G H (s ✦ m))
    step ¬sSκ = case claim₀ claim₁ (∈-dec S)
     where
      claim₀ : s ∈ S
             →  𝐵 (⟦ κ ⟧ᵐ γ g (Y , S , B)) G H s
              ≡ H s (λ m → 𝐵 (⟦ κ ⟧ᵐ γ g (Y , S , B)) G H (s ✦ m))
      claim₀ sS = begin
         B (λ s' → 𝐵 (g (Y (s' ^))) G H s') H s
        ≡⟨ pr₁ (gbr _ H s) sS ⟩
         𝐵 (g (Y (s ^))) G H s
        ≡⟨ pr₂ (pr₂ (pr₂ (pr₂ (ζ (Y (s ^))))) G H s) ¬sSg ⟩
         H s (λ m → 𝐵 (g (Y (s ^))) G H (s ✦ m))
        ≡⟨ ap (H s) (funExt ex) ⟩
         H s (λ m → 𝐵 (⟦ κ ⟧ᵐ γ g (Y , S , B)) G H (s ✦ m))
        ∎
       where
        ¬sSg : s ∉ 𝑆 (g (Y (s ^)))
        ¬sSg = Min-zero-cases _ _ ¬sSκ sS
        Ys≡Ysm : {m : ℕ} → Y (s ^) ≡ Y ((s ✦ m) ^)
        Ys≡Ysm {m} = SsY s sS ((s ✦ m) ^) (s∋sn^ s)
        ex : (m : ℕ)
           →  𝐵 (g (Y (s ^))) G H (s ✦ m) -- ≡ 𝐵 (⟦ κ ⟧ᵐ γ g (Y , S , B)) G H (s ✦ m)
            ≡ B (λ s' → 𝐵 (g (Y (s' ^))) G H s') H (s ✦ m)
        ex m = begin
          𝐵 (g (Y (s ^))) G H (s ✦ m)
         ≡⟨ ap (λ x → 𝐵 (g x) G H (s ✦ m)) Ys≡Ysm ⟩
          𝐵 (g (Y ((s ✦ m) ^))) G H (s ✦ m)
         ≡⟨ sym (pr₁ (gbr _ H (s ✦ m)) (mS s m sS)) ⟩
          B (λ s' → 𝐵 (g (Y (s' ^))) G H s') H (s ✦ m)
         ∎
      claim₁ : s ∉ S
             →  𝐵 (⟦ κ ⟧ᵐ γ g (Y , S , B)) G H s
              ≡ H s (λ m → 𝐵 (⟦ κ ⟧ᵐ γ g (Y , S , B)) G H (s ✦ m))
      claim₁ = pr₂ (gbr _ H s)

\end{code}
