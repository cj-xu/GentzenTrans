
 ============================
 =                          =
 =  §1.2  Gödel's System T  =
 =                          =
 ============================

    Chuangjie Xu, July 2019

    Updated in February 2020

\begin{code}

{-# OPTIONS --without-K --safe #-}

module TAuxiliaries where

open import Preliminaries
open import T

\end{code}

■ Function composition

\begin{code}

Comp : {Γ : Cxt} {τ₀ τ₁ τ₂ : Ty}
     → T Γ ((τ₁ ⇾ τ₂) ⇾ (τ₀ ⇾ τ₁) ⇾ τ₀ ⇾ τ₂)
Comp = Lam (Lam (Lam (ν₂ · (ν₁ · ν₀))))

_○_ : {Γ : Cxt} {τ₀ τ₁ τ₂ : Ty}
    → T Γ (τ₁ ⇾ τ₂) → T Γ (τ₀ ⇾ τ₁) → T Γ (τ₀ ⇾ τ₂)
t ○ u = Comp · t · u

\end{code}

■ Sequences of natural numbers

\begin{code}

-- Infinite sequences of natural numbers
ιᶥ : Ty
ιᶥ = ι ⇾ ι

Head : {Γ : Cxt} → T Γ (ιᶥ ⇾ ι)
Head = Lam (ν₀ · Zero)

Tail : {Γ : Cxt} → T Γ (ιᶥ ⇾ ιᶥ)
Tail = Lam (Lam (ν₁ · (Suc · ν₀)))

_☆_ : {Γ : Cxt} → T Γ ι → T Γ ιᶥ → T Γ ιᶥ
t ☆ u = Cons · t · u
 where
  Cons : {Γ : Cxt} → T Γ (ι ⇾ ιᶥ ⇾ ιᶥ)
  Cons = Lam (Lam (Rec · ν₁ · Lam (Lam (ν₂ · ν₁))))
  -- λ n u → rec a (λ i _ → u i)
  -- i.e.
  -- Cons n u  0      = n
  -- Cons n u (suc i) = u i

-- Finite sequences of natural numbers
ι* : Ty
ι* = ιᶥ ⊠ ι

^_^ : {Γ : Cxt} → T Γ ι* → T Γ (ι ⇾ ι)
^ t ^ = Pr1 · t

Len : {Γ : Cxt} → T Γ ι* → T Γ ι
Len t = Pr2 · t

_★_ : {Γ : Cxt} → T Γ ι* → T Γ ι → T Γ ι*
t ★ u = Cons · Len t · ^ t ^ · u
 where
  Cons : {Γ : Cxt}
      → T Γ (ι ⇾ ιᶥ ⇾ ι ⇾ ι*)
  Cons = Rec · Lam (Lam (Pair · (Rec · ν₀ · Lam (Lam Zero)) · (Suc · Zero)))
      -- rec  (λ f   v .  (      rec   v   (λ x   y . 0)    , 1 ))
             · Lam (Lam (Lam (Lam (Pair · (Rec · (ν₁ · Zero) · Lam (Lam (Pr1 · (ν₄ · (ν₃ ○ Suc) · ν₂) · ν₁)))
      --      (λ n   z    f    v .  (      rec    (f   0)     (λ i   g . pr₁   (z    (f ∘ suc)    v)    i)
                                        · (Suc · (Suc · ν₃))))))
      --                                ,  suc   (suc   n) ) )

\end{code}

■ Max and Min fucntions

\begin{code}

Max : {Γ : Cxt} → T Γ (ι ⇾ ι ⇾ ι)
Max = Rec · Lam ν₀
          · Lam (Lam (Rec · (Suc · ν₁) · Lam (Lam (Suc · (ν₂ · ν₁)))))

max : ℕ → ℕ → ℕ
max = ⟦ Max ⟧

Max-correct₀ : {n m : ℕ} → m ≤ n → max n m ≡ n
Max-correct₀ {0}      ≤zero   = refl
Max-correct₀ {suc n}  ≤zero   = refl
Max-correct₀         (≤suc r) = ap suc (Max-correct₀ r)

Max-correct₁ : {n m : ℕ} → n ≤ m → max n m ≡ m
Max-correct₁  ≤zero   = refl
Max-correct₁ (≤suc r) = ap suc (Max-correct₁ r)

Max-spec₀ : (n m : ℕ) → n ≤ max n m
Max-spec₀  0       m      = ≤zero
Max-spec₀ (suc n)  0      = ≤refl
Max-spec₀ (suc n) (suc m) = ≤suc (Max-spec₀ n m)

Max-spec₁ : (n m : ℕ) → m ≤ max n m
Max-spec₁  0       m      = ≤refl
Max-spec₁ (suc n)  0      = ≤zero
Max-spec₁ (suc n) (suc m) = ≤suc (Max-spec₁ n m)

Min : {Γ : Cxt} → T Γ (ι ⇾ ι ⇾ ι)
Min = Rec · Lam Zero
          · Lam (Lam (Rec · Zero · Lam (Lam (Suc · (ν₂ · ν₁)))))

min : ℕ → ℕ → ℕ
min = ⟦ Min ⟧

Min-correct₀ : {n m : ℕ} → n ≤ m → min n m ≡ n
Min-correct₀  ≤zero   = refl
Min-correct₀ (≤suc r) = ap suc (Min-correct₀ r)

Min-correct₁ : {n m : ℕ} → m ≤ n → min n m ≡ m
Min-correct₁ {zero}  {0}  ≤zero   = refl
Min-correct₁ {suc n} {0}  ≤zero   = refl
Min-correct₁             (≤suc r) = ap suc (Min-correct₁ r)

Min-spec₀ : (n m : ℕ) → min n m ≤ n
Min-spec₀  0       m      = ≤zero
Min-spec₀ (suc n)  0      = ≤zero
Min-spec₀ (suc n) (suc m) = ≤suc (Min-spec₀ n m)

Min-spec₁ : (n m : ℕ) → min n m ≤ m
Min-spec₁  0       m      = ≤zero
Min-spec₁ (suc n)  0      = ≤zero
Min-spec₁ (suc n) (suc m) = ≤suc (Min-spec₁ n m)

\end{code}

■ The largest value of an initial fragment of an infinite sequence

\begin{code}

--
-- Φ g n  is the maximum of g(i) for all i ≤ n.
--
Φ : {Γ : Cxt} → T Γ (ιᶥ ⇾ ι ⇾ ι)
Φ = Lam (Rec · (ν₀ · Zero) · Lam (Lam (Max · ν₀ · (ν₂ · (Suc · ν₁)))))
-- i.e.
-- Φ g  0      = g 0
-- Φ g (suc n) = max (Φ g n) (g (suc n))

Φ-spec : {i j : ℕ} → i ≤ j
       → {Γ : Cxt} (γ : ⟦ Γ ⟧ˣ)
       → (α : ℕᴺ) → α i ≤ ⟦ Φ ⟧ᵐ γ α j
Φ-spec {i} {0} ≤zero _ α = ≤refl
Φ-spec {i} {suc j} r _ α with ≤-cases r
Φ-spec {i} {suc j} r γ α | inl refl = Max-spec₁ (⟦ Φ ⟧ᵐ γ α j) (α (suc j))
Φ-spec {i} {suc j} r γ α | inr i≤j  = ≤trans (Φ-spec i≤j γ α) (Max-spec₀ (⟦ Φ ⟧ᵐ γ α j) (α (suc j)))

\end{code}

■ Less-than function

\begin{code}

𝟎 𝟏 : {Γ : Cxt} → T Γ ι
𝟎 = Zero
𝟏 = Suc · Zero

--
-- Lt n m = 1  iff  n < m.
--
Lt : {Γ : Cxt} → T Γ (ι ⇾ ι ⇾ ι)
Lt = Rec · (Rec · 𝟎 · Lam (Lam 𝟏))
         · Lam (Lam (Rec · 𝟎 · Lam (Lam (ν₂ · ν₁))))

Lt-spec₀ : {n m : ℕ} → n < m → ⟦ Lt ⟧ n m ≡ 1
Lt-spec₀ {0}     {suc m} (≤suc r) = refl
Lt-spec₀ {suc n} {suc m} (≤suc r) = Lt-spec₀ r

Lt-spec₀' : {n m : ℕ} → ⟦ Lt ⟧ n m ≡ 1 → n < m
Lt-spec₀' {0}     {suc m} _ = ≤suc ≤zero
Lt-spec₀' {suc n} {suc m} e = ≤suc (Lt-spec₀' e)

Lt-spec₁ : {n m : ℕ} → m ≤ n → ⟦ Lt ⟧ n m ≡ 0
Lt-spec₁ {0}     {0}      ≤zero   = refl
Lt-spec₁ {suc n} {0}      ≤zero   = refl
Lt-spec₁ {suc n} {suc m} (≤suc r) = Lt-spec₁ r

Lt-spec₁' : {n m : ℕ} → ⟦ Lt ⟧ n m ≡ 0 → m ≤ n
Lt-spec₁' {0}     {0}     _ = ≤zero
Lt-spec₁' {suc n} {0}     _ = ≤zero
Lt-spec₁' {suc n} {suc m} e = ≤suc (Lt-spec₁' e)

\end{code}

■ If function

\begin{code}

If : {Γ : Cxt} {τ : Ty}
   → T Γ (ι ⇾ τ ⇾ τ ⇾ τ)
If = Rec · Lam (Lam ν₀) · Lam (Lam (Lam (Lam ν₁)))

If-spec₀ : {τ : Ty} {a b : ⟦ τ ⟧ʸ}
         → ⟦ If ⟧ 0 a b ≡ b
If-spec₀ = refl

If-spec₁ : {τ : Ty} {a b : ⟦ τ ⟧ʸ} {n : ℕ}
         → ⟦ If ⟧ (suc n) a b ≡ a
If-spec₁ = refl

\end{code}

■ Addition and subtraction

\begin{code}

Num : ℕ → {Γ : Cxt} → T Γ ι
Num  0      = Zero
Num (suc n) = Suc · Num n

Plus Minus : {Γ : Cxt} → T Γ (ι ⇾ ι ⇾ ι)
Plus  = Rec · Lam ν₀   · Lam (Lam (Lam (Suc · (ν₁ · ν₀))))
Minus = Rec · Lam Zero · Lam (Lam (Rec · (Suc · ν₁) · Lam (Lam (ν₂ · ν₁))))

\end{code}

