
 ============================
 =                          =
 =  §1.2  Gödel's System T  =
 =                          =
 ============================

    Chuangjie Xu, July 2019

\begin{code}

{-# OPTIONS --without-K --safe #-}

module T where

open import Preliminaries

\end{code}

■ Types, contexts and terms of T

Here we work with the lambda-calculus version of System T, and with de
Bruijn indices instead of variables.

\begin{code}

infixr 30 _⇾_
infixr 31 _⊠_
infixl 20 _₊_
infixl 20 _·_

--
-- finite types
--
data Ty : Set where
 ι   : Ty
 _⇾_ _⊠_ : Ty → Ty → Ty

--
-- contexts as finite lists of types
--
data Cxt : Set where
 ε   : Cxt
 _₊_ : Cxt → Ty → Cxt

--
-- indices of types/variables in context
--
data ∥_∈_∥ (σ : Ty) : Cxt → Set where
 zero : {Γ : Cxt} → ∥ σ ∈ (Γ ₊ σ) ∥
 suc  : {τ : Ty} {Γ : Cxt} → ∥ σ ∈ Γ ∥ → ∥ σ ∈ Γ ₊ τ ∥

--
-- terms
--
data T (Γ : Cxt) : Ty → Set where
 Var  : {σ : Ty} → ∥ σ ∈ Γ ∥ → T Γ σ
 Lam  : {σ τ : Ty} → T (Γ ₊ σ) τ → T Γ (σ ⇾ τ)
 _·_  : {σ τ : Ty} → T Γ (σ ⇾ τ) → T Γ σ → T Γ τ
 Zero : T Γ ι
 Suc  : T Γ (ι ⇾ ι)
 Rec  : {σ : Ty} → T Γ (σ ⇾ (ι ⇾ σ ⇾ σ) ⇾ ι ⇾ σ)
 Pair : {σ τ : Ty} → T Γ (σ ⇾ τ ⇾ σ ⊠ τ)
 Pr1  : {σ τ : Ty} → T Γ (σ ⊠ τ ⇾ σ)
 Pr2  : {σ τ : Ty} → T Γ (σ ⊠ τ ⇾ τ)

\end{code}

■ The standard interpretation of T into Agda

\begin{code}

⟦_⟧ʸ : Ty → Set
⟦ ι ⟧ʸ     = ℕ
⟦ σ ⇾ τ ⟧ʸ = ⟦ σ ⟧ʸ → ⟦ τ ⟧ʸ
⟦ σ ⊠ τ ⟧ʸ = ⟦ σ ⟧ʸ × ⟦ τ ⟧ʸ

⟦_⟧ˣ : Cxt → Set
⟦ ε ⟧ˣ     = 𝟙
⟦ Γ ₊ ρ ⟧ˣ = ⟦ Γ ⟧ˣ × ⟦ ρ ⟧ʸ

infix 25 _₍_₎

_₍_₎ : {Γ : Cxt} {ρ : Ty} → ⟦ Γ ⟧ˣ → ∥ ρ ∈ Γ ∥ → ⟦ ρ ⟧ʸ
(_ , a) ₍ zero ₎  = a
(γ , _) ₍ suc i ₎ = γ ₍ i ₎

⟦_⟧ᵐ : {Γ : Cxt} {σ : Ty} → T Γ σ → ⟦ Γ ⟧ˣ → ⟦ σ ⟧ʸ
⟦ Var i ⟧ᵐ γ = γ ₍ i ₎
⟦ Lam t ⟧ᵐ γ = λ a → ⟦ t ⟧ᵐ (γ , a)
⟦ f · a ⟧ᵐ γ = ⟦ f ⟧ᵐ γ (⟦ a ⟧ᵐ γ)
⟦ Zero ⟧ᵐ  _ = 0
⟦ Suc ⟧ᵐ   _ = suc
⟦ Rec ⟧ᵐ   _ = rec
⟦ Pair ⟧ᵐ  _ = _,_
⟦ Pr1 ⟧ᵐ   _ = pr₁
⟦ Pr2 ⟧ᵐ   _ = pr₂

⟦_⟧ : {ρ : Ty} → T ε ρ → ⟦ ρ ⟧ʸ
⟦ t ⟧ = ⟦ t ⟧ᵐ ⋆

--
-- An (Agda) element a is "T-definable" if one can find a closed T
-- term whose standard interpretation is a.
--
T-definable : {ρ : Ty} → ⟦ ρ ⟧ʸ → Set
T-definable {ρ} a = Σ \(t : T ε ρ) → ⟦ t ⟧ ≡ a

\end{code}

■ Some auxiliaries

\begin{code}

ν₀ : {Γ : Cxt} {ρ : Ty} → T (Γ ₊ ρ) ρ
ν₀ = Var zero

ν₁ : {Γ : Cxt} {ρ σ : Ty} → T (Γ ₊ ρ ₊ σ) ρ
ν₁ = Var (suc zero)

ν₂ : {Γ : Cxt} {ρ σ₀ σ₁ : Ty} → T (Γ ₊ ρ ₊ σ₀ ₊ σ₁) ρ
ν₂ = Var (suc (suc zero))

ν₃ : {Γ : Cxt} {ρ σ₀ σ₁ σ₂ : Ty} → T (Γ ₊ ρ ₊ σ₀ ₊ σ₁ ₊ σ₂) ρ
ν₃ = Var (suc (suc (suc zero)))

Max : {Γ : Cxt} → T Γ (ι ⇾ ι ⇾ ι)
Max = Rec · Lam ν₀ · Lam (Lam (Rec · (Suc · ν₁) · Lam (Lam (Suc · (ν₂ · ν₁)))))

max : ℕ → ℕ → ℕ
max = ⟦ Max ⟧

Max-spec₀ : (n m : ℕ) → n ≤ max n m
Max-spec₀  0       m      = ≤zero
Max-spec₀ (suc n)  0      = ≤refl
Max-spec₀ (suc n) (suc m) = ≤suc (Max-spec₀ n m)

Max-spec₁ : (n m : ℕ) → m ≤ max n m
Max-spec₁  0       m      = ≤refl
Max-spec₁ (suc n)  0      = ≤zero
Max-spec₁ (suc n) (suc m) = ≤suc (Max-spec₁ n m)

ιᶥ : Ty
ιᶥ = ι ⇾ ι

--
-- Φ g n  is the maximum of g(i) for all i < n.
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
