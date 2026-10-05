
 ======================
 =                    =
 =  Gödel's System T  =
 =                    =
 ======================

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

■ Variables

\begin{code}

ν₀ : {Γ : Cxt} {ρ : Ty} → T (Γ ₊ ρ) ρ
ν₀ = Var zero

ν₁ : {Γ : Cxt} {ρ σ : Ty} → T (Γ ₊ ρ ₊ σ) ρ
ν₁ = Var (suc zero)

ν₂ : {Γ : Cxt} {ρ σ₀ σ₁ : Ty} → T (Γ ₊ ρ ₊ σ₀ ₊ σ₁) ρ
ν₂ = Var (suc (suc zero))

ν₃ : {Γ : Cxt} {ρ σ₀ σ₁ σ₂ : Ty} → T (Γ ₊ ρ ₊ σ₀ ₊ σ₁ ₊ σ₂) ρ
ν₃ = Var (suc (suc (suc zero)))

ν₄ : {Γ : Cxt} {ρ σ₀ σ₁ σ₂ σ₃ : Ty} → T (Γ ₊ ρ ₊ σ₀ ₊ σ₁ ₊ σ₂ ₊ σ₃) ρ
ν₄ = Var (suc (suc (suc (suc zero))))

\end{code}
