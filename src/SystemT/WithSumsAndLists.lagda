System T with binary sums and finite lists

This syntax extends the intrinsically typed terms of SystemT.Base.

\begin{code}

{-# OPTIONS --without-K --safe #-}

module SystemT.WithSumsAndLists where

open import Preliminaries

\end{code}

■ Types, contexts and terms of T

\begin{code}

infixr 30 _⇾_
infixr 31 _⊠_
infixr 31 _⊞_
infixl 20 _₊_
infixl 20 _·_

mutual
 data Ty : Set where
  dataᵀ : DataTy → Ty
  _⇾_ _⊠_ : Ty → Ty → Ty

 data DataTy : Set where
  nat  : DataTy
  sum  : Ty → Ty → DataTy
  list : Ty → DataTy

pattern ι = dataᵀ nat
pattern _⊞_ σ τ = dataᵀ (sum σ τ)
pattern Listᵀ σ = dataᵀ (list σ)

data Cxt : Set where
 ε   : Cxt
 _₊_ : Cxt → Ty → Cxt

data ∥_∈_∥ (σ : Ty) : Cxt → Set where
 zero : {Γ : Cxt} → ∥ σ ∈ (Γ ₊ σ) ∥
 suc  : {τ : Ty} {Γ : Cxt} → ∥ σ ∈ Γ ∥ → ∥ σ ∈ Γ ₊ τ ∥

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
 Inj1 : {σ τ : Ty} → T Γ (σ ⇾ σ ⊞ τ)
 Inj2 : {σ τ : Ty} → T Γ (τ ⇾ σ ⊞ τ)
 Case : {σ τ ρ : Ty} → T Γ ((σ ⇾ ρ) ⇾ (τ ⇾ ρ) ⇾ σ ⊞ τ ⇾ ρ)
 Nil  : {σ : Ty} → T Γ (Listᵀ σ)
 Cons : {σ : Ty} → T Γ (σ ⇾ Listᵀ σ ⇾ Listᵀ σ)
 LRec : {σ ρ : Ty} → T Γ (ρ ⇾ (σ ⇾ Listᵀ σ ⇾ ρ ⇾ ρ) ⇾ Listᵀ σ ⇾ ρ)

\end{code}

■ The standard interpretation of T into Agda

\begin{code}

⟦_⟧ʸ : Ty → Set
⟦ ι ⟧ʸ     = ℕ
⟦ σ ⇾ τ ⟧ʸ = ⟦ σ ⟧ʸ → ⟦ τ ⟧ʸ
⟦ σ ⊠ τ ⟧ʸ = ⟦ σ ⟧ʸ × ⟦ τ ⟧ʸ

⟦ σ ⊞ τ ⟧ʸ = ⟦ σ ⟧ʸ + ⟦ τ ⟧ʸ
⟦ Listᵀ σ ⟧ʸ = List ⟦ σ ⟧ʸ

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

⟦ Inj1 ⟧ᵐ _ = inl
⟦ Inj2 ⟧ᵐ _ = inr
⟦ Case ⟧ᵐ _ = case
⟦ Nil  ⟧ᵐ _ = []
⟦ Cons ⟧ᵐ _ = _∷_
⟦ LRec ⟧ᵐ _ = listrec

⟦_⟧ : {ρ : Ty} → T ε ρ → ⟦ ρ ⟧ʸ
⟦ t ⟧ = ⟦ t ⟧ᵐ ⋆

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

\end{code}

■ Auxiliaries

\begin{code}

Comp : {Γ : Cxt} {τ₀ τ₁ τ₂ : Ty}
     → T Γ ((τ₁ ⇾ τ₂) ⇾ (τ₀ ⇾ τ₁) ⇾ τ₀ ⇾ τ₂)
Comp = Lam (Lam (Lam (ν₂ · (ν₁ · ν₀))))

_○_ : {Γ : Cxt} {τ₀ τ₁ τ₂ : Ty}
    → T Γ (τ₁ ⇾ τ₂) → T Γ (τ₀ ⇾ τ₁) → T Γ (τ₀ ⇾ τ₂)
t ○ u = Comp · t · u

\end{code}
