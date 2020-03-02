
 =========================================
 =                                       =
 =  A Kolmogorov-style translation of T  =
 =                                       =
 =========================================

    Chuangjie Xu, July 2019

References.

□ Tarmo Uustalu.  Monad translating inductive and coinductive types.
  In: H. Geuvers, F. Wiedijk (Eds.), Types for Proofs and Programs
  (TYPES 2002). Lecture Notes in Computer Science, vol 2646, Springer,
  2002, pp. 299–315.

\begin{code}

{-# OPTIONS --without-K --safe #-}

open import T

module KolmogorovTranslation
      (J : Ty → Ty)
      (η : {Γ : Cxt} {σ : Ty} → T Γ (σ ⇾ J σ))
      (κ : {Γ : Cxt} {σ τ : Ty} → T Γ ((σ ⇾ J τ) ⇾ J σ ⇾ J τ))
 where

⟨_⟩ᴷᵒ ⟨_⟩ : Ty → Ty
⟨ ρ ⟩ᴷᵒ   = J ⟨ ρ ⟩
⟨ ι ⟩     = ι
⟨ σ ⊠ τ ⟩ = ⟨ σ ⟩ᴷᵒ ⊠ ⟨ τ ⟩ᴷᵒ
⟨ σ ⇾ τ ⟩ = ⟨ σ ⟩ᴷᵒ ⇾ ⟨ τ ⟩ᴷᵒ

⟪_⟫ᴷᵒ : Cxt → Cxt
⟪ ε ⟫ᴷᵒ     = ε
⟪ Γ ₊ ρ ⟫ᴷᵒ = ⟪ Γ ⟫ᴷᵒ ₊ ⟨ ρ ⟩ᴷᵒ

⟨_⟩ᵛ : {Γ : Cxt} {ρ : Ty} → ∥ ρ ∈ Γ ∥ → ∥ ⟨ ρ ⟩ᴷᵒ ∈ ⟪ Γ ⟫ᴷᵒ ∥
⟨ zero ⟩ᵛ  = zero
⟨ suc i ⟩ᵛ = suc ⟨ i ⟩ᵛ

infixl 20 _◇_

_◇_ : {Γ : Cxt} {σ τ : Ty} → T Γ (J (σ ⇾ J τ)) → T Γ σ → T Γ (J τ)
f ◇ a = ◇Ap · f · a
     -- κ (λ h → h a) f
 where
  ◇Ap : {Γ : Cxt} {σ τ : Ty} → T Γ (J (σ ⇾ J τ) ⇾ σ ⇾ J τ)
  ◇Ap = Lam (Lam (κ · Lam (ν₀ · ν₁) · ν₁))

Rec◇ : {Γ : Cxt} {ρ : Ty} → T Γ (ρ ⇾ (J ι ⇾ J (J ρ ⇾ J ρ)) ⇾ ι ⇾ J ρ)
Rec◇ = Lam (Lam (Rec · (η · ν₁) · Lam (Lam (ν₂ · (η · ν₁) ◇ ν₀))))
--   Rec◇(a,f,0) := η(a)
-- Rec◇(a,f,n+1) := f(ηn) ◇ Rec◇(a,f,n)

infix 60 _ᴷᵒ

_ᴷᵒ : {Γ : Cxt} {ρ : Ty} → T Γ ρ → T ⟪ Γ ⟫ᴷᵒ ⟨ ρ ⟩ᴷᵒ
Var i ᴷᵒ   = Var ⟨ i ⟩ᵛ
Lam t ᴷᵒ   = η · Lam (t ᴷᵒ)
(f · a) ᴷᵒ = f ᴷᵒ ◇ a ᴷᵒ
Pair ᴷᵒ    = η · Lam (η · Lam (η · (Pair · ν₁ · ν₀)))
Pr1 ᴷᵒ     = η · (κ · Pr1)
Pr2 ᴷᵒ     = η · (κ · Pr2)
Zero ᴷᵒ    = η · Zero
Suc ᴷᵒ     = η · (κ · Lam (η · (Suc · ν₀)))
Rec ᴷᵒ     = η · (κ · Lam (η · (κ · Lam (η · (κ · (Rec◇ · ν₁ · ν₀))))))

\end{code}
