
 =====================================
 =                                   =
 =  A Kuroda-style translation of T  =
 =                                   =
 =====================================

    Chuangjie Xu, July 2019

References.

□ Thomas Powell.  A functional interpretation with state.  In:
  Proceedings of the Thirty third Annual IEEE Symposium on Logic in
  Computer Science (LICS 2018), IEEE Computer Society Press, 2018,
  pp. 839–848.

\begin{code}

{-# OPTIONS --without-K --safe #-}

open import T
open import TAuxiliaries

module KurodaTranslation
       (J : Ty → Ty)
       (η : {Γ : Cxt} {σ : Ty} → T Γ (σ ⇾ J σ))
       (κ : {Γ : Cxt} {σ τ : Ty} → T Γ ((σ ⇾ J τ) ⇾ J σ ⇾ J τ))
 where

⟨_⟩ᴷ ⟨_⟩ : Ty → Ty
⟨ ρ ⟩ᴷ    = J ⟨ ρ ⟩
⟨ ι ⟩     = ι
⟨ σ ⊠ τ ⟩ = ⟨ σ ⟩ ⊠ ⟨ τ ⟩
⟨ σ ⇾ τ ⟩ = ⟨ σ ⟩ ⇾ J ⟨ τ ⟩

⟪_⟫ : Cxt → Cxt
⟪ ε ⟫     = ε
⟪ Γ ₊ ρ ⟫ = ⟪ Γ ⟫ ₊ ⟨ ρ ⟩

⟨_⟩ᵛ : {Γ : Cxt} {ρ : Ty} → ∥ ρ ∈ Γ ∥ → ∥ ⟨ ρ ⟩ ∈ ⟪ Γ ⟫ ∥
⟨ zero ⟩ᵛ  = zero
⟨ suc i ⟩ᵛ = suc ⟨ i ⟩ᵛ

infixl 20 _●_

_●_ : {Γ : Cxt} {σ τ : Ty} → T Γ (J (σ ⇾ J τ)) → T Γ (J σ) → T Γ (J τ)
f ● a = ●Ap · f · a
     -- κ (λ h → κ h a) f
 where
  ●Ap : {Γ : Cxt} {σ τ : Ty} → T Γ (J (σ ⇾ J τ) ⇾ J σ ⇾ J τ)
  ●Ap = Lam (Lam (κ · Lam (κ · ν₀ · ν₁) · ν₁))

Rec● : {Γ : Cxt} {ρ : Ty} → T Γ (ρ ⇾ (ι ⇾ J (ρ ⇾ J ρ)) ⇾ ι ⇾ J ρ)
Rec● = Lam (Lam (Rec · (η · ν₁) · Lam (Lam (ν₂ · ν₁ ● ν₀))))
--   Rec●(a,f,0) = η(a)
-- Rec●(a,f,n+1) = fn ● Rec●(a,f,n)

infix 60 _ᴷ

_ᴷ : {Γ : Cxt} {ρ : Ty} → T Γ ρ → T ⟪ Γ ⟫ ⟨ ρ ⟩ᴷ
Var i ᴷ   = η · Var ⟨ i ⟩ᵛ
Lam t ᴷ   = η · Lam (t ᴷ)
(f · a) ᴷ = f ᴷ ● a ᴷ
Pair ᴷ    = η · Lam (η · Lam (η · (Pair · ν₁ · ν₀)))
Pr1 ᴷ     = η · (η ○ Pr1)
Pr2 ᴷ     = η · (η ○ Pr2)
Zero ᴷ    = η · Zero
Suc ᴷ     = η · (η ○ Suc)
Rec ᴷ     = η · Lam (η · Lam (η · (Rec● · ν₁ · ν₀)))

\end{code}
