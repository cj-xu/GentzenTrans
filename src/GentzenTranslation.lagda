
 =============================================
 =                                           =
 =  §2  A Gentzen-style monadic translation  =
 =                                           =
 =============================================

    Chuangjie Xu, July 2019

    Updated in February 2020

We introduce a notion of a nucleus relative to System T, namely a
monad-like structure without restriction to satisfy the monad laws.
Then we present a syntactic translation of T into itself parametrized
by a nucleus. The translation structurally corresponds to Gentzen's
negative translation of classical logic.

\begin{code}

{-# OPTIONS --without-K --safe #-}

open import Preliminaries
open import T

module GentzenTranslation
       (Jι : Ty)
       (η  : {Γ : Cxt} → T Γ (ι ⇾ Jι))
       (κ  : {Γ : Cxt} → T Γ ((ι ⇾ Jι) ⇾ Jι ⇾ Jι))
 where

\end{code}

■ A syntactic translation of T parametrized by the nucleus (Jι, η, κ)

\begin{code}

--
-- Translate types
--
⟨_⟩ᴶ : Ty → Ty
⟨ ι ⟩ᴶ     = Jι
⟨ σ ⊠ τ ⟩ᴶ = ⟨ σ ⟩ᴶ ⊠ ⟨ τ ⟩ᴶ
⟨ σ ⇾ τ ⟩ᴶ = ⟨ σ ⟩ᴶ ⇾ ⟨ τ ⟩ᴶ

--
-- Translate contexts
--
⟪_⟫ᴶ : Cxt → Cxt
⟪ ε ⟫ᴶ     = ε
⟪ Γ ₊ ρ ⟫ᴶ = ⟪ Γ ⟫ᴶ ₊ ⟨ ρ ⟩ᴶ

⟨_⟩ᵛ : {Γ : Cxt} {ρ : Ty} → ∥ ρ ∈ Γ ∥ → ∥ ⟨ ρ ⟩ᴶ ∈ ⟪ Γ ⟫ᴶ ∥
⟨ zero ⟩ᵛ  = zero
⟨ suc i ⟩ᵛ = suc ⟨ i ⟩ᵛ

--
-- Extend κ to all types of T
--
KE : {ρ : Ty} {Γ : Cxt}
   → T Γ ((ι ⇾ ⟨ ρ ⟩ᴶ) ⇾ Jι ⇾ ⟨ ρ ⟩ᴶ)
KE {ι}     = κ
KE {τ ⊠ ρ} = Lam (Lam (Pair · (KE · Lam (Pr1 · (ν₂ · ν₀)) · ν₀)
                            · (KE · Lam (Pr2 · (ν₂ · ν₀)) · ν₀)))
KE {τ ⇾ ρ} = Lam (Lam (Lam (KE · Lam (ν₃ · ν₀ · ν₁) · ν₁)))

infix 60 _ᴶ
--
-- Translate terms
--
_ᴶ : {Γ : Cxt} {ρ : Ty} → T Γ ρ → T ⟪ Γ ⟫ᴶ ⟨ ρ ⟩ᴶ
Var i ᴶ   = Var ⟨ i ⟩ᵛ
Lam t ᴶ   = Lam (t ᴶ)
(f · a) ᴶ = f ᴶ · a ᴶ
Pair ᴶ    = Pair
Pr1 ᴶ     = Pr1
Pr2 ᴶ     = Pr2
Zero ᴶ    = η · Zero
Suc ᴶ     = κ · Lam (η · (Suc · ν₀))
         -- κ (η ∘ suc)
Rec{ρ} ᴶ  = Lam (Lam (KE · (Rec · ν₁ · Lam (ν₁ · (η · ν₀)))))
         -- λ a   f . KE (  rec ( a  ,      f ∘ η ))

\end{code}
