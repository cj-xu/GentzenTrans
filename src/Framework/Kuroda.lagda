
 =====================================
 =                                   =
 =  A Kuroda-style translation of T  =
 =                                   =
 =====================================

    Chuangjie Xu, July 2019

    Updated in October 2026 and restructured in November 2026

This module defines a Kuroda-style monadic translation of System T
and proves its fundamental theorem of logical relations. Its
call-by-value treatment of application follows Section 3 of [1].
The translated function and argument are both handled through the
Kleisli operation before application. The translation is parametrized
by a type-indexed nucleus, and soundness follows from the compatibility
conditions.

References.

[1] Thomas Powell. A unifying framework for continuity and complexity
    in higher types. Logical Methods in Computer Science 16(3),
    Article 17, 2020. doi:10.23638/LMCS-16(3:17)2020.

\begin{code}

{-# OPTIONS --without-K --safe #-}

open import Preliminaries
open import SystemT.Base
open import SystemT.Auxiliaries

module Framework.Kuroda
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

●Ap : {Γ : Cxt} {σ τ : Ty} → T Γ (J (σ ⇾ J τ) ⇾ J σ ⇾ J τ)
●Ap = Lam (Lam (κ · Lam (κ · ν₀ · ν₁) · ν₁))

_●_ : {Γ : Cxt} {σ τ : Ty} → T Γ (J (σ ⇾ J τ)) → T Γ (J σ) → T Γ (J τ)
f ● a = ●Ap · f · a
     -- κ (λ h → κ h a) f

Rec● : {Γ : Cxt} {ρ : Ty} → T Γ (ρ ⇾ (ι ⇾ J (ρ ⇾ J ρ)) ⇾ ι ⇾ J ρ)
Rec● = Lam (Lam (Rec · (η · ν₁) · Lam (Lam (ν₂ · ν₁ ● ν₀))))
--   Rec●(a,f,0) = η(a)
-- Rec●(a,f,n+1) = f(n) ● Rec●(a,f,n)

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

■ Logical relation

Given a computation relation C on interpretations, we define the
value relation V and extend it pointwise to assignments.

\begin{code}

module LogicalRelation
       (C : (ρ : Ty) → ⟦ ρ ⟧ʸ → ⟦ J ⟨ ρ ⟩ ⟧ʸ → Set)
 where

 V : (ρ : Ty) → ⟦ ρ ⟧ʸ → ⟦ ⟨ ρ ⟩ ⟧ʸ → Set
 V ι n a = n ≡ a
 V (σ ⊠ τ) x a = V σ (pr₁ x) (pr₁ a) × V τ (pr₂ x) (pr₂ a)
 V (σ ⇾ τ) f g = ∀ {x a} → V σ x a → C τ (f x) (g a)

 Vˣ : (Γ : Cxt) → ⟦ Γ ⟧ˣ → ⟦ ⟪ Γ ⟫ ⟧ˣ → Set
 Vˣ ε ⋆ ⋆ = 𝟙
 Vˣ (Γ ₊ ρ) (γ , x) (δ , a) = Vˣ Γ γ δ × V ρ x a

 V[Var] : {Γ : Cxt} {ρ : Ty}
        → {γ : ⟦ Γ ⟧ˣ} {δ : ⟦ ⟪ Γ ⟫ ⟧ˣ}
        → Vˣ Γ γ δ → (i : ∥ ρ ∈ Γ ∥)
        → V ρ (γ ₍ i ₎) (δ ₍ ⟨ i ⟩ᵛ ₎)
 V[Var] (_ , θ) zero = θ
 V[Var] (ξ , _) (suc i) = V[Var] ξ i

\end{code}

■ Compatibility conditions on the nucleus operations

\begin{code}

 η-compatible : Set
 η-compatible
   = {Γ : Cxt} {ρ : Ty} (γ : ⟦ Γ ⟧ˣ)
   → ∀ {x a} → V ρ x a → C ρ x (⟦ η ⟧ᵐ γ a)

 κ-compatible : Set
 κ-compatible
   = {Γ : Cxt} {σ τ : Ty} (γ : ⟦ Γ ⟧ˣ)
   → {f : ⟦ σ ⟧ʸ → ⟦ τ ⟧ʸ} {g : ⟦ ⟨ σ ⟩ ⟧ʸ → ⟦ J ⟨ τ ⟩ ⟧ʸ}
   → (∀ {x a} → V σ x a → C τ (f x) (g a))
   → ∀ {x w} → C σ x w → C τ (f x) (⟦ κ ⟧ᵐ γ g w)

\end{code}

■ Fundamental theorem of logical relations

\begin{code}

 module Soundness (Rη : η-compatible) (Rκ : κ-compatible) where

  C[●] : {Γ : Cxt} {σ τ : Ty} {γ : ⟦ Γ ⟧ˣ}
       → {f : ⟦ σ ⇾ τ ⟧ʸ} {F : ⟦ J ⟨ σ ⇾ τ ⟩ ⟧ʸ}
         {x : ⟦ σ ⟧ʸ} {a : ⟦ J ⟨ σ ⟩ ⟧ʸ}
       → C (σ ⇾ τ) f F → C σ x a
       → C τ (f x) (⟦ ●Ap ⟧ᵐ γ F a)
  C[●] {σ = σ} {τ = τ} φ χ = Rκ {σ = σ ⇾ τ} _ (λ θ → Rκ _ θ χ) φ

  C[Rec●] : {Γ : Cxt} {ρ : Ty} {γ : ⟦ Γ ⟧ˣ}
          → {a : ⟦ ρ ⟧ʸ} {b : ⟦ ⟨ ρ ⟩ ⟧ʸ}
          → V ρ a b
          → {f : ℕ → ⟦ ρ ⟧ʸ → ⟦ ρ ⟧ʸ} {g : ⟦ ⟨ ι ⇾ ρ ⇾ ρ ⟩ ⟧ʸ}
          → V (ι ⇾ ρ ⇾ ρ) f g
          → (n : ℕ) → C ρ (rec a f n) (⟦ Rec● ⟧ᵐ γ b g n)
  C[Rec●] θ ψ 0 = Rη _ θ
  C[Rec●] θ ψ (suc n) = C[●] (ψ refl) (C[Rec●] θ ψ n)

  FTLR : {Γ : Cxt} {ρ : Ty} (t : T Γ ρ)
       → {γ : ⟦ Γ ⟧ˣ} {δ : ⟦ ⟪ Γ ⟫ ⟧ˣ}
       → Vˣ Γ γ δ
       → C ρ (⟦ t ⟧ᵐ γ) (⟦ t ᴷ ⟧ᵐ δ)
  FTLR (Var i) ξ = Rη _ (V[Var] ξ i)
  FTLR (Lam t) ξ = Rη _ (λ {_} {_} θ → FTLR t (ξ , θ))
  FTLR (f · a) ξ = C[●] (FTLR f ξ) (FTLR a ξ)
  FTLR Pair ξ = Rη _ (λ {_} {_} θ → Rη _ (λ {_} {_} ψ → Rη _ (θ , ψ)))
  FTLR Pr1 ξ = Rη _ (λ {_} {_} θ → Rη _ (pr₁ θ))
  FTLR Pr2 ξ = Rη _ (λ {_} {_} θ → Rη _ (pr₂ θ))
  FTLR Zero ξ = Rη _ refl
  FTLR Suc ξ = Rη _ (λ {_} {_} θ → Rη _ (ap suc θ))
  FTLR (Rec {σ = ρ}) ξ
    = Rη _ (λ {_} {_} θ →
        Rη _ (λ {_} {_} ψ →
          Rη _ (λ { {n} refl → C[Rec●] θ ψ n })))

\end{code}
