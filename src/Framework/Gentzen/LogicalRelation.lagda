
 ==============================================
 =                                            =
 =  Logical Relation and Fundamental Theorem  =
 =                                            =
 ==============================================

    Chuangjie Xu, February 2020

    Restructured in November 2026

We prove a fundamental theorem of logical relations for the monadic
translation of System T. The theorem establishes soundness by showing
that each term and its translation have related interpretations under
related assignments.

For this, we fix a base relation Rι between ℕ and ⟦ Jι ⟧ʸ and assume
that the nucleus operations η and κ are compatible with it.

\begin{code}

{-# OPTIONS --without-K --safe #-}

open import Preliminaries
open import SystemT.Base

module Framework.Gentzen.LogicalRelation
       (Jι : Ty)
       (η  : {Γ : Cxt} → T Γ (ι ⇾ Jι))
       (κ  : {Γ : Cxt} → T Γ ((ι ⇾ Jι) ⇾ Jι ⇾ Jι))
       (_Rι_ : ⟦ ι ⟧ʸ → ⟦ Jι ⟧ʸ → Set)
 where

open import Framework.Gentzen.Translation Jι η κ

\end{code}

■ Extend Rι to a logical relation R for arbitrary types

\begin{code}

_R_ : {ρ : Ty} → ⟦ ρ ⟧ʸ → ⟦ ⟨ ρ ⟩ᴶ ⟧ʸ → Set
_R_ {ι} = _Rι_
_R_ {σ ⊠ τ} u v = (pr₁ u R pr₁ v) × (pr₂ u R pr₂ v)
_R_ {σ ⇾ τ} f g = ∀{x y} → x R y → f x R g y

_Rˣ_ : {Γ : Cxt} → ⟦ Γ ⟧ˣ → ⟦ ⟪ Γ ⟫ᴶ ⟧ˣ → Set
_Rˣ_ {ε} ⋆ ⋆ = 𝟙
_Rˣ_ {Γ ₊ ρ} (γ , x) (δ , a) = (γ Rˣ δ) × (x R a)

R[Var] : {Γ : Cxt} {ρ : Ty} {γ : ⟦ Γ ⟧ˣ} {δ : ⟦ ⟪ Γ ⟫ᴶ ⟧ˣ}
       → γ Rˣ δ → (i : ∥ ρ ∈ Γ ∥) → (γ ₍ i ₎) R (δ ₍ ⟨ i ⟩ᵛ ₎)
R[Var] (_ , θ)  zero   = θ
R[Var] (ξ , _) (suc i) = R[Var] ξ i

\end{code}

■ Compatibility conditions on the nucleus operations

\begin{code}

η-compatible : Set
η-compatible = {Γ : Cxt} (γ : ⟦ Γ ⟧ˣ) (n : ⟦ ι ⟧ʸ) → n Rι ⟦ η ⟧ᵐ γ n

κ-compatible : Set
κ-compatible = {Γ : Cxt} (γ : ⟦ Γ ⟧ˣ) {f : ⟦ ι ⇾ ι ⟧ʸ} {g : ⟦ ι ⇾ Jι ⟧ʸ}
             → (∀ i → f i Rι g i) → ∀ {n a} → n Rι a → f n Rι ⟦ κ ⟧ᵐ γ g a

R[KE] : κ-compatible
      → {ρ : Ty} {Γ : Cxt} {γ : ⟦ Γ ⟧ˣ} {f : ⟦ ι ⇾ ρ ⟧ʸ} {g : ⟦ ι ⇾ ⟨ ρ ⟩ᴶ ⟧ʸ}
      → (∀ i → f i R g i) → f R (⟦ KE ⟧ᵐ γ g)
R[KE] Rκ {ι} = Rκ _
R[KE] Rκ {σ ⊠ τ} ζ χ = R[KE] Rκ (pr₁ ∘ ζ) χ , R[KE] Rκ (pr₂ ∘ ζ) χ
R[KE] Rκ {σ ⇾ τ} ζ χ θ = R[KE] Rκ (λ i → ζ i θ) χ

\end{code}

■ Fundamental theorem of logical relations

\begin{code}

module Soundness (Rη : η-compatible) (Rκ : κ-compatible) where

 FTLR : {Γ : Cxt} {ρ : Ty} (t : T Γ ρ)
      → {γ : ⟦ Γ ⟧ˣ} {δ : ⟦ ⟪ Γ ⟫ᴶ ⟧ˣ} → γ Rˣ δ
      → ⟦ t ⟧ᵐ γ R ⟦ t ᴶ ⟧ᵐ δ
 FTLR (Var i) ξ = R[Var] ξ i
 FTLR (Lam t) ξ = λ θ → FTLR t (ξ , θ)
 FTLR (f · a) ξ = FTLR f ξ (FTLR a ξ)
 FTLR Pair _ θ δ = θ , δ
 FTLR Pr1 _ = pr₁
 FTLR Pr2 _ = pr₂
 FTLR Zero _ = Rη _ zero
 FTLR Suc _ = Rκ _ (Rη _ ∘ suc)
 FTLR Rec _ {x} {a} χ {f} {g} ξ = R[KE] Rκ claim
  where
   claim : ∀ i → rec x f i R rec a _ i
   claim  0      = χ
   claim (suc i) = ξ (Rη _ i) (claim i)

\end{code}
