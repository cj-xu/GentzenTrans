
 =============================================
 =                                           =
 =  §2  A Gentzen-style monadic translation  =
 =                                           =
 =============================================

    Chuangjie Xu, February 2020

We prove an instance of the Fundamental Theorem of logical relation to
demonstrate the soundness of the monadic translation in the sense that
each term of T is related to its translation.

For this, we have to assume that a relation Rι ⊆ ℕ × Jℕ is given such
that it holds for the nucleus, i.e. Rη and Rκ hold.

\begin{code}

{-# OPTIONS --without-K --safe #-}

open import Preliminaries
open import T

module LogicalRelation
       (Jι : Ty)
       (η  : {Γ : Cxt} → T Γ (ι ⇾ Jι))
       (κ  : {Γ : Cxt} → T Γ ((ι ⇾ Jι) ⇾ Jι ⇾ Jι))
       (_Rι_ : ⟦ ι ⟧ʸ → ⟦ Jι ⟧ʸ → Set)
       (Rη : {Γ : Cxt} (γ : ⟦ Γ ⟧ˣ) (n : ⟦ ι ⟧ʸ) → n Rι ⟦ η ⟧ᵐ γ n)
       (Rκ : {Γ : Cxt} (γ : ⟦ Γ ⟧ˣ) {f : ⟦ ι ⇾ ι ⟧ʸ} {g : ⟦ ι ⇾ Jι ⟧ʸ}
           → (∀ i → f i Rι g i) → ∀ {n a} → n Rι a → f n Rι ⟦ κ ⟧ᵐ γ g a)
 where

open import GentzenTranslation Jι η κ

\end{code}

■ Extend Rι to a logical relation R for arbitrary types

\begin{code}

_R_ : {ρ : Ty} → ⟦ ρ ⟧ʸ → ⟦ ⟨ ρ ⟩ᴶ ⟧ʸ → Set
_R_ {ι} = _Rι_
_R_ {σ ⊠ τ} u v = (pr₁ u R pr₁ v) × (pr₂ u R pr₂ v)
_R_ {σ ⇾ τ} f g = ∀{x y} → x R y → f x R g y

--
-- Extend R for contexts
--
_Rˣ_ : {Γ : Cxt} → ⟦ Γ ⟧ˣ → ⟦ ⟪ Γ ⟫ᴶ ⟧ˣ → Set
_Rˣ_ {ε} ⋆ ⋆ = 𝟙
_Rˣ_ {Γ ₊ ρ} (γ , x) (δ , a) = (γ Rˣ δ) × (x R a)

--
-- Corresponding variables in related contexts are related.
--
R[Var] : {Γ : Cxt} {ρ : Ty} {γ : ⟦ Γ ⟧ˣ} {δ : ⟦ ⟪ Γ ⟫ᴶ ⟧ˣ}
       → γ Rˣ δ → (i : ∥ ρ ∈ Γ ∥) → (γ ₍ i ₎) R (δ ₍ ⟨ i ⟩ᵛ ₎)
R[Var] (_ , θ)  zero   = θ
R[Var] (ξ , _) (suc i) = R[Var] ξ i

--
-- KE (the extension of κ) preserves the logical relation
--
R[KE] : {ρ : Ty} {Γ : Cxt} {γ : ⟦ Γ ⟧ˣ} {f : ⟦ ι ⇾ ρ ⟧ʸ} {g : ⟦ ι ⇾ ⟨ ρ ⟩ᴶ ⟧ʸ}
      → (∀ i → f i R g i) → f R (⟦ KE ⟧ᵐ γ g)
R[KE] {ι} = Rκ _
R[KE] {σ ⊠ τ} ζ χ = R[KE] (pr₁ ∘ ζ) χ , R[KE] (pr₂ ∘ ζ) χ
R[KE] {σ ⇾ τ} ζ χ θ = R[KE] (λ i → ζ i θ) χ

\end{code}

■ Fundamental Theorem of Logical Relation

\begin{code}

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
FTLR Rec _ {x} {a} χ {f} {g} ξ = R[KE] claim
 where
  claim : ∀ i → rec x f i R rec a _ i
  claim  0      = χ
  claim (suc i) = ξ (Rη _ i) (claim i)

\end{code}
