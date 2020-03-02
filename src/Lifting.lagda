
 ===============================================
 =                                             =
 =  §3.2  Lifting to higher-order functionals  =
 =                                             =
 ===============================================

    Chuangjie Xu, July 2019

    Updated in February 2020

\begin{code}

{-# OPTIONS --without-K --safe #-}

open import Preliminaries
open import T
open import TAuxiliaries

\end{code}

■ A nucleus for lifting to higher types

\begin{code}

module Lifting (X : Ty) where

Jι : Ty
Jι = X ⇾ ι

η : {Γ : Cxt} → T Γ (ι ⇾ Jι)
η = Lam (Lam ν₁)
 -- λ n  x . n

κ : {Γ : Cxt} → T Γ ((ι ⇾ Jι) ⇾ Jι ⇾ Jι)
κ = Lam (Lam (Lam (ν₂ · (ν₁ · ν₀) · ν₀)))
 -- λ g   f    x . g     (f  x)    x

--
-- Instantiate the translation by importing the following module
-- with the nucleus (Jι, η, κ)
--
open import GentzenTranslation Jι η κ

\end{code}

■ Relating terms and their lifting via a parametrized logical relation

\begin{code}

--
-- Base case of the logical relation
--
Rι : ⟦ X ⟧ʸ → ⟦ ι ⟧ʸ → ⟦ Jι ⟧ʸ → Set
Rι x n f = n ≡ f x

--
-- η preserves the logical relation
--
Rη : (x : ⟦ X ⟧ʸ)
   → {Γ : Cxt} (γ : ⟦ Γ ⟧ˣ) (n : ⟦ ι ⟧ʸ) → Rι x n (⟦ η ⟧ᵐ γ n)
Rη x _ n = refl

--
-- κ preserves the logical relation
--
Rκ : (x : ⟦ X ⟧ʸ)
   → {Γ : Cxt} (γ : ⟦ Γ ⟧ˣ) {f : ⟦ ι ⇾ ι ⟧ʸ} {g : ⟦ ι ⇾ Jι ⟧ʸ}
   → (∀ i → Rι x (f i) (g i)) → ∀ {n h} → Rι x n h → Rι x (f n) (⟦ κ ⟧ᵐ γ g h)
Rκ x γ {f} {g} ζ {n} {h} θ = transport (λ z → f n ≡ g z x) θ (ζ n)

--
-- Extend Rι to R for all types of T
--
R : ⟦ X ⟧ʸ → {ρ : Ty} → ⟦ ρ ⟧ʸ → ⟦ ⟨ ρ ⟩ᴶ ⟧ʸ → Set
R x = LR._R_
 where
  import LogicalRelation Jι η κ (Rι x) (Rη x) (Rκ x) as LR

\end{code}

■ If one can construct a generic element Ω : Xᴶ such that R x x Ω,
  then f = fᴶΩ up to pointwise equality.

\begin{code}

Cor : (Ω : T ε ⟨ X ⟩ᴶ) → (∀ x → R x x ⟦ Ω ⟧)
    → (t : T ε (X ⇾ ι))
    → ∀ x → ⟦ t ⟧ x ≡ ⟦ t ᴶ · Ω ⟧ x
Cor Ω r t x = LR.FTLR t ⋆ (r x)
 where
  import LogicalRelation Jι η κ (Rι x) (Rη x) (Rκ x) as LR

\end{code}
