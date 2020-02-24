
 ==========================
 =                        =
 =  §3.1  Majorizability  =
 =                        =
 ==========================

    Chuangjie Xu, July 2019

    Updated in February 2020

We construct majorants of T-terms via the monadic translation whose
correctness is guaranteed by the Fundamental Theorem of Logical Relation.

\begin{code}

{-# OPTIONS --without-K --safe #-}

open import Preliminaries
open import T

module Majorizability where

\end{code}

■ A nucleus for majorizability

\begin{code}

Jι : Ty
Jι = ι

η : {Γ : Cxt} → T Γ (ι ⇾ Jι)
η = Lam ν₀
--   λn.n

--
-- κ g n  is the maximum of g(i) for all i < n.
--
κ : {Γ : Cxt} → T Γ ((ι ⇾ Jι) ⇾ Jι ⇾ Jι)
κ = Φ
-- Lam (Rec · (ν₀ · Zero) · Lam (Lam (Max · ν₀ · (ν₂ · (Suc · ν₁)))))
-- i.e.
-- κ g  0      = g 0
-- κ g (suc n) = max (κ g n) (g (suc n))

κ-spec : {i j : ℕ} → i ≤ j
       → {Γ : Cxt} (γ : ⟦ Γ ⟧ˣ)
       → (g : ℕ → ℕ) → g i ≤ ⟦ κ ⟧ᵐ γ g j
κ-spec = Φ-spec

--
-- Instantiate the translation by importing the following module
-- with the nucleus (Jι, η, κ)
--
open import GentzenTranslation Jι η κ

\end{code}

■ Howard's majorizability relation

\begin{code}

--
-- The base case is just the usual ordering on ℕ
--
_⊲ι_ : ⟦ ι ⟧ʸ → ⟦ Jι ⟧ʸ → Set
_⊲ι_ = _≤_

--
-- η preserves the logical relation
--
⊲η : {Γ : Cxt} (γ : ⟦ Γ ⟧ˣ) (n : ⟦ ι ⟧ʸ) → n ⊲ι ⟦ η ⟧ᵐ γ n
⊲η _ n = ≤refl

--
-- κ preserves the logical relation
--
⊲κ : {Γ : Cxt} (γ : ⟦ Γ ⟧ˣ) {f : ⟦ ι ⇾ ι ⟧ʸ} {g : ⟦ ι ⇾ Jι ⟧ʸ}
   → (∀ i → f i ⊲ι g i) → ∀ {n a} → n ⊲ι a → f n ⊲ι ⟦ κ ⟧ᵐ γ g a
⊲κ γ {f} {g} ζ {x} θ = ≤trans (ζ x) (κ-spec θ γ g)

open import LogicalRelation Jι η κ _⊲ι_ ⊲η ⊲κ

--
-- Howard's majorizability relation extends ≤ to all types of T
--
_⊲_ : {ρ : Ty} → ⟦ ρ ⟧ʸ → ⟦ ⟨ ρ ⟩ᴶ ⟧ʸ → Set
_⊲_ = _R_
-- i.e.
-- n ⊲ι     m = n ≤ m
-- u ⊲[σ×τ] v = (pr₁ u ⊲σ pr₁ v) ∧ (pr₂ u ⊲τ pr₂ v)
-- f ⊲[σ→τ] g = ∀ x y → x ⊲σ y → f x ⊲τ g y

\end{code}

■ Corollary: Every closed T term is majorized by its translation.

\begin{code}

Cor[Maj] : {ρ : Ty} (t : T ε ρ) → ⟦ t ⟧ ⊲ ⟦ t ᴶ ⟧
Cor[Maj] t = FTLR t ⋆

\end{code}
