Chuangjie Xu, November 2026

This module contains the definitions of continuity moduli for
functions of type (ℕ → ℕ) → ℕ.

\begin{code}

{-# OPTIONS --without-K --safe #-}

module Applications.Continuity.Definitions where

open import Preliminaries

\end{code}

■ Moduli of pointwise continuity

\begin{code}

_is-a-modulus-of-continuity-of_ : (ℕᴺ → ℕ) → (ℕᴺ → ℕ) → Set
φ is-a-modulus-of-continuity-of f = ∀ α β → α ≡[ φ α ] β → f α ≡ f β

MoC-is-extensional : {f g φ : ℕᴺ → ℕ} → (∀ α → f α ≡ g α)
                   → φ is-a-modulus-of-continuity-of g
                   → φ is-a-modulus-of-continuity-of f
MoC-is-extensional {f} {g} {φ} ex mcg α β em = begin
  f α ≡⟨ ex α ⟩
  g α ≡⟨ mcg α β em ⟩
  g β ≡⟨ sym (ex β) ⟩
  f β ∎

\end{code}

■ Moduli of uniform continuity on bounded subsets of Baire space

\begin{code}

_is-a-modulus-of-uniform-continuity-of_ : (ℕᴺ → ℕ) → (ℕᴺ → ℕ) → Set
φ is-a-modulus-of-uniform-continuity-of f =
  ∀{δ α β} → α ≤¹ δ → β ≤¹ δ → α ≡[ φ δ ] β → f α ≡ f β

MoUC-is-extensional : {f g φ : ℕᴺ → ℕ} → (∀ α → f α ≡ g α)
                    → φ is-a-modulus-of-uniform-continuity-of g
                    → φ is-a-modulus-of-uniform-continuity-of f
MoUC-is-extensional {f} {g} {φ} ex mcg {δ} {α} {β} u v em = begin
  f α ≡⟨ ex α ⟩
  g α ≡⟨ mcg u v em ⟩
  g β ≡⟨ sym (ex β) ⟩
  f β ∎

\end{code}
