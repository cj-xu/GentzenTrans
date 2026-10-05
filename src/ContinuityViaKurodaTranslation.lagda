
 ===========================================
 =                                         =
 =  Continuity via the Kuroda Translation  =
 =                                         =
 ===========================================

    Chuangjie Xu, September 2022

This module instantiates the Kuroda-style monadic translation with a
nucleus for pointwise continuity.

\begin{code}

{-# OPTIONS --without-K --safe #-}

module ContinuityViaKurodaTranslation where

open import T
open import TAuxiliaries

\end{code}

A computation carries both a value and a bound on the input sequence
needed to determine that value. The operations η and κ introduce and
combine these bounds.

\begin{code}

J : Ty → Ty
J σ = ι ⇾ ιᶥ ⇾ σ ⊠ ι

η : {Γ : Cxt} {σ : Ty} → T Γ (σ ⇾ J σ)
η = Lam (Lam (Lam (Pair · ν₂ · ν₁)))
-- λ x n α . ⟨ x , n ⟩

κ : {Γ : Cxt} {σ τ : Ty} → T Γ ((σ ⇾ J τ) ⇾ J σ ⇾ J τ)
κ = Lam (Lam (Lam (Lam (Pair · (Pr1 · (ν₃ · (Pr1 · (ν₂ · ν₁ · ν₀)) · ν₁ · ν₀))
                             · (Max · (Max · (Pr2 · (ν₃ · (Pr1 · (ν₂ · ν₁ · ν₀)) · ν₁ · ν₀)) · (Pr2 · (ν₂ · ν₁ · ν₀))) · ν₁)))))
-- λ f x n α . ⟨ (f((xnα)₁,n,α))₁ , max((f((xnα)₁,n,α))₂,(xnα)₂,n) ⟩

open import KurodaTranslation J η κ

\end{code}

The generic element Ω records each query to the input sequence.
For a closed System T term f of type (ι ⇾ ι) ⇾ ι, the term M f
extracts the bound from the translation of f applied to Ω.

\begin{code}

Ω : {Γ : Cxt} → T Γ (J (ι ⇾ J ι))
Ω = η · Lam (Lam (Lam (Pair · (ν₀ · ν₂) · (Max · (Suc · ν₂) · ν₁))))
-- η (λ n m α . ⟨ αn , max(n+1,m) ⟩)

M : T ε (ιᶥ ⇾ ι) → T ε ((ι ⇾ ι) ⇾ ι)
M f = Lam (Lam (Pr2 · (ν₁ · ν₀))) · (f ᴷ ● Ω · Zero)
-- pr₂ ∘ ((fᴷ • Ω) 0)

\end{code}
