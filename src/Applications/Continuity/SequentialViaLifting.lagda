
 =============================================================
 =                                                           =
 =  Application: Sequential continuity at type 3 via lifting =
 =                                                           =
 =============================================================

    Chuangjie Xu, November 2026

We use the lifting nucleus to prove that T-definable type-3 functionals are
sequentially continuous relative to continuous convergence of type-2 inputs.

\begin{code}

{-# OPTIONS --without-K --safe #-}

module Applications.Continuity.SequentialViaLifting where

open import Preliminaries
open import SystemT.Base
open import SystemT.Auxiliaries

\end{code}

■ Continuous convergences

\begin{code}

_is-eventually-equal-to_ : (ℕ → type 0) → type 0 → Set
ns is-eventually-equal-to n = Σ \(m : ℕ) → ∀ {k} → m ≤ k → ns k ≡ n

_converges-pointwise-to_ : (ℕ → type 1) → type 1 → Set
αs converges-pointwise-to α
 = (n : ℕ) → (λ i → αs i n) is-eventually-equal-to (α n)

_converges-continuously-to_ : (ℕ → type 2) → type 2 → Set
fs converges-continuously-to f
 = (αs : ℕ → type 1) (α : type 1)
 → αs converges-pointwise-to α
 → (λ i → fs i (αs i)) is-eventually-equal-to (f α)

\end{code}

■ Sequential continuity of type-3 functionals relative to
  continuous convergence of type-2 inputs

\begin{code}

is-sequentially-continuous : type 3 → Set
is-sequentially-continuous H
 = (fs : ℕ → type 2) (f : type 2)
 → fs converges-continuously-to f
 → (λ i → H (fs i)) is-eventually-equal-to (H f)

\end{code}

■ Sequential continuity of T-definable type-3 functionals
  via the type-2 lifting nucleus

\begin{code}

open import Applications.Lifting (typeᵀ 2)

sc-η : (n : ℕ) → is-sequentially-continuous (λ _ → n)
sc-η n _ _ _ = 0 , (λ _ → refl)

sc-κ : {g : ℕ → type 3}
     → (∀ n → is-sequentially-continuous (g n))
     → {h : type 3} → is-sequentially-continuous h
     → is-sequentially-continuous (λ x → g (h x) x)
sc-κ {g} sg {h} sh fs f cf = max m n , proof
 where
  eh : (h ∘ fs) is-eventually-equal-to (h f)
  eh = sh fs f cf
  eg : (g (h f) ∘ fs) is-eventually-equal-to (g (h f) f)
  eg = sg (h f) fs f cf
  m n : ℕ
  m = pr₁ eh
  n = pr₁ eg
  proof : ∀ {k} → max m n ≤ k → g (h (fs k)) (fs k) ≡ g (h f) f
  proof {k} p = trans
    (ap (λ i → g i (fs k)) (pr₂ eh (≤trans (Max-spec₀ m n) p)))
    (pr₂ eg (≤trans (Max-spec₁ m n) p))

open PredicateUsage is-sequentially-continuous sc-η sc-κ

sc-Ω : Q {typeᵀ 2} ⟦ Ω ⟧
sc-Ω {u} qu fs f cf = cf αs α cα
 where
  αs : ℕ → type 1
  αs k n = u (λ _ → n) (fs k)
  α : type 1
  α n = u (λ _ → n) f
  cα : αs converges-pointwise-to α
  cα n = qu (sc-η n) fs f cf

Thm[SC3] : FunExt
         → (t : T ε (typeᵀ 3))
         → is-sequentially-continuous ⟦ t ⟧
Thm[SC3] funext = P[T-definable] funext sc-Ω

\end{code}
