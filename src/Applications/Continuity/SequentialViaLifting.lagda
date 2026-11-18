
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

■ Continuous convergences at pure finite types

\begin{code}

_is-eventually-equal-to_ : (ℕ → ℕ) → ℕ → Set
α is-eventually-equal-to n = Σ \(m : ℕ) → ∀ {k} → m ≤ k → α k ≡ n

converges : (n : ℕ) → (ℕ → type n) → type n → Set
converges  0      ns n = ns is-eventually-equal-to n
converges (suc n) fs f
  = (xs : ℕ → type n) (x : type n)
  → converges n xs x
  → (λ i → fs i (xs i)) is-eventually-equal-to (f x)

\end{code}

■ Sequential continuity of type-3 functionals relative to
  continuous convergence of type-2 inputs

\begin{code}

is-sequentially-continuous : type 3 → Set
is-sequentially-continuous H = converges 3 (λ _ → H) H

sequential-continuity-spec
  : {H : type 3}
  → is-sequentially-continuous H
  ≡ (∀ fs f → converges 2 fs f → (H ∘ fs) is-eventually-equal-to (H f))
sequential-continuity-spec = refl

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
sc-Ω {u} qu fs f cf = cf as a ca
 where
  as : ℕ → type 1
  as k n = u (λ _ → n) (fs k)
  a : type 1
  a n = u (λ _ → n) f
  pointwise : (n : ℕ) → (λ k → as k n) is-eventually-equal-to (a n)
  pointwise n = qu (sc-η n) fs f cf
  ca : converges 1 as a
  ca ns n (m , en) = max m l , proof
   where
    l : ℕ
    l = pr₁ (pointwise n)
    proof : ∀ {k} → max m l ≤ k → as k (ns k) ≡ a n
    proof {k} p = trans
      (ap (as k) (en (≤trans (Max-spec₀ m l) p)))
      (pr₂ (pointwise n) (≤trans (Max-spec₁ m l) p))

Thm[SC3] : FunExt
         → (t : T ε (typeᵀ 3))
         → is-sequentially-continuous ⟦ t ⟧
Thm[SC3] funext = P[T-definable] funext sc-Ω

\end{code}
