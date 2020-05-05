
 =========================
 =                       =
 =  §3.4  Bar recursion  =
 =                       =
 =========================

    Chuangjie Xu, May 2020


We implement the reviewer's example of definining moduli of uniform
continuity using functionals of general bar recursion.

\begin{code}

{-# OPTIONS --without-K --safe #-}

open import Preliminaries
open import T
open import TAuxiliaries
open import BarRecursion ι public
open import UniformContinuity

⟨⟩ : ℕ*
⟨⟩ = (λ n → n) , 0

MB : T ε (ιᶥ ⇾ ι) → ℕᴺ → ℕ
MB t δ = GBF t G H ⟨⟩
 where
  G : ℕ* → ℕ
  G _ = 0
  H : ℕ* → ℕᴺ → ℕ
  H (_ , n) f = suc (⟦ Φ ⟧ f (δ n))

1ʷ : ℕᴺ
1ʷ = λ i → 1

\end{code}
