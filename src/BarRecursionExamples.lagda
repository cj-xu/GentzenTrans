
 ===============================================================
 =                                                             =
 =  Application: Uniform Continuity via General Bar Recursion  =
 =                                                             =
 ===============================================================

    Chuangjie Xu, May 2020


We implement the reviewer's example of defining moduli of uniform
continuity using functionals of general bar recursion.

\begin{code}

{-# OPTIONS --without-K --safe #-}

open import Preliminaries
open import T
open import TAuxiliaries
open import BarRecursion ι public
open import UniformContinuity

\end{code}

For a fixed bound δ, `MB t δ` starts the recursion at the empty sequence.
If the current sequence secures `t`, the base case returns 0. Otherwise,
the step takes one plus the maximum of the recursive bounds for the
possible next inputs i ≤ δ(length s). Thus two inputs bounded by δ that
agree up to this bound follow the same branch; induction on the computed
bound gives equality of their values under `t`.

This correctness argument is not yet formalized in this module.

\begin{code}

⟨⟩ : ℕ*
⟨⟩ = (λ n → n) , 0

MB : T ε (ιᶥ ⇾ ι) → ℕᴺ → ℕ
MB t δ = GBF t G H ⟨⟩
 where
  G : ℕ* → ℕ
  G _ = 0
  H : ℕ* → ℕᴺ → ℕ
  H (_ , n) f = suc (⟦ Φ ⟧ f (δ n))

\end{code}
