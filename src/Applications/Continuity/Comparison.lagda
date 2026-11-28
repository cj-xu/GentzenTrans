Chuangjie Xu, November 2026

This module compares the moduli extracted by the Gentzen and
Kuroda translations.

\begin{code}

{-# OPTIONS --without-K --safe #-}

module Applications.Continuity.Comparison where

open import Preliminaries
open import SystemT.Base

import Applications.Continuity.PointwiseViaGentzen as Gentzen
import Applications.Continuity.PointwiseViaKuroda as Kuroda

t : T ε ((ι ⇾ ι) ⇾ ι)
t = Lam (Rec · (ν₀ · Zero) · Lam (Lam Zero) · (Suc · Zero))

t-zero : (α : ℕᴺ) → ⟦ t ⟧ α ≡ 0
t-zero α = refl

gentzen-modulus-zero : (α : ℕᴺ) → ⟦ Gentzen.𝐌 t ⟧ α ≡ 0
gentzen-modulus-zero α = refl

kuroda-modulus-one : (α : ℕᴺ) → ⟦ Kuroda.𝐌 t ⟧ α ≡ 1
kuroda-modulus-one α = refl

\end{code}
