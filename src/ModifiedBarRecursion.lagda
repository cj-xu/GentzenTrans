
 =========================================
 =                                       =
 =  Application: Modified Bar Recursion  =
 =                                       =
 =========================================

    Chuangjie Xu, November 2026

We construct a System T term for modified bar recursion in the sense
of Berger and Oliva [1], using the term for general bar recursion.
We then prove that its interpretation satisfies the defining equation.
The recursors in this module return natural numbers.


References

[1] U. Berger and P. Oliva.  Modified bar recursion.  Mathematical
    Structures in Computer Science, vol. 16, no. 2, pp. 163–183, 2006.

\begin{code}

{-# OPTIONS --without-K --safe #-}

module ModifiedBarRecursion where

open import Preliminaries
open import T
open import TAuxiliaries

open import GeneralBarRecursion ι

\end{code}

For a control functional Y : ℕᴺ → ℕ, modified bar recursion asks for
a functional ξ satisfying the equation below.

Here `s ＠ α` overwrites the first `len s` entries of `α` with `s`.

\begin{code}

MBR : (ℕᴺ → ℕ)
    → ((ℕ* → (ℕ → ℕ) → ℕᴺ) → ℕ* → ℕ)
    → Set
MBR Y ξ = (H : ℕ* → (ℕ → ℕ) → ℕᴺ) (s : ℕ*)
        → ξ H s ≡ Y (s ＠ H s (λ n → ξ H (s ✦ n)))

\end{code}

To convert a general bar recursor into a modified bar recursor for Y,
we use
 - λ s → Y (s ^) as the base functional, and
 - λ s f → Y (s ＠ H s f) as the step functional.

\begin{code}

Θ : {Γ : Cxt}
  → T Γ ((ιᶥ ⇾ ι)
      ⇾ ((ι* ⇾ ι) ⇾ (ι* ⇾ (ι ⇾ ι) ⇾ ι) ⇾ ι* ⇾ ι)  -- general bar recursion
      ⇾ ((ι* ⇾ (ι ⇾ ι) ⇾ ιᶥ) ⇾ ι* ⇾ ι))           -- modified bar recursion
Θ = Lam (Lam (Lam (ν₁ · Lam (ν₃ · ^ ν₀ ^)
                      · Lam (Lam (ν₄ · (Overwrite · ν₁ · (ν₂ · ν₁ · ν₀)))))))

Θ-spec : (Y : ℕᴺ → ℕ)
       → (S : ℕ* → ℕ)
       → (ξ : (ℕ* → ℕ) → (ℕ* → (ℕ → ℕ) → ℕ) → ℕ* → ℕ)
       → (S secures Y × GBR S ξ)
       → MBR Y (⟦ Θ ⟧ Y ξ)
Θ-spec Y S ξ (SsY , gbr) H s = case claim₀ claim₁ (∈-dec S)
 where
  G' : ℕ* → ℕ
  G' u = Y (u ^)
  H' : ℕ* → (ℕ → ℕ) → ℕ
  H' u f = Y (u ＠ H u f)
  F : ℕ* → ℕ
  F = ξ G' H'
  claim₀ : s ∈ S → F s ≡ Y (s ＠ H s (λ n → F (s ✦ n)))
  claim₀ sS = trans e₀ e₁
   where
    e₀ : F s ≡ Y (s ^)
    e₀ = pr₁ (gbr G' H' s) sS
    e₁ : Y (s ^) ≡ Y (s ＠ H s (λ n → F (s ✦ n)))
    e₁ = SsY s sS (s ＠ _) (s∋s＠α s _)
  claim₁ : s ∉ S → F s ≡ Y (s ＠ H s (λ n → F (s ✦ n)))
  claim₁ = pr₂ (gbr G' H' s)

\end{code}

Therefore, for each T-definable control functional, the corresponding
modified bar recursor is T-definable.

\begin{code}

𝐦𝐛𝐫 : T ε (ιᶥ ⇾ ι) → T ε ((ι* ⇾ (ι ⇾ ι) ⇾ ιᶥ) ⇾ ι* ⇾ ι)
𝐦𝐛𝐫 Y = Θ · Y · (𝐠𝐛𝐫 Y)

thm[MBR] : FunExt
         → (Y : T ε (ιᶥ ⇾ ι))
         → MBR ⟦ Y ⟧ ⟦ 𝐦𝐛𝐫 Y ⟧
thm[MBR] fe Y = Θ-spec ⟦ Y ⟧ ⟦ 𝐒 Y ⟧ ⟦ 𝐠𝐛𝐫 Y ⟧ (pr₂ (Thm[GBR] fe Y))

\end{code}
