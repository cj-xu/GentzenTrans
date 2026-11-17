
 ========================================
 =                                      =
 =  Application: Spector Bar Recursion  =
 =                                      =
 ========================================

    Chuangjie Xu, February 2020

    Updated in May 2020 and November 2026

Following Oliva and Steila [1], we construct a System T term for
Spector’s bar recursion from the term for general bar recursion.


Update in November 2026:

- We prove that the interpretation of the constructed term satisfies
  Spector's bar-recursion equations.


References

[1] P. Oliva and S. Steila.  A direct proof of Schwichtenberg's bar
    recursion closure theorem.  The Journal of Symbolic Logic, vol. 83,
    no. 1, pp. 70–83, 2018.

\begin{code}

{-# OPTIONS --without-K --safe #-}

open import T

module SpectorBarRecursion (σ : Ty) where

open import Preliminaries
open import TAuxiliaries

open import GeneralBarRecursion σ

\end{code}

Spector's bar recursion is controlled by a function Y : (ℕ → ℕ) → ℕ.
It asks for a function ξ : (ℕ* → A) → (ℕ* → (ℕ → A) → A) → ℕ* → A
satisfying

    (Y (s ^) < | s | → ξ G H s ≡ G s)
  × (Y (s ^) ≥ | s | → ξ G H s ≡ H s (λ n → ξ G H (s ✦ n))).

We define this specification by reusing the one for general bar recursion.

\begin{code}

SBR : {A : Set}
    → ((ℕ → ℕ) → ℕ)
    → ((ℕ* → A) → (ℕ* → (ℕ → A) → A) → ℕ* → A)
    → Set
SBR Y = GBR (λ s → lt (Y (s ^)) (len s))

\end{code}

We construct a step functional for general bar recursion from
the base and step functionals G and H for Spector's bar recursion.
It returns G s when Spector's stopping condition holds;
otherwise, it applies H s to the continuation.

\begin{code}

𝐻 : {Γ : Cxt}
  → T Γ ((ιᶥ ⇾ ι)          -- termination functional
      ⇾ (ι* ⇾ σ)           -- base functional for Spector's bar recursion
      ⇾ (ι* ⇾ (ι ⇾ σ) ⇾ σ) -- step functional for Spector's bar recursion
      ⇾ ι* ⇾ (ι ⇾ σ) ⇾ σ)  -- step functional for general bar recursion
𝐻 = Lam (Lam (Lam (Lam (Lam (If · (Minus · Len ν₁ · (ν₄ · ^ ν₁ ^))
                                · (ν₃ · ν₁)
                                · (ν₂ · ν₁ · ν₀))))))

𝐻-spec : (Y : ℕᴺ → ℕ) (G : ℕ* → ⟦ σ ⟧ʸ)
       → (H : ℕ* → (ℕ → ⟦ σ ⟧ʸ) → ⟦ σ ⟧ʸ)
       → (s : ℕ*) (f : ℕ → ⟦ σ ⟧ʸ)
       → (¬ (lt (Y (s ^)) (len s) ≡ 0) → ⟦ 𝐻 ⟧ Y G H s f ≡ G s)
       × (   lt (Y (s ^)) (len s) ≡ 0  → ⟦ 𝐻 ⟧ Y G H s f ≡ H s f)
𝐻-spec Y G H s f = claim₀ , claim₁
 where
  claim₀ : ¬ (lt (Y (s ^)) (len s) ≡ 0) → ⟦ 𝐻 ⟧ Y G H s f ≡ G s
  claim₀ q = If-spec₁ (Lm[n<m→m-n≠0] (Y (s ^)) (len s) (Lt→< q))
  claim₁ : lt (Y (s ^)) (len s) ≡ 0 → ⟦ 𝐻 ⟧ Y G H s f ≡ H s f
  claim₁ p = If-spec₀ (Lm[n≤m→n-m=0] (len s) (Y (s ^)) (Lt→≤ p))

\end{code}

To convert a general bar recursor into a Spector bar recursor for Y,
we use
 - λ s → Ψ (Y (s ^)) G H s as the base functional, and
 - 𝐻 Y G H as the step functional.

\begin{code}

Θ : {Γ : Cxt}
  → T Γ ((ιᶥ ⇾ ι)
      ⇾ ((ι* ⇾ σ) ⇾ (ι* ⇾ (ι ⇾ σ) ⇾ σ) ⇾ ι* ⇾ σ)  -- general bar recursion
      ⇾ ((ι* ⇾ σ) ⇾ (ι* ⇾ (ι ⇾ σ) ⇾ σ) ⇾ ι* ⇾ σ)) -- Spector's bar recursion
Θ = Lam (Lam (Lam (Lam (ν₂ · Lam (Ψ · (ν₄ · ^ ν₀ ^) · ν₂ · ν₁ · ν₀)
                           · (𝐻 · ν₃ · ν₁ · ν₀)))))

Θ-spec : FunExt
       → (Y : ℕᴺ → ℕ)
       → (S : ℕ* → ℕ)
       → (ξ : (ℕ* → ⟦ σ ⟧ʸ) → (ℕ* → (ℕ → ⟦ σ ⟧ʸ) → ⟦ σ ⟧ʸ) → ℕ* → ⟦ σ ⟧ʸ)
       → (monotone S × S secures Y × GBR S ξ)
       → SBR Y (⟦ Θ ⟧ Y ξ)
Θ-spec fe Y S ξ (mS , SsY , gbr) G H s = case claim₀ claim₁ (∈-dec S)
 where
  G' : ℕ* → ⟦ σ ⟧ʸ
  G' u = ⟦ Ψ ⟧ (Y (u ^)) G H u
  H' : ℕ* → (ℕ → ⟦ σ ⟧ʸ) → ⟦ σ ⟧ʸ
  H' = ⟦ 𝐻 ⟧ Y G H
  F : ℕ* → ⟦ σ ⟧ʸ
  F = ξ G' H'
  P : Set
  P = (¬ (lt (Y (s ^)) (len s) ≡ 0) → F s ≡ G s)
    × (   lt (Y (s ^)) (len s) ≡ 0  → F s ≡ H s (λ n → F (s ✦ n)))
  claim₀ : s ∈ S → P
  claim₀ sS = sclaim₀ , sclaim₁
   where
    e : F s ≡ G' s
    e = pr₁ (gbr G' H' s) sS
    gbrΨ = Ψ-GBR fe (Y (s ^)) G H s
    sclaim₀ : ¬ (lt (Y (s ^)) (len s) ≡ 0) → F s ≡ G s
    sclaim₀ p = trans e (pr₁ gbrΨ p)
    sclaim₁ : lt (Y (s ^)) (len s) ≡ 0 → F s ≡ H s (λ n → F (s ✦ n))
    sclaim₁ p = trans e (trans e' e'')
     where
      e' : G' s ≡ H s (λ n → ⟦ Ψ ⟧ (Y (s ^)) G H (s ✦ n))
      e' = pr₂ gbrΨ p
      ex : (n : ℕ) → ⟦ Ψ ⟧ (Y (s ^)) G H (s ✦ n) ≡ F (s ✦ n)
      ex n = trans e₀ (sym e₁)
       where
        eY : Y (s ^) ≡ Y ((s ✦ n) ^)
        eY = SsY s sS ((s ✦ n) ^) (s∋sn^ s)
        e₀ : ⟦ Ψ ⟧ (Y (s ^)) G H (s ✦ n) ≡ G' (s ✦ n)
        e₀ = ap (λ k → ⟦ Ψ ⟧ k G H (s ✦ n)) eY
        e₁ : F (s ✦ n) ≡ G' (s ✦ n)
        e₁ = pr₁ (gbr G' H' (s ✦ n)) (mS s n sS)
      e'' : H s (λ n → ⟦ Ψ ⟧ (Y (s ^)) G H (s ✦ n)) ≡ H s (λ n → F (s ✦ n))
      e'' = ap (H s) (fe ex)
  claim₁ : s ∉ S → P
  claim₁ nsS = (λ p → trans e (pr₁ hs p)) , (λ p → trans e (pr₂ hs p))
   where
    e : F s ≡ H' s (λ n → F (s ✦ n))
    e = pr₂ (gbr G' H' s) nsS
    hs : (¬ (lt (Y (s ^)) (len s) ≡ 0) → H' s (λ n → F (s ✦ n)) ≡ G s)
       × (   lt (Y (s ^)) (len s) ≡ 0  → H' s (λ n → F (s ✦ n)) ≡ H s (λ n → F (s ✦ n)))
    hs = 𝐻-spec Y G H s (λ n → F (s ✦ n))

\end{code}

Therefore, for each T-definable control functional, the corresponding
Spector bar recursor is T-definable.

\begin{code}

𝐬𝐛𝐫 : T ε (ιᶥ ⇾ ι) → T ε ((ι* ⇾ σ) ⇾ (ι* ⇾ (ι ⇾ σ) ⇾ σ) ⇾ ι* ⇾ σ)
𝐬𝐛𝐫 Y = Θ · Y · (𝐠𝐛𝐫 Y)

thm[SBR] : FunExt
         → (Y : T ε (ιᶥ ⇾ ι))
         → SBR ⟦ Y ⟧ ⟦ 𝐬𝐛𝐫 Y ⟧
thm[SBR] fe Y = Θ-spec fe ⟦ Y ⟧ ⟦ 𝐒 Y ⟧ ⟦ 𝐠𝐛𝐫 Y ⟧ (Thm[GBR] fe Y)

\end{code}
