
 =========================
 =                       =
 =  §3.4  Bar recursion  =
 =                       =
 =========================

    Chuangjie Xu, February 2020

Schwichtenberg [2] shows that the terms of Gödel's System T are closed
under the rule of Spector's bar recursion of types 0 and 1.  Oliva and
Steila [1] provide a more direct proof of Schwichtenberg's theorem via
their notion of general bar recursion whose termination condition is
given by decidable monotone predicates on finite sequences.  We present
their construction general-bar-recursion functionals [1, Def. 3.1&3.3]
as an instance of our translation, and refer to the following Agda
development for the proofs:

  https://cj-xu.github.io/agda/BRCT/BRCT.html


References

[1] P. Oliva and S. Steila.  A direct proof of Schwichtenberg's bar
    recursion closure theorem.  Accepted by The Journal of Symbolic
    Logic, 2017.

[2] H. Schwichtenberg.  On bar recursion of types 0 and 1.  The
    Journal of Symbolic Logic, vol. 44, no. 3, pp. 325–329, 1979.

\begin{code}

{-# OPTIONS --without-K --safe #-}

open import Preliminaries
open import T
open import TAuxiliaries hiding (Φ ; Φ-spec)

module BarRecursion (σ : Ty) where

\end{code}

■ A nucleus for general bar recursion

\begin{code}

Jι : Ty
Jι = (ιᶥ ⇾ ι) ⊠ (ι* ⇾ ι) ⊠ ((ι* ⇾ σ) ⇾ (ι* ⇾ (ι ⇾ σ) ⇾ σ) ⇾ ι* ⇾ σ)

private

 ⟨_,_,_⟩ : {Γ : Cxt}
         → T Γ (ιᶥ ⇾ ι)
         → T Γ (ι* ⇾ ι)
         → T Γ ((ι* ⇾ σ) ⇾ (ι* ⇾ (ι ⇾ σ) ⇾ σ) ⇾ ι* ⇾ σ)
         → T Γ Jι
 ⟨ t₀ , t₁ , t₂ ⟩ = Pair · t₀ · (Pair · t₁ · t₂)

 V : {Γ : Cxt}
   → T Γ Jι
   → T Γ (ιᶥ ⇾ ι)
 V w = Pr1 · w

 S : {Γ : Cxt}
   → T Γ Jι
   → T Γ (ι* ⇾ ι)
 S w = Pr1 · (Pr2 · w)

 B  : {Γ : Cxt}
   → T Γ Jι
   → T Γ ((ι* ⇾ σ) ⇾ (ι* ⇾ (ι ⇾ σ) ⇾ σ) ⇾ ι* ⇾ σ)
 B w = Pr2 · (Pr2 · w)

η : {Γ : Cxt} → T Γ (ι ⇾ Jι)
η = Lam ⟨ Lam ν₁ , Lam 𝟏 , Lam (Lam ν₁) ⟩
 -- λ n . ⟨ λα.n , λs.1 , λGH.G ⟩

κ : {Γ : Cxt} → T Γ ((ι ⇾ Jι) ⇾ Jι ⇾ Jι)
κ = Lam (Lam ⟨ Lam (V (ν₂ · (V ν₁ · ν₀)) · ν₀)
 -- λ g  w . ⟨ λ α . V (g    (V w    α)    α)
             , Lam (Min · (S ν₁ · ν₀) · (S (ν₂ · (V ν₁ · ^ ν₀ ^)) · ν₀))
 --          , λ s . min  ( S w   s   ,  S ( g  (V  w     s^)      s))
             , Lam (Lam (B ν₂ · Lam (B (ν₄ · (V ν₃ · ^ ν₀ ^)) · ν₂ · ν₁ · ν₀) · ν₀)) ⟩)
 --          , λ G   H . B w   (λ s . B (g   (V  w     s^))    G    H   s)    H  ⟩

--
-- Instantiate the translation by importing the following module
-- with the nucleus (Jι, η, κ)
--
open import GentzenTranslation Jι η κ public

\end{code}

■ The generic element Ω

\begin{code}

--
-- Helper function for constructing the constant bar-recursion functional Ψ
--
φ : {Γ : Cxt}
  → T Γ (ι ⇾ (ι* ⇾ σ) ⇾ (ι* ⇾ (ι ⇾ σ) ⇾ σ) ⇾ ι* ⇾ σ)
φ = Rec · Lam (Lam ν₁)
--  rec  (λ G   H . G)
        · Lam (Lam (Lam (Lam (Lam (ν₁ · ν₀ · Lam (ν₄ · ν₃ · ν₂ · (ν₁ ★ ν₀)))))))
--       (λ n   z    G    H    s . H    s   (λ x . z   G   H    (s ★ x)))
-- φ  0    G H = G
-- φ (n+1) G H = λs.H(s,λx.φ(n,G,H,s⋆x))

--
-- Bar-recursion functional for constant terminating functional λα.k
--
Ψ : {Γ : Cxt}
  → T Γ (ι ⇾ (ι* ⇾ σ) ⇾ (ι* ⇾ (ι ⇾ σ) ⇾ σ) ⇾ ι* ⇾ σ)
Ψ = Lam (Lam (Lam (Lam (If · (Minus · Len ν₀ · ν₃)
                           · (ν₂ · ν₀)
                           · (φ · (Minus · (Suc · ν₃) · Len ν₀) · ν₂ · ν₁ · ν₀)))))
-- Ψ(k,G,H,s) = G(s)              if |s|>k
-- Ψ(k,G,H,s) = φ(k+1-|s|,G,H,s)  otherwise

Α : {Γ : Cxt} → T Γ (ι ⇾ Jι)
Α = Lam ⟨ Lam (ν₀ · ν₁)
 -- λn. ⟨ λ α . α n
        , Lam (Lt · ν₁ · Len ν₀)
 --     , λ s . Lt   n    |s|
        , Ψ · ν₀ ⟩
 --     , Ψ n ⟩

Ω : {Γ : Cxt} → T Γ (Jι ⇾ Jι)
Ω = κ · Α

\end{code}

■ Bar-recursion functionals

\begin{code}

ℕ* : Set
ℕ* = ℕᴺ × ℕ

--
-- Functional of general bar recursion
--
GBF : T ε (ιᶥ ⇾ ι)
    → (ℕ* → ⟦ σ ⟧ʸ) → (ℕ* → (ℕ → ⟦ σ ⟧ʸ) → ⟦ σ ⟧ʸ) → ℕ* → ⟦ σ ⟧ʸ
GBF t = ⟦ B (t ᴶ · Ω) ⟧

private
 --
 -- Step functionals fro general bar recursion
 --
 H : {Γ : Cxt}
   → T Γ ((ιᶥ ⇾ ι)           -- termination functional
        ⇾ (ι* ⇾ σ)           -- base functional for Spector's bar recursion
        ⇾ (ι* ⇾ (ι ⇾ σ) ⇾ σ) -- step functional for Spector's bar recursion
        ⇾ ι* ⇾ (ι ⇾ σ) ⇾ σ)  -- step functional for general bar recursion
 H = Lam (Lam (Lam (Lam (Lam (If · (Minus · Len ν₁ · (ν₄ · ^ ν₁ ^))
                                 · (ν₃ · ν₁)
                                 · (ν₂ · ν₁ · ν₀))))))

 --
 -- Converting general-bar-recursion functional to Spector's one
 --
 Φ : {Γ : Cxt}
   → T Γ ((ιᶥ ⇾ ι)
        ⇾ ((ι* ⇾ σ) ⇾ (ι* ⇾ (ι ⇾ σ) ⇾ σ) ⇾ ι* ⇾ σ)  -- general bar recursion
        ⇾ ((ι* ⇾ σ) ⇾ (ι* ⇾ (ι ⇾ σ) ⇾ σ) ⇾ ι* ⇾ σ)) -- Spector's bar recursion
 Φ = Lam (Lam (Lam (Lam (ν₂ · Lam (Ψ · (ν₄ · ^ ν₀ ^) · ν₂ · ν₁ · ν₀) · (H · ν₃ · ν₁ · ν₀)))))

--
-- Functional of Spector's bar recursion
--
SBF : T ε (ιᶥ ⇾ ι)
    → (ℕ* → ⟦ σ ⟧ʸ) → (ℕ* → (ℕ → ⟦ σ ⟧ʸ) → ⟦ σ ⟧ʸ) → ℕ* → ⟦ σ ⟧ʸ
SBF t = ⟦ Φ · t · B (t ᴶ · Ω) ⟧

\end{code}
