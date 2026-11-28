
 =======================================
 =                                     =
 =  Application: Pointwise continuity  =
 =                                     =
 =======================================

    Chuangjie Xu, July 2019

    Updated in February 2020 and restructured in November 2026

We use the monadic translation to extract moduli of pointwise
continuity for T-definable functions and the fundamental theorem
of logical relations to verify the extracted moduli.

\begin{code}

{-# OPTIONS --without-K --safe #-}

module Applications.Continuity.PointwiseViaGentzen where

open import Preliminaries
open import SystemT.Base
open import SystemT.Auxiliaries
open import Applications.Continuity.Definitions
import Framework.Gentzen.LogicalRelation as GentzenLR

\end{code}

■ A nucleus for moduli of continuity

\begin{code}

Jι : Ty
Jι = (ιᶥ ⇾ ι) ⊠ (ιᶥ ⇾ ι)

-- η(n) := ⟨ λα.n , λα.0 ⟩
η : {Γ : Cxt} → T Γ (ι ⇾ Jι)
η = Lam (Pair · Lam ν₁ · Lam Zero)
--  λ n .      ⟨ λα.n  ,  λα.0 ⟩

-- κ(g,w) := ⟨ λα.V(g(V(w,α)),α) , λα.max(M(g(V(w,α)),α),M(w,α)) ⟩
κ : {Γ : Cxt} → T Γ ((ι ⇾ Jι) ⇾ Jι ⇾ Jι)
κ = Lam (Lam (Pair · Lam (Pr1 · (ν₂ · (Pr1 · ν₁ · ν₀)) · ν₀)
--  λ g   w .  ⟨     λ α . V    (g    ( V    w    α))   α
                   · Lam (Max · (Pr2 · (ν₂ · (Pr1 · ν₁ · ν₀)) · ν₀) · (Pr2 · ν₁ · ν₀))))
--             ,     λ α . max  ( M    (g    ( V    w    α))   α   ,   M    w    α ) ⟩

--
-- Instantiate the translation by importing the following module
-- with the nucleus (Jι, η, κ)
--
open import Framework.Gentzen.Translation Jι η κ

\end{code}

■ The generic element Ω

\begin{code}

-- Α(n) := ⟨ λα.αn , λα.n+1 ⟩
Α : {Γ : Cxt} → T Γ (ι ⇾ Jι)
Α = Lam (Pair · Lam (ν₀ · ν₁) · Lam (Suc · ν₁))
--  λ n .     ⟨ λ α . α   n   , λ α . n+1 ⟩
Ω : {Γ : Cxt} → T Γ (Jι ⇾ Jι)
Ω = κ · Α

\end{code}

■ A parametrized logical relation for continuity

\begin{code}

private
 V M : (ℕᴺ → ℕ) × (ℕᴺ → ℕ) → ℕᴺ → ℕ
 V = pr₁  -- value component
 M = pr₂  -- modulus component

Rι : ℕᴺ → ⟦ ι ⟧ʸ → ⟦ Jι ⟧ʸ → Set
Rι α n w =  (n ≡ V w α)
         -- n is the value of w at α
          × (∀ β → α ≡[ M w α ] β → V w α ≡ V w β)
         -- M(w,α) is a modulus of continuity of V(w) at α

module LR (α : ℕᴺ) = GentzenLR Jι η κ (Rι α)
open import Framework.Gentzen.Genericity Jι η κ ιᶥ Rι

Rη : (α : ℕᴺ) → LR.η-compatible α
Rη α _ n = refl , (λ _ _ → refl)

Rκ : (α : ℕᴺ) → LR.κ-compatible α
Rκ α γ {f} {g} ζ {n} {w} (e , prf) = trans e₀ e₁ , goal
 where
  e₀ : f n ≡ V (g n) α
  e₀ = pr₁ (ζ n)
  e₁ : V (g n) α ≡ V (g (V w α)) α
  e₁ = ap (λ x → V (g x) α) e
  m : ℕ
  m = M (⟦ κ ⟧ᵐ γ g w) α
  goal : ∀ β → α ≡[ m ] β → V (g (V w α)) α ≡ V (g (V w β)) β
  goal β em = trans claim₀ claim₂
   where
    m₀ m₁ : ℕ
    m₀ = M (g (V w α)) α
    m₁ = M w α
    em₀ : α ≡[ m₀ ] β
    em₀ = ≡[≤] em (Max-spec₀ m₀ m₁)
    em₁ : α ≡[ m₁ ] β
    em₁ = ≡[≤] em (Max-spec₁ m₀ m₁)
    claim₀ : V (g (V w α)) α ≡ V (g (V w α)) β
    claim₀ = pr₂ (ζ (V w α)) β em₀
    claim₁ : V w α ≡ V w β
    claim₁ = prf β em₁
    claim₂ : V (g (V w α)) β ≡ V (g (V w β)) β
    claim₂ = ap (λ x → V (g x) β) claim₁

RΩ : {Γ : Cxt} → is-generic (Ω {Γ})
RΩ _ α {n} {w} = Rκ α ⋆ claim {n} {w}
 where
  claim : ∀ i → Rι α (α i) (⟦ Α ⟧ i)
  claim i = refl , (λ β em → ≡[]-< em ≤refl)

\end{code}

■ Theorem: Every closed term t : ιᶥ ⇾ ι of T has a modulus of
           continuity given by the term Pr2(tᴶΩ).

\begin{code}

𝐌 : T ε (ιᶥ ⇾ ι) → T ε (ιᶥ ⇾ ι)
𝐌 t = Pr2 · (t ᴶ · Ω)

pointwise-modulus-correct
 : (t : T ε (ιᶥ ⇾ ι))
 → ⟦ 𝐌 t ⟧ is-a-modulus-of-pointwise-continuity-of ⟦ t ⟧
pointwise-modulus-correct t = MoC-is-extensional claim₀ claim₁
 where
  cor : (α : ℕᴺ) → Rι α (⟦ t ⟧ α) ⟦ t ᴶ · Ω ⟧
  cor α = FTLR t ⋆ (λ {n} {w} → RΩ ⋆ α {n} {w})
   where
    open LR.Soundness α (Rη α) (Rκ α) using (FTLR)
  claim₀ : ∀ α → ⟦ t ⟧ α ≡ V ⟦ t ᴶ · Ω ⟧ α
  claim₀ α = pr₁ (cor α)
  claim₁ : M ⟦ t ᴶ · Ω ⟧ is-a-modulus-of-pointwise-continuity-of V ⟦ t ᴶ · Ω ⟧
  claim₁ α = pr₂ (cor α)

\end{code}
