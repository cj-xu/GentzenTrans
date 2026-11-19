
 =======================================
 =                                     =
 =  Application: Pointwise continuity  =
 =                                     =
 =======================================

    Chuangjie Xu, July 2019

    Updated in February 2020 and restructured in November 2026

We construct moduli of continuity via the monadic translation and then
verify the correctness via the Fundamental Theorem of Logical Relation.

\begin{code}

{-# OPTIONS --without-K --safe #-}

module Applications.Continuity.PointwiseViaGentzen where

open import Preliminaries
open import SystemT.Base
open import SystemT.Auxiliaries
open import Applications.Continuity.Definitions

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

V M : (ℕᴺ → ℕ) × (ℕᴺ → ℕ) → ℕᴺ → ℕ
V = pr₁  -- value component
M = pr₂  -- modulus component

--
-- Base case of the logical relation
--
Rι : ℕᴺ → ⟦ ι ⟧ʸ → ⟦ Jι ⟧ʸ → Set
Rι α n w =  (n ≡ V w α)
         -- n is the value of w at α
          × (∀ β → α ≡[ M w α ] β → V w α ≡ V w β)
         -- M(w,α) is a modulus of continuity of V(w) at α

--
-- η preserves the logical relation
--
Rη : (α : ℕᴺ)
   → {Γ : Cxt} (γ : ⟦ Γ ⟧ˣ) (n : ⟦ ι ⟧ʸ) → Rι α n (⟦ η ⟧ᵐ γ n)
Rη α _ n = refl , (λ _ _ → refl)

--
-- κ preserves the logical relation
--
Rκ : (α : ℕᴺ)
   → {Γ : Cxt} (γ : ⟦ Γ ⟧ˣ) {f : ⟦ ι ⇾ ι ⟧ʸ} {g : ⟦ ι ⇾ Jι ⟧ʸ}
   → (∀ i → Rι α (f i) (g i)) → ∀ {n w} → Rι α n w → Rι α (f n) (⟦ κ ⟧ᵐ γ g w)
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

--
-- Ω preserves the logical relation
--
RΩ : (α : ℕᴺ)
   → ∀{n w} → Rι α n w → Rι α (α n) (⟦ Ω ⟧ w)
 -- i.e.  R α α ⟦ Ω ⟧
RΩ α {n} {w} = Rκ α ⋆ claim {n} {w}
 where
  claim : ∀ i → Rι α (α i) (⟦ Α ⟧ i)
  claim i = refl , (λ β em → ≡[]-< em ≤refl)

\end{code}

■ Theorem: Every closed term t : ℕᴺ ⇾ ℕ of T has a modulus of
           continuity given by the term M(tᴶΩ).

\begin{code}

Thm[Cont] : (t : T ε (ιᶥ ⇾ ι))
          → M ⟦ t ᴶ · Ω ⟧ is-a-modulus-of-continuity-of ⟦ t ⟧
Thm[Cont] t = MoC-is-extensional claim₀ claim₁
 where
  cor : (α : ℕᴺ) → Rι α (⟦ t ⟧ α) ⟦ t ᴶ · Ω ⟧
  cor α = LR.FTLR t ⋆ (λ {n} {w} → RΩ α {n} {w})
   where
    import Framework.Gentzen.LogicalRelation
      Jι η κ (Rι α) (Rη α) (Rκ α) as LR
  claim₀ : ∀ α → ⟦ t ⟧ α ≡ V ⟦ t ᴶ · Ω ⟧ α
  claim₀ α = pr₁ (cor α)
  claim₁ : M ⟦ t ᴶ · Ω ⟧ is-a-modulus-of-continuity-of V ⟦ t ᴶ · Ω ⟧
  claim₁ α = pr₂ (cor α)

\end{code}
