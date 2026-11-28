
 =================================
 =                               =
 =  Application: Majorizability  =
 =                               =
 =================================

    Chuangjie Xu, July 2019

    Updated in February 2020 and restructured in November 2026

We use the monadic translation to construct majorants for System T
terms. The fundamental theorem of logical relations shows that the
interpretation of each closed term is majorized by that of its
translation.

References

□ W. A. Howard.  Hereditarily majorizable functionals of finite type.
  In Metamathematical investigation of intuitionistic Arithmetic and
  Analysis, volume 344 of Lecture Notes in Mathematics, pages
  454–461. Springer, Berlin, 1973.

\begin{code}

{-# OPTIONS --without-K --safe #-}

module Applications.Majorizability where

open import Preliminaries
open import SystemT.Base
open import SystemT.Auxiliaries

\end{code}

■ A nucleus for majorizability

\begin{code}

Jι : Ty
Jι = ι

η : {Γ : Cxt} → T Γ (ι ⇾ Jι)
η = Lam ν₀
--   λn.n

--
-- κ g n  is the maximum of g(i) for all i ≤ n.
--
κ : {Γ : Cxt} → T Γ ((ι ⇾ Jι) ⇾ Jι ⇾ Jι)
κ = MaxUpTo
-- Lam (Rec · (ν₀ · Zero) · Lam (Lam (Max · ν₀ · (ν₂ · (Suc · ν₁)))))
-- i.e.
-- κ g  0      = g 0
-- κ g (suc n) = max (κ g n) (g (suc n))

κ-spec : {i j : ℕ} → i ≤ j
       → {Γ : Cxt} (γ : ⟦ Γ ⟧ˣ)
       → (g : ℕ → ℕ) → g i ≤ ⟦ κ ⟧ᵐ γ g j
κ-spec = MaxUpTo-spec

--
-- Instantiate the translation by importing the following module
-- with the nucleus (Jι, η, κ)
--
open import Framework.Gentzen.Translation Jι η κ

\end{code}

■ Howard's majorizability relation

\begin{code}

_⊲ι_ : ⟦ ι ⟧ʸ → ⟦ Jι ⟧ʸ → Set
_⊲ι_ = _≤_

⊲η : {Γ : Cxt} (γ : ⟦ Γ ⟧ˣ) (n : ⟦ ι ⟧ʸ) → n ⊲ι ⟦ η ⟧ᵐ γ n
⊲η _ n = ≤refl

⊲κ : {Γ : Cxt} (γ : ⟦ Γ ⟧ˣ) {f : ⟦ ι ⇾ ι ⟧ʸ} {g : ⟦ ι ⇾ Jι ⟧ʸ}
   → (∀ i → f i ⊲ι g i) → ∀ {n a} → n ⊲ι a → f n ⊲ι ⟦ κ ⟧ᵐ γ g a
⊲κ γ {f} {g} ζ {x} θ = ≤trans (ζ x) (κ-spec θ γ g)

open import Framework.Gentzen.LogicalRelation Jι η κ _⊲ι_
open Soundness ⊲η ⊲κ

--
-- Howard's majorizability relation extends ≤ to all types of T
--
_⊲_ : {ρ : Ty} → ⟦ ρ ⟧ʸ → ⟦ ⟨ ρ ⟩ᴶ ⟧ʸ → Set
_⊲_ = _R_
-- i.e.
-- n ⊲ι     m = n ≤ m
-- u ⊲[σ×τ] v = (pr₁ u ⊲σ pr₁ v) ∧ (pr₂ u ⊲τ pr₂ v)
-- f ⊲[σ→τ] g = ∀ x y → x ⊲σ y → f x ⊲τ g y

\end{code}

■ Corollary: Every closed T term is majorized by its translation.

\begin{code}

Cor[Maj] : {ρ : Ty} (t : T ε ρ) → ⟦ t ⟧ ⊲ ⟦ t ᴶ ⟧
Cor[Maj] t = FTLR t ⋆

\end{code}
