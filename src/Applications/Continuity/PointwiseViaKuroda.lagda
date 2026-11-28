
 ==================================================================
 =                                                                =
 =  Application: Pointwise continuity via the Kuroda Translation  =
 =                                                                =
 ==================================================================

    Chuangjie Xu, September 2022

    Updated in October 2026 and restructured in November 2026

This module instantiates the Kuroda-style monadic translation with a
nucleus for pointwise continuity.


Updates in October 2026:

- Verified the extracted moduli using the fundamental theorem of
  logical relations.

\begin{code}

{-# OPTIONS --without-K --safe #-}

module Applications.Continuity.PointwiseViaKuroda where

open import Preliminaries
open import SystemT.Base
open import SystemT.Auxiliaries
open import Applications.Continuity.Definitions

\end{code}

■ Pointwise-continuity nucleus for Kuroda translation

A computation carries both a value and a modulus on the input sequence
needed to determine that value. The operation η returns its value with
the incoming modulus. The operation κ takes the maximum of the incoming
modulus and the moduli returned by the two computations.

\begin{code}

J : Ty → Ty
J σ = ι ⇾ ιᶥ ⇾ σ ⊠ ι

η : {Γ : Cxt} {σ : Ty} → T Γ (σ ⇾ J σ)
η = Lam (Lam (Lam (Pair · ν₂ · ν₁)))

κ : {Γ : Cxt} {σ τ : Ty} → T Γ ((σ ⇾ J τ) ⇾ J σ ⇾ J τ)
κ = Lam (Lam (Lam (Lam (Pair · (Pr1 · (ν₃ · (Pr1 · (ν₂ · ν₁ · ν₀)) · ν₁ · ν₀))
                             · (Max · (Max · (Pr2 · (ν₃ · (Pr1 · (ν₂ · ν₁ · ν₀)) · ν₁ · ν₀))
                                           · (Pr2 · (ν₂ · ν₁ · ν₀)))
                                    · ν₁)))))

open import Framework.Kuroda J η κ

\end{code}

■ Generic element

A query at index i raises the incoming modulus n to max (suc i) n.

\begin{code}

q : {Γ : Cxt} → T Γ (ι ⇾ J ι)
q = Lam (Lam (Lam (Pair · (ν₀ · ν₂) · (Max · (Suc · ν₂) · ν₁))))

Ω : {Γ : Cxt} → T Γ (J (ι ⇾ J ι))
Ω = η · q

\end{code}

■ Logical relations for pointwise continuity

We define `V` and `C` together because `C` uses `V` to compare
the returned value.  The maps `V→K` and `K→V` let us pass between
this local relation and the one used by the framework.

\begin{code}

module At (α : ℕᴺ) (n : ℕ) where

 mutual
  V : (ρ : Ty) → ⟦ ρ ⟧ʸ → ⟦ ⟨ ρ ⟩ ⟧ʸ → Set
  V ι x a = x ≡ a
  V (σ ⊠ τ) x a = V σ (pr₁ x) (pr₁ a) × V τ (pr₂ x) (pr₂ a)
  V (σ ⇾ τ) f g = ∀ {x a} → V σ x a → C τ (f x) (g a)

  C : (ρ : Ty) → ⟦ ρ ⟧ʸ → ⟦ J ⟨ ρ ⟩ ⟧ʸ → Set
  C ρ x w = V ρ x (pr₁ (w n α))
           × (n ≤ pr₂ (w n α))
           × (∀ β → α ≡[ pr₂ (w n α) ] β
                    → pr₁ (w n β) ≡ pr₁ (w n α))

 module K = LogicalRelation C

 mutual
  V→K : (ρ : Ty) → ∀ {x a} → V ρ x a → K.V ρ x a
  V→K ι e = e
  V→K (σ ⊠ τ) (p , q) = V→K σ p , V→K τ q
  V→K (σ ⇾ τ) φ θ = φ (K→V σ θ)

  K→V : (ρ : Ty) → ∀ {x a} → K.V ρ x a → V ρ x a
  K→V ι e = e
  K→V (σ ⊠ τ) (p , q) = K→V σ p , K→V τ q
  K→V (σ ⇾ τ) φ θ = φ (V→K σ θ)

 η-compatible : K.η-compatible
 η-compatible {ρ = ρ} _ θ = K→V ρ θ , ≤refl , λ β _ → refl

 κ-compatible : K.κ-compatible
 κ-compatible {σ = σ} {τ = τ} γ {f = f} {g = g}
              ζ {x = x} {w = w} (θ , _ , stablew) =
   pr₁ p , Max-spec₁ (max k m) n , stable
  where
   a : ⟦ ⟨ σ ⟩ ⟧ʸ
   a = pr₁ (w n α)
   m k : ℕ
   m = pr₂ (w n α)
   k = pr₂ (g a n α)
   p : C τ (f x) (g a)
   p = ζ (V→K σ θ)
   stable : ∀ β → α ≡[ max (max k m) n ] β
          → pr₁ (g (pr₁ (w n β)) n β) ≡ pr₁ (g a n α)
   stable β em = trans e₀ e₁
    where
     em-w : α ≡[ m ] β
     em-w = ≡[≤] em (≤trans (Max-spec₁ k m) (Max-spec₀ (max k m) n))
     em-g : α ≡[ k ] β
     em-g = ≡[≤] em (≤trans (Max-spec₀ k m) (Max-spec₀ (max k m) n))
     e₀ : pr₁ (g (pr₁ (w n β)) n β) ≡ pr₁ (g a n β)
     e₀ = ap (λ v → pr₁ (g v n β)) (stablew β em-w)
     e₁ : pr₁ (g a n β) ≡ pr₁ (g a n α)
     e₁ = pr₂ (pr₂ p) β em-g

 q-related : V (ι ⇾ ι) α ⟦ q ⟧
 q-related {x = i} refl
   = refl
   , Max-spec₁ (suc i) n
   , λ β em → sym (≡[]-< em (Max-spec₀ (suc i) n))

 Ω-related : C (ι ⇾ ι) α ⟦ Ω ⟧
 Ω-related = η-compatible ⋆
    {a = ⟦ q ⟧} (V→K (ι ⇾ ι) {x = α} {a = ⟦ q ⟧} q-related)

 module S = K.Soundness η-compatible κ-compatible

 fΩ-related : (f : T ε (ιᶥ ⇾ ι))
            → C ι (⟦ f ⟧ α) ⟦ f ᴷ ● Ω ⟧
 fΩ-related f = S.C[●] {σ = ι ⇾ ι} {τ = ι} {γ = ⋆}
     {f = ⟦ f ⟧} {F = ⟦ f ᴷ ⟧} {x = α} {a = ⟦ Ω ⟧}
     (S.FTLR f ⋆) Ω-related

\end{code}

■ Moduli of continuity

\begin{code}

𝐌 : T ε (ιᶥ ⇾ ι) → T ε (ιᶥ ⇾ ι)
𝐌 f = Pr2 ○ (f ᴷ ● Ω · Zero)

pointwise-modulus-correct
 : (f : T ε (ιᶥ ⇾ ι))
 → ⟦ 𝐌 f ⟧ is-a-modulus-of-pointwise-continuity-of ⟦ f ⟧
pointwise-modulus-correct f α β em =
  let (eqα , _ , stable) = At.fΩ-related α 0 f
      (eqβ , _ , _) = At.fΩ-related β 0 f
  in trans eqα (trans (sym (stable β em)) (sym eqβ))

\end{code}
