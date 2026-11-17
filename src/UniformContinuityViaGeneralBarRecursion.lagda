
 ===============================================================
 =                                                             =
 =  Application: Uniform Continuity via General Bar Recursion  =
 =                                                             =
 ===============================================================

    Chuangjie Xu, May 2020

    Updated in November 2026


We implement the reviewer's example of defining moduli of uniform
continuity using functionals of general bar recursion.

Update in November 2026:

- Constructed a System T term for the modulus of uniform continuity.

- Proved the correctness of the constructed modulus.

\begin{code}

{-# OPTIONS --without-K --safe #-}

module UniformContinuityViaGeneralBarRecursion where

open import Preliminaries
open import T
open import TAuxiliaries
open import GeneralBarRecursion ι public
open import UniformContinuity using (_is-a-modulus-of-uniform-continuity-of_)

\end{code}

For a fixed bound δ, evaluating `𝐌 t δ` starts the recursion at the
empty sequence. If the current sequence secures `t`, the base case
returns 0. Otherwise, the step takes one plus the maximum of the
recursive bounds for the possible next inputs i ≤ δ(length s).

\begin{code}

⟨⟩ : ℕ*
⟨⟩ = (λ n → n) , 0

EmptySeq : {Γ : Cxt} → T Γ ι*
EmptySeq = Pair · Lam ν₀ · Zero

private
 G : {Γ : Cxt} → T Γ (ι* ⇾ ι)
 G = Lam Zero
 -- G _ = 0

 H : {Γ : Cxt} → T Γ (ιᶥ ⇾ ι* ⇾ ιᶥ ⇾ ι)
 H = Lam (Lam (Lam (Suc · (Φ · ν₀ · (ν₂ · Len ν₁)))))
 -- H δ s f = 1 + Φ f (δ | s |)

𝐌 : T ε (ιᶥ ⇾ ι) → T ε (ιᶥ ⇾ ι)
𝐌 t = Lam (Lam (ν₁ · G · (H · ν₀) · EmptySeq)) · 𝐠𝐛𝐫 t
-- 𝐌 t δ = 𝐠𝐛𝐫 t G (H δ) ⟨⟩

\end{code}

The proof below assumes function extensionality through Thm[GBR].

For a prefix s, let B s be the same bar-recursive bound started at s.
If B s ≤ m, two inputs bounded by δ that extend s and agree on the next
m entries have the same value under t. We prove this by induction on m.
At a secured prefix, security gives equality immediately. Otherwise,
the maximum in the step bounds the child selected by α (len s), since
this entry is at most δ (len s), and the induction hypothesis applies.

\begin{code}

𝐌-correct : FunExt
          → (t : T ε (ιᶥ ⇾ ι))
          → ⟦ 𝐌 t ⟧ is-a-modulus-of-uniform-continuity-of ⟦ t ⟧
𝐌-correct fe t {δ} {α} {β} α≤δ _ agreement =
  lemma (B ⟨⟩) ⟨⟩ ≤refl (λ i ()) (λ i ()) agreement
 where
  S : ℕ* → ℕ
  S = ⟦ 𝐒 t ⟧
  B : ℕ* → ℕ
  B = ⟦ 𝐠𝐛𝐫 t ⟧ ⟦ G ⟧ (⟦ H ⟧ δ)
  SsY : S secures ⟦ t ⟧
  SsY = pr₁ (pr₂ (Thm[GBR] fe t))
  gbr : (s : ℕ*)
      → (s ∈ ⟦ 𝐒 t ⟧ → B s ≡ ⟦ G ⟧ s)
      × (s ∉ ⟦ 𝐒 t ⟧ → B s ≡ ⟦ H ⟧ δ s (λ n → B (s ✦ n)))
  gbr = pr₂ (pr₂ (Thm[GBR] fe t)) ⟦ G ⟧ (⟦ H ⟧ δ)

  secured : (s : ℕ*) → s ∈ S → s ∋ α → s ∋ β
          → ⟦ t ⟧ α ≡ ⟦ t ⟧ β
  secured s sS sα sβ = trans (sym (SsY s sS α sα)) (SsY s sS β sβ)

  lemma : (m : ℕ) (s : ℕ*) → B s ≤ m → s ∋ α → s ∋ β
        → drop (len s) α ≡[ m ] drop (len s) β
        → ⟦ t ⟧ α ≡ ⟦ t ⟧ β
  lemma 0 s Bs≤0 sα sβ e = case (λ sS → secured s sS sα sβ) impossible (∈-dec S)
   where
    impossible : s ∉ S → ⟦ t ⟧ α ≡ ⟦ t ⟧ β
    impossible nsS = 𝟘-elim (suc≰zero
      (transport (λ k → k ≤ 0) (pr₂ (gbr s) nsS) Bs≤0))
  lemma (suc m) s Bs≤m sα sβ (≡[suc] e es) =
    case (λ sS → secured s sS sα sβ) descend (∈-dec S)
   where
    n : ℕ
    n = α (len s)
    sn : ℕ*
    sn = s ✦ n
    next-equal : n ≡ β (len s)
    next-equal = trans (sym (drop-head (len s) α))
                       (trans e (drop-head (len s) β))
    snα : sn ∋ α
    snα = ✦-prefix s α sα refl
    snβ : sn ∋ β
    snβ = ✦-prefix s β sβ next-equal
    next-agreement : drop (len sn) α ≡[ m ] drop (len sn) β
    next-agreement = transport (λ k → drop k α ≡[ m ] drop k β)
      (len✦-suc s) (drop-agreement (len s) es)
    descend : s ∉ S → ⟦ t ⟧ α ≡ ⟦ t ⟧ β
    descend nsS = lemma m sn child-bound snα snβ next-agreement
     where
      max-bound : ⟦ Φ ⟧ (λ i → B (s ✦ i)) (δ (len s)) ≤ m
      max-bound = ≤-pred
        (transport (λ k → k ≤ suc m) (pr₂ (gbr s) nsS) Bs≤m)
      child-bound : B sn ≤ m
      child-bound = ≤trans
        (Φ-spec (α≤δ (len s)) ⋆ (λ i → B (s ✦ i))) max-bound

\end{code}
