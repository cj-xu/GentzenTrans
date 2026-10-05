===============================================
 =                                             =
 =  Application: Church-Encoded Dialogue Tree  =
 =                                             =
 ===============================================

    Chuangjie Xu 2026

This module studies Church-encoded dialogue trees in Gödel's
System T. The main goal is to extract, from a closed term of
type `(ι ⇾ ι) ⇾ ι`, a Church-encoded dialogue tree and to prove
its correctness in the sense that its evaluation agrees with
the standard set-theoretic interpretation of the original term.

The module is inspired by Escardó, da Rocha Paiva, Rahli, and
Tosun, _Internal Effectful Forcing in System T_ (FSCD 2025,
LIPIcs 337, Article 19, DOI `10.4230/LIPIcs.FSCD.2025.19`).
Their paper uses internal effectful forcing to show, among
other things, that the dialogue tree associated to a System T
term is itself definable in System T via a Church encoding of
trees.

Our construction uses a direct logical relation between the
standard interpretation of System T and its Church-encoded
dialogue-tree interpretation. This proves that the extracted
System T term computes the same type-2 functional as the
original term. We also recall inductive dialogue trees to
verify that the internal evaluator agrees with their usual
evaluation on Church encodings; the extraction theorem itself
does not depend on these inductive trees.

\begin{code}

{-# OPTIONS --without-K --safe #-}

module InternalizedDialogueTree where

open import Preliminaries
open import T

\end{code}

■ Inductively defined dialogue trees in Agda

We begin with the ordinary inductive type of dialogue trees. A
tree is either a leaf `η n`, which immediately returns `n`, or
a branching node `β g i`, which queries the oracle at `i` and
continues with the subtree selected by the answer.

\begin{code}

data D : Set where
  η : ℕ → D
  β : (ℕ → D) → ℕ → D

eval : D → ℕᴺ → ℕ
eval (η n) _ = n
eval (β g i) α = eval (g (α i)) α

\end{code}

■ Church encodings of dialogue trees in System T

We next define the corresponding Church encoding in System T.
The terms `ηᵀ` and `βᵀ` encode leaves and queries.
The operation `κᵀ` supplies Kleisli extension for the
translation, and `Ωᵀ` is the generic element used to extract
a dialogue tree.

\begin{code}

Dᵀ : Ty → Ty
Dᵀ ρ = (ι ⇾ ρ) ⇾ ((ι ⇾ ρ) ⇾ ι ⇾ ρ) ⇾ ρ

ηᵀ : {ρ : Ty} {Γ : Cxt}
   → T Γ (ι ⇾ Dᵀ ρ)
ηᵀ = Lam (Lam (Lam (ν₁ · ν₂)))

βᵀ : {ρ : Ty} {Γ : Cxt}
   → T Γ ((ι ⇾ Dᵀ ρ) ⇾ ι ⇾ Dᵀ ρ)
βᵀ = Lam (Lam (Lam (Lam (ν₀ · Lam (ν₄ · ν₀ · ν₂ · ν₁) · ν₂))))

κᵀ : {ρ : Ty} {Γ : Cxt}
   → T Γ ((ι ⇾ Dᵀ ρ) ⇾ Dᵀ ρ ⇾ Dᵀ ρ)
κᵀ = Lam (Lam (Lam (Lam (ν₂ · Lam (ν₄ · ν₀ · ν₂ · ν₁) · ν₀))))

Ωᵀ : {ρ : Ty} {Γ : Cxt}
   → T Γ (Dᵀ ρ ⇾ Dᵀ ρ)
Ωᵀ = κᵀ · (βᵀ · ηᵀ)

\end{code}

From now on we specialise the result type `ρ` to the type-2
functional type `(ι ⇾ ι) ⇾ ι`. We write `typeᵀ-2` for this
System T type, `type-2` for its Agda interpretation `ℕᴺ → ℕ`,
and `Dᵀ₂` for the resulting Church-encoded tree type.

\begin{code}

typeᵀ-2 : Ty
typeᵀ-2 = (ι ⇾ ι) ⇾ ι

type-2 : Set
type-2 = ℕᴺ → ℕ

Dᵀ₂ : Ty
Dᵀ₂ = Dᵀ typeᵀ-2

\end{code}

■ Evaluation of Church-encoded dialogue trees

To evaluate a Church-encoded dialogue tree, we instantiate it
with the same leaf and branching algebra used by the inductive
evaluator. The operation `leaf` interprets leaves, while
`branch` interprets branching by querying the oracle at the
given index and continuing with the selected branch. The terms
`leafᵀ` and `branchᵀ` are their System T counterparts, and the
following lemmas record that their denotations are exactly the
intended Agda functions.

\begin{code}

branchᵀ : {Γ : Cxt}
        → T Γ ((ι ⇾ typeᵀ-2) ⇾ ι ⇾ typeᵀ-2)
branchᵀ = Lam (Lam (Lam (ν₂ · (ν₀ · ν₁) · ν₀)))

branch : (ℕ → type-2) → ℕ → type-2
branch g i α = g (α i) α

branchᵀ-interpretation : {Γ : Cxt} {γ : ⟦ Γ ⟧ˣ}
                       → ⟦ branchᵀ ⟧ᵐ γ ≡ branch
branchᵀ-interpretation = refl

leafᵀ : {Γ : Cxt}
      → T Γ (ι ⇾ typeᵀ-2)
leafᵀ = Lam (Lam ν₁)

leaf : ℕ → type-2
leaf n α = n

leafᵀ-interpretation : {Γ : Cxt} {γ : ⟦ Γ ⟧ˣ}
                     → ⟦ leafᵀ ⟧ᵐ γ ≡ leaf
leafᵀ-interpretation = refl

evalᵀ : {Γ : Cxt}
      → T Γ (Dᵀ₂ ⇾ (ι ⇾ ι) ⇾ ι)
evalᵀ = Lam (ν₀ · leafᵀ · branchᵀ)

\end{code}

■ Representable Church values

The semantic type `⟦ Dᵀ₂ ⟧ʸ` is a higher-order function space,
so its elements need not satisfy the fold laws of genuine
dialogue trees. Accordingly, we restrict attention to those
Church values that are represented by actual inductive
dialogue trees.

To do this, we define `run`, which interprets an inductive
dialogue tree in the same leaf and branching algebra as the
Church encoding. We then say that a dialogue tree `d`
represents a Church value `t` when both give the same result
for every leaf algebra `e` and every oracle `α`.

\begin{code}

run : D → (ℕ → type-2) → type-2
run (η n) e α = e n α
run (β g i) e α = run (g (α i)) e α

_represents_ : D → ⟦ Dᵀ₂ ⟧ʸ → Set
d represents t = ∀ (e : ℕ → type-2) (α : ℕᴺ) → t e branch α ≡ run d e α

\end{code}

The first lemma shows that `run` agrees with the ordinary
evaluator when the leaf algebra is `leaf`. It follows that
`evalᵀ` evaluates a represented Church value just as the
inductive evaluator evaluates its representing tree. This
checks the encoding independently of the extraction proof.

\begin{code}

run-eval : (t : D) (α : ℕᴺ) → run t leaf α ≡ eval t α
run-eval (η n) α = refl
run-eval (β g i) α = run-eval (g (α i)) α

evalᵀ-correct : {Γ : Cxt} (γ : ⟦ Γ ⟧ˣ)
              → (d : D) (t : ⟦ Dᵀ₂ ⟧ʸ) → d represents t
              → ∀ (α : ℕᴺ) → ⟦ evalᵀ ⟧ᵐ γ t α ≡ eval d α
evalᵀ-correct _ d _ r α = trans (r leaf α) (run-eval d α)

\end{code}

■ Direct logical relation

We now instantiate the Gentzen-style translation with the
Church type `Dᵀ₂`. For a closed term `t` of type 2, its
translation applied to the generic element `Ωᵀ` gives the
Church-encoded dialogue tree `dialogue-treeᵀ t`.

The base relation `Rι` compares the result `n` of a term on
an oracle `α` with a Church value `t`. It requires `t` to
return `e n α` for every leaf algebra `e`. Quantifying over
these algebras makes the relation stable under `κᵀ` directly;
no inductive-tree witness is needed for the fundamental theorem.

\begin{code}

open import GentzenTranslation Dᵀ₂ ηᵀ κᵀ

dialogue-treeᵀ : T ε ((ι ⇾ ι) ⇾ ι) → T ε Dᵀ₂
dialogue-treeᵀ t = t ᴶ · Ωᵀ

Rι : ℕᴺ → ℕ → ⟦ Dᵀ₂ ⟧ʸ → Set
Rι α n t = (e : ℕ → type-2) → t e branch α ≡ e n α

Rη : (α : ℕᴺ)
   → {Γ : Cxt} (γ : ⟦ Γ ⟧ˣ) (n : ℕ)
   → Rι α n (⟦ ηᵀ ⟧ᵐ γ n)
Rη α γ n e = refl

Rκ : (α : ℕᴺ)
   → {Γ : Cxt} (γ : ⟦ Γ ⟧ˣ)
   → {f : ℕ → ℕ} {g : ℕ → ⟦ Dᵀ₂ ⟧ʸ}
   → (∀ i → Rι α (f i) (g i))
   → ∀ {n : ℕ} {t : ⟦ Dᵀ₂ ⟧ʸ}
   → Rι α n t
   → Rι α (f n) (⟦ κᵀ ⟧ᵐ γ g t)
Rκ α γ {f} {g} ζ {n} {t} r e =
  trans (r (λ i → g i e branch)) (ζ n e)

RΩ : (α : ℕᴺ)
   → ∀ {n t} → Rι α n t
   → Rι α (α n) (⟦ Ωᵀ ⟧ t)
RΩ α {n} {t} r e = r (λ i → branch (λ j → e j) i)

R : ℕᴺ → {ρ : Ty} → ⟦ ρ ⟧ʸ → ⟦ ⟨ ρ ⟩ᴶ ⟧ʸ → Set
R α = LR._R_
 where
  import LogicalRelation Dᵀ₂ ηᵀ κᵀ
    (Rι α) (Rη α) (Rκ α) as LR

Cor[R] : {ρ : Ty} (t : T ε ρ) (α : ℕᴺ)
       → R α ⟦ t ⟧ ⟦ t ᴶ ⟧
Cor[R] t α = LR.FTLR t ⋆
 where
  import LogicalRelation Dᵀ₂ ηᵀ κᵀ
    (Rι α) (Rη α) (Rκ α) as LR

\end{code}

■ Correctness theorem

By the fundamental theorem, `t ᴶ` preserves the logical
relation. The generic element `Ωᵀ` relates an oracle answer
to its Church-encoded query. Instantiating the base relation
with the leaf algebra `leaf` gives the evaluation equation
for the extracted dialogue-tree term. Unlike the separate
check of `evalᵀ-correct` above, this proof uses no inductive
dialogue tree or representation witness.

\begin{code}

Theorem : (t : T ε ((ι ⇾ ι) ⇾ ι))
        → (α : ℕᴺ)
        → ⟦ t ⟧ α ≡ ⟦ evalᵀ · dialogue-treeᵀ t ⟧ α
Theorem t α = sym (Cor[R] t α (λ {n} {d} → RΩ α {n} {d}) leaf)

\end{code}
