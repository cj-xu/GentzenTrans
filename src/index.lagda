
     ---------------------------------------------------------
      A Gentzen-style monadic translation of Gödel's System T
     ---------------------------------------------------------

                   Chuangjie Xu, August 2019

                   Updated in February 2020


We introduce a syntactic translation of Gödel’s System T parametrized
by a weak notion of a monad, and prove a corresponding fundamental
theorem of logical relation. Our translation structurally corresponds
to Gentzen’s negative translation of classical logic. By instantiating
the monad and the base case of the logical relation, we reveal various
properties and structures of T-definable functionals such as
majorizability, continuity and bar recursion.


This Agda development is organized as follow:

1. Gödel's system T (extended with products)

2. A Gentzen-style monadic translation of System T

3. Fundamental theorem of logical relation

4. Examples of nuclei and their applications

5. Other monadic translations of System T


The source files are available at

    https://github.com/cj-xu/GentzenTrans

All the files are tested in the safe mode of Agda version 2.6.1.


\begin{code}

{-# OPTIONS --safe #-}

\end{code}

■ Gödel's system T

we work with the lambda-calculus version of System T.

\begin{code}

import T
import TAuxiliaries

\end{code}

■ A Gentzen-style monadic translation

We define a syntactic translation of T into itself, parametrized by a
nucleus (Jι, η, κ) which is given as module parameters.

\begin{code}

import GentzenTranslation

\end{code}

■ Fundamental theorem of logical relation

We show that every term is related to its translation w.r.t. the
logical relation extending a given relation on natural numbers.

\begin{code}

import LogicalRelation

\end{code}

■ Example I: majorizability

The translation of any term t of T majorizes t itself.

\begin{code}

import Majorizability

\end{code}

■ Example II: lifting to higher-order functionals

We lift natural numbers to functions of type X → ℕ for type X of T.
This allows us to apply the usual syntactic method to prove properties
of functions of type X → ℕ.

\begin{code}

import Lifting

\end{code}

■ Example III: pointwise continuity

Given a term f : ℕᴺ → ℕ in T, we obtain a term M : ℕᴺ → ℕ which is a
modulus of continuity of f from the translation of f.

\begin{code}

import Continuity

\end{code}

■ Example IV: uniform continuity

Given a term f : ℕᴺ → ℕ in T, we obtain from the translation of f a
function M : ℕᴺ → ℕ such that, for any θ : ℕᴺ, M(θ) is a modulus of
uniform continuity of f restricted to inputs pointwise bounded by θ.

\begin{code}

import UniformContinuity

\end{code}

■ Example V: bar recursion

Given Y : ℕᴺ → ℕ in T, we obtain a general-bar-recursion functional
form the translation of Y.

\begin{code}

import BarRecursion

\end{code}

■ Other monadic translations

We implement another two monadic translations, corresponding to the
negative translations due to Kuroda and Kolmogorov.

\begin{code}

import KurodaTranslation
import KolmogorovTranslation

\end{code}
