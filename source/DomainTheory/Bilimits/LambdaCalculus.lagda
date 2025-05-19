Peter Mosses, May 2025
Incomplete

Formalization of the untyped λ-calculus and its interpretation in Scott's D∞.
See DomainTheory.Bilimits.Dinfinity for the construction of D∞.

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons

module DomainTheory.Bilimits.LambdaCalculus
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : Prop-Ext)
       where

open PropositionalTruncation pt

open import UF.Base
open import UF.Subsingletons-Properties

open import DomainTheory.Basics.Dcpo pt fe 𝓤₀
open import DomainTheory.Basics.Exponential pt fe 𝓤₀
open import DomainTheory.Basics.Miscelanea pt fe 𝓤₀
open import DomainTheory.Basics.Pointed pt fe 𝓤₀
open import DomainTheory.Bilimits.Sequential pt fe 𝓤₁ 𝓤₁
open import DomainTheory.Lifting.LiftingSet pt fe 𝓤₀ pe

open import Naturals.Order hiding (subtraction')
open import Naturals.Addition renaming (_+_ to _+'_)
open import Notation.Order

open import DomainTheory.Bilimits.Dinfinity pt fe pe hiding (ρ)

\end{code}

We have the non-trivial domain 𝓓∞ and isomorphism 𝓓∞ ≃ᵈᶜᵖᵒ (𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞).

Below, we define the function abs from continuous endofunctions on 𝓓∞ to 𝓓∞.
The function app composes the inverse of abs with extracting the underlying
function fron a continuous function.

\begin{code}

abs : ⟨ 𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞ ⟩ → ⟨ 𝓓∞ ⟩
abs = [ 𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞ , 𝓓∞  ]⟨ π-exp∞' ⟩

app : ⟨ 𝓓∞ ⟩ → ⟨ 𝓓∞ ⟩ → ⟨ 𝓓∞ ⟩
app = underlying-function 𝓓∞ 𝓓∞ ∘ [ 𝓓∞  , 𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞ ]⟨ ε-exp∞' ⟩
 
\end{code}

We define an abstract syntax for terms of the λ-calculus, parametrized by the
abstract syntax of variables with a Bool-valued equality test.

The terms of the λ-calculus include free variables, so their abstract syntax
is not well-scoped.

\begin{code}

open import MLTT.Bool using (Bool; if_then_else_)

module Terms
        (Var  : 𝓤₀ ̇)
        (_==_ : Var → Var → Bool)
       where

 data Exp : 𝓤₀ ̇ where
  var_ : Var → Exp
  ƛ_·_ : Var → Exp → Exp
  _·_  : Exp → Exp → Exp
 variable e : Exp

\end{code}

As usual in conventional Scott–Strachey style denotational semantics,
bindings are modeled by environments ρ : Env that map variables v : Var
to elements of semantic domains, and ρ [ x / v ] extends ρ to map v to x.

We define Env simply as a function type, as we do not need it to be a domain.

\begin{code}

 Env = Var → ⟨ 𝓓∞ ⟩
 variable ρ : Env

 _[_/_] : Env → ⟨ 𝓓∞ ⟩ → Var → Env
 ρ [ x / v ] = λ v′ → if v == v′ then x else ρ v′

\end{code}

The denotation ⟦ e ⟧ of a term e is an element of the type Env → ⟨ 𝓓∞ ⟩.

\begin{code}

 ⟦_⟧ : Exp → Env → ⟨ 𝓓∞ ⟩
 ƛ-is-continuous : ∀ e ρ v → is-continuous 𝓓∞ 𝓓∞ (λ x → ⟦ e ⟧ (ρ [ x / v ]))

 ⟦ var v   ⟧ ρ = ρ v
 ⟦ ƛ v · e ⟧ ρ = abs ( (λ x → ⟦ e ⟧ (ρ [ x / v ])) , ƛ-is-continuous e ρ v )
 ⟦ e₁ · e₂ ⟧ ρ = app ( ⟦ e₁ ⟧ ρ ) ( ⟦ e₂ ⟧ ρ )

 ƛ-is-continuous e ρ v = {!   !}

\end{code}

The definition of ƛ-is-continuous e ρ v appears to require lifting lubs of
directed families through the denotation of term e, and could be lengthy...
