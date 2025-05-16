Peter Mosses, 16 May 2025
Incomplete initial draft

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

We have the non-trivial domain 𝓓∞ ≃ᵈᶜᵖᵒ (𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞)

We start by defining an abstract syntax for terms of the λ-calculus,
parametrized by the abstract syntax of variables with boolean equality.

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

Environments ρ : Env map variables v : Var to elements of ⟨ 𝓓∞ ⟩.

The environment ρ [ x / v ] maps v to x, and otherwise maps variables as ρ.

\begin{code}

 Env = Var → ⟨ 𝓓∞ ⟩
 variable ρ : Env

 _[_/_] : Env → ⟨ 𝓓∞ ⟩ → Var → Env
 ρ [ d / v ] = λ v′ → if v == v′ then d else ρ v′

\end{code}

The denotation ⟦ e ⟧ of a term e is a function of an environment ρ : Env.

In the absence of explicit fixed points, continuity of denotations is
irrelevant.  For simplicity, we take Env → ⟨ 𝓓∞ ⟩ as the type of denotations.

\begin{code}

 ⟦_⟧ : Exp → Env → ⟨ 𝓓∞ ⟩
 ⟦ var v   ⟧ ρ =
  ρ v
 ⟦ ƛ v · e ⟧ ρ =
  [ 𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞ , 𝓓∞  ]⟨ π-exp∞' ⟩
   ( (λ x → ⟦ e ⟧ (ρ [ x / v ])) , {!   !} )
 ⟦ e₁ · e₂ ⟧ ρ =
  [ 𝓓∞ , 𝓓∞ ]⟨
   [ 𝓓∞  , 𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞ ]⟨ ε-exp∞' ⟩ ( ⟦ e₁ ⟧ ρ )
  ⟩ ( ⟦ e₂ ⟧ ρ )

\end{code}
