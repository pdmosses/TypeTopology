---
title:          Thesis Index
author:         Ayberk Tosun
date-started:   2024-09-19
---

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.Base
open import UF.FunExt
open import UF.PropTrunc
open import UF.Sets
open import UF.Size
open import UF.Subsingletons
open import UF.SubtypeClassifier

module Locales.ThesisIndex
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : Prop-Ext)
       where

open import Locales.ContinuousMap.FrameHomomorphism-Definition pt fe
open import Locales.Frame pt fe
open import Locales.InitialFrame pt fe
open import Locales.Nucleus pt fe
open import Locales.Sierpinski
open import UF.Logic
open import Locales.Compactness.Definition pt fe
open import Locales.Compactness.Properties pt fe pe
open import Locales.Sierpinski.UniversalProperty
open import OrderedTypes.SupLattice pt fe hiding (⟨_⟩)

open AllCombinators pt fe
open Locale

\end{code}

\section{Chapter 2}

\begin{code}

Definition-2·5·16·a : (𝓤 : Universe) → 𝓤 ⁺  ̇
Definition-2·5·16·a = propext

Definition-2·5·16·b : 𝓤ω
Definition-2·5·16·b = Prop-Ext

Definition-2·6·1 : {!!}
Definition-2·6·1 = {!!}

Definition-2·6·2 : {!!}
Definition-2·6·2 = {!!}

Example-2·6·3 : {!!}
Example-2·6·3 = {!!}

Definition-2·6·4 : {!!}
Definition-2·6·4 = {!!}

Example-2·6·5 : {!!}
Example-2·6·5 = {!!}

Lemma-2·6·6 : {!!}
Lemma-2·6·6 = {!!}

Definition-2·6·7 : {!!}
Definition-2·6·7 = {!!}

Lemma-2·6·8 : {!!}
Lemma-2·6·8 = {!!}

Theorem-2·6·9 : {!!}
Theorem-2·6·9 = {!!}

\end{code}

\section{Definition of the notion of frame}

\begin{code}

Definition-3·1·1 : (𝓤 𝓥 𝓦 : Universe) → (𝓤 ⊔ 𝓥 ⊔ 𝓦) ⁺  ̇
Definition-3·1·1 = Frame

Lemma-3·1·2 : (X : 𝓤  ̇ )
            → (_≤_ : X → X → Ω 𝓥)
            → is-partial-order X _≤_
            → is-set X
Lemma-3·1·2 {𝓤} {𝓥} X _≤_ ϑ = carrier-of-[ P ]-is-set
 where
  P : Poset 𝓤 𝓥
  P = X , _≤_ , ϑ

Lemma-3·1·3 : {!!}
Lemma-3·1·3 = {!!}

\end{code}

\subsection{Local smallness of frames}

\subsection{Primer on predicative lattice theory}

\begin{code}

Definition-3·1·5 : {!!}
Definition-3·1·5 = {!!}

Definition-3·1·8 : {!!}
Definition-3·1·8 = {!!}

\end{code}

\subsection{Categories of frames and locales}

Given frames `K` and `L`, the type of frame homomorphisms from `K` into `L` is
denoted `K ─f→ L`.

\begin{code}

Definition-3·1·13 : Frame 𝓤 𝓥 𝓦 → Frame 𝓤' 𝓥' 𝓦 → 𝓤 ⊔ 𝓦 ⁺ ⊔ 𝓤' ⊔ 𝓥'  ̇
Definition-3·1·13 = FrameHomomorphisms._─f→_

\end{code}

\section{Basic examples of locales}

\begin{code}

Example-3·1·14 : (pe : Prop-Ext) (𝓤 : Universe) → Locale (𝓤 ⁺) 𝓤 𝓤
Example-3·1·14 pe _ = 𝟏Loc pe

Lemma-3·1·15 : {!!}
Lemma-3·1·15 = {!!}

Lemma-3·1·16 : _
Lemma-3·1·16 = 𝟎-𝔽𝕣𝕞-initial

Example-3·1·18 : _
Example-3·1·18 = {!!}

Example-3·1·21 : _
Example-3·1·21 = 𝕊

Proposition-3·1·22 : _
Proposition-3·1·22 = universal-property-of-sierpinski

\end{code}

\section{Sublocales}

Definition of the notion of nucleus:

\begin{code}

Definition-3·2·1 : _
Definition-3·2·1 = Nucleus

\end{code}

The closed nucleus:

\begin{code}

Example-3·2·2 : _
Example-3·2·2 = closed-nucleus

Lemma-3·2·7 : _
Lemma-3·2·7 = nuclei-are-monotone

Lemma-3·3·1 : _
Lemma-3·3·1 =
 characterization-of-compactness₂.directed-families-have-upper-bounds-of-Kuratowski-finite-subsets

\end{code}

The conjuction is not formulated explicitly anywhere, so we do it here.

\begin{code}

open characterization-of-compactness₁
open characterization-of-compactness₂
open characterization-of-compactness₃

Lemma-3·3·2 : (X : Locale (𝓤 ⁺) 𝓤 𝓤) (U : ⟨ 𝒪 X ⟩)
            → ((is-compact-open' X U ⇔ is-compact-open'' X U)
               ∧
               (is-compact-open'' X U ⇔ is-compact-open X U)
               ∧
               (is-compact-open X U ⇔ is-compact-open' X U)) holds
Lemma-3·3·2 X U = P , Q , R
 where
  P : (is-compact-open' X U ⇔ is-compact-open'' X U) holds
  P = compact-open'-implies-compact-open'' X U ,
      compact-open''-implies-compact-open' X U

  R : (is-compact-open X U ⇔ is-compact-open' X U) holds
  R = compact-open-implies-compact-open' X U
    , compact-open'-implies-compact-open X U

  Q : (is-compact-open'' X U ⇔ is-compact-open X U) holds
  Q = pr₂ R ∘ pr₂ P , pr₁ P ∘ pr₁ R

Definition-3·3·3 : _
Definition-3·3·3 = is-compact-open

Example-3·3·4 : {!!}
Example-3·3·4 = {!!}

Lemma-3·3·7 : {!!}
Lemma-3·3·7 = {!!}

Definition-3·3·8 : {!!}
Definition-3·3·8 = {!!}

Lemma-3·3·10 : {!!}
Lemma-3·3·10 = {!!}

Lemma-3·3·11 : {!!}
Lemma-3·3·11 = {!!}

Definition-3·4·1 : {!!}
Definition-3·4·1 = {!!}

Lemma-3·4·2 : {!!}
Lemma-3·4·2 = {!!}

Example-3·4·3 : {!!}
Example-3·4·3 = {!!}

Lemma-3·4·4 : {!!}
Lemma-3·4·4 = {!!}

Definition-3·4·5 : {!!}
Definition-3·4·5 = {!!}

Example-3·4·6 : {!!}
Example-3·4·6 = {!!}

Lemma-3·4·8 : {!!}
Lemma-3·4·8 = {!!}

Corollary-3·4·9 : {!!}
Corollary-3·4·9 = {!!}

Lemma-3·5·4 : {!!}
Lemma-3·5·4 = {!!}

Definition-3·5·8 : {!!}
Definition-3·5·8 = {!!}

Lemma-3·5·9 : {!!}
Lemma-3·5·9 = {!!}

Example-3·5·10 : {!!}
Example-3·5·10 = {!!}

Definition-3·5·12 : {!!}
Definition-3·5·12 = {!!}

Lemma-3·5·13 : {!!}
Lemma-3·5·13 = {!!}

Lemma-3·5·14 : {!!}
Lemma-3·5·14 = {!!}

Definition-3·6·1 : {!!}
Definition-3·6·1 = {!!}

\end{code}

\section{Compactness and the way-below relation}

\subsection{Compact opens}

\subsection{The way-below relation}

\section{Clopens and the well-inside relation}

\subsection{Clopens}

\subsection{The well-inside relation}

\section{Bases}

\subsection{Intensional vs. extensional bases}

\subsection{Weak vs. strong bases}

\subsection{Directification of bases}

\subsection{Examples}

\section{Important classes of locales}

\section{Adjoint Functor Theorem for frames}

\subsection{Construction of Heyting implications}
