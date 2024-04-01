---
title: Parametricity via Cohesion
author: C.B. Aberlé
---

**Abstract:** Parametricity is a key metatheoretic property of type systems, from which one is able to derive strong uniformity/modularity properties of proofs and programs within these systems. In recent years, various systems of dependent type theory have emerged with the aim of internalizing such parametric reasoning into their internal logic, employing various syntactic and semantic methods and concepts toward this end. This paper presents a first step toward the unification, simplification, and extension of these various methods for internalizing parametricity. Specifically, I argue that there is an essentially modal aspect of parametricity, which is intimately connected with the category-theoretic concept of cohesion.

On this basis, I describe a general categorical semantics for modal parametricity, develop a corresponding framework of axioms (with computational interpretations) in dependent type theory that can be used to internally represent and reason about such parametricity, and show this in practice by implementing these axioms in Agda and using them to verify parametricity properties of Agda programs. In closing, I sketch the outlines of a more general synthetic theory of parametricity, and consider potential applications in domains ranging from homotopy type theory to the analysis of linear programs.

# The past, present & future of parametricity in type theory



```agda
{-# OPTIONS --rewriting --cohesion --flat-split --without-K #-}
module parametricity-via-cohesion where
```

# Cohesion and Parametricity

# Axioms for Modal Parametricity

# Applications of Modal Parametricity

# Toward a synthetic theory of parametricity