---
title: Parametricity via Cohesion
author: C.B. Aberlé
header-includes:
    - \usepackage{quiver}
---

**Abstract:** Parametricity is a key metatheoretic property of type systems, from which one is able to derive strong uniformity/modularity properties of proofs and programs within these systems. In recent years, various systems of dependent type theory have emerged with the aim of internalizing such parametric reasoning into their internal logic, employing various syntactic and semantic methods and concepts toward this end. This paper presents a first step toward the unification, simplification, and extension of these various methods for internalizing parametricity. Specifically, I argue that there is an essentially modal aspect of parametricity, which is intimately connected with the category-theoretic concept of cohesion.

On this basis, I describe a general categorical semantics for modal parametricity, develop a corresponding framework of axioms (with computational interpretations) in dependent type theory that can be used to internally represent and reason about such parametricity, and show this in practice by implementing these axioms in Agda and using them to verify parametricity properties of Agda programs. In closing, I sketch the outlines of a more general synthetic theory of parametricity, and consider potential applications in domains ranging from homotopy type theory to the analysis of linear programs.

# The past, present & future of parametricity in type theory

Reynolds (1983) began his seminal introduction of the concept of *parametricity* with the declaration that "type structure is a syntactic discipline for enforcing levels of abstraction." In the ensuing decades, this idea of Reynolds' has been overwhelmingly vindicated by the success of type systems in achieving modularity and abstraction in domains ranging from programming to interactive theorem proving. Yet the fate of Reynolds' particular strategy for formalizing this idea in terms of logical relations is rather more ambiguous.

Reynolds' original analysis of parametricity targeted the polymorphic $\lambda$-calculus (aka System F). Intuitively, polymorphic programs in System F cannot inspect the types over which they are defined and so must behave *essentially the same* for all types at which they are instantiated. To make this intuitive idea precise, Reynolds posed an ingenious solution in terms of logical relations, whereby every System F type is equipped with a suitable binary relation on its inhabitants, such that all terms constructible in System F must preserve the relations defined on their component types. On this basis, Reynolds was able to establish many significant properties of the abstraction afforded by System F's type structure, e.g: all closed terms of type $\forall X . X \to X$ are extensionally equivalent to the identity function.

Reynolds' results have been extended to many type systems, programming languages, etc. However, as the complexity and expressivity of these systems increases, so too does the difficulty of defining parametricity relations for their types, and proving that the inhabitants of these types respect their corresponding relations. Moreover, the abstract, mathematical patterns underlying the definitions of such relations have not always been clear. The problem -- from a certain point of view, at any rate -- is that the usual theory of parametricity relations for type systems is "analytic,"" i.e. defined in terms of the particular constructs afforded by those systems, when what would be more desirable is a "synthetic" theory that boils the requirements for parametricity down to a few axioms, such that any type theory satisfying these axioms would necessarily enjoy parametricity and the expected consequences thereof.

For this purpose, a fruitful strategy is to consider ways of *internalizing* parametricity into the internal logic of a dependent type theory. Parametricity proofs are typically conducted in the metatheory of a particular type system, but if that type system is expressive enough to encode mathematical propositions in its types -- as is the case for dependent type theory -- there exists the possibility of instead defining and proving parametricity properties within the system itself. By considering the sorts of constructs a dependent type theory must contain in order to afford such internal parametric reasoning, we may arrive at an axiomatic specification of parametricity itself, as desired.

However, such internalization of parametricity into dependent type theory poses challenges of its own, owing to the fact that internal parametricity may be applied to itself, generating a complex, higher-dimensional structure of relations on types (c.f. Bernardy \& Moulin). Various type theories for internal parametricity have thus been proposed, each posing its own solution to taming this complexity. So far, however, the majority of these type theories have targeted only specific models (usually some appropriately-chosen presheaf categories) rather than an axiomatically-defined *class* of models, and in this sense the analysis of parametricity offered by these type theories remains *analytic,* rather than *synthetic*. This in particular limits any insight into whether and how these appraoches to internal parametricity may be related to one another, generalized, or simplified.

As a first step toward the unification, simplification, and generalization of these approaches to internal parametricity, I propose an analysis of parametricity in terms of the category-theoretic concept of *cohesion*. Cohesion here refers to a particular relation between categories whereby one is equipped with an adjoint string of modalities that together make its objects behave like abstract spaces, whose points are bound together by some sort of *cohesion* that serves to constrain the structure-preserving maps that exist between these spaces. Such a notion of cohesion is suspiciously reminiscent of the informal idea behind Reynolds' formulation of parametricity outlined above, particularly if one interprets the *cohesion* that binds types together as the structure of relations that inhere between them. Moreover, by inspection of the categorical models of extant type theories for internal parametricity, along with classical models of parametricity, one finds that many if not all of these exhibit cohesion, in this sense. The main contribution of this paper is thus to show that this basic setup of cohesion is essentially *all* that is needed to recover classical parametricity results internally in dependent type theory. As both an illustration and verification of this idea, this paper is also a literate Agda document wherein the axioms for and theorems resulting from such parametricity in terms of cohesion have been fully formalized and checked for validity.

```agda
{-# OPTIONS --rewriting --cohesion --flat-split --without-K #-}
module parametricity-via-cohesion where
    
open import Agda.Primitive
open import Agda.Builtin.Sigma
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
```

# Cohesion and Parametricity

The notion of *cohesion* as an abstract characterization of when one category (specifically a topos) behaves like a category of spaces defined over the objects of another, is due primarily to Lawvere. The central concept of axiomatic cohesion is an arrangement of four adjoint functors as in the following diagram:$$
\begin{tikzcd}
	{\mathcal{E}} \\
	\\
	{\mathcal{S}}
	\arrow[""{name=0, anchor=center, inner sep=0}, "\Gamma"{description}, curve={height=-12pt}, from=1-1, to=3-1]
	\arrow[""{name=1, anchor=center, inner sep=0}, "\nabla"{description}, curve={height=30pt}, from=3-1, to=1-1]
	\arrow[""{name=2, anchor=center, inner sep=0}, "\Delta"{description}, curve={height=-12pt}, from=3-1, to=1-1]
	\arrow[""{name=3, anchor=center, inner sep=0}, "\Pi"{description}, curve={height=30pt}, from=1-1, to=3-1]
	\arrow["\dashv"{anchor=center}, draw=none, from=3, to=2]
	\arrow["\dashv"{anchor=center}, draw=none, from=2, to=0]
	\arrow["\dashv"{anchor=center}, draw=none, from=0, to=1]
\end{tikzcd}
$$ where $\mathcal{E,S}$ are both topoi, $\Delta, \nabla$ are both fully faithful, and $\Pi$ preserves finite products. Given such an arrangement, we think of the objects of $\mathcal{E}$ as *spaces* and those of $\mathcal{S}$ as *sets* (even if $\mathcal{S}$ is not the category of sets), where $\Gamma$ is the functor that sends a space to its set of points, $\Delta$ sends a set to the corresponding *discrete space*, $\nabla$ sends a set to the corresponding *codiscrete space*, and $\Pi$ sends a space to its set of connected components. These in turn induce a string of adjoint modalities on $\mathcal{E}$: $$
\smallint \dashv \flat \dashv \sharp 
$$ where $\smallint = \Delta \circ \Pi$ and $\sharp = \nabla \circ \Gamma$ are idempotent monads, $\flat = \Delta \circ \Gamma$ is an idempotent comonad, and both $\flat$ and $\sharp$ preserve finite limits.

A concrete example of cohesion comes from the category of reflexive graphs $\mathbf{RGph}$, which is cohesive over the category of sets $\mathbf{Set}$. Here, $\Gamma$ is the functor that sends a reflexive graph to its set of vertices, $\Delta$ sends a set $V$ to the "discrete" reflexive graph on $V$ whose only edges are self-loops, $\nabla$ sends $V$ to the "codiscrete" graph where there is a unique edge between any pair of vertices, and $\Pi$ sends a reflexive graph to its set of (weakly) connected components. It is worth noting, at this point, that many classical models of parametricity are based upon semantic interpretations of types as reflexive graphs, and this, I wish to argue is no accident, and the key property of reflexive graphs underlying such interpretations is precisely their cohesive structure.[^1] More generally, for any base topos $\mathcal{S}$, we may construct its corresponding topos $\mathbf{RGph}(\mathcal{S})$ of *internal reflexive graphs*, which will similarly be cohesive over $\mathcal{S}$, so we can in fact use the language of such internal reflexive graphs to derive parametricity results for *any* topos (or indeed, any $\infty$-topos, as described below).

[^1]: Similarly, the category of bicubical sets is cohesive over that of cubical sets, a fact exploited by Nuyts, Devriese & Vezzossi in the semantics for their type theory for parametric quantifiers. 

In fact, this same setup of cohesion is interpretable, *mutatis mutandis*, in the case where $\mathcal{E,S}$ are not topoi, but rather *$\infty$-topoi*, i.e. models of homotopy type theory. This allows us to use the language of homotopy type theory -- suitably extended with constructs for the above-described modalities (the $\flat$ modality in particular, which, for technical reasons, cannot be axiomatized directly in ordinary HoTT) -- to work *synthetically* with the structure of such a cohesive $\infty$-topos. For present purposes, we accomplish this by working in Agda with the `--cohesion` and `--flat-split` flags enabled, along with `--without-K`, which ensures compatibility with the treatment of propositional equality in HoTT.

I therefore begin by recalling some standard definitions from HoTT, which shall be essential in defining much of the structure to follow. Essentially all of these definitions have to do with the *identity type* former `_≡_` and its associated constructor `refl : ∀ {ℓ} {A : Set ℓ} {a : A} → a ≡ a`, as defined in the module `Agda.Builtin.Equality`:
```agda
module hott where
```
First of all, we have the operation of *transport*, which embodies the principle of *indiscernability of identicals* (i.e. if `a0 = a1` and `B a1` then `B a0`):
```agda
    transp : ∀ {ℓ κ} {A : Set ℓ} {a0 a1 : A} 
             → (B : A → Set κ) → (a0 ≡ a1) → B a1 → B a0
    transp B refl b = b
```

The notion of *contractibility* then expresses the idea that a type is essentially uniquely inhabited.
```agda
    isContr : ∀ {ℓ} (A : Set ℓ) → Set ℓ
    isContr A = Σ A (λ a → (b : A) → a ≡ b)
```
Similarly, the notion of a type being a *proposition* expresses the idea that the type essentially has *at most one* inhabitant.
```agda
    isProp : ∀ {ℓ} (A : Set ℓ) → Set ℓ
    isProp A = (a b : A) → a ≡ b
```
Finally, the notion of *equivalence* expresses the idea that a function between types has an *essentially unique* inverse. (Those familiar with HoTT may note that I use the *contractible fibres* definition of equivalence, as this shall be the most convenient to work with, for present purposes).
```agda
    isEquiv : ∀ {ℓ κ} {A : Set ℓ} {B : Set κ} 
              → (A → B) → Set (ℓ ⊔ κ)
    isEquiv {A = A} {B = B} f = 
        (b : B) → isContr (Σ A (λ a → f a ≡ b))

    mkInv : ∀ {ℓ κ} {A : Set ℓ} {B : Set κ}
            → (f : A → B) → isEquiv f → B → A
    mkInv f e b = fst (fst (e b))

open hott
```

The reader familiar with HoTT may note that, so far, we have not included anything related to the characteristic axiom of HoTT, namely Voevodsky's *univalence axiom*. In fact, this is by design, as this axiom is largely unneeded in what follows, save for an incidental lemma to prove admissibility of another axiom. I thus postulate univalence in a separate module, which will only be used in this latter proof:

```agda
module univalence where
```
To state univalence, we first define the operation that takes an identity to an equivalence between types:

```agda
    idToEquiv : ∀ {ℓ} (A B : Set ℓ)
                → A ≡ B → Σ (A → B) (λ f → isEquiv f)
    idToEquiv A B refl =
        ((λ a → a) , λ b → ((b , refl) , λ {(c , refl) → refl}))
```

The univalence axiom asserts that this map is itself an equivalence:

```agda
    postulate
        axiom : ∀ {ℓ} {A B : Set ℓ} → isEquiv (idToEquiv A B)
```

Having defined some essential structures of the language of HoTT, we may now proceed to similarly define some essential structures of the language of HoTT *with cohesive modalities*. 
```agda
module cohesion where
```
Of principal importance here is the $\flat$ modality, which (intuitively) takes a type $A$ to its corresponding *discretization* $\flat A$, wherein all cohesion between points has been eliminated. However, in order for this operation to be well-behaved, $A$ must not depend upon any variables whose types are not themselves *discrete*, in this sense. To solve this problem, the `--cohesion` flag introduces a new form of variable binding `@♭ x : X`, which metatheoretically asserts that $x$ is an element of the discretization of $X$. In this case, we say that $x$ is a *crisp* element of $X$.

With this notion in hand, we can define the $\flat$ modality as an operation on *crisp* types:

```agda
    data ♭ {@♭ ℓ : Level} (@♭ A : Set ℓ) : Set ℓ where
        con : (@♭ x : A) → ♭ A
```

As expected, the $\flat$ modality is a comonad with the following counit operation $\epsilon$:

```agda
    ε : {@♭ l : Level} {@♭ A : Set l} → ♭ A → A
    ε (con x) = x
```

A crisp type is then *discrete* precisely when this map is an equivalence:

```agda
    isDiscrete : ∀ {@♭ ℓ : Level} → (@♭ A : Set ℓ) → Set ℓ
    isDiscrete {ℓ = ℓ} A = isEquiv (ε {ℓ} {A})

open cohesion
```

Perhaps surprisingly, with these few definitions alone, we are already nearly in a position to derive parametricity theorems in Agda (and more generally, in any type theory supporting the above constructions). What more is needed is merely a way of detecting when the elements of a given type are *related,* or somehow bound together, by the cohesive structure of that type.

For this purpose, it is useful to take a geometric perspective upon cohesion, and correspondingly, parametricity. What we are after is essentially the *shape* of an abstract relation between points, and an object $I$ in our cohesive topos $\mathcal{E}$ (correspondingly, a type in our type theory) which *classifies* this shape in other objects (types) in that maps $I → A$ correspond to such abstract relations between points in $A$. For this purpose, I propose that the *shape* of an abstract relation is nothing other than a *line segment,* i.e. two distinct points which are somehow *connected*. By way of concrete example, in the topos of reflexive graphs $\mathbf{RGph}$, the role of a classifier for this shape is played by the "walking edge" graph $\bullet → \bullet$, consisting of two points and a single non-identity (directed) edge. More generally, using the language of cohesion, we can capture this notion of an abstract line segment in the following axiomatic characterization of $I$:

> $I$ is an object of $\mathcal{E}$ that is *strictly bipointed* and *connected*.

Unpacking the terms used in this characterization, we have the following:

* *Strictly bipointed* means that $I$ is equipped with a choice of two elements $i_0, i_1 : I$, such that the proposition $(i_0 = i_1) → \bot$ (i.e. $i_0 \neq i_1$) holds in the internal language of $\mathcal{E}$.
* *Connected* means that the object/type $\smallint I$ is a proposition, i.e. $I$ essentially has *at most one* connected component.



## Conservative Extensions

### Extension Types

### Graph Types

## Parametricity via Cohesion

# Toward a synthetic theory of parametricity