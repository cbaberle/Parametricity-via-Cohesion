---
title: Parametricity via Cohesion
author: C.B. Aberlé
classoption: 12pt
geometry:
    - top=1in
    - bottom=1in
    - left=1in
    - right=1in
header-includes:
    - \usepackage{quiver}
    - \usepackage[utf8]{inputenc}
    - \usepackage{newunicodechar}
    - \newunicodechar{λ}{\ensuremath{\mathnormal\lambda}}
    - \newunicodechar{∀}{\ensuremath{\mathnormal\forall}}
    - \newunicodechar{≡}{\ensuremath{\mathnormal\equiv}}
    - \newunicodechar{ℓ}{\ensuremath{\mathnormal\ell}}
    - \newunicodechar{κ}{\ensuremath{\mathnormal\kappa}}
    - \newunicodechar{Σ}{\ensuremath{\mathnormal\Sigma}}
    - \newunicodechar{⊔}{\ensuremath{\mathnormal\sqcup}}
    - \newunicodechar{♭}{\ensuremath{\mathnormal\flat}}
    - \newunicodechar{ε}{\ensuremath{\mathnormal\epsilon}}
    - \newunicodechar{₀}{\ensuremath{\mathnormal{_0}}}
    - \newunicodechar{⊥}{\ensuremath{\mathnormal\bot}}
    - \newunicodechar{⊤}{\ensuremath{\mathnormal\top}}
    - \newunicodechar{α}{\ensuremath{\mathnormal\alpha}}
    - \newunicodechar{β}{\ensuremath{\mathnormal\beta}}
    - \newunicodechar{η}{\ensuremath{\mathnormal\eta}}
    - \newunicodechar{⁻}{\ensuremath{\mathnormal{^-}}}
    - \newunicodechar{¹}{\ensuremath{\mathnormal{^1}}}
    - \newunicodechar{ℕ}{\ensuremath{\mathbb{N}}}
    - \newunicodechar{ω}{\ensuremath{\mathnormal\omega}}
    - \usepackage{fourier}
    - \usepackage{cochineal}
    - \DeclareMathAlphabet{\mathcal}{OMS}{cmsy}{m}{n}
---

> **Abstract:** Parametricity is a key metatheoretic property of type systems, implying strong uniformity \& modularity properties of the structure of types within these systems. In recent years, various systems of dependent type theory have emerged with the aim of internalizing such parametric reasoning into their internal logic, employing various syntactic and semantic methods and concepts toward this end. This paper presents a first step toward the unification, simplification, and extension of these various methods for internalizing parametricity. Specifically, I argue that there is an essentially modal aspect of parametricity, which is intimately connected with the category-theoretic concept of cohesion. On this basis, I describe a general categorical semantics for modal parametricity, develop a corresponding framework of axioms (with computational interpretations) in dependent type theory that can be used to internally represent and reason about such parametricity, and show this in practice by implementing these axioms in Agda and using them to verify parametricity theorems therein. I then demonstrate the use of these axioms in deriving induction principles for higher inductive types, and in closing, I sketch the outlines of a more general synthetic theory of parametricity, with applications in domains ranging from homotopy type theory to the analysis of program modules.

# The past, present & future of parametricity

Reynolds began his seminal introduction of the concept of *parametricity* with the declaration that "type structure is a syntactic discipline for enforcing levels of abstraction." In the ensuing decades, this idea of Reynolds' has been overwhelmingly vindicated by the success of type systems in achieving modularity and abstraction in domains ranging from programming to interactive theorem proving. Yet the fate of Reynolds' particular strategy for formalizing this idea is rather more ambiguous.

Reynolds' original analysis of parametricity targeted the polymorphic $\lambda$-calculus (aka System F). Intuitively, polymorphic programs in System F cannot inspect the types over which they are defined and so must behave *essentially the same* for all types at which they are instantiated. To make this intuitive idea precise, Reynolds posed an ingenious solution in terms of logical relations, whereby every System F type is equipped with a suitable binary relation on its inhabitants, such that all terms constructible in System F must preserve the relations defined on their component types. On this basis, Reynolds was able to establish many significant properties of the abstraction afforded by System F's type structure, e.g: all closed terms of type $\forall X . X \to X$ are extensionally equivalent to the identity function.

Reynolds' results have subsequently been extended to many type systems. However, as the complexity and expressivity of these systems increases, so too does the difficulty of defining parametricity relations for their types, and proving that the inhabitants of these types respect their corresponding relations. Moreover, the abstract, mathematical patterns underlying the definitions of such relations have not always been clear. The problem essentially is that the usual theory of parametricity relations for type systems is "analytic," i.e. defined in terms of the particular constructs afforded by those systems, when what would be more desirable is a "synthetic" theory that boils the requirements for parametricity down to a few axioms.

The need for such an axiomatic specification of parametricity is made all the more apparent by recent developments in *Homotopy Type Theory* and related fields, wherein dependent type theories capable of proving parametricity theorems *internally* for their own type structures have been developed and applied by various authors to solve some major open problems in these fields. Each such type theory has posed its own solution to the problem of internalizing parametricity, and although some commonalities exist between these systems, there is as yet no one framework that subsumes them all. In particular, the majority of these type theories have targeted only specific semantic models (usually some appropriately-chosen presheaf categories) rather than an axiomatically-defined *class* of models, and in this sense the analysis of parametricity offered by these type theories remains *analytic,* rather than *synthetic*. This in particular limits any insight into whether and how these approaches to internal parametricity may be related to one another, generalized, or simplified.

As a first step toward the unification, simplification, and generalization of these approaches to internal parametricity, I propose an analysis of parametricity in terms of the category-theoretic concept of *cohesion*. Cohesion here refers to a particular relation between categories whereby one is equipped with an adjoint string of modalities that together make its objects behave like abstract spaces, whose points are bound together by some sort of *cohesion* that serves to constrain the maps that exist between these spaces. Such a notion of cohesion is reminiscent of the informal idea behind Reynolds' formulation of parametricity outlined above, particularly if one interprets the *cohesion* that binds types together as the structure of relations that inhere between them. Moreover, by inspection of the categorical models of extant type theories for internal parametricity, along with classical models of parametricity, one finds that many (if not quite all) of these exhibit cohesion, in this sense. The main contribution of this paper is thus to show that this basic setup of cohesion is essentially *all* that is needed to recover classical parametricity results internally in dependent type theory. As both an illustration and verification of this idea, this paper is also a literate Agda document wherein the axioms for and theorems resulting from such parametricity via cohesion have been fully formalized and checked for validity.

```agda
{-# OPTIONS --rewriting --cohesion --flat-split --without-K #-}
module parametricity-via-cohesion where
    
open import Agda.Primitive
open import Data.Empty
open import Agda.Builtin.Unit
open import Agda.Builtin.Bool
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
$$ where $\smallint = \Delta \circ \Pi$ and $\sharp = \nabla \circ \Gamma$ are idempotent monads, and $\flat = \Delta \circ \Gamma$ is an idempotent comonad.

A concrete example of cohesion comes from the category of reflexive graphs $\mathbf{RGph}$, which is cohesive over the category of sets $\mathbf{Set}$. Here, $\Gamma$ is the functor that sends a reflexive graph to its set of vertices, $\Delta$ sends a set $V$ to the "discrete" reflexive graph on $V$ whose only edges are self-loops, $\nabla$ sends $V$ to the "codiscrete" graph where there is a unique edge between any pair of vertices, and $\Pi$ sends a reflexive graph to its set of (weakly) connected components. It is worth noting, at this point, that many classical models of parametricity are based upon semantic interpretations of types as reflexive graphs. This, I wish to argue, is no accident, and the key property of reflexive graphs underlying such interpretations is precisely their cohesive structure. More generally, for any base topos $\mathcal{S}$, we may construct its corresponding topos $\mathbf{RGph}(\mathcal{S})$ of *internal reflexive graphs*, which will similarly be cohesive over $\mathcal{S}$, so we can in fact use the language of such internal reflexive graphs to derive parametricity results for *any* topos (or indeed, any $\infty$-topos, as described below).

In fact, this same setup of cohesion is interpretable, *mutatis mutandis*, in the case where $\mathcal{E,S}$ are not topoi, but rather *$\infty$-topoi*, i.e. models of homotopy type theory. This allows us to use the language of homotopy type theory -- suitably extended with constructs for the above-described modalities (the $\flat$ modality in particular, which, for technical reasons, cannot be axiomatized directly in ordinary HoTT) -- to work *synthetically* with the structure of such a cohesive $\infty$-topos. For present purposes, we accomplish this by working in Agda with the `--cohesion` and `--flat-split` flags enabled, along with `--without-K`, which ensures compatibility with the treatment of propositional equality in HoTT.

I therefore begin by recalling some standard definitions from HoTT, which shall be essential in defining much of the structure to follow. Essentially all of these definitions have to do with the *identity type* former `_≡_` and its associated constructor `refl : ∀ {ℓ} {A : Set ℓ} {a : A} → a ≡ a`, as defined in the module `Agda.Builtin.Equality`:
```agda
module hott where
```
First of all, we have the induction principle for the identity type, aka the `J` rule:

```agda
    J : ∀ {ℓ κ} {A : Set ℓ} {a : A}
        → (B : (b : A) → a ≡ b → Set κ)
        → {b : A} → (p : a ≡ b) → B a refl → B b p
    J B refl b = b
```
We then obtain the operation of *transport* as the recursor for the identity type:
```agda
    transp : ∀ {ℓ κ} {A : Set ℓ} {a b : A} 
             → (B : A → Set κ) → (a ≡ b) → B a → B b
    transp B p b = J (λ a _ → B a) p b
```
Additionally, both `J` and `transp` are symmetric, and so can be applied "in the opposite direction":
```agda
    J⁻¹ : ∀ {ℓ κ} {A : Set ℓ} {a : A}
          → (B : (b : A) → a ≡ b → Set κ)
          → {b : A} → (p : a ≡ b) → B b p → B a refl
    J⁻¹ B refl b = b

    transp⁻¹ : ∀ {ℓ κ} {A : Set ℓ} {a b : A} 
               → (B : A → Set κ) → (a ≡ b) → B b → B a
    transp⁻¹ B p b = J⁻¹ (λ a _ → B a) p b
```
Moreover, since all functions must preserve relations of identity, we may apply a function to both sides of an identification as follows:
```agda
    ap : ∀ {ℓ κ} {A : Set ℓ} {B : Set κ} {a b : A}
         → (f : A → B) → a ≡ b → f a ≡ f b
    ap f refl = refl
```

The notion of *contractibility* then expresses the idea that a type is essentially uniquely inhabited.
```agda
    isContr : ∀ {ℓ} (A : Set ℓ) → Set ℓ
    isContr A = Σ A (λ a → (b : A) → a ≡ b)
```
Similarly, the notion of *equivalence* expresses the idea that a function between types has an *essentially unique* inverse.[^1] 

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

[^1]: Those familiar with HoTT may note that I use the *contractible fibres* definition of equivalence, as this shall be the most convenient to work with, for present purposes.

The reader familiar with HoTT may note that, so far, we have not included anything relating to the *univalence axiom* -- arguably the characteristic axiom of HoTT. In fact, this is by design, as a goal of the current formalization is to assume only axioms that can be given straightforward computational interpretations that preserve the property that every closed term of the ambient type theory evaluates to a *canonical normal form* (canonicity), so that these axioms give a *constructive* and *computationally sound* interpretation of parametricity. While the univalence axiom *can* be given a computational interpretation compatible with canonicity, as in Cubical Type Theory, doing so is decidedly *not* a straightforward matter. Moreover, it turns out that the univalence axiom is largely unneeded in what follows, save for demonstrating admissibility of some additional axioms which admit more straightforward computational interpretations that are (conjecturally) compatible with canonicity. I thus shall have need for univalence only as a metatheoretic assumption. In this setting, univalence allows us to convert equivalences between types into *identifications* of those types, which may then be transported over accordingly.

Having defined some essential structures of the language of HoTT, we may now proceed to similarly define some essential structures of the language of HoTT *with cohesive modalities*. 
```agda
module cohesion where
```
Of principal importance here is the $\flat$ modality, which (intuitively) takes a type $A$ to its corresponding *discretization* $\flat A$, wherein all cohesion between points has been eliminated. However, in order for this operation to be well-behaved, $A$ must not depend upon any variables whose types are not themselves *discrete*, in this sense. To solve this problem, the `--cohesion` flag introduces a new form of variable binding `@♭ x : X`, which metatheoretically asserts that $x$ is an element of the discretization of $X$, such that $X$ may only depend upon variables bound with `@♭`. In this case, we say that $x$ is a *crisp* element of $X$.

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

Beyond such notions of *discreteness*, etc., what more is required the sake of parametricity is some way of detecting when the elements of a given type are *related,* or somehow bound together, by the cohesive structure of that type.

For this purpose, it is useful to take a geometric perspective upon cohesion, and correspondingly, parametricity. What we are after is essentially the *shape* of an abstract relation between points, and an object $I$ in our cohesive topos $\mathcal{E}$ (correspondingly, a type in our type theory) which *classifies* this shape in other objects (types) in that maps $I \to A$ correspond to such abstract relations between points in $A$. In this case, the *shape* of an abstract relation is may be considered as a *path*, i.e. two distinct points which are somehow *connected*. By way of concrete example, in the topos of reflexive graphs $\mathbf{RGph}$, the role of a classifier for this shape is played by the "walking edge" graph $\bullet \to \bullet$, consisting of two points and a single non-identity (directed) edge. More generally, using the language of cohesion, we can capture this notion of an abstract line segment in the following axiomatic characterization of $I$:

> $I$ is an object of $\mathcal{E}$ that is *strictly bipointed* and *weakly connected*.

Unpacking the terms used in this characterization, we have the following:

* *Strictly bipointed* means that $I$ is equipped with a choice of two elements $i_0, i_1 : I$, such that the proposition $(i_0 = i_1) \to \bot$ (i.e. $i_0 \neq i_1$) holds in the internal language of $\mathcal{E}$.
* *Weakly connected* means that the unit map $\eta : I \to \smallint I$ is essentially constant, in that it factors through a contractible object/type. Intuitively, this says that the image of $I$ in $\smallint I$ essentially consists of a single connected component.

Note that the above-given example of the walking edge graph straightforwardly satisfies both of these requirements, as it consists of two distinct vertices belonging to a single (weakly) connected component. I also note in passing that, If the assumption of weak connectedness is strengthened to *strong connectedness* -- i.e. the object/type $\smallint I$ is itself contractible -- then the existence of such an object $I$ as above is equivalent to Lawvere's axiom of *sufficient cohesion.* We might therefore refer to the conjunction of the above conditions as an axiom of *weak sufficient cohesion* for the ambient $\infty$-topos $\mathcal{E}$.

We can begin to formalize such *weak sufficient cohesion* in Agda by postulating a type $I$ with two given elements $i_0,i_1$:

```agda
postulate
    I : Set₀
    i0 i1 : I
```

We could also, in principle, directly postulate strict bipointedness of $I$, as an axiom of the form `i0 ≡ i1 → ⊥`. However, this is in fact unnecessary, as this axiom will instead follow from an equivalent formulation introduced in a following subsection.

On the other hand, we do not yet have the capability to postulate the axiom of weak connectedness as written above, since we have not yet formalized the $\smallint$ modality. We could do so, but again, it is in fact better for present purposes to rephrase this axiom in an equivalent form involving only the $\flat$ modality, which can be done as follows:

> A type $A$ is connected if and only if, for every *discrete* type $B$, any function $A \to B$ is essentially constant, in the sense of factoring through a contractible type.

To see that this equivalence holds: in one direction, assume that $A$ is weakly connected. Then for any map $f : A \to B$, by the adjunction $\smallint \dashv \flat$ and discreteness of $B$, there exist maps $f_\flat : A \to \flat B$ and $f^\smallint : \smallint A \to B$, such that following diagram commutes: $$
\begin{tikzcd}
	{A} & {\smallint A} \\
	{\flat B} & B
	\arrow["{f_\flat}"{description}, from=1-1, to=2-1]
	\arrow["{f^\smallint}"{description}, from=1-2, to=2-2]
	\arrow["{\epsilon}"{description}, from=2-1, to=2-2]
	\arrow["{\eta}"{description}, from=1-1, to=1-2]
	\arrow["f"{description}, from=1-1, to=2-2]
\end{tikzcd}
$$ Then since by assumption $\eta$ factors through a contractible type, so does $f$.

In the other direction, assume that every map $f : A \to B$ is essentially constant, for every discrete type $B$. Then in particular, the map $\eta : A \to \smallint A$ is essentially constant, since $\smallint A$ is discrete (as it lies in the image of the *discretization* functor $\Delta$).

Hence the property of $I$ being weakly connected can be expressed purely in terms of its relation to the *discrete types*. Specifically, if we think of maps $I \to A$ as abstract *relations* or *paths* between elements of $A$, then weak connectedness of $I$ equivalently says that *all paths between points of discrete types are constant*.

In order to conveniently express this property in Agda, it shall therefore be prudent first to introduce some additional constructs for ergonomically handling paths, analogous to the definition of path types in Cubical type theory.

## Path Types

In principle, given $a,b : A$, we could define the type of paths from $a$ to $b$ in $A$ as the type $\Sigma f : I \to A . (f ~ i_0 = a) \times (f ~ i_1 = b)$. However, experience with such a naïve formalization shows that it incurs a high number of laborious transportations along equalities that should be easy enough to infer automatically. Hence I instead follow the approach taken by cubical type theory and related systems, and give an explicit axiomatization for *path types*, with corresponding rewrite rules to apply the associated equalities automatically:

```agda
postulate
    Path : ∀ {ℓ} (A : I → Set ℓ) (a0 : A i0) (a1 : A i1) → Set ℓ
```
The introduction rule for path types corresponds to *function abstraction*
```agda
    pabs : ∀ {ℓ} {A : I → Set ℓ} 
           → (f : (i : I) → A i) → Path A (f i0) (f i1)
```
and likewise, the elimination rule corresponds to *function application*.
```agda
    papp : ∀ {ℓ} {A : I → Set ℓ} {a0 : A i0} {a1 : A i1}
           → Path A a0 a1 → (i : I) → A i
```
We may then postulate the usual $\beta$-law as an identity for this type, along with special identities for application to $i0$ and $i1$. All of these are made into rewrite rules, allowing Agda to apply them automatically, and thus obviating the need for excessive use of transport:[^2]
```agda
    pβ : ∀ {ℓ} {A : I → Set ℓ} (f : (i : I) → A i) 
           → (i : I) → papp (pabs f) i ≡ f i
    {-# REWRITE pβ #-}
    papp0 : ∀ {ℓ} {A : I → Set ℓ} {a0 : A i0} {a1 : A i1} 
            → (p : Path A a0 a1) → papp p i0 ≡ a0
    {-# REWRITE papp0 #-}
    papp1 : ∀ {ℓ} {A : I → Set ℓ} {a0 : A i0} {a1 : A i1} 
            → (p : Path A a0 a1) → papp p i1 ≡ a1
    {-# REWRITE papp1 #-}
```

[^2]: We could additionally postulate an $\eta$-law for path types, analogous to the usual $\eta$-law for function types; however, this is unnecessary for what follows, and so I omit this assumption.

With this formalization of path types in hand, we can straightforwardly formalize the equivalent formulation of weak connectedness of $I$ given above. For this purpose, we first define the map `idToPath` that takes an identification $a ≡ b$ to a path from $a$ to $b$:

```agda
idToPath : ∀ {ℓ} {A : Set ℓ} {a b : A}
           → a ≡ b → Path (λ _ → A) a b
idToPath {a = a} refl = pabs (λ _ → a)
```

A type $A$ is *path-discrete* if for all $a,b : A$ the map `idToPath` is an equivalence:
```agda
isPathDiscrete : ∀ {ℓ} (A : Set ℓ) → Set ℓ
isPathDiscrete {ℓ = ℓ} A = 
    {a b : A} → isEquiv (idToPath {ℓ} {A} {a} {b})
```

We then postulate the following axioms:

```agda
postulate
    pathConst1 : ∀ {@♭ ℓ : Level} {@♭ A : Set ℓ} {a b : A}
                   → isDiscrete A → (e : Path (λ _ → A) a b)
                   → Σ (a ≡ b) (λ p → idToPath p ≡ e)
    pathConst2 : ∀ {@♭ ℓ : Level} {@♭ A : Set ℓ} {a b : A}
                   → (dA : isDiscrete A) → (e : Path (λ _ → A) a b)
                   → (q : a ≡ b) → (r : idToPath q ≡ e)
                   → pathConst1 dA e ≡ (q , r)
```
which together imply that, if $A$ is discrete, then it is *path-discrete*:

```agda
isDisc→isPDisc : ∀ {@♭ ℓ : Level} {@♭ A : Set ℓ}
                 → isDiscrete A → isPathDiscrete A
isDisc→isPDisc dA e = 
    (pathConst1 dA e , λ (p , q) → pathConst2 dA e p q)
```

As it stands, we have not yet given a procedure for evaluating the axioms `pathConst1` and `pathConst2` when they are applied to canonical forms, which means that computation on these terms will generally get stuck and thus violate canonicity. Toward rectifying this, I prove a key identity regarding these axioms, add a further postulate asserting that this identity is equal to `refl`, and convert both of these to rewrite rules:

```agda
rwPathConst1 : ∀ {@♭ ℓ : Level} {@♭ A : Set ℓ} {a : A} → (dA : isDiscrete A) 
               → pathConst1 dA (pabs (λ _ → a)) ≡ (refl , refl)
rwPathConst1 {a = a} dA = pathConst2 dA (pabs (λ _ → a)) refl refl
{-# REWRITE rwPathConst1 #-}

postulate
    rwPathConst2 : ∀ {@♭ ℓ : Level} {@♭ A : Set ℓ} {a : A} → (dA : isDiscrete A)
                   → pathConst2 dA (pabs (λ _ → a)) refl refl ≡ refl
    {-# REWRITE rwPathConst2 #-}
```
Although a full proof of canonicity is beyond the scope of this paper, I conjecture that adding these rules suffices to preserve canonicity, and I verify a few concrete cases of this conjecture later in the paper.

So much for the (weak) connectedness of $I$; let us now turn our attention to the other property we had previously stipulated of $I$, namely its *strict bipointedness*. As mentioned previously, we could simply postulate this stipulation directly as an axiom -- however, for the purpose of proving parametricity theorems, a more prudent strategy is to instead formalize a class of $I$-indexed type families, whose computational behavior follows from this assumption (and which, in turn, implies it). Because these type families essentially correspond to the *graphs* of predicates and relations on arbitrary types, I refer to them as *graph types*.

## Graph Types

For present purposes, we need only concern ourselves with the simplest class of graph types: *unary graph types*, which, as the name would imply, correspond to graphs of unary predicates. Given a type $A$, a type family $B : A \to \mathsf{Type}$, and an element $i : I$, the *graph type* $\mathsf{Gph}^1 ~ i ~ A ~ B$ is defined to be equal to $A$ when $i$ is $i_0$, and equivalent to $\Sigma x : A . B x$ when $i$ is $i_1$. Intuitively, an element of $\mathsf{Gph}^1 ~ i ~ A ~ B$ is a dependent pair whose second element *only exists when $i$ is equal to $i_1$*. We may formalize this in Agda as follows, by postulating a rewrite rule that evaluates $\mathsf{Gph}^1 ~ i_0 ~ A ~ B$ to $A$:

```agda
postulate
    Gph1 : ∀ {ℓ} (i : I) (A : Set ℓ) (B : A → Set ℓ) → Set (ℓ)

    g1rw0 : ∀ {ℓ} (A : Set ℓ) (B : A → Set ℓ) → Gph1 i0 A B ≡ A
    {-# REWRITE g1rw0 #-}
```

We then have the following introduction rule for elements of $\mathsf{Gph}^1 ~ i ~ A ~ B$, which are pairs where the second element of the pair only exists under the assumption that $i = i_1$. When $i = i_0$ instead, the pair collapses to its first element:

```agda
    g1pair : ∀ {ℓ} {A : Set ℓ} {B : A → Set ℓ} (i : I)
             → (a : A) → (b : (i ≡ i1) → B a) → Gph1 i A B

    g1pair0 : ∀ {ℓ} {A : Set ℓ} {B : A → Set ℓ}
              → (a : A) → (b : (i0 ≡ i1) → B a)
              → g1pair {B = B} i0 a b ≡ a
    {-# REWRITE g1pair0 #-}
```

The first projection from such a pair may then be taken no matter what $i$ is, and reduces to the identity function when $i$ is $i_0$:

```agda
    g1fst : ∀ {ℓ} {A : Set ℓ} {B : A → Set ℓ} (i : I)
            → (g : Gph1 i A B) → A
    
    g1beta1 : ∀ {ℓ} {A : Set ℓ} {B : A → Set ℓ} (i : I)
              → (a : A) → (b : (i ≡ i1) → B a)
              → g1fst i (g1pair {B = B} i a b) ≡ a
    {-# REWRITE g1beta1 #-}
    
    g1fst0 : ∀ {ℓ} {A : Set ℓ} {B : A → Set ℓ}
             → (g : Gph1 i0 A B) → g1fst {B = B} i0 g ≡ g
    {-# REWRITE g1fst0 #-}
```

The second projection, meanwhile, may only be taken when $i$ is equal to $i_1$:

```agda
    g1snd : ∀ {ℓ} {A : Set ℓ} {B : A → Set ℓ}
            → (g : Gph1 i1 A B) → B (g1fst i1 g)
    
    g1beta2 : ∀ {ℓ} {A : Set ℓ} {B : A → Set ℓ}
              → (a : A) → (b : (i1 ≡ i1) → B a)
              → g1snd (g1pair {B = B} i1 a b) ≡ b refl
    {-# REWRITE g1beta2 #-}
```

It is straightforward to see that the inclusion of graph types makes strict bipointedness of the interval provable, as follows:

```agda
strBpt : (i0 ≡ i1) → ⊥
strBpt p = g1snd (transp (λ i → Gph1 i ⊤ (λ _ → ⊥)) p tt)
```

And in fact, the converse holds under the assumption of univalence. Specifically, in the presence of univalence and the assumption of strict bipointedness for $I$, the type $\mathsf{Gph}^1 ~ i ~ A ~ B$ may be regarded as a computationally convenient shorthand for the type $\Sigma x : A . (i = i_1) \to B x$, in much the same way as the type $\mathsf{Path} ~ A ~ a_0 ~ a_1$ serves as shorthand for the type $\Sigma f : (\Pi i : I . A i) . (f ~ i_0 = a_0) \times (f ~ i_1 = a_1)$. This fact is due to the following equivalence $$\begin{array}{rl} &\Sigma x : A . (i_0 = i_1) \to B x\\ \simeq & \Sigma x : A . \bot \to B x\\ \simeq & \Sigma x : A . \top \\ \simeq & A \end{array}$$ which is given by the map $\mathsf{fst} : (\Sigma x : A . (i_0 = i_1) \to B x) \to A$ and which, under univalence, becomes an identity between its domain and codomain, thereby justifying the use of this and associated identities as rewrite rules which, conjecturally, are fully compatible with canonictiy.

A few additional theorems, concerning identities between elements of graph types, are as follows, the latter of which I make into a rewrite rule for convenience:

```agda
apg1pair : ∀ {ℓ} {A : Set ℓ} {B : A → Set ℓ}
           → {a b : A} {aB : B a} {bB : B b} 
           → (p : a ≡ b) → aB ≡ transp⁻¹ B p bB 
           → (i : I) → g1pair i a (λ _ → aB) ≡ g1pair i b (λ _ → bB)
apg1pair refl refl i = refl

apg1pair0 : ∀ {ℓ} {A : Set ℓ} {B : A → Set ℓ}
            → {a b : A} {aB : B a} {bB : B b}
            → (p : a ≡ b) → (q : aB ≡ transp⁻¹ B p bB)
            → apg1pair p q i0 ≡ p
apg1pair0 refl refl = refl
{-# REWRITE apg1pair0 #-}
```

In principle, we could continue in this manner, and define graph types for relations of arities greater than 1 as well. However, unary graph types are sufficient for what follows. Having thus given appropriate axioms (and corresponding computation rules) to capture the desiderata that $I$ be strictly bipointed and weakly connected, we are now in a position to prove some classical parametricity theorems using this structure.

## Parametricity via Sufficient Cohesion

I begin this section with an old chestnut of parametricity theorems -- a proof that any *polymorphic function* of type `(X : Set) → X → X` must be equivalent to the polymorphic identity function `λ X → λ x → x`. 

```agda
PolyId : (ℓ : Level) → Set (lsuc ℓ)
PolyId ℓ = (X : Set ℓ) → X → X
```

Before proceeding with this proof, however, it will be prudent to consider the *meaning* of this theorem in the context of the cohesive type theory we have so-far developed. Specifically, I wish to ask: over which types should the type variable `X` in the type `(X : Set) → X → X` be considered as ranging in the statement of this theorem? Although it is tempting to think that the answer to this question should be "all types" (or as close to this as one can get predicatively), if one considers the relation between our cohesive setup and Reynolds' original setup of parametricity, a subtler picture emerges. A type, in our framework, corresponds not to a type in the object language of e.g. bare sets, but rather to an object of the cohesive topos used to interpret the parametric structure of this object language, e.g. the category of reflexive graphs. In this sense, we should expect the parametricity result for the type `(X : Set) → X → X` to generally hold only for those types corresponding to those in the object language, i.e. the *discrete types*. Indeed, the discrete types by construction are those which cannot distinguish elements of other types belonging to the same connected component, which intuitively corresponds to the fundamental idea of parametricity -- that functions defined over these types must behave essentially the same for related inputs.

However, we cannot state this formulation of the theorem directly, since it would require us to bind $X$ as `@♭ X : Set`, which would kill all of the cohesive structure on `Set` and pose no restriction on the functions inhabiting this type. The solution, in this case, is to restrict the range of `X` to types which are *path-discrete*, since this requirement can be stated even for `X` not crisp.

To prove the desired parametricity theorem for the type `PolyId` as above, then, we first prove a *substitution lemma* as follows:

> For any function `α : PolyIdA` and any path-discrete type `A` with `a : A` and a type family `B : A → Set`, there is a function `B a → B(α A a)`

```agda
module paramId {ℓ} (A : Set ℓ) (pdA : isPathDiscrete A) (B : A → Set ℓ) 
                   (a : A) (b : B a) (α : PolyId ℓ) where
```

The key step in the proof of this lemma is to construct a "dependent path" over the type family `Gph1 i A B : I → Set` as follows:

```agda
    lemma0 : (i : I) → Gph1 i A B
    lemma0 i = α (Gph1 i A B) (g1pair i a (λ _ → b))
```

Then taking the second projection of `lemma0` evaluated at `i1` yields an element of $B$ evaluated at the first projection of `lemma0` evaluated at `i1`:

```agda
    lemma1 : B (g1fst i1 (lemma0 i1))
    lemma1 = g1snd (lemma0 i1)
```

And we can use `lemma0` to construct a path from `α A a` to `g1fst i1 (lemma0 i1)` as follows:

```agda
    lemma2 : Path (λ _ → A) (α A a) (g1fst i1 (lemma0 i1))
    lemma2 = pabs (λ i → g1fst i (lemma0 i))
```

And then since `A` is path-discrete, this path becomes an equality along which we can transport `lemma1`:

```
    substLemma : B (α A a)
    substLemma = transp⁻¹ B (mkInv idToPath pdA lemma2) lemma1
```

From this substitution lemma, it straightforwardly follows that any element of `PolyId` must be extensionally equivalent to the polymorphic identity function when evaluated at a path-discrete type:

```agda
polyId : ∀ {ℓ} (A : Set ℓ) (pdA : isPathDiscrete A) (a : A)
         → (α : PolyId ℓ) → α A a ≡ a
polyId A pdA a α = paramId.substLemma A pdA (λ b → b ≡ a) a refl α
```

Before we congratulate ourselves for proving this theorem, however, we ought to reflect on the significance of what we have proved. For we have proved *only* that the restrictions of elements of `PolyId` to path-discrete types are equivalent to that of the polymorphic identity function. The theorem would then after all be trivial if it turned out that the only path-discrete types were (e.g.) those containing at most one element (i.e. the *mere propositions*, in the terminology of HoTT). To show that this is not the case, we make use of our assumption of *connectedness* for $I$, which we have already seen implies that every discrete type is path-discrete. To give a concrete (non-trivial) instance of this, I now show that the type of Booleans is discrete (hence path-discrete) and use this to test the canonicity conjecture on a simple example:


```agda
module BoolDiscrete where
```

Showing that `Bool` is discrete is a simple matter of pattern matching
```agda
    boolIsDisc : isDiscrete Bool
    boolIsDisc false = (con false , refl) , λ { (con false , refl) → refl}
    boolIsDisc true  = (con true  , refl) , λ { (con true , refl) → refl}
```
It follows that `Bool` is also path-discrete and so the above parametricity theorem may be applied to it.
```agda
    boolIsPDisc : isPathDiscrete Bool
    boolIsPDisc = isDisc→isPDisc boolIsDisc

    polyIdBool : (α : PolyId lzero) → (b : Bool) → α Bool b ≡ b
    polyIdBool α b = polyId Bool boolIsPDisc b α
```

We can use this to check that, in at least one specific case, the proof of `polyId` yields a canonical form (namely `refl`) when it is applied to canonical forms:

```agda
    shouldBeRefl1 : true ≡ true
    shouldBeRefl1 = polyIdBool (λ X → λ x → x) true
```

Running Agda's normalization procedure on this term shows that it does indeed evaluate to `refl`.

## Parametricity & (Higher) Inductive Types 

The foregoing proof of parametricity for the type of the polymorphic identity function remains ultimately a toy example. To demonstrate the true power of this approach to parametricity, I turn now to some more intricate examples of its use, in proving universal properties for simplified presentations of inductive types and higher inductive types.

In general, it is easy to write down what should be the *recursion* principle for an inductive type generated by some set of constructors, but harder (though feasible) to write down the corresponding *induction* principle. When one begins to consider more complex generalizations of inductive types, such as higher inductive types, inductive-inductive types, etc, these difficulties begin to multiply. What would be ideal would be a way of deriving the induction principle for an inductive type from its *recursor,* hence requiring only the latter to be specified as part of the primitive data of the inductive type. However, in most systems of ordinary dependent type theory this is generally not possible (c.f. Geuvers). In HoTT, there is one way around this issue, due to Awodey, Frey & Speight, whereby additional *naturality* constraints are imposed upon the would-be inductive type, that serve to make the corresponding induction principle derivable from the recursor. However, when one goes on to apply this technique to *higher-inductive types,* which may specify constructors not only for *elements* of a type, but also for instances of its (higher) identity types, the complexity of these naturality conditions renders them impractical to work with. The ballooning complexity of these conditions is an instance of the infamous *coherence problem* in HoTT, whereby the complexity of coherence conditions for higher-categorical structures seemingly escapes any simple inductive definition.

As an alternative, let us consider ways of using *parametricity* to derive induction principles for inductive and higher inductive types, starting with the prototypical inductive type, the natural numbers $\mathbb{N}$.

First, we define the type of the recursor for $\mathbb{N}$:

```agda
Recℕ : Setω
Recℕ = ∀ {ℓ} (A : Set ℓ) → A → (A → A) → A
```
We may then postulate the usual constructors and identities for $\mathbb{N}$[^3]
```agda
postulate
    ℕ : Set₀
    zero : ℕ
    succ : ℕ → ℕ
    recℕ : ℕ → Recℕ
    zeroβ : ∀ {ℓ} (A : Set ℓ) (a : A) (f : A → A) → recℕ zero A a f ≡ a
    {-# REWRITE zeroβ #-}
    succβ : ∀ {ℓ} (n : ℕ) (A : Set ℓ) (a : A) (f : A → A)
            → recℕ (succ n) A a f ≡ f (recℕ n A a f)
    {-# REWRITE succβ #-}
    ℕη : (n : ℕ) → recℕ n ℕ zero succ ≡ n
    {-# REWRITE ℕη #-}
```

[^3]: Note that among the identities postulated as rewrite rules for $\mathbb{N}$ is its $\eta$-law, i.e. $\mathsf{rec\mathbb{N}} ~ n ~ \mathbb{N} ~ \mathsf{zero} ~ \mathsf{succ} = n$ for all $n : \mathbb{N}$. This will be important for deriving the induction principle for $\mathbb{N}$.

From here, we may proceed essentially as in the proof of parametricity for `PolyId`, by proving an analogous *substitution lemma* for `Recℕ`, following essentially the same steps:

```agda
module paramℕ {ℓ} (α : Recℕ) (A : Set ℓ) (pdA : isPathDiscrete A) 
                  (B : A → Set ℓ) (a : A) (b : B a)
                  (f : A → A) (ff : (x : A) → B x → B (f x)) where

    lemma0 : (i : I) → Gph1 i A B
    lemma0 i = α (Gph1 i A B)
                 (g1pair i a (λ _ → b))
                 (λ g → let g' j q = transp (λ k → Gph1 k A B) q g in
                        g1pair i (f (g1fst i g))
                               (λ p → J⁻¹ (λ j q → B (f (g1fst j (g' j q)))) p
                                          (ff (g1fst i1 (g' i1 p)) 
                                              (g1snd (g' i1 p)))))

    lemma1 : B (g1fst i1 (lemma0 i1))
    lemma1 = g1snd (lemma0 i1)

    lemma2 : Path (λ _ → A) (α A a f) (g1fst i1 (lemma0 i1))
    lemma2 = pabs (λ i → g1fst i (lemma0 i))

    substLemma : B (α A a f)
    substLemma = transp⁻¹ B (mkInv idToPath pdA lemma2) lemma1
```

In order to apply this lemma to $\mathbb{N}$ itself, we must further postulate that $\mathbb{N}$ is path-discrete (in fact, one could show by induction that $ℕ$ is *discrete*, hence path-discrete by the assumption of connectedness for $I$; however, since we have not yet proven induction for $\mathbb{N}$, we must instead take this result as an additional axiom, from which induction on $\mathbb{N}$ will follow). 

```agda
postulate
    pdℕ1 : ∀ {m n : ℕ} (e : Path (λ _ → ℕ) m n) 
           → Σ (m ≡ n) (λ p → idToPath p ≡ e)
    pdℕ2 : ∀ {m n : ℕ} (e : Path (λ _ → ℕ) m n)
           → (q : m ≡ n) (r : idToPath q ≡ e)
           → pdℕ1 e ≡ (q , r)

pdℕ : isPathDiscrete ℕ
pdℕ e = (pdℕ1 e , λ (q , r) → pdℕ2 e q r)

rwPDℕ1 : (n : ℕ) → pdℕ1 (pabs (λ _ → n)) ≡ (refl , refl)
rwPDℕ1 n = pdℕ2 (pabs (λ _ → n)) refl refl
{-# REWRITE rwPDℕ1 #-}

postulate
    rwPDℕ2 : (n : ℕ) → pdℕ2 (pabs (λ _ → n)) refl refl ≡ refl
    {-# REWRITE rwPDℕ2 #-}
```

Induction for $\mathbb{N}$ then follows as a straightforward consequence of the substitution lemma:[^4]

```agda
indℕ : (P : ℕ → Set) → P zero → ((n : ℕ) → P n → P (succ n)) → (n : ℕ) → P n
indℕ P pz ps n = paramℕ.substLemma (recℕ n) ℕ pdℕ P zero pz succ ps
```

[^4]: Note that our use of the $\eta$-law for $\mathbb{N}$ as a rewrite rule is critical to the above proof, since otherwise in the last step, we would obtain not a proof of `P n`, but rather `P (recℕ n ℕ succ zero)`.

As in the case of the parametricity theorem for `PolyId`, we may test that the derived induction principle for $\mathbb{N}$ evaluates canonical forms to canonical forms. The following example tests this for the usual inductive proof that `zero` is an identity element for addition on the right:

```agda
module ℕexample where
    _plus_ : ℕ → ℕ → ℕ
    m plus n = recℕ m ℕ n succ

    zeroIdR : (n : ℕ) → n plus zero ≡ n
    zeroIdR n = indℕ (λ m → m plus zero ≡ m) refl (λ m p → ap succ p) n
    
    shouldBeRefl2 : succ (succ zero) ≡ succ (succ zero)
    shouldBeRefl2 = zeroIdR (succ (succ zero))
```

Running Agda's normalization procedure on `shouldBeRefl2` again confirms that it evaluates to `refl`.

Moving on, then, from inductive types to *higher* inductive types, we may now consider deriving the induction principle for the *circle* $S^1$, defined to be the type freely generated by a single basepoint $\mathsf{base} : S^1$, with a nontrivial identification $\mathsf{loop} : \mathsf{base} = \mathsf{base}$. The recursor for $S^1$ thus has the following type:

```agda
RecS¹ : Setω
RecS¹ = ∀ {ℓ} (A : Set ℓ) → (a : A) → a ≡ a → A
```

Then, just as before, we may postulate the corresponding constructors and $\beta\eta$-laws for $S^1$:

```agda
postulate
    S¹ : Set₀
    base : S¹
    loop : base ≡ base
    recS¹ : S¹ → RecS¹
    baseβ : ∀ {ℓ} (A : Set ℓ) (a : A) (l : a ≡ a) → recS¹ base A a l ≡ a
    {-# REWRITE baseβ #-}
    loopβ : ∀ {ℓ} (A : Set ℓ) (a : A) (l : a ≡ a)
              → ap (λ s → recS¹ s A a l) loop ≡ l
    {-# REWRITE loopβ #-}
    S¹η : (s : S¹) → recS¹ s S¹ base loop ≡ s
    {-# REWRITE S¹η #-}
```

The proof of induction for $S^1$ is then in essentials the same as the one given above for $\mathbb{N}$. We begin by proving a *substitution lemma* for `RecS¹`, following exactly the same steps as in the proof of the corresponding theorem for `Recℕ`:

```agda
module paramS¹ {ℓ} (A : Set ℓ) (pdA : isPathDiscrete A) (B : A → Set ℓ) 
                   (a : A) (b : B a) (l : a ≡ a)
                   (lB : b ≡ transp⁻¹ B l b) (α : RecS¹) where

    lemma0 : (i : I) → Gph1 i A B
    lemma0 i = α (Gph1 i A B) (g1pair i a (λ _ → b)) (apg1pair l lB i)

    lemma1 : B (g1fst i1 (lemma0 i1))
    lemma1 = g1snd (lemma0 i1)

    lemma2 : Path (λ _ → A) (α A a l) (g1fst i1 (lemma0 i1))
    lemma2 = pabs (λ i → g1fst i (lemma0 i))

    substLemma : B (α A a l)
    substLemma = transp⁻¹ B (mkInv idToPath pdA lemma2) lemma1
```

We then postulate that $S^1$ is path-discrete, as before, in order to apply this lemma to $S^1$ itself:

```agda
postulate
    pdS¹1 : ∀ {s t : S¹} (e : Path (λ _ → S¹) s t)
            → Σ (s ≡ t) (λ p → idToPath p ≡ e)
    pdS¹2 : ∀ {s t : S¹} (e : Path (λ _ → S¹) s t)
            → (q : s ≡ t) (r : idToPath q ≡ e)
            → pdS¹1 e ≡ (q , r)

pdS¹ : isPathDiscrete S¹
pdS¹ e = (pdS¹1 e , λ (q , r) → pdS¹2 e q r)

rwPDS¹1 : (s : S¹) → pdS¹1 (pabs (λ _ → s)) ≡ (refl , refl)
rwPDS¹1 s = pdS¹2 (pabs (λ _ → s)) refl refl
{-# REWRITE rwPDS¹1 #-}

postulate
    rwPDS¹2 : (s : S¹) → pdS¹2 (pabs (λ _ → s)) refl refl ≡ refl
    {-# REWRITE rwPDS¹2 #-}
```

And then the desired induction principle for $S^1$ follows straightforwardly:

```agda
indS¹ : (P : S¹ → Set) (pb : P base) → pb ≡ transp⁻¹ P loop pb → (s : S¹) → P s
indS¹ P pb pl s = paramS¹.substLemma S¹ pdS¹ P base pb loop pl (recS¹ s)
```

Although it is not in general possible to verify that this same construction is capable of deriving induction principles for *all* higher inductive types -- essentially because there is as yet no well-established definition of what higher inductive types are *in general* -- there appears to be no difficulty in extending this method of proof to all known classes of higher inductive types. Moreover, that the proof of induction for $S^1$ is essentially no more complex than that for $\mathbb{N}$ suggests that this method is capable of taming the complexity of coherences for such higher inductive types, and in this sense provides a solution to this instance of the coherence problem.

# Toward a synthetic theory of parametricity

The theory so-far developed essentially gives a synthetic framework for working in the internal language of a (weakly) *sufficiently cohesive $\infty$-topos*. This framework in turn proves capable of deriving significant parametricity results internally, with immediate applications in e.g. resolving coherence problems having to do with higher inductive types. It remains to be seen what further applications can be developed for this theory and its particular approach to parametricity. From this perspective, it is profitable to survey what other approaches there are to internalizing parametricity theorems in dependent type theory, and how they might be related to the one given in this paper.

### Cohesion & Gluing

In recent years, there has been some work related toward a synthetic theory of parametricity in terms of the topos-theoretic construction of *Artin Gluing*. This approach, outlined iniitally by Sterling in his thesis and subsequently spearheaded by Sterling and his collaborators as part of the more general programme of *Synthetic Tait Computability* (STC), works in the internal language of a topos equipped with two (mere) propositions $L$ and $R$, that are *mutually exclusive* in that $L \wedge R \to \bot$. The central idea of this approach is to synthetically reconstruct the usual account of parametricity in terms of logical relations by careful use of the *open* and *closed* modalities induced by these propositions, which play a similar role in STC to the *graph types* introduced above. Using this approach, one can e.g. prove representation independence theorems for module signatures as in Sterling & Harper.

Clearly, there is some affinity between the approach to parametricity in terms of gluing and that in terms of cohesion presented above, not least of which having to do with the fact that they both offer characteristically *modal* perspectives on parametricity. Yet there is a further sense in which these two approaches are related, which is that every sufficiently cohesive topos contains a model of Sterling's setup of STC for parametricity, as follows: given a sufficiently cohesive topos $\mathcal{E}$ over some base topos $\mathcal{S}$, for any strictly bipointed object $I \in \mathcal{E}$ with distinguished points $i_0, i_1 : I$, the *slice topos* $\mathcal{E}/I$, whose internal language corresponds to that of $\mathcal{E}$ extended with an arbitrary element $i : I$, is thereby equipped with two mutually exclusive propositions, namely $i = i_0$ and $i = i_1$. Hence all of the parametricity theorems available in STC can be recovered in the above-given framework (in particular, instances of closed modalities can be encoded as higher inductive types, which, as we have just seen, are easily added to the above framework).

On the other hand, there is no analogue in STC of the axiom of connectedness for the interval, and its consequent parametricity theorems, most notably the above-mentioned derivability of induction principles for higher inductive types. This suggests that in these latter results, which are intimately connected with the *coherence problem* of HoTT, the structure of *cohesion* and its relation to parametricity plays an essential role. Nonetheless, it remains interesting to consider how parametricity via cohesion and parametricity via gluing may yet prove to be related, and one may hope for a fruitful cross-pollination between these two theories.

### Cohesion & Coherence

As just mentioned, there appears to be an intimate link between *parametricity*, *cohesion*, and *coherence*, as demonstrated e.g. by the above-given proof of induction for $S^1$. The existence of such a link is further supported by other recent developments in HoTT and related fields. E.g. Cavallo & Harper have used their system of internal parametricity for cubical type theory to derive coherence theorems for the smash product. More recently still, Kolomatskaia & Shulman have introduced their system of *displayed* type theory, which utilizes yet another form of internal parametricity to solve the previously-open problem of representing *semi-simplicial types* in HoTT.

In outlining the above framework for parametricity in terms of cohesion, I hope to have taken a first step toward the unification of these various systems that use parametricity to tackle instances of the coherence problem. Cavallo & Harper's system is readily assimilated to this framework, as are other related systems that take a *cubical* approach to internal parametricity, such as that of Nuyts, Devriese & Vezzossi, since these all take their semantics in various topoi of bicubical sets, which all are sufficiently cohesive over corresponding topoi of cubical sets. On the other hand, Kolomatskaia & Shulman's system cannot be assimilated in quite the same way, since their system takes its semantics in the $\infty$-topos of augmented semisimplicial spaces, which is *not* cohesive over spaces. It thus remains to be seen if the above framework can be generalized so as to be inclusive of this example as well. Alternatively, one might seek to generalize or modify Kolomatskaia & Shulman's system so as to be interpretable in an $\infty$-topos that *is* cohesive over spaces, e.g. the $\infty$-topos of simplicial spaces. If this latter proves feasible, then this in turn would reveal yet further connections between parametricity via cohesion and another prominent attempt at a solution to the coherence problem, namely Riehl & Shulman's *simplicial type theory*, which takes its semantics in simplicial spaces.

It appears, in all these cases, that parametricity is *the* tool for the job of taming the complexity of higher coherences in HoTT and elsewhere. In this sense, Reynolds was right in thinking that parametricity captures a fundamental property of abstraction, for, as any type theorist worth their salt knows, abstraction is ultimately the best tool we have for managing complexity.

## Acknowledgements

The origins of this paper trace to research I did as an undergraduate at Merton College, Oxford, in the Summer of 2020, as part of the Merton College Summer Projects Scheme. Naturally, this work was conducted at a time of considerable stress for myself and the world at large, and I am massively indebted to the academic support staff at Merton, who were immensely helpful in keeping me afloat at that time. I am particularly grateful to Katy Fifield, Jemma Underdown, and Jane Gover for the support they provided to me in the course of my undergraduate studies. More recently, I am grateful to Frank Pfenning and Steve Awodey for their encouragement in continuing to pursue this line of research.