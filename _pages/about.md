---
permalink: /
title: "Mathematics, Coding, Education"
excerpt: "About me"
author_profile: true
redirect_from: 
  - /about/
  - /about.html
---

### Updates
<img src="{{site.url}}/images/eckmann-hilton-in-my-hopf-fibration.jpg" style="display: block; margin: auto;" />

Don't believe me? Watch the talk to find out why!

I recently gave a talk at HoTT/UF2024 hosted by KU Leuven. You can find details about the talk, along with a recording, under the talks section on [the following page](https://morphismz.github.io/talks/2024-04-03-hottuf).

Bio
======
I graduated summa cum laude from the University of Colorado, Boulder with a bachelors of arts in mathematics, with a double major in philosophy. For my honors, I defended a thesis in the mathematics department, written under the direction of [Professor Jonathan Wise](https://math.colorado.edu/~jonathan.wise/), titled “Eckmann-Hilton and the Hopf Fibration in Homotopy Type Theory." I have subsequently presented the results of my thesis at a few mathematics confrences, information about which (including slides, abstracts, and a recording of one of them) can be found [on the talks page](https://morphismz.github.io/talks).

Within mathematics, I have a focus in higher category theory and homotopy theory, in type theory and the foundations of math, and in the connections between these subjects and computer science, such as functional programming and the formal verification of proofs and programs. As an application this latter interest, I am a contributor to the [agda-unimath repository](https://unimath.github.io/agda-unimath/), an encyclopedia of formalized mathematics and certified programs.

I also have an interest in mathematical cryptography, combinatorics and probability theory. I enjoy writing programs implementing ideas from these subjects.


Mathematics
======
My areas of specialization with in mathematics include higher category theory and homotopy theory, the foundations of mathematics and formal verification. In particular, I have a focus in synthetic approaches to higher category theory and homotopy theory, such as [omotopy type theory](https://en.wikipedia.org/wiki/Homotopy_type_theory). I focus on [univalent approaches to the foundations of mathematics](https://en.wikipedia.org/wiki/Univalent_foundations). I hope to help advance their prominence in the mathematical community by developing mathematics in Homotopy Type Theory. As an example of this, [my honors thesis](https://morphismz.github.io/publication/2023-04-06-honors-thesis) constructs the Hopf fibration in a uniquely univalent way. This construction of the Hopf fibration makes salient its connection to the Eckmann-Hilton argument and further demonstrates that the generator of `π₃(𝕊²)` is the Eckmann-Hilton identification.

agda-unimath
======
I am a contributor to the [agda-unimath repository](https://unimath.github.io/agda-unimath/) repository, a collaborative and sprawling formal verification project comprising over 300K lines of code. The principal aim of agda-unimath is to "create an online encyclopedia of formalized mathematics containing an extensive curriculum of topics from a univalent point of view." For more on the what the "univalent point of view" entails, please see [the following page](https://en.wikipedia.org/wiki/Univalent_foundations).

Written in [Agda](https://agda.readthedocs.io/en/v2.6.4.3/getting-started/what-is-agda.html), a dependently typed pure functional programming language, agda-unimath employs a variant of [Martin Löf Type Theory](https://ncatlab.org/nlab/show/Martin-L%C3%B6f+dependent+type+theory) combined with the [univalence axiom](https://ncatlab.org/nlab/show/univalence+axiom) and [postulated higher inductive types](https://ncatlab.org/nlab/show/higher+inductive+type). This allows agda-unimath to treat homotopical and higher categorical structures as primitive objects, paving the way for the development of [synthetic homotopy theory](https://unimath.github.io/agda-unimath/synthetic-homotopy-theory.html). Additionally, this enables the development of many branches of mathematics from the univalent point of view. In particular, agda-unimath contains a substantial amount of [univalent group theory](https://unimath.github.io/agda-unimath/group-theory.html) and [univalent combinatorics](https://unimath.github.io/agda-unimath/univalent-combinatorics.html).

A full acount of my contributions to agda-unimath can be found [here](https://github.com/UniMath/agda-unimath/pulls?q=is%3Apr+is%3Aclosed+author%3Amorphismz). Here are some selected contributions:

- The Eckmann-Hilton Argument: I am one of the primary authors of the page on the [Eckmann-Hilton argument](https://unimath.github.io/agda-unimath/synthetic-homotopy-theory.eckmann-hilton-argument.html?highlight=eckmann#the-eckmann-hilton-argument). This pages formalizes the Eckmann-Hilton argument using the naturality condition of the descent data of the family of based identifications induced by a 2-loop.

- The Universal Property of the Family of Fibers of a Map: I am one of the primary authors of the page on the [universal property of the family of fibers of a map](https://unimath.github.io/agda-unimath/foundation.universal-property-family-of-fibers-of-maps.html). This pages formalizes the universal property of the family of fibers of a map. The universal property states that, for a map `h : A → B`, the family of fibers is the initial type family over `B` equipped with a lift of `h`.

- The Suspension of a Type: The suspension of a type X is the (homotopy) pushout of the span `unit <-- X --> unit`. Pushouts are defined in agda-unimath by postulating a type with their universal property. I have helped to formalize some propreties of the suspension of a type, including:
  - [a characterization of identifications in the type of suspension structures](https://unimath.github.io/agda-unimath/synthetic-homotopy-theory.suspensions-of-types.html#4783)
  - [a proof suspsensions have the universal property excpected of them](https://unimath.github.io/agda-unimath/synthetic-homotopy-theory.suspensions-of-types.html#11043)
  - [definitions of the unit and counit of the suspension loop space adjunction](https://unimath.github.io/agda-unimath/synthetic-homotopy-theory.suspensions-of-types.html#15436)
  - [the equivalence of the suspension loop space adjunction](https://unimath.github.io/agda-unimath/synthetic-homotopy-theory.suspensions-of-types.html#18007).

I am curruently in the process of formalizing the main results of my honors thesis and incorporating it into the agda-unimath library. You can read more about this project [on the projects page](https://morphismz.github.io/projects/2023-eh-hopf) or keep up to date by reading [the associated github issue](https://github.com/UniMath/agda-unimath/issues/702). 

Philosophy
======
In my junior and senior year at CU, I was president of the [CU Boulder Undergraduate Philosophy Club](https://www.colorado.edu/philosophy/events/undergraduate-philosophy-club). As president I scheduled faculty talks, helped facilitate club discussions, and strived to make the philosophy club a more inclusive enviroment by hosting speakers from the Minorities and Philosophy program.

My interests in philosophy are primarily in metaphysics, philosophy of language, and the philosophy of mathematics. My favorite philosophical text is Saul Kripke's *Naming and Necessity*.

Teaching and Tutoring
======
I am currently the lead mathematics instructor at Temple Grandin School, serving students with Asperger's Syndrome and similar learning profiles.