**Explorations of (Synthetic) Homotopy Theory in Coq**
---- 

These files contain some explorations/developments of homotopy theory inside intensional type theory, investigating the ideas discussed at the Oberwolfach mini-workshop in Feb/Mar 2011.

They are to be read with the propositional-equality-as-paths philosophy, as used in eg the univalent foundations of Voevodsky.  The core concept is the inductive type usually thought of as *propositional equality*, considered instead as the *space of paths* (or *morphisms*, *1-cells*…) between points of types.  Thus types are considered as something like spaces, instead of just like sets; and so we can develop homotopy theory purely internally.

Currently contains files:

- `paths.v`: Definition of path spaces, and basic workhorse functions for composition of paths, transport along paths, etc.

- `basic_weqs.v`: Some basic homotopy-theoretic definitions — contractibility, weak equivalences, basic constructions with these.

- `etacorrection.v`: The propositional η-rule, and a couple of lemmas.

- `univalence.v`: Voevodsky’s Univalence axiom, and its important equivalent form as an induction principle for weq’s.

- `pathspaces.v`: Definition and constructions on the total path spaces of types.

- `fext_from_univalence.v`: Deduction of functional extensionality from UA.  (Depending on all the files above.)

- `higher-induction_experiments.v`: investigating (approximations of) higher-dimensional inductive type definitions — the interval, the circle, and mapping cylinders.
