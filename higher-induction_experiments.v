(** Some experiments with the idea of inductive definitions that allow constructors to produce not only points in the type being defined, but also paths in this type, i.e. points of its path space.

Obviously such definitions are not possible in Coq; here we simulate them by taking as axioms the recursors which they should produce if they *were* allowed, and worked similarly to the standard inductive definitions.  So, the types of these recursor axioms were essentially produced by imitating the standard recursors produced by Coq.

They types become necessarily slightly more complicated, since the ‘computation’ rules may only be assumed up to propositional equality.  One could also imagine an extension of the type theory in which these really were *computation* rules, holding up to definitional equality; i.e. where these “higher-dimensional” inductive definitions were implemented just as an extension of the normal ones.

There are three sections, investigating successively the interval; the circle; and the mapping cylinder of a map.  This last demonstrates a non-trivial consequence of these axioms: a “cofibration/trivial fibration” weak factorisation on the type theory.  *)



Require Import paths.


                   
Section Interval.

Axiom Interval : Type.

Axiom left_pt : Interval.
Axiom right_pt : Interval.
Axiom segment : left_pt ~ right_pt.

(**
The non-dependent eliminators, written as a warmup for the dependent ones.
Too weak to do anything with, but helpful to start seeing how these eliminators work.  We will never actually use these. *)

Axiom Interval_rect' : forall (Y:Type) (d_l : Y) (d_r : Y) (d_seg : d_l ~ d_r),
                          Interval -> Y.

Axiom Interval_comp'_l :  forall (Y:Type) (d_l : Y) (d_r : Y) (d_seg : d_l ~ d_r),
                     Interval_rect' Y d_l d_r d_seg left_pt ~ d_l.

Axiom Interval_comp'_r :  forall (Y:Type) (d_l : Y) (d_r : Y) (d_seg : d_l ~ d_r),
                     Interval_rect' Y d_l d_r d_seg right_pt ~ d_r.

Axiom Interval_comp'_seg :  forall (Y:Type) (d_l : Y) (d_r : Y) (d_seg : d_l ~ d_r),
                trans (sym (Interval_comp'_l Y d_l d_r d_seg))
               (trans (cong (Interval_rect' Y d_l d_r d_seg) segment)
                      (Interval_comp'_r Y d_l d_r d_seg))
                ~ d_seg.


(** The actual eliminators: *)

Axiom Interval_rect : forall (P : Interval -> Type)
                       (d_l : P left_pt) (d_r : P right_pt)
                       (d_seg : transport P segment d_l ~ d_r),
                          forall x : Interval, P x.
(** Writing this, one may be surprised by the type of d_seg; one realises that in these sorts of induction principles, one will need coercions between fibers to make the hypotheses about id-terms well-typed. *)

Axiom Interval_comp_l :  forall (P : Interval -> Type)
                       (d_l : P left_pt) (d_r : P right_pt)
                       (d_seg : transport P segment d_l ~ d_r),
                     Interval_rect P d_l d_r d_seg left_pt ~ d_l.

Axiom Interval_comp_r :  forall (P : Interval -> Type)
                       (d_l : P left_pt) (d_r : P right_pt)
                       (d_seg : transport P segment d_l ~ d_r),
                     Interval_rect P d_l d_r d_seg right_pt ~ d_r.

Axiom Interval_comp_seg :  forall (P : Interval -> Type)
                       (d_l : P left_pt) (d_r : P right_pt)
                       (d_seg : transport P segment d_l ~ d_r),
                trans (sym (cong (transport P segment)
                              (Interval_comp_l P d_l d_r d_seg)) )
               (trans (cong_dep (Interval_rect P d_l d_r d_seg) segment)
                      (Interval_comp_r P d_l d_r d_seg))
                ~ d_seg.
(** the type of the conclusion here is somewhat tricky to give!  But it is correct, I think — and in fact is of a reasonably generalisable form. *)

Definition interval_is_contractible : (isContr Interval).
unfold isContr.  split with right_pt.
pose (P := fun y => y ~ right_pt).
pose (d_l := segment).
pose (d_r := refl : right_pt ~ right_pt).
apply (@Interval_rect P d_l d_r).
unfold d_l, d_r.  simpl.
apply transport_of_path_is_composition.
Defined.

Definition twist : Interval -> Interval.
apply (Interval_rect (fun _ => Interval) right_pt left_pt).
exact (trans nondependent_transport_is_trivial (sym segment)).
Defined.

Definition ttl_l : twist (twist left_pt) ~ left_pt.
unfold twist at 2; simpl.
apply (trans (cong _ (Interval_comp_l (fun _ => Interval) _ _ _))). 
apply (Interval_comp_r (fun _ => Interval)).
Defined.

Definition ttr_r : twist (twist right_pt) ~ right_pt.
unfold twist at 2; simpl.
apply (trans (cong _ (Interval_comp_r (fun _ => Interval) _ _ _))). 
apply (Interval_comp_l (fun _ => Interval)).
Defined.

(*
Definition twist_is_involution : forall x : Interval, twist (twist x) ~ x.
apply (@Interval_rect (fun x => (twist (twist x)) ~ x) ttl_l ttr_r).

Some rather fiddly 2-dimensional reasoning may be needed here…

Oh, d’oh!  Of course not — this whole thing will be trivial since Interval is contractible.  *)

End Interval.




Section Circle.

Axiom Circle : Type.

Axiom base : Circle.
Axiom loop : base ~ base.
 
(** Warm-up, again, with the non-dependent version:
Axiom Circle_rect' : forall (Y:Type)
                           (d_b : Y)
                           (d_l : d_b ~ d_b), 
                           { f: Circle -> Y & {p : (f base ~ d_b) & 
                             (transport (fun x => x ~ x) p (cong f loop)) ~ d_l }}.
*)

Axiom Circle_rect : forall (P : Circle -> Type)
                           (d_b : P base)
                           (d_l : transport P loop d_b ~ d_b), 
                           forall x:Circle, P x.
(** Here, one might reasonably expect the type of d_l to be just  d_b ~ d_b (I thought it would be, at first).  But a little thought shows that it needs to include this transport.  Three very different justifications:
  (a) without this, one has trouble stating the axiom Circle_compute_loop;
  (b) as the Interval version shows above, in general the hypotheses for id-constructors in these induction principles will *need* coercions in their types;
  (c) most convincingly, inspecting the universal property for ΣS^1 in the groupoid model, with respect to fibrations over itself, shows that it satisfies _this_ version, not the naïve one.  (The complication comes from the form of morphisms in the total space of the fibration.)  *)
 
Axiom Circle_compute_base :  forall (P : Circle -> Type)
                           (d_b : P base)
                           (d_l : transport P loop d_b ~ d_b), 
                   Circle_rect P d_b d_l base ~ d_b.

Axiom Circle_compute_loop :  forall (P : Circle -> Type)
                           (d_b : P base)
                           (d_l : transport P loop d_b ~ d_b), 
               (trans (sym (cong (transport P loop)
                                 (Circle_compute_base P d_b d_l)) )
               (trans (cong_dep (Circle_rect P d_b d_l) loop)
                      (Circle_compute_base P d_b d_l)))
                ~ d_l.

(**  Compare this to the conclusion of Interval_comp_seg:
 
               (trans (sym (cong (transport P segment)
                              (Interval_comp_l P d_l d_r d_seg)) )
               (trans (cong_dep (Interval_rect P d_l d_r d_seg) segment)
                      (Interval_comp_r P d_l d_r d_seg)))
               ~ d_seg.

These do indeed fit a pattern which — at least for the 1-dimensional level — can now be written down in general without too much difficulty!
*)

(** Exercise 1: if the circle is contractible, then UIP holds.  (Not hard.) *)

(** Exercise 2: there is a map from \Z to the group  base ~ base.  (Mathematically not hard; not sure about the Coq side.)  *)

(** Exercise 3: now assuming univalence, show there is a map fron  base ~ base  to \Z.  (Shouldn’t be hard Coq-wise; mathematically nice, requires one non-trivial idea.) *)

(** Exercise 4: show that these maps are mutually inverse.  Or alternatively, that either one of them is an isomorphism.  (Probably quite hard!) *)


End Circle.



Section MappingCylinder.

Axiom map_cyl: forall {X Y:Type} (f:X -> Y), Y -> Type.
(** defined before introducing X, Y, f since otherwise this is interpreted as dependent just on Y, with X and f allowed to vary in the constructors. *)

Variables X Y:Type.
Variable f : X -> Y.

Axiom inl :   forall x:X, map_cyl f (f x).  
Axiom inr :   forall y:Y, map_cyl f y.
Axiom inseg : forall x:X, inl x ~ inr (f x).

Axiom map_cyl_rect : forall (P : (forall y:Y, map_cyl f y -> Type))
                       (d_l : forall x:X, P (f x) (inl x))
                       (d_r : forall y:Y, P y (inr y))
                       (d_seg : forall x:X,
                  transport (P (f x)) (inseg x) (d_l x) ~ d_r (f x)),
             forall (y:Y) (z: map_cyl f y), P y z. 

Axiom map_cyl_comp_l : forall (P : (forall y:Y, map_cyl f y -> Type))
                       (d_l : forall x:X, P (f x) (inl x))
                       (d_r : forall y:Y, P y (inr y))
                       (d_seg : forall x:X,
                  transport (P (f x)) (inseg x) (d_l x) ~ d_r (f x)),
      forall x:X, (map_cyl_rect P d_l d_r d_seg) (f x) (inl x) ~ d_l x.

Axiom map_cyl_comp_r : forall (P : (forall y:Y, map_cyl f y -> Type))
                       (d_l : forall x:X, P (f x) (inl x))
                       (d_r : forall y:Y, P y (inr y))
                       (d_seg : forall x:X,
                  transport (P (f x)) (inseg x) (d_l x) ~ d_r (f x)),
      forall y:Y, (map_cyl_rect P d_l d_r d_seg) y (inr y) ~ d_r y.

Axiom map_cyl_comp_seg : forall (P : (forall y:Y, map_cyl f y -> Type))
                       (d_l : forall x:X, P (f x) (inl x))
                       (d_r : forall y:Y, P y (inr y))
                       (d_seg : forall x:X,
                  transport (P (f x)) (inseg x) (d_l x) ~ d_r (f x)),
      forall x:X,
          (trans (sym (cong (transport (P (f x)) (inseg x))
                          (map_cyl_comp_l P d_l d_r d_seg x)))
          (trans (cong_dep (map_cyl_rect P d_l d_r d_seg (f x)) (inseg x))
                 (map_cyl_comp_r P d_l d_r d_seg (f x))))
          ~ (d_seg x).

(** Again: compare to the final type from the Interval_comp_seg:

               (trans (sym (cong (transport P segment)
                              (Interval_comp_l P d_l d_r d_seg)) )
               (trans (cong_dep  (Interval_rect P d_l d_r d_seg) segment)
                      (Interval_comp_r P d_l d_r d_seg)))
               ~ d_seg.
*)


(** Exercise 1: for each y:Y, map_cyl y is contractible.  In other words, map_cyl f is a trivial fibration, and hence gives a factorisation of f into a cofibration (inl) followed by a trivial fibration. *)

Theorem map_cyl_trivial : forall y:Y, isContr (map_cyl f y).
Proof.
  intros y.  unfold isContr.  split with (inr y).
  pose (P := (fun (y:Y) (z: map_cyl f y) => z ~ inr y)). 
  pose (d_l := (fun (x:X) => (inseg x)) : forall x:X, P (f x) (inl x)).
  pose (d_r := (fun (y:Y) => refl) : forall y:Y, P y (inr y)).
  apply (map_cyl_rect P d_l d_r).
  unfold P, d_l, d_r.  intro x.
  apply transport_of_path_is_composition.
Defined.

End MappingCylinder.

Check @map_cyl.
(*   : forall X Y : Type, (X -> Y) -> Y -> Type *)
Check inl.
(*   : forall (X Y : Type) (f : X -> Y) (x : X), map_cyl f (f x) *)
Check map_cyl_trivial.
(*   : forall (X Y : Type) (f : X -> Y) (y : Y), isContr (map_cyl f y) *)

(** If we really had these defined as inductive types, with the computation rules actually holding up to definitional equality, this shows that we would now have a second (algebraic?) weak factorisation system, which together with the GG awfs gives much of the structure of a model category on the theory!

 (The generating trivial fibrations are families of contractible types.  Then any unary constructor of an inductively defined type, considered as a morphism, is a cofibration — e.g. inl into the total mapping cylinder, or refl into the total path space — this is not hard to prove.)  *)