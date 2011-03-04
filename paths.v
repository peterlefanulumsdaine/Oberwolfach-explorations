
(** Path spaces, and basic lemmas about them. *)

Inductive Paths {X:Type} : X -> X -> Type :=
  | refl {x:X} : Paths x x.

Notation "x ~ y" := (Paths x y) (at level 50) : type_scope.



(** The commonest higher-groupoid operations in the path spaces: *)

Definition sym {X:Type} {x y : X} (p : x ~ y) : y ~ x :=
match p with refl x => refl end.

Definition symIsInvol  {X:Type} {x y : X} (p : x ~ y)
              : sym (sym p) ~ p.
induction p; simpl.  exact refl.
Defined.

Definition trans {X:Type} {x y z : X} (p : x ~ y) (q : y ~ z) : x ~ z.
induction p.  exact q.
Defined.

Definition symSwitchesTrans {X:Type} {x y z : X} (p : x ~ y) (q : y ~ z)
               : sym (trans p q) ~ trans (sym q) (sym p).
induction p.  induction q.  simpl.  exact refl.
Defined.

Definition transIsAssoc {X:Type} {x y z w : X} (p:x~y) (q:y~z) (r:z~w) 
               : trans (trans p q) r ~ trans p (trans q r).
induction p; induction q; induction r; simpl.  exact refl.
Defined. 

Definition transRightUnit {X:Type} {x y: X} (p:x~y) 
               : trans p refl ~ p.
induction p; simpl.  exact refl.
Defined. 

Definition transLeftUnit {X:Type} {x y: X} (p:x~y) 
               : trans refl p ~ p.
induction p; simpl.  exact refl.
Defined. 

Definition symLeftInverse {X:Type} {x y: X} (p:x~y)
               : trans (sym p) p ~ refl.
induction p; simpl.  exact refl.
Defined.

Definition symRightInverse {X:Type} {x y: X} (p:x~y)
               : trans p (sym p) ~ refl.
induction p; simpl.  exact refl.
Defined.





(** transport along paths aka coercion etc. *)

Definition transport {X:Type} (P: X -> Type) {x x':X} (p: x ~ x') : P x -> P x'.
induction p.  exact (fun y => y).
Defined.

Lemma transport_of_path_is_composition {X:Type} {x x' : X} (p: x ~ x') :
         (transport (fun y => y ~ x') p p) ~ refl.
induction p.  simpl.  exact refl.
Defined.

Lemma nondependent_transport_is_trivial {X Y : Type} {x x' : X} {p : x ~ x'} {y : Y}
              : transport (fun _ => Y) p y ~ y.
induction p.  apply refl.
Defined.




(** congruence of all maps for paths, aka functoriality etc. *)

Definition cong {X Y:Type} (f: X -> Y) {x x' : X} (p: x ~ x') : f x ~ f x'.
induction p.  exact refl.
Defined.

Definition congPreservesTrans {X Y:Type} (f: X -> Y) {x y z : X} 
             (p: x ~ y) (q: y ~ z) : (cong f (trans p q)) ~ trans (cong f p) (cong f q).
induction p.  induction q.  simpl.  exact refl.
Defined.

Definition congPreservesSym {X Y:Type} (f: X -> Y) {x y : X} 
             (p: x ~ y) : (cong f (sym p)) ~ sym (cong f p).
induction p.  simpl.  exact refl.
Defined.


Definition cong_dep {X:Type} {P : X -> Type} (f: forall x:X, P x)
                   {x x' : X} (p: x ~ x') : transport P p (f x) ~ f x'.
induction p.  exact refl.
Defined.




(* Some constructions on sigma types and paths *)

Definition pair {X:Type} {P:X->Type} (x:X) (y:P x) := existT P x y.

Definition pairPath {X:Type} {P: X -> Type} {x x' : X} (p : x ~ x') :
             forall {y : P x} {y' : P x'} (q : (transport P p y) ~ y'), 
                  (pair x y) ~ (pair x' y').
induction p. simpl.  intros y y' q; induction q.  exact refl.
Defined.


